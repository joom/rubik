From Stdlib Require Import Arith Bool List Lia.
From Rubik Require Export Cube.Group Cube.Invariant.
Import ListNotations.

(** * Solving one slot at a time

    A solving method fixes the pieces in a fixed order, each step using a
    sequence that leaves the finished ones alone. Composed on the left, each
    slot's reading changes on its own, so the choice at each step depends on
    twenty-four values rather than on the whole cube. That is what makes the
    method checkable: each step is a small table, and the table is verified by
    computing what its sequences denote.

    Nothing here knows where the tables came from. *)

(** Comparing slot readings. *)
Definition corner_slot_eqb (x y : corner_slot) : bool :=
  if corner_slot_eq_dec x y then true else false.

(** And the same for an edge slot reading. *)
Definition edge_slot_eqb (x y : edge_slot) : bool :=
  if edge_slot_eq_dec x y then true else false.

(** A test that says yes really is an equality, which is what lets a table
    lookup stand in for the reading it answered. *)
Lemma corner_slot_eqb_true x y : corner_slot_eqb x y = true -> x = y.
Proof. unfold corner_slot_eqb; destruct (corner_slot_eq_dec x y); congruence. Qed.

(** The same for an edge reading. *)
Lemma edge_slot_eqb_true x y : edge_slot_eqb x y = true -> x = y.
Proof. unfold edge_slot_eqb; destruct (edge_slot_eq_dec x y); congruence. Qed.

(** The slots a cube already has right. *)
Definition corners_done (d : cube) (cs : list corner) : Prop :=
  forall X, In X cs -> read_corner d X = (X, T0).

(** And the edge slots it has right. *)
Definition edges_done (d : cube) (es : list edge) : Prop :=
  forall Y, In Y es -> read_edge d Y = (Y, F0).

(** Composing on the left leaves a finished slot finished, provided the
    sequence's own cube holds that piece at home. *)
Lemma corners_done_keep d h cs :
  corners_done d cs -> (forall X, In X cs -> read_corner h X = (X, T0)) ->
  corners_done (compose h d) cs.
Proof.
  intros Hd Hh X HX; rewrite read_corner_compose, (Hd X HX).
  apply follow_corner_fixed, Hh, HX.
Qed.

(** The same for an edge slot. *)
Lemma edges_done_keep d h es :
  edges_done d es -> (forall Y, In Y es -> read_edge h Y = (Y, F0)) ->
  edges_done (compose h d) es.
Proof.
  intros Hd Hh Y HY; rewrite read_edge_compose, (Hd Y HY).
  apply follow_edge_fixed, Hh, HY.
Qed.

(** * Tables

    A table answers, for each reading a slot might show, with a sequence that
    brings that slot home without disturbing the ones already done. *)

Definition corner_table := list (corner_slot * list move).

(** And one for an edge slot. *)
Definition edge_table := list (edge_slot * list move).

(** The sequence a table gives for a reading, or nothing if it has no entry. *)
Fixpoint corner_lookup (t : corner_table) (v : corner_slot) : list move :=
  match t with
  | [] => []
  | (u, w) :: r => if corner_slot_eqb u v then w else corner_lookup r v
  end.

(** The same for an edge table. *)
Fixpoint edge_lookup (t : edge_table) (v : edge_slot) : list move :=
  match t with
  | [] => []
  | (u, w) :: r => if edge_slot_eqb u v then w else edge_lookup r v
  end.

(** Whether the table has an entry for this reading at all. *)
Definition corner_covers (t : corner_table) (v : corner_slot) : bool :=
  existsb (fun e => corner_slot_eqb (fst e) v) t.

(** The same for an edge table. *)
Definition edge_covers (t : edge_table) (v : edge_slot) : bool :=
  existsb (fun e => edge_slot_eqb (fst e) v) t.

(** A reading the table covers is one of its entries, so whatever the table
    was checked for holds of the sequence looked up. *)
Lemma corner_lookup_in t v : corner_covers t v = true -> In (v, corner_lookup t v) t.
Proof.
  unfold corner_covers; induction t as [| [u w] t IH]; simpl; [discriminate |].
  destruct (corner_slot_eqb u v) eqn:E; simpl; [intros _ | intro H].
  - left; rewrite (corner_slot_eqb_true u v E); reflexivity.
  - right; apply IH, H.
Qed.

(** The same for an edge table. *)
Lemma edge_lookup_in t v : edge_covers t v = true -> In (v, edge_lookup t v) t.
Proof.
  unfold edge_covers; induction t as [| [u w] t IH]; simpl; [discriminate |].
  destruct (edge_slot_eqb u v) eqn:E; simpl; [intros _ | intro H].
  - left; rewrite (edge_slot_eqb_true u v E); reflexivity.
  - right; apply IH, H.
Qed.

(** What a table has to satisfy: every sequence in it leaves the finished
    slots alone and brings its own reading home. Both are computations on the
    cube the sequence denotes. *)
Definition corner_table_ok (t : corner_table) (cs : list corner) (es : list edge)
    (X : corner) : bool :=
  forallb (fun e =>
    let w := snd e in
    andb (forallb (fun Y => corner_slot_eqb (read_corner (element w) Y) (Y, T0)) cs)
    (andb (forallb (fun Y => edge_slot_eqb (read_edge (element w) Y) (Y, F0)) es)
          (corner_slot_eqb (follow_corner (element w) (fst e)) (X, T0)))) t.

(** The same conditions for a table that finishes an edge slot. *)
Definition edge_table_ok (t : edge_table) (cs : list corner) (es : list edge)
    (Y : edge) : bool :=
  forallb (fun e =>
    let w := snd e in
    andb (forallb (fun X => corner_slot_eqb (read_corner (element w) X) (X, T0)) cs)
    (andb (forallb (fun Z => edge_slot_eqb (read_edge (element w) Z) (Z, F0)) es)
          (edge_slot_eqb (follow_edge (element w) (fst e)) (Y, F0)))) t.

(** One step of the method. *)
Lemma finish_corner t cs es X d :
  corner_table_ok t cs es X = true -> corner_covers t (read_corner d X) = true ->
  corners_done d cs -> edges_done d es ->
  corners_done (compose (element (corner_lookup t (read_corner d X))) d) (X :: cs) /\
  edges_done (compose (element (corner_lookup t (read_corner d X))) d) es.
Proof.
  intros Hok Hcov Hc He.
  set (w := corner_lookup t (read_corner d X)).
  pose proof (corner_lookup_in t (read_corner d X) Hcov) as Hin.
  unfold corner_table_ok in Hok; rewrite forallb_forall in Hok.
  specialize (Hok _ Hin); cbn [fst snd] in Hok.
  apply Bool.andb_true_iff in Hok as [H1 Hok].
  apply Bool.andb_true_iff in Hok as [H2 H3].
  rewrite forallb_forall in H1, H2.
  assert (Hfc : forall Y, In Y cs -> read_corner (element w) Y = (Y, T0))
    by (intros Y HY; apply corner_slot_eqb_true, H1, HY).
  assert (Hfe : forall Y, In Y es -> read_edge (element w) Y = (Y, F0))
    by (intros Y HY; apply edge_slot_eqb_true, H2, HY).
  split; [| apply edges_done_keep; auto].
  intros Y [<- | HY].
  - rewrite read_corner_compose; apply corner_slot_eqb_true, H3.
  - apply (corners_done_keep d (element w) cs Hc Hfc Y HY).
Qed.

(** And one step at an edge slot. *)
Lemma finish_edge t cs es Y d :
  edge_table_ok t cs es Y = true -> edge_covers t (read_edge d Y) = true ->
  corners_done d cs -> edges_done d es ->
  corners_done (compose (element (edge_lookup t (read_edge d Y))) d) cs /\
  edges_done (compose (element (edge_lookup t (read_edge d Y))) d) (Y :: es).
Proof.
  intros Hok Hcov Hc He.
  set (w := edge_lookup t (read_edge d Y)).
  pose proof (edge_lookup_in t (read_edge d Y) Hcov) as Hin.
  unfold edge_table_ok in Hok; rewrite forallb_forall in Hok.
  specialize (Hok _ Hin); cbn [fst snd] in Hok.
  apply Bool.andb_true_iff in Hok as [H1 Hok].
  apply Bool.andb_true_iff in Hok as [H2 H3].
  rewrite forallb_forall in H1, H2.
  assert (Hfc : forall X, In X cs -> read_corner (element w) X = (X, T0))
    by (intros X HX; apply corner_slot_eqb_true, H1, HX).
  assert (Hfe : forall Z, In Z es -> read_edge (element w) Z = (Z, F0))
    by (intros Z HZ; apply edge_slot_eqb_true, H2, HZ).
  split; [apply corners_done_keep; auto |].
  intros Z [<- | HZ].
  - rewrite read_edge_compose; apply edge_slot_eqb_true, H3.
  - apply (edges_done_keep d (element w) es He Hfe Z HZ).
Qed.

(** * Which readings a slot can show

    A finished slot holds its own piece, so no unfinished slot can hold one of
    those pieces: the pieces of a reachable cube are all different. *)

Lemma corner_rank_inj X Y : corner_rank X = corner_rank Y -> X = Y.
Proof. destruct X, Y; simpl; congruence. Qed.

(** And edge ranks determine an edge. *)
Lemma edge_rank_inj X Y : edge_rank X = edge_rank Y -> X = Y.
Proof. destruct X, Y; simpl; congruence. Qed.

(** Reading a corner slot is reading the piece list at that slot's rank. *)
Lemma read_corner_nth d X : fst (read_corner d X) = nth (corner_rank X) (corner_pieces d) URF.
Proof. destruct X; reflexivity. Qed.

(** And the same for an edge slot. *)
Lemma read_edge_nth d Y : fst (read_edge d Y) = nth (edge_rank Y) (edge_pieces d) UR.
Proof. destruct Y; reflexivity. Qed.

(** A cube always reports eight corner pieces, *)
Lemma corner_pieces_length d : length (corner_pieces d) = 8.
Proof. reflexivity. Qed.

(** and twelve edge pieces. *)
Lemma edge_pieces_length d : length (edge_pieces d) = 12.
Proof. reflexivity. Qed.

(** Corner ranks are exactly the positions of that list, *)
Lemma corner_rank_lt X : corner_rank X < 8.
Proof. destruct X; simpl; lia. Qed.

(** and edge ranks the positions of this one. *)
Lemma edge_rank_lt Y : edge_rank Y < 12.
Proof. destruct Y; simpl; lia. Qed.

(** Distinct slots of a duplicate-free cube hold distinct pieces. *)
Lemma corner_slot_inj d X Y :
  NoDup (corner_ranks d) -> fst (read_corner d X) = fst (read_corner d Y) -> X = Y.
Proof.
  intros H E; apply NoDup_map_inv in H.
  rewrite NoDup_nth in H.
  apply corner_rank_inj, (H (corner_rank X) (corner_rank Y));
    [ rewrite corner_pieces_length; apply corner_rank_lt
    | rewrite corner_pieces_length; apply corner_rank_lt
    | rewrite <- !read_corner_nth; exact E ].
Qed.

(** The same for edge slots. *)
Lemma edge_slot_inj d X Y :
  NoDup (edge_ranks d) -> fst (read_edge d X) = fst (read_edge d Y) -> X = Y.
Proof.
  intros H E; apply NoDup_map_inv in H.
  rewrite NoDup_nth in H.
  apply edge_rank_inj, (H (edge_rank X) (edge_rank Y));
    [ rewrite edge_pieces_length; apply edge_rank_lt
    | rewrite edge_pieces_length; apply edge_rank_lt
    | rewrite <- !read_edge_nth; exact E ].
Qed.

(** So an unfinished slot never shows a finished slot's piece. *)
Lemma corner_fresh d cs X :
  wellformed d -> corners_done d cs -> ~ In X cs -> ~ In (fst (read_corner d X)) cs.
Proof.
  intros [Hnd _] Hs HX Hin.
  assert (E : fst (read_corner d X) = fst (read_corner d (fst (read_corner d X))))
    by (rewrite (Hs _ Hin); reflexivity).
  apply HX; rewrite (corner_slot_inj d X _ Hnd E); exact Hin.
Qed.

(** And the same for edges. *)
Lemma edge_fresh d es Y :
  wellformed d -> edges_done d es -> ~ In Y es -> ~ In (fst (read_edge d Y)) es.
Proof.
  intros [_ Hnd] Hs HY Hin.
  assert (E : fst (read_edge d Y) = fst (read_edge d (fst (read_edge d Y))))
    by (rewrite (Hs _ Hin); reflexivity).
  apply HY; rewrite (edge_slot_inj d Y _ Hnd E); exact Hin.
Qed.

(** Every reading of a corner slot, and of an edge slot. *)
Definition all_corner_readings : list corner_slot :=
  [(URF,T0);(URF,T1);(URF,T2);(UFL,T0);(UFL,T1);(UFL,T2);
   (ULB,T0);(ULB,T1);(ULB,T2);(UBR,T0);(UBR,T1);(UBR,T2);
   (DFR,T0);(DFR,T1);(DFR,T2);(DLF,T0);(DLF,T1);(DLF,T2);
   (DBL,T0);(DBL,T1);(DBL,T2);(DRB,T0);(DRB,T1);(DRB,T2)].

(** And every reading an edge slot can show. *)
Definition all_edge_readings : list edge_slot :=
  [(UR,F0);(UR,F1);(UF,F0);(UF,F1);(UL,F0);(UL,F1);(UB,F0);(UB,F1);
   (DR,F0);(DR,F1);(DF,F0);(DF,F1);(DL,F0);(DL,F1);(DB,F0);(DB,F1);
   (FR,F0);(FR,F1);(FL,F0);(FL,F1);(BL,F0);(BL,F1);(BR,F0);(BR,F1)].

(** The list really is every corner reading, *)
Lemma all_corner_readings_complete v : In v all_corner_readings.
Proof. destruct v as [X t]; destruct X, t; simpl; tauto. Qed.

(** and this one every edge reading. *)
Lemma all_edge_readings_complete v : In v all_edge_readings.
Proof. destruct v as [Y f]; destruct Y, f; simpl; tauto. Qed.

(** The readings a slot can still show once the listed slots are finished. *)
Definition corner_inb (X : corner) (cs : list corner) : bool :=
  existsb (fun Y => Nat.eqb (corner_rank X) (corner_rank Y)) cs.

(** The same test for an edge slot. *)
Definition edge_inb (Y : edge) (es : list edge) : bool :=
  existsb (fun Z => Nat.eqb (edge_rank Y) (edge_rank Z)) es.

(** A slot outside the finished list fails the test, *)
Lemma corner_inb_false X cs : ~ In X cs -> corner_inb X cs = false.
Proof.
  intro H; apply Bool.not_true_is_false; intro E.
  apply existsb_exists in E as [Y [HY HE]]; apply Nat.eqb_eq, corner_rank_inj in HE.
  subst; contradiction.
Qed.

(** and the same for an edge slot. *)
Lemma edge_inb_false Y es : ~ In Y es -> edge_inb Y es = false.
Proof.
  intro H; apply Bool.not_true_is_false; intro E.
  apply existsb_exists in E as [Z [HZ HE]]; apply Nat.eqb_eq, edge_rank_inj in HE.
  subst; contradiction.
Qed.

(** The corner readings still possible once the listed slots are finished. *)
Definition corner_domain (cs : list corner) : list corner_slot :=
  filter (fun v => negb (corner_inb (fst v) cs)) all_corner_readings.

(** And the edge readings. *)
Definition edge_domain (es : list edge) : list edge_slot :=
  filter (fun v => negb (edge_inb (fst v) es)) all_edge_readings.

(** A reading whose piece is unfinished is one of those, *)
Lemma in_corner_domain v cs : ~ In (fst v) cs -> In v (corner_domain cs).
Proof.
  intro H; apply filter_In; split;
    [apply all_corner_readings_complete | rewrite (corner_inb_false _ _ H); reflexivity].
Qed.

(** and the same for an edge reading. *)
Lemma in_edge_domain v es : ~ In (fst v) es -> In v (edge_domain es).
Proof.
  intro H; apply filter_In; split;
    [apply all_edge_readings_complete | rewrite (edge_inb_false _ _ H); reflexivity].
Qed.

(** * Finishing

    All twenty slots right is the solved cube, and the last slot of each kind
    needs no table: its piece is the only one left and its orientation is
    forced by the totals. *)

Definition all_corner_slots : list corner :=
  [URF; UFL; ULB; UBR; DFR; DLF; DBL; DRB].

(** and all twelve edge slots. *)
Definition all_edge_slots : list edge :=
  [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL; BL; BR].

(** Every slot right is the solved cube, which is how a run ends. *)
Lemma solved_everywhere d :
  corners_done d all_corner_slots -> edges_done d all_edge_slots -> d = solved_cube.
Proof.
  intros Hc He; apply cube_ext.
  - intro X; rewrite read_corner_solved_cube; apply Hc; destruct X; simpl; tauto.
  - intro Y; rewrite read_edge_solved_cube; apply He; destruct Y; simpl; tauto.
Qed.

(** The eighth corner holds the only piece left, unturned because the
    rotations of a reachable cube cancel. *)
Lemma last_corner d :
  wellformed d -> twist_total d = T0 ->
  corners_done d [URF; UFL; ULB; UBR; DFR; DLF; DBL] ->
  read_corner d DRB = (DRB, T0).
Proof.
  intros Hw Ht Hs.
  assert (Hfr : ~ In (fst (read_corner d DRB)) [URF; UFL; ULB; UBR; DFR; DLF; DBL])
    by (apply corner_fresh; auto; simpl; intuition discriminate).
  pose proof (Hs URF ltac:(simpl; tauto)) as H0.
  pose proof (Hs UFL ltac:(simpl; tauto)) as H1.
  pose proof (Hs ULB ltac:(simpl; tauto)) as H2.
  pose proof (Hs UBR ltac:(simpl; tauto)) as H3.
  pose proof (Hs DFR ltac:(simpl; tauto)) as H4.
  pose proof (Hs DLF ltac:(simpl; tauto)) as H5.
  pose proof (Hs DBL ltac:(simpl; tauto)) as H6.
  cbn [read_corner] in Hfr, H0, H1, H2, H3, H4, H5, H6 |- *.
  destruct (xDRB d) as [P t] eqn:E; cbn [fst] in Hfr.
  assert (P = DRB) by (destruct P; simpl in Hfr; tauto); subst P.
  unfold twist_total, twists, corner_slots in Ht.
  cbn [map fold_right] in Ht.
  rewrite H0, H1, H2, H3, H4, H5, H6, E in Ht; cbn [snd] in Ht.
  destruct t; cbn [twist_add] in Ht; congruence.
Qed.

(** And the twelfth edge, unflipped because the flips cancel. *)
Lemma last_edge d :
  wellformed d -> flip_total d = F0 ->
  edges_done d [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL; BL] ->
  read_edge d BR = (BR, F0).
Proof.
  intros Hw Hf Hs.
  assert (Hfr : ~ In (fst (read_edge d BR)) [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL; BL])
    by (apply edge_fresh; auto; simpl; intuition discriminate).
  pose proof (Hs UR ltac:(simpl; tauto)) as H0.
  pose proof (Hs UF ltac:(simpl; tauto)) as H1.
  pose proof (Hs UL ltac:(simpl; tauto)) as H2.
  pose proof (Hs UB ltac:(simpl; tauto)) as H3.
  pose proof (Hs DR ltac:(simpl; tauto)) as H4.
  pose proof (Hs DF ltac:(simpl; tauto)) as H5.
  pose proof (Hs DL ltac:(simpl; tauto)) as H6.
  pose proof (Hs DB ltac:(simpl; tauto)) as H7.
  pose proof (Hs FR ltac:(simpl; tauto)) as H8.
  pose proof (Hs FL ltac:(simpl; tauto)) as H9.
  pose proof (Hs BL ltac:(simpl; tauto)) as H10.
  cbn [read_edge] in Hfr, H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.
  destruct (yBR d) as [P f] eqn:E; cbn [fst] in Hfr.
  assert (P = BR) by (destruct P; simpl in Hfr; tauto); subst P.
  unfold flip_total, flips, edge_slots in Hf.
  cbn [map fold_right] in Hf.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, E in Hf; cbn [snd] in Hf.
  destruct f; cbn [flip_add] in Hf; congruence.
Qed.

(** The eleventh edge holds its own piece. The other candidate would leave the
    last two exchanged, and that is odd, which no sequence can produce. *)
Lemma eleventh_edge d :
  wellformed d -> cube_parity d = false ->
  corners_done d all_corner_slots ->
  edges_done d [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL] ->
  fst (read_edge d BL) = BL.
Proof.
  intros Hw Hp Hc He.
  assert (HBL : ~ In (fst (read_edge d BL)) [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL])
    by (apply edge_fresh; auto; simpl; intuition discriminate).
  assert (HBR : ~ In (fst (read_edge d BR)) [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL])
    by (apply edge_fresh; auto; simpl; intuition discriminate).
  assert (Hne : fst (read_edge d BL) <> fst (read_edge d BR))
    by (intro E; discriminate (edge_slot_inj d BL BR (proj2 Hw) E)).
  pose proof (Hc URF ltac:(simpl; tauto)) as C0.
  pose proof (Hc UFL ltac:(simpl; tauto)) as C1.
  pose proof (Hc ULB ltac:(simpl; tauto)) as C2.
  pose proof (Hc UBR ltac:(simpl; tauto)) as C3.
  pose proof (Hc DFR ltac:(simpl; tauto)) as C4.
  pose proof (Hc DLF ltac:(simpl; tauto)) as C5.
  pose proof (Hc DBL ltac:(simpl; tauto)) as C6.
  pose proof (Hc DRB ltac:(simpl; tauto)) as C7.
  pose proof (He UR ltac:(simpl; tauto)) as E0.
  pose proof (He UF ltac:(simpl; tauto)) as E1.
  pose proof (He UL ltac:(simpl; tauto)) as E2.
  pose proof (He UB ltac:(simpl; tauto)) as E3.
  pose proof (He DR ltac:(simpl; tauto)) as E4.
  pose proof (He DF ltac:(simpl; tauto)) as E5.
  pose proof (He DL ltac:(simpl; tauto)) as E6.
  pose proof (He DB ltac:(simpl; tauto)) as E7.
  pose proof (He FR ltac:(simpl; tauto)) as E8.
  pose proof (He FL ltac:(simpl; tauto)) as E9.
  cbn [read_corner read_edge] in HBL, HBR, Hne, C0, C1, C2, C3, C4, C5, C6, C7,
                     E0, E1, E2, E3, E4, E5, E6, E7, E8, E9 |- *.
  destruct (yBL d) as [P f] eqn:EL; destruct (yBR d) as [Q g] eqn:ER.
  cbn [fst] in HBL, HBR, Hne |- *.
  destruct P; try (simpl in HBL; tauto); try reflexivity.
  exfalso; destruct Q; try (simpl in HBR; tauto); try congruence.
  unfold cube_parity, corner_ranks, edge_ranks, corner_pieces, edge_pieces,
         corner_slots, edge_slots in Hp.
  cbn [map] in Hp.
  rewrite C0, C1, C2, C3, C4, C5, C6, C7, E0, E1, E2, E3, E4, E5, E6, E7,
          E8, E9, EL, ER in Hp.
  vm_compute in Hp; discriminate.
Qed.

(** * What the method starts from and ends with *)

(** A cube some sequence produces. Every cube the method meets is one, since
    it only ever composes with sequences. *)
Definition generated (d : cube) : Prop := exists q, element q = d.

(** Composing with any sequence keeps a cube one that sequences produce. *)
Lemma generated_step w d : generated d -> generated (compose (element w) d).
Proof. intros [q <-]; exists (w ++ q); apply element_app. Qed.

(** A cube that can be solved is one of them, by undoing its solution. *)
Lemma generated_solvable c : solvable c -> generated c.
Proof. apply solvable_element. Qed.

(** So its pieces are all different, *)
Lemma generated_wellformed d : generated d -> wellformed d.
Proof. intros [q <-]; apply wellformed_element. Qed.

(** its two rearrangements have even combined parity, *)
Lemma generated_cube_parity d : generated d -> cube_parity d = false.
Proof. intros [q <-]; apply cube_parity_element. Qed.

(** its corner rotations cancel, *)
Lemma generated_twist d : generated d -> twist_total d = T0.
Proof. intros [q <-]; unfold element; apply twist_total_run_cube. Qed.

(** and its edge flips cancel. *)
Lemma generated_flip d : generated d -> flip_total d = F0.
Proof. intros [q <-]; unfold element; apply flip_total_run_cube. Qed.

(** Two steps in a row are one step with the sequences joined. *)
Lemma compose_steps w u d :
  compose (element w) (compose (element u) d) = compose (element (w ++ u)) d.
Proof. rewrite element_app, compose_assoc; reflexivity. Qed.

(** A sequence that solves a cube from the left solves it from the right, so
    the method's sequence is a solution in the ordinary sense. *)
Lemma solution_of_left c W :
  solvable c -> compose (element W) c = solved_cube -> run_cube c W = solved_cube.
Proof.
  intros [p Hp] HW; rewrite run_cube_by_element.
  rewrite run_cube_by_element in Hp.
  assert (E : element W = element p).
  { rewrite <- (compose_id_r (element W)), <- Hp, <- compose_assoc, HW.
    apply compose_id_l. }
  rewrite E; exact Hp.
Qed.

(** * How long the answer is *)

Definition corner_table_bounded (t : corner_table) (b : nat) : bool :=
  forallb (fun e => Nat.leb (length (snd e)) b) t.

(** And the same for an edge table. *)
Definition edge_table_bounded (t : edge_table) (b : nat) : bool :=
  forallb (fun e => Nat.leb (length (snd e)) b) t.

(** So a lookup is never longer than the bound its table passed, *)
Lemma corner_lookup_bounded t v b :
  corner_table_bounded t b = true -> corner_covers t v = true -> length (corner_lookup t v) <= b.
Proof.
  intros Hb Hc; unfold corner_table_bounded in Hb; rewrite forallb_forall in Hb.
  apply Nat.leb_le, (Hb _ (corner_lookup_in t v Hc)).
Qed.

(** and the same for an edge table. *)
Lemma edge_lookup_bounded t v b :
  edge_table_bounded t b = true -> edge_covers t v = true -> length (edge_lookup t v) <= b.
Proof.
  intros Hb Hc; unfold edge_table_bounded in Hb; rewrite forallb_forall in Hb.
  apply Nat.leb_le, (Hb _ (edge_lookup_in t v Hc)).
Qed.

(** * Running the whole method

    The stages differ only in which slot they finish and which table they
    consult, so the method is a fold over a list of them. What each stage may
    assume is what the stages before it established, which is why the check
    below carries the finished slots along. *)

Inductive stage :=
| CornerStage (X : corner) (t : corner_table) (b : nat)
| EdgeStage (Y : edge) (t : edge_table) (b : nat).

(** The cube after running the stages. *)
Fixpoint chain_state (ss : list stage) (d : cube) : cube :=
  match ss with
  | [] => d
  | CornerStage X t _ :: r => chain_state r (compose (element (corner_lookup t (read_corner d X))) d)
  | EdgeStage Y t _ :: r => chain_state r (compose (element (edge_lookup t (read_edge d Y))) d)
  end.

(** And the sequence that gets there. Later stages compose on the left, so
    their sequences come first. *)
Fixpoint chain_word (ss : list stage) (d : cube) : list move :=
  match ss with
  | [] => []
  | CornerStage X t _ :: r =>
      let w := corner_lookup t (read_corner d X) in chain_word r (compose (element w) d) ++ w
  | EdgeStage Y t _ :: r =>
      let w := edge_lookup t (read_edge d Y) in chain_word r (compose (element w) d) ++ w
  end.

(** The sequence a run builds really carries the cube to the state it ends in. *)
Lemma chain_state_word ss : forall d,
  compose (element (chain_word ss d)) d = chain_state ss d.
Proof.
  induction ss as [| s ss IH]; intro d; simpl;
    [rewrite element_nil; apply compose_id_l |].
  destruct s; rewrite element_app, compose_assoc; apply IH.
Qed.

(** The slots the stages finish. *)
Fixpoint stage_corners (ss : list stage) : list corner :=
  match ss with
  | [] => []
  | CornerStage X _ _ :: r => stage_corners r ++ [X]
  | EdgeStage _ _ _ :: r => stage_corners r
  end.

(** And the edge slots they finish. *)
Fixpoint stage_edges (ss : list stage) : list edge :=
  match ss with
  | [] => []
  | CornerStage _ _ _ :: r => stage_edges r
  | EdgeStage Y _ _ :: r => stage_edges r ++ [Y]
  end.

(** What a run of the method is allowed to do. The two runs differ only in
    this: which sequences their tables may use, which readings a slot can
    show, and what stays true of every cube on the way. Bundling those with
    the facts they have to satisfy keeps one driver for both. *)
Record policy := Policy {
  usable : list move -> bool;
  corner_readings : list corner -> list corner_slot;
  edge_readings : list edge -> edge -> list edge_slot;
  invariant : cube -> Prop;
  usable_nil : usable [] = true;
  usable_app : forall w u, usable (w ++ u) = andb (usable w) (usable u);
  invariant_generated : forall d, invariant d -> generated d;
  invariant_step : forall w d,
    usable w = true -> invariant d -> invariant (compose (element w) d);
  cdom_covers : forall d cs X,
    invariant d -> corners_done d cs -> ~ In X cs -> In (read_corner d X) (corner_readings cs);
  edom_covers : forall d es Y,
    invariant d -> edges_done d es -> ~ In Y es -> In (read_edge d Y) (edge_readings es Y)
}.

(** What the stages have to check out as, given what is finished already. *)
Fixpoint chain_ok (P : policy) (cs : list corner) (es : list edge)
    (ss : list stage) : bool :=
  match ss with
  | [] => true
  | CornerStage X t b :: r =>
      corner_table_ok t cs es X && forallb (corner_covers t) (corner_readings P cs) &&
      corner_table_bounded t b && negb (corner_inb X cs) &&
      forallb (fun e => usable P (snd e)) t && chain_ok P (X :: cs) es r
  | EdgeStage Y t b :: r =>
      edge_table_ok t cs es Y && forallb (edge_covers t) (edge_readings P es Y) &&
      edge_table_bounded t b && negb (edge_inb Y es) &&
      forallb (fun e => usable P (snd e)) t && chain_ok P cs (Y :: es) r
  end.

(** The longest answer the stages' tables allow, added up over them. *)
Fixpoint chain_bound (ss : list stage) : nat :=
  match ss with
  | [] => 0
  | CornerStage _ _ b :: r => b + chain_bound r
  | EdgeStage _ _ b :: r => b + chain_bound r
  end.

(** A slot in the finished list passes the test, *)
Lemma corner_inb_true X cs : In X cs -> corner_inb X cs = true.
Proof.
  intro H; apply existsb_exists; exists X; split; [exact H | apply Nat.eqb_refl].
Qed.

(** and the same for an edge slot. *)
Lemma edge_inb_true Y es : In Y es -> edge_inb Y es = true.
Proof.
  intro H; apply existsb_exists; exists Y; split; [exact H | apply Nat.eqb_refl].
Qed.

(** Running the stages finishes every slot they name, keeps whatever the
    policy promises, uses only the sequences it allows, and answers within the
    length its tables allow. *)
Lemma chain_correct (P : policy) ss : forall cs es d,
  chain_ok P cs es ss = true -> invariant P d -> corners_done d cs -> edges_done d es ->
  invariant P (chain_state ss d) /\
  corners_done (chain_state ss d) (stage_corners ss ++ cs) /\
  edges_done (chain_state ss d) (stage_edges ss ++ es) /\
  usable P (chain_word ss d) = true /\
  length (chain_word ss d) <= chain_bound ss.
Proof.
  induction ss as [| s ss IH]; intros cs es d Hok Hinv Hc He.
  { simpl; refine (conj Hinv (conj Hc (conj He (conj _ _))));
      [apply (usable_nil P) | simpl; lia]. }
  simpl in Hok |- *.
  destruct s as [X t b | Y t b];
    repeat (apply Bool.andb_true_iff in Hok as [Hok ?]).
  - match goal with H : negb _ = true |- _ => rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HX : ~ In X cs)
      by (intro Hin; rewrite (corner_inb_true X cs Hin) in Hfresh; discriminate).
    assert (Hcov : corner_covers t (read_corner d X) = true).
    { match goal with H : forallb _ (corner_readings P cs) = true |- _ =>
        rewrite forallb_forall in H;
        apply H, (cdom_covers P d cs X Hinv Hc HX) end. }
    assert (Hw : usable P (corner_lookup t (read_corner d X)) = true).
    { match goal with H : forallb _ t = true |- _ =>
        rewrite forallb_forall in H; apply (H _ (corner_lookup_in t _ Hcov)) end. }
    destruct (finish_corner t cs es X d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    destruct (IH (X :: cs) es _ ltac:(assumption)
                 (invariant_step P _ _ Hw Hinv) Hc' He')
      as [Hi' [Hc'' [He'' [Hu Hl]]]].
    pose proof (corner_lookup_bounded t (read_corner d X) b ltac:(assumption) Hcov).
    rewrite <- app_assoc; simpl.
    refine (conj Hi' (conj Hc'' (conj He'' (conj _ _))));
      [rewrite (usable_app P), Hu, Hw; reflexivity
      | rewrite length_app; lia].
  - match goal with H : negb _ = true |- _ => rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HY : ~ In Y es)
      by (intro Hin; rewrite (edge_inb_true Y es Hin) in Hfresh; discriminate).
    assert (Hcov : edge_covers t (read_edge d Y) = true).
    { match goal with H : forallb _ (edge_readings P es Y) = true |- _ =>
        rewrite forallb_forall in H;
        apply H, (edom_covers P d es Y Hinv He HY) end. }
    assert (Hw : usable P (edge_lookup t (read_edge d Y)) = true).
    { match goal with H : forallb _ t = true |- _ =>
        rewrite forallb_forall in H; apply (H _ (edge_lookup_in t _ Hcov)) end. }
    destruct (finish_edge t cs es Y d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    destruct (IH cs (Y :: es) _ ltac:(assumption)
                 (invariant_step P _ _ Hw Hinv) Hc' He')
      as [Hi' [Hc'' [He'' [Hu Hl]]]].
    pose proof (edge_lookup_bounded t (read_edge d Y) b ltac:(assumption) Hcov).
    rewrite <- app_assoc; simpl.
    refine (conj Hi' (conj Hc'' (conj He'' (conj _ _))));
      [rewrite (usable_app P), Hu, Hw; reflexivity
      | rewrite length_app; lia].
Qed.

(** The run with all eighteen moves: any sequence, any reading, and the only
    thing that stays true is that the cube is one some sequence produces. *)
Definition every_word (w : list move) : bool := true.

(** Trivially so, since it allows everything. *)
Lemma every_word_app w u :
  every_word (w ++ u) = andb (every_word w) (every_word u).
Proof. reflexivity. Qed.

(** The policy that run follows. *)
Definition plain : policy.
Proof.
  refine (Policy every_word corner_domain (fun es _ => edge_domain es) generated
                 eq_refl every_word_app (fun d H => H) _ _ _).
  - intros w d _ Hg; apply generated_step, Hg.
  - intros d cs X Hg Hs HX;
      apply in_corner_domain, corner_fresh; auto using generated_wellformed.
  - intros d es Y Hg Hs HY;
      apply in_edge_domain, edge_fresh; auto using generated_wellformed.
Defined.

(** A stage whose slot is already known to hold its own piece needs the table
    to answer only for that piece. *)
Lemma edge_covers_forced t Y d :
  edge_covers t (Y, F0) = true -> edge_covers t (Y, F1) = true ->
  fst (read_edge d Y) = Y -> edge_covers t (read_edge d Y) = true.
Proof.
  intros H0 H1 HY; destruct (read_edge d Y) as [P f]; cbn [fst] in HY; subst P;
    destruct f; assumption.
Qed.

(** Reading a finished-slot list in any order. *)
Lemma corners_done_sub d cs cs' :
  (forall X, In X cs' -> In X cs) -> corners_done d cs -> corners_done d cs'.
Proof. intros H Hs X HX; apply Hs, H, HX. Qed.

(** And the same for edge slots. *)
Lemma edges_done_sub d es es' :
  (forall Y, In Y es' -> In Y es) -> edges_done d es -> edges_done d es'.
Proof. intros H Hs Y HY; apply Hs, H, HY. Qed.
