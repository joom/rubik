From Stdlib Require Import Arith List Lia.
From Rubik Require Export Group Invariant.
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
Definition cslot_eqb (x y : cslot) : bool :=
  if cslot_eq_dec x y then true else false.
Definition eslot_eqb (x y : eslot) : bool :=
  if eslot_eq_dec x y then true else false.

Lemma cslot_eqb_true x y : cslot_eqb x y = true -> x = y.
Proof. unfold cslot_eqb; destruct (cslot_eq_dec x y); congruence. Qed.
Lemma eslot_eqb_true x y : eslot_eqb x y = true -> x = y.
Proof. unfold eslot_eqb; destruct (eslot_eq_dec x y); congruence. Qed.
Lemma cslot_eqb_refl x : cslot_eqb x x = true.
Proof. unfold cslot_eqb; destruct (cslot_eq_dec x x); congruence. Qed.
Lemma eslot_eqb_refl x : eslot_eqb x x = true.
Proof. unfold eslot_eqb; destruct (eslot_eq_dec x x); congruence. Qed.

(** The slots a cube already has right. *)
Definition solvedc (d : cube) (cs : list corner) : Prop :=
  forall X, In X cs -> getc d X = (X, T0).
Definition solvede (d : cube) (es : list edge) : Prop :=
  forall Y, In Y es -> gete d Y = (Y, F0).

(** Composing on the left leaves a finished slot finished, provided the
    sequence's own cube holds that piece at home. *)
Lemma solvedc_keep d h cs :
  solvedc d cs -> (forall X, In X cs -> getc h X = (X, T0)) ->
  solvedc (ccompose h d) cs.
Proof.
  intros Hd Hh X HX; rewrite getc_ccompose, (Hd X HX).
  apply capply_fixesc, Hh, HX.
Qed.

Lemma solvede_keep d h es :
  solvede d es -> (forall Y, In Y es -> gete h Y = (Y, F0)) ->
  solvede (ccompose h d) es.
Proof.
  intros Hd Hh Y HY; rewrite gete_ccompose, (Hd Y HY).
  apply eapply_fixese, Hh, HY.
Qed.

(** * Tables

    A table answers, for each reading a slot might show, with a sequence that
    brings that slot home without disturbing the ones already done. *)

Definition ctable := list (cslot * list move).
Definition etable := list (eslot * list move).

Fixpoint clookup (t : ctable) (v : cslot) : list move :=
  match t with
  | [] => []
  | (u, w) :: r => if cslot_eqb u v then w else clookup r v
  end.

Fixpoint elookup (t : etable) (v : eslot) : list move :=
  match t with
  | [] => []
  | (u, w) :: r => if eslot_eqb u v then w else elookup r v
  end.

Definition ccovers (t : ctable) (v : cslot) : bool :=
  existsb (fun e => cslot_eqb (fst e) v) t.
Definition ecovers (t : etable) (v : eslot) : bool :=
  existsb (fun e => eslot_eqb (fst e) v) t.

Lemma clookup_in t v : ccovers t v = true -> In (v, clookup t v) t.
Proof.
  unfold ccovers; induction t as [| [u w] t IH]; simpl; [discriminate |].
  destruct (cslot_eqb u v) eqn:E; simpl; [intros _ | intro H].
  - left; rewrite (cslot_eqb_true u v E); reflexivity.
  - right; apply IH, H.
Qed.

Lemma elookup_in t v : ecovers t v = true -> In (v, elookup t v) t.
Proof.
  unfold ecovers; induction t as [| [u w] t IH]; simpl; [discriminate |].
  destruct (eslot_eqb u v) eqn:E; simpl; [intros _ | intro H].
  - left; rewrite (eslot_eqb_true u v E); reflexivity.
  - right; apply IH, H.
Qed.

(** What a table has to satisfy: every sequence in it leaves the finished
    slots alone and brings its own reading home. Both are computations on the
    cube the sequence denotes. *)
Definition ctable_ok (t : ctable) (cs : list corner) (es : list edge)
    (X : corner) : bool :=
  forallb (fun e =>
    let w := snd e in
    andb (forallb (fun Y => cslot_eqb (getc (element w) Y) (Y, T0)) cs)
    (andb (forallb (fun Y => eslot_eqb (gete (element w) Y) (Y, F0)) es)
          (cslot_eqb (capply (element w) (fst e)) (X, T0)))) t.

Definition etable_ok (t : etable) (cs : list corner) (es : list edge)
    (Y : edge) : bool :=
  forallb (fun e =>
    let w := snd e in
    andb (forallb (fun X => cslot_eqb (getc (element w) X) (X, T0)) cs)
    (andb (forallb (fun Z => eslot_eqb (gete (element w) Z) (Z, F0)) es)
          (eslot_eqb (eapply (element w) (fst e)) (Y, F0)))) t.

(** One step of the method. *)
Lemma cstep t cs es X d :
  ctable_ok t cs es X = true -> ccovers t (getc d X) = true ->
  solvedc d cs -> solvede d es ->
  solvedc (ccompose (element (clookup t (getc d X))) d) (X :: cs) /\
  solvede (ccompose (element (clookup t (getc d X))) d) es.
Proof.
  intros Hok Hcov Hc He.
  set (w := clookup t (getc d X)).
  pose proof (clookup_in t (getc d X) Hcov) as Hin.
  unfold ctable_ok in Hok; rewrite forallb_forall in Hok.
  specialize (Hok _ Hin); cbn [fst snd] in Hok.
  apply Bool.andb_true_iff in Hok as [H1 Hok].
  apply Bool.andb_true_iff in Hok as [H2 H3].
  rewrite forallb_forall in H1, H2.
  assert (Hfc : forall Y, In Y cs -> getc (element w) Y = (Y, T0))
    by (intros Y HY; apply cslot_eqb_true, H1, HY).
  assert (Hfe : forall Y, In Y es -> gete (element w) Y = (Y, F0))
    by (intros Y HY; apply eslot_eqb_true, H2, HY).
  split; [| apply solvede_keep; auto].
  intros Y [<- | HY].
  - rewrite getc_ccompose; apply cslot_eqb_true, H3.
  - apply (solvedc_keep d (element w) cs Hc Hfc Y HY).
Qed.

Lemma estep t cs es Y d :
  etable_ok t cs es Y = true -> ecovers t (gete d Y) = true ->
  solvedc d cs -> solvede d es ->
  solvedc (ccompose (element (elookup t (gete d Y))) d) cs /\
  solvede (ccompose (element (elookup t (gete d Y))) d) (Y :: es).
Proof.
  intros Hok Hcov Hc He.
  set (w := elookup t (gete d Y)).
  pose proof (elookup_in t (gete d Y) Hcov) as Hin.
  unfold etable_ok in Hok; rewrite forallb_forall in Hok.
  specialize (Hok _ Hin); cbn [fst snd] in Hok.
  apply Bool.andb_true_iff in Hok as [H1 Hok].
  apply Bool.andb_true_iff in Hok as [H2 H3].
  rewrite forallb_forall in H1, H2.
  assert (Hfc : forall X, In X cs -> getc (element w) X = (X, T0))
    by (intros X HX; apply cslot_eqb_true, H1, HX).
  assert (Hfe : forall Z, In Z es -> gete (element w) Z = (Z, F0))
    by (intros Z HZ; apply eslot_eqb_true, H2, HZ).
  split; [apply solvedc_keep; auto |].
  intros Z [<- | HZ].
  - rewrite gete_ccompose; apply eslot_eqb_true, H3.
  - apply (solvede_keep d (element w) es He Hfe Z HZ).
Qed.

(** * Which readings a slot can show

    A finished slot holds its own piece, so no unfinished slot can hold one of
    those pieces: the pieces of a reachable cube are all different. *)

Lemma corner_rank_inj X Y : corner_rank X = corner_rank Y -> X = Y.
Proof. destruct X, Y; simpl; congruence. Qed.

Lemma edge_rank_inj X Y : edge_rank X = edge_rank Y -> X = Y.
Proof. destruct X, Y; simpl; congruence. Qed.

Lemma getc_nth d X : fst (getc d X) = nth (corner_rank X) (corner_pieces d) URF.
Proof. destruct X; reflexivity. Qed.

Lemma gete_nth d Y : fst (gete d Y) = nth (edge_rank Y) (edge_pieces d) UR.
Proof. destruct Y; reflexivity. Qed.

Lemma corner_pieces_length d : length (corner_pieces d) = 8.
Proof. reflexivity. Qed.

Lemma edge_pieces_length d : length (edge_pieces d) = 12.
Proof. reflexivity. Qed.

Lemma corner_rank_lt X : corner_rank X < 8.
Proof. destruct X; simpl; lia. Qed.

Lemma edge_rank_lt Y : edge_rank Y < 12.
Proof. destruct Y; simpl; lia. Qed.

(** Distinct slots of a duplicate-free cube hold distinct pieces. *)
Lemma corner_slot_inj d X Y :
  NoDup (cranks d) -> fst (getc d X) = fst (getc d Y) -> X = Y.
Proof.
  intros H E; apply NoDup_map_inv in H.
  rewrite NoDup_nth in H.
  apply corner_rank_inj, (H (corner_rank X) (corner_rank Y));
    [ rewrite corner_pieces_length; apply corner_rank_lt
    | rewrite corner_pieces_length; apply corner_rank_lt
    | rewrite <- !getc_nth; exact E ].
Qed.

Lemma edge_slot_inj d X Y :
  NoDup (eranks d) -> fst (gete d X) = fst (gete d Y) -> X = Y.
Proof.
  intros H E; apply NoDup_map_inv in H.
  rewrite NoDup_nth in H.
  apply edge_rank_inj, (H (edge_rank X) (edge_rank Y));
    [ rewrite edge_pieces_length; apply edge_rank_lt
    | rewrite edge_pieces_length; apply edge_rank_lt
    | rewrite <- !gete_nth; exact E ].
Qed.

(** So an unfinished slot never shows a finished slot's piece. *)
Lemma corner_fresh d cs X :
  wellformed d -> solvedc d cs -> ~ In X cs -> ~ In (fst (getc d X)) cs.
Proof.
  intros [Hnd _] Hs HX Hin.
  assert (E : fst (getc d X) = fst (getc d (fst (getc d X))))
    by (rewrite (Hs _ Hin); reflexivity).
  apply HX; rewrite (corner_slot_inj d X _ Hnd E); exact Hin.
Qed.

Lemma edge_fresh d es Y :
  wellformed d -> solvede d es -> ~ In Y es -> ~ In (fst (gete d Y)) es.
Proof.
  intros [_ Hnd] Hs HY Hin.
  assert (E : fst (gete d Y) = fst (gete d (fst (gete d Y))))
    by (rewrite (Hs _ Hin); reflexivity).
  apply HY; rewrite (edge_slot_inj d Y _ Hnd E); exact Hin.
Qed.

(** Every reading of a corner slot, and of an edge slot. *)
Definition all_cslots : list cslot :=
  [(URF,T0);(URF,T1);(URF,T2);(UFL,T0);(UFL,T1);(UFL,T2);
   (ULB,T0);(ULB,T1);(ULB,T2);(UBR,T0);(UBR,T1);(UBR,T2);
   (DFR,T0);(DFR,T1);(DFR,T2);(DLF,T0);(DLF,T1);(DLF,T2);
   (DBL,T0);(DBL,T1);(DBL,T2);(DRB,T0);(DRB,T1);(DRB,T2)].

Definition all_eslots : list eslot :=
  [(UR,F0);(UR,F1);(UF,F0);(UF,F1);(UL,F0);(UL,F1);(UB,F0);(UB,F1);
   (DR,F0);(DR,F1);(DF,F0);(DF,F1);(DL,F0);(DL,F1);(DB,F0);(DB,F1);
   (FR,F0);(FR,F1);(FL,F0);(FL,F1);(BL,F0);(BL,F1);(BR,F0);(BR,F1)].

Lemma all_cslots_complete v : In v all_cslots.
Proof. destruct v as [X t]; destruct X, t; simpl; tauto. Qed.

Lemma all_eslots_complete v : In v all_eslots.
Proof. destruct v as [Y f]; destruct Y, f; simpl; tauto. Qed.

(** The readings a slot can still show once the listed slots are finished. *)
Definition corner_inb (X : corner) (cs : list corner) : bool :=
  existsb (fun Y => Nat.eqb (corner_rank X) (corner_rank Y)) cs.
Definition edge_inb (Y : edge) (es : list edge) : bool :=
  existsb (fun Z => Nat.eqb (edge_rank Y) (edge_rank Z)) es.

Lemma corner_inb_false X cs : ~ In X cs -> corner_inb X cs = false.
Proof.
  intro H; apply Bool.not_true_is_false; intro E.
  apply existsb_exists in E as [Y [HY HE]]; apply Nat.eqb_eq, corner_rank_inj in HE.
  subst; contradiction.
Qed.

Lemma edge_inb_false Y es : ~ In Y es -> edge_inb Y es = false.
Proof.
  intro H; apply Bool.not_true_is_false; intro E.
  apply existsb_exists in E as [Z [HZ HE]]; apply Nat.eqb_eq, edge_rank_inj in HE.
  subst; contradiction.
Qed.

Definition cdomain (cs : list corner) : list cslot :=
  filter (fun v => negb (corner_inb (fst v) cs)) all_cslots.
Definition edomain (es : list edge) : list eslot :=
  filter (fun v => negb (edge_inb (fst v) es)) all_eslots.

Lemma in_cdomain v cs : ~ In (fst v) cs -> In v (cdomain cs).
Proof.
  intro H; apply filter_In; split;
    [apply all_cslots_complete | rewrite (corner_inb_false _ _ H); reflexivity].
Qed.

Lemma in_edomain v es : ~ In (fst v) es -> In v (edomain es).
Proof.
  intro H; apply filter_In; split;
    [apply all_eslots_complete | rewrite (edge_inb_false _ _ H); reflexivity].
Qed.

(** A table that answers for every reading still possible answers for the one
    the cube actually shows. *)
Lemma ccovers_of t cs X d :
  forallb (ccovers t) (cdomain cs) = true ->
  wellformed d -> solvedc d cs -> ~ In X cs -> ccovers t (getc d X) = true.
Proof.
  intros Hall Hw Hs HX; rewrite forallb_forall in Hall.
  apply Hall, in_cdomain, corner_fresh; auto.
Qed.

Lemma ecovers_of t es Y d :
  forallb (ecovers t) (edomain es) = true ->
  wellformed d -> solvede d es -> ~ In Y es -> ecovers t (gete d Y) = true.
Proof.
  intros Hall Hw Hs HY; rewrite forallb_forall in Hall.
  apply Hall, in_edomain, edge_fresh; auto.
Qed.

(** * Finishing

    All twenty slots right is the solved cube, and the last slot of each kind
    needs no table: its piece is the only one left and its orientation is
    forced by the totals. *)

Definition all_corner_slots : list corner :=
  [URF; UFL; ULB; UBR; DFR; DLF; DBL; DRB].
Definition all_edge_slots : list edge :=
  [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL; BL; BR].

Lemma solved_everywhere d :
  solvedc d all_corner_slots -> solvede d all_edge_slots -> d = csolved.
Proof.
  intros Hc He; apply cube_ext.
  - intro X; rewrite getc_csolved; apply Hc; destruct X; simpl; tauto.
  - intro Y; rewrite gete_csolved; apply He; destruct Y; simpl; tauto.
Qed.

(** The eighth corner holds the only piece left, unturned because the
    rotations of a reachable cube cancel. *)
Lemma last_corner d :
  wellformed d -> twist_total d = T0 ->
  solvedc d [URF; UFL; ULB; UBR; DFR; DLF; DBL] ->
  getc d DRB = (DRB, T0).
Proof.
  intros Hw Ht Hs.
  assert (Hfr : ~ In (fst (getc d DRB)) [URF; UFL; ULB; UBR; DFR; DLF; DBL])
    by (apply corner_fresh; auto; simpl; intuition discriminate).
  pose proof (Hs URF ltac:(simpl; tauto)) as H0.
  pose proof (Hs UFL ltac:(simpl; tauto)) as H1.
  pose proof (Hs ULB ltac:(simpl; tauto)) as H2.
  pose proof (Hs UBR ltac:(simpl; tauto)) as H3.
  pose proof (Hs DFR ltac:(simpl; tauto)) as H4.
  pose proof (Hs DLF ltac:(simpl; tauto)) as H5.
  pose proof (Hs DBL ltac:(simpl; tauto)) as H6.
  cbn [getc] in Hfr, H0, H1, H2, H3, H4, H5, H6 |- *.
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
  solvede d [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL; BL] ->
  gete d BR = (BR, F0).
Proof.
  intros Hw Hf Hs.
  assert (Hfr : ~ In (fst (gete d BR)) [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL; BL])
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
  cbn [gete] in Hfr, H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.
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
  wellformed d -> cparity d = false ->
  solvedc d all_corner_slots ->
  solvede d [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL] ->
  fst (gete d BL) = BL.
Proof.
  intros Hw Hp Hc He.
  assert (HBL : ~ In (fst (gete d BL)) [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL])
    by (apply edge_fresh; auto; simpl; intuition discriminate).
  assert (HBR : ~ In (fst (gete d BR)) [UR; UF; UL; UB; DR; DF; DL; DB; FR; FL])
    by (apply edge_fresh; auto; simpl; intuition discriminate).
  assert (Hne : fst (gete d BL) <> fst (gete d BR))
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
  cbn [getc gete] in HBL, HBR, Hne, C0, C1, C2, C3, C4, C5, C6, C7,
                     E0, E1, E2, E3, E4, E5, E6, E7, E8, E9 |- *.
  destruct (yBL d) as [P f] eqn:EL; destruct (yBR d) as [Q g] eqn:ER.
  cbn [fst] in HBL, HBR, Hne |- *.
  destruct P; try (simpl in HBL; tauto); try reflexivity.
  exfalso; destruct Q; try (simpl in HBR; tauto); try congruence.
  unfold cparity, cranks, eranks, corner_pieces, edge_pieces,
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

Lemma generated_step w d : generated d -> generated (ccompose (element w) d).
Proof. intros [q <-]; exists (w ++ q); apply element_app. Qed.

Lemma generated_csolvable c : csolvable c -> generated c.
Proof. apply csolvable_element. Qed.

Lemma generated_wellformed d : generated d -> wellformed d.
Proof. intros [q <-]; apply wellformed_element. Qed.

Lemma generated_cparity d : generated d -> cparity d = false.
Proof. intros [q <-]; apply cparity_element. Qed.

Lemma generated_twist d : generated d -> twist_total d = T0.
Proof. intros [q <-]; unfold element; apply twist_total_crun. Qed.

Lemma generated_flip d : generated d -> flip_total d = F0.
Proof. intros [q <-]; unfold element; apply flip_total_crun. Qed.

(** Two steps in a row are one step with the sequences joined. *)
Lemma ccompose_steps w u d :
  ccompose (element w) (ccompose (element u) d) = ccompose (element (w ++ u)) d.
Proof. rewrite element_app, ccompose_assoc; reflexivity. Qed.

(** A sequence that solves a cube from the left solves it from the right, so
    the method's sequence is a solution in the ordinary sense. *)
Lemma solution_of_left c W :
  csolvable c -> ccompose (element W) c = csolved -> crun c W = csolved.
Proof.
  intros [p Hp] HW; rewrite crun_by_element.
  rewrite crun_by_element in Hp.
  assert (E : element W = element p).
  { rewrite <- (ccompose_id_r (element W)), <- Hp, <- ccompose_assoc, HW.
    apply ccompose_id_l. }
  rewrite E; exact Hp.
Qed.

(** * How long the answer is *)

Definition ctable_bounded (t : ctable) (b : nat) : bool :=
  forallb (fun e => Nat.leb (length (snd e)) b) t.
Definition etable_bounded (t : etable) (b : nat) : bool :=
  forallb (fun e => Nat.leb (length (snd e)) b) t.

Lemma clookup_bounded t v b :
  ctable_bounded t b = true -> ccovers t v = true -> length (clookup t v) <= b.
Proof.
  intros Hb Hc; unfold ctable_bounded in Hb; rewrite forallb_forall in Hb.
  apply Nat.leb_le, (Hb _ (clookup_in t v Hc)).
Qed.

Lemma elookup_bounded t v b :
  etable_bounded t b = true -> ecovers t v = true -> length (elookup t v) <= b.
Proof.
  intros Hb Hc; unfold etable_bounded in Hb; rewrite forallb_forall in Hb.
  apply Nat.leb_le, (Hb _ (elookup_in t v Hc)).
Qed.

(** * Running the whole method

    The stages differ only in which slot they finish and which table they
    consult, so the method is a fold over a list of them. What each stage may
    assume is what the stages before it established, which is why the check
    below carries the finished slots along. *)

Inductive stage :=
| Cstage (X : corner) (t : ctable) (b : nat)
| Estage (Y : edge) (t : etable) (b : nat).

(** The cube after running the stages. *)
Fixpoint chain_state (ss : list stage) (d : cube) : cube :=
  match ss with
  | [] => d
  | Cstage X t _ :: r => chain_state r (ccompose (element (clookup t (getc d X))) d)
  | Estage Y t _ :: r => chain_state r (ccompose (element (elookup t (gete d Y))) d)
  end.

(** And the sequence that gets there. Later stages compose on the left, so
    their sequences come first. *)
Fixpoint chain_word (ss : list stage) (d : cube) : list move :=
  match ss with
  | [] => []
  | Cstage X t _ :: r =>
      let w := clookup t (getc d X) in chain_word r (ccompose (element w) d) ++ w
  | Estage Y t _ :: r =>
      let w := elookup t (gete d Y) in chain_word r (ccompose (element w) d) ++ w
  end.

Lemma chain_state_word ss : forall d,
  ccompose (element (chain_word ss d)) d = chain_state ss d.
Proof.
  induction ss as [| s ss IH]; intro d; simpl;
    [rewrite element_nil; apply ccompose_id_l |].
  destruct s; rewrite element_app, ccompose_assoc; apply IH.
Qed.

(** The slots the stages finish. *)
Fixpoint stagesc (ss : list stage) : list corner :=
  match ss with
  | [] => []
  | Cstage X _ _ :: r => stagesc r ++ [X]
  | Estage _ _ _ :: r => stagesc r
  end.

Fixpoint stagese (ss : list stage) : list edge :=
  match ss with
  | [] => []
  | Cstage _ _ _ :: r => stagese r
  | Estage Y _ _ :: r => stagese r ++ [Y]
  end.

(** What the stages have to check out as, given what is finished already. *)
Fixpoint chain_ok (cs : list corner) (es : list edge) (ss : list stage) : bool :=
  match ss with
  | [] => true
  | Cstage X t b :: r =>
      ctable_ok t cs es X && forallb (ccovers t) (cdomain cs) &&
      ctable_bounded t b && negb (corner_inb X cs) && chain_ok (X :: cs) es r
  | Estage Y t b :: r =>
      etable_ok t cs es Y && forallb (ecovers t) (edomain es) &&
      etable_bounded t b && negb (edge_inb Y es) && chain_ok cs (Y :: es) r
  end.

Fixpoint chain_bound (ss : list stage) : nat :=
  match ss with
  | [] => 0
  | Cstage _ _ b :: r => b + chain_bound r
  | Estage _ _ b :: r => b + chain_bound r
  end.

Lemma corner_inb_true X cs : In X cs -> corner_inb X cs = true.
Proof.
  intro H; apply existsb_exists; exists X; split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma edge_inb_true Y es : In Y es -> edge_inb Y es = true.
Proof.
  intro H; apply existsb_exists; exists Y; split; [exact H | apply Nat.eqb_refl].
Qed.

(** Running the stages finishes every slot they name, and finishes no cube
    that was not already a cube some sequence produces. *)
Lemma chain_correct ss : forall cs es d,
  chain_ok cs es ss = true -> generated d -> solvedc d cs -> solvede d es ->
  generated (chain_state ss d) /\
  solvedc (chain_state ss d) (stagesc ss ++ cs) /\
  solvede (chain_state ss d) (stagese ss ++ es).
Proof.
  induction ss as [| s ss IH]; intros cs es d Hok Hg Hc He; simpl in *;
    [repeat split; auto |].
  destruct s as [X t b | Y t b];
    repeat (apply Bool.andb_true_iff in Hok as [Hok ?]).
  - match goal with H : negb _ = true |- _ =>
      rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HX : ~ In X cs)
      by (intro Hin; rewrite (corner_inb_true X cs Hin) in Hfresh; discriminate).
    assert (Hcov : ccovers t (getc d X) = true)
      by (eapply ccovers_of; eauto using generated_wellformed).
    destruct (cstep t cs es X d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    destruct (IH (X :: cs) es _ ltac:(assumption)
                 (generated_step _ _ Hg) Hc' He') as [Hg'' [Hc'' He'']].
    rewrite <- app_assoc; simpl; repeat split; assumption.
  - match goal with H : negb _ = true |- _ =>
      rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HY : ~ In Y es)
      by (intro Hin; rewrite (edge_inb_true Y es Hin) in Hfresh; discriminate).
    assert (Hcov : ecovers t (gete d Y) = true)
      by (eapply ecovers_of; eauto using generated_wellformed).
    destruct (estep t cs es Y d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    destruct (IH cs (Y :: es) _ ltac:(assumption)
                 (generated_step _ _ Hg) Hc' He') as [Hg'' [Hc'' He'']].
    rewrite <- app_assoc; simpl; repeat split; assumption.
Qed.

(** And the answer is no longer than the tables allow. *)
Lemma chain_length ss : forall cs es d,
  chain_ok cs es ss = true -> generated d -> solvedc d cs -> solvede d es ->
  length (chain_word ss d) <= chain_bound ss.
Proof.
  induction ss as [| s ss IH]; intros cs es d Hok Hg Hc He; simpl in *; [lia |].
  destruct s as [X t b | Y t b];
    repeat (apply Bool.andb_true_iff in Hok as [Hok ?]).
  - match goal with H : negb _ = true |- _ => rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HX : ~ In X cs)
      by (intro Hin; rewrite (corner_inb_true X cs Hin) in Hfresh; discriminate).
    assert (Hcov : ccovers t (getc d X) = true)
      by (eapply ccovers_of; eauto using generated_wellformed).
    destruct (cstep t cs es X d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    rewrite length_app.
    pose proof (clookup_bounded t (getc d X) b ltac:(assumption) Hcov).
    pose proof (IH (X :: cs) es _ ltac:(assumption)
                   (generated_step _ _ Hg) Hc' He'); lia.
  - match goal with H : negb _ = true |- _ => rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HY : ~ In Y es)
      by (intro Hin; rewrite (edge_inb_true Y es Hin) in Hfresh; discriminate).
    assert (Hcov : ecovers t (gete d Y) = true)
      by (eapply ecovers_of; eauto using generated_wellformed).
    destruct (estep t cs es Y d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    rewrite length_app.
    pose proof (elookup_bounded t (gete d Y) b ltac:(assumption) Hcov).
    pose proof (IH cs (Y :: es) _ ltac:(assumption)
                   (generated_step _ _ Hg) Hc' He'); lia.
Qed.

(** A stage whose slot is already known to hold its own piece needs the table
    to answer only for that piece. *)
Lemma ecovers_forced t Y d :
  ecovers t (Y, F0) = true -> ecovers t (Y, F1) = true ->
  fst (gete d Y) = Y -> ecovers t (gete d Y) = true.
Proof.
  intros H0 H1 HY; destruct (gete d Y) as [P f]; cbn [fst] in HY; subst P;
    destruct f; assumption.
Qed.

(** Adding one more finished slot to the list. *)
Lemma solvedc_cons d X cs :
  getc d X = (X, T0) -> solvedc d cs -> solvedc d (X :: cs).
Proof. intros H Hs Y [<- | HY]; auto. Qed.

Lemma solvede_cons d Y es :
  gete d Y = (Y, F0) -> solvede d es -> solvede d (Y :: es).
Proof. intros H Hs Z [<- | HZ]; auto. Qed.

(** Reading a finished-slot list in any order. *)
Lemma solvedc_sub d cs cs' :
  (forall X, In X cs' -> In X cs) -> solvedc d cs -> solvedc d cs'.
Proof. intros H Hs X HX; apply Hs, H, HX. Qed.

Lemma solvede_sub d es es' :
  (forall Y, In Y es' -> In Y es) -> solvede d es -> solvede d es'.
Proof. intros H Hs Y HY; apply Hs, H, HY. Qed.
