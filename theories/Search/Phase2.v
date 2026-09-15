From Stdlib Require Import Arith List Lia Permutation.
From Rubik Require Export Search.Phase1.
Import ListNotations.

(** * The second phase

    From inside the subgroup, finish the cube using only the ten moves that
    keep it there. Three more tables bound how far the pieces still have to
    travel. *)

(** The tables the second phase prunes with. *)
Record tables2 :=
  Tables2 { t_cornerperm : table; t_udperm : table; t_sliceperm : table }.

(** Gathered when the solver runs, not when the program loads, so the tables
    are built before they are read. *)
Definition build_tables2 (u : unit) : tables2 :=
  Tables2 cornerperm_table udperm_table sliceperm_table.

(** How far the pieces still have to travel, as far as any one table can tell. *)
Definition estimate2 (T : tables2) (c : cube) : nat :=
  Nat.max (table_get (t_cornerperm T) (cornerperm_index c))
    (Nat.max (table_get (t_udperm T) (udperm_index c))
       (table_get (t_sliceperm T) (sliceperm_index c))).

(** The moves the second phase may still try after a given move. *)
Definition allowed_moves2 (prev : option move) : list move :=
  filter (allowed prev) phase2_moves.

(** Take the first move that solves the cube within the remaining depth. *)
Fixpoint search2 (T : tables2) (d : nat) (prev : option move) (c : cube)
  : option (list move) :=
  if cube_eqb c csolved then Some []
  else
    match d with
    | 0 => None
    | S d' =>
        if Nat.leb (estimate2 T c) d then
          choose_move (fun m => search2 T d' (Some m) (cturn m c)) (allowed_moves2 prev)
        else None
    end.

(** Anything the second phase returns really solves the cube. *)
Theorem search2_sound T d prev c p :
  search2 T d prev c = Some p -> crun c p = csolved /\ length p <= d.
Proof.
  revert prev c p; induction d as [| d IH]; intros prev c p; cbn [search2];
    destruct (cube_eqb c csolved) eqn:E.
  - intro H; inversion H; subst; simpl;
      split; [apply cube_eqb_spec; auto | auto].
  - discriminate.
  - intro H; inversion H; subst; simpl;
      split; [apply cube_eqb_spec; auto | auto with arith].
  - destruct (Nat.leb (estimate2 T c) (S d)); [| discriminate].
    intro H; destruct (choose_move_sound _ _ _ H) as [m [q [Hin [Hr ->]]]].
    destruct (IH _ _ _ Hr) as [Hrun Hlen]; simpl; split; [| lia].
    exact Hrun.
Qed.

(** Try depths in turn until the cube comes out solved. *)
Fixpoint deepen2 (T : tables2) (fuel depth : nat) (c : cube)
  : option (list move) :=
  match search2 T depth None c with
  | Some p => Some p
  | None =>
      match fuel with
      | 0 => None
      | S n => deepen2 T n (S depth) c
      end
  end.

(** The second phase, searching as deep as it is allowed. *)
Definition phase2 (T : tables2) (limit : nat) (c : cube) : option (list move) :=
  deepen2 T limit 0 c.

(** Whatever it returns really solves the cube it was given. *)
Theorem phase2_sound T limit c p : phase2 T limit c = Some p -> crun c p = csolved.
Proof.
  unfold phase2; generalize 0 as d; revert p.
  induction limit as [| limit IH]; intros p d; cbn [deepen2];
    destruct (search2 T d None c) as [q |] eqn:E; try discriminate;
    try (intro H; inversion H; subst; exact (proj1 (search2_sound _ _ _ _ _ E))).
  apply IH.
Qed.

(** * Why the second phase always finds something

    The same argument as for the first phase, with two differences. Only ten
    moves are allowed, so the rewriting has to stay inside them; and the
    coordinates are placements rather than rotations, so their spaces are
    rearrangements and a cube only belongs to one if it can be solved at
    all. *)

(** The ten moves are exactly the ones the second phase may use. *)
Lemma phase2_moves_complete m : phase2_move m = true -> In m phase2_moves.
Proof.
  destruct m as [f t]; destruct f, t; try discriminate; intros _; simpl; tauto.
Qed.

(** Two half turns of a face undo each other. *)
Lemma half_turn_involutive f c : cturn (f, Half) (cturn (f, Half) c) = c.
Proof.
  apply paint_inj; rewrite !paint_cturn; unfold_moves; apply quarter_four.
Qed.

(** Merging two allowed turns of one face yields an allowed turn, or nothing:
    the free faces allow every amount, and the others only the half turn,
    which is its own inverse. *)
Lemma phase2_move_merge f t1 t2 :
  phase2_move (f, t1) = true -> phase2_move (f, t2) = true ->
  (forall c, cturn (f, t2) (cturn (f, t1) c) = c) \/
  (exists t3, phase2_move (f, t3) = true /\
     forall c, cturn (f, t2) (cturn (f, t1) c) = cturn (f, t3) c).
Proof.
  assert (free : forall f, (f = Up \/ f = Down) ->
    (forall c, cturn (f, t2) (cturn (f, t1) c) = c) \/
    (exists t3, phase2_move (f, t3) = true /\
       forall c, cturn (f, t2) (cturn (f, t1) c) = cturn (f, t3) c)).
  { intros g Hg; destruct (csame_face_merge g t1 t2) as [H | [t3 H]];
      [left; exact H |].
    right; exists t3; split; [| exact H].
    destruct Hg as [-> | ->]; destruct t3; reflexivity. }
  destruct f; intros H1 H2; try (apply free; auto; fail);
    destruct t1, t2; try discriminate; left; apply half_turn_involutive.
Qed.

(** Rewriting a sequence of allowed moves into a canonical one that is still
    made of allowed moves. *)
Lemma normalise_phase2 p :
  Forall (fun m => phase2_move m = true) p ->
  exists q, canonical None q /\ Forall (fun m => phase2_move m = true) q /\
    (forall c, crun c q = crun c p) /\ length q <= length p.
Proof.
  apply (canonical_exists cube cturn phase2_move
           (fun f t1 t2 H1 H2 => phase2_move_merge f t1 t2 H1 H2)
           (fun f g t1 t2 Hop c => cmove_comm f g t1 t2 c Hop)).
Qed.

(** A move rearranges the corners, whatever else it does. *)
Lemma corner_pieces_perm m c : Permutation (corner_pieces c) (corner_pieces (cturn m c)).
Proof.
  destruct_cube c; destruct m as [f t]; destruct f, t;
    unfold corner_pieces; cbn [corner_slots cturn cquarter
      xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB map];
    rewrite ?cshift_fst; cbn [fst];
    apply (Permutation_count_occ corner_eq_dec); intro x; cbn;
    repeat (destruct (corner_eq_dec _ x)); lia.
Qed.

(** An allowed move rearranges each group of edges within itself. *)
Lemma ud_pieces_perm m c :
  phase2_move m = true -> Permutation (ud_pieces c) (ud_pieces (cturn m c)).
Proof.
  destruct_cube c; destruct m as [f t]; destruct f, t; try discriminate; intros _;
    unfold ud_pieces, edge_pieces; cbn [edge_slots cturn cquarter
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map firstn];
    rewrite ?eshift_fst; cbn [fst];
    apply (Permutation_count_occ edge_eq_dec); intro x; cbn;
    repeat (destruct (edge_eq_dec _ x)); lia.
Qed.

(** and the slice edges within the slice. *)
Lemma slice_pieces_perm m c :
  phase2_move m = true -> Permutation (slice_pieces c) (slice_pieces (cturn m c)).
Proof.
  destruct_cube c; destruct m as [f t]; destruct f, t; try discriminate; intros _;
    unfold slice_pieces, edge_pieces; cbn [edge_slots cturn cquarter
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map skipn];
    rewrite ?eshift_fst; cbn [fst];
    apply (Permutation_count_occ edge_eq_dec); intro x; cbn;
    repeat (destruct (edge_eq_dec _ x)); lia.
Qed.

(** So a whole sequence rearranges them, and a cube that can be solved sits in
    the space of rearrangements its coordinate tables were built over. *)
Lemma corner_pieces_crun_perm c q :
  Permutation (corner_pieces c) (corner_pieces (crun c q)).
Proof.
  revert c; induction q as [| m q IH]; intro c; [apply Permutation_refl |].
  apply perm_trans with (corner_pieces (cturn m c)); [apply corner_pieces_perm | apply IH].
Qed.

(** The same for the outer edges, *)
Lemma ud_pieces_crun_perm c q :
  Forall (fun m => phase2_move m = true) q ->
  Permutation (ud_pieces c) (ud_pieces (crun c q)).
Proof.
  revert c; induction q as [| m q IH]; intros c H; [apply Permutation_refl |].
  inversion H; subst; apply perm_trans with (ud_pieces (cturn m c));
    [apply ud_pieces_perm; auto | apply IH; auto].
Qed.

(** and for the slice edges. *)
Lemma slice_pieces_crun_perm c q :
  Forall (fun m => phase2_move m = true) q ->
  Permutation (slice_pieces c) (slice_pieces (crun c q)).
Proof.
  revert c; induction q as [| m q IH]; intros c H; [apply Permutation_refl |].
  inversion H; subst; apply perm_trans with (slice_pieces (cturn m c));
    [apply slice_pieces_perm; auto | apply IH; auto].
Qed.

(** A sequence that solves the cube is, read one coordinate at a time, a path
    of the same length to that coordinate's goal. *)
Lemma cornerperm_reaches c q :
  Forall (fun m => phase2_move m = true) q -> crun c q = csolved ->
  reaches cornerperm_step cornerperm_goal (length q) (corner_pieces c).
Proof.
  revert c; induction q as [| m q IH]; intros c Hf H;
    unfold crun in H; cbn [fold_left] in H; simpl.
  - apply reaches_goal; rewrite H; reflexivity.
  - inversion Hf; subst; apply reaches_step with (corner_pieces (cturn m c));
      [| apply IH; auto].
    rewrite corner_pieces_cturn; apply in_map_iff;
      exists m; split; [reflexivity | apply phase2_moves_complete; auto].
Qed.

(** The same for the outer edge placement, *)
Lemma udperm_reaches c q :
  Forall (fun m => phase2_move m = true) q -> crun c q = csolved ->
  reaches udperm_step udperm_goal (length q) (ud_pieces c).
Proof.
  revert c; induction q as [| m q IH]; intros c Hf H;
    unfold crun in H; cbn [fold_left] in H; simpl.
  - apply reaches_goal; rewrite H; reflexivity.
  - inversion Hf; subst; apply reaches_step with (ud_pieces (cturn m c));
      [| apply IH; auto].
    rewrite ud_pieces_cturn by auto; apply in_map_iff;
      exists m; split; [reflexivity | apply phase2_moves_complete; auto].
Qed.

(** and for the slice placement. *)
Lemma sliceperm_reaches c q :
  Forall (fun m => phase2_move m = true) q -> crun c q = csolved ->
  reaches sliceperm_step sliceperm_goal (length q) (slice_pieces c).
Proof.
  revert c; induction q as [| m q IH]; intros c Hf H;
    unfold crun in H; cbn [fold_left] in H; simpl.
  - apply reaches_goal; rewrite H; reflexivity.
  - inversion Hf; subst; apply reaches_step with (slice_pieces (cturn m c));
      [| apply IH; auto].
    rewrite slice_pieces_cturn by auto; apply in_map_iff;
      exists m; split; [reflexivity | apply phase2_moves_complete; auto].
Qed.

(** Naming what a table lookup is, as in the first phase. *)
Lemma cornerperm_lookup c :
  table_get cornerperm_table (cornerperm_index c)
  = cornerperm_estimate (corner_pieces c).
Proof. unfold cornerperm_estimate; rewrite cornerperm_index_key; reflexivity. Qed.

(** The same for the outer edge table, *)
Lemma udperm_lookup c :
  table_get udperm_table (udperm_index c) = udperm_estimate (ud_pieces c).
Proof. unfold udperm_estimate; rewrite udperm_index_key; reflexivity. Qed.

(** and for the slice table. *)
Lemma sliceperm_lookup c :
  table_get sliceperm_table (sliceperm_index c)
  = sliceperm_estimate (slice_pieces c).
Proof. unfold sliceperm_estimate; rewrite sliceperm_index_key; reflexivity. Qed.

(** What the three tables have to satisfy, and that they do. *)
Definition tables2_ok : Prop :=
  consistentb cornerperm_step cornerperm_goal cornerperm_dom cornerperm_estimate
    = true /\
  consistentb udperm_step udperm_goal udperm_dom udperm_estimate = true /\
  consistentb sliceperm_step sliceperm_goal sliceperm_dom sliceperm_estimate = true.

(** The kernel runs those three checks too. *)
Theorem tables2_checked : tables2_ok.
Proof.
  split; [apply cornerperm_checked
         | split; [apply udperm_checked | apply sliceperm_checked]].
Qed.

(** So the tables never overestimate how far the cube still has to go. *)
Theorem estimate2_admissible u c q :
  Forall (fun m => phase2_move m = true) q ->
  crun c q = csolved -> estimate2 (build_tables2 u) c <= length q.
Proof.
  intros Hf H; unfold estimate2, build_tables2;
    cbn [t_cornerperm t_udperm t_sliceperm].
  rewrite cornerperm_lookup, udperm_lookup, sliceperm_lookup.
  apply Nat.max_lub; [| apply Nat.max_lub].
  - apply cornerperm_safe; [| apply cornerperm_reaches; auto].
    apply perms_complete, Permutation_sym.
    replace all_corners with (corner_pieces (crun c q)) by (rewrite H; reflexivity).
    apply corner_pieces_crun_perm.
  - apply udperm_safe; [| apply udperm_reaches; auto].
    apply perms_complete, Permutation_sym.
    replace ud_edges with (ud_pieces (crun c q)) by (rewrite H; reflexivity).
    apply ud_pieces_crun_perm; auto.
  - apply sliceperm_safe; [| apply sliceperm_reaches; auto].
    apply perms_complete, Permutation_sym.
    replace slice_edges with (slice_pieces (crun c q)) by (rewrite H; reflexivity).
    apply slice_pieces_crun_perm; auto.
Qed.

(** The second phase returns whenever some canonical sequence of allowed moves
    of the allowed length solves the cube. *)
Lemma search2_complete T :
  (forall c q, Forall (fun m => phase2_move m = true) q ->
     crun c q = csolved -> estimate2 T c <= length q) ->
  forall d prev c q, canonical prev q ->
    Forall (fun m => phase2_move m = true) q ->
    crun c q = csolved -> length q <= d ->
  exists p, search2 T d prev c = Some p.
Proof.
  intro Hadm; induction d as [| d IH]; intros prev c q Hc Hf H Hl; cbn [search2];
    destruct (cube_eqb c csolved) eqn:E; try (exists []; reflexivity);
    destruct q as [| m q];
    try (exfalso; unfold crun in H; cbn [fold_left] in H;
         apply cube_eqb_spec in H; congruence).
  - simpl in Hl; lia.
  - simpl in Hl; apply le_S_n in Hl; destruct Hc as [Ha Hc].
    inversion Hf; subst.
    replace (Nat.leb (estimate2 T c) (S d)) with true;
      [| symmetry; apply Nat.leb_le;
         apply Nat.le_trans with (length (m :: q));
         [apply Hadm; auto | simpl; lia]].
    destruct (IH (Some m) (cturn m c) q Hc ltac:(auto) H Hl) as [p Hp].
    apply (choose_move_complete _ _ m p); [| exact Hp].
    unfold allowed_moves2; apply filter_In; split;
      [apply phase2_moves_complete; auto | exact Ha].
Qed.

(** Deepening returns as soon as one of the depths it tries does. *)
Lemma deepen2_complete T fuel depth c (q : list move) :
  (forall d, length q <= d -> exists p, search2 T d None c = Some p) ->
  length q <= depth + fuel -> exists p, deepen2 T fuel depth c = Some p.
Proof.
  revert depth; induction fuel as [| fuel IH]; intros depth Hp Hl;
    cbn [deepen2]; destruct (search2 T depth None c) as [r |] eqn:E;
    try (exists r; reflexivity).
  - destruct (Hp depth ltac:(lia)) as [p Hq]; congruence.
  - apply IH; [exact Hp | lia].
Qed.

(** The second phase always returns when the cube can be solved with allowed
    moves within the limit it was given. *)
Theorem phase2_complete T limit c q :
  (forall c' q', Forall (fun m => phase2_move m = true) q' ->
     crun c' q' = csolved -> estimate2 T c' <= length q') ->
  Forall (fun m => phase2_move m = true) q -> crun c q = csolved ->
  length q <= limit -> exists p, phase2 T limit c = Some p.
Proof.
  intros Hadm Hf H Hl; destruct (normalise_phase2 q Hf) as [r [Hc [Hfr [Hr Hlr]]]].
  unfold phase2; apply (deepen2_complete T limit 0 c r); [| simpl; lia].
  intros d Hd; apply (search2_complete T Hadm d None c r); auto.
  rewrite Hr; exact H.
Qed.
