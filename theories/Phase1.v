From Stdlib Require Import Arith List Lia PArith.
From Rubik Require Export Tables Prune.
Import ListNotations.

(** * The first phase

    Search with all eighteen moves for a sequence that carries the cube into
    the subgroup the second phase can finish. The three coordinate tables
    supply the lower bound that makes the search tractable: none of them can
    overestimate, so the largest of them is still a lower bound. *)

(** The three tables, built once and handed to the search. Passing them as an
    argument rather than reaching for them by name is what keeps them from
    being rebuilt at every node. *)
Record tables1 := Tables1 { t_twist : table; t_flip : table; t_slice : table }.

(** Gathered when the solver runs, not when the program loads. A top-level
    record would copy the three tables at static-initialisation time, which
    may happen before they are built, leaving the search with a heuristic of
    zero and no pruning at all. *)
Definition build_tables1 (u : unit) : tables1 :=
  Tables1 twist_table flip_table slice_table.

(** How far the cube still is from the subgroup, as far as any one coordinate
    can tell. Each is a lower bound, so the largest of them is too. *)
Definition estimate1 (T : tables1) (c : cube) : nat :=
  Nat.max (table_get (t_twist T) (twist_index c))
    (Nat.max (table_get (t_flip T) (flip_index c))
       (table_get (t_slice T) (slice_index c))).

(** A decidable test for membership in the subgroup. *)
Definition in_subgroupb (c : cube) : bool :=
  andb (twist_goal (twists c))
    (andb (flip_goal (flips c)) (slice_goal (slice_mask c))).

(** The test decides exactly the subgroup condition. *)
Lemma in_subgroupb_spec c : in_subgroupb c = true <-> in_subgroup c.
Proof.
  unfold in_subgroupb, in_subgroup, oriented, sliced, twist_goal, flip_goal, slice_goal.
  split.
  - intro H; apply Bool.andb_true_iff in H as [Ht H];
      apply Bool.andb_true_iff in H as [Hf Hs].
    destruct (list_eq_dec twist_eq_dec _ _); [| discriminate].
    destruct (list_eq_dec flip_eq_dec _ _); [| discriminate].
    destruct (list_eq_dec Bool.bool_dec _ _); [| discriminate].
    repeat split; assumption.
  - intros [[Ht Hf] Hs]; rewrite Ht, Hf, Hs.
    destruct (list_eq_dec twist_eq_dec _ _); [| contradiction].
    destruct (list_eq_dec flip_eq_dec _ _); [| contradiction].
    destruct (list_eq_dec Bool.bool_dec _ _); [| contradiction].
    reflexivity.
Qed.

(** Take the first move that reaches the subgroup within the remaining depth,
    abandoning a branch as soon as the tables say it cannot. *)
Fixpoint search1 (T : tables1) (d : nat) (prev : option move) (c : cube)
  : option (list move) :=
  if in_subgroupb c then Some []
  else
    match d with
    | 0 => None
    | S d' =>
        if Nat.leb (estimate1 T c) d then
          choose_move (fun m => search1 T d' (Some m) (cturn m c)) (allowed_moves prev)
        else None
    end.

(** Anything the first phase returns really does reach the subgroup, using no
    more moves than it was allowed. *)
Theorem search1_sound T d prev c p :
  search1 T d prev c = Some p -> in_subgroup (crun c p) /\ length p <= d.
Proof.
  revert prev c p; induction d as [| d IH]; intros prev c p; cbn [search1];
    destruct (in_subgroupb c) eqn:E.
  - intro H; inversion H; subst; simpl; split; [apply in_subgroupb_spec; auto | auto].
  - discriminate.
  - intro H; inversion H; subst; simpl;
      split; [apply in_subgroupb_spec; auto | auto with arith].
  - destruct (Nat.leb (estimate1 T c) (S d)); [| discriminate].
    intro H; destruct (choose_move_sound _ _ _ H) as [m [q [Hin [Hr ->]]]].
    destruct (IH _ _ _ Hr) as [Hrun Hlen]; simpl; split; [| lia].
    exact Hrun.
Qed.

(** Try depths in turn until the subgroup is reached. *)
Fixpoint deepen1 (T : tables1) (fuel depth : nat) (c : cube)
  : option (list move) :=
  match search1 T depth None c with
  | Some p => Some p
  | None =>
      match fuel with
      | 0 => None
      | S n => deepen1 T n (S depth) c
      end
  end.

(** The first phase, searching as deep as it is allowed. *)
Definition phase1 (T : tables1) (limit : nat) (c : cube) : option (list move) :=
  deepen1 T limit 0 c.

(** Whatever it returns reaches the subgroup. *)
Theorem phase1_sound T limit c p : phase1 T limit c = Some p -> in_subgroup (crun c p).
Proof.
  unfold phase1; generalize 0 as d; revert p.
  induction limit as [| limit IH]; intros p d; cbn [deepen1];
    destruct (search1 T d None c) as [q |] eqn:E; try discriminate;
    try (intro H; inversion H; subst; exact (proj1 (search1_sound _ _ _ _ _ E))).
  apply IH.
Qed.


(** * Why the first phase always finds something

    Soundness says nothing about whether the search returns at all. It returns
    whenever some sequence of the allowed length reaches the subgroup, and
    that rests on two things: the pruning throws away no sequence that is not
    matched by an equally short canonical one, and the tables never
    overestimate, so the bound never cuts off a branch that would have
    worked. *)

(** Every move appears in the list the tables were stepped with. *)
Lemma table_moves_complete m : In m table_moves.
Proof. destruct m as [f t]; destruct f, t; simpl; tauto. Qed.

(** A cube always has eight corner rotations to report, twelve flips, and
    twelve slots that are either slice or not. *)
Lemma twists_length c : length (twists c) = 8.
Proof. unfold twists, corner_slots; rewrite length_map; reflexivity. Qed.

Lemma flips_length c : length (flips c) = 12.
Proof. unfold flips, edge_slots; rewrite length_map; reflexivity. Qed.

Lemma slice_mask_length c : length (slice_mask c) = 12.
Proof.
  unfold slice_mask, edge_pieces, edge_slots; rewrite !length_map; reflexivity.
Qed.

(** A sequence reaching the subgroup is, read one coordinate at a time, a path
    of the same length to that coordinate's own goal. *)
Lemma twist_reaches c q :
  in_subgroup (crun c q) -> reaches twist_step twist_goal (length q) (twists c).
Proof.
  revert c; induction q as [| m q IH]; intros c H;
    unfold crun in H; cbn [fold_left] in H; simpl.
  - apply reaches_goal; destruct H as [[Ht _] _]; unfold twist_goal;
      rewrite Ht; destruct (list_eq_dec twist_eq_dec _ _); congruence.
  - apply reaches_step with (twists (cturn m c)); [| apply IH, H].
    rewrite twists_cturn; apply in_map_iff;
      exists m; split; [reflexivity | apply table_moves_complete].
Qed.

Lemma flip_reaches c q :
  in_subgroup (crun c q) -> reaches flip_step flip_goal (length q) (flips c).
Proof.
  revert c; induction q as [| m q IH]; intros c H;
    unfold crun in H; cbn [fold_left] in H; simpl.
  - apply reaches_goal; destruct H as [[_ Hf] _]; unfold flip_goal;
      rewrite Hf; destruct (list_eq_dec flip_eq_dec _ _); congruence.
  - apply reaches_step with (flips (cturn m c)); [| apply IH, H].
    rewrite flips_cturn; apply in_map_iff;
      exists m; split; [reflexivity | apply table_moves_complete].
Qed.

Lemma slice_reaches c q :
  in_subgroup (crun c q) -> reaches slice_step slice_goal (length q) (slice_mask c).
Proof.
  revert c; induction q as [| m q IH]; intros c H;
    unfold crun in H; cbn [fold_left] in H; simpl.
  - apply reaches_goal; destruct H as [_ Hs]; unfold slice_goal;
      rewrite Hs; destruct (list_eq_dec Bool.bool_dec _ _); congruence.
  - apply reaches_step with (slice_mask (cturn m c)); [| apply IH, H].
    rewrite slice_mask_cturn; apply in_map_iff;
      exists m; split; [reflexivity | apply table_moves_complete].
Qed.

(** Naming what a table lookup is before using it. Left as a bare lookup, the
    unifier would try to reduce the table itself, which takes longer than the
    proof is worth. *)
Lemma twist_lookup c :
  table_get twist_table (twist_index c) = twist_estimate (twists c).
Proof. unfold twist_estimate; rewrite twist_index_key; reflexivity. Qed.

Lemma flip_lookup c : table_get flip_table (flip_index c) = flip_estimate (flips c).
Proof. unfold flip_estimate; rewrite flip_index_key; reflexivity. Qed.

Lemma slice_lookup c :
  table_get slice_table (slice_index c) = slice_estimate (slice_mask c).
Proof. unfold slice_estimate; rewrite slice_index_key; reflexivity. Qed.

(** What the three tables have to satisfy, and that they do. The checks are
    decidable, so the kernel runs them rather than taking them on trust. *)
Definition tables1_ok : Prop :=
  consistentb twist_step twist_goal twist_dom twist_estimate = true /\
  consistentb flip_step flip_goal flip_dom flip_estimate = true /\
  consistentb slice_step slice_goal slice_dom slice_estimate = true.

Theorem tables1_checked : tables1_ok.
Proof.
  split; [apply twist_checked | split; [apply flip_checked | apply slice_checked]].
Qed.

(** So the tables never overestimate how far the subgroup is, and the bound
    the search prunes with never rejects a branch that would have worked. *)
Theorem estimate1_admissible u c q :
  in_subgroup (crun c q) -> estimate1 (build_tables1 u) c <= length q.
Proof.
  intro H; unfold estimate1, build_tables1; cbn [t_twist t_flip t_slice].
  rewrite twist_lookup, flip_lookup, slice_lookup.
  apply Nat.max_lub; [| apply Nat.max_lub].
  - apply twist_safe; [| apply twist_reaches, H].
    apply tuples_complete; [apply all_twists_complete | apply twists_length].
  - apply flip_safe; [| apply flip_reaches, H].
    apply tuples_complete; [apply all_flips_complete | apply flips_length].
  - apply slice_safe; [| apply slice_reaches, H].
    apply tuples_complete; [intros [|]; simpl; tauto | apply slice_mask_length].
Qed.

(** Rewriting a sequence of cube moves into a canonical one. This is the
    generic normalisation instantiated at cubes, with every move allowed. *)
Lemma normalise_cube p :
  exists q, canonical None q /\ (forall c, crun c q = crun c p) /\
    length q <= length p.
Proof.
  destruct (canonical_exists cube cturn (fun _ => true)
              (fun f t1 t2 _ _ =>
                 match csame_face_merge f t1 t2 with
                 | or_introl H => or_introl H
                 | or_intror (ex_intro _ t3 H) =>
                     or_intror (ex_intro _ t3 (conj eq_refl H))
                 end)
              (fun f g t1 t2 Hop c => cmove_comm f g t1 t2 c Hop)
              p (proj2 (Forall_forall _ p) (fun m _ => eq_refl)))
    as [q [Hc [_ [Hq Hl]]]].
  exists q; repeat split; auto.
Qed.

(** The first phase returns whenever some canonical sequence of the allowed
    length reaches the subgroup. *)
Lemma search1_complete T :
  (forall c q, in_subgroup (crun c q) -> estimate1 T c <= length q) ->
  forall d prev c q, canonical prev q -> in_subgroup (crun c q) -> length q <= d ->
  exists p, search1 T d prev c = Some p.
Proof.
  intro Hadm; induction d as [| d IH]; intros prev c q Hc H Hl; cbn [search1];
    destruct (in_subgroupb c) eqn:E; try (exists []; reflexivity);
    destruct q as [| m q];
    try (exfalso; unfold crun in H; cbn [fold_left] in H;
         apply in_subgroupb_spec in H; congruence).
  - simpl in Hl; lia.
  - simpl in Hl; apply le_S_n in Hl; destruct Hc as [Ha Hc].
    replace (Nat.leb (estimate1 T c) (S d)) with true;
      [| symmetry; apply Nat.leb_le;
         apply Nat.le_trans with (length (m :: q)); [apply Hadm, H | simpl; lia]].
    destruct (IH (Some m) (cturn m c) q Hc H Hl) as [p Hp].
    apply (choose_move_complete _ _ m p); [| exact Hp].
    rewrite allowed_moves_filter; apply filter_In; split;
      [rewrite <- table_moves_all; apply table_moves_complete | exact Ha].
Qed.

(** Deepening returns as soon as one of the depths it tries does. *)
Lemma deepen1_complete T fuel depth c (q : list move) :
  (forall d, length q <= d -> exists p, search1 T d None c = Some p) ->
  length q <= depth + fuel -> exists p, deepen1 T fuel depth c = Some p.
Proof.
  revert depth; induction fuel as [| fuel IH]; intros depth Hp Hl;
    cbn [deepen1]; destruct (search1 T depth None c) as [r |] eqn:E;
    try (exists r; reflexivity).
  - destruct (Hp depth ltac:(lia)) as [p Hq]; congruence.
  - apply IH; [exact Hp | lia].
Qed.

(** The first phase always returns when the subgroup is within reach of the
    limit it was given. The pruning costs nothing here: any sequence at all is
    matched by a canonical one that is no longer. *)
Theorem phase1_complete T limit c q :
  (forall c' q', in_subgroup (crun c' q') -> estimate1 T c' <= length q') ->
  in_subgroup (crun c q) -> length q <= limit ->
  exists p, phase1 T limit c = Some p.
Proof.
  intros Hadm H Hl; destruct (normalise_cube q) as [r [Hc [Hr Hlr]]].
  unfold phase1; apply (deepen1_complete T limit 0 c r); [| simpl; lia].
  intros d Hd; apply (search1_complete T Hadm d None c r); auto.
  rewrite Hr; exact H.
Qed.
