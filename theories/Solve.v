From Stdlib Require Import Arith List Lia PArith.
From Rubik Require Export Phase2 Solvable.
Import ListNotations.

(** * Solving a cube

    The two phases in sequence, and the entry point the viewer calls: read the
    pieces off a sticker cube, solve, and hand back the moves. *)

(** Reach the subgroup, then finish inside it. *)
Definition two_phase (T1 : tables1) (T2 : tables2) (lim1 lim2 : nat) (c : cube)
  : option (list move) :=
  match phase1 T1 lim1 c with
  | None => None
  | Some p =>
      match phase2 T2 lim2 (crun c p) with
      | None => None
      | Some q => Some (p ++ q)
      end
  end.

(** Whatever the two phases return solves the cube. *)
Theorem two_phase_sound T1 T2 lim1 lim2 c p :
  two_phase T1 T2 lim1 lim2 c = Some p -> crun c p = csolved.
Proof.
  unfold two_phase; destruct (phase1 T1 lim1 c) as [a |] eqn:E1; [| discriminate].
  destruct (phase2 T2 lim2 (crun c a)) as [b |] eqn:E2; [| discriminate].
  intro H; inversion H; subst; rewrite crun_app.
  exact (phase2_sound _ _ _ _ E2).
Qed.

(** * Solving a sticker cube *)

(** Read the cubies off the cube, solve, and hand back the moves. *)
Definition solve_two_phase (T1 : tables1) (T2 : tables2) (lim1 lim2 : nat)
    (s : state) : option (list move) :=
  two_phase T1 T2 lim1 lim2 (to_cubies s).

(** Every sequence it returns really solves the cube it was given. This is the
    guarantee the viewer needs, and it does not depend on the tables being
    right: a wrong table could only make the search fail or wander, never make
    it accept a sequence that does not solve. *)
Theorem solve_two_phase_sound T1 T2 lim1 lim2 s p :
  valid_state s -> solve_two_phase T1 T2 lim1 lim2 s = Some p ->
  run s p = init_state.
Proof.
  intros Hv H; unfold solve_two_phase in H.
  apply two_phase_sound in H.
  rewrite <- (paint_to_cubies s Hv), <- paint_crun, H.
  apply paint_csolved.
Qed.

(** * Why the solver always answers

    Soundness alone would be satisfied by a solver that never returns. What
    makes it return is that each phase is asked for something that is really
    there: a sequence into the subgroup, and a sequence of allowed moves out
    of it. Both are supplied by the solving method in [Solvable.v], which
    finishes one slot at a time from checked tables. The pruning throws
    nothing away and the checked tables never overestimate, so neither can
    stop the search from finding what is there. *)

(** How far each phase may have to look. These are the lengths the solving
    method needs, not the lengths the two-phase search returns, which on a
    real cube is around twenty. *)
Definition phase1_reach (lim1 : nat) : Prop :=
  forall c, csolvable c -> exists q, in_subgroup (crun c q) /\ length q <= lim1.

Definition phase2_reach (lim2 : nat) : Prop :=
  forall c, csolvable c -> in_subgroup c ->
    exists q, Forall (fun m => phase2_move m = true) q /\
      crun c q = csolved /\ length q <= lim2.

(** A solution reaches the subgroup, since the solved cube is in it. *)
Theorem phase1_reach_bound : phase1_reach full_bound.
Proof.
  intros c Hs; destruct (full_solution c Hs) as [r [Hr Hl]].
  exists r; split; [rewrite Hr; apply csolved_in_subgroup | exact Hl].
Qed.

(** And inside the subgroup the allowed moves suffice. *)
Theorem phase2_reach_bound : phase2_reach domino_bound.
Proof. exact subgroup_solution. Qed.

(** The two phases always return. *)
Theorem two_phase_complete u1 u2 c :
  csolvable c ->
  exists p, two_phase (build_tables1 u1) (build_tables2 u2)
              full_bound domino_bound c = Some p.
Proof.
  intro Hs; unfold two_phase.
  destruct (phase1_reach_bound c Hs) as [q1 [HG Hl1]].
  destruct (phase1_complete (build_tables1 u1) full_bound c q1
              (estimate1_admissible u1) HG Hl1) as [p Hp].
  rewrite Hp.
  assert (HG1 : in_subgroup (crun c p)) by (apply phase1_sound with (1 := Hp)).
  destruct (phase2_reach_bound (crun c p) (csolvable_crun c p Hs) HG1)
    as [q2 [Hf2 [Hsol Hl2]]].
  destruct (phase2_complete (build_tables2 u2) domino_bound (crun c p) q2
              (estimate2_admissible u2) Hf2 Hsol Hl2) as [r Hr].
  rewrite Hr; exists (p ++ r); reflexivity.
Qed.

(** A physically valid sticker cube reads back as a solvable cube. *)
Lemma csolvable_to_cubies s : valid_state s -> csolvable (to_cubies s).
Proof.
  intros [p <-].
  replace (to_cubies (run init_state p)) with (crun csolved p);
    [apply csolvable_crun; exists []; reflexivity |].
  rewrite <- paint_csolved, <- paint_crun, to_cubies_paint; reflexivity.
Qed.

(** So the solver answers on every cube a real scramble can produce. This is
    the other half of the guarantee: together with soundness, the viewer's
    solve button always comes back with a sequence, and that sequence solves
    the cube. *)
Theorem solve_two_phase_complete u1 u2 s :
  valid_state s ->
  exists p, solve_two_phase (build_tables1 u1) (build_tables2 u2)
              full_bound domino_bound s = Some p.
Proof.
  intro Hv; unfold solve_two_phase.
  apply two_phase_complete; auto using csolvable_to_cubies.
Qed.
