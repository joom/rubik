From Stdlib Require Import Arith List Lia PArith.
From Rubik Require Export Phase2.
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

(** Running a sequence in stages is running the whole of it. *)
Lemma crun_app c p q : crun c (p ++ q) = crun (crun c p) q.
Proof. unfold crun; apply fold_left_app. Qed.

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
