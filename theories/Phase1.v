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
Definition h1 (T : tables1) (c : cube) : nat :=
  Nat.max (tget (t_twist T) (twist_index c))
    (Nat.max (tget (t_flip T) (flip_index c))
       (tget (t_slice T) (slice_index c))).

(** A decidable test for membership in the subgroup. *)
Definition in_G1b (c : cube) : bool :=
  andb (twist_goal (twists c))
    (andb (flip_goal (flips c)) (slice_goal (slice_mask c))).

(** The test decides exactly the subgroup condition. *)
Lemma in_G1b_spec c : in_G1b c = true <-> in_G1 c.
Proof.
  unfold in_G1b, in_G1, oriented, sliced, twist_goal, flip_goal, slice_goal.
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
Fixpoint p1 (T : tables1) (d : nat) (prev : option move) (c : cube)
  : option (list move) :=
  if in_G1b c then Some []
  else
    match d with
    | 0 => None
    | S d' =>
        if Nat.leb (h1 T c) d then
          choose_move (fun m => p1 T d' (Some m) (cm2f m c)) (allowed_moves prev)
        else None
    end.

(** Anything the first phase returns really does reach the subgroup, using no
    more moves than it was allowed. *)
Theorem p1_sound T d prev c p :
  p1 T d prev c = Some p -> in_G1 (crun c p) /\ length p <= d.
Proof.
  revert prev c p; induction d as [| d IH]; intros prev c p; cbn [p1];
    destruct (in_G1b c) eqn:E.
  - intro H; inversion H; subst; simpl; split; [apply in_G1b_spec; auto | auto].
  - discriminate.
  - intro H; inversion H; subst; simpl;
      split; [apply in_G1b_spec; auto | auto with arith].
  - destruct (Nat.leb (h1 T c) (S d)); [| discriminate].
    intro H; destruct (choose_move_some _ _ _ H) as [m [q [Hin [Hr ->]]]].
    destruct (IH _ _ _ Hr) as [Hrun Hlen]; simpl; split; [| lia].
    exact Hrun.
Qed.

(** Try depths in turn until the subgroup is reached. *)
Fixpoint deepen1 (T : tables1) (fuel depth : nat) (c : cube)
  : option (list move) :=
  match p1 T depth None c with
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
Theorem phase1_sound T limit c p : phase1 T limit c = Some p -> in_G1 (crun c p).
Proof.
  unfold phase1; generalize 0 as d; revert p.
  induction limit as [| limit IH]; intros p d; cbn [deepen1];
    destruct (p1 T d None c) as [q |] eqn:E; try discriminate;
    try (intro H; inversion H; subst; exact (proj1 (p1_sound _ _ _ _ _ E))).
  apply IH.
Qed.
