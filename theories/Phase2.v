From Stdlib Require Import Arith List Lia PArith.
From Rubik Require Export Phase1.
Import ListNotations.

(** * The second phase

    From inside the subgroup, finish the cube using only the ten moves that
    keep it there. Three more tables bound how far the pieces still have to
    travel. *)

(** The tables the second phase prunes with. *)
Record tables2 := Tables2 { t_cperm : table; t_e8 : table; t_e4 : table }.

(** Gathered when the solver runs, not when the program loads, so the tables
    are built before they are read. *)
Definition build_tables2 (u : unit) : tables2 :=
  Tables2 cperm_table e8_table e4_table.

(** How far the pieces still have to travel, as far as any one table can tell. *)
Definition h2 (T : tables2) (c : cube) : nat :=
  Nat.max (tget (t_cperm T) (cperm_index c))
    (Nat.max (tget (t_e8 T) (e8_index c))
       (tget (t_e4 T) (e4_index c))).

(** The moves the second phase may still try after a given move. *)
Definition allowed_moves2 (prev : option move) : list move :=
  filter (allowed prev) Movel2.

(** Take the first move that solves the cube within the remaining depth. *)
Fixpoint p2 (T : tables2) (d : nat) (prev : option move) (c : cube)
  : option (list move) :=
  if cube_eqb c csolved then Some []
  else
    match d with
    | 0 => None
    | S d' =>
        if Nat.leb (h2 T c) d then
          choose_move (fun m => p2 T d' (Some m) (cm2f m c)) (allowed_moves2 prev)
        else None
    end.

(** Anything the second phase returns really solves the cube. *)
Theorem p2_sound T d prev c p :
  p2 T d prev c = Some p -> crun c p = csolved /\ length p <= d.
Proof.
  revert prev c p; induction d as [| d IH]; intros prev c p; cbn [p2];
    destruct (cube_eqb c csolved) eqn:E.
  - intro H; inversion H; subst; simpl;
      split; [apply cube_eqb_spec; auto | auto].
  - discriminate.
  - intro H; inversion H; subst; simpl;
      split; [apply cube_eqb_spec; auto | auto with arith].
  - destruct (Nat.leb (h2 T c) (S d)); [| discriminate].
    intro H; destruct (choose_move_some _ _ _ H) as [m [q [Hin [Hr ->]]]].
    destruct (IH _ _ _ Hr) as [Hrun Hlen]; simpl; split; [| lia].
    exact Hrun.
Qed.

(** Try depths in turn until the cube comes out solved. *)
Fixpoint deepen2 (T : tables2) (fuel depth : nat) (c : cube)
  : option (list move) :=
  match p2 T depth None c with
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
    destruct (p2 T d None c) as [q |] eqn:E; try discriminate;
    try (intro H; inversion H; subst; exact (proj1 (p2_sound _ _ _ _ _ E))).
  apply IH.
Qed.
