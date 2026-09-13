From Stdlib Require Import Bool List.
From Rubik Require Export Sticker TurnTables.
Import ListNotations.

(** * Turning the cube

    The eighteen face turns, sequences of them, and what it means for a cube
    to be one a scramble could have produced. *)

(** Expose each sticker so concrete permutation identities reduce directly. *)
Ltac destruct_state s :=
  destruct s as [a b]; unfold grid in *;
  repeat match goal with
  | x : triple _ |- _ => destruct x
  end.

(** Four clockwise quarter turns return every sticker to its original slot. *)
Lemma quarter_four f s : quarter f (quarter f (quarter f (quarter f s))) = s.
Proof.
  destruct f; destruct_state s; reflexivity.
Qed.

(** The half-turn table is exactly two clockwise quarter turns, so the direct
    definition may be unfolded wherever a proof prefers to reason about
    quarter turns. *)
Lemma half_spec f s : half f s = quarter f (quarter f s).
Proof.
  destruct f; destruct_state s; reflexivity.
Qed.

(** The counterclockwise table is exactly three clockwise quarter turns. *)
Lemma quarter_inv_spec f s : quarter_inv f s = quarter f (quarter f (quarter f s)).
Proof.
  destruct f; destruct_state s; reflexivity.
Qed.

(** * Moves and sequences *)

(** Quarter, half, and inverse quarter turns each cost one search step. *)
Inductive turns := CW | Half | CCW.

(** A face together with a turn amount describes one legal move. *)
Definition move := (face * turns)%type.

(** All 18 face turns are tried in a fixed order to break shortest-path ties. *)
Definition Movel : list move := list_prod faces [CW; Half; CCW].

(** Each turn amount reads its own table, so a move rebuilds the 54 stickers
    once however far the face is turned. *)
Definition m2f (m : move) (s : state) : state :=
  let (f, t) := m in
  match t with
  | CW => quarter f s
  | Half => half f s
  | CCW => quarter_inv f s
  end.

(** Restate a move as repeated clockwise quarter turns. Proofs about moves
    reduce with this and then argue about [quarter] alone. *)
Ltac unfold_moves := cbn [m2f]; rewrite ?half_spec, ?quarter_inv_spec.

(** Reversing a quarter turn undoes it; a half turn is its own inverse. *)
Definition minv (m : move) : move :=
  let (f, t) := m in
  (f, match t with CW => CCW | Half => Half | CCW => CW end).

(** Following any move by its inverse restores the entire cube. *)
Lemma moves_inv m s : m2f (minv m) (m2f m s) = s.
Proof.
  destruct m as [f t]; destruct t; cbn [minv]; unfold_moves; apply quarter_four.
Qed.

(** A sequence acts left to right, passing each resulting cube to the next move. *)
Definition run (s : state) (p : list move) : state :=
  fold_left (fun s m => m2f m s) p s.

(** Executing concatenated sequences is the same as executing them in stages. *)
Lemma run_app s p q : run s (p ++ q) = run (run s p) q.
Proof.
  apply fold_left_app.
Qed.

(** * Physical validity *)

(** A state is reachable when legal moves can scramble the solved cube into it. *)
Definition reachable (s : state) : Prop := exists p, run init_state p = s.

(** Physical validity is reachability, rather than an algebraic cubie test. *)
Definition valid_state : state -> Prop := reachable.

(** Appending one legal move to a scramble preserves physical validity. *)
Lemma move_valid m s : valid_state s -> valid_state (m2f m s).
Proof.
  intros [p <-]; exists (p ++ [m]); rewrite run_app; reflexivity.
Qed.
