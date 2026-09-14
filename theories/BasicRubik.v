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
Inductive amount := CW | Half | CCW.

(** A face together with a turn amount describes one legal move. *)
Definition move := (face * amount)%type.

(** All 18 face turns are tried in a fixed order to break shortest-path ties. *)
Definition all_moves : list move := list_prod faces [CW; Half; CCW].

(** Each turn amount reads its own table, so a move rebuilds the 54 stickers
    once however far the face is turned. *)
Definition turn (m : move) (s : state) : state :=
  let (f, t) := m in
  match t with
  | CW => quarter f s
  | Half => half f s
  | CCW => quarter_inv f s
  end.

(** Restate a move as repeated clockwise quarter turns. Proofs about moves
    reduce with this and then argue about [quarter] alone. *)
Ltac unfold_moves := cbn [turn]; rewrite ?half_spec, ?quarter_inv_spec.

(** Reversing a quarter turn undoes it; a half turn is its own inverse. *)
Definition inverse (m : move) : move :=
  let (f, t) := m in
  (f, match t with CW => CCW | Half => Half | CCW => CW end).

(** Following any move by its inverse restores the entire cube. *)
Lemma inverse_undoes m s : turn (inverse m) (turn m s) = s.
Proof.
  destruct m as [f t]; destruct t; cbn [inverse]; unfold_moves; apply quarter_four.
Qed.

(** A sequence acts left to right, passing each resulting cube to the next move. *)
Definition run (s : state) (p : list move) : state :=
  fold_left (fun s m => turn m s) p s.

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
Lemma move_valid m s : valid_state s -> valid_state (turn m s).
Proof.
  intros [p <-]; exists (p ++ [m]); rewrite run_app; reflexivity.
Qed.

(** * Faces on an axis

    A total order on faces, and which pairs are the two ends of one axis.
    The pruning needs both, and so does the move algebra below. *)

(** Faces in the model's U/R/F/D/L/B order, so that opposite faces differ by
    three and a total order on faces is available. *)
Definition face_rank (f : face) : nat :=
  match f with
  | Up => 0 | Right => 1 | Front => 2 | Down => 3 | Left => 4 | Back => 5
  end.

(** Ranks determine a face, so comparing them compares faces. *)
Lemma face_rank_inj f g : face_rank f = face_rank g -> f = g.
Proof. destruct f, g; simpl; congruence. Qed.

(** Opposite faces are the two ends of one axis: U and D, R and L, F and B. *)
Definition opposite (f g : face) : bool :=
  Nat.eqb (face_rank f + 3) (face_rank g) || Nat.eqb (face_rank g + 3) (face_rank f).

Lemma opposite_sym f g : opposite f g = opposite g f.
Proof. unfold opposite; apply Bool.orb_comm. Qed.

(** Two turns of one face are a single turn of that face, or nothing at all. *)
Lemma same_face_merge (f : face) (t1 t2 : amount) :
  (forall s, turn (f, t2) (turn (f, t1) s) = s) \/
  (exists t3, forall s, turn (f, t2) (turn (f, t1) s) = turn (f, t3) s).
Proof.
  destruct t1, t2;
    [ right; exists Half | right; exists CCW | left
    | right; exists CCW | left | right; exists CW
    | left | right; exists CW | right; exists Half ];
    intro s; unfold_moves; rewrite ?quarter_four; reflexivity.
Qed.

(** Quarter turns of opposite faces move disjoint cubies, so they commute. *)
Lemma quarter_comm f g s :
  opposite f g = true -> quarter f (quarter g s) = quarter g (quarter f s).
Proof.
  destruct f, g; simpl opposite; try discriminate; intros _;
    destruct_state s; reflexivity.
Qed.

(** Turns of opposite faces commute, whatever their amounts. *)
Lemma move_comm f g t1 t2 s :
  opposite f g = true ->
  turn (f, t1) (turn (g, t2) s) = turn (g, t2) (turn (f, t1) s).
Proof.
  intro H; destruct t1, t2; unfold_moves;
    repeat rewrite (quarter_comm f g _ H); reflexivity.
Qed.
