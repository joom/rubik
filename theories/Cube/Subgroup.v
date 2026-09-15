From Stdlib Require Import List.
From Rubik Require Export Cube.Cubie.
Import ListNotations.

(** * The subgroup the two phases meet in

    A cube can be finished with up turns, down turns and half turns of the
    other four faces exactly when no piece is turned in its slot and the four
    slice edges are somewhere in the slice. The first phase aims at that
    condition; the second may use only the moves that preserve it. *)

(** Every corner square with its slot, and every edge unflipped. *)
Definition oriented (c : cube) : Prop :=
  twists c = repeat T0 8 /\ flips c = repeat F0 12.

(** Where the slice edges sit when the slice is intact. *)
Definition slice_home : list bool :=
  [false; false; false; false; false; false; false; false; true; true; true; true].

(** The four slice edges occupy the four slice slots, in any order. *)
Definition sliced (c : cube) : Prop := slice_mask c = slice_home.

(** Membership in the subgroup the second phase searches. *)
Definition in_subgroup (c : cube) : Prop := oriented c /\ sliced c.

(** The solved cube is in the subgroup. *)
Lemma csolved_in_subgroup : in_subgroup csolved.
Proof. repeat split. Qed.

(** * The moves the second phase may use *)

(** Up and down turn freely; the other four faces only by half turns. *)
Definition phase2_move (m : move) : bool :=
  match m with
  | (Up, _) | (Down, _) => true
  | (_, Half) => true
  | _ => false
  end.

(** The second phase never disturbs what the first phase achieved. This is
    what makes the two-phase decomposition correct: whatever the second phase
    does, the cube stays in the subgroup, so the orientation and slice work of
    the first phase is never undone. *)
Theorem phase2_move_keeps_subgroup m c :
  phase2_move m = true -> in_subgroup c -> in_subgroup (cturn m c).
Proof.
  destruct m as [f t]; destruct f, t; try discriminate; intros _;
    intros [[Htw Hfl] Hsl]; destruct_cube c;
    unfold in_subgroup, oriented, sliced, slice_mask, twists, flips, edge_pieces in *;
    cbn [corner_slots edge_slots cturn cquarter
         xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB
         yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR
         cshift eshift fst snd map repeat] in *;
    injection Htw as ?; injection Hfl as ?; injection Hsl as ?; subst;
    repeat split; cbn [twist_add flip_add]; try reflexivity;
    repeat match goal with H : is_slice _ = _ |- _ => rewrite H end; reflexivity.
Qed.

(** The ten moves the second phase is allowed, written out rather than
    filtered. A constant defined by filtering another module's constant is
    emitted by extraction as an initializer that runs before that module is
    declared, which does not compile. *)
Definition phase2_moves : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, Half); (Front, Half);
   (Down, CW); (Down, Half); (Down, CCW); (Left, Half); (Back, Half)].

(** It is exactly the moves the second phase may use. *)
Lemma phase2_moves_filter : phase2_moves = filter phase2_move all_moves.
Proof. reflexivity. Qed.

(** Every move in the list is one the second phase may use. *)
Lemma phase2_moves_allowed m : In m phase2_moves -> phase2_move m = true.
Proof. rewrite phase2_moves_filter; intro H; apply filter_In in H; tauto. Qed.
