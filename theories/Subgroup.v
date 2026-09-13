From Stdlib Require Import List.
From Rubik Require Export Cubie.
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
Definition in_G1 (c : cube) : Prop := oriented c /\ sliced c.

(** The solved cube is in the subgroup. *)
Lemma in_G1_csolved : in_G1 csolved.
Proof. repeat split. Qed.

(** * The moves the second phase may use *)

(** Up and down turn freely; the other four faces only by half turns. *)
Definition phase2 (m : move) : bool :=
  match m with
  | (Up, _) | (Down, _) => true
  | (_, Half) => true
  | _ => false
  end.

(** The second phase never disturbs what the first phase achieved. This is
    what makes the two-phase decomposition correct: whatever the second phase
    does, the cube stays in the subgroup, so the orientation and slice work of
    the first phase is never undone. *)
Theorem in_G1_phase2 m c : phase2 m = true -> in_G1 c -> in_G1 (cm2f m c).
Proof.
  destruct m as [f t]; destruct f, t; try discriminate; intros _;
    intros [[Htw Hfl] Hsl]; destruct_cube c;
    unfold in_G1, oriented, sliced, slice_mask, twists, flips, epieces in *;
    cbn [cslots eslots cm2f cquarter
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
Definition Movel2 : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, Half); (Front, Half);
   (Down, CW); (Down, Half); (Down, CCW); (Left, Half); (Back, Half)].

(** It is exactly the moves the second phase may use. *)
Lemma Movel2_filter : Movel2 = filter phase2 Movel.
Proof. reflexivity. Qed.

(** Every move in the list is one the second phase may use. *)
Lemma Movel2_phase2 m : In m Movel2 -> phase2 m = true.
Proof. rewrite Movel2_filter; intro H; apply filter_In in H; tauto. Qed.
