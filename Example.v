From Stdlib Require Import List.
From minirubik Require Import Geometry Solver.
Import ListNotations.

(** * Executable solver examples *)

(** An already solved cube needs no moves. *)
Example solved : solve init_state = Some [].
Proof.
  lazy; reflexivity.
Qed.

(** One clockwise right turn is solved by its inverse. *)
Example right_turn : solve (m2f (Right, CW) init_state) = Some [(Right, CCW)].
Proof.
  lazy; reflexivity.
Qed.

(** A front half turn is undone by the same half turn. *)
Example front_half_turn : solve (m2f (Front, Half) init_state) = Some [(Front, Half)].
Proof.
  lazy; reflexivity.
Qed.

(** A two-face scramble is solved by reversing and inverting its moves. *)
Example two_turns :
  solve (run init_state [(Right, CW); (Up, CW)]) = Some [(Up, CCW); (Right, CCW)].
Proof.
  lazy; reflexivity.
Qed.

(** All 18 single-turn scrambles have the expected one-move solution. *)
Example every_single_turn m : solve (m2f m init_state) = Some [minv m].
Proof.
  destruct m as [f t]; destruct f, t; lazy; reflexivity.
Qed.

(** A sufficient explicit limit recovers the shortest two-move solution. *)
Example bounded_shortest :
  solve_bounded 2 (run init_state [(Right, CW); (Up, CW)]) =
    Some [(Up, CCW); (Right, CCW)].
Proof.
  vm_compute; reflexivity.
Qed.

(** A one-move allowance cannot solve this two-face scramble. *)
Example insufficient_depth :
  solve_bounded 1 (run init_state [(Right, CW); (Up, CW)]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

(** Three interacting faces exercise search beyond single-turn cases. *)
Example three_faces :
  solve_bounded 3 (run init_state [(Front, CW); (Right, Half); (Up, CCW)]) =
    Some [(Up, CW); (Right, Half); (Front, CCW)].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Sticker movement *)

(** A front clockwise turn carries the upper front edge onto the right face. *)
Example front_edge :
  sticker_at (quarter Front init_state) (Right, Mid, Low) = Up.
Proof.
  reflexivity.
Qed.

(** The same turn carries the upper front right corner onto the right face. *)
Example front_corner :
  sticker_at (quarter Front init_state) (Right, High, Low) = Up.
Proof.
  reflexivity.
Qed.

(** * Invalid states *)

(** A uniformly colored cube is representable but violates the fixed-center
    invariant. *)
Definition monochrome : state :=
  (Triple (solid Up) (solid Up) (solid Up),
   Triple (solid Up) (solid Up) (solid Up)).

(** The center invariant proves total search rejects the monochrome cube. *)
Example invalid_cube : solve monochrome = None.
Proof.
  apply solve_none; intro H.
  pose proof (valid_centers monochrome H Right) as E; discriminate E.
Qed.

(** * Proof assumption audit *)

(** Every theorem below must report that it is closed under the global context. *)
Print Assumptions quarter_geometry.
Print Assumptions solve_init.
Print Assumptions solve_minimal.
Print Assumptions solve_length.
Print Assumptions solve_none.
Print Assumptions solve_bounded_spec.
