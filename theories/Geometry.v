From Stdlib Require Import List ZArith.
From Rubik Require Export BasicRubik.

(** * Addressing stickers *)

(** The first, middle, and last positions address a row or column of a face. *)
Inductive index := Low | Mid | High.

(** Select one entry of a triple by its position. *)
Definition pick {A} (i : index) (t : triple A) : A :=
  let '(Triple a b c) := t in
  match i with
  | Low => a
  | Mid => b
  | High => c
  end.

(** Select a face while respecting the U/R/F and D/L/B storage order. *)
Definition face_grid (f : face) (s : state) : grid :=
  let '(Triple u r f', Triple d l b) := s in
  match f with
  | Up => u
  | Right => r
  | Front => f'
  | Down => d
  | Left => l
  | Back => b
  end.

(** A face, row, and column uniquely locate one of the 54 stickers. *)
Definition facelet := (face * index * index)%type.

(** Read a sticker by selecting its face, then its row and column. *)
Definition sticker_at (s : state) (l : facelet) : color :=
  let '(f, row, col) := l in
  pick col (pick row (face_grid f s)).

(** * Integer geometry *)

(** Integer vectors use axes pointing right (+x), up (+y), and front (+z),
    describing positions and outward normals without rounding. *)
Definition vector := (Z * Z * Z)%type.

Open Scope Z_scope.

(** Row and column indices become offsets centered at zero. *)
Definition coordinate (i : index) : Z :=
  match i with
  | Low => -1
  | Mid => 0
  | High => 1
  end.

(** Decode offsets -1, 0, and 1; other integers default to [High]. *)
Definition to_index (z : Z) : index :=
  if Z.eqb z (-1) then Low
  else if Z.eqb z 0 then Mid
  else High.

(** Each face points along one signed coordinate axis. *)
Definition normal (f : face) : vector :=
  match f with
  | Up => (0, 1, 0)
  | Right => (1, 0, 0)
  | Front => (0, 0, 1)
  | Down => (0, -1, 0)
  | Left => (-1, 0, 0)
  | Back => (0, 0, -1)
  end.

(** Embed an outside-view row and column into the cube with coordinates -1 to 1. *)
Definition position (l : facelet) : vector :=
  let '(f, row, col) := l in
  let r := coordinate row in
  let c := coordinate col in
  match f with
  | Up => (c, 1, r)
  | Right => (1, -r, -c)
  | Front => (c, -r, 1)
  | Down => (c, -1, -r)
  | Left => (-1, -r, c)
  | Back => (-c, -r, -1)
  end.

(** Projection onto a face normal identifies its outer layer. *)
Definition dot (a b : vector) : Z :=
  let '(x, y, z) := a in
  let '(x', y', z') := b in
  x * x' + y * y' + z * z'.

(** For a signed unit-axis normal, rotate by minus 90 degrees using the cross
    product. *)
Definition clockwise (n v : vector) : vector :=
  let '(a, b, c) := n in
  let '(x, y, z) := v in
  let d := dot n v in
  (a * d - (b * z - c * y),
   b * d - (c * x - a * z),
   c * d - (a * y - b * x)).

(** Recover a face, row, and column from a sticker position and its outward normal. *)
Definition locate (n p : vector) : facelet :=
  let '(a, b, c) := n in
  let '(x, y, z) := p in
  if Z.eqb b 1 then (Up, to_index z, to_index x)
  else if Z.eqb a 1 then (Right, to_index (-y), to_index (-z))
  else if Z.eqb c 1 then (Front, to_index (-y), to_index x)
  else if Z.eqb b (-1) then (Down, to_index (-z), to_index x)
  else if Z.eqb a (-1) then (Left, to_index (-y), to_index z)
  else (Back, to_index (-y), to_index (-x)).

(** Rotate a sticker and its normal only when it lies in the selected outer
    layer. *)
Definition turn_facelet (f : face) (l : facelet) : facelet :=
  let '(g, _, _) := l in
  let n := normal f in
  if Z.eqb (dot n (position l)) 1
  then locate (clockwise n (normal g)) (clockwise n (position l))
  else l.

Close Scope Z_scope.

(** * Geometric correctness *)

(** The generated permutation agrees with the independent geometric rotation. *)
Theorem quarter_geometry f s l :
  sticker_at (quarter f s) (turn_facelet f l) = sticker_at s l.
Proof.
  destruct l as [[g row] col]; destruct f, g, row, col;
    destruct_state s; reflexivity.
Qed.

(** An outer-layer turn leaves every face center in place. *)
Theorem centers_fixed f g s :
  sticker_at (quarter f s) (g, Mid, Mid) = sticker_at s (g, Mid, Mid).
Proof.
  destruct f, g; destruct_state s; reflexivity.
Qed.

(** Every allowed turn amount preserves all face centers. *)
Lemma move_centers_fixed m g s :
  sticker_at (turn m s) (g, Mid, Mid) = sticker_at s (g, Mid, Mid).
Proof.
  destruct m as [f []]; unfold_moves; repeat rewrite centers_fixed; reflexivity.
Qed.

(** Center preservation extends from individual moves to whole sequences. *)
Lemma run_centers_fixed p g s :
  sticker_at (run s p) (g, Mid, Mid) = sticker_at s (g, Mid, Mid).
Proof.
  revert s; induction p as [| m p IH]; intro s; cbn [run fold_left]; auto.
  change (sticker_at (run (turn m s) p) (g, Mid, Mid) = sticker_at s (g, Mid, Mid)).
  rewrite IH; apply move_centers_fixed.
Qed.

(** Every reachable cube retains the solved reference frame at its centers. *)
Theorem valid_centers s : valid_state s ->
  forall f, sticker_at s (f, Mid, Mid) = f.
Proof.
  intros [p <-] f; rewrite run_centers_fixed; destruct f; reflexivity.
Qed.
