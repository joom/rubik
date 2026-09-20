From Stdlib Require Import List.
From Rubik Require Export Cube.BasicRubik.
Import ListNotations.

(** * The cubie model

    The sticker model says where each of the 54 colors sits. A solver needs
    less than that and more structure: a cube is 8 corner pieces and 12 edge
    pieces, each sitting in a slot and rotated within it. Kociemba's
    coordinates are all defined over that view, so this file builds it and
    proves it agrees with the stickers move for move. *)

(** The eight corner slots, named by the faces they touch. *)
Inductive corner := URF | UFL | ULB | UBR | DFR | DLF | DBL | DRB.

(** The twelve edge slots. *)
Inductive edge := UR | UF | UL | UB | DR | DF | DL | DB | FR | FL | BL | BR.

(** How far a corner is rotated within its slot. *)
Inductive twist := T0 | T1 | T2.

(** Whether an edge is flipped within its slot. *)
Inductive flip := F0 | F1.

(** Facelet positions within a corner slot and within an edge slot. *)
Inductive corner_facet := C0 | C1 | C2.
(** And the two positions within an edge slot. *)
Inductive edge_facet := E0 | E1.

(** A slot holds a piece together with its rotation. *)
Definition corner_slot := (corner * twist)%type.
(** An edge slot likewise. *)
Definition edge_slot := (edge * flip)%type.

(** A cube records which piece occupies each of the twenty slots. Centers are
    fixed by every legal move, so they carry no information. *)
Record cube := Cube {
  xURF : corner_slot; xUFL : corner_slot; xULB : corner_slot; xUBR : corner_slot;
  xDFR : corner_slot; xDLF : corner_slot; xDBL : corner_slot; xDRB : corner_slot;
  yUR : edge_slot; yUF : edge_slot; yUL : edge_slot; yUB : edge_slot;
  yDR : edge_slot; yDF : edge_slot; yDL : edge_slot; yDB : edge_slot;
  yFR : edge_slot; yFL : edge_slot; yBL : edge_slot; yBR : edge_slot
}.

(** * Rotation arithmetic *)

(** Turning a corner by two amounts in succession. *)
Definition twist_add (t u : twist) : twist :=
  match u with
  | T0 => t
  | T1 => match t with T0 => T1 | T1 => T2 | T2 => T0 end
  | T2 => match t with T0 => T2 | T1 => T0 | T2 => T1 end
  end.

(** Flipping an edge twice restores it. *)
Definition flip_add (a b : flip) : flip :=
  match b with
  | F0 => a
  | F1 => match a with F0 => F1 | F1 => F0 end
  end.

(** A corner rotated by [t] shows at position [i] the facelet it would
    otherwise show [t] positions earlier. *)
Definition corner_facet_before (i : corner_facet) (t : twist) : corner_facet :=
  match t with
  | T0 => i
  | T1 => match i with C0 => C2 | C1 => C0 | C2 => C1 end
  | T2 => match i with C0 => C1 | C1 => C2 | C2 => C0 end
  end.

(** The same for an edge. *)
Definition edge_facet_before (i : edge_facet) (f : flip) : edge_facet :=
  match f with
  | F0 => i
  | F1 => match i with E0 => E1 | E1 => E0 end
  end.

(** Rotating a piece already in a slot, used by the turn tables below. *)
Definition shift_corner (k : twist) (x : corner_slot) : corner_slot :=
  match k with T0 => x | _ => let (X, t) := x in (X, twist_add t k) end.

(** Flipping a piece already in a slot. *)
Definition shift_edge (k : flip) (y : edge_slot) : edge_slot :=
  match k with F0 => y | _ => let (Y, f) := y in (Y, flip_add f k) end.
