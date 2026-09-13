From Stdlib Require Import Bool List.
Import ListNotations.

(** * The sticker cube

    A cube as its 54 visible colours. Everything else in the development is
    checked against this: it is the model the viewer shows and the model a
    solution is finally judged against. *)

(** * Sticker representation *)

(** The six outward faces also name the colors of their solved stickers. *)
Inductive face := Up | Right | Front | Down | Left | Back.

(** A sticker color is named after the face it occupies in the solved cube. *)
Definition color := face.

(** Three entries share one shape, reused for rows, grids, and face groups. *)
Inductive triple (A : Type) := Triple (a b c : A).
Arguments Triple {A} _ _ _.

(** Three rows of three colors form a face viewed from outside the cube. *)
Definition grid := triple (triple color).

(** The 54 stickers are grouped as U/R/F and D/L/B, with row-major grids. *)
Definition state := (triple grid * triple grid)%type.

(** Filling a grid with one color describes a solved face. *)
Definition solid (c : color) : grid :=
  Triple (Triple c c c) (Triple c c c) (Triple c c c).

(** The solved cube places every sticker on the face matching its color. *)
Definition init_state : state :=
  (Triple (solid Up) (solid Right) (solid Front),
   Triple (solid Down) (solid Left) (solid Back)).

(** * Decidable equality *)

(** Face equality is decidable by comparing the six constructors. *)
Definition face_eq_dec (x y : face) : {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

(** Deciding equality entry by entry lifts an equality test to triples. *)
Definition triple_eq_dec {A} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (x y : triple A) : {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

(** Comparing all 54 stickers decides whether two cube states coincide. *)
Definition state_eq_dec (x y : state) : {x = y} + {x <> y}.
Proof.
  decide equality; repeat apply triple_eq_dec; apply face_eq_dec.
Defined.

(** A boolean view of state equality is convenient for computations. *)
Definition state_eq (x y : state) : bool :=
  if state_eq_dec x y then true else false.

(** The boolean comparison recognizes exactly equal states. *)
Lemma state_eq_correct x y : state_eq x y = true <-> x = y.
Proof.
  unfold state_eq; destruct (state_eq_dec x y); intuition discriminate.
Qed.

(** * Faces and moves *)

(** A fixed face order makes enumeration and search results deterministic. *)
Definition faces : list face := [Up; Right; Front; Down; Left; Back].
