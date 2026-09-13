From Stdlib Require Import Arith List Lia.
From Rubik Require Import BasicRubik.
Import ListNotations.

(** * Pruning the move space

    Two restrictions cut the branching without losing anything a solution
    needs: turning the same face twice running is the same as turning it once
    or not at all, and turns of opposite faces commute, so only one of their
    two orders is worth trying. *)

(** Faces in the model's U/R/F/D/L/B order, so that opposite faces differ by
    three and a total order on faces is available. *)
Definition face_rank (f : face) : nat :=
  match f with
  | Up => 0 | Right => 1 | Front => 2 | Down => 3 | Left => 4 | Back => 5
  end.

(** Opposite faces are the two ends of one axis: U and D, R and L, F and B. *)
Definition opposite (f g : face) : bool :=
  Nat.eqb (face_rank f + 3) (face_rank g) || Nat.eqb (face_rank g + 3) (face_rank f).

(** Turning the same face twice running is never part of a shortest solution,
    and opposite faces commute, so only one of their two orders is kept. *)
Definition allowed (prev : option move) (m : move) : bool :=
  match prev with
  | None => true
  | Some (p, _) =>
      andb (negb (Nat.eqb (face_rank (fst m)) (face_rank p)))
           (negb (andb (opposite (fst m) p) (Nat.ltb (face_rank p) (face_rank (fst m)))))
  end.

(** The moves still worth trying after a given move, written out rather than
    filtered.  [allowed] looks only at the previous move's face, so there are
    seven answers; naming them as constants keeps the search from rebuilding a
    list at every node. *)
Definition after_none : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, CW); (Right, Half);
   (Right, CCW); (Front, CW); (Front, Half); (Front, CCW); (Down, CW);
   (Down, Half); (Down, CCW); (Left, CW); (Left, Half); (Left, CCW);
   (Back, CW); (Back, Half); (Back, CCW)].

(** After an up turn: the four side faces, since down would only be tried in
    the other order. *)
Definition after_up : list move :=
  [(Right, CW); (Right, Half); (Right, CCW); (Front, CW); (Front, Half);
   (Front, CCW); (Left, CW); (Left, Half); (Left, CCW); (Back, CW);
   (Back, Half); (Back, CCW)].

(** After a right turn. *)
Definition after_right : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Front, CW); (Front, Half);
   (Front, CCW); (Down, CW); (Down, Half); (Down, CCW); (Back, CW);
   (Back, Half); (Back, CCW)].

(** After a front turn. *)
Definition after_front : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, CW); (Right, Half);
   (Right, CCW); (Down, CW); (Down, Half); (Down, CCW); (Left, CW);
   (Left, Half); (Left, CCW)].

(** After a down turn, where the opposite face is still worth trying. *)
Definition after_down : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, CW); (Right, Half);
   (Right, CCW); (Front, CW); (Front, Half); (Front, CCW); (Left, CW);
   (Left, Half); (Left, CCW); (Back, CW); (Back, Half); (Back, CCW)].

(** After a left turn. *)
Definition after_left : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, CW); (Right, Half);
   (Right, CCW); (Front, CW); (Front, Half); (Front, CCW); (Down, CW);
   (Down, Half); (Down, CCW); (Back, CW); (Back, Half); (Back, CCW)].

(** After a back turn. *)
Definition after_back : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, CW); (Right, Half);
   (Right, CCW); (Front, CW); (Front, Half); (Front, CCW); (Down, CW);
   (Down, Half); (Down, CCW); (Left, CW); (Left, Half); (Left, CCW)].

(** Pick the answer for the previous move's face. *)
Definition allowed_moves (prev : option move) : list move :=
  match prev with
  | None => after_none
  | Some (Up, _) => after_up
  | Some (Right, _) => after_right
  | Some (Front, _) => after_front
  | Some (Down, _) => after_down
  | Some (Left, _) => after_left
  | Some (Back, _) => after_back
  end.

(** They are exactly the legal moves that pass the pruning test. *)
Lemma allowed_moves_filter prev : allowed_moves prev = filter (allowed prev) Movel.
Proof. destruct prev as [[f t] |]; try destruct f; reflexivity. Qed.

(** * Trying the moves in turn *)

(** Try a list of moves in order. *)
Fixpoint choose_move (rec : move -> option (list move)) (l : list move)
  : option (list move) :=
  match l with
  | [] => None
  | m :: rest =>
      match rec m with
      | Some p => Some (m :: p)
      | None => choose_move rec rest
      end
  end.

(** A successful choice came from some move in the list. *)
Lemma choose_move_some rec l p :
  choose_move rec l = Some p ->
  exists m q, In m l /\ rec m = Some q /\ p = m :: q.
Proof.
  induction l as [| m l IH]; simpl; [discriminate |].
  destruct (rec m) as [q |] eqn:R.
  - intro H; inversion H; exists m, q; auto.
  - intro H; destruct (IH H) as [m' [q' [Hin [Hr He]]]]; exists m', q'; auto.
Qed.
