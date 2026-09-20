From Stdlib Require Import List.
From Rubik Require Export Cube.Cubie.
Import ListNotations.

(** * The cube as a group

    A cube records where each piece sits. It can also be read as the
    rearrangement that put it there, and then two cubes can be composed.

    This is what makes a solving method provable. A claim like "this sequence
    brings that piece home without disturbing the solved ones" quantifies over
    every cube it might be applied to, which no computation can check. Composed
    the other way it becomes a claim about the single cube the sequence denotes,
    which is one computation. [run_cube_element] below is that change of view. *)

(** * Reading a slot by name *)

(** The piece in a named corner slot, and in a named edge slot. *)
Definition read_corner (c : cube) (X : corner) : corner_slot :=
  match X with
  | URF => xURF c | UFL => xUFL c | ULB => xULB c | UBR => xUBR c
  | DFR => xDFR c | DLF => xDLF c | DBL => xDBL c | DRB => xDRB c
  end.

(** And the piece in a named edge slot. *)
Definition read_edge (c : cube) (Y : edge) : edge_slot :=
  match Y with
  | UR => yUR c | UF => yUF c | UL => yUL c | UB => yUB c
  | DR => yDR c | DF => yDF c | DL => yDL c | DB => yDB c
  | FR => yFR c | FL => yFL c | BL => yBL c | BR => yBR c
  end.

(** A cube is exactly its twenty slot readings. *)
Lemma cube_eta c :
  c = Cube (read_corner c URF) (read_corner c UFL) (read_corner c ULB) (read_corner c UBR)
           (read_corner c DFR) (read_corner c DLF) (read_corner c DBL) (read_corner c DRB)
           (read_edge c UR) (read_edge c UF) (read_edge c UL) (read_edge c UB)
           (read_edge c DR) (read_edge c DF) (read_edge c DL) (read_edge c DB)
           (read_edge c FR) (read_edge c FL) (read_edge c BL) (read_edge c BR).
Proof. destruct c; reflexivity. Qed.

(** So an equation between cubes can be proved one slot at a time. *)
Lemma cube_ext x y :
  (forall X, read_corner x X = read_corner y X) -> (forall Y, read_edge x Y = read_edge y Y) -> x = y.
Proof.
  intros Hc He; rewrite (cube_eta x), (cube_eta y),
    (Hc URF), (Hc UFL), (Hc ULB), (Hc UBR),
    (Hc DFR), (Hc DLF), (Hc DBL), (Hc DRB),
    (He UR), (He UF), (He UL), (He UB), (He DR), (He DF),
    (He DL), (He DB), (He FR), (He FL), (He BL), (He BR);
    reflexivity.
Qed.

(** * Composition *)

(** Follow one slot reading through a cube: the entry says which piece to look
    up and how much further to rotate what is found. *)
Definition follow_corner (c : cube) (x : corner_slot) : corner_slot :=
  let (X, t) := x in shift_corner t (read_corner c X).

(** And the same for an edge reading. *)
Definition follow_edge (c : cube) (y : edge_slot) : edge_slot :=
  let (Y, f) := y in shift_edge f (read_edge c Y).

(** Applying the rearrangement [g] to the cube [c]. Every slot of the result
    reads the slot of [c] that [g] says feeds it. *)
Definition compose (c g : cube) : cube :=
  Cube (follow_corner c (xURF g)) (follow_corner c (xUFL g)) (follow_corner c (xULB g))
       (follow_corner c (xUBR g)) (follow_corner c (xDFR g)) (follow_corner c (xDLF g))
       (follow_corner c (xDBL g)) (follow_corner c (xDRB g))
       (follow_edge c (yUR g)) (follow_edge c (yUF g)) (follow_edge c (yUL g))
       (follow_edge c (yUB g)) (follow_edge c (yDR g)) (follow_edge c (yDF g))
       (follow_edge c (yDL g)) (follow_edge c (yDB g)) (follow_edge c (yFR g))
       (follow_edge c (yFL g)) (follow_edge c (yBL g)) (follow_edge c (yBR g)).

(** A corner slot of a composition reads what the right cube says to read, *)
Lemma read_corner_compose c g X : read_corner (compose c g) X = follow_corner c (read_corner g X).
Proof. destruct X; reflexivity. Qed.

(** and the same for an edge slot. *)
Lemma read_edge_compose c g Y : read_edge (compose c g) Y = follow_edge c (read_edge g Y).
Proof. destruct Y; reflexivity. Qed.

(** Reading a slot of the solved cube gives that slot's own piece, unturned. *)
Lemma read_corner_solved_cube X : read_corner solved_cube X = (X, T0).
Proof. destruct X; reflexivity. Qed.

(** and an edge slot its own piece, unflipped. *)
Lemma read_edge_solved_cube Y : read_edge solved_cube Y = (Y, F0).
Proof. destruct Y; reflexivity. Qed.

(** The solved cube is the identity on both sides. *)
Lemma compose_id_r c : compose c solved_cube = c.
Proof.
  apply cube_ext; intros; rewrite ?read_corner_compose, ?read_edge_compose,
    ?read_corner_solved_cube, ?read_edge_solved_cube; reflexivity.
Qed.

(** And on the left. *)
Lemma compose_id_l g : compose solved_cube g = g.
Proof.
  apply cube_ext; intro X; rewrite ?read_corner_compose, ?read_edge_compose.
  - destruct (read_corner g X) as [P t]; cbn; rewrite read_corner_solved_cube;
      destruct t, P; reflexivity.
  - destruct (read_edge g X) as [P f]; cbn; rewrite read_edge_solved_cube;
      destruct f, P; reflexivity.
Qed.

(** Rotating a slot reading further commutes with following it through a
    cube, which is what makes composition associative. *)
Lemma follow_corner_shift c k x : follow_corner c (shift_corner k x) = shift_corner k (follow_corner c x).
Proof.
  destruct x as [X t]; destruct k, t; simpl;
    destruct (read_corner c X) as [P u]; destruct u; reflexivity.
Qed.

(** And the same for an edge reading. *)
Lemma follow_edge_shift c k y : follow_edge c (shift_edge k y) = shift_edge k (follow_edge c y).
Proof.
  destruct y as [Y f]; destruct k, f; simpl;
    destruct (read_edge c Y) as [P u]; destruct u; reflexivity.
Qed.

(** Following a reading through a composition is following it through each in
    turn, which is what makes composition associative. *)
Lemma follow_corner_compose a b x : follow_corner (compose a b) x = follow_corner a (follow_corner b x).
Proof.
  destruct x as [X t]; cbn [follow_corner]; rewrite read_corner_compose.
  symmetry; apply follow_corner_shift.
Qed.

(** The same for an edge reading. *)
Lemma follow_edge_compose a b y : follow_edge (compose a b) y = follow_edge a (follow_edge b y).
Proof.
  destruct y as [Y f]; cbn [follow_edge]; rewrite read_edge_compose.
  symmetry; apply follow_edge_shift.
Qed.

(** Composition is associative, so a sequence of rearrangements can be folded
    in either direction. *)
Lemma compose_assoc a b g :
  compose (compose a b) g = compose a (compose b g).
Proof.
  apply cube_ext; intro X;
    rewrite ?read_corner_compose, ?read_edge_compose;
    [apply follow_corner_compose | apply follow_edge_compose].
Qed.

(** * Turning is composing

    A quarter turn rearranges the slots the same way whatever sits in them, so
    turning a cube is composing it with the cube that one turn produces from
    solved. *)
Lemma quarter_cube_element f d : quarter_cube f d = compose d (quarter_cube f solved_cube).
Proof. destruct_cube d; destruct f; reflexivity. Qed.

(** The same for a whole move. *)
Lemma turn_cube_element m d : turn_cube m d = compose d (turn_cube m solved_cube).
Proof.
  destruct m as [f t]; destruct t; cbn [turn_cube].
  - apply quarter_cube_element.
  - rewrite (quarter_cube_element f (quarter_cube f d)), (quarter_cube_element f d),
      (quarter_cube_element f (quarter_cube f solved_cube)), compose_assoc; reflexivity.
  - rewrite (quarter_cube_element f (quarter_cube f (quarter_cube f d))),
      (quarter_cube_element f (quarter_cube f d)), (quarter_cube_element f d),
      (quarter_cube_element f (quarter_cube f (quarter_cube f solved_cube))),
      (quarter_cube_element f (quarter_cube f solved_cube)),
      !compose_assoc; reflexivity.
Qed.

(** And for a whole sequence. Running a sequence on any cube is composing that
    cube with the single cube the sequence denotes, so a claim about every
    cube a sequence might meet becomes a claim about one cube. *)
Theorem run_cube_element c p : run_cube c p = compose c (run_cube solved_cube p).
Proof.
  revert c; induction p as [| m p IH]; intro c;
    [symmetry; apply compose_id_r |].
  change (run_cube c (m :: p)) with (run_cube (turn_cube m c) p).
  change (run_cube solved_cube (m :: p)) with (run_cube (turn_cube m solved_cube) p).
  rewrite (IH (turn_cube m c)), (IH (turn_cube m solved_cube)),
    (turn_cube_element m c), compose_assoc; reflexivity.
Qed.

(** * Sequences as group elements

    A sequence denotes the cube it produces from solved. Concatenating
    sequences composes their cubes, so questions about sequences become
    questions about cubes. *)

(** The cube a sequence denotes. *)
Definition element (p : list move) : cube := run_cube solved_cube p.

(** Concatenation composes. *)
Lemma element_app p q : element (p ++ q) = compose (element p) (element q).
Proof. unfold element; rewrite run_cube_app; apply run_cube_element. Qed.

(** The empty sequence denotes the solved cube. *)
Lemma element_nil : element [] = solved_cube.
Proof. reflexivity. Qed.

(** Running a sequence is composing with what it denotes. *)
Lemma run_cube_by_element c p : run_cube c p = compose c (element p).
Proof. apply run_cube_element. Qed.

(** Undoing a sequence composes to the solved cube on both sides, so the
    reversed sequence denotes an inverse. *)
Lemma element_inverse_r p :
  compose (element p) (element (inverse_path p)) = solved_cube.
Proof.
  rewrite <- element_app; unfold element; rewrite run_cube_app;
    apply run_cube_inverse_path.
Qed.

(** * Leaving a piece alone

    A sequence that fixes a piece is one whose cube holds that piece at home
    and unturned. That is a single reading of a single cube, so it can be
    checked by computing. *)

(** The pieces a rearrangement leaves exactly where they belong. *)
Definition fixes_corner (g : cube) (P : corner) : Prop := read_corner g P = (P, T0).

(** And the edge pieces. *)
Definition fixes_edge (g : cube) (P : edge) : Prop := read_edge g P = (P, F0).

(** Composing on the left leaves such a slot reading alone, whatever it was. *)
Lemma follow_corner_fixed g P t : fixes_corner g P -> follow_corner g (P, t) = (P, t).
Proof. unfold fixes_corner; intro H; cbn [follow_corner]; rewrite H; destruct t; reflexivity. Qed.

(** The same for an edge reading. *)
Lemma follow_edge_fixed g P f : fixes_edge g P -> follow_edge g (P, f) = (P, f).
Proof. unfold fixes_edge; intro H; cbn [follow_edge]; rewrite H; destruct f; reflexivity. Qed.

(** A cube that can be solved is itself the cube of some sequence: undo the
    solution and the solved cube runs to it. *)
Lemma solvable_element c : solvable c -> exists r, element r = c.
Proof.
  intros [p Hp]; exists (inverse_path p).
  rewrite run_cube_by_element in Hp.
  symmetry; rewrite <- (compose_id_r c), <- (element_inverse_r p),
    <- compose_assoc, Hp; apply compose_id_l.
Qed.
