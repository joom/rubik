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
    which is one computation. [crun_element] below is that change of view. *)

(** * Reading a slot by name *)

(** The piece in a named corner slot, and in a named edge slot. *)
Definition getc (c : cube) (X : corner) : cslot :=
  match X with
  | URF => xURF c | UFL => xUFL c | ULB => xULB c | UBR => xUBR c
  | DFR => xDFR c | DLF => xDLF c | DBL => xDBL c | DRB => xDRB c
  end.

(** And the piece in a named edge slot. *)
Definition gete (c : cube) (Y : edge) : eslot :=
  match Y with
  | UR => yUR c | UF => yUF c | UL => yUL c | UB => yUB c
  | DR => yDR c | DF => yDF c | DL => yDL c | DB => yDB c
  | FR => yFR c | FL => yFL c | BL => yBL c | BR => yBR c
  end.

(** A cube is exactly its twenty slot readings. *)
Lemma cube_eta c :
  c = Cube (getc c URF) (getc c UFL) (getc c ULB) (getc c UBR)
           (getc c DFR) (getc c DLF) (getc c DBL) (getc c DRB)
           (gete c UR) (gete c UF) (gete c UL) (gete c UB)
           (gete c DR) (gete c DF) (gete c DL) (gete c DB)
           (gete c FR) (gete c FL) (gete c BL) (gete c BR).
Proof. destruct c; reflexivity. Qed.

(** So an equation between cubes can be proved one slot at a time. *)
Lemma cube_ext x y :
  (forall X, getc x X = getc y X) -> (forall Y, gete x Y = gete y Y) -> x = y.
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
Definition capply (c : cube) (x : cslot) : cslot :=
  let (X, t) := x in cshift t (getc c X).

(** And the same for an edge reading. *)
Definition eapply (c : cube) (y : eslot) : eslot :=
  let (Y, f) := y in eshift f (gete c Y).

(** Applying the rearrangement [g] to the cube [c]. Every slot of the result
    reads the slot of [c] that [g] says feeds it. *)
Definition ccompose (c g : cube) : cube :=
  Cube (capply c (xURF g)) (capply c (xUFL g)) (capply c (xULB g))
       (capply c (xUBR g)) (capply c (xDFR g)) (capply c (xDLF g))
       (capply c (xDBL g)) (capply c (xDRB g))
       (eapply c (yUR g)) (eapply c (yUF g)) (eapply c (yUL g))
       (eapply c (yUB g)) (eapply c (yDR g)) (eapply c (yDF g))
       (eapply c (yDL g)) (eapply c (yDB g)) (eapply c (yFR g))
       (eapply c (yFL g)) (eapply c (yBL g)) (eapply c (yBR g)).

(** A corner slot of a composition reads what the right cube says to read, *)
Lemma getc_ccompose c g X : getc (ccompose c g) X = capply c (getc g X).
Proof. destruct X; reflexivity. Qed.

(** and the same for an edge slot. *)
Lemma gete_ccompose c g Y : gete (ccompose c g) Y = eapply c (gete g Y).
Proof. destruct Y; reflexivity. Qed.

(** Reading a slot of the solved cube gives that slot's own piece, unturned. *)
Lemma getc_csolved X : getc csolved X = (X, T0).
Proof. destruct X; reflexivity. Qed.

(** and an edge slot its own piece, unflipped. *)
Lemma gete_csolved Y : gete csolved Y = (Y, F0).
Proof. destruct Y; reflexivity. Qed.

(** The solved cube is the identity on both sides. *)
Lemma ccompose_id_r c : ccompose c csolved = c.
Proof.
  apply cube_ext; intros; rewrite ?getc_ccompose, ?gete_ccompose,
    ?getc_csolved, ?gete_csolved; reflexivity.
Qed.

(** And on the left. *)
Lemma ccompose_id_l g : ccompose csolved g = g.
Proof.
  apply cube_ext; intro X; rewrite ?getc_ccompose, ?gete_ccompose.
  - destruct (getc g X) as [P t]; cbn; rewrite getc_csolved;
      destruct t, P; reflexivity.
  - destruct (gete g X) as [P f]; cbn; rewrite gete_csolved;
      destruct f, P; reflexivity.
Qed.

(** Rotating a slot reading further commutes with following it through a
    cube, which is what makes composition associative. *)
Lemma capply_shift c k x : capply c (cshift k x) = cshift k (capply c x).
Proof.
  destruct x as [X t]; destruct k, t; simpl;
    destruct (getc c X) as [P u]; destruct u; reflexivity.
Qed.

(** And the same for an edge reading. *)
Lemma eapply_shift c k y : eapply c (eshift k y) = eshift k (eapply c y).
Proof.
  destruct y as [Y f]; destruct k, f; simpl;
    destruct (gete c Y) as [P u]; destruct u; reflexivity.
Qed.

(** Following a reading through a composition is following it through each in
    turn, which is what makes composition associative. *)
Lemma capply_ccompose a b x : capply (ccompose a b) x = capply a (capply b x).
Proof.
  destruct x as [X t]; cbn [capply]; rewrite getc_ccompose.
  symmetry; apply capply_shift.
Qed.

(** The same for an edge reading. *)
Lemma eapply_ccompose a b y : eapply (ccompose a b) y = eapply a (eapply b y).
Proof.
  destruct y as [Y f]; cbn [eapply]; rewrite gete_ccompose.
  symmetry; apply eapply_shift.
Qed.

(** Composition is associative, so a sequence of rearrangements can be folded
    in either direction. *)
Lemma ccompose_assoc a b g :
  ccompose (ccompose a b) g = ccompose a (ccompose b g).
Proof.
  apply cube_ext; intro X;
    rewrite ?getc_ccompose, ?gete_ccompose;
    [apply capply_ccompose | apply eapply_ccompose].
Qed.

(** * Turning is composing

    A quarter turn rearranges the slots the same way whatever sits in them, so
    turning a cube is composing it with the cube that one turn produces from
    solved. *)
Lemma cquarter_element f d : cquarter f d = ccompose d (cquarter f csolved).
Proof. destruct_cube d; destruct f; reflexivity. Qed.

(** The same for a whole move. *)
Lemma cturn_element m d : cturn m d = ccompose d (cturn m csolved).
Proof.
  destruct m as [f t]; destruct t; cbn [cturn].
  - apply cquarter_element.
  - rewrite (cquarter_element f (cquarter f d)), (cquarter_element f d),
      (cquarter_element f (cquarter f csolved)), ccompose_assoc; reflexivity.
  - rewrite (cquarter_element f (cquarter f (cquarter f d))),
      (cquarter_element f (cquarter f d)), (cquarter_element f d),
      (cquarter_element f (cquarter f (cquarter f csolved))),
      (cquarter_element f (cquarter f csolved)),
      !ccompose_assoc; reflexivity.
Qed.

(** And for a whole sequence. Running a sequence on any cube is composing that
    cube with the single cube the sequence denotes, so a claim about every
    cube a sequence might meet becomes a claim about one cube. *)
Theorem crun_element c p : crun c p = ccompose c (crun csolved p).
Proof.
  revert c; induction p as [| m p IH]; intro c;
    [symmetry; apply ccompose_id_r |].
  change (crun c (m :: p)) with (crun (cturn m c) p).
  change (crun csolved (m :: p)) with (crun (cturn m csolved) p).
  rewrite (IH (cturn m c)), (IH (cturn m csolved)),
    (cturn_element m c), ccompose_assoc; reflexivity.
Qed.

(** * Sequences as group elements

    A sequence denotes the cube it produces from solved. Concatenating
    sequences composes their cubes, so questions about sequences become
    questions about cubes. *)

(** The cube a sequence denotes. *)
Definition element (p : list move) : cube := crun csolved p.

(** Concatenation composes. *)
Lemma element_app p q : element (p ++ q) = ccompose (element p) (element q).
Proof. unfold element; rewrite crun_app; apply crun_element. Qed.

(** The empty sequence denotes the solved cube. *)
Lemma element_nil : element [] = csolved.
Proof. reflexivity. Qed.

(** Running a sequence is composing with what it denotes. *)
Lemma crun_by_element c p : crun c p = ccompose c (element p).
Proof. apply crun_element. Qed.

(** Undoing a sequence composes to the solved cube on both sides, so the
    reversed sequence denotes an inverse. *)
Lemma element_inverse_r p :
  ccompose (element p) (element (inverse_path p)) = csolved.
Proof.
  rewrite <- element_app; unfold element; rewrite crun_app;
    apply crun_inverse_path.
Qed.

(** * Leaving a piece alone

    A sequence that fixes a piece is one whose cube holds that piece at home
    and unturned. That is a single reading of a single cube, so it can be
    checked by computing. *)

(** The pieces a rearrangement leaves exactly where they belong. *)
Definition fixesc (g : cube) (P : corner) : Prop := getc g P = (P, T0).

(** And the edge pieces. *)
Definition fixese (g : cube) (P : edge) : Prop := gete g P = (P, F0).

(** Composing on the left leaves such a slot reading alone, whatever it was. *)
Lemma capply_fixesc g P t : fixesc g P -> capply g (P, t) = (P, t).
Proof. unfold fixesc; intro H; cbn [capply]; rewrite H; destruct t; reflexivity. Qed.

(** The same for an edge reading. *)
Lemma eapply_fixese g P f : fixese g P -> eapply g (P, f) = (P, f).
Proof. unfold fixese; intro H; cbn [eapply]; rewrite H; destruct f; reflexivity. Qed.

(** A cube that can be solved is itself the cube of some sequence: undo the
    solution and the solved cube runs to it. *)
Lemma csolvable_element c : csolvable c -> exists r, element r = c.
Proof.
  intros [p Hp]; exists (inverse_path p).
  rewrite crun_by_element in Hp.
  symmetry; rewrite <- (ccompose_id_r c), <- (element_inverse_r p),
    <- ccompose_assoc, Hp; apply ccompose_id_l.
Qed.
