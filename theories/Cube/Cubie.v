From Stdlib Require Import List.
From Rubik Require Export Cube.CubieDefs Cube.CubieTables.
Import ListNotations.

(** * The piece model and the sticker model agree

    The tables in [CubieTables] say how pieces move and what colours they
    show. Everything here ties them back to the stickers, so that a claim
    about pieces is a claim about the cube the viewer draws. *)

(** Rotating a piece leaves it the same piece and adds to its rotation. *)
Lemma shift_corner_fst k x : fst (shift_corner k x) = fst x.
Proof. destruct x; destruct k; reflexivity. Qed.

(** And adds to its rotation. *)
Lemma shift_corner_snd k x : snd (shift_corner k x) = twist_add (snd x) k.
Proof. destruct x; destruct k; reflexivity. Qed.

(** Flipping leaves it the same piece. *)
Lemma shift_edge_fst k y : fst (shift_edge k y) = fst y.
Proof. destruct y; destruct k; reflexivity. Qed.

(** And adds to its flip. *)
Lemma shift_edge_snd k y : snd (shift_edge k y) = flip_add (snd y) k.
Proof. destruct y; destruct k; reflexivity. Qed.

(** * The turn tables agree with the stickers *)

(** Rotating by two amounts in succession steps the facelet position twice. *)
Lemma corner_facet_before_add i t k : corner_facet_before i (twist_add t k) = corner_facet_before (corner_facet_before i k) t.
Proof. destruct i, t, k; reflexivity. Qed.

(** The same for an edge's two positions. *)
Lemma edge_facet_before_add i f k : edge_facet_before i (flip_add f k) = edge_facet_before (edge_facet_before i k) f.
Proof. destruct i, f, k; reflexivity. Qed.

(** Rotating a piece within its slot shifts which facelet each position shows. *)
Lemma corner_color_shift k x i :
  corner_color (shift_corner k x) i = corner_color x (corner_facet_before i k).
Proof.
  destruct x as [X t]; destruct k; cbn [shift_corner corner_color];
    rewrite ?corner_facet_before_add; reflexivity.
Qed.

(** And flipping an edge swaps which facelet each position shows. *)
Lemma edge_color_shift k y i :
  edge_color (shift_edge k y) i = edge_color y (edge_facet_before i k).
Proof.
  destruct y as [Y f]; destruct k; cbn [shift_edge edge_color];
    rewrite ?edge_facet_before_add; reflexivity.
Qed.

(** Turning the cubies and then painting is painting and then turning the
    stickers. This is the bridge every later coordinate proof rests on. *)
Theorem paint_quarter_cube f c : paint (quarter_cube f c) = quarter f (paint c).
Proof.
  destruct c; destruct f; cbn [paint quarter_cube quarter];
    rewrite ?corner_color_shift, ?edge_color_shift;
    cbn [corner_facet_before edge_facet_before]; reflexivity.
Qed.

(** The twenty slots in table order, so a projection is one [map] away. *)
Definition corner_slots (c : cube) : list corner_slot :=
  [xURF c; xUFL c; xULB c; xUBR c; xDFR c; xDLF c; xDBL c; xDRB c].

(** And the twelve edge slots. *)
Definition edge_slots (c : cube) : list edge_slot :=
  [yUR c; yUF c; yUL c; yUB c; yDR c; yDF c; yDL c; yDB c;
   yFR c; yFL c; yBL c; yBR c].

(** Listing the slots loses nothing: two cubes with the same slots are equal. *)
Lemma slots_determine x y :
  corner_slots x = corner_slots y -> edge_slots x = edge_slots y -> x = y.
Proof.
  destruct x, y; unfold corner_slots, edge_slots; cbn; intros H1 H2;
    injection H1 as ? ? ? ? ? ? ? ?; injection H2 as ? ? ? ? ? ? ? ? ? ? ? ?;
    subst; reflexivity.
Qed.

(** Comparing one slot. Deciding equality field by field on the whole record
    would work but produces a term extraction cannot digest, so the comparison
    goes through the slot lists instead. *)
Definition corner_slot_eq_dec (x y : corner_slot) : {x = y} + {x <> y}.
Proof. decide equality; decide equality. Defined.

(** And one edge slot. *)
Definition edge_slot_eq_dec (x y : edge_slot) : {x = y} + {x <> y}.
Proof. decide equality; decide equality. Defined.

(** Comparing two cubes, slot by slot. *)
Definition cube_eqb (x y : cube) : bool :=
  andb (if list_eq_dec corner_slot_eq_dec (corner_slots x) (corner_slots y)
        then true else false)
       (if list_eq_dec edge_slot_eq_dec (edge_slots x) (edge_slots y)
        then true else false).

(** The comparison decides equality exactly. *)
Lemma cube_eqb_spec x y : cube_eqb x y = true <-> x = y.
Proof.
  unfold cube_eqb; split.
  - intro H; apply Bool.andb_true_iff in H as [H1 H2].
    destruct (list_eq_dec corner_slot_eq_dec _ _) as [Hc |]; [| discriminate].
    destruct (list_eq_dec edge_slot_eq_dec _ _) as [He |]; [| discriminate].
    apply slots_determine; assumption.
  - intros ->.
    destruct (list_eq_dec corner_slot_eq_dec _ _); [| contradiction].
    destruct (list_eq_dec edge_slot_eq_dec _ _); [| contradiction]; reflexivity.
Qed.

(** * Moves and sequences *)

(** Every piece at home and unturned. *)
Definition solved_cube : cube :=
  Cube (URF, T0) (UFL, T0) (ULB, T0) (UBR, T0)
       (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
       (UR, F0) (UF, F0) (UL, F0) (UB, F0) (DR, F0) (DF, F0)
       (DL, F0) (DB, F0) (FR, F0) (FL, F0) (BL, F0) (BR, F0).

(** The solved cubies paint the solved cube. *)
Lemma paint_solved_cube : paint solved_cube = init_state.
Proof. reflexivity. Qed.

(** One, two, or three quarter turns, mirroring [turn]. *)
Definition turn_cube (m : move) (c : cube) : cube :=
  let (f, t) := m in
  match t with
  | CW => quarter_cube f c
  | Half => quarter_cube f (quarter_cube f c)
  | CCW => quarter_cube f (quarter_cube f (quarter_cube f c))
  end.

(** The bridge extends from quarter turns to every legal move. *)
Theorem paint_turn_cube m c : paint (turn_cube m c) = turn m (paint c).
Proof.
  destruct m as [f t]; destruct t; cbn [turn_cube]; unfold_moves;
    repeat rewrite paint_quarter_cube; reflexivity.
Qed.

(** A sequence acts on the cubies left to right, as it does on the stickers. *)
Definition run_cube (c : cube) (p : list move) : cube :=
  fold_left (fun c m => turn_cube m c) p c.

(** The bridge extends from moves to whole sequences. *)
Theorem paint_run_cube c p : paint (run_cube c p) = run (paint c) p.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  change (paint (run_cube (turn_cube m c) p) = run (turn m (paint c)) p).
  rewrite IH, paint_turn_cube; reflexivity.
Qed.

(** * Reading the cubies back off the stickers *)

(** A slot's three colors say which corner sits there and how it is turned. *)
Lemma corner_of_color x :
  corner_of (corner_color x C0) (corner_color x C1) (corner_color x C2) = x.
Proof. destruct x as [X t]; destruct X, t; reflexivity. Qed.

(** An edge slot's two colours say which edge sits there and whether it is
    flipped. *)
Lemma edge_of_color y :
  edge_of (edge_color y E0) (edge_color y E1) = y.
Proof. destruct y as [Y f]; destruct Y, f; reflexivity. Qed.

(** Painting a cube and reading it back recovers it exactly. *)
Theorem to_cubies_paint c : to_cubies (paint c) = c.
Proof.
  destruct c; cbn [paint to_cubies];
    rewrite !corner_of_color, !edge_of_color; reflexivity.
Qed.

(** Every cube a scramble can produce is painted by some cubie arrangement. *)
Lemma valid_painted s : valid_state s -> exists c, paint c = s.
Proof.
  intros [p <-]; exists (run_cube solved_cube p); rewrite paint_run_cube, paint_solved_cube; reflexivity.
Qed.

(** So on a physically valid cube the two models are inverse to one another,
    and the cubie reading loses nothing. *)
Theorem paint_to_cubies s : valid_state s -> paint (to_cubies s) = s.
Proof.
  intro H; destruct (valid_painted s H) as [c <-]; rewrite to_cubies_paint; reflexivity.
Qed.

(** * The move algebra on cubes

    Painting is injective, so every equation between sticker moves carries over
    to cubies unchanged. Both facts the normalisation needs come across this
    bridge. *)

(** Distinct cubes show distinct stickers, since to_cubies reads the cubies back. *)
Lemma paint_inj x y : paint x = paint y -> x = y.
Proof.
  intro H; rewrite <- (to_cubies_paint x), <- (to_cubies_paint y), H; reflexivity.
Qed.

(** Two turns of one face are one turn of that face, or nothing at all. *)
Lemma same_face_merge_cube (f : face) (t1 t2 : amount) :
  (forall c, turn_cube (f, t2) (turn_cube (f, t1) c) = c) \/
  (exists t3, forall c, turn_cube (f, t2) (turn_cube (f, t1) c) = turn_cube (f, t3) c).
Proof.
  destruct (same_face_merge f t1 t2) as [H | [t3 H]].
  - left; intro c; apply paint_inj; rewrite !paint_turn_cube; apply H.
  - right; exists t3; intro c; apply paint_inj; rewrite !paint_turn_cube; apply H.
Qed.

(** Turns of opposite faces commute. *)
Lemma move_comm_cube f g t1 t2 c :
  opposite f g = true ->
  turn_cube (f, t1) (turn_cube (g, t2) c) = turn_cube (g, t2) (turn_cube (f, t1) c).
Proof.
  intro H; apply paint_inj; rewrite !paint_turn_cube; apply move_comm, H.
Qed.

(** Running a sequence in stages is running the whole of it. *)
Lemma run_cube_app c p q : run_cube c (p ++ q) = run_cube (run_cube c p) q.
Proof. unfold run_cube; apply fold_left_app. Qed.

(** Following a move by its inverse restores the cube. *)
Lemma inverse_undoes_cube m c : turn_cube (inverse m) (turn_cube m c) = c.
Proof. apply paint_inj; rewrite !paint_turn_cube; apply inverse_undoes. Qed.

(** Undoing a whole sequence: its moves inverted, in the other order. *)
Definition inverse_path (p : list move) : list move := rev (map inverse p).

(** Undoing one more move means undoing it last. *)
Lemma inverse_path_cons m p : inverse_path (m :: p) = inverse_path p ++ [inverse m].
Proof. reflexivity. Qed.

(** Running a sequence and then undoing it leaves the cube alone. *)
Lemma run_cube_inverse_path c p : run_cube (run_cube c p) (inverse_path p) = c.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  rewrite inverse_path_cons.
  change (run_cube c (m :: p)) with (run_cube (turn_cube m c) p).
  rewrite run_cube_app, IH; apply inverse_undoes_cube.
Qed.

(** A cube that can be solved stays solvable however it is turned. *)
Definition solvable (c : cube) : Prop := exists p, run_cube c p = solved_cube.

(** A cube that can be solved stays solvable however it is turned. *)
Lemma solvable_run_cube c p : solvable c -> solvable (run_cube c p).
Proof.
  intros [r Hr]; exists (inverse_path p ++ r);
    rewrite run_cube_app, run_cube_inverse_path; exact Hr.
Qed.

(** * Reading a cube one aspect at a time

    Each of these projections is what one coordinate of the solver looks
    at, and each moves on its own under a turn. *)

(** How far each corner is turned in its slot. *)
Definition twists (c : cube) : list twist := map snd (corner_slots c).

(** Whether each edge is flipped in its slot. *)
Definition flips (c : cube) : list flip := map snd (edge_slots c).

(** Which edge piece occupies each slot. *)
Definition edge_pieces (c : cube) : list edge := map fst (edge_slots c).

(** The four edges belonging to the middle slice. *)
Definition is_slice (e : edge) : bool :=
  match e with FR | FL | BL | BR => true | _ => false end.

(** Which slots hold a middle-slice edge, in slot order. *)
Definition slice_mask (c : cube) : list bool := map is_slice (edge_pieces c).

(** Which corner sits in each slot. *)
Definition corner_pieces (c : cube) : list corner := map fst (corner_slots c).

(** Which edge sits in each of the eight non-slice slots, and in the slice. *)
Definition ud_pieces (c : cube) : list edge := firstn 8 (edge_pieces c).
(** Which edge sits in each of the four slice slots. *)
Definition slice_pieces (c : cube) : list edge := skipn 8 (edge_pieces c).

(** Splitting a cube into its twenty pieces and rotations, so that the
    subgroup conditions become equations between variables. *)
Ltac destruct_cube c :=
  destruct c as [[X1 t1] [X2 t2] [X3 t3] [X4 t4]
                 [X5 t5] [X6 t6] [X7 t7] [X8 t8]
                 [Y1 g1] [Y2 g2] [Y3 g3] [Y4 g4]
                 [Y5 g5] [Y6 g6] [Y7 g7] [Y8 g8]
                 [Y9 g9] [Y10 g10] [Y11 g11] [Y12 g12]].
