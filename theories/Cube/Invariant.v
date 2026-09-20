From Stdlib Require Import Arith List Lia.
From Rubik Require Export Cube.Group Cube.ParityTables.
Import ListNotations.

(** * Parity invariants

    Three quantities no move can change. They are what lets the orientation
    coordinates be packed: with the totals fixed, the last corner's rotation
    and the last edge's flip are determined by the others, so the two
    orientation coordinates hold 2187 and 2048 values rather than 6561 and
    4096. The slice count is what makes the slice coordinate a choice of four
    slots out of twelve rather than an arbitrary mask. *)

(** The rotations of all eight corners, added up in the group of turns. *)
Definition twist_total (c : cube) : twist := fold_right twist_add T0 (twists c).

(** The flips of all twelve edges, added up. *)
Definition flip_total (c : cube) : flip := fold_right flip_add F0 (flips c).

(** How many slots hold a slice edge. *)
Definition slice_count (c : cube) : nat := count_occ Bool.bool_dec (slice_mask c) true.

(** Names for the twenty projections, so a turn becomes a rearrangement. *)
Ltac expose :=
  unfold twist_total, flip_total, slice_count, slice_mask, twists, flips, edge_pieces;
  cbn [corner_slots edge_slots quarter_cube turn_cube
       xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB
       yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR
       map fold_right fst snd];
  rewrite ?shift_corner_snd, ?shift_edge_snd, ?shift_corner_fst, ?shift_edge_fst;
  cbn [fst snd].

(** A quarter turn moves rotations between corners and adds a fixed amount to
    each, and those amounts cancel. *)
Lemma twist_total_quarter_cube f c : twist_total (quarter_cube f c) = twist_total c.
Proof.
  destruct_cube c; destruct f; expose;
    destruct t1, t2, t3, t4, t5, t6, t7, t8; reflexivity.
Qed.

(** A quarter turn flips edges in pairs, so the total flip is unchanged. *)
Lemma flip_total_quarter_cube f c : flip_total (quarter_cube f c) = flip_total c.
Proof.
  destruct_cube c; destruct f; expose;
    destruct g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12; reflexivity.
Qed.

(** A quarter turn only moves edges between slots, so it cannot change how
    many slice edges are in the slice. *)
Lemma slice_count_quarter_cube f c : slice_count (quarter_cube f c) = slice_count c.
Proof.
  destruct_cube c; destruct f; expose;
    generalize (is_slice Y1), (is_slice Y2), (is_slice Y3), (is_slice Y4),
      (is_slice Y5), (is_slice Y6), (is_slice Y7), (is_slice Y8),
      (is_slice Y9), (is_slice Y10), (is_slice Y11), (is_slice Y12);
    intros b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12;
    destruct b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12; reflexivity.
Qed.

(** Each invariant survives any turn amount, since a move is quarter turns. *)
Lemma twist_total_turn_cube m c : twist_total (turn_cube m c) = twist_total c.
Proof.
  destruct m as [f t]; destruct t; cbn [turn_cube];
    rewrite ?twist_total_quarter_cube; reflexivity.
Qed.

(** The edge flips likewise cancel whatever the turn amount. *)
Lemma flip_total_turn_cube m c : flip_total (turn_cube m c) = flip_total c.
Proof.
  destruct m as [f t]; destruct t; cbn [turn_cube];
    rewrite ?flip_total_quarter_cube; reflexivity.
Qed.

(** And a move only moves slice edges between slots. *)
Lemma slice_count_turn_cube m c : slice_count (turn_cube m c) = slice_count c.
Proof.
  destruct m as [f t]; destruct t; cbn [turn_cube];
    rewrite ?slice_count_quarter_cube; reflexivity.
Qed.

(** And therefore any sequence of moves. *)
Lemma twist_total_run_cube c p : twist_total (run_cube c p) = twist_total c.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  change (twist_total (run_cube (turn_cube m c) p) = twist_total c).
  rewrite IH; apply twist_total_turn_cube.
Qed.

(** The flip total survives a whole sequence. *)
Lemma flip_total_run_cube c p : flip_total (run_cube c p) = flip_total c.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  change (flip_total (run_cube (turn_cube m c) p) = flip_total c).
  rewrite IH; apply flip_total_turn_cube.
Qed.

(** So does the number of slice edges in the slice. *)
Lemma slice_count_run_cube c p : slice_count (run_cube c p) = slice_count c.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  change (slice_count (run_cube (turn_cube m c) p) = slice_count c).
  rewrite IH; apply slice_count_turn_cube.
Qed.

(** * What a physically valid cube must satisfy *)

(** Reading the cubies off a scramble is the same as scrambling the cubies. *)
Lemma to_cubies_scramble p : to_cubies (run init_state p) = run_cube solved_cube p.
Proof.
  replace (run init_state p) with (paint (run_cube solved_cube p))
    by (rewrite paint_run_cube, paint_solved_cube; reflexivity).
  apply to_cubies_paint.
Qed.

(** No reachable cube has a net corner rotation. A single corner twisted in
    place is therefore not a cube any scramble can produce. *)
Theorem twist_total_valid s : valid_state s -> twist_total (to_cubies s) = T0.
Proof.
  intros [p <-]; rewrite to_cubies_scramble, twist_total_run_cube; reflexivity.
Qed.

(** Nor a net edge flip, so a single flipped edge is likewise unreachable. *)
Theorem flip_total_valid s : valid_state s -> flip_total (to_cubies s) = F0.
Proof.
  intros [p <-]; rewrite to_cubies_scramble, flip_total_run_cube; reflexivity.
Qed.

(** And the four slice edges are always somewhere, so the slice coordinate
    ranges over choices of four slots out of twelve. *)
Theorem slice_count_valid s : valid_state s -> slice_count (to_cubies s) = 4.
Proof.
  intros [p <-]; rewrite to_cubies_scramble, slice_count_run_cube; reflexivity.
Qed.

(** * The fourth invariant: parity

    The three totals above are about orientation. The remaining invariant is
    about position, and it is the one that rules out a cube with exactly two
    pieces exchanged and everything else in place. A quarter turn is a
    four-cycle on the corners and a four-cycle on the edges. Each is odd, so
    each list's parity flips and their combination does not. *)

(** A position for each slot name, so a list of pieces becomes a list of
    numbers and can be counted for inversions. *)
Definition corner_rank (X : corner) : nat :=
  match X with
  | URF => 0 | UFL => 1 | ULB => 2 | UBR => 3
  | DFR => 4 | DLF => 5 | DBL => 6 | DRB => 7
  end.

(** And a position for each edge slot. *)
Definition edge_rank (Y : edge) : nat :=
  match Y with
  | UR => 0 | UF => 1 | UL => 2 | UB => 3 | DR => 4 | DF => 5
  | DL => 6 | DB => 7 | FR => 8 | FL => 9 | BL => 10 | BR => 11
  end.

(** Where the corners sit and where the edges sit, as numbers. *)
Definition corner_ranks (c : cube) : list nat := map corner_rank (corner_pieces c).

(** And where the edges sit. *)
Definition edge_ranks (c : cube) : list nat := map edge_rank (edge_pieces c).

(** A cube whose pieces are all different, which every reachable cube is. *)
Definition wellformed (c : cube) : Prop := NoDup (corner_ranks c) /\ NoDup (edge_ranks c).

(** The combined parity of the two rearrangements. *)
Definition cube_parity (c : cube) : bool := xorb (parity (corner_ranks c)) (parity (edge_ranks c)).

(** Expose both lists of a turned cube as rearrangements of the original. *)
Ltac expose_ranks :=
  unfold wellformed, cube_parity, corner_ranks, edge_ranks, corner_pieces, edge_pieces in *;
  cbn [corner_slots edge_slots quarter_cube
       xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB
       yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map] in *;
  rewrite ?shift_corner_fst, ?shift_edge_fst; cbn [fst map] in *.

(** A turn keeps the pieces all different. *)
Lemma wellformed_quarter_cube f c : wellformed c -> wellformed (quarter_cube f c).
Proof.
  destruct_cube c; intros [Hc He]; destruct f; expose_ranks; split.
  - apply (nodup_corners_Up _ _ _ _ _ _ _ _ Hc).
  - apply (nodup_edges_Up _ _ _ _ _ _ _ _ _ _ _ _ He).
  - apply (nodup_corners_Right _ _ _ _ _ _ _ _ Hc).
  - apply (nodup_edges_Right _ _ _ _ _ _ _ _ _ _ _ _ He).
  - apply (nodup_corners_Front _ _ _ _ _ _ _ _ Hc).
  - apply (nodup_edges_Front _ _ _ _ _ _ _ _ _ _ _ _ He).
  - apply (nodup_corners_Down _ _ _ _ _ _ _ _ Hc).
  - apply (nodup_edges_Down _ _ _ _ _ _ _ _ _ _ _ _ He).
  - apply (nodup_corners_Left _ _ _ _ _ _ _ _ Hc).
  - apply (nodup_edges_Left _ _ _ _ _ _ _ _ _ _ _ _ He).
  - apply (nodup_corners_Back _ _ _ _ _ _ _ _ Hc).
  - apply (nodup_edges_Back _ _ _ _ _ _ _ _ _ _ _ _ He).
Qed.

(** And it flips both parities, so their combination is unchanged. *)
Lemma cube_parity_quarter_cube f c : wellformed c -> cube_parity (quarter_cube f c) = cube_parity c.
Proof.
  destruct_cube c; intros [Hc He]; destruct f; expose_ranks.
  - rewrite (parity_corners_Up _ _ _ _ _ _ _ _ Hc), (parity_edges_Up _ _ _ _ _ _ _ _ _ _ _ _ He);
      destruct (parity _), (parity _); reflexivity.
  - rewrite (parity_corners_Right _ _ _ _ _ _ _ _ Hc), (parity_edges_Right _ _ _ _ _ _ _ _ _ _ _ _ He);
      destruct (parity _), (parity _); reflexivity.
  - rewrite (parity_corners_Front _ _ _ _ _ _ _ _ Hc), (parity_edges_Front _ _ _ _ _ _ _ _ _ _ _ _ He);
      destruct (parity _), (parity _); reflexivity.
  - rewrite (parity_corners_Down _ _ _ _ _ _ _ _ Hc), (parity_edges_Down _ _ _ _ _ _ _ _ _ _ _ _ He);
      destruct (parity _), (parity _); reflexivity.
  - rewrite (parity_corners_Left _ _ _ _ _ _ _ _ Hc), (parity_edges_Left _ _ _ _ _ _ _ _ _ _ _ _ He);
      destruct (parity _), (parity _); reflexivity.
  - rewrite (parity_corners_Back _ _ _ _ _ _ _ _ Hc), (parity_edges_Back _ _ _ _ _ _ _ _ _ _ _ _ He);
      destruct (parity _), (parity _); reflexivity.
Qed.

(** A whole move is one, two or three quarter turns. *)
Lemma wellformed_turn_cube m c : wellformed c -> wellformed (turn_cube m c).
Proof.
  destruct m as [f t]; destruct t; cbn [turn_cube]; intro H;
    repeat apply wellformed_quarter_cube; exact H.
Qed.

(** And a whole move, being one, two or three of them. *)
Lemma cube_parity_turn_cube m c : wellformed c -> cube_parity (turn_cube m c) = cube_parity c.
Proof.
  destruct m as [f t]; destruct t; cbn [turn_cube]; intro H;
    rewrite ?cube_parity_quarter_cube by auto using wellformed_quarter_cube; reflexivity.
Qed.

(** And a whole sequence. *)
Lemma wellformed_run_cube c p : wellformed c -> wellformed (run_cube c p).
Proof.
  revert c; induction p as [| m p IH]; intros c H; [exact H |].
  change (run_cube c (m :: p)) with (run_cube (turn_cube m c) p).
  apply IH, wellformed_turn_cube, H.
Qed.

(** And a whole sequence. *)
Lemma cube_parity_run_cube c p : wellformed c -> cube_parity (run_cube c p) = cube_parity c.
Proof.
  revert c; induction p as [| m p IH]; intros c H; [reflexivity |].
  change (run_cube c (m :: p)) with (run_cube (turn_cube m c) p).
  rewrite (IH (turn_cube m c) (wellformed_turn_cube m c H)); apply cube_parity_turn_cube, H.
Qed.

(** The solved cube has all pieces different and even parity. *)
Lemma wellformed_solved_cube : wellformed solved_cube.
Proof.
  split; cbn [corner_ranks edge_ranks corner_pieces edge_pieces corner_slots edge_slots
              solved_cube map fst]; repeat constructor; simpl; intuition discriminate.
Qed.

(** The solved cube is in order, so its parity is even, *)
Lemma cube_parity_solved_cube : cube_parity solved_cube = false.
Proof. reflexivity. Qed.

(** So every cube a sequence can produce has all pieces different and even
    parity. A cube with exactly two pieces exchanged has odd parity, so no
    sequence produces it: that is what the last step of a solving method needs
    in order to know it is already finished. *)
Theorem wellformed_element p : wellformed (element p).
Proof. apply wellformed_run_cube, wellformed_solved_cube. Qed.

(** and so is that of every cube a sequence produces. A cube with exactly two
    pieces exchanged is odd, so no sequence produces it. *)
Theorem cube_parity_element p : cube_parity (element p) = false.
Proof.
  unfold element; rewrite cube_parity_run_cube by apply wellformed_solved_cube;
    apply cube_parity_solved_cube.
Qed.
