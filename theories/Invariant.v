From Stdlib Require Import Arith List Lia.
From Rubik Require Export Cubie.
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
  unfold twist_total, flip_total, slice_count, slice_mask, twists, flips, epieces;
  cbn [cslots eslots cquarter cm2f
       xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB
       yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR
       map fold_right fst snd];
  rewrite ?cshift_snd, ?eshift_snd, ?cshift_fst, ?eshift_fst;
  cbn [fst snd].

(** A quarter turn moves rotations between corners and adds a fixed amount to
    each, and those amounts cancel. *)
Lemma twist_total_cquarter f c : twist_total (cquarter f c) = twist_total c.
Proof.
  destruct_cube c; destruct f; expose;
    destruct t1, t2, t3, t4, t5, t6, t7, t8; reflexivity.
Qed.

(** A quarter turn flips edges in pairs, so the total flip is unchanged. *)
Lemma flip_total_cquarter f c : flip_total (cquarter f c) = flip_total c.
Proof.
  destruct_cube c; destruct f; expose;
    destruct g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12; reflexivity.
Qed.

(** A quarter turn only moves edges between slots, so it cannot change how
    many slice edges are in the slice. *)
Lemma slice_count_cquarter f c : slice_count (cquarter f c) = slice_count c.
Proof.
  destruct_cube c; destruct f; expose;
    generalize (is_slice Y1), (is_slice Y2), (is_slice Y3), (is_slice Y4),
      (is_slice Y5), (is_slice Y6), (is_slice Y7), (is_slice Y8),
      (is_slice Y9), (is_slice Y10), (is_slice Y11), (is_slice Y12);
    intros b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12;
    destruct b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12; reflexivity.
Qed.

(** Each invariant survives any turn amount, since a move is quarter turns. *)
Lemma twist_total_cm2f m c : twist_total (cm2f m c) = twist_total c.
Proof.
  destruct m as [f t]; destruct t; cbn [cm2f];
    rewrite ?twist_total_cquarter; reflexivity.
Qed.

(** The edge flips likewise cancel whatever the turn amount. *)
Lemma flip_total_cm2f m c : flip_total (cm2f m c) = flip_total c.
Proof.
  destruct m as [f t]; destruct t; cbn [cm2f];
    rewrite ?flip_total_cquarter; reflexivity.
Qed.

(** And a move only moves slice edges between slots. *)
Lemma slice_count_cm2f m c : slice_count (cm2f m c) = slice_count c.
Proof.
  destruct m as [f t]; destruct t; cbn [cm2f];
    rewrite ?slice_count_cquarter; reflexivity.
Qed.

(** And therefore any sequence of moves. *)
Lemma twist_total_crun c p : twist_total (crun c p) = twist_total c.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  change (twist_total (crun (cm2f m c) p) = twist_total c).
  rewrite IH; apply twist_total_cm2f.
Qed.

(** The flip total survives a whole sequence. *)
Lemma flip_total_crun c p : flip_total (crun c p) = flip_total c.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  change (flip_total (crun (cm2f m c) p) = flip_total c).
  rewrite IH; apply flip_total_cm2f.
Qed.

(** So does the number of slice edges in the slice. *)
Lemma slice_count_crun c p : slice_count (crun c p) = slice_count c.
Proof.
  revert c; induction p as [| m p IH]; intro c; [reflexivity |].
  change (slice_count (crun (cm2f m c) p) = slice_count c).
  rewrite IH; apply slice_count_cm2f.
Qed.

(** * What a physically valid cube must satisfy *)

(** Reading the cubies off a scramble is the same as scrambling the cubies. *)
Lemma to_cubies_scramble p : to_cubies (run init_state p) = crun csolved p.
Proof.
  replace (run init_state p) with (paint (crun csolved p))
    by (rewrite paint_crun, paint_csolved; reflexivity).
  apply to_cubies_paint.
Qed.

(** No reachable cube has a net corner rotation. A single corner twisted in
    place is therefore not a cube any scramble can produce. *)
Theorem twist_total_valid s : valid_state s -> twist_total (to_cubies s) = T0.
Proof.
  intros [p <-]; rewrite to_cubies_scramble, twist_total_crun; reflexivity.
Qed.

(** Nor a net edge flip, so a single flipped edge is likewise unreachable. *)
Theorem flip_total_valid s : valid_state s -> flip_total (to_cubies s) = F0.
Proof.
  intros [p <-]; rewrite to_cubies_scramble, flip_total_crun; reflexivity.
Qed.

(** And the four slice edges are always somewhere, so the slice coordinate
    ranges over choices of four slots out of twelve. *)
Theorem slice_count_valid s : valid_state s -> slice_count (to_cubies s) = 4.
Proof.
  intros [p <-]; rewrite to_cubies_scramble, slice_count_crun; reflexivity.
Qed.
