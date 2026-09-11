From Stdlib Require Import Arith List Lia.
From Rubik Require Import BasicRubik.

(** * Admissible sticker bounds

    Turning a face permutes its own stickers without changing how many match
    that face. On adjacent faces it changes four edge stickers and eight
    corner stickers. These give independent lower bounds on moves remaining. *)

(** A sticker contributes one when it does not match its destination face. *)
Definition misplaced (f c : face) : nat := if face_eq_dec f c then 0 else 1.

(** Each sticker contributes at most one to the bound. *)
Lemma misplaced_bound f c : misplaced f c <= 1.
Proof. unfold misplaced; destruct (face_eq_dec f c); lia. Qed.

(** Count the four edge stickers on a face. *)
Definition edge_count (f : face) (g : grid) : nat :=
  let '(Triple (Triple _ a _) (Triple b _ c) (Triple _ d _)) := g in
  misplaced f a + misplaced f b + misplaced f c + misplaced f d.

(** Count the four corner stickers on a face. *)
Definition corner_count (f : face) (g : grid) : nat :=
  let '(Triple (Triple a _ b) _ (Triple c _ d)) := g in
  misplaced f a + misplaced f b + misplaced f c + misplaced f d.

(** Sum a face statistic over all six faces. *)
Definition total_count (count : face -> grid -> nat) (s : state) : nat :=
  let '(Triple u r f, Triple d l b) := s in
  count Up u + count Right r + count Front f +
  count Down d + count Left l + count Back b.

(** One move repairs at most four edge stickers. *)
Lemma edge_count_move m s :
  total_count edge_count s <= 4 + total_count edge_count (m2f m s).
Proof.
  destruct m as [f t]; destruct f, t; destruct_state s;
    cbn [m2f quarter total_count edge_count];
    repeat match goal with
    | |- context [misplaced ?f ?c] =>
        let x := fresh "x" in
        let H := fresh "H" in
        pose proof (misplaced_bound f c) as H;
        set (x := misplaced f c) in *
    end; lia.
Qed.

(** One move repairs at most eight corner stickers. *)
Lemma corner_count_move m s :
  total_count corner_count s <= 8 + total_count corner_count (m2f m s).
Proof.
  destruct m as [f t]; destruct f, t; destruct_state s;
    cbn [m2f quarter total_count corner_count];
    repeat match goal with
    | |- context [misplaced ?f ?c] =>
        let x := fresh "x" in
        let H := fresh "H" in
        pose proof (misplaced_bound f c) as H;
        set (x := misplaced f c) in *
    end; lia.
Qed.

(** Any solution must budget enough moves to repair every edge sticker. *)
Lemma edge_count_solution s p : run s p = init_state ->
  total_count edge_count s <= 4 * length p.
Proof.
  revert s; induction p as [| m p IH]; intros s H.
  - change (s = init_state) in H; subst; vm_compute; auto.
  - specialize (IH (m2f m s) H).
    pose proof (edge_count_move m s); simpl length; lia.
Qed.

(** Any solution must also repair every corner sticker. *)
Lemma corner_count_solution s p : run s p = init_state ->
  total_count corner_count s <= 8 * length p.
Proof.
  revert s; induction p as [| m p IH]; intros s H.
  - change (s = init_state) in H; subst; vm_compute; auto.
  - specialize (IH (m2f m s) H).
    pose proof (corner_count_move m s); simpl length; lia.
Qed.

(** Reject a subtree only when its remaining moves cannot repair its stickers. *)
Definition feasible (d : nat) (s : state) : bool :=
  (total_count edge_count s <=? 4 * d) &&
  (total_count corner_count s <=? 8 * d).

(** This pruning test never rejects a solution that fits the remaining depth. *)
Theorem feasible_solution d s p : run s p = init_state -> length p <= d ->
  feasible d s = true.
Proof.
  intros H L; unfold feasible; apply Bool.andb_true_iff; split;
    apply Nat.leb_le.
  - pose proof (edge_count_solution s p H); lia.
  - pose proof (corner_count_solution s p H); lia.
Qed.
