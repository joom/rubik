From Stdlib Require Import Arith List Lia Permutation Bool.
Import ListNotations.

(** * Parity of a rearrangement

    A cube's pieces are a rearrangement of the twenty slots, and one fact
    about rearrangements is not visible in any single piece: whether the
    number of swaps needed to undo it is odd or even. A quarter turn is a
    four-cycle on corners and a four-cycle on edges, both odd, so their sum is
    even and stays even. That is what rules out a cube with exactly two pieces
    exchanged, which is the last thing a solving method has to know.

    Parity is counted here as inversions: pairs listed out of order. *)

(** How many entries of a list are smaller than a given one. *)
Fixpoint below (x : nat) (l : list nat) : nat :=
  match l with [] => 0 | y :: r => (if y <? x then 1 else 0) + below x r end.

(** Pairs of a list that are out of order. *)
Fixpoint inversions (l : list nat) : nat :=
  match l with [] => 0 | x :: r => below x r + inversions r end.

(** Out-of-order pairs straddling two lists. *)
Fixpoint cross (a b : list nat) : nat :=
  match a with [] => 0 | x :: r => below x b + cross r b end.

(** Whether the number of inversions is odd. *)
Definition parity (l : list nat) : bool := Nat.odd (inversions l).

Lemma below_app x a b : below x (a ++ b) = below x a + below x b.
Proof. induction a as [| y a IH]; simpl; lia. Qed.

Lemma below_perm x a b : Permutation a b -> below x a = below x b.
Proof.
  intro H; induction H; simpl; lia.
Qed.

Lemma cross_app a b c : cross (a ++ b) c = cross a c + cross b c.
Proof. induction a as [| y a IH]; simpl; lia. Qed.

Lemma cross_perm_r a b b' : Permutation b b' -> cross a b = cross a b'.
Proof.
  intro H; induction a as [| x a IH]; simpl; [reflexivity |].
  rewrite (below_perm x b b' H), IH; reflexivity.
Qed.

Lemma inversions_app a b :
  inversions (a ++ b) = inversions a + cross a b + inversions b.
Proof.
  induction a as [| x a IH]; simpl; [lia |].
  rewrite below_app, IH; lia.
Qed.

(** Odd and even alternate across a single step. *)
Lemma odd_step n m : n = S m \/ m = S n -> Nat.odd n = negb (Nat.odd m).
Proof.
  intros [-> | ->]; rewrite Nat.odd_succ, <- Nat.negb_odd;
    [reflexivity | rewrite Bool.negb_involutive; reflexivity].
Qed.

(** Exchanging two neighbours changes exactly one pair, so it flips parity. *)
Lemma parity_adjacent a x y c :
  x <> y -> parity (a ++ x :: y :: c) = negb (parity (a ++ y :: x :: c)).
Proof.
  intro Hxy; unfold parity; rewrite !inversions_app.
  rewrite (cross_perm_r a (x :: y :: c) (y :: x :: c)) by apply perm_swap.
  cbn [inversions below].
  apply odd_step.
  destruct (Nat.ltb_spec y x) as [H1 | H1]; destruct (Nat.ltb_spec x y) as [H2 | H2];
    first [left; lia | right; lia].
Qed.

(** Exchanging any two distinct entries flips parity: slide one to the other
    with neighbour swaps, exchange, and slide back, which is an odd number of
    flips however far apart they sit. *)
Lemma parity_swap : forall b a x y c,
  x <> y -> ~ In x b -> ~ In y b ->
  parity (a ++ x :: b ++ y :: c) = negb (parity (a ++ y :: b ++ x :: c)).
Proof.
  induction b as [| z b IH]; intros a x y c Hxy Hx Hy; simpl.
  - apply parity_adjacent; auto.
  - assert (Hxz : x <> z) by (intro; subst; apply Hx; simpl; auto).
    assert (Hzy : z <> y) by (intro; subst; apply Hy; simpl; auto).
    assert (E1 : a ++ z :: x :: b ++ y :: c = (a ++ [z]) ++ x :: b ++ y :: c)
      by (rewrite <- app_assoc; reflexivity).
    assert (E2 : a ++ z :: y :: b ++ x :: c = (a ++ [z]) ++ y :: b ++ x :: c)
      by (rewrite <- app_assoc; reflexivity).
    rewrite (parity_adjacent a x z (b ++ y :: c) Hxz).
    rewrite <- (parity_adjacent a z y (b ++ x :: c) Hzy).
    rewrite E1, E2, (IH (a ++ [z]) x y c Hxy
                       (fun H => Hx (or_intror H)) (fun H => Hy (or_intror H))).
    rewrite Bool.negb_involutive; reflexivity.
Qed.

(** The distinctness a swap needs is exactly what a duplicate-free list says. *)
Lemma nodup_split (a : list nat) (x : nat) (b : list nat) (y : nat) (c : list nat) :
  NoDup (a ++ x :: b ++ y :: c) -> x <> y /\ ~ In x b /\ ~ In y b.
Proof.
  intro H; split; [| split].
  - apply NoDup_remove_2 in H; intro; subst; apply H, in_or_app; right;
      apply in_or_app; right; simpl; auto.
  - apply NoDup_remove_2 in H; intro; apply H, in_or_app; right;
      apply in_or_app; left; auto.
  - rewrite app_comm_cons, app_assoc in H; apply NoDup_remove_2 in H;
      intro; apply H, in_or_app; left; apply in_or_app; right; simpl; auto.
Qed.

(** Exchanging two entries of a duplicate-free list flips its parity. *)
Lemma parity_exchange (a : list nat) (x : nat) (b : list nat) (y : nat) (c : list nat) :
  NoDup (a ++ x :: b ++ y :: c) ->
  parity (a ++ x :: b ++ y :: c) = negb (parity (a ++ y :: b ++ x :: c)).
Proof.
  intro H; destruct (nodup_split a x b y c H) as [H1 [H2 H3]];
    apply parity_swap; auto.
Qed.

(** Exchanging keeps a list duplicate-free, so a chain of exchanges can carry
    the hypothesis along rather than rediscovering it at every step. *)
Lemma nodup_exchange (a : list nat) (x : nat) (b : list nat) (y : nat) (c : list nat) :
  NoDup (a ++ x :: b ++ y :: c) -> NoDup (a ++ y :: b ++ x :: c).
Proof.
  intro H; eapply Permutation_NoDup; [| exact H].
  apply Permutation_app_head.
  apply perm_trans with (y :: x :: (b ++ c)).
  - apply perm_trans with (x :: y :: (b ++ c)).
    + apply perm_skip, Permutation_sym, Permutation_middle.
    + apply perm_swap.
  - apply perm_skip, Permutation_middle.
Qed.
