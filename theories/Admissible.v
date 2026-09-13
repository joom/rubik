From Stdlib Require Import Arith List Lia Permutation FMapPositive PArith.
Import ListNotations.

(** * Checked pruning tables

    A search is only as fast as its heuristic, and Kociemba's heuristics are
    distance tables built by breadth-first search. Proving a breadth-first
    search correct is a great deal of work for a table that, once built, can
    simply be checked.

    A heuristic is safe for iterative deepening when it never overestimates
    the distance to a goal. That follows from two local conditions: it reads
    zero at every goal, and it never drops by more than one across a single
    step. Both are decidable over a finite space, so the table can be built by
    any procedure at all and then verified. Nothing here needs to know how the
    table was produced. *)

Section Admissible.

(** A search space: the states, the steps between them, and the goals. *)
Variable A : Type.
Variable step : A -> list A.
Variable goal : A -> bool.

(** [reaches n x] says some path of [n] steps takes [x] to a goal. *)
Inductive reaches : nat -> A -> Prop :=
| reaches_goal x : goal x = true -> reaches 0 x
| reaches_step n x y : In y (step x) -> reaches n y -> reaches (S n) x.

(** A heuristic that never overestimates the distance to a goal, across the
    states the table was built for. *)
Definition admissible_on (dom : list A) (h : A -> nat) : Prop :=
  forall n x, In x dom -> reaches n x -> h x <= n.

(** The same two conditions as one decidable test over a finite space. *)
Definition consistentb (dom : list A) (h : A -> nat) : bool :=
  forallb (fun x =>
    andb (if goal x then Nat.eqb (h x) 0 else true)
         (forallb (fun y => Nat.leb (h x) (S (h y))) (step x))) dom.

(** Passing the test makes the heuristic safe, provided the listed states are
    closed under stepping, so that a path out of the list cannot escape it.
    Walk any path to a goal and the bound follows one step at a time. *)
Theorem consistentb_admissible (dom : list A) (h : A -> nat) :
  (forall x y, In x dom -> In y (step x) -> In y dom) ->
  consistentb dom h = true -> admissible_on dom h.
Proof.
  intros Hclosed Hchk; unfold consistentb in Hchk; rewrite forallb_forall in Hchk.
  intros n x Hin H; revert Hin.
  induction H as [x Hg | n x y Hstep Hr IH]; intro Hin.
  - pose proof (Hchk x Hin) as Hc; apply Bool.andb_true_iff in Hc as [Hz _].
    rewrite Hg in Hz; apply Nat.eqb_eq in Hz; lia.
  - pose proof (Hchk x Hin) as Hc; apply Bool.andb_true_iff in Hc as [_ Hs].
    rewrite forallb_forall in Hs.
    pose proof (Hs y Hstep) as Hle; apply Nat.leb_le in Hle.
    specialize (IH (Hclosed x y Hin Hstep)); lia.
Qed.

End Admissible.

Arguments reaches {A} step goal n x.
Arguments admissible_on {A} step goal dom h.
Arguments consistentb {A} step goal dom h.
Arguments consistentb_admissible {A} step goal dom h.

(** * Enumerating a coordinate space

    A coordinate is a fixed-length tuple over a small alphabet, so its whole
    space is the tuples of that length. *)

Fixpoint tuples {A : Type} (n : nat) (xs : list A) : list (list A) :=
  match n with
  | 0 => [[]]
  | S k => flat_map (fun a => map (cons a) (tuples k xs)) xs
  end.

(** Every tuple of the right length over an exhaustive alphabet is listed. *)
Lemma tuples_complete {A : Type} (xs : list A) :
  (forall x, In x xs) -> forall n l, length l = n -> In l (@tuples A n xs).
Proof.
  intros Hx n; induction n as [| n IH]; intros [| a l] Hl;
    simpl in Hl; try discriminate.
  - left; reflexivity.
  - apply in_flat_map; exists a; split; [apply Hx |].
    apply in_map, IH; injection Hl; auto.
Qed.

(** And nothing of the wrong length is. *)
Lemma tuples_length {A : Type} (xs : list A) n l :
  In l (@tuples A n xs) -> length l = n.
Proof.
  revert l; induction n as [| n IH]; intros l H; simpl in H.
  - destruct H as [<- | []]; reflexivity.
  - apply in_flat_map in H as [a [_ H]]; apply in_map_iff in H as [r [<- Hr]].
    simpl; f_equal; auto.
Qed.

(** * Enumerating a permutation space

    The second phase's coordinates say where pieces sit rather than how they
    are turned, so their spaces are the rearrangements of a fixed list rather
    than all tuples over an alphabet. *)

(** Every way of dropping one element into a list. *)
Fixpoint insert_all {A : Type} (a : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[a]]
  | x :: r => (a :: x :: r) :: map (cons x) (insert_all a r)
  end.

(** Every rearrangement of a list. *)
Fixpoint perms {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | a :: r => flat_map (insert_all a) (perms r)
  end.

(** Dropping an element in produces exactly the rearrangements that put it
    somewhere among the rest. *)
Lemma insert_all_split {A : Type} (a : A) l1 l2 :
  In (l1 ++ a :: l2) (insert_all a (l1 ++ l2)).
Proof.
  revert l2; induction l1 as [| x l1 IH]; intro l2; simpl.
  - destruct l2; simpl; auto.
  - right; apply in_map, IH.
Qed.

(** And it produces nothing else. *)
Lemma insert_all_sound {A : Type} (a : A) l l' :
  In l' (insert_all a l) -> Permutation (a :: l) l'.
Proof.
  revert l'; induction l as [| x r IH]; intros l' H; simpl in H.
  - destruct H as [<- | []]; apply Permutation_refl.
  - destruct H as [<- | H]; [apply Permutation_refl |].
    apply in_map_iff in H as [q [<- Hq]].
    apply perm_trans with (x :: a :: r); [apply perm_swap |].
    apply perm_skip, IH, Hq.
Qed.

(** The enumeration lists rearrangements and nothing else. *)
Lemma perms_sound {A : Type} (l l' : list A) : In l' (perms l) -> Permutation l l'.
Proof.
  revert l'; induction l as [| a r IH]; intros l' H; simpl in H.
  - destruct H as [<- | []]; apply Permutation_refl.
  - apply in_flat_map in H as [m [Hm Hi]].
    apply perm_trans with (a :: m); [apply perm_skip, IH, Hm |].
    apply insert_all_sound, Hi.
Qed.

(** And it lists every one of them. *)
Lemma perms_complete {A : Type} (l l' : list A) :
  Permutation l l' -> In l' (perms l).
Proof.
  revert l'; induction l as [| a r IH]; intros l' H; simpl.
  - apply Permutation_nil in H; subst; auto.
  - assert (Ha : In a l') by (apply (Permutation_in a H); simpl; auto).
    apply in_split in Ha as [l1 [l2 ->]].
    apply Permutation_cons_app_inv in H.
    apply in_flat_map; exists (l1 ++ l2); split; [apply IH, H | apply insert_all_split].
Qed.
