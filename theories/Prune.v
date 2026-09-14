From Stdlib Require Import Arith List Lia.
From Rubik Require Import BasicRubik.
Import ListNotations.

(** * Pruning the move space

    Two restrictions cut the branching without losing anything a solution
    needs: turning the same face twice running is the same as turning it once
    or not at all, and turns of opposite faces commute, so only one of their
    two orders is worth trying. *)

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
Lemma allowed_moves_filter prev : allowed_moves prev = filter (allowed prev) all_moves.
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
Lemma choose_move_sound rec l p :
  choose_move rec l = Some p ->
  exists m q, In m l /\ rec m = Some q /\ p = m :: q.
Proof.
  induction l as [| m l IH]; simpl; [discriminate |].
  destruct (rec m) as [q |] eqn:R.
  - intro H; inversion H; exists m, q; auto.
  - intro H; destruct (IH H) as [m' [q' [Hin [Hr He]]]]; exists m', q'; auto.
Qed.

(** If some move in the list succeeds, the choice returns something. *)
Lemma choose_move_complete rec l m p :
  In m l -> rec m = Some p -> exists r, choose_move rec l = Some r.
Proof.
  induction l as [| m' l IH]; simpl; [contradiction |].
  intros [<- | Hin] Hr.
  - rewrite Hr; eexists; reflexivity.
  - destruct (rec m') as [q |]; [eexists; reflexivity | apply IH; auto].
Qed.

(** * Why the pruning loses nothing

    The search only ever tries moves [allowed_moves] keeps, so a completeness
    argument has to know that nothing is lost by that. Every sequence can be
    rewritten into one the pruning keeps, without getting longer and without
    changing where it lands: two turns of one face collapse into at most one,
    and turns of opposite faces can be swapped into the chosen order. *)

(** A path the pruning keeps: every move is allowed after the one before it. *)
Fixpoint canonical (prev : option move) (p : list move) : Prop :=
  match p with
  | [] => True
  | m :: q => allowed prev m = true /\ canonical (Some m) q
  end.

(** A boolean view of the same thing, so the rewriting can branch on it. *)
Fixpoint canonicalb (prev : option move) (p : list move) : bool :=
  match p with
  | [] => true
  | m :: q => allowed prev m && canonicalb (Some m) q
  end.

Lemma canonicalb_spec prev p : canonicalb prev p = true <-> canonical prev p.
Proof.
  revert prev; induction p as [| m q IH]; intro prev; simpl; [tauto |].
  rewrite Bool.andb_true_iff, IH; tauto.
Qed.

(** A path the pruning rejects has an adjacent pair it rejects. *)
Lemma not_canonical_split prev p : ~ canonical prev p ->
  (exists m b, p = m :: b /\ allowed prev m = false) \/
  (exists a m1 m2 b, p = a ++ m1 :: m2 :: b /\ allowed (Some m1) m2 = false).
Proof.
  revert prev; induction p as [| m q IH]; intros prev H; [contradiction H; exact I |].
  destruct (allowed prev m) eqn:A.
  - assert (Hq : ~ canonical (Some m) q) by (intro C; apply H; split; auto).
    destruct (IH _ Hq) as [[m2 [b [Eq A2]]] | [a [m1 [m2 [b [Eq A2]]]]]].
    + right; exists [], m, m2, b; subst q; auto.
    + right; exists (m :: a), m1, m2, b; subst q; auto.
  - left; exists m, q; auto.
Qed.

(** Ranks weighted by position. Swapping an out-of-order pair of opposite
    faces lowers this, which is what makes the rewriting terminate. *)
Fixpoint weight_from (i : nat) (p : list move) : nat :=
  match p with
  | [] => 0
  | m :: q => i * face_rank (fst m) + weight_from (S i) q
  end.

Definition weight (p : list move) : nat := weight_from 0 p.

Lemma weight_from_app i a c :
  weight_from i (a ++ c) = weight_from i a + weight_from (i + length a) c.
Proof.
  revert i; induction a as [| m a IH]; intro i; simpl.
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IH; replace (S i + length a) with (i + S (length a)) by lia; lia.
Qed.

Section Normalise.

(** The rewriting is about move sequences, so it is stated once for any set a
    move acts on: the stickers, the cubies, or a coordinate. *)
Variable A : Type.
Variable act : move -> A -> A.

(** The moves a caller is willing to use. The first phase allows all of them;
    the second allows ten, and the rewriting has to stay inside that ten. *)
Variable ok : move -> bool.

(** Running a sequence left to right. *)
Definition act_run (a : A) (p : list move) : A := fold_left (fun a m => act m a) p a.

(** Two turns of one face are one turn of that face, or nothing at all. *)
Hypothesis merge : forall f t1 t2,
  ok (f, t1) = true -> ok (f, t2) = true ->
  (forall a, act (f, t2) (act (f, t1) a) = a) \/
  (exists t3, ok (f, t3) = true /\
     forall a, act (f, t2) (act (f, t1) a) = act (f, t3) a).

(** Turns of opposite faces commute. *)
Hypothesis comm : forall f g t1 t2, opposite f g = true ->
  forall a, act (f, t1) (act (g, t2) a) = act (g, t2) (act (f, t1) a).

Lemma act_run_app a p q : act_run a (p ++ q) = act_run (act_run a p) q.
Proof. unfold act_run; apply fold_left_app. Qed.

(** Replacing one adjacent pair by anything with the same effect leaves the
    endpoint alone. *)
Lemma act_run_replace x m1 m2 c b :
  (forall a, act_run a c = act m2 (act m1 a)) ->
  forall a, act_run a (x ++ c ++ b) = act_run a (x ++ m1 :: m2 :: b).
Proof.
  intros H a; rewrite !act_run_app, H.
  change (m1 :: m2 :: b) with ([m1; m2] ++ b); rewrite act_run_app; reflexivity.
Qed.

(** Every sequence has a canonical one that is no longer, lands in the same
    place, and uses only moves the caller allows. *)
Lemma normalise : forall n k p, length p <= n -> weight p < k ->
  Forall (fun m => ok m = true) p ->
  exists q, canonical None q /\ Forall (fun m => ok m = true) q /\
    (forall a, act_run a q = act_run a p) /\ length q <= length p.
Proof.
  induction n as [| n IHn]; intros k p Hl Hw Hok.
  - exists []; destruct p; simpl in Hl; [| lia]; repeat split; auto.
  - revert p Hl Hw Hok; induction k as [| k IHk]; intros p Hl Hw Hok; [lia |].
    destruct (canonicalb None p) eqn:C.
    + exists p; repeat split; auto; apply canonicalb_spec; auto.
    + assert (NC : ~ canonical None p)
        by (intro X; apply canonicalb_spec in X; congruence).
      destruct (not_canonical_split _ _ NC)
        as [[m [b [Eq Ab]]] | [x [m1 [m2 [b [Eq Ab]]]]]];
        [subst p; simpl in Ab; discriminate |].
      subst p; destruct m1 as [f1 t1]; destruct m2 as [f2 t2];
        cbn [allowed fst] in Ab.
      assert (Hx : Forall (fun m => ok m = true) x /\ ok (f1, t1) = true /\
                   ok (f2, t2) = true /\ Forall (fun m => ok m = true) b).
      { apply Forall_app in Hok as [H1 H2]; inversion H2; subst;
          match goal with H : Forall _ (_ :: b) |- _ => inversion H; subst end;
          repeat split; auto. }
      destruct Hx as [Hxo [H1o [H2o Hbo]]].
      apply Bool.andb_false_iff in Ab; destruct Ab as [Ab | Ab].
      * apply Bool.negb_false_iff, Nat.eqb_eq, face_rank_inj in Ab; subst f2.
        destruct (merge f1 t1 t2 H1o H2o) as [Hm | [t3 [Ht3 Hm]]].
        -- destruct (IHn (S (weight (x ++ b))) (x ++ b))
             as [q [Hc [Hqo [Hq Hlq]]]].
           ++ rewrite !length_app in *; simpl in *; lia.
           ++ lia.
           ++ apply Forall_app; auto.
           ++ exists q; repeat split; auto.
              ** intro a; rewrite Hq.
                 apply (act_run_replace x (f1, t1) (f1, t2) [] b);
                   intro; unfold act_run; simpl; symmetry; apply Hm.
              ** rewrite !length_app in *; simpl in *; lia.
        -- destruct (IHn (S (weight (x ++ (f1, t3) :: b))) (x ++ (f1, t3) :: b))
             as [q [Hc [Hqo [Hq Hlq]]]].
           ++ rewrite !length_app in *; simpl in *; lia.
           ++ lia.
           ++ apply Forall_app; split; auto.
           ++ exists q; repeat split; auto.
              ** intro a; rewrite Hq.
                 apply (act_run_replace x (f1, t1) (f1, t2) [(f1, t3)] b);
                   intro; unfold act_run; simpl; symmetry; apply Hm.
              ** rewrite !length_app in *; simpl in *; lia.
      * apply Bool.negb_false_iff, Bool.andb_true_iff in Ab.
        destruct Ab as [Aop Alt]; apply Nat.ltb_lt in Alt.
        destruct (IHk (x ++ (f2, t2) :: (f1, t1) :: b)) as [q [Hc [Hqo [Hq Hlq]]]].
        -- rewrite !length_app in *; simpl in *; lia.
        -- unfold weight in *; rewrite !weight_from_app in *;
             cbn [weight_from fst] in *; rewrite !Nat.mul_succ_l in *; lia.
        -- apply Forall_app; split; auto.
        -- exists q; repeat split; auto.
           ++ intro a; rewrite Hq.
              apply (act_run_replace x (f1, t1) (f2, t2) [(f2, t2); (f1, t1)] b).
              intro; unfold act_run; simpl; apply comm; rewrite opposite_sym; exact Aop.
           ++ rewrite !length_app in *; simpl in *; lia.
Qed.

(** Every sequence is matched by a canonical one that is no longer. *)
Corollary canonical_exists p : Forall (fun m => ok m = true) p ->
  exists q, canonical None q /\ Forall (fun m => ok m = true) q /\
    (forall a, act_run a q = act_run a p) /\ length q <= length p.
Proof. intro H; apply (normalise (length p) (S (weight p))); auto. Qed.

End Normalise.
