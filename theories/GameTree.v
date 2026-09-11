From Stdlib Require Import Arith List Lia.
From GameTrees Require Import Cotrees.
From Rubik Require Import BasicRubik Heuristic.
Import ListNotations.

(** * The cube as a coinductive game tree

    A cube has no finite game to play out, so its tree is coinductive: it is
    unfolded lazily and only ever explored to a depth. This file builds the tree, prunes it, and proves the depth-limited
    search sound and complete for canonical paths. *)

(** * Nodes

    A node carries the move that produced this cube together with the cube
    itself. Keeping the move in the node is what lets the successor function
    prune without being handed a history. *)
Definition node : Type := (option move * state)%type.

(** The cube at a node. *)
Definition node_state (n : node) : state := snd n.

(** The move that produced a node, absent only at the root. *)
Definition node_move (n : node) : option move := fst n.

(** * Pruning

    Two restrictions cut the tree without losing any shortest solution. They
    are justified by the normalisation theorem below. *)

(** Faces in the model's U/R/F/D/L/B order, so that opposite faces differ by
    three and a total order on faces is available. *)
Definition face_rank (f : face) : nat :=
  match f with
  | Up => 0 | Right => 1 | Front => 2 | Down => 3 | Left => 4 | Back => 5
  end.

(** Ranks determine a face, so comparing them compares faces. *)
Lemma face_rank_inj f g : face_rank f = face_rank g -> f = g.
Proof. destruct f, g; simpl; congruence. Qed.

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

(** The moves still worth trying after a given move. *)
Definition allowed_moves (prev : option move) : list move :=
  filter (allowed prev) Movel.

(** Every allowed move is a legal move. *)
Lemma allowed_moves_sound prev m : In m (allowed_moves prev) -> In m Movel.
Proof.
  unfold allowed_moves; intro H; apply filter_In in H; tauto.
Qed.

(** An allowed move is exactly a legal move that passes the pruning test. *)
Lemma allowed_moves_iff prev m :
  In m (allowed_moves prev) <-> allowed prev m = true.
Proof.
  unfold allowed_moves; rewrite filter_In; split; [tauto |].
  intro H; split; [apply moves_complete | exact H].
Qed.

(** There are eighteen moves, so no node has more children than that. *)
Lemma allowed_moves_bound prev : length (allowed_moves prev) <= 18.
Proof.
  unfold allowed_moves; etransitivity; [apply filter_length_le | reflexivity].
Qed.

(** * The tree *)

(** The children of a node: one per move the pruning still permits. *)
Definition steps (n : node) : list node :=
  map (fun m => (Some m, m2f m (node_state n))) (allowed_moves (node_move n)).

(** The successor function the tree is unfolded with. *)
Definition next (n : node) : colist node := colist_of_list (steps n).

(** The pruned game tree of a cube, unfolded lazily and without end. *)
Definition cube_tree (s : state) : cotree node := unfold_cotree next (None, s).

(** * Searching the tree

    The search takes the first child that leads to a solved cube. Children are
    forced one at a time, so a branch the search never reaches is never built:
    this is what makes an endless tree usable. *)

(** Try the children of a node in order. The fuel bounds the colist walk, and
    eighteen always suffices because no node has more children than there are
    moves. *)
Fixpoint choose_child (rec : cotree node -> option (list move)) (fuel : nat)
    (l : colist (cotree node)) : option (list move) :=
  match fuel with
  | 0 => None
  | S k =>
      match l with
      | conil => None
      | cocons c cs =>
          match node_move (root c), rec c with
          | Some m, Some p => Some (m :: p)
          | _, _ => choose_child rec k cs
          end
      end
  end.

(** Walk the tree to a depth, returning the moves down to the first solved cube. *)
Fixpoint walk (d : nat) (t : cotree node) : option (list move) :=
  if state_eq_dec (node_state (root t)) init_state then Some []
  else
    match d with
    | 0 => None
    | S d' =>
        if feasible d (node_state (root t)) then
          match t with
          | conode _ cs => choose_child (walk d') 18 cs
          end
        else None
    end.

(** * A plain mirror

    [walk] is the program that runs, but reasoning about a cofixpoint through
    its unfolding equations is awkward. This ordinary recursion computes the
    same answers, and every proof about the search goes through it. *)

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

(** The same pruned depth-limited search, written without a tree. *)
Fixpoint plain (d : nat) (prev : option move) (s : state) : option (list move) :=
  if state_eq_dec s init_state then Some []
  else
    match d with
    | 0 => None
    | S d' =>
        if feasible d s then
          choose_move (fun m => plain d' (Some m) (m2f m s)) (allowed_moves prev)
        else None
    end.

(** Walking the children of an unfolded node agrees with trying its moves. *)
Lemma choose_child_unfold (rec : cotree node -> option (list move))
    (recp : move -> option (list move)) (s : state) (l : list move) (fuel : nat) :
  length l <= fuel ->
  (forall m, rec (unfold_cotree next (Some m, m2f m s)) = recp m) ->
  choose_child rec fuel
    (comap (unfold_cotree next) (colist_of_list (map (fun m => (Some m, m2f m s)) l)))
  = choose_move recp l.
Proof.
  revert fuel; induction l as [| m l IH]; intros fuel Hlen Hrec.
  - destruct fuel; reflexivity.
  - destruct fuel as [| fuel]; simpl in Hlen; [lia |].
    cbn [map choose_child colist_of_list comap root node_move fst].
    rewrite Hrec; cbn [choose_move].
    destruct (recp m) as [p |]; [reflexivity |].
    apply IH; [lia | exact Hrec].
Qed.

(** The tree search and the plain recursion return the same answer. *)
Theorem walk_plain d prev s : walk d (unfold_cotree next (prev, s)) = plain d prev s.
Proof.
  revert prev s; induction d as [| d IH]; intros prev s;
    rewrite (cotree_decompose_eq (unfold_cotree next (prev, s)));
    cbn [cotree_decompose unfold_cotree walk plain root node_state snd];
    destruct (state_eq_dec s init_state) as [E | E]; auto.
  all: destruct (feasible _ s); auto.
  unfold next, steps; cbn [node_state node_move fst snd].
  apply choose_child_unfold; [apply allowed_moves_bound | intro m; apply IH].
Qed.

(** Searching a cube's pruned tree to a depth. *)
Definition tree_search (d : nat) (s : state) : option (list move) :=
  walk d (cube_tree s).

(** The tree search is the plain recursion, started with no previous move. *)
Corollary tree_search_plain d s : tree_search d s = plain d None s.
Proof. apply walk_plain. Qed.

(** * Why the pruning loses nothing

    Both restrictions rewrite a solution into one the pruned tree contains,
    without ever making it longer. Turning a face twice running collapses into
    at most one turn, and opposite faces commute, so their order is free. *)

(** A path the pruned tree contains: every move is allowed after the last. *)
Fixpoint canonical (prev : option move) (p : list move) : Prop :=
  match p with
  | [] => True
  | m :: q => allowed prev m = true /\ canonical (Some m) q
  end.

(** Two turns of one face are a single turn of that face, or nothing at all. *)
Lemma same_face_merge (f : face) (t1 t2 : turns) :
  (forall s, m2f (f, t2) (m2f (f, t1) s) = s) \/
  (exists t3, forall s, m2f (f, t2) (m2f (f, t1) s) = m2f (f, t3) s).
Proof.
  destruct t1, t2;
    [ right; exists Half | right; exists CCW | left
    | right; exists CCW | left | right; exists CW
    | left | right; exists CW | right; exists Half ];
    intro s; unfold_moves; rewrite ?quarter_four; reflexivity.
Qed.

(** Quarter turns of opposite faces move disjoint cubies, so they commute. *)
Lemma quarter_comm f g s :
  opposite f g = true -> quarter f (quarter g s) = quarter g (quarter f s).
Proof.
  destruct f, g; simpl opposite; try discriminate; intros _;
    destruct_state s; reflexivity.
Qed.

(** Turns of opposite faces commute, whatever their amounts. *)
Lemma move_comm f g t1 t2 s :
  opposite f g = true ->
  m2f (f, t1) (m2f (g, t2) s) = m2f (g, t2) (m2f (f, t1) s).
Proof.
  intro H; destruct t1, t2; unfold_moves;
    repeat rewrite (quarter_comm f g _ H); reflexivity.
Qed.

(** A path that is not canonical has an adjacent pair the pruning rejects. *)
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

(** A boolean view of canonicity, so the normalisation below can branch on it. *)
Fixpoint canonicalb (prev : option move) (p : list move) : bool :=
  match p with
  | [] => true
  | m :: q => allowed prev m && canonicalb (Some m) q
  end.

(** The boolean and the propositional views agree. *)
Lemma canonicalb_spec prev p : canonicalb prev p = true <-> canonical prev p.
Proof.
  revert prev; induction p as [| m q IH]; intro prev; simpl; [tauto |].
  rewrite Bool.andb_true_iff, IH; tauto.
Qed.

(** Being opposite does not depend on which face is named first. *)
Lemma opposite_sym f g : opposite f g = opposite g f.
Proof. unfold opposite; apply Bool.orb_comm. Qed.

(** Ranks weighted by position. Swapping an out-of-order pair of opposite
    faces always lowers this, which is what makes the reordering terminate. *)
Fixpoint weight_from (i : nat) (p : list move) : nat :=
  match p with
  | [] => 0
  | m :: q => i * face_rank (fst m) + weight_from (S i) q
  end.

Definition weight (p : list move) : nat := weight_from 0 p.

(** Weight splits along a concatenation, with the tail shifted by the prefix. *)
Lemma weight_from_app i a c :
  weight_from i (a ++ c) = weight_from i a + weight_from (i + length a) c.
Proof.
  revert i; induction a as [| m a IH]; intro i; simpl.
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IH; replace (S i + length a) with (i + S (length a)) by lia; lia.
Qed.

(** Running two moves is applying them in turn. *)
Lemma run_pair s m1 m2 : run s [m1; m2] = m2f m2 (m2f m1 s).
Proof. reflexivity. Qed.

(** Rewriting one adjacent pair inside a path. *)
Lemma run_middle s a c b :
  run s (a ++ c ++ b) = run (run (run s a) c) b.
Proof. rewrite !run_app; reflexivity. Qed.

(** Replacing one adjacent pair by anything that has the same effect leaves the
    cube the path arrives at unchanged. *)
Lemma run_replace_pair s a m1 m2 c b :
  run (run s a) c = m2f m2 (m2f m1 (run s a)) ->
  run s (a ++ c ++ b) = run s (a ++ m1 :: m2 :: b).
Proof.
  intro H; rewrite run_middle.
  change (m1 :: m2 :: b) with ([m1; m2] ++ b).
  rewrite run_middle, run_pair, H; reflexivity.
Qed.

(** Every solution can be rewritten into one the pruned tree contains, without
    ever getting longer. The rewriting either shortens the path, by collapsing
    two turns of one face, or reorders a pair of opposite faces, which leaves
    the length alone but lowers the weight; so it cannot go on forever. *)
Lemma normalise : forall n k s p,
  length p <= n -> weight p < k -> run s p = init_state ->
  exists q, canonical None q /\ run s q = init_state /\ length q <= length p.
Proof.
  induction n as [| n IHn]; intros k s p Hl Hw Hr.
  - exists []; destruct p; simpl in Hl; [| lia]; repeat split; auto.
  - revert s p Hl Hw Hr; induction k as [| k IHk]; intros s p Hl Hw Hr; [lia |].
    destruct (canonicalb None p) eqn:C.
    + exists p; repeat split; auto; apply canonicalb_spec; auto.
    + assert (NC : ~ canonical None p)
        by (intro X; apply canonicalb_spec in X; congruence).
      destruct (not_canonical_split _ _ NC)
        as [[m [b [Eq A]]] | [a [m1 [m2 [b [Eq A]]]]]];
        [subst p; simpl in A; discriminate |].
      subst p; destruct m1 as [f1 t1]; destruct m2 as [f2 t2];
        cbn [allowed fst] in A.
      apply Bool.andb_false_iff in A; destruct A as [A | A].
      * apply Bool.negb_false_iff, Nat.eqb_eq, face_rank_inj in A; subst f2.
        destruct (same_face_merge f1 t1 t2) as [Hm | [t3 Hm]].
        -- destruct (IHn (S (weight (a ++ b))) s (a ++ b)) as [q [Hc [Hq Hlq]]].
           ++ rewrite !length_app in *; simpl in *; lia.
           ++ lia.
           ++ transitivity (run s (a ++ (f1, t1) :: (f1, t2) :: b)); [| exact Hr].
              apply (run_replace_pair s a (f1, t1) (f1, t2) [] b);
                simpl; symmetry; apply Hm.
           ++ exists q; repeat split; auto; rewrite !length_app in *; simpl in *; lia.
        -- destruct (IHn (S (weight (a ++ (f1, t3) :: b))) s (a ++ (f1, t3) :: b))
             as [q [Hc [Hq Hlq]]].
           ++ rewrite !length_app in *; simpl in *; lia.
           ++ lia.
           ++ transitivity (run s (a ++ (f1, t1) :: (f1, t2) :: b)); [| exact Hr].
              apply (run_replace_pair s a (f1, t1) (f1, t2) [(f1, t3)] b);
                simpl; symmetry; apply Hm.
           ++ exists q; repeat split; auto; rewrite !length_app in *; simpl in *; lia.
      * apply Bool.negb_false_iff, Bool.andb_true_iff in A.
        destruct A as [Aop Alt]; apply Nat.ltb_lt in Alt.
        destruct (IHk s (a ++ (f2, t2) :: (f1, t1) :: b)) as [q [Hc [Hq Hlq]]].
        -- rewrite !length_app in *; simpl in *; lia.
        -- unfold weight in *; rewrite !weight_from_app in *;
             cbn [weight_from fst] in *; rewrite !Nat.mul_succ_l in *; lia.
        -- transitivity (run s (a ++ (f1, t1) :: (f2, t2) :: b)); [| exact Hr].
           apply (run_replace_pair s a (f1, t1) (f2, t2) [(f2, t2); (f1, t1)] b).
           cbn [run fold_left]; apply move_comm; rewrite opposite_sym; exact Aop.
        -- exists q; repeat split; auto; rewrite !length_app in *; simpl in *; lia.
Qed.

(** Every solution is matched by a canonical one that is no longer. *)
Corollary canonical_exists s p : run s p = init_state ->
  exists q, canonical None q /\ run s q = init_state /\ length q <= length p.
Proof. intro H; apply (normalise (length p) (S (weight p)) s p); auto. Qed.

(** * What the search finds *)

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

(** If nothing was chosen, nothing in the list succeeded. *)
Lemma choose_move_none rec l m :
  choose_move rec l = None -> In m l -> rec m = None.
Proof.
  induction l as [| m' l IH]; simpl; [contradiction |].
  destruct (rec m') as [q |] eqn:R; [discriminate |].
  intros H [<- | Hin]; auto.
Qed.

(** Anything the search returns really solves the cube, within the depth. *)
Lemma plain_sound d prev s p :
  plain d prev s = Some p -> run s p = init_state /\ length p <= d.
Proof.
  revert prev s p; induction d as [| d IH]; intros prev s p; cbn [plain];
    destruct (state_eq_dec s init_state) as [E | E].
  - intro H; inversion H; subst; simpl; auto.
  - discriminate.
  - intro H; inversion H; subst; simpl; auto with arith.
  - destruct (feasible (S d) s); [| discriminate].
    intro H; destruct (choose_move_some _ _ _ H) as [m [q [Hin [Hr ->]]]].
    destruct (IH _ _ _ Hr) as [Hrun Hlen]; simpl; split; [| lia].
    rewrite <- Hrun; reflexivity.
Qed.

(** A canonical solution within the depth is always found. *)
Lemma plain_complete d prev s p :
  canonical prev p -> run s p = init_state -> length p <= d -> plain d prev s <> None.
Proof.
  revert prev s p; induction d as [| d IH]; intros prev s p Hc Hr Hlen;
    cbn [plain]; destruct (state_eq_dec s init_state) as [E | E]; try discriminate.
  all: try rewrite (feasible_solution _ _ _ Hr Hlen).
  - destruct p as [| m q]; cbn [run fold_left length] in *; [contradiction | lia].
  - destruct p as [| m q]; cbn [run fold_left length] in *; [contradiction |].
    destruct Hc as [Ha Hc]; intro H.
    assert (Hin : In m (allowed_moves prev)) by (apply allowed_moves_iff; exact Ha).
    apply (IH (Some m) (m2f m s) q Hc Hr); [lia |].
    exact (choose_move_none _ _ m H Hin).
Qed.
