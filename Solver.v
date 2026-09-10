From Stdlib Require Import Arith Lia List.
From minirubik Require Export BasicRubik.
Import ListNotations.

(** * Depth-limited search *)

(** Try candidates in order and return the first successful result. *)
Fixpoint choose {A B} (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: xs =>
      match f x with
      | Some y => Some y
      | None => choose f xs
      end
  end.

(** A successful choice comes from a candidate actually present in the list. *)
Lemma choose_some {A B} (f : A -> option B) xs y :
  choose f xs = Some y -> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [| x xs IH]; simpl; [discriminate |].
  destruct (f x) eqn:E.
  - intro H; inversion H; subst; exists x; auto.
  - intro H; destruct (IH H) as [z [Hz Ez]]; exists z; auto.
Qed.

(** Choice fails exactly when every available candidate fails. *)
Lemma choose_none {A B} (f : A -> option B) xs :
  choose f xs = None <-> forall x, In x xs -> f x = None.
Proof.
  induction xs as [| x xs IH]; simpl; [tauto |].
  destruct (f x) eqn:E; split; try discriminate.
  - intro H; specialize (H x (or_introl eq_refl)); congruence.
  - intros H z [<- | Hz]; auto; apply IH; auto.
  - intro H; apply IH; intros; apply H; auto.
Qed.

(** Try all move sequences within a depth limit, stopping at the first solution. *)
Fixpoint search (depth : nat) (s : state) : option (list move) :=
  if state_eq_dec s init_state then Some []
  else
    match depth with
    | 0 => None
    | S n => choose (fun m => option_map (cons m) (search n (m2f m s))) Movel
    end.

(** A successful depth-limited search solves the cube within its allowance. *)
Lemma search_sound n s p : search n s = Some p ->
  run s p = init_state /\ length p <= n.
Proof.
  revert s p; induction n as [| n IH]; intros s p; cbn [search];
    destruct (state_eq_dec s init_state) as [E | E].
  - intro H; inversion H; subst; simpl; auto.
  - discriminate.
  - intro H; inversion H; subst; simpl; auto with arith.
  - intro H; apply choose_some in H; destruct H as [m [_ H]].
    destruct (search n (m2f m s)) as [q |] eqn:Q; simpl in H; try discriminate.
    inversion H; subst; specialize (IH _ _ Q); simpl; intuition lia.
Qed.

(** A solution within the depth limit prevents search from failing. *)
Lemma search_complete n s p :
  run s p = init_state -> length p <= n -> search n s <> None.
Proof.
  revert s p; induction n as [| n IH]; intros s p Hp Hlen;
    cbn [search]; destruct (state_eq_dec s init_state) as [E | E]; try discriminate.
  - destruct p; cbn [run fold_left length] in *; [contradiction | lia].
  - destruct p as [| m p]; cbn [run fold_left length] in *; [contradiction |].
    intro H; rewrite choose_none in H; specialize (H m (moves_complete m)).
    destruct (search n (m2f m s)) eqn:Q; simpl in H; try discriminate.
    eapply IH; eauto; lia.
Qed.

(** * Shortest paths and finiteness *)

(** A shortest solution uses no more moves than any other solving sequence. *)
Definition shortest (s : state) (p : list move) : Prop :=
  run s p = init_state /\
  forall q, run s q = init_state -> length p <= length q.

(** If any solution fits a finite limit, a shortest one fits that limit too. *)
Lemma shortest_exists n s :
  (exists p, run s p = init_state /\ length p <= n) ->
  exists p, shortest s p /\ length p <= n.
Proof.
  induction n as [| n IH]; intros [p [Hp Hlen]].
  - exists p; unfold shortest; repeat split; auto; lia.
  - destruct (search n s) as [q |] eqn:E.
    + destruct (search_sound _ _ _ E) as [Hq Lq].
      destruct (IH (ex_intro _ q (conj Hq Lq))) as [r [Hr Lr]].
      exists r; split; auto; lia.
    + exists p; split; auto; split; auto.
      intros q Hq; destruct (Nat.le_gt_cases (length q) n); [| lia].
      exfalso; eapply search_complete; eauto.
Qed.

(** Record the state before each move, excluding the final endpoint. *)
Fixpoint visits (s : state) (p : list move) : list state :=
  match p with
  | [] => []
  | m :: p => s :: visits (m2f m s) p
  end.

(** There is one recorded departure state for every move in a path. *)
Lemma visits_length s p : length (visits s p) = length p.
Proof.
  revert s; induction p; simpl; auto.
Qed.

(** A visited state can be reached by a prefix of the original sequence. *)
Lemma visits_split s p t : In t (visits s p) ->
  exists a b, p = a ++ b /\ run s a = t.
Proof.
  revert s; induction p as [| m p IH]; intros s H; simpl in H; [contradiction |].
  destruct H as [<- | H].
  - exists [], (m :: p); simpl; auto.
  - destruct (IH _ H) as [a [b [E R]]].
    exists (m :: a), b; simpl; subst; auto.
Qed.

(** Removing the first move from a shortest solution leaves a shortest suffix. *)
Lemma shortest_tail s m p : shortest s (m :: p) -> shortest (m2f m s) p.
Proof.
  intros [H Min]; split; auto.
  intros q Hq; specialize (Min (m :: q) Hq); simpl in Min; lia.
Qed.

(** A shortest path never revisits a state: removing the loop would shorten it. *)
Lemma shortest_nodup s p : shortest s p -> NoDup (visits s p).
Proof.
  revert s; induction p as [| m p IH]; intros s H; simpl; constructor.
  - intro Hin; destruct (visits_split _ _ _ Hin) as [a [b [E R]]].
    destruct H as [H Min]; subst p; simpl in H; rewrite run_app, R in H.
    specialize (Min b H); simpl in Min; rewrite length_app in Min; lia.
  - apply IH; eapply shortest_tail; eauto.
Qed.

(** The finite sticker space bounds loop-free paths without assuming a cube
    diameter. *)
Definition state_bound : nat := length all_states.

(** Distinct departure states bound the length of any shortest solution. *)
Lemma shortest_bound s p : shortest s p -> length p <= state_bound.
Proof.
  intro H; rewrite <- (visits_length s p); unfold state_bound.
  apply NoDup_incl_length; [apply shortest_nodup; auto |].
  intros t _; apply all_states_complete.
Qed.

(** * Iterative deepening *)

(** Try depths from [depth] through [depth + fuel], returning the first success. *)
Fixpoint deepen (fuel depth : nat) (s : state) : option (list move) :=
  match search depth s with
  | Some p => Some p
  | None =>
      match fuel with
      | 0 => None
      | S n => deepen n (S depth) s
      end
  end.

(** Search the full finite bound for a shortest solution; evaluate with [lazy]. *)
Definition solve (s : state) : option (list move) :=
  deepen state_bound 0 s.

(** Iterative deepening returns a solution within the largest depth it tries. *)
Lemma deepen_sound fuel depth s p : deepen fuel depth s = Some p ->
  run s p = init_state /\ length p <= fuel + depth.
Proof.
  revert depth; induction fuel as [| fuel IH]; intro depth; simpl;
    destruct (search depth s) as [q |] eqn:E.
  - intro H; inversion H; subst; apply search_sound in E; auto.
  - discriminate.
  - intro H; inversion H; subst; apply search_sound in E; intuition lia.
  - intro H; specialize (IH _ H); intuition lia.
Qed.

(** A solution within the final depth guarantees iterative deepening succeeds. *)
Lemma deepen_complete fuel depth s p :
  run s p = init_state -> length p <= fuel + depth -> deepen fuel depth s <> None.
Proof.
  revert depth; induction fuel as [| fuel IH]; intros depth Hp Hlen; simpl;
    destruct (search depth s) eqn:E; try discriminate.
  - intro H; eapply search_complete; eauto.
  - apply IH; auto; lia.
Qed.

(** Once all smaller depths are excluded, the first success is globally
    shortest. *)
Lemma deepen_minimal fuel depth s p :
  (forall q, run s q = init_state -> depth <= length q) ->
  deepen fuel depth s = Some p -> shortest s p.
Proof.
  revert depth; induction fuel as [| fuel IH]; intros depth Lower; simpl;
    destruct (search depth s) as [q |] eqn:E; try discriminate.
  - intro H; inversion H; subst; apply search_sound in E.
    destruct E as [Hp Lp]; split; auto; intros q Hq; specialize (Lower q Hq); lia.
  - intro H; inversion H; subst; apply search_sound in E.
    destruct E as [Hp Lp]; split; auto; intros q Hq; specialize (Lower q Hq); lia.
  - apply IH; intros q Hq.
    destruct (Nat.le_gt_cases (length q) depth); [| lia].
    exfalso; eapply search_complete; eauto.
Qed.

(** * Total solver guarantees *)

(** Every returned sequence solves the supplied cube. *)
Theorem solve_sound s p : solve s = Some p -> run s p = init_state.
Proof.
  intro H; exact (proj1 (deepen_sound _ _ _ _ H)).
Qed.

(** The total solver always chooses a globally shortest solution. *)
Theorem solve_minimal s p : solve s = Some p -> shortest s p.
Proof.
  apply deepen_minimal; intros; lia.
Qed.

(** Every physically valid cube receives a solution without supplying a witness. *)
Theorem solve_complete s : valid_state s -> exists p, solve s = Some p.
Proof.
  rewrite valid_iff_solvable; intros [p Hp].
  destruct (shortest_exists (length p) s) as [q [Hq _]]; [exists p; auto |].
  destruct (solve s) as [r |] eqn:E; [exists r; reflexivity |].
  exfalso; apply (deepen_complete state_bound 0 s q); auto.
  - exact (proj1 Hq).
  - rewrite Nat.add_0_r; apply (shortest_bound s); auto.
Qed.

(** Validity guarantees a returned solution together with its global optimality. *)
Theorem solve_init s : valid_state s ->
  exists p, solve s = Some p /\ run s p = init_state /\
    forall q, run s q = init_state -> length p <= length q.
Proof.
  intro H; destruct (solve_complete s H) as [p E].
  exists p; split; auto; apply solve_minimal; auto.
Qed.

(** The finite-state bound applies to every solution the total solver returns. *)
Theorem solve_length s p : solve s = Some p -> length p <= state_bound.
Proof.
  intro H; apply (shortest_bound s); apply solve_minimal; auto.
Qed.

(** Total search fails exactly on cubes unreachable by legal moves. *)
Theorem solve_none s : solve s = None <-> ~ valid_state s.
Proof.
  split.
  - intros E H; destruct (solve_complete s H) as [p P]; congruence.
  - intros H; destruct (solve s) as [p |] eqn:E; auto.
    exfalso; apply H; apply valid_iff_solvable; exists p; eapply solve_sound; eauto.
Qed.

(** * Bounded solver guarantees *)

(** Search up to an explicit limit; [None] means no solution fits that limit. *)
Definition solve_bounded (limit : nat) (s : state) : option (list move) :=
  deepen limit 0 s.

(** A bounded success is globally shortest and respects the requested limit. *)
Theorem solve_bounded_spec limit s p : solve_bounded limit s = Some p ->
  shortest s p /\ length p <= limit.
Proof.
  intro H; split.
  - apply (deepen_minimal limit 0 s p); [intros; lia | exact H].
  - apply deepen_sound in H; simpl in H; lia.
Qed.

(** Bounded failure excludes every solution at or below the requested depth. *)
Theorem solve_bounded_none limit s : solve_bounded limit s = None <->
  forall p, run s p = init_state -> limit < length p.
Proof.
  split.
  - intros E p Hp; destruct (Nat.le_gt_cases (length p) limit); auto.
    exfalso; apply (deepen_complete limit 0 s p); auto; lia.
  - intro H; destruct (solve_bounded limit s) as [p |] eqn:E; auto.
    apply solve_bounded_spec in E; destruct E as [[Hp _] Lp].
    specialize (H p Hp); lia.
Qed.
