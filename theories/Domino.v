From Stdlib Require Import Arith List Lia.
From Rubik Require Export Chain Subgroup.
Import ListNotations.

(** * Solving inside the subgroup

    The same method again, restricted to the ten moves the second phase may
    use. Two things change. The sequences must all be allowed moves, which is
    one more computation per table entry. And inside the subgroup nothing is
    turned or flipped, so each slot shows only which piece sits there: the
    tables need one entry per piece rather than one per piece and rotation. *)

(** A sequence the second phase may use. *)
Definition phase2_word (w : list move) : bool := forallb phase2_move w.

(** Allowed moves never leave the subgroup, so neither does a sequence of
    them, nor the cube such a sequence denotes. *)
Lemma crun_subgroup w c :
  Forall (fun m => phase2_move m = true) w -> in_subgroup c ->
  in_subgroup (crun c w).
Proof.
  revert c; induction w as [| m w IH]; intros c Hw Hc; [exact Hc |].
  inversion Hw; subst.
  change (crun c (m :: w)) with (crun (cturn m c) w).
  apply IH; [assumption | apply phase2_move_keeps_subgroup; assumption].
Qed.

Lemma phase2_word_Forall w :
  phase2_word w = true -> Forall (fun m => phase2_move m = true) w.
Proof.
  unfold phase2_word; intro H; apply Forall_forall; intros m Hm;
    rewrite forallb_forall in H; apply H, Hm.
Qed.

Lemma phase2_word_subgroup w : phase2_word w = true -> in_subgroup (element w).
Proof.
  intro H; apply crun_subgroup;
    [apply phase2_word_Forall, H | apply csolved_in_subgroup].
Qed.

(** Inside the subgroup nothing is turned, nothing is flipped, and the slice
    slots hold exactly the slice edges. *)
Lemma subgroup_twist d X : in_subgroup d -> snd (getc d X) = T0.
Proof.
  intros [[Ht _] _]; unfold twists, corner_slots in Ht;
    cbn [map] in Ht; injection Ht as ? ? ? ? ? ? ? ?;
    destruct X; cbn [getc]; assumption.
Qed.

Lemma subgroup_flip d Y : in_subgroup d -> snd (gete d Y) = F0.
Proof.
  intros [[_ Hf] _]; unfold flips, edge_slots in Hf;
    cbn [map] in Hf; injection Hf as ? ? ? ? ? ? ? ? ? ? ? ?;
    destruct Y; cbn [gete]; assumption.
Qed.

Lemma subgroup_slice d Y : in_subgroup d -> is_slice (fst (gete d Y)) = is_slice Y.
Proof.
  intros [_ Hs]; unfold sliced, slice_mask, edge_pieces, edge_slots in Hs;
    cbn [map] in Hs; injection Hs as ? ? ? ? ? ? ? ? ? ? ? ?;
    destruct Y; cbn [gete is_slice]; assumption.
Qed.

(** A cube is exactly its twenty readings, so the subgroup conditions can be
    checked one slot at a time. *)
Lemma corner_slots_map c : corner_slots c = map (getc c) all_corner_slots.
Proof. destruct c; reflexivity. Qed.

Lemma edge_slots_map c : edge_slots c = map (gete c) all_edge_slots.
Proof. destruct c; reflexivity. Qed.

Lemma in_subgroup_intro c :
  (forall X, snd (getc c X) = T0) ->
  (forall Y, snd (gete c Y) = F0) ->
  (forall Y, is_slice (fst (gete c Y)) = is_slice Y) ->
  in_subgroup c.
Proof.
  intros Hc He Hs; split; [split |].
  - unfold twists; rewrite corner_slots_map, map_map.
    transitivity (map (fun _ : corner => T0) all_corner_slots);
      [apply map_ext; exact Hc | reflexivity].
  - unfold flips; rewrite edge_slots_map, map_map.
    transitivity (map (fun _ : edge => F0) all_edge_slots);
      [apply map_ext; exact He | reflexivity].
  - unfold sliced, slice_mask, edge_pieces;
      rewrite edge_slots_map, !map_map.
    transitivity (map is_slice all_edge_slots);
      [apply map_ext; exact Hs | reflexivity].
Qed.

(** The subgroup is closed under composition. *)
Lemma subgroup_ccompose h d :
  in_subgroup h -> in_subgroup d -> in_subgroup (ccompose h d).
Proof.
  intros Hh Hd; apply in_subgroup_intro.
  - intro X; rewrite getc_ccompose.
    pose proof (subgroup_twist d X Hd) as Ht.
    destruct (getc d X) as [P t]; cbn [snd] in Ht; subst t.
    cbn [capply cshift]; apply (subgroup_twist h P Hh).
  - intro Y; rewrite gete_ccompose.
    pose proof (subgroup_flip d Y Hd) as Hf.
    destruct (gete d Y) as [P f]; cbn [snd] in Hf; subst f.
    cbn [eapply eshift]; apply (subgroup_flip h P Hh).
  - intro Y; rewrite gete_ccompose.
    pose proof (subgroup_flip d Y Hd) as Hf.
    pose proof (subgroup_slice d Y Hd) as Hsl.
    destruct (gete d Y) as [P f]; cbn [snd fst] in Hf, Hsl; subst f.
    cbn [eapply eshift]; rewrite (subgroup_slice h P Hh); exact Hsl.
Qed.

(** * Domains inside the subgroup

    Only the unturned readings occur, so the tables answer for those alone. *)

Definition cdomain0 (cs : list corner) : list cslot :=
  filter (fun v => negb (corner_inb (fst v) cs))
         (map (fun X => (X, T0)) all_corner_slots).

Lemma in_cdomain0 v cs :
  snd v = T0 -> ~ In (fst v) cs -> In v (cdomain0 cs).
Proof.
  intros Ht Hc; apply filter_In; split;
    [| rewrite (corner_inb_false _ _ Hc); reflexivity].
  apply in_map_iff; exists (fst v); split;
    [destruct v; cbn in Ht; subst; reflexivity |].
  destruct (fst v); simpl; tauto.
Qed.

Lemma ccovers_of0 t cs X d :
  forallb (ccovers t) (cdomain0 cs) = true ->
  in_subgroup d -> wellformed d -> solvedc d cs -> ~ In X cs ->
  ccovers t (getc d X) = true.
Proof.
  intros Hall Hsub Hw Hs HX; rewrite forallb_forall in Hall.
  apply Hall, in_cdomain0; [apply subgroup_twist, Hsub | apply corner_fresh; auto].
Qed.

(** An edge slot shows only pieces of its own kind: inside the subgroup the
    slice edges stay in the slice and the others stay out of it. *)
Definition edomain2 (es : list edge) (Y : edge) : list eslot :=
  filter (fun v => andb (negb (edge_inb (fst v) es))
                        (Bool.eqb (is_slice (fst v)) (is_slice Y)))
         (map (fun Z => (Z, F0)) all_edge_slots).

Lemma in_edomain2 v es Y :
  snd v = F0 -> ~ In (fst v) es -> is_slice (fst v) = is_slice Y ->
  In v (edomain2 es Y).
Proof.
  intros Hf Hc Hsl; apply filter_In; split.
  - apply in_map_iff; exists (fst v); split;
      [destruct v; cbn in Hf; subst; reflexivity |].
    destruct (fst v); simpl; tauto.
  - rewrite (edge_inb_false _ _ Hc), Hsl; cbn [negb andb].
    destruct (is_slice Y); reflexivity.
Qed.

Lemma ecovers_of2 t es Y d :
  forallb (ecovers t) (edomain2 es Y) = true ->
  in_subgroup d -> wellformed d -> solvede d es -> ~ In Y es ->
  ecovers t (gete d Y) = true.
Proof.
  intros Hall Hsub Hw Hs HY; rewrite forallb_forall in Hall.
  apply Hall, in_edomain2;
    [apply subgroup_flip, Hsub | apply edge_fresh; auto
    | apply subgroup_slice, Hsub].
Qed.

(** * The restricted chain

    Same stages, same step, but each table must also be made of allowed moves,
    and the readings it answers for are the unturned ones. *)

Fixpoint chain2_ok (cs : list corner) (es : list edge) (ss : list stage) : bool :=
  match ss with
  | [] => true
  | Cstage X t b :: r =>
      ctable_ok t cs es X && forallb (ccovers t) (cdomain0 cs) &&
      ctable_bounded t b && negb (corner_inb X cs) &&
      forallb (fun e => phase2_word (snd e)) t && chain2_ok (X :: cs) es r
  | Estage Y t b :: r =>
      etable_ok t cs es Y && forallb (ecovers t) (edomain2 es Y) &&
      etable_bounded t b && negb (edge_inb Y es) &&
      forallb (fun e => phase2_word (snd e)) t && chain2_ok cs (Y :: es) r
  end.

(** Running the restricted stages finishes their slots, stays inside the
    subgroup, and uses only allowed moves. *)
Lemma chain2_correct ss : forall cs es d,
  chain2_ok cs es ss = true -> generated d -> in_subgroup d ->
  solvedc d cs -> solvede d es ->
  generated (chain_state ss d) /\ in_subgroup (chain_state ss d) /\
  solvedc (chain_state ss d) (stagesc ss ++ cs) /\
  solvede (chain_state ss d) (stagese ss ++ es) /\
  phase2_word (chain_word ss d) = true /\
  length (chain_word ss d) <= chain_bound ss.
Proof.
  induction ss as [| s ss IH]; intros cs es d Hok Hg Hsub Hc He.
  { simpl; refine (conj Hg (conj Hsub (conj Hc (conj He (conj _ _)))));
      [reflexivity | simpl; lia]. }
  simpl in Hok |- *.
  destruct s as [X t b | Y t b];
    repeat (apply Bool.andb_true_iff in Hok as [Hok ?]).
  - match goal with H : negb _ = true |- _ => rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HX : ~ In X cs)
      by (intro Hin; rewrite (corner_inb_true X cs Hin) in Hfresh; discriminate).
    assert (Hcov : ccovers t (getc d X) = true)
      by (eapply ccovers_of0; eauto using generated_wellformed).
    assert (Hw : phase2_word (clookup t (getc d X)) = true).
    { match goal with H : forallb _ t = true |- _ =>
        rewrite forallb_forall in H; apply (H _ (clookup_in t _ Hcov)) end. }
    destruct (cstep t cs es X d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    destruct (IH (X :: cs) es _ ltac:(assumption)
                 (generated_step _ _ Hg)
                 (subgroup_ccompose _ _ (phase2_word_subgroup _ Hw) Hsub)
                 Hc' He')
      as [Hg'' [Hs'' [Hc'' [He'' [Hp'' Hl'']]]]].
    pose proof (clookup_bounded t (getc d X) b ltac:(assumption) Hcov).
    rewrite <- app_assoc; simpl.
    refine (conj Hg'' (conj Hs'' (conj Hc'' (conj He'' (conj _ _))))).
    + unfold phase2_word in *; rewrite forallb_app, Hp'', Hw; reflexivity.
    + rewrite length_app; lia.
  - match goal with H : negb _ = true |- _ => rename H into Hfresh end.
    apply Bool.negb_true_iff in Hfresh.
    assert (HY : ~ In Y es)
      by (intro Hin; rewrite (edge_inb_true Y es Hin) in Hfresh; discriminate).
    assert (Hcov : ecovers t (gete d Y) = true)
      by (eapply ecovers_of2; eauto using generated_wellformed).
    assert (Hw : phase2_word (elookup t (gete d Y)) = true).
    { match goal with H : forallb _ t = true |- _ =>
        rewrite forallb_forall in H; apply (H _ (elookup_in t _ Hcov)) end. }
    destruct (estep t cs es Y d ltac:(assumption) Hcov Hc He) as [Hc' He'].
    destruct (IH cs (Y :: es) _ ltac:(assumption)
                 (generated_step _ _ Hg)
                 (subgroup_ccompose _ _ (phase2_word_subgroup _ Hw) Hsub)
                 Hc' He')
      as [Hg'' [Hs'' [Hc'' [He'' [Hp'' Hl'']]]]].
    pose proof (elookup_bounded t (gete d Y) b ltac:(assumption) Hcov).
    rewrite <- app_assoc; simpl.
    refine (conj Hg'' (conj Hs'' (conj Hc'' (conj He'' (conj _ _))))).
    + unfold phase2_word in *; rewrite forallb_app, Hp'', Hw; reflexivity.
    + rewrite length_app; lia.
Qed.

(** The eighth up-or-down edge is forced: inside the subgroup no slice edge
    can sit in its slot, and the other seven are taken. *)
Lemma eighth_ud_edge d :
  wellformed d -> in_subgroup d ->
  solvede d [DL; DF; DR; UB; UL; UF; UR] ->
  gete d DB = (DB, F0).
Proof.
  intros Hw Hsub Hs.
  assert (Hfr : ~ In (fst (gete d DB)) [DL; DF; DR; UB; UL; UF; UR])
    by (apply edge_fresh; auto; simpl; intuition discriminate).
  pose proof (subgroup_slice d DB Hsub) as Hsl.
  pose proof (subgroup_flip d DB Hsub) as Hfl.
  destruct (gete d DB) as [P f]; cbn [fst snd] in Hfr, Hsl, Hfl; subst f.
  destruct P; try (simpl in Hfr; tauto); try discriminate Hsl; reflexivity.
Qed.
