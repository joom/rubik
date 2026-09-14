From Stdlib Require Import Arith List Lia.
From Rubik Require Export ChainTables DominoTables.
Import ListNotations.

(** * Every solvable cube has a short solution

    The chain finishes the seven corners its tables cover, then the eighth is
    forced: it holds the only piece left, unturned because the rotations
    cancel. Then the ten edges its tables cover, then the eleventh, whose
    piece is forced by parity and whose flip the last table fixes, and then
    the twelfth, forced the same way as the eighth.

    Nothing about the tables is assumed. Everything they have to satisfy was
    computed when [ChainTables.v] was compiled. *)

Theorem full_solution c :
  csolvable c -> exists r, crun c r = csolved /\ length r <= full_bound.
Proof.
  intro Hs.
  assert (Hg : generated c) by (apply generated_csolvable, Hs).
  assert (Hc0 : solvedc c []) by (intros ? []).
  assert (He0 : solvede c []) by (intros ? []).

  (** The seven corner stages. *)
  destruct (chain_correct corner_stages [] [] c corner_stages_ok Hg Hc0 He0)
    as [HgA [HcA HeA]].
  pose proof (chain_length corner_stages [] [] c corner_stages_ok Hg Hc0 He0) as HlA.
  rewrite corner_stages_slots, app_nil_r in HcA.

  (** The eighth corner is forced. *)
  assert (HDRB : getc (chain_state corner_stages c) DRB = (DRB, T0)).
  { apply last_corner;
      [apply generated_wellformed, HgA | apply generated_twist, HgA |].
    eapply solvedc_sub; [| exact HcA]; simpl; tauto. }
  assert (HcA8 : solvedc (chain_state corner_stages c) all_corner_slots)
    by (intros X HX; destruct X; first [exact HDRB | apply HcA; simpl; tauto]).
  assert (HeA0 : solvede (chain_state corner_stages c) []) by (intros ? []).

  (** The ten edge stages. *)
  destruct (chain_correct edge_stages all_corner_slots []
              (chain_state corner_stages c) edge_stages_ok HgA HcA8 HeA0)
    as [HgB [HcB HeB]].
  pose proof (chain_length edge_stages all_corner_slots []
                (chain_state corner_stages c) edge_stages_ok HgA HcA8 HeA0) as HlB.
  rewrite edge_stages_slots, app_nil_r in HeB.
  rewrite edge_stages_corners, app_nil_l in HcB.

  (** The eleventh edge holds its own piece; only its flip can be wrong. *)
  assert (HBL : fst (gete (chain_state edge_stages (chain_state corner_stages c)) BL)
                = BL).
  { apply eleventh_edge;
      [apply generated_wellformed, HgB | apply generated_cparity, HgB | exact HcB |].
    eapply solvede_sub; [| exact HeB]; simpl; tauto. }
  assert (Hcov : ecovers etab_10
                   (gete (chain_state edge_stages (chain_state corner_stages c)) BL)
                 = true)
    by (apply ecovers_forced;
        [apply etab_10_covers_0 | apply etab_10_covers_1 | exact HBL]).
  destruct (estep etab_10 all_corner_slots
              [FL; FR; DB; DL; DF; DR; UB; UL; UF; UR] BL
              (chain_state edge_stages (chain_state corner_stages c))
              etab_10_ok Hcov HcB HeB) as [HcC HeC].
  pose proof (elookup_bounded etab_10
                (gete (chain_state edge_stages (chain_state corner_stages c)) BL)
                17 etab_10_bounded Hcov) as Hl10.
  assert (HgC : generated (ccompose (element (elookup etab_10
                   (gete (chain_state edge_stages (chain_state corner_stages c)) BL)))
                   (chain_state edge_stages (chain_state corner_stages c))))
    by (apply generated_step, HgB).

  (** The twelfth edge is forced. *)
  assert (HBR : gete (ccompose (element (elookup etab_10
                  (gete (chain_state edge_stages (chain_state corner_stages c)) BL)))
                  (chain_state edge_stages (chain_state corner_stages c))) BR
                = (BR, F0)).
  { apply last_edge;
      [apply generated_wellformed, HgC | apply generated_flip, HgC |].
    eapply solvede_sub; [| exact HeC]; simpl; tauto. }
  assert (HeC12 : solvede (ccompose (element (elookup etab_10
                    (gete (chain_state edge_stages (chain_state corner_stages c)) BL)))
                    (chain_state edge_stages (chain_state corner_stages c)))
                    all_edge_slots)
    by (intros Y HY; destruct Y; first [exact HBR | apply HeC; simpl; tauto]).
  assert (Hfin : ccompose (element (elookup etab_10
                   (gete (chain_state edge_stages (chain_state corner_stages c)) BL)))
                   (chain_state edge_stages (chain_state corner_stages c)) = csolved)
    by (apply solved_everywhere; [exact HcC | exact HeC12]).

  (** The three sequences, joined in the order they compose. *)
  exists ((elookup etab_10
             (gete (chain_state edge_stages (chain_state corner_stages c)) BL)
           ++ chain_word edge_stages (chain_state corner_stages c))
          ++ chain_word corner_stages c).
  split.
  - apply solution_of_left; [exact Hs |].
    rewrite <- ccompose_steps, <- ccompose_steps.
    rewrite (chain_state_word corner_stages c).
    rewrite (chain_state_word edge_stages (chain_state corner_stages c)).
    exact Hfin.
  - rewrite !length_app, <- full_bound_ok, Nat.add_assoc.
    apply Nat.add_le_mono; [apply Nat.add_le_mono |]; assumption.
Qed.

(** * And a short solution using only the ten allowed moves

    The same method again inside the subgroup, where nothing is turned or
    flipped: seven corner stages, then the eighth corner forced, then seven
    for the outer edges and the eighth forced, then two slice stages and the
    last two slice edges forced, one by parity and one by counting. *)

Local Notation dA c := (chain_state dcorner_stages c).
Local Notation dB c := (chain_state dud_stages (chain_state dcorner_stages c)).
Local Notation dC c :=
  (chain_state dslice_stages
     (chain_state dud_stages (chain_state dcorner_stages c))).

Theorem subgroup_solution c :
  csolvable c -> in_subgroup c ->
  exists r, Forall (fun m => phase2_move m = true) r /\
            crun c r = csolved /\ length r <= domino_bound.
Proof.
  intros Hs Hsub.
  assert (Hg : generated c) by (apply generated_csolvable, Hs).
  assert (Hc0 : solvedc c []) by (intros ? []).
  assert (He0 : solvede c []) by (intros ? []).

  (** The seven corner stages, then the eighth corner. *)
  destruct (chain2_correct dcorner_stages [] [] c dcorner_stages_ok Hg Hsub Hc0 He0)
    as [HgA [HsA [HcA [HeA [HpA HlA]]]]].
  rewrite dcorner_stages_slots, app_nil_r in HcA.
  assert (HDRB : getc (dA c) DRB = (DRB, T0)).
  { apply last_corner;
      [apply generated_wellformed, HgA | apply generated_twist, HgA |].
    eapply solvedc_sub; [| exact HcA]; simpl; tauto. }
  assert (HcA8 : solvedc (dA c) all_corner_slots)
    by (intros X HX; destruct X; first [exact HDRB | apply HcA; simpl; tauto]).
  assert (HeA0 : solvede (dA c) []) by (intros ? []).

  (** The seven outer edge stages, then the eighth outer edge. *)
  destruct (chain2_correct dud_stages all_corner_slots [] (dA c)
              dud_stages_ok HgA HsA HcA8 HeA0)
    as [HgB [HsB [HcB [HeB [HpB HlB]]]]].
  rewrite dud_stages_slots, app_nil_r in HeB.
  rewrite dud_stages_corners, app_nil_l in HcB.
  assert (HDB : gete (dB c) DB = (DB, F0)).
  { apply eighth_ud_edge; [apply generated_wellformed, HgB | exact HsB |].
    eapply solvede_sub; [| exact HeB]; simpl; tauto. }
  assert (HeB8 : solvede (dB c) ud_done)
    by (intros Y HY; unfold ud_done in HY; destruct Y; simpl in HY;
        first [exact HDB | apply HeB; simpl; tauto
              | exfalso; clear -HY; intuition discriminate]).

  (** The two slice stages, then the last two slice edges. *)
  destruct (chain2_correct dslice_stages all_corner_slots ud_done (dB c)
              dslice_stages_ok HgB HsB HcB HeB8)
    as [HgC [HsC [HcC [HeC [HpC HlC]]]]].
  rewrite dslice_stages_slots in HeC.
  rewrite dslice_stages_corners, app_nil_l in HcC.
  unfold ud_done in HeC; cbn [app] in HeC.
  assert (HBLp : fst (gete (dC c) BL) = BL).
  { apply eleventh_edge;
      [apply generated_wellformed, HgC | apply generated_cparity, HgC | exact HcC |].
    eapply solvede_sub; [| exact HeC]; simpl; tauto. }
  assert (HBL : gete (dC c) BL = (BL, F0)).
  { pose proof (subgroup_flip (dC c) BL HsC) as Hf.
    destruct (gete (dC c) BL) as [P f]; cbn [fst snd] in HBLp, Hf; subst; reflexivity. }
  assert (HBR : gete (dC c) BR = (BR, F0)).
  { apply last_edge;
      [apply generated_wellformed, HgC | apply generated_flip, HgC |].
    intros Y HY; destruct Y; simpl in HY;
      first [exact HBL | apply HeC; simpl; tauto
            | exfalso; clear -HY; intuition discriminate]. }
  assert (HeC12 : solvede (dC c) all_edge_slots)
    by (intros Y HY; destruct Y;
        first [exact HBR | exact HBL | apply HeC; simpl; tauto]).
  assert (Hfin : (dC c) = csolved)
    by (apply solved_everywhere; [exact HcC | exact HeC12]).

  (** The three sequences, joined in the order they compose. *)
  exists ((chain_word dslice_stages (dB c) ++ chain_word dud_stages (dA c))
          ++ chain_word dcorner_stages c).
  split; [| split].
  - apply Forall_app; split; [apply Forall_app; split |];
      apply phase2_word_Forall; assumption.
  - apply solution_of_left; [exact Hs |].
    rewrite <- ccompose_steps, <- ccompose_steps.
    rewrite (chain_state_word dcorner_stages c).
    rewrite (chain_state_word dud_stages (chain_state dcorner_stages c)).
    rewrite (chain_state_word dslice_stages
               (chain_state dud_stages (chain_state dcorner_stages c))).
    exact Hfin.
  - rewrite !length_app, <- domino_bound_ok, Nat.add_assoc.
    apply Nat.add_le_mono; [apply Nat.add_le_mono |]; assumption.
Qed.
