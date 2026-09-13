From Stdlib Require Import List.
From Rubik Require Import Cubie Geometry Invariant Phase1 Subgroup Solve Tables Viewer.
Import ListNotations.

(** * Proof assumption audit

    Every theorem below must report that it is closed under the global
    context: the development rests on no axioms of its own. *)

Print Assumptions quarter_geometry.
Print Assumptions colors_roundtrip.
Print Assumptions solve_request_correct.
Print Assumptions accepted_solution_solves.

Print Assumptions paint_cquarter.
Print Assumptions paint_crun.
Print Assumptions to_cubies_paint.
Print Assumptions paint_to_cubies.
Print Assumptions in_G1_phase2.
Print Assumptions twist_total_valid.
Print Assumptions flip_total_valid.
Print Assumptions slice_count_valid.
Print Assumptions consistentb_admissible.
Print Assumptions twists_cm2f.
Print Assumptions flips_cm2f.
Print Assumptions slice_mask_cm2f.
Print Assumptions cpieces_cm2f.
Print Assumptions e8pieces_cm2f.
Print Assumptions e4pieces_cm2f.
Print Assumptions twist_h_admissible.
Print Assumptions cperm_h_admissible.
Print Assumptions flip_h_admissible.
Print Assumptions slice_h_admissible.
Print Assumptions e8_h_admissible.
Print Assumptions e4_h_admissible.
Print Assumptions in_G1b_spec.
Print Assumptions phase1_sound.
Print Assumptions phase2_sound.
Print Assumptions two_phase_sound.
Print Assumptions solve_two_phase_sound.

(** * Executable regressions

    Small computations that would break loudly if the model drifted. *)

(** A single twisted corner has correct centres and correct colours, yet no
    scramble can produce it: the corner rotations of a reachable cube cancel. *)
Example twisted_corner_unreachable :
  ~ valid_state (paint (Cube (URF, T1) (UFL, T0) (ULB, T0) (UBR, T0)
                             (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
                             (UR, F0) (UF, F0) (UL, F0) (UB, F0)
                             (DR, F0) (DF, F0) (DL, F0) (DB, F0)
                             (FR, F0) (FL, F0) (BL, F0) (BR, F0))).
Proof.
  intro H; apply twist_total_valid in H.
  rewrite to_cubies_paint in H; vm_compute in H; discriminate.
Qed.

(** A front quarter turn flips four edges, so it leaves the subgroup the
    second phase searches. This is why the second phase may not use it. *)
Example front_leaves_G1 : flips (cm2f (Front, CW) csolved) <> repeat F0 12.
Proof. vm_compute; discriminate. Qed.

(** Half turns of the same face stay inside it. *)
Example front_half_keeps_G1 : in_G1 (cm2f (Front, Half) csolved).
Proof. apply in_G1_phase2; [reflexivity | apply in_G1_csolved]. Qed.

(** Reading a scrambled cube's pieces, turning them, and painting back agrees
    with turning the stickers directly. *)
Example cubies_roundtrip :
  let s := run init_state [(Right, CW); (Up, Half); (Front, CCW)] in
  paint (cm2f (Left, CW) (to_cubies s)) = m2f (Left, CW) s.
Proof. vm_compute; reflexivity. Qed.

(** The monochrome cube fails the centre invariant, so it is not a cube any
    scramble can produce. *)
Definition monochrome : state :=
  (Triple (solid Up) (solid Up) (solid Up),
   Triple (solid Up) (solid Up) (solid Up)).

(** Its centres disagree with the solved frame, which no legal move can do. *)
Example monochrome_unreachable : ~ valid_state monochrome.
Proof.
  intro H; pose proof (valid_centers monochrome H Right) as E; discriminate E.
Qed.

(** Solving end to end is not exercised here. It would force the six pruning
    tables to be built inside a proof term, which the kernel then has to
    replay on every independent recheck. The solver is exercised by running
    it, not by proving what it returns. *)
