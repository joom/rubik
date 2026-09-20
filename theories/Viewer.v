From Stdlib Require Import Arith List.
From Rubik Require Import Cube.BasicRubik Cube.Geometry Search.Solve.
Import ListNotations.

(** * A value-only boundary for the native viewer *)

(** Face numbers follow the model's U/R/F/D/L/B order at the native boundary. *)
Definition face_code (f : face) : nat :=
  match f with
  | Up => 0 | Right => 1 | Front => 2 | Down => 3 | Left => 4 | Back => 5
  end.

(** Unknown color numbers default to the back-face color. *)
Definition code_face (n : nat) : face := nth n faces Back.

(** Flatten a triple without changing the order of its entries. *)
Definition triple_list {A} (t : triple A) : list A :=
  let '(Triple a b c) := t in [a; b; c].

(** Serialize all 54 colors as plain numbers, independent of C++ object layout. *)
Definition colors_of (s : state) : list nat :=
  let '(a, b) := s in
  map face_code (flat_map (fun g => flat_map triple_list (triple_list g))
                         (triple_list a ++ triple_list b)).

(** Read one row from a color snapshot, using solved-up colors for missing entries. *)
Definition read_row (xs : list nat) (offset : nat) : triple color :=
  Triple (code_face (nth offset xs 0))
         (code_face (nth (offset + 1) xs 0))
         (code_face (nth (offset + 2) xs 0)).

(** Read three consecutive rows from a color snapshot. *)
Definition read_grid (xs : list nat) (offset : nat) : grid :=
  Triple (read_row xs offset) (read_row xs (offset + 3))
         (read_row xs (offset + 6)).

(** Reconstruct the six face grids from a snapshot in model order. *)
Definition from_colors (xs : list nat) : state :=
  (Triple (read_grid xs 0) (read_grid xs 9) (read_grid xs 18),
   Triple (read_grid xs 27) (read_grid xs 36) (read_grid xs 45)).

(** Serializing a color and reading it back preserves that color. *)
Lemma face_code_roundtrip f : code_face (face_code f) = f.
Proof. destruct f; reflexivity. Qed.

(** Native snapshots round-trip every sticker, including unsolved states. *)
Theorem colors_roundtrip s : from_colors (colors_of s) = s.
Proof.
  destruct_state s; unfold from_colors, read_grid, read_row;
    cbn [colors_of triple_list flat_map map app nth Nat.add].
  repeat rewrite face_code_roundtrip; reflexivity.
Qed.

(** Every cube snapshot has exactly one entry per sticker. *)
Theorem colors_length s : length (colors_of s) = 54.
Proof. destruct_state s; reflexivity. Qed.

(** Consecutive move codes group clockwise, half, and inverse turns by face. *)
Definition move_code (m : move) : nat :=
  let '(f, t) := m in
  3 * face_code f + match t with CW => 0 | Half => 1 | CCW => 2 end.

(** Decode a move code; the native input layer supplies values from zero to 17. *)
Definition code_move (n : nat) : move :=
  (nth (n / 3) faces Up, nth (n mod 3) [CW; Half; CCW] CW).

(** The native move encoding preserves every one of the 18 legal moves. *)
Lemma move_code_roundtrip m : code_move (move_code m) = m.
Proof. destruct m as [f t]; destruct f, t; reflexivity. Qed.

(** Encoding and decoding a whole solution preserves its order and moves. *)
Lemma path_code_roundtrip p : map code_move (map move_code p) = p.
Proof.
  induction p as [| m p IH]; simpl; auto.
  rewrite move_code_roundtrip, IH; reflexivity.
Qed.

(** How deep each phase may look before giving up. These are the lengths the
    solving method in [Solvable.v] needs, which is what makes the search
    provably answer. A real cube is finished far sooner, at about twelve moves
    and eighteen, since the deepening stops at the first depth that works; the
    limits only decide when the worker abandons a cube it cannot solve. *)
Definition phase1_limit : nat := full_bound.

(** And the depth the second phase is allowed. *)
Definition phase2_limit : nat := domino_bound.

(** The worker solves its snapshot in two phases. The six pruning tables are
    built once per request rather than once per node. *)
Definition solve_snapshot (xs : list nat) : option (list nat) :=
  let T1 := build_tables1 tt in
  let T2 := build_tables2 tt in
  option_map (map move_code)
    (solve_two_phase T1 T2 phase1_limit phase2_limit (from_colors xs)).

(** Every worker result decodes to a sequence that really solves its snapshot.
    This is weaker than the exhaustive solver's guarantee, which was that the
    sequence is as short as possible; two-phase solutions are short but not
    always shortest. It holds however the tables came out. *)
Theorem solve_snapshot_sound s p :
  valid_state s -> solve_snapshot (colors_of s) = Some p ->
  run s (map code_move p) = init_state.
Proof.
  intro Hv; unfold solve_snapshot; rewrite colors_roundtrip.
  destruct (solve_two_phase _ _ _ _ s) as [q|] eqn:E; simpl; try discriminate.
  intro H; inversion H; subst p; rewrite path_code_roundtrip.
  exact (solve_two_phase_sound _ _ _ _ _ _ Hv E).
Qed.

(** The background job receives only the cube snapshot. *)
Definition solve_request : list nat -> option (list nat) := solve_snapshot.

(** The job entry point carries the same guarantee as the solver itself. *)
Theorem solve_request_sound s p :
  valid_state s -> solve_request (colors_of s) = Some p ->
  run s (map code_move p) = init_state.
Proof. apply solve_snapshot_sound. Qed.

(** * Pure interaction state *)

(** Named phases distinguish pending work, successful plans, and bounded failure. *)
Inductive ui_state := Ready | Searching | SolutionReady | Solved | NoSolution | InvalidReply.

(** Encode display phases at the native boundary, without exposing Rocq constructors. *)
Definition ui_state_code (p : ui_state) : nat :=
  match p with
  | Ready => 0 | Searching => 1 | SolutionReady => 2 | Solved => 3
  | NoSolution => 4 | InvalidReply => 6
  end.

(** The viewer owns a cube, undo history, pending solution, and playback controls. *)
Record view := View {
  cube : state; (** The current 54-sticker state. *)
  history : list move; (** Executed moves, newest first, for undo. *)
  solution : list move; (** Remaining solution moves in execution order. *)
  playing : bool; (** Whether timer events advance the solution. *)
  status : ui_state (** The current interaction state. *)
}.

(** Start solved with no pending actions. *)
Definition initial_view (_ : unit) : view := View init_state [] [] false Ready.

(** Applying a manual turn records its inverse opportunity and discards stale solutions. *)
Definition turn_view (m : move) (v : view) : view :=
  View (turn m (cube v)) (m :: history v) [] false Ready.

(** Undo removes exactly one manual or playback move from the history. *)
Definition undo_view (v : view) : view :=
  match history v with
  | [] => v
  | m :: rest => View (turn (inverse m) (cube v)) rest [] false Ready
  end.

(** Playback applies the next certified move while retaining the rest of the plan. *)
Definition step_view (v : view) : view :=
  match solution v with
  | [] => View (cube v) (history v) [] false (status v)
  | m :: rest =>
      View (turn m (cube v)) (m :: history v) rest
           (andb (playing v) (negb (Nat.eqb (length rest) 0)))
           (if Nat.eqb (length rest) 0 then Solved else SolutionReady)
  end.

(** A result is accepted only if replaying it actually solves the current cube. *)
Definition accept_solution (p : list nat) (v : view) : view :=
  let moves := map code_move p in
  if state_eq (run (cube v) moves) init_state
  then View (cube v) (history v) moves false SolutionReady
  else View (cube v) (history v) [] false InvalidReply.

(** Even an erroneous external reply cannot install a non-solving move sequence. *)
Theorem accepted_solution_solves p v :
  status (accept_solution p v) = SolutionReady ->
  run (cube v) (solution (accept_solution p v)) = init_state.
Proof.
  unfold accept_solution.
  destruct (state_eq (run (cube v) (map code_move p)) init_state) eqn:E;
    simpl; try discriminate.
  intros _; apply state_eq_correct; exact E.
Qed.

(** Manual turns preserve physical validity throughout interaction. *)
Theorem turn_view_valid m v : valid_state (cube v) -> valid_state (cube (turn_view m v)).
Proof. apply move_valid. Qed.

(** Pending searches temporarily suppress cube edits until completion or cancellation. *)
Definition searching (v : view) : bool :=
  match status v with Searching => true | _ => false end.

(** The worker also always answers, with nothing assumed. *)
Theorem solve_snapshot_complete s :
  valid_state s -> exists p, solve_snapshot (colors_of s) = Some p.
Proof.
  intro Hv; unfold solve_snapshot, phase1_limit, phase2_limit;
    rewrite colors_roundtrip.
  destruct (solve_two_phase_complete tt tt s Hv) as [q Hq].
  rewrite Hq; exists (map move_code q); reflexivity.
Qed.

(** The same for the job entry point. *)
Theorem solve_request_complete s :
  valid_state s -> exists p, solve_request (colors_of s) = Some p.
Proof. apply solve_snapshot_complete. Qed.
