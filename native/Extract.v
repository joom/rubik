From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.DequeList
  Mapping.ZInt Mapping.Real Monads.ITree.
From Crane Require Extraction.
From Rubik Require Import BasicRubik Solver Viewer native.App.

(** Triples become value arrays, so solver snapshots share no reference counts
    across threads. *)
Crane Extract Inductive triple => "std::array<%t0, 3>"
  [ "std::array<%t0, 3>{%a0, %a1, %a2}" ]
  "const auto& [%b0a0, %b0a1, %b0a2] = %scrut; %br0" From "array".

Set Crane Loopify.
(** Crane's loopification currently requests a mutable accessor on lazy
    cotrees. Keep this depth-bounded traversal recursive until that is fixed. *)
Crane NoLoopify walk.
Set Crane Extraction Output Directory ".".
Crane Extraction "rubik" init_state m2f run inverse solve_bounded
  colors_of from_colors move_code code_move solve_snapshot solve_request
  program.
