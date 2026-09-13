(** Lists stay Crane's persistent cons lists. Mapping them to [std::deque]
    makes every cons copy the whole list, which turns building the solver's
    pruning tables from milliseconds into minutes. *)
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Mapping.ZInt Mapping.Real Monads.ITree.
From Crane Require Extraction.
From Rubik Require Import BasicRubik Viewer native.App.

(** Triples become value arrays, so solver snapshots share no reference counts
    across threads. *)
Crane Extract Inductive triple => "std::array<%t0, 3>"
  [ "std::array<%t0, 3>{%a0, %a1, %a2}" ]
  "const auto& [%b0a0, %b0a1, %b0a2] = %scrut; %br0" From "array".

Set Crane Loopify.
Set Crane Extraction Output Directory ".".
Crane Extraction "rubik" init_state m2f run
  colors_of from_colors move_code code_move solve_snapshot solve_request
  program.
