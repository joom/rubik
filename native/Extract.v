(** Lists stay Crane's persistent cons lists. Mapping them to [std::deque]
    makes every cons copy the whole list, which turns building the solver's
    pruning tables from milliseconds into minutes. *)
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Mapping.ZInt Mapping.Real Monads.ITree.
From Crane Require Extraction.
From Rubik Require Import Sticker native.App.

(** Triples become value arrays, so solver snapshots share no reference counts
    across threads. *)
Crane Extract Inductive triple => "std::array<%t0, 3>"
  [ "std::array<%t0, 3>{%a0, %a1, %a2}" ]
  "const auto& [%b0a0, %b0a1, %b0a2] = %scrut; %br0" From "array".

Set Crane Loopify.
Set Crane Extraction Output Directory ".".
(** [main] is the whole program: extraction emits the C++ entry point from it,
    so the executable is the generated file and nothing else. *)
Crane Extraction "rubik" main.
