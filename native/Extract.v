(** Lists stay Crane's persistent cons lists. Mapping them to [std::deque]
    makes every cons copy the whole list, which turns building the solver's
    pruning tables from milliseconds into minutes. *)
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Mapping.ZInt Mapping.Real Monads.ITree.
From Crane Require Extraction.
From Stdlib Require Import BinPos.
From Rubik Require Import Cube.Sticker Native.App.

(** Triples become value arrays, so solver snapshots share no reference counts
    across threads. *)
Crane Extract Inductive triple => "std::array<%t0, 3>"
  [ "std::array<%t0, 3>{%a0, %a1, %a2}" ]
  "const auto& [%b0a0, %b0a1, %b0a2] = %scrut; %br0" From "array".

(** Table indices are binary numbers, so a lookup is a walk down the bits
    rather than arithmetic on a machine word. Crane's own mapping sends
    [positive] to a 32-bit unsigned int; the edge-placement indices need
    thirty-three bits, so it is widened to a 64-bit one here. Overriding a
    mapping that [Mapping.ZInt] already set is what the overlap warnings
    below are about, and widening is the safe direction. *)
Crane Extract Inductive positive =>
  "std::uint64_t"
  [ "(2 * %a0 + 1)" "(2 * %a0)" "UINT64_C(1)" ]
  "if (%scrut == 1) { %br2 } else if (%scrut % 2 != 0) { std::uint64_t %b0a0 = (%scrut - 1) / 2; %br0 } else { std::uint64_t %b1a0 = %scrut / 2; %br1 }"
  From "cstdint".

Set Crane Loopify.
Set Crane Extraction Output Directory ".".
(** [main] is the whole program: extraction emits the C++ entry point from it,
    so the executable is the generated file and nothing else. *)
Crane Extraction "rubik" main.
