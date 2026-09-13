(** * Process services: extraction to C++

    Re-exports [ProcDefs.v] and maps its effects onto the two wrappers in
    [process_helpers.h]. *)

From Crane Require Import Mapping.Std Monads.ITree.
From Crane Require Extraction.
From Rubik Require Export native.ProcDefs.

Crane Extract Inductive procE => ""
  [ "rl_getenv(%a0)" "rl_exit_now(%a0)" ]
  From "process_helpers.h".

Crane Extract Inlined Constant proc_getenv => "rl_getenv(%a0)"
  From "process_helpers.h".
Crane Extract Inlined Constant proc_exit => "rl_exit_now(%a0)"
  From "process_helpers.h".
