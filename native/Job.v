(** * Cancellable background jobs: extraction to C++

    Re-exports [JobDefs.v] and maps its effects onto the header in
    [background_job.hpp], which spawns one detached thread per job and keeps
    its result in a cell both sides share. *)

From Crane Require Import Mapping.Std Monads.ITree.
From Crane Require Extraction.
From minirubik Require Export native.JobDefs.

Crane Extract Inlined Constant job => "crane::job<%t0>"
  From "background_job.hpp".

Crane Extract Inductive jobE => ""
  [ "crane::job_start(%a0, %a1)" "%a0.poll()" "%a0.cancel()" ]
  From "background_job.hpp".

Crane Extract Inlined Constant job_start => "crane::job_start(%a0, %a1)"
  From "background_job.hpp".
Crane Extract Inlined Constant job_poll => "%a0.poll()"
  From "background_job.hpp".
Crane Extract Inlined Constant job_cancel => "%a0.cancel()"
  From "background_job.hpp".
