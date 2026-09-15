(** * Process services: shared definitions

    The two things an extracted entry point needs from the host and cannot ask
    raylib for: what the environment says, and how to stop. Keeping them as
    effects is what lets the entry point itself be written in Rocq.

    Nothing here knows what the program does. [Proc.v] re-exports this module
    and adds the C++ extraction mappings. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree.
From Corelib Require Import PrimString.

(** Reading one environment variable, and ending the process. *)
Inductive procE : Type -> Type :=
| GetEnv : PrimString.string -> procE (option PrimString.string)
| ExitNow : nat -> procE unit.

(** The value of an environment variable, or nothing when it is unset. *)
Definition proc_getenv {E} `{procE -< E} (name : PrimString.string)
  : itree E (option PrimString.string) := embed (GetEnv name).

(** Stop at once with this status, without unwinding. A search deep enough to
    outlive the window is abandoned rather than waited for, so the process must
    not run destructors that could race a worker still reading its own state. *)
Definition proc_exit {E} `{procE -< E} (code : nat) : itree E unit :=
  embed (ExitNow code).
