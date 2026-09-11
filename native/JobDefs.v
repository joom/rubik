(** * Cancellable background jobs: shared definitions

    A job runs a pure function off the calling thread and is then *polled*,
    never waited for, so an interactive loop keeps running while it works.
    This is what [Monads.Par] does not offer: [future.get] blocks, and so does
    [Monads.Thread]'s [join]. Cancelling abandons a job that is still running
    rather than waiting for it to notice.

    Nothing here knows what the job computes. [Job.v] re-exports this module
    and adds the C++ extraction mappings. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree.

(** A handle on a background computation of a [B]. *)
Axiom job : Type -> Type.

(** Starting, polling, and abandoning one background computation. *)
#[universes(polymorphic)]
Inductive jobE : Type -> Type :=
| StartJob : forall {A B}, (A -> B) -> A -> jobE (job B)
| PollJob : forall {B}, job B -> jobE (option B)
| CancelJob : forall {B}, job B -> jobE unit.

(** Run [f] on [a] off the calling thread and return a handle at once. *)
Definition job_start {E} `{jobE -< E} {A B} (f : A -> B) (a : A)
  : itree E (job B) := embed (StartJob f a).

(** The finished value, once, or nothing while the job is still running.
    This never blocks, and never returns the value of a cancelled job. *)
Definition job_poll {E} `{jobE -< E} {B} (h : job B) : itree E (option B) :=
  embed (PollJob h).

(** Abandon a job. It may still be running, but nothing will read its result. *)
Definition job_cancel {E} `{jobE -< E} {B} (h : job B) : itree E unit :=
  embed (CancelJob h).
