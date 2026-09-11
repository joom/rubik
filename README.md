# Certified 3×3×3 Rubik’s cube solver

This repository models all 54 stickers of a 3×3×3 cube and proves that its
solver returns a shortest solution for every state reachable by legal moves.
It builds with **Rocq 9.0.0** and the standard library; BigNums is no longer
required.

```sh
opam exec -- make
opam exec -- make check
```

The build is driven by **dune**: the `Makefile` is a thin set of entry points
over `dune build`. `make` builds the proofs in [theories/](theories), and
`make check` also checks the generated move tables and rechecks the compiled
proofs with `rocqchk`, independently of the build. Python 3 is needed only for
the table check and regeneration. `make install` installs the `minirubik`
namespace.

## Model and moves

A `state` contains six 3×3 sticker grids in the order **Up, Right, Front,
Down, Left, Back**:

```coq
Definition state := (triple grid * triple grid)%type.
Definition grid := triple (triple color).
```

Each grid contains three rows, each with three colors. Rows run top to bottom
and columns left to right when viewing the face from outside. Colors use the
six face names. `init_state` has each face uniformly colored with its own name.
The coordinate convention is specified in [Geometry.v](theories/Geometry.v): +x is
right, +y is up, and +z is front.

A move is a pair `(face, turns)`, where `turns` is `CW`, `Half`, or `CCW`.
There are 18 moves. Clockwise is viewed from outside the moving face. All
moves cost one, including half turns: solutions are minimal in the **face-turn
metric**. Centers are fixed; all eight corners and twelve edges move.

`m2f m s` applies a move, `run s moves` applies a sequence from left to right,
and `inverse moves` reverses a sequence and inverts each move.

`valid_state s` means that some sequence of legal moves takes `init_state` to
`s`. This is a reachability definition of physical validity, not a separate
algebraic test of corner twists, edge flips, and permutation parity. Arbitrary
sticker assignments can be represented, but the completeness theorem only
requires this physical validity predicate. Whole-cube rotations are not moves;
the solved center colors fix the reference frame.

## Using the solver

```coq
From Stdlib Require Import List.
From minirubik Require Import Solver.
Import ListNotations.

Definition scrambled := run init_state [(Right, CW); (Up, CW)].

Eval lazy in solve scrambled.
(* Some [(Up, CCW); (Right, CCW)] *)

Eval vm_compute in solve_bounded 2 scrambled.
(* Some [(Up, CCW); (Right, CCW)] *)

Eval vm_compute in solve_bounded 1 scrambled.
(* None: no solution of length at most 1 *)
```

`solve : state -> option (list move)` uses iterative deepening. A successful
result is globally shortest. It searches up to a proved finite-state bound,
so `None` means that the cube is invalid. No scramble history or validity
proof is an input to the computation.

**This is an exhaustive reference solver, not a fast solver for arbitrary
scrambles.** The branching factor is 18 and the general termination bound is
`6^54`, the size of the unrestricted sticker space. That bound is deliberately
loose; it does not claim the cube’s actual diameter. Deep scrambles and
exhaustive invalidity checks are computationally impractical.

Use `lazy` with `solve`: it searches shallow depths before evaluating the
rest of the enormous finite-state bound. Eager evaluation such as `vm_compute`
of `solve` attempts to materialize that bound. For controlled computations,
use `solve_bounded limit s` with `vm_compute`. A bounded success is still
globally shortest; bounded `None` means only that the required depth exceeds
`limit`. [Example.v](theories/Example.v) contains executable regressions.

## Native 3D viewer

The cube is also a raylib application whose every decision lives in Rocq: the
palette, the panel layout, hit testing, the orbit camera, the turn animation,
and the frame loop. [Crane](https://github.com/bloomberg/crane) extracts all of
it to C++.

![Viewer screenshot](assets/screenshot.png)

### How the layers are arranged

[native/RaylibDefs.v](native/RaylibDefs.v) and [native/Raylib.v](native/Raylib.v)
are **generic raylib bindings**. They mention no cube. They declare the handle
and geometry types, the key and button names, and one effect per raylib call,
and they map those effects onto [native/raylib_helpers.h](native/raylib_helpers.h),
a header of thin inline wrappers. Any application could build on them, the same
way Rocqman builds on its separate SDL2 bindings. They live in this repository
only for convenience.

[native/JobDefs.v](native/JobDefs.v) and [native/Job.v](native/Job.v) are a
second, equally generic binding: a **cancellable background job**. `job_start`
runs any pure Rocq function off the calling thread and hands back a handle,
`job_poll` reads its finished value at most once without ever blocking, and
`job_cancel` abandons it. Crane's own `Monads.Par` and `Monads.Thread` do not
fit here, because `future.get` and `join` both block, and an interactive loop
cannot afford either. [native/background_job.hpp](native/background_job.hpp)
implements it with one detached thread and a cell the two sides share.

Solving the cube is just one use of that job. [native/App.v](native/App.v) is
the viewer written against both bindings, running at `raylibE +' jobE`, so
neither binding knows about the other or about a cube.

That leaves the C++ side with nothing to decide. It wraps raylib calls, it runs
a thread, and it parses two command-line arguments. Every pixel position, every
color, every hit test, and every frame of animation is computed by extracted
Rocq, and the function the worker thread runs is named by Rocq too, so the
native side cannot substitute a different solver.

Positions and angles are Rocq reals, which Crane extracts to a `long double`
wrapper, so the rendering layer sits outside the proof trust boundary. The
certified cube results do not depend on it: they go through
[Viewer.v](theories/Viewer.v), whose 54-number boundary is checked with the rest of the
proofs.

`colors_roundtrip` proves that a 54-number snapshot decodes back to the same
state, `solve_request_correct` proves that a reply from the job decodes to a
globally shortest solution, and `accepted_solution_solves` proves that a wrong
or stale reply can never be installed as a plan.

### Animation

Every turn is animated. The application hands the frame its own undo history,
compares it against the previous frame's, and reads a single pushed or popped
move as the layer to sweep and the direction to sweep it. It keeps the old
snapshot on screen until the sweep lands, so the picture and the model never
disagree. A turn in progress owns the cube, so commands cannot pile up. Resets
and scrambles change the history by more than one move and are shown at once.

### Building

Crane is a submodule, so clone with it:

```sh
git clone --recurse-submodules https://github.com/joom/rubik.git
git submodule update --init crane     # if you already cloned without it
```

You need Rocq with `dune`, a C++23 compiler, and CMake 3.24. raylib is fetched
and built automatically when it is not already installed.

```sh
opam exec -- make extract
cmake -S . -B build/native -DCMAKE_BUILD_TYPE=Release
cmake --build build/native -j8
./build/native/rubik
```

`make extract` runs `dune build native/Extract.vo` and copies the result into
`native/generated/`. Crane is a **vendored dune directory**, so the plugin and
its theories are built in place from the submodule and nothing is ever
installed over your opam switch. WebAssembly is not wired up yet.

`./build/native/rubik --smoke shot.png` runs a scripted self-test: the same
extracted loop, driven from a fixed sequence instead of a keyboard. It
scrambles, searches, plays the solution back, and exits non-zero unless it
ended solved and exported the screenshot.

### Controls

- drag with the mouse to orbit, scroll to zoom, `Home` to recenter
- `U R F D L B` turn a face, with `Shift` for an inverse turn and `Alt` for a
  half turn; the side panel does the same with buttons
- `S` scrambles three turns, `X` resets, `Backspace` undoes one turn
- `[` and `]` change the search allowance
- `Enter` starts or cancels the search, `Space` steps one move, `P` plays back

### About the search allowance

The allowance goes up to twenty moves, which is an allowance and not a promise.
The branching factor is eighteen, so only the first handful of depths return in
interactive time; asking for more than about seven will not finish while you
wait. The search runs as a background job over a copied snapshot, so the view
keeps orbiting regardless, and a cancelled job's result is discarded before it
can reach the screen. Cancelling and quitting both abandon a running search
rather than waiting for it, so neither one blocks.

## Proof guarantees

All proofs are checked by Rocq, with no added axioms, admitted proofs, or
unchecked computation casts.

| Theorem | Guarantee |
| --- | --- |
| `quarter_geometry` | Every sticker follows a clockwise 3D outer-layer rotation. |
| `quarter_four`, `moves_inv` | Four quarter turns are identity; every move has an inverse. |
| `valid_centers` | Legal sequences preserve the solved centers. |
| `solve_sound` | Every returned sequence reaches `init_state`. |
| `solve_complete` | Every valid state receives a solution. |
| `solve_minimal`, `solve_init` | No solving sequence is shorter than the returned sequence. |
| `solve_length` | Returned lengths satisfy the proved finite-state bound. |
| `solve_none` | Unbounded failure is equivalent to physical invalidity. |
| `solve_bounded_spec`, `solve_bounded_none` | Bounded results are shortest; failure excludes every solution within the limit. |
| `colors_roundtrip`, `colors_length` | The viewer’s 54-number snapshot preserves every sticker. |
| `solve_snapshot_correct`, `solve_request_correct` | A reply from the background job decodes to a globally shortest solution of its snapshot. |
| `accepted_solution_solves` | A wrong or stale reply is never installed as a playback plan. |

A shortest path cannot revisit a state. Enumerating the finite sticker type
therefore bounds a shortest solution whenever any solution exists. This proves
termination and completeness without precomputing the cube graph or trusting
a numerical diameter. The build prints the assumptions of the principal
theorems; each reports `Closed under the global context`.

The move tables in [BasicRubik.v](theories/BasicRubik.v) are generated by
[scripts/generate_moves.py](scripts/generate_moves.py). Regenerate them with
`python3 scripts/generate_moves.py`. The generator is not part of the proof
trust boundary: [Geometry.v](theories/Geometry.v) checks the tables against a separate
geometric specification inside Rocq.

## Source documentation and style

Every Rocq declaration has a one- or two-line Rocqdoc comment explaining its
purpose. The source is organized into small thematic sections, with explicit
public types, consistent proof indentation, and one branch per line for
multiline matches. Generated move tables follow the same style.

```sh
opam exec -- make html       # Browse the coqdoc output it points at
python3 scripts/generate_moves.py --check
```

Keep comments focused on intuition, assumptions, or guarantees. Update the
move generator when changing generated code, then run `make check` to verify
both reproducibility and the proofs.

## Migration from the 2×2×2 version

The old seven-corner `State` constructor, nine-move alphabet, packed 63-bit
tables, and 11-move bound have been replaced. `solve` now returns an option so
that invalid sticker assignments have an explicit result. The obsolete
`Rubik63.v` and unbuilt `Solver31.v` implementations have been removed.

The original [paper.pdf](paper.pdf) describes the historical 2×2×2 algorithm;
it does not describe this implementation. Original author: Laurent Théry.
