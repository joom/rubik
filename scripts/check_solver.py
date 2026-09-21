#!/usr/bin/env python3
"""Solve random scrambles with the extracted solver and check every answer.

The proofs already say that whatever the solver returns solves the cube it was
given. What they cannot say is that the program in the repository is the one
the proofs are about: extraction, the C++ toolchain and the bindings all sit
outside the kernel. So this runs the built binary on scrambles it has never
seen and multiplies each answer out against the Python cube model, which is
itself read from the generated Rocq tables. A disagreement means something
between the proofs and the executable is broken.
"""

import argparse
import random
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cubelib as L

ROOT = Path(__file__).resolve().parent.parent
SOLVER = ROOT / "build" / "native" / "solve_tool"


def scrambles(count, length, seed, codes):
    """Cubes reached by running random legal sequences from solved."""
    rng = random.Random(seed)
    return [L.element([rng.choice(codes) for _ in range(length)]) for _ in range(count)]


def solve(solver, cubes, mode):
    """Hand every cube to one run of the batch solver, in order."""
    lines = "\n".join(L.to_line(mode, c) for c in cubes) + "\n"
    out = subprocess.run([str(solver)], input=lines, capture_output=True,
                         text=True, check=True).stdout.split("\n")
    while out and not out[-1].strip():
        out.pop()
    if len(out) != len(cubes):
        raise SystemExit(f"solver answered {len(out)} of {len(cubes)} cubes")
    return out


def check(cube, answer, allowed):
    """Run the answer on the cube and say what, if anything, is wrong."""
    if answer.strip() == "FAIL":
        return "no solution returned"
    word = [int(code) for code in answer.split()]
    if any(m not in allowed for m in word):
        return "used a move this phase is not allowed"
    for m in word:
        cube = L.compose(cube, L.MOVES[m])
    return None if cube == L.SOLVED else "the answer does not solve the cube"


def main():
    """Solve a batch in each mode and fail on the first answer that is wrong."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path, default=SOLVER,
                        help="the batch solver to exercise")
    parser.add_argument("--count", type=int, default=5, help="cubes per mode")
    parser.add_argument("--length", type=int, default=25, help="scramble length")
    parser.add_argument("--seed", type=int, default=None,
                        help="fix the scrambles; omit for fresh ones each run")
    args = parser.parse_args()
    if not args.solver.exists():
        raise SystemExit(f"{args.solver} is not built; see the README")

    seed = random.randrange(1 << 30) if args.seed is None else args.seed
    total = 0
    # "F" may use all eighteen moves, "D" only the ten the second phase allows,
    # so the cubes it is given have to be reachable with those ten.
    for mode, codes in [("F", list(range(18))), ("D", L.PHASE2_CODES)]:
        cubes = scrambles(args.count, args.length, seed, codes)
        answers = solve(args.solver, cubes, mode)
        for i, (cube, answer) in enumerate(zip(cubes, answers)):
            wrong = check(cube, answer, codes)
            if wrong:
                print(f"mode {mode}, cube {i} (seed {seed}): {wrong}", file=sys.stderr)
                print(f"  cube:   {L.to_line(mode, cube)}", file=sys.stderr)
                print(f"  answer: {answer}", file=sys.stderr)
                raise SystemExit(1)
            total += 1
        lengths = [len(a.split()) for a in answers]
        print(f"mode {mode}: {len(answers)} solved, "
              f"{min(lengths)}-{max(lengths)} moves")
    print(f"{total} solutions verified against the Python cube model (seed {seed})")


if __name__ == "__main__":
    main()
