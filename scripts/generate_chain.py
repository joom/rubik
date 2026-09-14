#!/usr/bin/env python3
"""Generate the word tables the solving chains use.

The chain finishes one slot at a time. At each stage it needs, for every
reading the slot might show, a sequence that brings that slot home and leaves
the finished ones alone. Those sequences are found here by solving cubes with
the extracted solver, so this script needs `build/native/solve_tool`.

Two chains are produced: theories/ChainTables.v with all eighteen moves, and
theories/DominoTables.v with only the ten the second phase may use.

Nothing printed here is trusted. Every entry is rechecked inside Rocq by
computing what its sequence denotes, so a wrong table fails to compile rather
than proving anything false.
"""

import argparse
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cubelib as L

ROOT = Path(__file__).resolve().parent.parent
TOOL = ROOT / "build/native/solve_tool"

AMOUNTS = ["CW", "Half", "CCW"]
FACE_NAMES = ["Up", "Right", "Front", "Down", "Left", "Back"]
TWISTS = ["T0", "T1", "T2"]
FLIPS = ["F0", "F1"]


def word_text(w):
    return "[" + "; ".join(f"({FACE_NAMES[m // 3]}, {AMOUNTS[m % 3]})" for m in w) + "]"


def rocq_list(xs):
    return "[" + "; ".join(xs) + "]"


def solve(mode, elements):
    """One sequence per cube, from the extracted solver, checked on the way."""
    if not TOOL.exists():
        raise SystemExit(f"{TOOL} is missing; build it with "
                         "'cmake --build build/native --target solve_tool'")
    payload = "\n".join(L.to_line(mode, h) for h in elements) + "\n"
    out = subprocess.run([str(TOOL)], input=payload, capture_output=True, text=True)
    lines = out.stdout.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    if len(lines) != len(elements):
        raise SystemExit(f"solver answered {len(lines)} of {len(elements)} cubes")
    words = []
    for h, line in zip(elements, lines):
        if line.strip() == "FAIL":
            raise SystemExit("solver gave up on a cube")
        p = [int(x) for x in line.split()] if line.strip() else []
        w = L.invert_word(p)
        if L.element(w) != h:
            raise SystemExit("solver answer does not rebuild the cube")
        if mode == "D" and not all(m in L.PHASE2_CODES for m in w):
            raise SystemExit("solver used a move the second phase may not")
        words.append(w)
    return words


def render_table(name, kind, entries):
    rows = []
    for piece, orient, w in entries:
        if kind == "c":
            key = f"({L.CORNERS[piece]}, {TWISTS[orient]})"
        else:
            key = f"({L.EDGES[piece]}, {FLIPS[orient]})"
        rows.append(f"   ({key}, {word_text(w)})")
    kindname = "ctable" if kind == "c" else "etable"
    return f"Definition {name} : {kindname} :=\n  [" + ";\n".join(rows).lstrip() + "].\n"


def full_chain():
    """The eighteen-move chain: seven corner stages then eleven edge ones."""
    stages = []
    for k in range(7):
        done = list(range(k))
        rows = [(p, t) for p in range(8) if p not in done for t in range(3)]
        stages.append(("c", k, done, [], rows))
    for j in range(11):
        done = list(range(j))
        rows = [(p, f) for p in range(12) if p not in done for f in range(2)]
        stages.append(("e", j, list(range(8)), done, rows))
    jobs, index = [], []
    for kind, slot, done_c, done_e, rows in stages:
        for piece, orient in rows:
            if kind == "c":
                h = L.build_corner_element(done_c, done_e, slot, piece, orient, True)
            else:
                h = L.build_edge_element(done_c, done_e, slot, piece, orient,
                                         list(range(12)))
            if h is None:
                assert kind == "e" and slot == 10 and piece == 11
                continue
            jobs.append(h)
            index.append((kind, slot, piece, orient))
    return jobs, index


def domino_chain():
    """The ten-move chain: corners, then the eight outer edges, then the slice."""
    stages = []
    for k in range(7):
        stages.append(("c", k, list(range(k)), [], [p for p in range(8) if p >= k]))
    for j in range(7):
        stages.append(("e", j, list(range(8)), list(range(j)),
                       [p for p in range(8) if p >= j]))
    for j in (8, 9):
        done = list(range(8)) + list(range(8, j))
        stages.append(("e", j, list(range(8)), done,
                       [p for p in L.SLICE if p not in done]))
    jobs, index = [], []
    for kind, slot, done_c, done_e, rows in stages:
        for piece in rows:
            h = L.build_domino_element(done_c, done_e, kind, slot, piece)
            assert h is not None, (kind, slot, piece)
            jobs.append(h)
            index.append((kind, slot, piece, 0))
    return jobs, index


def group(index, words):
    out = {}
    for (kind, slot, piece, orient), w in zip(index, words):
        out.setdefault((kind, slot), []).append((piece, orient, w))
    return out


FULL_HEADER = '''(* Generated by scripts/generate_chain.py. Do not edit: run the script.
   The sequences were found by solving cubes with the extracted solver. None
   of that is trusted: every entry is rechecked below by computing what its
   sequence denotes, so a wrong table fails to compile rather than proving
   anything false. *)

From Stdlib Require Import Arith List Lia.
From Rubik Require Export Chain.
Import ListNotations.

(** * Tables for solving with all eighteen moves

    One table per slot, in the order the chain finishes them: seven corners,
    then eleven edges. The eighth corner and the twelfth edge have no table;
    what they must hold is forced. *)

'''

DOMINO_HEADER = '''(* Generated by scripts/generate_chain.py. Do not edit: run the script.
   As in ChainTables.v, every entry is rechecked below, including that its
   sequence uses only moves the second phase may make. *)

From Stdlib Require Import Arith List Lia.
From Rubik Require Export Domino.
Import ListNotations.

(** * Tables for solving inside the subgroup

    Seven corner stages, then seven for the outer edges, then two for the
    slice. The eighth corner, the eighth outer edge and the last two slice
    edges have no table; what they must hold is forced. *)

'''


def emit_full(groups):
    bounds = {k: max(len(w) for _, _, w in v) for k, v in groups.items()}
    body = "\n".join(render_table(f"{kind}tab_{slot}", kind, entries)
                     for (kind, slot), entries in sorted(groups.items())) + "\n"
    cstages = "; ".join(f"Cstage {L.CORNERS[k]} ctab_{k} {bounds[('c', k)]}"
                        for k in range(7))
    estages = "; ".join(f"Estage {L.EDGES[j]} etab_{j} {bounds[('e', j)]}"
                        for j in range(10))
    total = (sum(bounds[("c", k)] for k in range(7)) +
             sum(bounds[("e", j)] for j in range(10)) + bounds[("e", 10)])
    edone = rocq_list(list(reversed(L.EDGES[:10])))
    body += f'''(** The stages in the order they run. *)
Definition corner_stages : list stage := [{cstages}].
Definition edge_stages : list stage := [{estages}].

(** The tables answer for every reading still possible, leave the finished
    slots alone, and bring their own slot home. *)
Lemma corner_stages_ok : chain_ok [] [] corner_stages = true.
Proof. vm_compute; reflexivity. Qed.

Lemma corner_stages_slots :
  stagesc corner_stages = {rocq_list(list(reversed(L.CORNERS[:7])))}.
Proof. vm_compute; reflexivity. Qed.

Lemma edge_stages_ok : chain_ok all_corner_slots [] edge_stages = true.
Proof. vm_compute; reflexivity. Qed.

Lemma edge_stages_slots : stagese edge_stages = {edone}.
Proof. vm_compute; reflexivity. Qed.

Lemma edge_stages_corners : stagesc edge_stages = [].
Proof. vm_compute; reflexivity. Qed.

(** The eleventh edge holds its own piece, so its table answers only for the
    two flips it can show. *)
Lemma etab_10_ok : etable_ok etab_10 all_corner_slots {edone} BL = true.
Proof. vm_compute; reflexivity. Qed.

Lemma etab_10_covers_0 : ecovers etab_10 (BL, F0) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma etab_10_covers_1 : ecovers etab_10 (BL, F1) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma etab_10_bounded : etable_bounded etab_10 {bounds[("e", 10)]} = true.
Proof. vm_compute; reflexivity. Qed.

(** The longest answer the tables allow, added up over the stages. *)
Definition full_bound : nat := {total}.

Lemma full_bound_ok :
  {bounds[("e", 10)]} + (chain_bound edge_stages + chain_bound corner_stages)
  = full_bound.
Proof. vm_compute; reflexivity. Qed.
'''
    return FULL_HEADER + body


def emit_domino(groups):
    bounds = {k: max(len(w) for _, _, w in v) for k, v in groups.items()}
    body = "\n".join(render_table(f"d{kind}tab_{slot}", kind, entries)
                     for (kind, slot), entries in sorted(groups.items())) + "\n"
    cstages = "; ".join(f"Cstage {L.CORNERS[k]} dctab_{k} {bounds[('c', k)]}"
                        for k in range(7))
    ustages = "; ".join(f"Estage {L.EDGES[j]} detab_{j} {bounds[('e', j)]}"
                        for j in range(7))
    sstages = "; ".join(f"Estage {L.EDGES[j]} detab_{j} {bounds[('e', j)]}"
                        for j in (8, 9))
    total = (sum(bounds[("c", k)] for k in range(7)) +
             sum(bounds[("e", j)] for j in range(7)) +
             sum(bounds[("e", j)] for j in (8, 9)))
    udone = rocq_list([L.EDGES[7]] + list(reversed(L.EDGES[:7])))
    body += f'''(** The stages in the order they run. *)
Definition dcorner_stages : list stage := [{cstages}].
Definition dud_stages : list stage := [{ustages}].
Definition dslice_stages : list stage := [{sstages}].

(** The eight outer edge slots, once they are all finished. *)
Definition ud_done : list edge := {udone}.

Lemma dcorner_stages_ok : chain2_ok [] [] dcorner_stages = true.
Proof. vm_compute; reflexivity. Qed.

Lemma dcorner_stages_slots :
  stagesc dcorner_stages = {rocq_list(list(reversed(L.CORNERS[:7])))}.
Proof. vm_compute; reflexivity. Qed.

Lemma dud_stages_ok : chain2_ok all_corner_slots [] dud_stages = true.
Proof. vm_compute; reflexivity. Qed.

Lemma dud_stages_slots : stagese dud_stages = {rocq_list(list(reversed(L.EDGES[:7])))}.
Proof. vm_compute; reflexivity. Qed.

Lemma dud_stages_corners : stagesc dud_stages = [].
Proof. vm_compute; reflexivity. Qed.

Lemma dslice_stages_ok : chain2_ok all_corner_slots ud_done dslice_stages = true.
Proof. vm_compute; reflexivity. Qed.

Lemma dslice_stages_slots :
  stagese dslice_stages = {rocq_list([L.EDGES[9], L.EDGES[8]])}.
Proof. vm_compute; reflexivity. Qed.

Lemma dslice_stages_corners : stagesc dslice_stages = [].
Proof. vm_compute; reflexivity. Qed.

(** The longest answer the tables allow, added up over the stages. *)
Definition domino_bound : nat := {total}.

Lemma domino_bound_ok :
  chain_bound dslice_stages + (chain_bound dud_stages + chain_bound dcorner_stages)
  = domino_bound.
Proof. vm_compute; reflexivity. Qed.
'''
    return DOMINO_HEADER + body


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    jobs, index = full_chain()
    (ROOT / "theories/ChainTables.v").write_text(emit_full(group(index, solve("F", jobs))))
    jobs, index = domino_chain()
    (ROOT / "theories/DominoTables.v").write_text(
        emit_domino(group(index, solve("D", jobs))))


if __name__ == "__main__":
    main()
