#!/usr/bin/env python3
"""Generate the word tables the solving chains use.

The chain finishes one slot at a time. At each stage it needs, for every
reading the slot might show, a sequence that brings that slot home and leaves
the finished ones alone. Those sequences are found here by solving cubes with
the extracted solver, so this script needs `build/native/solve_tool`.

Two chains are produced: ChainTables.v with all eighteen moves, and
DominoTables.v with only the ten the second phase may use, both under
theories/Bounds/.

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
TWISTS = ["T0", "T1", "T2"]
FLIPS = ["F0", "F1"]


FACE_NAMES = ["Up", "Right", "Front", "Down", "Left", "Back"]


def word_text(word):
    """A move sequence as a Rocq list of (face, amount) pairs."""
    return rocq_list(f"({FACE_NAMES[m // 3]}, {AMOUNTS[m % 3]})" for m in word)


def rocq_list(items):
    """Any sequence of already-rendered terms as a Rocq list."""
    return "[" + "; ".join(items) + "]"


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


def table_name(kind, slot, domino):
    """The Rocq name of one stage's table."""
    what = L.CORNERS[slot].lower() if kind == "c" else L.EDGES[slot].lower()
    return ("domino_" if domino else "") + f"{what}_table"


def table_comment(kind, slot, done_c, done_e):
    """One line saying which slot this table finishes and what is behind it."""
    what = L.CORNERS[slot] if kind == "c" else L.EDGES[slot]
    if kind == "c":
        behind = "nothing else finished" if not done_c else \
            f"{len(done_c)} corners already finished"
    else:
        behind = ("all eight corners" if not done_e else
                  f"all eight corners and {len(done_e)} edges") + " already finished"
    return f"(** Finishing the {what} slot, with {behind}. *)"


def render_table(name, kind, entries, comment):
    """One stage's table as a Rocq definition, keyed by the reading it answers."""
    rows = []
    for piece, orient, w in entries:
        if kind == "c":
            key = f"({L.CORNERS[piece]}, {TWISTS[orient]})"
        else:
            key = f"({L.EDGES[piece]}, {FLIPS[orient]})"
        rows.append(f"   ({key}, {word_text(w)})")
    kindname = "corner_table" if kind == "c" else "edge_table"
    return (comment + f"\nDefinition {name} : {kindname} :=\n  ["
            + ";\n".join(rows).lstrip() + "].\n")


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
    """Collect the solved sequences back into one list per stage."""
    out = {}
    for (kind, slot, piece, orient), w in zip(index, words):
        out.setdefault((kind, slot), []).append((piece, orient, w))
    return out


def done_sets(kind, slot):
    """What a stage may assume is already finished when it runs."""
    if kind == "c":
        return list(range(slot)), []
    return list(range(8)), list(range(slot))


FULL_HEADER = '''(* Generated by scripts/generate_chain.py. Do not edit: run the script.
   The sequences were found by solving cubes with the extracted solver. None
   of that is trusted: every entry is rechecked below by computing what its
   sequence denotes, so a wrong table fails to compile rather than proving
   anything false. *)

From Stdlib Require Import Arith List Lia.
From Rubik Require Export Bounds.Chain.
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
From Rubik Require Export Bounds.Domino.
Import ListNotations.

(** * Tables for solving inside the subgroup

    Seven corner stages, then seven for the outer edges, then two for the
    slice. The eighth corner, the eighth outer edge and the last two slice
    edges have no table; what they must hold is forced. *)

'''


def emit_full(groups):
    """The whole eighteen-move module: tables, stages, checks and bound."""
    bounds = {k: max(len(w) for _, _, w in v) for k, v in groups.items()}
    body = "\n".join(
        render_table(table_name(kind, slot, False), kind, entries,
                     table_comment(kind, slot, *done_sets(kind, slot)))
        for (kind, slot), entries in sorted(groups.items())) + "\n"
    cstages = "; ".join(f"CornerStage {L.CORNERS[k]} {table_name('c', k, False)} {bounds[('c', k)]}"
                        for k in range(7))
    estages = "; ".join(f"EdgeStage {L.EDGES[j]} {table_name('e', j, False)} {bounds[('e', j)]}"
                        for j in range(10))
    total = (sum(bounds[("c", k)] for k in range(7)) +
             sum(bounds[("e", j)] for j in range(10)) + bounds[("e", 10)])
    edone = rocq_list(list(reversed(L.EDGES[:10])))
    body += f'''(** The stages in the order they run. *)
(** The corner stages in the order they run. *)
Definition corner_stages : list stage := [{cstages}].
(** And the edge stages. *)
Definition edge_stages : list stage := [{estages}].

(** The tables answer for every reading still possible, leave the finished
    slots alone, and bring their own slot home. *)
Lemma corner_stages_ok : chain_ok plain [] [] corner_stages = true.
Proof. vm_compute; reflexivity. Qed.

(** The corner slots they finish, newest first. *)
Lemma corner_stages_slots :
  stage_corners corner_stages = {rocq_list(list(reversed(L.CORNERS[:7])))}.
Proof. vm_compute; reflexivity. Qed.

(** The edge stages check out too, given the corners are done. *)
Lemma edge_stages_ok : chain_ok plain all_corner_slots [] edge_stages = true.
Proof. vm_compute; reflexivity. Qed.

(** The edge slots they finish, newest first. *)
Lemma edge_stages_slots : stage_edges edge_stages = {edone}.
Proof. vm_compute; reflexivity. Qed.

(** They finish no corner slot. *)
Lemma edge_stages_corners : stage_corners edge_stages = [].
Proof. vm_compute; reflexivity. Qed.

(** The eleventh edge holds its own piece, so its table answers only for the
    two flips it can show. *)
Lemma bl_table_ok : edge_table_ok bl_table all_corner_slots {edone} BL = true.
Proof. vm_compute; reflexivity. Qed.

(** It answers when that edge is unflipped, *)
Lemma bl_table_covers_0 : edge_covers bl_table (BL, F0) = true.
Proof. vm_compute; reflexivity. Qed.

(** and when it is flipped. *)
Lemma bl_table_covers_1 : edge_covers bl_table (BL, F1) = true.
Proof. vm_compute; reflexivity. Qed.

(** And its answers are short. *)
Lemma bl_table_bounded : edge_table_bounded bl_table {bounds[("e", 10)]} = true.
Proof. vm_compute; reflexivity. Qed.

(** The longest answer the tables allow, added up over the stages. *)
Definition full_bound : nat := {total}.

(** Which is what the stages add up to. *)
Lemma full_bound_ok :
  {bounds[("e", 10)]} + (chain_bound edge_stages + chain_bound corner_stages)
  = full_bound.
Proof. vm_compute; reflexivity. Qed.
'''
    return FULL_HEADER + body


def emit_domino(groups):
    """The same for the ten-move module."""
    bounds = {k: max(len(w) for _, _, w in v) for k, v in groups.items()}
    body = "\n".join(
        render_table(table_name(kind, slot, True), kind, entries,
                     table_comment(kind, slot, *done_sets(kind, slot)))
        for (kind, slot), entries in sorted(groups.items())) + "\n"
    cstages = "; ".join(f"CornerStage {L.CORNERS[k]} {table_name('c', k, True)} {bounds[('c', k)]}"
                        for k in range(7))
    ustages = "; ".join(f"EdgeStage {L.EDGES[j]} {table_name('e', j, True)} {bounds[('e', j)]}"
                        for j in range(7))
    sstages = "; ".join(f"EdgeStage {L.EDGES[j]} {table_name('e', j, True)} {bounds[('e', j)]}"
                        for j in (8, 9))
    total = (sum(bounds[("c", k)] for k in range(7)) +
             sum(bounds[("e", j)] for j in range(7)) +
             sum(bounds[("e", j)] for j in (8, 9)))
    udone = rocq_list([L.EDGES[7]] + list(reversed(L.EDGES[:7])))
    body += f'''(** The stages in the order they run. *)
Definition dcorner_stages : list stage := [{cstages}].
(** The outer edge stages. *)
Definition dud_stages : list stage := [{ustages}].
(** And the slice stages. *)
Definition dslice_stages : list stage := [{sstages}].

(** The eight outer edge slots, once they are all finished. *)
Definition ud_done : list edge := {udone}.

(** The corner stages check out. *)
Lemma dcorner_stages_ok : chain_ok restricted [] [] dcorner_stages = true.
Proof. vm_compute; reflexivity. Qed.

(** The corner slots they finish, newest first. *)
Lemma dcorner_stages_slots :
  stage_corners dcorner_stages = {rocq_list(list(reversed(L.CORNERS[:7])))}.
Proof. vm_compute; reflexivity. Qed.

(** The outer edge stages check out, given the corners are finished. *)
Lemma dud_stages_ok : chain_ok restricted all_corner_slots [] dud_stages = true.
Proof. vm_compute; reflexivity. Qed.

(** The outer edge slots they finish, and no corner slot. *)
Lemma dud_stages_slots : stage_edges dud_stages = {rocq_list(list(reversed(L.EDGES[:7])))}.
Proof. vm_compute; reflexivity. Qed.

(** They finish no corner slot. *)
Lemma dud_stages_corners : stage_corners dud_stages = [].
Proof. vm_compute; reflexivity. Qed.

(** And the slice stages, given the outer edges are finished. *)
Lemma dslice_stages_ok : chain_ok restricted all_corner_slots ud_done dslice_stages = true.
Proof. vm_compute; reflexivity. Qed.

(** The slice slots they finish, and no corner slot. *)
Lemma dslice_stages_slots :
  stage_edges dslice_stages = {rocq_list([L.EDGES[9], L.EDGES[8]])}.
Proof. vm_compute; reflexivity. Qed.

(** They finish no corner slot either. *)
Lemma dslice_stages_corners : stage_corners dslice_stages = [].
Proof. vm_compute; reflexivity. Qed.

(** The longest answer the tables allow, added up over the stages. *)
Definition domino_bound : nat := {total}.

(** Which is what the stages add up to. *)
Lemma domino_bound_ok :
  chain_bound dslice_stages + (chain_bound dud_stages + chain_bound dcorner_stages)
  = domino_bound.
Proof. vm_compute; reflexivity. Qed.
'''
    return DOMINO_HEADER + body


def main():
    """Rewrite both targets, or check that the checked-in ones match."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="fail if the checked-in tables are stale")
    args = parser.parse_args()
    jobs, index = full_chain()
    written = {"theories/Bounds/ChainTables.v": emit_full(group(index, solve("F", jobs)))}
    jobs, index = domino_chain()
    written["theories/Bounds/DominoTables.v"] = emit_domino(group(index, solve("D", jobs)))
    for target, text in written.items():
        path = ROOT / target
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f"{target} is stale; run scripts/generate_chain.py")
        else:
            path.write_text(text)


if __name__ == "__main__":
    main()
