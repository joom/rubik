"""The cube group, mirroring theories/Cube/CubieDefs.v and Cube/Group.v.

A library for the generators, not a command. It reads the move tables out
of the generated Rocq file, so it cannot drift from what the proofs use.
Rocq rechecks everything the generators produce, so a mistake here cannot
make a proof unsound.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FACES = ["Up", "Right", "Front", "Down", "Left", "Back"]
CORNERS = ["URF", "UFL", "ULB", "UBR", "DFR", "DLF", "DBL", "DRB"]
EDGES = ["UR", "UF", "UL", "UB", "DR", "DF", "DL", "DB", "FR", "FL", "BL", "BR"]
CI = {n: i for i, n in enumerate(CORNERS)}
EI = {n: i for i, n in enumerate(EDGES)}


def quarter_tables():
    """Per face: for each destination slot, (source slot, shift)."""
    text = (ROOT / "theories/Cube/CubieTables.v").read_text()
    body = text[text.index("Definition cquarter"):]
    body = body[:body.index("\n  end.")]
    out = {}
    for i, face in enumerate(FACES):
        start = body.index(f"| {face} =>")
        end = len(body) if i + 1 == len(FACES) else body.index(f"| {FACES[i + 1]} =>")
        chunk = body[start:end]
        cs = [(CI[s], int(k)) for k, s in re.findall(r"cshift T(\d) x(\w+)", chunk)]
        es = [(EI[s], int(k)) for k, s in re.findall(r"eshift F(\d) y(\w+)", chunk)]
        assert len(cs) == 8 and len(es) == 12
        out[face] = (cs, es)
    return out


class Cube:
    """cp[i], co[i] is the piece and twist in corner slot i; ep/eo likewise."""

    __slots__ = ("cp", "co", "ep", "eo")

    def __init__(self, cp, co, ep, eo):
        self.cp, self.co, self.ep, self.eo = list(cp), list(co), list(ep), list(eo)

    def __eq__(self, other):
        return (self.cp, self.co, self.ep, self.eo) == \
               (other.cp, other.co, other.ep, other.eo)


SOLVED = Cube(range(8), [0] * 8, range(12), [0] * 12)


def compose(c, g):
    """ccompose c g: slot X of the result reads slot g.cp[X] of c."""
    return Cube([c.cp[g.cp[i]] for i in range(8)],
                [(c.co[g.cp[i]] + g.co[i]) % 3 for i in range(8)],
                [c.ep[g.ep[i]] for i in range(12)],
                [(c.eo[g.ep[i]] + g.eo[i]) % 2 for i in range(12)])


def _quarter_element(face, tables):
    """The cube one clockwise turn of this face produces from solved."""
    cs, es = tables[face]
    return Cube([s for s, _ in cs], [k for _, k in cs],
                [s for s, _ in es], [k for _, k in es])


def move_elements():
    """The cube each of the eighteen moves denotes, indexed by move code."""
    tables = quarter_tables()
    out = {}
    for fi, face in enumerate(FACES):
        q = _quarter_element(face, tables)
        h = compose(q, q)
        t = compose(h, q)
        out[3 * fi + 0] = q
        out[3 * fi + 1] = h
        out[3 * fi + 2] = t
    return out


MOVES = move_elements()
PHASE2_CODES = [0, 1, 2, 4, 7, 9, 10, 11, 13, 16]


def element(word):
    """The cube a sequence denotes, running left to right from solved."""
    c = SOLVED
    for m in word:
        c = compose(c, MOVES[m])
    return c


def invert_word(word):
    """The sequence that undoes this one."""
    flip = {0: 2, 1: 1, 2: 0}
    return [3 * (m // 3) + flip[m % 3] for m in reversed(word)]


def to_line(mode, c):
    """One cube as a line for the batch solver: a mode letter then twenty slots."""
    parts = [mode]
    for i in range(8):
        parts += [str(c.cp[i]), str(c.co[i])]
    for i in range(12):
        parts += [str(c.ep[i]), str(c.eo[i])]
    return " ".join(parts)


def perm_parity(p):
    """Whether the number of inversions is odd, as theories/Parity.v counts."""
    n = len(p)
    return sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j]) % 2


def assign(free_slots, free_pieces, fixed):
    """Match the free slots to the free pieces, leaving as much alone as
    possible: a slot keeps its own piece whenever that piece is still going."""
    out = dict(fixed)
    slots = [i for i in free_slots if i not in out]
    pieces = [q for q in free_pieces if q not in out.values()]
    keep = [i for i in slots if i in pieces]
    for i in keep:
        out[i] = i
    rest_s = [i for i in slots if i not in out]
    rest_p = [q for q in pieces if q not in out.values()]
    for i, q in zip(rest_s, rest_p):
        out[i] = q
    return out, rest_s


def _fill(n, mapping):
    """A slot-indexed mapping read out as a list."""
    return [mapping[i] for i in range(n)]


def build_corner_element(done_c, done_e, slot, piece, twist, free_edges):
    """A cube fixing the finished slots that brings `piece` home to `slot`.

    Built to disturb as little as possible, so the sequences that realise it
    stay short.
    """
    fixed = {i: i for i in done_c}
    fixed[piece] = slot
    cmap, cspare = assign(range(8), range(8), fixed)
    if len(cmap) != 8:
        return None
    cp = _fill(8, cmap)
    co = [0] * 8
    co[piece] = (3 - twist) % 3
    if co[piece]:
        others = [i for i in range(8) if i not in done_c and i != piece]
        if not others:
            return None
        co[others[0]] = twist % 3
    fixed_e = {j: j for j in done_e}
    emap, espare = assign(range(12), range(12), fixed_e)
    ep = _fill(12, emap)
    eo = [0] * 12
    if perm_parity(cp) ^ perm_parity(ep):
        pool = [j for j in range(12) if j not in done_e] if free_edges else []
        spare = [i for i in range(8) if i not in done_c and i != piece]
        if len(pool) >= 2:
            ep[pool[0]], ep[pool[1]] = ep[pool[1]], ep[pool[0]]
        elif len(spare) >= 2:
            cp[spare[0]], cp[spare[1]] = cp[spare[1]], cp[spare[0]]
        else:
            return None
    return Cube(cp, co, ep, eo)


def build_edge_element(done_c, done_e, slot, piece, flip, pool):
    """The same for an edge slot, with all the corners already finished."""
    if sorted(done_c) != list(range(8)):
        return None
    cp, co = list(range(8)), [0] * 8
    fixed = {j: j for j in done_e}
    fixed[piece] = slot
    emap, espare = assign(pool, pool, fixed)
    for j in range(12):
        emap.setdefault(j, j)
    if sorted(emap.values()) != list(range(12)):
        return None
    ep = _fill(12, emap)
    eo = [0] * 12
    eo[piece] = flip
    if flip:
        others = [j for j in pool if j not in done_e and j != piece]
        if not others:
            return None
        eo[others[0]] ^= 1
    if perm_parity(cp) ^ perm_parity(ep):
        spare = [j for j in pool if j not in done_e and j != piece]
        if len(spare) >= 2:
            ep[spare[0]], ep[spare[1]] = ep[spare[1]], ep[spare[0]]
        else:
            return None
    return Cube(cp, co, ep, eo)


SLICE = [8, 9, 10, 11]


def build_domino_element(done_c, done_e, kind, slot, piece):
    """A cube of allowed moves fixing the finished slots and placing `piece`.

    Inside the subgroup nothing is turned or flipped and the slice edges stay
    in the slice, so only the two rearrangements are free.
    """
    fixed_c = {i: i for i in done_c}
    fixed_e = {j: j for j in done_e}
    if kind == "c":
        fixed_c[piece] = slot
    else:
        fixed_e[piece] = slot
    cmap, _ = assign(range(8), range(8), fixed_c)
    if sorted(cmap.values()) != list(range(8)):
        return None
    cp = _fill(8, cmap)
    emap = dict(fixed_e)
    for pool in (list(range(8)), SLICE):
        part, _ = assign(pool, pool, {j: q for j, q in emap.items() if j in pool})
        emap.update(part)
    if sorted(emap.values()) != list(range(12)):
        return None
    ep = _fill(12, emap)
    if perm_parity(cp) ^ perm_parity(ep):
        for pool in (SLICE, list(range(8))):
            spare = [j for j in pool if j not in done_e and j != piece]
            if len(spare) >= 2:
                ep[spare[0]], ep[spare[1]] = ep[spare[1]], ep[spare[0]]
                break
        else:
            spare = [i for i in range(8) if i not in done_c and i != piece]
            if len(spare) >= 2:
                cp[spare[0]], cp[spare[1]] = cp[spare[1]], cp[spare[0]]
            else:
                return None
    return Cube(cp, [0] * 8, ep, [0] * 12)
