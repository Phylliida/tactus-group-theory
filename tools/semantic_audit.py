#!/usr/bin/env python3
"""semantic_audit.py — prototype auditor for semantic rewriting systems.

Python seed of the Phase-2 verified auditor (docs/zfc-group-2-plan.md Part II/V.3).
Checks, per system:
  Law 1  : per-rule affix-disjointness.
  Law 4' : after maximal Tietze elimination of state letters + CYCLIC reduction,
           no surviving relator may be data-only.  (The refined, order-robustified
           survivor check — run under many elimination orders, worst case taken.)
  H1     : abelianization of the surviving presentation; data-only lattice vectors
           reported as INFO (known false positives: doubler a=0, font-copier 2a◦=0,
           blinker 2(a-b)=0 — all sound; see docs Part V).
Validation corpus = every system from the 2026-07-03 session, poisons and cleans.
"""
import random
from itertools import count

# ---------- free group words: tuples of nonzero ints (negative = inverse) ----------

def inv(w):  return tuple(-x for x in reversed(w))

def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x: out.pop()
        else: out.append(x)
    return tuple(out)

def cyc(w):
    w = red(w)
    while len(w) >= 2 and w[0] == -w[-1]: w = w[1:-1]
    return w

def cyckey(w):
    w = cyc(w)
    if not w: return ()
    return min(min(w[k:] + w[:k] for k in range(len(w))),
               min(inv(w)[k:] + inv(w)[:k] for k in range(len(w))))

def subst(w, s, sol):
    out = []
    for x in w:
        if x == s:    out.extend(sol)
        elif x == -s: out.extend(inv(sol))
        else:         out.append(x)
    return red(tuple(out))

# ---------- systems ----------

class System:
    def __init__(self, name, letters, states, rules, expect, whitelist=()):
        self.name = name
        self.ids = {nm: i + 1 for i, nm in enumerate(letters)}
        self.names = {i + 1: nm for i, nm in enumerate(letters)}
        self.states = {self.ids[s] for s in states}
        self.data = {i for i in self.names if i not in self.states}
        self.rules = [(self.word(l), self.word(r)) for l, r in rules]
        self.expect = expect  # 'POISON' or 'CLEAN'
        # declared-semantic data-only relators (collapsed schema tokens), by cyclic key
        self.whitelist = {cyckey(self.word(w)) for w in whitelist}

    def word(self, s):
        out = []
        for tok in s.split():
            neg = tok.startswith('-')
            out.append((-1 if neg else 1) * self.ids[tok.lstrip('-')])
        return tuple(out)

    def show(self, w):
        return '.'.join(('-' if x < 0 else '') + self.names[abs(x)] for x in w) or '1'

# ---------- checks ----------

def law1(sys_):
    bad = []
    for l, r in sys_.rules:
        if l and r and (l[0] == r[0] or l[-1] == r[-1]):
            bad.append((l, r))
        # one-state-per-side
        for side in (l, r):
            if sum(1 for x in side if abs(x) in sys_.states) > 1:
                bad.append((l, r))
    return bad

def eliminate(relators, states, rng):
    rel = [red(r) for r in relators if red(r)]
    states = set(states)
    while True:
        cands = []
        for i, r in enumerate(rel):
            for s in states:
                occ = [j for j, x in enumerate(r) if abs(x) == s]
                if len(occ) == 1:
                    cands.append((i, s, occ[0]))
        if not cands: return rel, states
        i, s, j = rng.choice(cands)
        r = rel[i]
        u, v = r[:j], r[j + 1:]
        sol = red(inv(u) + inv(v)) if r[j] == s else red(v + u)
        rel = [subst(r2, s, sol) for k, r2 in enumerate(rel) if k != i]
        rel = [r3 for r3 in rel if r3]
        states.discard(s)

def law4prime(sys_, tries=40):
    relators = [red(l + inv(r)) for l, r in sys_.rules]
    worst = []
    for t in range(tries):
        rng = random.Random(t)
        surv, _ = eliminate(relators, sys_.states, rng)
        for r in surv:
            c = cyc(r)
            if c and all(abs(x) in sys_.data for x in c) and cyckey(c) not in sys_.whitelist:
                worst.append(c)
    seen, out = set(), []
    for c in worst:
        key = cyckey(c)
        if key not in seen:
            seen.add(key); out.append(c)
    return out

def h1_data_vectors(sys_):
    """Integer-eliminate state coordinates; report data-only lattice vectors (INFO)."""
    relators = [red(l + inv(r)) for l, r in sys_.rules]
    n = len(sys_.names)
    rows = []
    for r in relators:
        v = [0] * (n + 1)
        for x in r: v[abs(x)] += (1 if x > 0 else -1)
        rows.append(v)
    cols = sorted(sys_.states) + sorted(sys_.data)   # states first
    rows = [[r[c] for c in cols] for r in rows]
    ns = len(sys_.states)
    # fraction-free elimination on state columns
    pr = 0
    for c in range(ns):
        piv = next((i for i in range(pr, len(rows)) if rows[i][c] != 0), None)
        if piv is None: continue
        rows[pr], rows[piv] = rows[piv], rows[pr]
        for i in range(len(rows)):
            if i != pr and rows[i][c] != 0:
                a, b = rows[pr][c], rows[i][c]
                rows[i] = [a * y - b * x for x, y in zip(rows[pr], rows[i])]
        pr += 1
    out = []
    dnames = [sys_.names[c] for c in sorted(sys_.data)]
    for i in range(len(rows)):
        if all(rows[i][c] == 0 for c in range(ns)) and any(rows[i][ns:]):
            from math import gcd
            g = 0
            for y in rows[i][ns:]: g = gcd(g, abs(y))
            out.append({dn: y // g for dn, y in zip(dnames, rows[i][ns:]) if y})
    return out

# ---------- the 2026-07-03 corpus ----------

S = []
S.append(System("boolean_collapse", ["t", "b", "n", "m"], [],
    [("n t", "b"), ("n b", "t"), ("m t t", "t"), ("m t b", "b"), ("m b t", "b"), ("m b b", "b")],
    'POISON'))
S.append(System("stationary_pump", ["g", "h", "q", "p"], ["q", "p"],
    [("q", "p g"), ("p", "q h")], 'POISON'))
S.append(System("laundering_eraser", ["st", "s", "s2"], ["s", "s2"],
    [("st s", "s2"), ("st s2", "s")], 'POISON'))
S.append(System("shuttle_builder", ["a", "L", "R", "Lh", "Rh", "g", "g1", "g2", "g3"],
    ["g", "g1", "g2", "g3"],
    [("g R", "a g1 Rh"), ("a g1", "g1 a"), ("L g1", "Lh g2"), ("g2 a", "a g2"),
     ("g2 Rh", "a g3 R"), ("a g3", "g3 a"), ("Lh g3", "L g"), ("g a", "a g")], 'POISON'))
S.append(System("m1_guard", ["gg", "nn", "a", "b"], ["gg"], [("gg nn", "nn gg")], 'CLEAN'))
S.append(System("m2_translate", ["a", "b", "q", "qp"], ["q", "qp"], [("q a", "b qp")], 'CLEAN'))
S.append(System("m3_blinker", ["a", "b", "q", "qp"], ["q", "qp"],
    [("q a", "b qp"), ("qp a", "b q")], 'CLEAN'))
S.append(System("m4_mixed", ["a", "b", "q", "qp"], ["q", "qp"],
    [("q a", "b qp"), ("qp b", "a q")], 'CLEAN'))
S.append(System("m5_doubler", ["a", "q"], ["q"], [("q a", "a a q")], 'CLEAN'))
S.append(System("m5_ratio_bs23", ["a", "q"], ["q"], [("q a a", "a a a q")], 'CLEAN'))
S.append(System("m5_mint_motion", ["a", "b", "gg", "q"], ["q"], [("q a", "gg b q")], 'CLEAN'))
S.append(System("m5p_shuttle", ["a", "b", "q", "r"], ["q", "r"],
    [("q a", "b q"), ("a r", "r b")], 'CLEAN'))
S.append(System("m6_courier", ["a", "w", "q", "p"], ["q", "p"],
    [("q a", "p"), ("p w", "w p")], 'CLEAN'))
S.append(System("m7_ratio_pair", ["a", "b", "q", "r"], ["q", "r"],
    [("q a", "b q"), ("r a", "b b r")], 'CLEAN'))
S.append(System("m7_twin_blinkers", ["a", "b", "q", "qp", "r", "rp"], ["q", "qp", "r", "rp"],
    [("q a", "b qp"), ("qp a", "b q"), ("r a", "b rp"), ("rp a", "b r")], 'CLEAN'))
S.append(System("font_copier_core", ["a", "am", "ac", "F", "Fp", "D", "Dh", "h", "d", "d1", "c", "c2"],
    ["h", "d", "d1", "c", "c2"],
    [("h F", "F d"), ("d a", "a am d1"), ("am d1", "c"), ("c Fp", "Fp c"),
     ("c D", "ac Dh c2"), ("c Dh", "ac D c2"), ("Fp c2", "c2 Fp"), ("a c2", "c2 a"),
     ("F c2", "h F")], 'CLEAN'))

S.append(System("s9_zero_consume_AS_WRITTEN_A4",
    ["x1", "x2", "Oh", "Ok", "z", "z1"], ["z", "z1"],
    [("x1 z", "z1"), ("x2 z", "z1"), ("z1 Oh", "Ok z"), ("z1 Ok", "Oh z")],
    'POISON'))
S.append(System("s9_fixed_peel_pair_deposit",
    ["x1", "x2", "g1", "g2", "z", "zp"], ["z", "zp"],
    [("z x1", "g1 g1 zp"), ("zp x1", "g1 g1 z"),
     ("z x2", "g2 g2 zp"), ("zp x2", "g2 g2 z")],
    'CLEAN'))

S.append(System("s7_erase_pair_quartet", ["st", "P", "e", "e1", "e3", "e4"],
    ["e", "e1", "e3", "e4"],
    [("st e", "e1"), ("e1 P", "P e3"), ("e3 st", "e4"), ("P e4", "e P")], 'CLEAN'))
S.append(System("s6_zigzag_comparator", ["st", "sm", "A", "k", "k1", "k2", "k3"],
    ["k", "k1", "k2", "k3"],
    [("st k", "k1 sm"), ("k1 A", "A k2"), ("k2 st", "sm k3"),
     ("sm k3", "k3 sm"), ("A k3", "k A"), ("sm k", "k sm")], 'CLEAN'))
S.append(System("unit_sweep_raw", ["br", "cb", "M", "one", "u", "w", "w1"],
    ["w", "w1"],
    [("w br M one", "w1"), ("w1 u", "u w1"), ("w1 cb", "w")], 'POISON'))
S.append(System("unit_sweep_whitelisted", ["br", "cb", "M", "one", "u", "w", "w1"],
    ["w", "w1"],
    [("w br M one", "w1"), ("w1 u", "u w1"), ("w1 cb", "w")], 'CLEAN',
    whitelist=["br M one cb"]))

# ---------- run ----------

if __name__ == "__main__":
    fails = 0
    for sys_ in S:
        l1 = law1(sys_)
        poison = law4prime(sys_)
        h1 = h1_data_vectors(sys_)
        verdict = 'POISON' if poison else 'CLEAN'
        ok = (verdict == sys_.expect)
        fails += (not ok)
        print(f"=== {sys_.name}  [{verdict}]  expected {sys_.expect}  {'OK' if ok else '** MISMATCH **'}")
        if l1:     print(f"    Law1 violations: {len(l1)}")
        for c in poison[:4]:
            print(f"    data-only survivor: {sys_.show(c)}")
        for v in h1:
            print(f"    H1 data vector (INFO): {v}")
    print(f"\n{'ALL EXPECTATIONS MET' if fails == 0 else f'{fails} MISMATCHES'}")
