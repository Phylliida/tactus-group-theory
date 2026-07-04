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
    def __init__(self, name, letters, states, rules, expect, whitelist=(), transient=()):
        self.name = name
        self.ids = {nm: i + 1 for i, nm in enumerate(letters)}
        self.names = {i + 1: nm for i, nm in enumerate(letters)}
        self.states = {self.ids[s] for s in states}
        self.data = {i for i in self.names if i not in self.states}
        self.rules = [(self.word(l), self.word(r)) for l, r in rules]
        self.expect = expect  # 'POISON' or 'CLEAN'
        # declared-semantic data-only relators (collapsed schema tokens), by cyclic key
        self.whitelist = {cyckey(self.word(w)) for w in whitelist}
        # transient letters (marks/flavors/walls, never in canonical codes): data-only
        # survivors composed PURELY of transient letters are WARN, not POISON
        self.transient = {self.ids[t] for t in transient}

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

def conj_resolutions(sys_, surv):
    """Resolve pairs of survivors of shape s·A·s⁻¹·B (same state s, same core A):
    derive B₁·B₂⁻¹ — the consequence-combination step Tietze alone misses
    (the mechanism behind the shuttle's a²=1 and deposit-order torsion)."""
    derived, seen = [], {}
    for r in surv:
        c = cyc(r); n = len(c)
        for i in range(n):
            s = c[i]
            if abs(s) not in sys_.states or s < 0: continue
            for j in range(n):
                if i == j or c[j] != -s: continue
                A = tuple(c[(i + 1 + t) % n] for t in range((j - i - 1) % n))
                B = tuple(c[(j + 1 + t) % n] for t in range((i - j - 1) % n))
                if any(abs(x) == abs(s) for x in A): continue
                key = (abs(s), red(A))
                val = red(inv(B))                    # s·A·s⁻¹ = B⁻¹
                if key in seen:
                    if seen[key] != val:
                        derived.append(red(seen[key] + inv(val)))
                else:
                    seen[key] = val
    return derived

def _pos_pair_split(c):
    """If cyclically-reduced c has a rotation of sign-form (+...+)(-...-), return (P, N)
    with P, N positive words and the relator meaning P = N.  Else None.  (A cancellation
    product of two positive tokens is always P·N^-1 for positive P,N by construction; this
    recovers the readable positive PAIR.)"""
    c = cyc(c)
    if not c: return None
    n = len(c)
    for k in range(n):
        rot = c[k:] + c[:k]
        signs = [x > 0 for x in rot]
        if any(signs) and any(not s for s in signs) \
           and all(signs[:signs.index(False)]) and not any(signs[signs.index(False):]):
            P = tuple(rot[:signs.index(False)])
            N = tuple(-x for x in reversed(rot[signs.index(False):]))
            return (P, N)
    return None

def token_interaction_probe(whitelist_words):
    """Consequence-closure candidates for the whitelist (Law P', law-p-prime.md §7).
    whitelist_words: list of int-tuples (positive token words, each ε-trivial in G).
    Cancel every ORDERED pair of tokens at every cyclic alignment; keep the products that are
    GENUINE TWO-SIDED positive pairs (P = N, both nonempty) — the readable derived tokens each
    owing a witness.  (NOT a length filter: the derived relator can equal parent length, e.g.
    M1 = X0.  Corrected 2026-07-04 after the length-filter missed exactly that.)
    Returns {cyckey(P·N^-1): (P, N)}."""
    toks = [red(w) for w in whitelist_words if red(w)]
    parents = {cyckey(w) for w in toks}
    found = {}
    for a in toks:
        for b in toks:
            for s in range(len(a)):
                for t in range(len(b)):
                    c = red((a[s:] + a[:s]) + inv(b[t:] + b[:t]))
                    pn = _pos_pair_split(c)
                    if pn is None: continue
                    P, N = pn
                    key = cyckey(red(P + inv(N)))
                    if key and key not in parents:
                        found.setdefault(key, (P, N))
    return found

def law4prime(sys_, tries=40, return_warns=False):
    relators = [red(l + inv(r)) for l, r in sys_.rules]
    worst, warns = [], []
    for t in range(tries):
        rng = random.Random(t)
        surv, _ = eliminate(relators, sys_.states, rng)
        for r in list(surv) + conj_resolutions(sys_, surv):
            c = cyc(r)
            if c and all(abs(x) in sys_.data for x in c) and cyckey(c) not in sys_.whitelist:
                if sys_.transient and any(abs(x) in sys_.transient for x in c):
                    warns.append(c)      # transient-only OR mixed: tiered warns, not auto-poison
                else:
                    worst.append(c)      # PURE-CODE data survivor: definite poison
    seen, out = set(), []
    for c in worst:
        key = cyckey(c)
        if key not in seen:
            seen.add(key); out.append(c)
    if return_warns:
        wseen, wout = set(), []
        for c in warns:
            k = cyckey(c)
            if k not in wseen: wseen.add(k); wout.append(c)
        return out, wout
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

S.append(System("pass1_swap_core",
    ["Hm", "br", "cb", "cbm", "M", "X", "u", "tri", "H", "D", "D1", "D2", "D3"],
    ["H", "D", "D1", "D2", "D3"],
    [("H br M br X", "br X br M D"), ("D", "tri D1"), ("D1 u", "u D1"),
     ("D1 cb", "cbm D2"), ("u D2", "D2 u"), ("tri D2", "D3"),
     ("M D3", "D3 M"), ("X D3", "D3 X"), ("br D3", "D3 br"), ("Hm D3", "H Hm")],
    'CLEAN'))
S.append(System("pass1_dup_courier_SPEC_order",
    ["c", "cm", "cc", "cc2", "tri", "P", "mk", "dp", "k", "g2", "un"],
    ["mk", "dp", "k", "g2", "un"],
    [("mk c", "cm mk"), ("dp cm", "cm cc dp"), ("g2 cc", "k"),
     ("cm k", "k cm"), ("P k", "k P"),
     ("tri k", "cc2 tri g2"),                       # deposit BEFORE ▲ (S4 spec order)
     ("g2 P", "P g2"), ("g2 cm", "cm g2"), ("un cm", "c un")],
    'CLEAN'))
S.append(System("pass1_deposit_WRONG_order",
    ["cc", "cc2", "tri", "trib", "P", "k", "g2"],
    ["k", "g2"],
    [("g2 cc", "k"), ("P k", "k P"), ("g2 P", "P g2"),
     ("tri k", "trib cc2 g2"),                      # deposit AFTER the flipped wall
     ("trib k", "tri cc2 g2")],
    'POISON'))

S.append(System("s3_restart_flip_SHARED_states",
    ["brf", "brg", "cb", "cbm", "m1", "m3"], ["m1", "m3"],
    [("m1 cb", "cbm m3"), ("brf m3", "brg m1"), ("brg m3", "brf m1")], 'POISON'))
S.append(System("s3_restart_flip_PARITY_states",
    ["brf", "brg", "cb", "cbm", "m1a", "m3a", "m1b", "m3b"],
    ["m1a", "m3a", "m1b", "m3b"],
    [("m1a cb", "cbm m3a"), ("brf m3a", "brg m1b"),
     ("m1b cb", "cbm m3b"), ("brg m3b", "brf m1a")], 'CLEAN'))
S.append(System("pass3_spine_advance",
    ["br", "brm", "M", "Mm", "P", "ke", "ke1"], ["ke", "ke1"],
    [("ke br M", "brm Mm ke1"), ("ke1 P", "P ke1"), ("ke1 br M", "brm Mm ke"),
     ("ke P", "P ke")], 'CLEAN'))

S.append(System("pico_shield_lifecycle",
    ["F", "Fp", "a", "am", "ac", "Al", "Al2", "Lb", "Rb", "Rbh", "T", "P",
     "h", "d", "d1", "c", "c2", "k", "g", "e", "e1", "g2", "g3"],
    ["h", "d", "d1", "c", "c2", "k", "g", "e", "e1", "g2", "g3"],
    [("h F", "F d"), ("d a", "a am d1"), ("am d1", "c"),          # builder: dup at font
     ("c Fp", "Fp c"), ("c Lb", "Lb c"),                          # carry into yard
     ("c Rb", "ac Rb c2"),                                        # yard deposit (single rule)
     ("Lb c2", "c2 Lb"), ("Fp c2", "c2 Fp"), ("a c2", "c2 a"),
     ("F c2", "h F"),                                             # builder cycle closes
     ("k ac", "Al g"),                                            # verify: re-flavor, hand off
     ("g Al", "e"),                                               # export pickup
     ("e Rb", "Rbh e1"),                                          # out-cross, wall flips
     ("e1 P", "P e1"), ("e1 T", "Al2 T g2"),                      # store deposit (single rule)
     ("P g2", "g2 P"), ("Rbh g2", "g3 Rb"),                       # in-cross, wall un-flips
     ("g3 Al", "e")],                                             # export cycle closes
    'CLEAN'))
S.append(System("pico_export_deposit_WRONG",
    ["Al2", "T", "Th", "P", "e1", "g2"], ["e1", "g2"],
    [("e1 T", "g2 Al2 Th"), ("e1 Th", "g2 Al2 T"),
     ("P e1", "e1 P"), ("g2 P", "P g2")], 'POISON'))

S.append(System("s10_binder_stack",              # M8b core: push/pop bracket marks + zigzag
    ["Tm", "br", "brb", "v", "st", "stm", "dn", "up"], ["dn", "up"],
    [("dn br", "brb dn"),          # descend: push (transduce bracket in passing)
     ("dn v", "v dn"),             # walk variables
     ("dn st", "stm up"),          # mark one stroke, turn (transducing turn)
     ("v up", "up v"),             # ascend walk
     ("brb up", "up br"),          # ascend: pop (restore bracket)
     ("Tm up", "dn Tm")],          # single-rule restart at top anchor
    'CLEAN'))
S.append(System("s13_yard_flag",                 # Law-6 flag toggle: open/close flips
    ["Y0", "Y1", "P", "Tm", "Tw", "W", "o", "o1", "cl", "cl1"],
    ["o", "o1", "cl", "cl1"],
    [("o Y0", "Y1 o1"),            # open: flag flips, distinct state-pair
     ("o1 P", "P o1"), ("o1 Tm", "cl Tw"),
     ("P cl", "cl P"), ("Y1 cl", "cl1 Y0"),      # close: flag flips back, distinct state-pair
     ("W cl1", "o W")],
    'CLEAN'))

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
