#!/usr/bin/env python3
"""m0_check.py — the two mechanical checks docs/m0-closure.md §7 owes.

(a) KB critical-pair pass on the 9 oriented rules R̂: enumerate every overlap/containment,
    verify joinability, report any non-joinable pair (= a new rule KB would add = a FIFTH RULE).
(b) Injectivity fuzz: enumerate all R̂-irreducible positive words up to length N over
    {⟨,⟩,M,X,0,1}, map by ψ (⟩↦1⁻¹M⁻¹⟨⁻¹, 0↦X⁻¹M1, else fixed) into F(⟨,M,X,1), free-reduce,
    assert images pairwise distinct.  Also confirms ψ(⟩⟨M1)=ε (bicyclic finding, now free-group).

Alphabet chars: ( = ⟨ , ) = ⟩ , and M X 0 1 literally.
"""

# ---- string rewriting over the 6-letter alphabet ----
RULES = [  # (name, lhs, rhs)
    ("r1", "X0", "M1"),
    ("d1", "(M1)", ""), ("d2", "M1)(", ""), ("d3", "1)(M", ""), ("d4", ")(M1", ""),
    ("e1", "(X0)", ""), ("e2", "X0)(", ""), ("e3", "0)(X", ""), ("e4", ")(X0", ""),
]

def one_step_reducts(w):
    outs = []
    for _, l, r in RULES:
        start = 0
        while True:
            p = w.find(l, start)
            if p < 0: break
            outs.append(w[:p] + r + w[p+len(l):])
            start = p + 1
    return outs

def normal_forms(w):
    """all irreducible words reachable from w (system is terminating -> finite)."""
    seen, nfs, stack = {w}, set(), [w]
    while stack:
        x = stack.pop()
        red = one_step_reducts(x)
        if not red:
            nfs.add(x)
        for y in red:
            if y not in seen:
                seen.add(y); stack.append(y)
    return nfs

def joinable(a, b):
    return len(normal_forms(a) & normal_forms(b)) > 0

# ---- (a) critical pairs ----
def critical_pairs():
    cps = []  # (word, reductA, reductB, kind, ri, rj)
    for i, (ni, li, ri_) in enumerate(RULES):
        for j, (nj, lj, rj_) in enumerate(RULES):
            # suffix(li) == prefix(lj) overlaps
            for k in range(1, min(len(li), len(lj))):
                if li[-k:] == lj[:k]:
                    w = li + lj[k:]
                    a = ri_ + lj[k:]              # apply i at 0
                    b = li[:len(li)-k] + rj_      # apply j at len(li)-k
                    cps.append((w, a, b, f"overlap {ni}/{nj} k={k}"))
            # containment: li inside lj (proper), i != j
            if i != j and len(li) < len(lj):
                p = lj.find(li)
                while p >= 0:
                    w = lj
                    a = rj_                                  # apply j (whole)
                    b = lj[:p] + ri_ + lj[p+len(li):]        # apply i inside
                    cps.append((w, a, b, f"contain {ni} in {nj} @ {p}"))
                    p = lj.find(li, p+1)
    return cps

def run_kb():
    print("=== (a) KB critical-pair check on R̂ (9 rules) ===")
    cps = critical_pairs()
    bad = []
    for w, a, b, kind in cps:
        if not joinable(a, b):
            bad.append((w, a, b, kind, normal_forms(a), normal_forms(b)))
    print(f"  critical pairs examined: {len(cps)}")
    print(f"  NON-joinable (would force a new rule): {len(bad)}")
    for w, a, b, kind, na, nb in bad[:20]:
        print(f"    !! {kind}: {w!r}  ->A {sorted(na)}  ->B {sorted(nb)}")
    # confluence corollary: unique NF for every overlap word
    nonuniq = [w for (w, a, b, kind) in cps if len(normal_forms(w)) != 1]
    print(f"  overlap words with non-unique normal form: {len(nonuniq)} (expect 0 if confluent)")
    return len(bad) == 0 and len(nonuniq) == 0

# ---- (b) injectivity fuzz ----
# free-group letters: (=1 M=2 X=3 1=4  (signed ints)
G = {'(':1, 'M':2, 'X':3, '1':4}
PSI = {
    '(': [1],
    ')': [-4, -2, -1],       # 1⁻¹ M⁻¹ (⁻¹
    'M': [2],
    'X': [3],
    '0': [-3, 2, 4],         # X⁻¹ M 1
    '1': [4],
}
def freered(seq):
    out = []
    for x in seq:
        if out and out[-1] == -x: out.pop()
        else: out.append(x)
    return tuple(out)
def psi(w):
    s = []
    for ch in w: s.extend(PSI[ch])
    return freered(s)

ALPHA = "()MX01"
def has_redex(w):
    return any(l in w for _, l, _ in RULES)

def gen_irreducibles(maxlen):
    """DFS positive words with no redex; append-pruned (redexes have length <= 4)."""
    words = []
    def rec(w):
        words.append(w)
        if len(w) >= maxlen: return
        for ch in ALPHA:
            nw = w + ch
            # only a new redex can appear in the last <=4 chars
            tail = nw[-4:]
            if any(l in tail for _, l, _ in RULES):
                continue
            rec(nw)
    for ch in ALPHA:
        if not has_redex(ch):
            rec(ch)
    return words

def run_fuzz(maxlen=9):
    print(f"\n=== (b) injectivity fuzz: R̂-irreducibles up to length {maxlen} ===")
    words = gen_irreducibles(maxlen)
    img = {}
    collisions = []
    for w in words:
        im = psi(w)
        if im in img and img[im] != w:
            collisions.append((img[im], w, im))
        else:
            img.setdefault(im, w)
    print(f"  irreducible words tested: {len(words)}")
    print(f"  distinct ψ-images: {len(img)}")
    print(f"  COLLISIONS (ψ(u)=ψ(v), u≠v both irreducible): {len(collisions)}")
    for a, b, im in collisions[:20]:
        print(f"    !! ψ({a!r}) = ψ({b!r}) = {im}")
    # spot facts
    rpm1 = ")(M1"
    print("  psi(rot ⟩⟨M1) =", psi(rpm1), " (expect () = ε: bicyclic finding, now free-group)")
    print("  psi(X0) =", psi("X0"), ", psi(M1) =", psi("M1"), " (expect equal: r1 collision)")
    return len(collisions) == 0

if __name__ == "__main__":
    ok_a = run_kb()
    ok_b = run_fuzz(9)
    print(f"\nRESULT: KB {'CLEAN' if ok_a else 'FAILED'} ; injectivity {'CLEAN' if ok_b else 'FAILED (correction needed)'}")
