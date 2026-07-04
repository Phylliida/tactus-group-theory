#!/usr/bin/env python3
"""nbg_machine.py — the NBG machine, built: expander + audit + running simulator.

EXPANDER: generates the literal rule list for the shield-pipeline core (families N1-N4, N9, N10
of docs/nbg-machine-rules-v1.md) over the FULL NBG data alphabet — per-letter courier/export
states, exactly the audited PICO shapes, letter-indexed.
AUDIT: runs the full semantic_audit battery on the expanded machine.
SIMULATOR: a Thue rewriting engine + scripted driver; DEMO: the machine builds the atom
fragment ⌜E∈ v |⌝ letter-by-letter from the font, through the shield, verifies by re-flavor,
and exports it into the store — the first formula the NBG group ever wrote.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semantic_audit import System, law1, law4prime, h1_data_vectors

DATA = ["br", "cb", "X", "M", "one", "zero", "A", "Ein", "Eeq", "v", "st"]  # the 11 NBG letters

def expand_rules():
    """Families N1-N4 (font-dup + yard courier), N9 (verify re-flavor), N10 (export)."""
    R = []
    # builder entry: REQUEST-CONDITIONED fetch (choice points must be window-conditioned —
    # shared-LHS choice rules identify their branches; requests r_x make each branch distinct)
    for x in DATA:
        R.append((f"r_{x} h", f"d_{x}"))             # consume request (from the right), become fetcher
        R.append((f"d_{x} Hm", f"Hm d_{x}"))
        R.append((f"d_{x} F", f"F d_{x}"))
        for y in DATA:
            R.append((f"d_{x} r_{y}", f"r_{y} d_{x}"))
            if y != x:
                R.append((f"d_{x} {y}", f"{y} d_{x}"))   # walk past non-targets
        R.append((f"d_{x} {x}", f"{x} {x}m d1"))     # dup the target (distinct LHS from walks)
        R.append((f"{x}m d1", f"c_{x}"))             # fused pickup (definitional shrink)
    for x in DATA:                       # N3 carry into yard (font_copier_core shapes)
        R.append((f"c_{x} Fp", f"Fp c_{x}"))
        R.append((f"c_{x} Lb", f"Lb c_{x}"))
        for y in DATA:                                # slide over font content + yard content
            R.append((f"c_{x} {y}", f"{y} c_{x}"))
            R.append((f"c_{x} {y}c", f"{y}c c_{x}"))
        R.append((f"c_{x} Rb", f"{x}c Rb c2"))       # yard deposit: SINGLE RULE, before wall
    # builder return (shared)
    R.append(("Rb c2", "c2 Rb"))                     # cross the yard wall back
    R.append(("Lb c2", "c2 Lb")); R.append(("Fp c2", "c2 Fp"))
    R.append(("F c2", "c2 F"))
    for x in DATA:
        R.append((f"{x} c2", f"c2 {x}"))
        R.append((f"{x}c c2", f"c2 {x}c"))
        R.append((f"r_{x} c2", f"c2 r_{x}"))
    R.append(("Hm c2", "h Hm"))                      # builder cycle closes at the home anchor
    # N9 verify: re-flavor deposited -> live-ready (per-letter distinct both sides)
    for w in ["Hm", "F", "Fp", "Lb"] + DATA:         # verifier reaches the yard
        R.append((f"g {w}", f"{w} g"))
    for x in DATA:
        R.append((f"g {x}c", f"{x}L g"))
        R.append((f"{x}L g", f"g {x}L"))             # slide back left to pick up
        R.append((f"{x}c g", f"g {x}c"))             # slide back over unconverted too
        for y in DATA:
            R.append((f"e_{x} {y}L", f"{y}L e_{x}"))  # carry out over converted letters
            R.append((f"e_{x} {y}c", f"{y}c e_{x}"))  # ...and over unconverted
    # N10 export: per-letter pickup, out-cross (flip), store deposit at T (single rule), return
    for x in DATA:
        R.append((f"g {x}L", f"e_{x}"))
        R.append((f"e_{x} Rb", f"Rbh ex_{x}"))
        R.append((f"ex_{x} P", f"P ex_{x}"))
        R.append((f"ex_{x} T", f"{x}S T g2"))
        for y in DATA:                                # cross previously stored letters
            R.append((f"ex_{x} {y}S", f"{y}S ex_{x}"))
    R.append(("P g2", "g2 P")); R.append(("T g2", "g2 T"))
    R.append(("Rbh g2", "g Rb"))  # return AS the verifier
    for y in DATA:
        R.append((f"{y}S g2", f"g2 {y}S"))
    return R

def letters_and_states(R):
    toks = set()
    for l, r in R: toks |= set(l.split()) | set(r.split())
    states = {t for t in toks if t in ("h","d1","c2","g","g2")
              or t.startswith(("c_","e_","ex_","d_"))}
    return sorted(toks - states), sorted(states)

# ---------------- simulator ----------------

def parse(R, sysd):
    return [(tuple(l.split()), tuple(r.split())) for l, r in R]

def apply_once(word, rules, allowed=None):
    for li, (l, r) in enumerate(rules):
        if allowed and (l, r) not in allowed: continue
        n = len(l)
        for p in range(len(word) - n + 1):
            if tuple(word[p:p+n]) == l:
                return word[:p] + list(r) + word[p+n:], (l, r, p)
    return None, None

def drive(word, rules, phase, cap=400, trace=None):
    steps = 0
    while steps < cap:
        new, info = apply_once(word, rules, allowed=phase)
        if new is None: return word, steps
        word = new; steps += 1
        if trace is not None and steps <= trace:
            print("      " + " ".join(word))
    return word, steps

if __name__ == "__main__":
    R = expand_rules()
    letters, states = letters_and_states(R)
    print(f"EXPANDED: {len(R)} literal rules, {len(states)} states, {len(letters)} letters")

    transient = [t for t in letters if t not in DATA]   # marks/flavors/walls: never in codes
    sysd = System("nbg_shield_core_expanded", letters + states, states,
                  R, 'CLEAN', transient=transient)
    l1 = law1(sysd)
    poison, warns = law4prime(sysd, tries=3, return_warns=True)
    print(f"AUDIT: Law1 violations: {len(l1)}; PURE-CODE poisons: {len(poison)}; "
          f"transient/mixed warns: {len(warns)}")
    for c in poison[:5]: print("  POISON:", sysd.show(c))
    for c in warns[:2]:  print("  WARN (transient/mixed decoration relation):", sysd.show(c))
    verdict = "CLEAN" if (not l1 and not poison) else "POISON"
    print(f"VERDICT: {verdict}  (warns = relations among shielded transients; "
          f"semantically inert — yard content is ⊤-material)")

    # ------- DEMO: build & export the atom fragment  E∈ v |  -------
    rules = parse(R, sysd)
    word = "r_st r_v r_Ein h Hm F Ein v st Fp Lb Rb P T".split()
    print("\nDEMO — the machine writes ⌜E∈ v |⌝ into the store through the shield:")
    print("  start:", " ".join(word))
    def is_export(l, r):
        toks = set(l) | set(r)
        return any(t in ("g", "g2") or t.startswith(("e_", "ex_")) for t in toks)
    build_phase = {(l, r) for (l, r) in rules if not is_export(l, r)}
    word, n = drive(word, rules, build_phase, cap=600)
    print(f"  build (request-driven, all 3 letters): ({n} steps) ->", " ".join(word))
    vx_phase = {(l, r) for (l, r) in rules if is_export(l, r)}
    word = ["g" if w == "h" else w for w in word]     # hand dispatch to verifier/exporter
    word, n = drive(word, rules, vx_phase, cap=800)
    print(f"  verify+export: ({n} steps) ->", " ".join(word))
    stored = [w for w in word if w.endswith("S")]
    print(f"  STORE CONTENTS: {' '.join(stored)}  "
          f"{'— the atom arrived.' if stored else '(export incomplete)'}")
