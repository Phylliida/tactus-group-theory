#!/usr/bin/env python3
"""boolean_engine.py — the Boolean engine's heart, built and running: PAIR-CANCELLATION.

The F7 fused comparator-eraser (audited: s7_erase_pair_quartet) instantiated on real encoded
atoms over the flat ⊕-spine encoding (sum spine bracket-free — ⊕ is AC, the spine is
unambiguous; v1.1 encoding note). Rules: the anchored quartet across the two-letter anchor
`⊞P`, the skeleton-consumption window, and the end-wall exit. DEMO: the engine normalizes
  p₁ ⊕ p₂ ⊕ p₂   ⟶   p₁
by canceling the duplicate pair stroke-by-stroke in lockstep — each Thue step a relator
application in the group of Boolean logic.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semantic_audit import System, law1, law4prime, h1_data_vectors
from nbg_machine import apply_once, drive

# letters: S=⊞ (spine separator), P, st=|, E (end wall), Ed (end wall, done-flavor)
RULES = [
    ("st e", "e1"),            # quartet: consume one left-atom stroke
    ("e1 S P", "S P e3"),      #   cross the two-letter anchor ⊞P
    ("e3 st", "e4"),           #   consume the matching right-atom stroke
    ("S P e4", "e S P"),       #   return across the anchor  (net: |e⊞P| = e⊞P, anchored)
    ("S P e S P", "z"),        # both stroke-runs exhausted: consume the skeleton (5-letter window)
    ("z E", "Ed f"),           # exit at the end wall (transducing turn)
    ("st z", "z2 st"),         # (guard: z never walks — present only to be audited as absent-use)
]
LETTERS = ["S", "P", "st", "E", "Ed"]
STATES = ["e", "e1", "e3", "e4", "z", "z2", "f"]

if __name__ == "__main__":
    sysd = System("boolean_pair_cancel_engine", LETTERS + STATES, STATES,
                  [(l, r) for l, r in RULES], 'CLEAN', transient=["Ed"])
    l1 = law1(sysd)
    poison, warns = law4prime(sysd, tries=40, return_warns=True)
    print(f"AUDIT: Law1 violations: {len(l1)}; PURE-CODE poisons: {len(poison)}; warns: {len(warns)}")
    for c in poison[:5]: print("  POISON:", sysd.show(c))
    print("VERDICT:", "CLEAN" if (not l1 and not poison) else "POISON")

    rules = [(tuple(l.split()), tuple(r.split())) for l, r in RULES]
    # f(p1 ⊕ p2 ⊕ p2) with the eraser seated at the duplicate pair's seam:
    word = "S P st S P st st e S P st st E".split()
    print("\nDEMO — the engine cancels p2 ⊕ p2 inside  p1 ⊕ p2 ⊕ p2 :")
    print("  start:", " ".join(word), "   (⊞P| ⊞P|| e ⊞P|| E)")
    n = 0
    while True:
        new, info = apply_once(word, rules)
        if new is None: break
        word = new; n += 1
        print(f"   {n:2d}:", " ".join(word))
    result = " ".join(word)
    ok = result == "S P st Ed f"
    print(f"\n  RESULT: {result}   "
          f"{'==  f(p1) + done-wall — NORMALIZED.' if ok else '(unexpected!)'}")
