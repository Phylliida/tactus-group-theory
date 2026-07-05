# ROADMAP — the ZFC group, from here (master summary)

*2026-07-04. One-page orientation for the whole "self-contained ZFC group" thread: the goal, what's
proven, what's designed, what remains, in order. Read this first; every claim links to its detail doc.*

---

## The goal

A **finitely presented group `G₂`** and a computable map `f` (formula → word) such that
`f(σ)=f(τ) in G₂  ⟺  ZFC ⊢ σ↔τ` — a foundation of mathematics folded into one printable group,
where **every relator is itself a theorem** (no non-semantic scaffolding), and derivation length is
**polynomial** in proof length. Three axes at once: self-contained, readable, low-overhead.

Two framings coexist: (1) the **traditional** Aanderaa–Cohen+Higman route (`AGENDA.md`, ~90% machine-
checked, removes `axiom_ceer_fp_embedding` via GAP-2); (2) the **semantic-basis** route (this thread) —
build `G₂` as a *rewriting machine whose rules are logic schemas*, giving readability + poly overhead.

---

## The idea (semantic basis) in three moves

1. **Relators = provable equivalences.** `f(σ)f(τ)⁻¹` with `ZFC⊢σ↔τ`. Prefix encoding makes whole
   schemas collapse to instance-free "window rules" (`¬¬φ↔φ` ⟹ relator `¬¬`).
2. **The group is a reversible rewriting machine.** Proof *search* → proof *replay* (Bennett): run
   inside `σ∧Θ` transparent history; states are provably-redundant guards; every step a provable
   window rule. Completeness = replay a Hilbert proof; the group simulates *checking*, not searching.
3. **Soundness = positivity.** The group must add no shortcuts beyond the intended rewriting. This is
   the one hard theorem, and the whole program's spine (`Law P`).

Full theory: **`semantic-finite-basis.md`** (laws, M-ladder, parser principle). Capstone construction +
formalization campaign: **`zfc-group-2-plan.md`**. ZFC layer spec: **`nbg-machine-rules-v1.md`**.

---

## What we learned (the transferable results)

- **The Laws of Semantic Machines** (0–6 + P): cycle-relator principle, affix hygiene, no-absorption,
  trajectory-injectivity, mint-must-move, boot-via-encoding, shield discipline, positivity. Every
  soundness failure is a *laundering mode*; each became a mechanical audit probe. (§3.5.)
- **The M-ladder** (M1–M7): positivity proven **on paper** for 9 machine-fragment shapes, each by a
  distinct mechanism (free-product NF, intrinsic Britton, defect-flow, retraction, BS-groups, courier
  markers, junction decoupling). Ambient-group *wildness is orthogonal to trace soundness*. (§4.)
- **The parser principle**: positivity ⟺ no *emergent* ambiguities; dragons = emergent ambiguities;
  proven absent through M7. (§5.)
- **Erasure trichotomy**: the only sound ways to lose information (duplicate-cancel / uncompute /
  peel-with-pair-deposit). "Nothing is erased against nothing."
- **The tools out-scored the humans**: a Python auditor (`tools/semantic_audit.py`, 32-system corpus)
  and a 9.4M-word injectivity fuzz caught 5 real poisons — 3 authored by us *while knowing all the
  rules*. Audits are load-bearing, not decorative.
- **The retraction insight** (formalization): most "hard" admits dissolve into reuse. Faithfulness via
  a section/retraction (φ∘ψ≡id) needs neither confluence nor scar-induction.
- **Negative result**: the naive scaffolding-free carrier is provably NOT f.p. (`H₂ ≅ ⊕ℤ^(|κ|−1)`,
  infinite rank) — so the machine relators are *forced*, not an artifact. (`carrier-not-fp-plan.md`.)

---

## What is MACHINE-VERIFIED (Verus/tactus, full crate 2862/0)

| Module | Status | What |
|---|---|---|
| `src/carrier_not_fp.rs` | 31/0 | Miller carrier not-f.p. — **NF-1 + NF-A core** (refutation conditional only on the escape hypothesis) |
| `src/m0_token.rs` | 25/0 | **M0 COMPLETE, both directions** — the token quotient `G_T ≅ free_group(4)` via ψ (soundness = hom-transport; completeness = retraction) |
| `src/thue.rs` | 18/0 | **Phase 0** — Thue congruence, `positivity` spec (Law P), the bridge (Thue⟹group), + congruence primitives (refl/single/trans/symmetric/prepend) |
| `src/m1_guard.rs` | 34/0 | **M1 COMPLETE** — `positivity(m1_rules,4)` both directions, first M-ladder rung. ⟹ via two-projection route (kill_n/kill_g → same deletes → combinatorial peel induction), no free-product NF |

## What is DESIGNED + AUDITED + RUNNING (Python, not yet formalized)

- **The Boolean machine** (`boolean-group-rules-v1.md`, ~450 rules): 4 passes, 9 subroutines, all
  audited clean. `tools/boolean_engine.py` runs pair-cancellation (`x⊕x=0` in 10 steps).
- **The NBG machine** (`nbg-machine-rules-v1.md`, ~900 rules): shield pipeline; `tools/nbg_machine.py`
  writes `⌜E∈ v |⌝` into the store (1068 rules, audit clean).
- **M0-closure** (`m0-closure.md` + `law-p-prime.md`): the token layer is free; Law P′ (two-layer
  positivity with witnessed whitelist); rotation/consequence closure; §7 checks run (KB 35 pairs no
  fifth rule; injectivity fuzz 9.4M/0).

---

## The path from here (dependency order)

```
Phase 0  thue.rs .......................... ✅ DONE
M0  token layer (G_T ≅ free) .............. ✅ DONE  (base case of positivity)
Phase 1  M-ladder rungs (each = positivity(rules,n)):
   M1 guard-motion ........................ ✅ DONE (m1_guard.rs 34/0, two-projection route)
   M2 translate · M3 blinker · M5 doubler · M6 courier · M7 junction-decoupling (the CROWN)
   → each: define rules, prove ⟹ (mechanism from §4), ⟸ is free from thue.rs
Phase 2  the VERIFIED auditor ............. Laws 0–6 as spec fns; port tools/semantic_audit.py to exec
Phase 3  Boolean group end-to-end ......... expander emits ~450 rules → audit → completeness
   (normalize-simulation, gap2_srm_walk idiom) + Lemma-2-Boolean (junction decoupling over §4.7)
   → theorem_boolean_logic_group  ("the group of Boolean logic")
Phase 4  ZFC layer ........................ M8 rungs (shield/subst-comparator cycles) + RCL (replay
   completeness, computability crate) + NBG axiom mints → theorem_zfc_group_2
Phase 5  papers ........................... "Positivity for semantic rewriting groups I" (after Ph3);
   the ZFC group + the H₂ negative result as the framing pair (needs carrier_not_fp finished)

PARALLEL arc: carrier_not_fp — discharge the escape hypothesis (NF-2a refactor of lemma_pred_to_limit
   + NF-2b representative-collapse valuation [pinned] + NF-3 [PROVEN on paper, weight/contraction
   induction] + NF-4) → NF-A unconditional → v2 (Tietze/any-generators) + NF-7 (ZFC ¬¬-class instance).
```

## Immediate next actions (any is a clean session)
1. **Finish M1's ⟹** — `docs/m1-positivity-plan.md` Part A (projection homs) then Part B (peel
   induction). ~15–20 lemmas, route pinned. *(recommended after a /roll — fresh context)*
2. **carrier_not_fp NF-3** — self-contained, PROVEN on paper (contraction induction); good warm-up.
3. **M2 or M3** — next M-ladder rungs (M3 blinker cashes in the banked `britton_lemma`).
4. **The Phase-2 verified auditor** — ports the 32-system corpus into a machine-checked tool.

## Honest residuals
- Traditional AGENDA: `axiom_ceer_fp_embedding` + ~3 Church–Turing axioms until GAP-2 (α-srm arc) lands.
- Semantic route: everything above M0/thue is designed+audited but not formalized; positivity ⟹ per
  rung is real (elementary) proof work. No known obstruction anywhere; the H₂ result shows the
  scaffolding is necessary, not that the *designed* group fails.
- tactus: the gate carries ~27 pre-existing exec-fn errors (1 fn, `apply_hom_symbol_exec`, a diagnosed
  pipeline bug) — proof modules are 0-error; check LOCATIONS not counts.

---
*Detail docs: `semantic-finite-basis.md` (theory) · `zfc-group-2-plan.md` (construction+campaign) ·
`boolean-group-rules-v1.md` / `nbg-machine-rules-v1.md` (machines) · `m0-closure.md` / `law-p-prime.md`
(token layer) · `m1-positivity-plan.md` (current front) · `carrier-not-fp-plan.md` (negative result).
Tools: `tools/semantic_audit.py` · `tools/m0_check.py` · `tools/boolean_engine.py` · `tools/nbg_machine.py`.
Memory index: `project_semantic_finite_basis.md`.*
