# The NBG Machine — concrete rule families v1 (ZFC Group 2.0 layer)
## Companion to zfc-group-2-plan.md (Parts I/III) and boolean-group-rules-v1.md

*2026-07-03/04, session close. Status: expansion-ready machine spec. Every family is annotated
with its AUDITED shape class (corpus system in `tools/semantic_audit.py`, 32 systems, all green)
— formalization and expansion are transcription against validated patterns, not design.*

---

## 1. Zone layout and alphabet (pinned = the audited PICO layout)

```
Hm · [WORK: σ ∧ Θ-live] · F [font] F′ · ⟨ₛ [YARD] ⟩ₛ · T · Y
```
(The live formula σ with its store Θ as one right-nested conjunction in WORK; the font holds one
copy of each data letter; the yard is the single permanent shield; `T` = store-edge deposit
anchor for exports; `Y ∈ {Y₀,Y₁}` = Law-6 flag. Orientation matches `pico_shield_lifecycle`.)

**Data letters** (ring basis + FOL): `⟨ ⟩ X M 1 0` (Boolean layer), `A` (∀), `E∈ E=` (atom
heads), `v |` (variables `v|^i`) — 10 letters + marked flavors `Σ• Σ◦` + wall/anchor letters
(`F F′ ⟨ₛ ⟩ₛ ⟩̂ₛ T Hm Y₀ Y₁`) + ghost atoms `p_x` (one per data letter, for peel-deposits).

## 2. Pinned simplifications (each removes a subsystem)

1. **NBG has no function symbols ⟹ terms = variables ⟹ S10 collapses.** Substitution instances
   `φ[y/x]` never copy subtrees: Q1-verification is a VARIABLE comparator — stroke-zigzags
   against the binder and the substituted variable (audited classes: `s6_zigzag_comparator`,
   `s10_binder_stack`). The subtree-copier of plan-III.3 is NOT NEEDED. (Capture side condition
   "y free for x": binder-stack + FV-check, same classes.)
2. **Permissive driver.** Thue-completeness needs paths, not schedules: the ZFC layer has NO
   pass-sequencing machinery — any macro may fire where its window matches; completeness is
   argued by exhibiting the replay path (RCL), termination is not required. (The Boolean layer
   keeps its sweeps only for its own completeness measures.)
3. **NBG axiom mints are matcher-free.** Each axiom is a FIXED closed sentence: one concrete
   store-append rule per axiom (`s_T ⟩ = ⟨M-node ⌜Aᵢ⌝ ⟩ s_T′`-shaped, state-led, single rule).
   Only LOGICAL schemas (ring-tautologies, Q1–Q3, Eq) need the yard.
4. **Shield-internal junk is free.** The yard is permanent (V.1): spent verification material
   stays entombed with no cleanup obligation (or is pair-tricked away at leisure). Verification
   always runs on an in-yard COPY of the candidate (font/dup machinery), never the original.

## 3. NBG axiom mint list (N-AX; 18 single rules)

Gödel's grouping (exact primitive-notation codes fixed at transcription; content does not affect
the machine audit — each is one long concrete rule, semantically witnessed by axiomhood):
A1–A4 (extensionality, pairing group); B1–B8 (class existence: intersection, complement, domain,
membership relation, product, converse, two permutations); C1–C4 (infinity, union, power set,
replacement); D (foundation); E (global choice). Estimated code lengths 50–500 letters each.

## 4. Rule families (shape-class–annotated)

| Family | Content | Schemas (≈rules) | Audited shape class |
|---|---|---|---|
| N1 dispatch/walks | state motion over data + walls | 12 (≈90) | M1 / `pass1_swap_core` walks |
| N2 font-dup | double a font letter | 2 (≈20) | `m5_doubler`, `font_copier_core` |
| N3 yard-courier | carry twin into yard, deposit | 6 (≈50) | `font_copier_core`, deposit = single-rule (`pico`) |
| N4 shield-build | assemble candidate γ-copy in yard | uses N2+N3 | `pico_shield_lifecycle` builder |
| N5 ring-verify | Boolean engine ON SHIELDED COPY over blocks; accept iff skeleton ⇝ 1 | engine + 8 glue | Probe-0 machine + `s3` (block walks, PARITY restarts) |
| N6 var-subst compare (Q1) | binder-stroke zigzag; substituted-occurrence zigzag; capture check | 15 (≈60) | `s6_zigzag_comparator`, `s10_binder_stack` |
| N7 FV-check (Q3, closures) | free-occurrence sweep w/ scope marks | 8 (≈30) | `s10_binder_stack` class |
| N8 Q2/Eq matchers | pointwise block comparators | 12 (≈50) | `s6` + `pass3_spine_advance` classes |
| N9 verify-exit / re-flavor | pattern-accepted ⟹ re-flavor candidate live-ready | 4 (≈15) | `pico` verifier (`k ac = Al g`) |
| N10 export | pickup, out-cross (flip), store-deposit at `T` (single rule), in-cross (unflip) | 6 (≈25) | `pico_shield_lifecycle` export; wrong orders = `pico_export_deposit_WRONG`, `pass1_deposit_WRONG_order` (banned) |
| N11 MP-on-live | locate `γⱼ`, block-compare vs implication line, engine transmute `A∧(A→B) ~ A∧B` | 10 (≈45) | `s6`/engine classes |
| N12 flag & store-ctl | Law-6 toggle; store tail-finding | 6 (≈20) | `s13_yard_flag`; M1 walks |
| N-AX axiom mints | one per NBG axiom | 18 (18) | single-rule mint (tree; no cycle) |

**Estimated totals: ≈ 105 schemas ⟹ ≈ 420–480 ZFC-layer rules + Boolean engine (≈450) ⟹
≈ 900 rules, ≈ 130–160 states, 2·10⁴–10⁵ symbols** (axiom codes dominate symbol count).

## 5. Replay macro programs (per ℋ*-proof-line kind; RCL III.2 crosswalk)

- **NBG axiom line:** one N-AX mint at the store tail. (III.2 case 1.)
- **Ring-tautology closure:** N4 build the closure candidate; N2/N3 dup it; N5 verify the copy
  (skeleton ⇝ 1, spent copy stays entombed); N9 re-flavor original; N10 export. (Case 2a.)
- **Q1/Q2/Q3/Eq instance:** N4 build; N6/N7/N8 verify against the live `∀xφ` / pattern; N9+N10.
  (Case 2b — the live anchor is read through the yard wall by the comparators: zigzags may cross
  `⟨ₛ` as ordinary wall-walks, validated class.)
- **MP line:** N11 entirely on live store material. (Case 3.)
- **Finish:** N11's transmutation instance `A∧(A↔B) ~ B∧(A↔B)` at `σ`; then the whole store
  construction reverses (Thue symmetry — no machinery). (Cases 4–5.)

## 6. Law compliance and the audit plan

Laws 0–6 + deposit-order + flip-pairing + erasure-trichotomy honored BY CONSTRUCTION via shape
classes: all deposits single-rule; all anchor-flips carry distinct state-pairs or parity states;
all turns transduce; no shared-context consumption anywhere (per-letter rules always differ on
both sides); mint only via font-dup; erasure only via pair-deposit/uncompute; home/dispatch
anchored at `Hm`. Audit plan: expand N1–N12 with the (Python now / verified later) expander;
run the full battery (Law 1, randomized-Tietze survivors, conjugation-resolution, whitelist,
H₁ triage) on the LITERAL list; expected whitelist entries: the collapsed unit tokens
(`⟨M1⟩`, `⟨X0⟩` analogues) only.

## 7. Formalization crosswalk (Part II phases)

Phase 0–1 consume nothing here (thue.rs + M-ladder). Phase 2's verified auditor takes §4's
tables as its input format. Phase 3 = Boolean engine (its own doc). Phase 4 formalizes: N-AX
mints (trivial), the RCL against §5's macro programs (the induction cases are 1:1 with the
bullet list), and Lemma-2-ZFC via junction decoupling over §4's cycle inventory — every cycle
class already has its proven mechanism named in the table. **Nothing in this machine awaits a
design decision; every family awaits only transcription, expansion, audit, and proof.**
