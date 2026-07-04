# The Group of Boolean Logic — concrete rule list v1
## (expansion-ready; companion to semantic-finite-basis.md §6)

*2026-07-03. Status: complete machine specification at schema granularity — every state named,
every family an explicit schema over explicit finite index sets, mechanically expandable. The
expander + Law-auditor script (§8) is the designated next brick; hand-expansion is deliberately
NOT attempted (the laws are machine-checkable; transcription should be machine-done).*

---

## 1. Alphabet and encoding (final v1 decisions)

**Data letters** `Σ = { ⟨, ⟩, X, M, 1, 0, P, | }` — bracketed Polish: every binary node is
`⟨ op u v ⟩` (`op ∈ {X, M}`, X = ⊕, M = ∧); atoms `P|^i`; constants `1, 0`.
**Marked twins** `Σ• = { ⟨•, ⟩•, X•, M•, 1•, 0•, P•, |• }` (copy/progress marks) and a second
flavor `Σ◦` (copied/processed marks). **Placeholder** `▲` (insertion point; minted/retired within
a single macro, always with motion). Marked letters and `▲` are code-transient; their rules are
witnessed via 0-anchored contexts (witness-liberation, §6.3 of the main note).

**Encoding.** `f(σ) = H₀ · ⌜σ⌝` with `H₀` the home-state chunk (Law 5: the boot lives in `f`).
Canonical code: `f̂(ν) = H₀ · ⌜ν⌝` for ν sorted ANF (right-nested `⟨X m ⟨X m′ …⟩⟩`, monomials
right-nested sorted `⟨M a ⟨M a′ …⟩⟩`, no duplicate atoms in monomials, no duplicate monomials,
constants only as the empty-sum `0` / empty-product `1`). Completeness target:
`f(σ) ⇝* f̂(ANF σ)` — machine ends back at home in `H₀`.

**States** are chunks (comma-free realization layer, main note §6.4 item 2); listed here as
atomic names. Convention: every rule has exactly one state per side (no data-data rules — M8
avoided), sides affix-disjoint (Law 1 checked per family below).

## 2. Global architecture

Four passes, chained through home: `H₀ → PASS1 → H₀¹ → PASS2 → H₀² → PASS3 → H₀³ → PASS4 → H₀`.
Each pass: sweep right seeking its redex; on finding one, run the macro, then RETURN HOME and
restart the pass (maximal simplicity; termination by pass-specific measures). A clean sweep (no
redex, reaching the right end) transitions to the next pass's home state via a transducing turn
at the terminal position (Law 3).

Termination measures (for the completeness proof, v2): PASS1: #(M-above-X) in the tree order;
PASS2: per-monomial inversions + duplicate count; PASS3: monomial-sequence inversions + duplicate
pairs; PASS4: #constants in non-normal position. Each macro strictly decreases its measure.

## 3. Subroutine library (rule families with index sets)

Notation: `s x = x s′` families list their letter range explicitly. `#rules` = expanded count.

**S1 — WALK(s; L):** `s x = x s` for `x ∈ L ⊆ Σ ∪ Σ• ∪ Σ◦`. Guard motion (M1). Used by every
traveling state; each instantiation lists its `L`. Hygiene: ✓ (distinct first/last letters).

**S2 — TURN(s → s′; W → W′):** `s W = W′ s′`, `W ≠ W′` marked/unmarked bracket flavors. (Law 3.)

**S3 — MATCH-SUBTERM(m-family):** mark the extent of the subterm opening at the current `⟨`.
Classical innermost-pair marking: repeat { sweep right from region start; on window `⟨ z ⟩` with
`z ∈ {1,0}` or `z` a fully-marked atom/subterm boundary pattern, mark the pair }. Schemas:
- `m ⟨ = ⟨† m₁` (flag region start; `⟨†` a third bracket flavor)
- `m₁ x = x m₁` for x ∈ Σ (seek)
- innermost-mark: `m₁ ⟨ z ⟩ = ⟨• z• ⟩• m₂`-shaped windows, z-range: `{1, 0, P}` + stroke-runs
  handled by atom-marking sub-rules `m₂ | = |• m₂`, closing `m₂ ⟩ = ⟩• m₃`
- restart/exit: `m₃` returns to region start (WALK left over marked), exits when `⟨†`'s partner
  is marked: `⟨† … all-marked … ⟩•` detection window `m ⟨† = …` etc.
~10 schemas, expanded ≈ 30 rules. Cycles: every mark cycle's net relator carries bracket anchors
(mark-flavors change per cycle) — Law 4′ ✓ by construction; unmark pass (S8) is the inverse
family, separate states (no mark/unmark two-rule laundering cycles: different state sets, and
mark→unmark composites pass through pass-transition states carrying bracket anchors).

**S4 — COURIER(c_x; over L):** pickup `g x• = c_x` (x ∈ Σ: 8 rules per pickup site family),
slide `c_x y = y c_x` (y ∈ L), deposit-at-placeholder `c_x ▲ = x◦ ▲ r` (deposit the copied
letter, in order, left of ▲; `r` = return state). M6-proven shapes. ≈ 8 + 8·|L| + 8 rules
per instantiation.

**S5 — DUP-REGION (alternative copier, BS-doubler idiom, M5(b)):** `d x = x x• d` for
`x ∈ Σ` within a MATCHed region — kept in v1 as the copier for PASS1's C-copy (dup, then
courier the marked twins rightward to the ▲ site, preserving order). 8 rules + courier calls.

**S6 — COMPARE-ATOMS (zigzag, F4/M3-M4 class):** two adjacent atom codes `P|^i … P|^j`
(with bounded intervening structure held in state): blinker states `k, k′` alternate marking one
stroke on each side per round trip: `k |= |• k₁`, WALK, `k₁ | = |• k₂` (right side), WALK back,
`k₂ → k` — turns transduce at the `P`/bracket anchors. Exits: both sides exhaust same round →
EQUAL-exit state; one side exhausts first → LESS/GREATER-exit states (three exit turns, Law 3).
≈ 12 schemas / ≈ 25 rules. Cycle relators: anchored on `P`/brackets ✓ Law 4′.

**S7 — ERASE-PAIR (the §6.3 anchored zigzag; F7):** on a certified-equal adjacent duplicate
pair: fused comparator–eraser deleting in lockstep across the anchor: core quartet
`| e = e₁`, `e₁ P = P e₃`, `e₃ | = e₄`, `P e₄ = e P` (net `| e P | = e P`, anchored ✓) +
structural-letter analogues for the monomial spine (`M`/bracket quartets, same shape) +
factor-fold entry (below). ≈ 10 schemas / ≈ 25 rules.

**S8 — UNMARK(u; L):** `u x• = x u` for the pass's marked range; sweeps restore Σ after macros.

**S9 — UNIT-SWEEPS (guarded constant deletion; the §6.1 featured-catch idiom):**
- `w ⟨ M 1 = w₁` … `w₁ ⟩ = w` -shaped windows deleting unit-wraps `⟨M 1 u⟩ → u` in passing
  (delete the 4 structural letters around `u` in two anchored bites, state-carrying);
- dual `⟨M u 1⟩`, additive units `⟨X 0 u⟩`, `⟨X u 0⟩`;
- zero-product collapse `⟨M 0 u⟩ → 0` and `⟨M u 0⟩ → 0`: NOT naked (u unbounded) — implemented
  as: mark u (S3), erase u against its own mark-twin via S5-inverse (un-dup: `d′ x x• = x d′`??
  — NO: un-dup of unequal material is unsound; instead) — v1 route: DUP-INVERSE ELIMINATION:
  build nothing; use S7-style anchored consumption of the marked region against the `0` anchor:
  quartet family `x• z₀ = z₀'`, alternating flavors of the dedicated zero-anchor letter pair
  (z₀, z₀′ = marked `0` flavors) — cycle relator `x• z₀ x'• = z₀`-shaped: anchored on z₀ ✓
  Law 4′ ✓ (the anchor is the certificate AND it survives every cycle).
  ≈ 14 schemas / ≈ 40 rules.

## 4. Pass programs

**PASS1 (distribute/flatten):** dispatch `D` sweeps (S1 over Σ); redex windows `D ⟨ M ⟨ X` (R1
shape) and `D ⟨ M` + later `⟨ X` at second arg (R2 shape, detected on the return leg): macro =
structural swap window (`⟨M⟨X…` → `⟨X⟨M…` prefix rules, 4–6 concrete windows) + mint `▲` at
insertion point (`p = ▲ p′`, motion ✓ Law 4) + S3(MATCH C) + S5(dup C) + S4(courier twins to ▲,
order-preserving) + retire `▲` (`r ▲ = r′`, motion ✓) + S8 + return home. ≈ 20 schemas beyond
subroutines.

**PASS2 (monomial normalize):** for each monomial: adjacent-atom S6 compare; GREATER → swap via
S4-courier (transport the smaller atom's code across, ▲-mediated); EQUAL → dedup `a∧a→a`: S7 on
the atom pair + unit-fix (the spine `⟨M a ⟨M a u⟩⟩ → ⟨M a u⟩`: two structural deletions,
anchored windows). Bubble until clean sweep. ≈ 15 schemas.

**PASS3 (sum normalize):** adjacent-monomial compare = lexicographic S6 loop over the two spines
(reusing S6 with monomial-boundary turns); GREATER → S4 swap; EQUAL → **pair-cancel**: S7 fused
zigzag over the two spines (atom-by-atom, structural quartet per level), ending in `⟨X 0 0⟩`-core
→ S9 sweeps. Bubble until clean sweep. ≈ 15 schemas.

**PASS4 (constants + exit):** S9 sweeps to fixpoint; empty-sum/product conventions (`⟨X m 0⟩`
tail trimming, top-level `0`/`1` finalization); final clean sweep exits into `H₀` at home via
terminal transducing turn. ≈ 8 schemas.

## 5. State inventory (v1)

`H₀, H₀¹, H₀², H₀³` (homes); `D, D←` (PASS1 dispatch); S3: `m, m₁, m₂, m₃, m←`; S5: `d`;
S4: `g, r` + `c_x` (8); S6: `k, k₁, k₂, k₃` + 3 exits; S7: `e, e₁, e₃, e₄` + spine variants
(≈ 6); S9: `w, w₁, …` (≈ 6); S8: `u`; PASS2/3 dispatchers + swap crews (≈ 10).
**Total ≈ 45–55 states** — within the audit's 30–60 estimate.

## 6. Rule-count tally (expanded, estimated)

S1 instantiations ≈ 120; S3 ≈ 30; S4 ≈ 60 (two instantiations); S5 ≈ 8; S6 ≈ 25; S7 ≈ 25;
S8 ≈ 16; S9 ≈ 40; pass-specific windows ≈ 60. **Total ≈ 380–420 rules** — order 10², as
estimated; every rule ∈ Sem (0-anchored witnesses for marked/transient material).

## 7. Audit summary (family level)

- **Law 1:** every schema has state-led vs data-led sides or distinct state flavors — affix-
  disjoint by shape; cross-relator pieces = single chunks (comma-free layer pending, §6.4-2).
- **Law 0/4/4′ cycle survey:** cycles = {sweep round-trips (net-trivial, harmless), mark/unmark
  (bracket-anchored), courier loops (transport = intended), zigzag rounds (anchored quartets),
  dup (BS, cleared), mint/retire ▲ (per-macro, with motion)}. NO data-only net relators found at
  schema level. **The expander must re-verify on the literal graph** — §6.3's laundering example
  shows this check must be mechanical, not visual.
- **Law 2/3/5:** no absorption shapes; all turns transduce; boot in `f`. ✓
- **M8 check:** zero data-data rules. ✓ Completion-divergence: deferred to mechanical KB run.

## 8. The expander/auditor (designated next brick — build, don't hand-check)

A small tool (Rust or Python, this repo's choice) that: (1) expands §3–§4's schemas × index sets
into the literal rule list; (2) checks Law 1 per rule (affix-disjointness, chunk-piece bounds);
(3) builds the state graph, enumerates cycle basis, computes each cycle's net relator via free
reduction, checks Law 4′ (no data-only relators); (4) runs Knuth–Bendix to bounded depth
(completion-divergence probe, M8); (5) emits the presentation (generators + relators) — i.e.,
**the tool's output IS the group of Boolean logic**, machine-audited against the laws. Natural
follow-ups: a brute-force positivity fuzzer (random positive word pairs, group-equality via the
splitting normal forms vs Thue-reachability) and eventually the tactus formalization.

---
*v1 caveats, honestly: PASS1's R2-redex handling and PASS3's monomial-boundary turns are the two
spots most likely to need schema surgery on expansion; S9's zero-anchored consumption is new —
flagged for the fuzzer. Nothing here is theory-risk; it is all Law-auditable construction.*

---

# Appendix A — expanded schemas for the flagged spots (v1.1)

## A.1 S3 MATCH-SUBTERM, full listing

Goal: from a state at a subterm's opening bracket, mark exactly that subterm's extent.
Letters: third bracket flavor `⟨†` (region start), marked `⟨•,⟩•`, and per-letter marks.
States: `m` (entry), `m₁` (seek innermost), `m₂` (atom interior), `m₃` (rewind), `m₄` (exit test).

```
(1)  m ⟨ = ⟨† m₁                        (flag region start)
(2)  m₁ x = x m₁            x ∈ {X, M, ⟨}        (descend/seek rightward)
(3)  m₁ ⟨ c = ⟨• c• m₃      c ∈ {1, 0}           (innermost constant leaf: wait—leaves sit inline;
                                                   leaf marking:)
(3′) m₁ c = c• m₃           c ∈ {1, 0}           (mark constant leaf)
(4)  m₁ P = P• m₂                                (enter atom)
(5)  m₂ | = |• m₂                                (mark strokes)
(6)  m₂ y = y m₃-dispatch    y ∈ {⟨, X, M, P, 1, 0, ⟩}  (atom done; y unconsumed — handled by m₃ rules below)
(7)  m₁ ⟩ = ⟩• m₃                                (close reached with children marked ⟹ mark it)
(8)  m₁ x• = x• m₁                               (skip already-marked material)
(9)  m₃ x• = x• m₃ ; m₃ x = x m₃  (x data)       (rewind right-to-left is not needed: rewind LEFT:)
(9′) x m₃ = m₃ x  — NO (data-data shape) — rewind as: m₃ walks LEFT via left-moving state rules:
     x• m₃ = m₃ x• and x m₃ = m₃ x are ILLEGAL shapes (state on wrong side is fine — rule shape
     `a s = s' a` IS legal, one state per side): use m₃ with left-motion:
(9″) x• m₃L = m₃L x•, x m₃L = m₃L x   x ∈ Σ      (left rewind, M5′-legal left-mover shapes)
(10) ⟨† m₃L = ⟨† m₄?? — turn at region start: ⟨† m₃L = m₄ ⟨†   (transducing turn on flavor? ⟨†
     already distinct — Law 3 satisfied by state change + distinct wall)
(11) m₄: re-seek (as m₁) — if the sweep finds NO unmarked letter before the matching ⟩•-candidate,
     exit; else loop to m₁. Exit detection: m₄ reaches a ⟩ whose interior is fully marked:
     m₄ ⟩ = ⟩• m_done   (the region's own close: it is the FIRST unmarked ⟩ met when everything
     interior is marked — invariant maintained by (7) marking closes only when reached through
     marked material).
```
Correctness invariant (for the completeness proof): after each m₄-loop, the set of marked
letters is a union of complete subtrees of the region, growing by ≥1 leaf per loop; termination:
#unmarked in region strictly decreases. Cycle audit: all loops pass through the `⟨†` anchor
(rewind turns there) — Law 4′ ✓. (The m₂→m₃ hand-off (6) needs per-y dispatch rules; 7 rules.)
Expanded count ≈ 34.

## A.2 PASS1, R2 redex (`⟨M A ⟨X B C⟩⟩` with A X-free) — full macro

Detection: on the return leg (left-moving `D←` after a clean right sweep segment), window
`D← ⟨ X = flag` is wrong-side; instead: during the RIGHT sweep, at each `⟨M`, push a bracket
mark `⟨ₘ` (M-context flag); when the sweep later meets `⟨X` while the nearest enclosing flag is
`⟨ₘ` — adjacency encoded by: the flag is on THIS M-node's opening, and the X-node is its SECOND
child. Second-child detection: after `⟨ₘ M`, run MATCH-SUBTERM on the first child A (marks it),
so the next unmarked `⟨` after A's marked block is the second child's opening: window
`d₂ ⟨ X = ⟨• X• d₃` fires only in that configuration (state d₂ is only produced post-MATCH).
Macro (mirror of R1 with roles swapped): structural rewrite target
`⟨X ⟨M A B⟩ ⟨M A C⟩⟩` — copy A (not C): A is already MARKED (bonus from detection):
DUP its marked block in place (S5 on marked letters: `d x• = x◦ x•? d` — twin flavor emits the
copy as ◦-marked), courier the ◦-copy rightward past B to the C-position insertion point `▲`
(minted after B's end — B's end located by a second MATCH-SUBTERM), then the bounded structural
windows: `⟨ₘ M → ⟨ X ⟨ M`-shaped re-bracketing at the redex root (4 concrete windows: root
rewrite, mid-separator `⟨M`-insertion at ▲, two close-bracket fixes), unmark-sweep (S8), retire
▲, return home. New states: `d₂, d₃, dup-crew, c-crew (reused), r₂`. ≈ 22 schemas.
Cycle audit: all macro cycles thread the `⟨ₘ` flag anchor; the flag is created and consumed
within one macro (flag-mint has motion; Law 4/4′ ✓).

## A.3 PASS3 monomial-boundary turns — comparator lifting

Comparing adjacent monomials `⟨X m ⟨X m′ R⟩⟩`: the S6 atom-comparator runs on the FIRST atoms of
m, m′; on EQUAL, advance both spines one `⟨M a`-segment (marking consumed segments) and recurse;
on LESS/GREATER exit with the verdict. Boundary rules (the flagged spot): the zigzag's turns
happen at the two monomials' current-segment `P`-anchors; the SPINE-ADVANCE windows are:
```
(t1) k= ⟨ M = ⟨• M• k=′        (left spine: consume segment head after EQUAL verdict)
(t2) k=′ walks right (over marked) to the right spine; k=′ ⟨ M = ⟨• M• k=″ (right spine)
(t3) k=″ → k (restart S6 on next atom pair)
(t4) end-cases: left spine exhausted first (window `k= a-tail-end pattern` where the spine's
     last atom lacks a following ⟨M): verdicts SHORTER-LEFT (⟹ m < m′ in deg-lex) etc.
     — 4 end-windows (left/right × exhausted/continuing).
```
The monomial-boundary turn anchors are the `⟨M`-flavored marks — every zigzag cycle nets a
relator containing them (Law 4′ ✓). On final EQUAL-exhausted-both: enter F7 pair-cancel (S7)
with both spines fully marked (the marks BECOME the dual-erase's synchronization track — this
is the fusion that makes S7's lockstep well-defined). ≈ 14 schemas.

## A.4 S9 zero-anchored consumption, full quartet family

Purpose: `⟨M u 0⟩ → 0` and mirror — consume the (arbitrary) subterm u against the live `0`
anchor. Letters: anchor flavors `0̂, 0̌` (alternating); states `z, z₁`.
```
(z1) x 0̂ = 0̌      — ILLEGAL as written (no state) — actual family:
(z1) z x = z₁      x ∈ Σ∪Σ•   (consume one letter of u, left of the anchor-state pair)
     — z sits immediately LEFT of the anchor; consumption happens on z's left ⟹ left-moving
     retire: x z = z₁  (state-right shape, M5′-legal)
(z2) z₁ 0̂ = 0̌ z    (touch the anchor, flip its flavor — the anchor IS the certificate and it
                    survives every cycle)
(z3) x z = z₁ ; z₁ 0̌ = 0̂ z   (the alternating twin)
(z4) entry: w ⟨ M = z-init windows from the S9 dispatch (detect `M`-node with 0 second child:
     via MATCH on first child + window `z-init 0 ⟩ = 0̂ ⟩ z` anchor-flavoring)
(z5) exit: z reaches the node's ⟨: window `⟨ z₁? …` → delete the bracket pair and M around the
     bare anchor: `⟨ M-mark z 0̂ ⟩ = 0 w′`-shaped bounded window (restore plain 0, exit state).
```
Net cycle relator (one z/z₁ round): `x·z·0̂ ↔ z·0̌`-composite ⟹ contains z-states AND the anchor
flavor flip — never data-only (Law 4′ ✓ — and the flavor alternation means even TWO rounds net
an anchored relator, unlike the laundering pattern). Backward soundness: reversed, the family
MINTS arbitrary letters next to a live flipped anchor inside the M-node being deleted — sound:
the node is ≡ 0 regardless of u's content (0-conjunct), which is precisely the semantic witness
family. ≈ 18 rules expanded.

## A.5 Revised tally

v1.1 expanded estimate: previous ≈ 380–420, plus A.1–A.4 refinements net +40–60 (R2 macro and
boundary turns were under-counted; S3 fully priced) ⟹ **≈ 440–480 rules**. Still order 10².
All new cycles anchored; no data-data rules introduced (the A.1(9′) note shows where the shape
discipline bites and how left-mover shapes stay legal).

## A.6 CORRECTION to A.4 (mechanically confirmed): zero-anchored consumption is POISON

The A.4 quartet consumes arbitrary letters through a shared state-pair (`x z = z₁` for all x).
**Any two such rules identify their letters**: eliminating `z₁` from `x₁z = z₁`, `x₂z = z₁`
leaves the data-only survivor `x₁·x₂⁻¹`. Confirmed by `tools/semantic_audit.py`
(`s9_zero_consume_AS_WRITTEN_A4` → POISON, survivor `x1.-x2`). The anchor-flavor alternation
protected the CYCLE but not the RULE-PAIR — a third laundering mode: **shared-context
consumption**.

**The fix — peel-with-pair-deposit (S9′, mechanically confirmed CLEAN):** to annihilate
`⟨M u 0⟩ → 0`, never consume `u` against nothing. Peel `u` head-letter-wise, each peel
DEPOSITING a designated ghost-atom pair: window `z·x = p_x p_x·z′`-shaped (per-letter distinct
both sides ⟹ no identification; alternating states for hygiene). Semantic witness: inside the
zero-summand, `(x∧u′)∧0 ⊕ R ≡ u′∧0 ⊕ (p_x ⊕ p_x) ⊕ R` — both `≡ R`. The deposited pairs are
then F7-pair-cancelled: **the graveyard self-cleans**, endpoints stay canonical.

**The erasure trichotomy (closing the theory):** the ONLY legal loss mechanisms are
(a) F7 lockstep duplicate-cancel (the copy is the record), (b) uncompute-by-reversal
(Thue symmetry), (c) peel-with-pair-deposit (which reduces to (a) after deposit).
Everything else — generic erasers, certificate-carrying erasers, shared-context consumers —
is one of the three confirmed laundering modes. Rule-of-thumb for the auditor and all future
opcode design: **nothing is ever erased against nothing.**

## A.7 Audited families round 2 + the collapsed-token finding (auditor corpus now 22)

**S7 erase-pair quartet: CLEAN** (mechanical confirmation of §6.3's hand analysis; anchored net
relator, benign `st` H₁ signature). **S6 zigzag comparator (minimal model): CLEAN** — the
bounce/mark idiom validated.

**The unit-sweep finding.** The walk-through unit-deletion (`w ⟨M1 = w₁`, walks, `w₁ ⟩ = w`)
generates the data-only group consequence **`⟨M1⟩ = 1`** (survivor `br.M.one.cb`). The Law 4′
check flags it — correctly conservative — but this one is *legitimately semantic*:

> `f(1∧1)·f(1)⁻¹ = ⟨M11⟩·1⁻¹` freely reduces to exactly `⟨M1⟩` ∈ Sem.

It is a §2.1 **cancellation-collapsed schema token**. Two theory notes: (i) the bracketed
encoding blocks naive tail-collapse (a closing bracket interrupts the §2.1 cancellation), yet
the machine REGENERATES the collapsed tokens as derived consequences — the group finds its own
schema tokens; (ii) such tokens are honest, witnessed, data-only relators that the Lemma-2
parser must treat as first-class (they are short and concrete; same for `⟨X0⟩ = 1` from the
additive unit sweep, witness `f(0⊕0)·f(0)⁻¹`).

**Auditor upgrade: the witnessed whitelist.** Data-only survivors are now matched (up to cyclic
rotation/inversion) against DECLARED semantic tokens, each declaration owing a witness pair;
undeclared data-only survivors remain poison flags. Corpus: `unit_sweep_raw` → POISON
(undeclared), `unit_sweep_whitelisted` → CLEAN. **Audit protocol from here: every data-only
survivor must either ship a witness (whitelist entry) or kill the design.**

Families still awaiting this treatment: PASS1 structural-swap windows + R2 macro composite,
S3 full MATCH-SUBTERM listing, PASS3 spine-advance composite, and (ZFC layer) S10–S16.
Method identical: transcribe into the corpus, run, explain every survivor.

## A.8 PASS1 audited + the deposit-order law + the conjugation-resolution upgrade (corpus 25)

**pass1_swap_core: CLEAN.** The distribution redex machinery — the 6-letter swap window
`H⟨M⟨X = ⟨X⟨M·D`, in-macro mint/retire of `▲`, transducing turn at `⟩→⟩•`, walk-back, home
return — validated. Two design requirements surfaced and pinned:
- **Home-anchor requirement:** home detection MUST use a dedicated wrapper letter `Hm`
  (`Hm·D₃ = H·Hm`). Using an ordinary letter creates duplicate-LHS rules whose group consequence
  identifies states — friendly-fire control collapse (semantically sound, hence outside the
  soundness auditor's scope: documented as a completeness hazard, fix mandatory).

**The deposit-order law (micro-law, mechanically confirmed).** Courier deposits at a placeholder:
the S4 spec order (`c_x ▲ = x◦ ▲ r` — deposit BEFORE the placeholder, single rule, no flavor
pair) is **load-bearing, not stylistic**. The tempting alternative — flavor-flipping the
placeholder with wall-first deposits (`▲ k = ▲̂ x◦ g`, `▲̂ k = ▲ x◦ g`) — creates hidden
wall-flavor torsion: combining the two flavors' conjugation forms forces **`(▲̂⁻¹▲)² = 1`**,
a data-only relator invisible to plain Tietze-survivor checking. My own first transcription of
the courier used the wrong order — the transcription-bug class the tool exists for.
(`pass1_dup_courier_SPEC_order` → CLEAN; `pass1_deposit_WRONG_order` → POISON, survivor
`trib.-tri.trib.-tri`.)

**Auditor upgrade: conjugation-resolution.** The mechanical form of the hand-combination that
refuted the shuttle: survivors of shape `s·A·s⁻¹·B` are indexed by `(state s, core A)`; pairs
with equal keys derive `B₁·B₂⁻¹`, which re-enters the data-only check. This closes the main
consequence-closure gap flagged in the capstone IV.2′ meta-lesson (Tietze alone ≠ audit). All
previously-audited systems keep their verdicts under the upgrade (shuttle still POISON via its
own mechanism; font-copier still CLEAN — its two conjugation forms have DIFFERENT cores, so no
resolution fires: the discriminator is exact on the corpus).

## A.9 Round 4: S3 restart turns + PASS3 spine-advance (corpus 28) — the flip-pairing law

**The flip-pairing law (generalizing the deposit-order law).** Two rules
`α·s = β·s′` and `β·s = α·s′` — a flavor-flip pair SHARING its state-pair — force
`(α⁻¹β)² = 1`: data-only torsion (mechanically: `s3_restart_flip_SHARED_states` → POISON,
survivor `brg.-brf.brg.-brf`). Fixes, all validated: (i) carry flip-PARITY in the states
(`s3_restart_flip_PARITY_states` → CLEAN); (ii) a SINGLE restart rule with no flavor pair
(A.1's original `⟨† m₃ = m₄ ⟨†` — nothing to combine); (iii) the font-copier escape: if the
anchors cross sides with a deposit between (`s·α = X·β·s′` shape), the pair yields the
consistent `s·m·s⁻¹ = X·m⁻¹·X⁻¹` instead of torsion. Side-of-approach and deposit placement
decide — **the law is a design heuristic; the auditor's survivor + conjugation-resolution
passes are the judge, instance by instance.**

**PASS3 spine-advance: CLEAN** — the two-spine advance cycle (`ke⟨M = ⟨•M•ke₁`, walk,
`ke₁⟨M = ⟨•M•ke`) nets the anchored conjugation `ke·(⟨M)²·ke⁻¹ = (⟨•M•)²`; no combination
fires (state-pairs differ). The A.3 design is validated as written.

Running tally of laundering modes, all mechanically detectable: state-cycles (Law 0/4),
bounded-bit mint counting (shuttle), shared-context consumption (S9), duplicate-LHS home
detection (friendly fire, documented), wall-first flavor deposits (deposit-order), shared-state
flavor-flips (flip-pairing). Six modes, six probes, twenty-eight systems, zero unexplained
survivors.

## A.10 THE ENGINE'S HEART RUNS (tools/boolean_engine.py)

The pair-cancellation engine — F7's fused comparator–eraser on real encoded atoms over the flat
⊕-spine (v1.1 encoding note: the sum spine is bracket-free; ⊕ is AC and the spine unambiguous) —
**audits CLEAN (0/0/0) and executes**: `p₁ ⊕ p₂ ⊕ p₂ ⟶ p₁` in ten Thue steps: two zigzag
round-trips eating one stroke from each copy per cycle (the anchored quartet across `⊞P`), the
5-letter skeleton-consumption window, the transducing done-wall exit. **Ten relator applications
in the group of Boolean logic, computing `x ⊕ x = 0` — the ring's arithmetic performed by the
group itself.** Every rule an audited shape; the trace is the first normalization the Boolean
group ever performed.

## A.11 Whitelist consequence-closure → Law P′ (see docs/law-p-prime.md)

The A.7 witnessed-whitelist protocol has a follow-on obligation, worked out 2026-07-04. The two
collapsed unit tokens `⟨M1⟩ = ε`, `⟨X0⟩ = ε` are not closed under consequence: eliminating `⟩`
derives the positive pair **`M1 = X0`** (sound — it is the collapsed schema `1∧u ↔ 0⊕u`, both
`≡ u`, witnessed). And they are not closed under rotation: naive rotation-free `T̂` is refuted by
a bicyclic-monoid invariant (`⟩⟨M1 ↦ qp ≠ ε`). The `token_interaction_probe` in
`tools/semantic_audit.py` (run this session) mechanically reproduces both — returning the 8
rotation-identities plus `M1 = X0` as the minimal `T̂` generating set. This turns plain positivity
(the V.3/`positivity` spec) into **Law P′** (`positivity_mod` over the join `Thue(R) ∨ ≈_T`) and
adds the **M0 rung** (that `≈_T` is a finite Thue congruence `T̂`). Canonical codes are proved
`T̂`-irreducible (endpoint lemma), so endpoint soundness is unaffected. Full treatment, NF-3
proof, NF-2b pin: `docs/law-p-prime.md`.
