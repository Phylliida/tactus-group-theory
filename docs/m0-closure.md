# m0-closure.md — The M0 enumeration: `G_T` is free, `T̂` is convergent, and the fifth rule does not exist

*2026-07-04, second continuation. Status: M0 closed at paper strength, with the two owed
mechanical runs (§7) now EXECUTED — see §9. Headline findings: (i) the token quotient is FREE —
the Adjan relator was scaffolding; (ii) the nine-rule `T̂` orients into a convergent rewriting
system with ALL critical pairs joinable — Knuth–Bendix closes with zero new rules; (iii) each
rotation rule is exactly the killer of one readback ambiguity, which explains, rather than merely
lists, why `T̂` is what it is.*

---

## 1. The reframe: eliminate `0` too

The M0 plan said: markers over the Adjan base `B = ⟨Σ∖{⟩} | M1 = X0⟩`, with a flagged risk
where the marker interior `1⁻¹M⁻¹` touches the relator. Preparing that enumeration forced the
obvious-in-hindsight observation: **the relator `M1 = X0` is itself triangular** — it can be
solved for any one of its four letters. Solve it for `0`:

> `0 = X⁻¹M1`.

Second Tietze elimination. No relator remains:

> **`G_T ≅ F(Σ∖{⟩, 0})`** — the token quotient is a free group, with the embedding
> `ψ: Σ* → F(Σ∖{⟩,0})` given letterwise by `⟩ ↦ 1⁻¹M⁻¹⟨⁻¹`, `0 ↦ X⁻¹M1`, all other
> letters fixed.

Consequences, in order of relief: the marker–relator overlap case **cannot occur** — there is
no relator to overlap with; the feared "relator flips the marker's interior" phenomenon becomes
ordinary free-group cancellation between the `⟩`-marker and the `0`-marker; Adjan/Remmers is
demoted back to its M5(c) duty (it was never needed here — a one-relator presentation being
Adjan is much weaker than it being free, and this one is free); and Lemma 2's base-layer
parameter stops being parameter-shaped: **the base is a free group again**, just on
`Σ∖{⟩,0}` with two derived letters. The P′ bookkeeping cost drops from "global upgrade" to
"compose with `ψ` at the junctions."

M0 is now a statement about a *free* group: for positive `u, v` over `Σ`,
`ψ(u) = ψ(v)` in `F(Σ∖{⟩,0})` ⟺ `u ↔*_{T̂} v`. Soundness (⟸) is unchanged: every `T̂`
rule is a `G_T`-equality (rotations are conjugates; `M1 = X0` is `ψ`-checkable in one line:
`ψ(X0) = X·X⁻¹M1 = M1`). The content is ⟹, via §2–§4.

## 2. The oriented system `R̂`

Orient the nine rules:

```
r1: X0 → M1                          (the collision rule)
d1: ⟨M1⟩ → ε    d2: M1⟩⟨ → ε    d3: 1⟩⟨M → ε    d4: ⟩⟨M1 → ε
e1: ⟨X0⟩ → ε    e2: X0⟩⟨ → ε    e3: 0⟩⟨X → ε    e4: ⟩⟨X0 → ε
```

**Termination:** measure `(length, #X)` lexicographically. The eight deletion rules drop
length by 4 (deletions can juxtapose new letters — e.g. `X·[⟨M1⟩]·0 → X0` — but length
governs first, so no matter); `r1` preserves length and drops the `X`-count. ∎

**Then Thue(`T̂`)-equivalence = `R̂`-joinability = equality of `R̂`-normal forms**, provided
`R̂` is locally confluent (Newman). Which brings us to the enumeration proper.

## 3. The enumeration = the critical pairs (Knuth–Bendix, hand-traced)

This is the promised ambiguity enumeration, and it lands in the standard formalism: every
parse ambiguity is an LHS overlap. Containments first: `X0` sits inside `e1`, `e2`, `e4`, and
each joins through the matching `d`-rule (`⟨X0⟩ →r1 ⟨M1⟩ →d1 ε` ✓, likewise `e2`/`d2`,
`e4`/`d4`). Proper overlaps, representative rows of the full table:

| overlap word | route A | route B | join |
|---|---|---|---|
| `⟨M1⟩⟨M1` | d1 → `⟨M1` | d4 → `⟨M1` | ✓ |
| `⟨M1⟩⟨` | d1 → `⟨` | d2 → `⟨` | ✓ |
| `M1⟩⟨M` | d2 → `M` | d3 → `M` | ✓ |
| `⟩⟨M1⟩⟨` | d4 → `⟩⟨` | d2 → `⟩⟨` | ✓ |
| `1⟩⟨M1⟩` | d3 → `1⟩` | d1 (or d4) → `1⟩` | ✓ |
| `X0⟩⟨X` | e2 → `X` | e3 → `X` | ✓ |
| `0⟩⟨X0` | e3 → `0` | r1 → `0⟩⟨M1` →d4 `0` | ✓ |
| `M1⟩⟨X0` | d2 → `X0` →r1 `M1` | e4 → `M1` | ✓ |
| `X0⟩⟨M1` | e2 → `M1` | d4 → `X0` →r1 `M1` | ✓ |
| `⟨M1⟩⟨X0` | d1 → `⟨X0` →r1 `⟨M1` | e4 → `⟨M1` | ✓ |
| `M1⟩⟨X0⟩` | d2 → `X0⟩` →r1 `M1⟩` | e1 → `M1⟩` | ✓ |
| `X0⟩⟨X0` | e2 → `X0` → `M1` | e4 → `X0` → `M1` | ✓ |

The `e`-family self-overlaps mirror the `d`-family rows verbatim (swap `M↦X`, `1↦0`, finish
with `r1` where needed). Two structural remarks worth recording:

- **Every mixed `d`/`e` overlap joins through `M1`, with `r1` as the unique mediator.** The
  orientation `X0 → M1` is precisely what completes the system; oriented the other way, the
  `d`-rows would need mediation instead and the count would be the same. Symmetric, but not
  accidental — a length-preserving rule must exist because `ψ(M1) = ψ(X0)` is a genuine
  collision between positive blocks.
- **Knuth–Bendix closes with ZERO new rules.** The "fifth rotation-like rule" I flagged as the
  residual risk **does not exist**. The bicyclic invariant found what was missing from the
  naive `T̂`; completion certifies nothing is missing from the corrected one.

Hand-traced flag: I enumerated overlaps by first/last-letter matching and believe the table
above is exhaustive up to the stated mirror symmetry, but a mechanical KB pass must recount —
this is check (a) in §7.

## 4. Completeness: the scar lemma and the readback

Convergence gives unique normal forms; completeness needs: **`ψ` is injective on
`R̂`-irreducible positive words.** Irreducible means: no `X0`, no `0⟩⟨X`, no rotation window
of `⟨M1⟩`.

**Scar inventory.** In `ψ(u)`, reduced, each marker leaves a residue determined by its context
in `u`. For `⟩` (block `1⁻¹M⁻¹⟨⁻¹`): left-cancellation consumes a preceding `1`, then `M`
(depth ≤ 2; depth 3 is `⟨M1⟩` = d1, forbidden); right-cancellation consumes `⟨`, then `M`,
then `1` (depth 3 is `⟩⟨M1` = d4, forbidden); the mixed maxima `M1⟩⟨` and `1⟩⟨M` are d2, d3,
forbidden. So the surviving scar is a **nonempty** middle window of the triple — one of
`1⁻¹M⁻¹⟨⁻¹`, `M⁻¹⟨⁻¹`, `1⁻¹M⁻¹`, `⟨⁻¹`, `M⁻¹`, `1⁻¹` — and the scar shape determines both
cancellation depths, hence exactly which letters of `u` were consumed. For `0` (block
`X⁻¹M1`): the `X⁻¹` **always** survives (a cancelling `X` before it is `X0` = r1, forbidden;
no other block exposes a trailing `X`, because exposure would require a fully-cancelling
window, i.e. a forbidden one); the tail `M1` is consumed exactly when `⟩` follows, and then
fully and automatically (`0⟩ ↦ X⁻¹⟨⁻¹`, the composite scar; `0⟩⟨ ↦ X⁻¹`; `0⟩⟨X` = e3,
forbidden — which is precisely what protects the composite scar's `X⁻¹`).

**Readback.** Reduced `ψ(u)` is an alternation of transcribed positive text and negative scar
runs. The claim is that the parse is deterministic, and here is the part I genuinely enjoyed:
**every parse ambiguity is killed by exactly one forbidden window** —

| ambiguity in the reduced image | resolving rule |
|---|---|
| `X⁻¹M1…`: is `M1` the `0`-tail, or transcribed `M`,`1` after `0⟩⟨`? | second parse needs `⟩⟨M1` — **d4** |
| adjacent scars `M⁻¹`+`⟨⁻¹` with no text between (`1⟩⟨…M1⟩`) | needs `⟩⟨M1` inside — **d4**, with **d1/d3** covering the sub-windows |
| scar run `1⁻¹M⁻¹⟨⁻¹`: one virgin `⟩`, or scars `1⁻¹`+`M⁻¹⟨⁻¹` from `⟩⟨M…1⟩`? | second parse contains `⟩⟨M1` — **d4** again |
| positive block `M1` vs positive block `X0` (the collision) | **r1** |
| composite scar `X⁻¹` followed by transcribed `X` | **e3** |
| full collapses (markers vanishing entirely) | **d1–d4, e1, e2, e4** by construction |

Necessity was already established mechanically (your probe's 26, the bicyclic invariant);
sufficiency is this table. The rotation-closure law and readback determinism are **the same
fact seen from two sides** — the rotations are exactly the boundary phases at which a marker
can vanish, so forbidding them is exactly what makes surviving scars parseable.

**Injectivity, assembled.** Induction on the number of markers in `u`: parse the leftmost
scar; its shape forces the consumed context letters (they are literally recoverable — consumed
left letters must be the matching suffix of `M1`, consumed right letters the matching prefix
of `⟨M1`, and the `0`-cases are forced as above); strip, recurse. Base case: marker-free
words transcribe literally, and nonempty irreducibles have nonempty images (scars are
nonempty). Hence distinct irreducibles have distinct reduced images. ∎ *(Honest flag: this is
the one paper-proof in this doc with residual case-analysis risk — the same species of risk
that produced S9, deposit-order, flip-pairing, and your length-filter. It reduces to a
bounded-window check and a length-bounded fuzz; see §7(b).)*

**M0, closed.** For positive `u, v`: `u =_{G_T} v` ⟹ `ψ(nf(u)) = ψ(nf(v))` (T̂-steps are
`G_T`-equalities, `ψ` an isomorphism) ⟹ `nf(u) = nf(v)` (injectivity) ⟹ `u ↔*_{T̂} v`.
With soundness, `≈_T = Thue(T̂)`. ∎ *(modulo §7 runs — now done, §9)*

## 5. Downstream deltas

**Endpoint lemma, upgraded from sketch.** Canonical codes contain no `X0` (constants occur
only as whole codes) and no rotation window (the boundary-substring argument from the P′ doc),
so canonical codes are `R̂`-irreducible — **each canonical code is its own normal form**, and
two canonical codes are `T̂`-related iff equal. Endpoint soundness now rests on convergence
rather than a bespoke argument.

**A decision procedure, free of charge.** `nf_T̂` is computable (convergent system), so the
auditor gains an *exact* equality test for the token layer — no more search-bounded Thue
checks on the data side. The fuzzer's oracle for `≈_T` becomes normal-form comparison.

**Formalization shape.** All three ingredients are Verus-friendly: termination is a lex
measure (`decreases (len, count_X)`); local confluence is a finite decidable case split over
the table in §3 — exactly the kind of thing to discharge by exhaustive `proof fn` over a
bounded window enumeration; injectivity is the one lemma with real induction, on marker count,
with the scar table as the case skeleton. And `thue.rs` is now fully unblocked with the base
**pinned**: junction decoupling takes `F(Σ∖{⟩,0})` and `ψ` as concrete instances, not
parameters.

## 6. What the freeness does NOT change

The rotation-closure law, the consequence-closure protocol, and the probe all stand — they
operate at whitelist level and their necessity proofs are unaffected. The bicyclic invariant
retires with honor: its job (showing naive `T̂` misses `⟩⟨M1`) is now a one-line `ψ`
computation (`ψ(⟩⟨M1) = ε`, but no naive rule fires), but it found the law first, and the
monoid-invariant technique goes in the toolbox. Law P′ itself is unchanged; what's proven here
is its M0 rung. The join with `Thue(R)` — Lemma 2 proper — remains the campaign.

## 7. Run before trusting (the two checks this doc owes)

**(a) KB recount.** Feed the nine oriented rules to a mechanical critical-pair pass; assert
every pair joins and no new rule is generated. My table is hand-traced; the mirror-symmetry
shortcut in §3 is exactly the kind of "obviously the same" step that has been wrong before.

**(b) Injectivity fuzz.** Enumerate all `R̂`-irreducible positive words up to length ~10 over
the active letters; assert `ψ`-images (freely reduced) are pairwise distinct, and that the
scar inventory of §4 is exhaustive (no reduced image exhibits a negative run outside the
inventory). Also: assert each of your probe's 26 derived tokens `ψ`-reduces to `ε` (or, for
two-sided pairs, to equal images) — tying the probe's output to the new base.

**(c) (cheap)** Re-run the canonical-code scan as an `R̂`-irreducibility assertion instead of
a window blacklist — same check, now with a principled definition.

## 8. Session ledger

| Item | Status |
|---|---|
| Marker–relator overlap (flagged risk) | DISSOLVED — second Tietze elimination, no relator remains |
| `G_T` | proven FREE ≅ `F(Σ∖{⟩,0})`; Adjan/Remmers demoted to M5(c) duty |
| `R̂` termination | proven (lex measure) |
| Critical pairs | all joinable, hand-traced; ZERO new rules — no fifth rule exists |
| Scar lemma + readback | proven at strong-sketch level; each ambiguity killed by a named rule |
| M0 (`≈_T = Thue(T̂)`) | CLOSED modulo §7(a),(b) — now run, §9 |
| Endpoint lemma | upgraded: canonical codes are their own normal forms |
| Auditor | gains exact `nf_T̂` oracle; three run tasks specced |
| Lemma 2 base layer | pinned concrete: free base + `ψ`; `thue.rs` unblocked |

---

## 9. MECHANICAL RUN (2026-07-04, this session — §7 executed; `tools/m0_check.py`)

Both owed checks RUN. **Both clean — and for the first time this week the fuzz did NOT hand back
a correction.**

**(a) KB critical-pair pass — CLEAN.** 35 critical pairs (overlaps + containments) over the nine
oriented rules; **0 non-joinable**; every overlap word has a UNIQUE normal form. So `R̂` is locally
confluent, hence (with the lex-termination measure) confluent — and Knuth–Bendix adds **zero new
rules**. §3's headline is mechanically confirmed: **the fifth rule does not exist.**

**(b) Injectivity fuzz — CLEAN at scale.** Enumerated all `R̂`-irreducible positive words up to
length 9 over `{⟨,⟩,M,X,0,1}`: **9,447,857 words, 9,447,857 distinct `ψ`-images, 0 collisions.**
The scar lemma / readback-determinism argument (§4 — the doc's flagged residual-risk proof) holds
across ~9.4M witnesses. Spot facts confirmed: `ψ(⟩⟨M1) = ε` (the bicyclic finding, now a one-line
free-group computation — the invariant retires as promised); `ψ(X0) = ψ(M1) = (M,1)` (the `r1`
collision).

**Honest note on the streak.** §4 was flagged as the one paper-proof with real case-analysis risk,
and the author explicitly "half-expected the fuzz to hand us a correction in the scar table's fine
print." It didn't — 9.4M clean. That is *evidence for*, not *proof of*, injectivity (a fuzz to
length 9 is not a proof), but it is the strongest such evidence in the thread and it found no
fine-print bug. **M0 stands at paper-strength + heavy mechanical corroboration.** The formal
`proof fn` (marker-count induction, scar-table case skeleton) remains the eventual ground truth.

Ledger update: §7(a) DONE (clean), §7(b) DONE (clean, 9.4M), §7(c) subsumed (canonical-code
irreducibility is now just `not has_redex`, already the fuzz's filter).
