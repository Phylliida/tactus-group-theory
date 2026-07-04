# The Semantic Finite Basis Problem
## Positivity for semantic rewriting groups, I — working notes

*Danielle + Claude, 2026-07-03. Status: research notes, paper-math only (nothing here is
formalized yet). Born from the H₂ non-finite-presentability discussion recorded in
`carrier-not-fp-plan.md`; sibling to the ZFC-group program (`AGENDA.md`) and the
overhead-reduction program (`../after-zfc-group.md`).*

---

## 1. The question

Fix a computable injection `f` from formulas of ZFC's language into **positive** words over a
finite alphabet (the "formula-flavored generators"), and let

> `Sem := { f(σ)·f(τ)⁻¹ : ZFC ⊢ σ↔τ } ⊆ F` (the free group on the alphabet).

**Semantic finite basis question.** Is there an encoding `f` and a FINITE `R ⊆ Sem` such that for
all sentences σ, τ:

> `f(σ) = f(τ)` in `G := F/ncl(R)`  ⟺  `ZFC ⊢ σ↔τ` ?

Completeness = `ncl(R)` reaches all of `Sem`; soundness = it never identifies codes of
non-equivalent sentences. Informally: a Higman-style group whose relators are **individually
theorems** — zero non-semantic scaffolding. If YES, this is the "self-contained ZFC group" of the
minimality discussion: a finitely presented group that IS a foundation of mathematics, every
relator a readable logical truth.

Context: the scaffolding-free carrier one first writes down (the Miller/Layer-0.5 CEER carrier) is
provably NOT finitely presentable — `H₂ ≅ ⊕_κ ℤ^(|κ|−1)` over the Lindenbaum classes κ, infinite
rank (see `carrier-not-fp-plan.md`; formalization of that theorem is a separate live arc). The
present question survives that obstruction because it allows ANY encoding and any abstract group.
As far as we know the question is open and unstudied.

---

## 2. Two intuitions that dissolve

### 2.1 Cancellation-collapse: schemas fit in single relators

With a prefix-compositional (Polish) encoding, `f(¬φ) = ¬·f(φ)` etc., the semantic relator for the
double-negation instance φ₀ freely reduces:

```
f(¬¬φ₀)·f(φ₀)⁻¹ = ¬¬·f(φ₀)·f(φ₀)⁻¹ = ¬¬
```

The instance cancels; the reduced element is instance-free, applies (via `ncl`) at every position
of every formula, and is *literally an element of Sem*. So "each relator individually semantic"
does NOT force instance-boundedness — one relator can carry a whole schema. This works for every
**tail-sharing** schema `C₁[φ] ↔ C₂[φ]` (same trailing subtree, same position): the relator
reduces to the pure "window rule" `w₁·w₂⁻¹` in structural letters.

What does NOT collapse: variable-permuting/duplicating schemas. ∧-commutativity's relator is
`∧f(σ₀)f(τ₀)f(σ₀)⁻¹f(τ₀)⁻¹∧⁻¹` — instances survive. Such schemas must be *simulated by walks*
(machine-style), not asserted.

### 2.2 Transparent guards: machine states can be semantic

A rewriting machine needs head/state markers; markers must be formula material (any relator
mentioning a non-formula letter is not in `Sem`). Logic supplies **semantically transparent,
syntactically visible** material: contexts `K` with `K[φ] ↔ φ` provable for all φ (`⊤∧·`,
`(χ→χ)→·`, `·⊕C` for `C ≡ ⊥/0`, …), pairwise distinguishable as strings.

Crucial subtlety: the transparency schema itself must NEVER be a relator — `φ ↔ K[φ]` has one side
a suffix of the other, so its relator is the guard word itself, forcing `k = 1` and erasing the
marker. Include only **motion/transformation** rules for guards (e.g. `K[¬φ] ↔ ¬K[φ]`, provable,
tail-sharing, collapsing to `k¬ = ¬k`). Guards then function as honest tape/state letters.

---

## 3. The poison: what the group adds beyond Thue rewriting

`ncl(R)`-membership is derivability by subword replacement (conjugation = context) plus free
cancellation. The group forcibly closes the congruence under cancellation and all Malcev
quasi-identities — and this over-closure is the entire soundness risk.

### 3.1 Finding A: absorption (first counterexample)

`∀x∀xφ ↔ ∀xφ` is provable (vacuous requantification), tail-sharing, collapsing to `qq = q` for the
`∀x`-letter — whence `q = 1` in `G`, asserting the FALSE schema `∀xφ ↔ φ`. One innocent truth
kills soundness. Generalization: **a connective may serve as a bare generator only if its semantic
action on Lindenbaum classes is injective** (`¬` ✓, transparent guards ✓, quantifiers ✗ — the
above IS the failure of left-cancellativity `∀xP(x) ~ ∀x∀xP(x)`, `P(x) ≁ ∀xP(x)` realized).

### 3.2 The Boolean collapse theorem (evaluation is poison too)

0-atom sandbox: closed formulas over `⊤,⊥,¬,∧`, Polish letters `{t,b,¬,∧}`, and the six
leaf-evaluation relators (each a genuine equivalence of closed formulas):

```
¬t = b,  ¬b = t,  ∧tt = t,  ∧tb = b,  ∧bt = b,  ∧bb = b.
```

**Theorem.** This group is `ℤ` and it satisfies `⊤ = ⊥`; all closed formulas become equal.

*Proof.* `∧tt = t` right-cancels to `∧ = t⁻¹`. Rule 5 becomes `t⁻¹¬tt = ¬t`, i.e. `¬t = t¬`.
Rule 6 becomes `t⁻¹¬t¬t = ¬t`; commuting, `¬¬t = ¬t`, so `¬ = 1`; rule 1 gives `b = t`. Every
code now has value `t¹` in `⟨t⟩ ≅ ℤ`. ∎

Moral: evaluation is many-to-one — maximally irreversible — and the group punishes irreversibility
instantly, already at depth zero. The machine paradigm is forced even for constants.

### 3.3 Poison taxonomy and the hygiene discipline

All observed failures are one phenomenon: *whatever survives free cancellation between a relator's
two sides becomes an unintended definition.*

1. **Suffix-shared absorption** `u·w = w` ⟹ `u = 1` (the `∀x∀x` poison).
2. **Prefix-shared padding** `u = u·w` ⟹ `w = 1` (kills schema-level guard insertion).
3. **Shrinking definitional cascade** (`∧tt = t` ⟹ `∧ = t⁻¹` ⟹ dominoes).

Same coin as §2.1: cancellation is the schema-generalizer AND the soundness-destroyer.

**Affix-hygiene discipline** (mechanically auditable per candidate `R`):
(a) each relator's two sides are affix-disjoint, so its free reduction IS the intended window and
nothing more; (b) cross-relator shared subwords ("pieces") are confined within single guard-chunk
boundaries (arrange the guard chunks as a comma-free code of long strings — see §6.2).

### 3.4 Design consequences

- **Reversibility reframe.** Generators must act injectively; the machine should be a reversible
  computer (Bennett). Proof *search* becomes reversible proof *replay*: run inside `σ ∧ Θ` /
  `σ ⊕ Θ` with Θ transparent history material — every configuration is a formula provably
  equivalent to σ, so every step is semantic by construction; histories are Bennett-uncomputed so
  the derivation terminates at literally `f(τ)`.
- **The boot problem and the wrapper.** Guard insertion as a schema is poison (taxonomy 2), so the
  ENCODING absorbs the boot: define `f(σ) := code(E[σ])` for a fixed transparent wrapper `E`.
  Every code is born guarded; no insertion schema ever needed.
- **Length changes** (σ, τ of different sizes) go through affix-disjoint state rules
  ("mint/retire a blank guard"), permitted by the taxonomy.

---

## 4. The M-ladder: minimal positivity theorems (PROVEN)

Notation: for a rule set `R` of positive-word pairs, the **Thue congruence** is generated by
subword replacement among positive words; **positivity** for `R` means: for positive `u,v`,
`u = v` in `G = ⟨alphabet | R⟩` iff `u ↔*_Thue v`. Positivity is exactly the statement "the free
group adds no shortcuts" — our Britton-substitute, in each fragment.

### 4.1 M1 — guard motion

`R = {gn = ng}` over `{g,n,a,b}`. Then `G = F(a,b) ∗ ℤ²`; free-product normal form shows two
positive words are equal iff same data-letter ("wall") sequence and same per-gap `(#g,#n)` — which
is precisely the Thue congruence. **Positivity holds.** ∎

### 4.2 M2 — one read/translate rule (tree-shaped control)

`R = {qa = bq′}`, all four letters distinct. (One machine step: read `a`, write `b`, move right,
state `q → q′`.)

*Monoid side:* orient `bq′ → qa`; no critical pairs, `#q′` strictly decreases ⟹ finite complete
rewriting system; normal forms = positives with no `bq′` substring.

*Group side:* Tietze-eliminate `q′ = b⁻¹qa`, so `G ≅ F(q,a,b)`, and `G`-equality of positive words
is equality of substituted images (`sub: q′ ↦ b⁻¹qa`, other letters fixed) in the free group.

*Readback:* in `sub(w)` for irreducible `w`, a `b⁻¹` arises only as the first letter of
`sub(q′)`, and can only cancel against a *literal* preceding `b` — i.e. substring `bq′`, excluded.
So images of irreducibles are reduced as written and parse back uniquely (`b⁻¹` flags `q′`).
`sub` is injective on irreducibles. **Positivity holds.** ∎

### 4.3 M3 — THE BLINKER (first control loop)

`R = { qa = bq′, q′a = bq }` — the head toggles state each step. Tietze elimination no longer
yields a free group; this is the critical test.

*Thue side:* orient both left-to-right; no critical pairs, `#a` decreases ⟹ complete; normal
forms = positives where **no state letter is immediately followed by `a`**.

*Group side:* eliminate `q′ = b⁻¹qa`; the second relator becomes `qa² = b²q`:

> `G ≅ ⟨ a, b, q | q a² q⁻¹ = b² ⟩` — an **HNN extension of `F(a,b)`**, stable letter `q`,
> associated subgroups `⟨a²⟩ → ⟨b²⟩`.

The eliminated control cycle *became a stable letter*. Britton's lemma — the very tool the
classical constructions install police letters to enable — applies to the police-free group
because the machine's loop manufactures the HNN structure intrinsically.

**Theorem (M3 positivity).** The positive trace of `ncl(R)` equals the Thue congruence.

*Proof.* Write a positive `u = w₀ s₁ w₁ ⋯ sₖ wₖ` (`sᵢ ∈ {q,q′}`, `wᵢ ∈ {a,b}*`). Substituting
`q′ ↦ b⁻¹qa` gives `sub(u) = g₀ q g₁ q ⋯ q gₖ` with syllables

```
gᵢ = a^{εᵢ} · wᵢ · b^{−δᵢ₊₁},   εᵢ = [sᵢ = q′],  δᵢ₊₁ = [sᵢ₊₁ = q′]
```

(ε₀ := 0 for the 0th syllable; δ beyond the last is 0). All stable letters occur positively, so no
pinches exist and both expressions are Britton-reduced. For `sub(u) = sub(v)`, `q`-exponent count
forces equal `k`; the Britton pinch cascade on `sub(u)·sub(v)⁻¹` yields compensations
`dᵢ = a^{2mᵢ} ∈ ⟨a²⟩` with

```
hᵢ = a^{−2mᵢ} · gᵢ · b^{2mᵢ₊₁}      (m's at junctions 1..k; m₀ = mₖ₊₁ = 0).
```

Now the mechanism. If `u, v` are Thue-irreducible, each `wᵢ` (i ≥ 1) is empty or starts with `b`,
so **every reduced syllable begins with `a`-exponent `εᵢ ∈ {0,1}`** — including all degenerate
cases (`gᵢ ∈ {1, a, a^ε b^j, …}`: right-multiplication by `b`-powers never affects the `a`-head,
and internal cancellation `w b^{−δ}` only shortens `b`-tails). A nonzero compensation shifts
syllable `i`'s head by the even amount `−2mᵢ`; from `{0,1}` any even shift exits `{0,1}` (the
`±1` escapes are blocked by parity, absorption into interior letters by the codes' positivity and
the `b`-type letter following the head). Hence **all `mᵢ = 0`**: the tuples are literally equal.
Heads then read back the state sequences (`εᵢ` recovers `sᵢ`, hence also every `δ`), after which
the data blocks match: `wᵢ = w′ᵢ`. So `sub` is injective on irreducibles; with confluence on the
Thue side, positivity follows. ∎

**The structural point.** The associated subgroup has granularity 2 because the control cycle has
length 2 (one loop consumes two `a`s); the head cap is 1 because "state never followed by `a`" is
the machine's own normal-form discipline — the unconsumed window letter. *The margin that defeats
the free group's sliding moves is exactly the machine's operational invariant.* The classical
police letters were scaffolding for this alignment; here it arises intrinsically.

### 4.4 M4 — mixed transduction (mixed cycle words): defect flow

`R = { qa = bq′, q′b = aq }` — right-mover transducing `a→b` in state `q`, `b→a` in state `q′`.
(Label correction vs the first draft: this is not direction reversal — both rules move right —
it is the smallest system whose *cycle word is mixed*. True left-movers are deferred to M5′.)

*Thue side:* orient left-to-right; state letters move strictly right ⟹ terminating; no critical
pairs ⟹ complete. Irreducibles: **no `qa` and no `q′b`** — the follow-constraint is now
state-dependent (`a` forbidden after `q`, `b` forbidden after `q′`).

*Group side:* eliminating `q′ = b⁻¹qa` turns the second relator into `qab = baq`:

> `G ≅ ⟨ a, b, q | q(ab)q⁻¹ = ba ⟩` — HNN of `F(a,b)`, associated subgroups `⟨ab⟩ → ⟨ba⟩`,
> **mixed** cycle words. Compensations: `hᵢ = (ab)^{−mᵢ} gᵢ (ba)^{mᵢ₊₁}`.

**The new phenomenon.** The M3 head-cap argument FAILS locally: because `wᵢ` may start with `a`
after `q′`, syllable heads are unbounded, and there is a genuine *local masquerade* — with
`mᵢ = 1`, the `u`-syllable `a` (from adjacent `…q′q…`) maps exactly to the `v`-syllable `b⁻¹`
(from adjacent `…qq′…`): `(ab)⁻¹·a = b⁻¹`. The group locally "tries" to commute the resting head's
phase, `q′q ↔ qq′`. Compensations are no longer locally impossible — only **globally
inconsistent**.

**Theorem (M4 positivity).** The positive trace of `ncl(R)` equals the Thue congruence.

*Proof shape (defect flow).* Case analysis on the reduced form of `(ab)^{−mᵢ}gᵢ(ba)^{mᵢ₊₁}`
against the constrained syllable shapes (`P` or `P·b⁻¹`, `P` positive, with the state-dependent
start constraint) gives three forced lemmas:
1. `mᵢ < 0` is impossible (it prepends positive `ab…`, forcing an `h`-syllable with `s′ᵢ = q′`
   whose data starts with `b` — forbidden).
2. `mᵢ ≥ 2` is impossible (≥ 3 uncancellable negative letters: after the single `a`-head cancels,
   the next junction pits `b⁻¹` against a non-`b`-start `wᵢ`).
3. `mᵢ = 1` forces the exact masquerade: `gᵢ = a` (`sᵢ = q′, wᵢ = ε, sᵢ₊₁ = q`),
   `hᵢ = b⁻¹` (`s′ᵢ = q, w′ᵢ = ε, s′ᵢ₊₁ = q′`), and `mᵢ₊₁ = 0`.
Then the propagation analysis: a defect at junction `i` forces `mᵢ₊₂ = 1` with syllable `i+1`
empty on both sides (`u = ⋯q′qq′q⋯` vs `v = ⋯qq′qq′⋯`, pure alternating state runs) — any data
letter in the run yields an `a`-start after `q` on one side, contradiction. So the defect **flows
rightward through state-only material and cannot stop**; at the right boundary (`m_{k+1} = 0`
by definition) the final equation `hₖ = (ab)^{−1}gₖ` demands a positive syllable equal to
`b⁻¹wₖ` — impossible. Hence all `mᵢ = 0`, tuples equal, states and data read back as in M3. ∎

**Structural lessons.** (i) The general positivity condition is not purely local: it is local
caps *plus a boundary-discharge argument* — compensation defects are conserved, forced to
propagate, and annihilated only at word ends. Very machine-flavored: the group's cheat attempt
behaves like a particle that must exit through the boundary and can't. (ii) Corollary warning:
on **circular** words the defect could cycle forever — conjugacy-positivity may fail where
equality-positivity holds. Our target (the word problem on codes) only needs equality. (iii) The
masquerade defect has semantic meaning: the group attempts to identify the two rest-phases of the
head (`q′q` vs `qq′`); the machine's state discipline plus finite word length refuses it.

### 4.5 M5′ — two-way motion: return-collapse, head-passing, and the shuttle theorem

**Phenomenon 1 — the return-collapse law.** Two-way motion enables closed head trajectories.
Micro-example: `{qa = bq′, bq′ = q″a}` (step right, step back left) has the Thue consequence
`qa ~ q″a`, whose collapsed relator is `q = q″`. General law: **if the machine can connect two
configurations with identical tape and head position but different states, the group identifies
the state chunks.** For transparent guards this identification is semantically SOUND but
control-fatal — a new failure category: *friendly fire* (consequences that respect the Lindenbaum
congruence but destroy the machine's state discipline, after which unintended transitions may
cascade into genuine unsoundness). Design law: **trajectory-injectivity** — no two states
connected by a net-trivial trajectory; enforced by transduce-on-turn (walls change flavor:
`qW = rW′` with `W ≠ W′`, never `qW = rW`) and phase/zone discipline. One-way systems (M2–M4)
satisfied it vacuously.

**Phenomenon 2 — head collisions = critical pairs; completion = head-passing.** With left- and
right-movers, LHSs overlap (`q·a·r`): Knuth–Bendix completion adds head-passing rules. These are
Thue-consequences (congruence unchanged) and group-consequences (immediate), so positivity may be
proven against the completed system.

**The shuttle core.** `R = { qa = bq, ar = rb }` — a right-mover `q` and a left-mover `r`, both
transducing `a→b`. Completion: the overlap `qar` gives exactly one critical pair, joined by the
head-passing rule; `{qa→bq, ar→rb, bqr→qrb}` is complete (lex measure: `#a`, then state-letter
position sum). Irreducibles: no `qa`, `ar`, `bqr`.

*Group side:* `b = qaq⁻¹` and `b = r⁻¹ar` give `G = ⟨a,q,r | qaq⁻¹ = r⁻¹ar⟩`; substituting
`s := rq` turns the relator into `[s,a] = 1`:

> `G ≅ ℤ²(a,s) ∗ F(q)` — a **free product**; no HNN sliding at all. The head-passing/completion
> rule `bqr = qrb` is, on the group side, precisely the commutator `[s,a]`:
> `sub(bqr) = q(as)q⁻¹ = q(sa)q⁻¹ = sub(qrb)`. **Knuth–Bendix completion on the Thue side = the
> commutation structure of the group.** (Dictionary entry.)

**Theorem (M5′ positivity, proof at sketch+spot-check rigor).** The positive trace of `ncl(R)`
equals the Thue congruence. *Proof architecture:* free-product normal forms in `ℤ² ∗ F(q)` under
`sub: a↦a, q↦q, b↦qaq⁻¹, r↦sq⁻¹`; the parsing ambiguities of a normal form are in bijection with
the three rules — `sub(bq)` merges to a `qa`-shape (`qa` forbidden in irreducibles ⟹ reads back
as `bq`), `sub(ar) = sub(rb) = (as)q⁻¹`-shape (`ar` forbidden ⟹ reads back as `rb`), and the
`ℤ²`-commutation ambiguity is exactly `bqr` vs `qrb` (`bqr` forbidden ⟹ reads back as `qrb`).
Every NF-ambiguity is one rule, always resolved to the irreducible side; injectivity on
irreducibles follows by syllable-wise parsing. Spot-checked collision families:
`arq ~ rqa` (both ⇝ `rbq` ✓), `arqrq ~ rqarq` (both ⇝ `rqrbq` ✓), `bqⁿ` (unique preimage of
`qaq^{n-1}` since `qa…` is reducible ✓). The full case enumeration is mechanical; flagged for a
complete write-out (or SAT-audit) later. ∎(sketch)

**Lessons.** (i) Two-way motion produced no dragon — instead the *group got tamer* (free product
vs HNN), because the composite cycle `s = rq` acts trivially on the data it slides past.
(ii) The completion/commutation dictionary suggests the general soundness proof should be stated
against the completed rule set, with group structure mirroring the completion's geometry.
(iii) The return-collapse law is the first constraint that binds the OPCODE DESIGNER rather than
the prover — it goes into the Probe 0 instruction-set discipline next to affix hygiene.

---

## 5. The general program

### 5.1 Cycle-Britton route (primary)

For a machine with state graph Γ: eliminate a spanning tree of Γ — one stable letter per
independent cycle — landing in an iterated HNN over `F(data)` whose associated subgroups are
generated by the **cycle words** (data-translation products around each control loop).

> **Conjecture (head-cap positivity).** If every nontrivial element of every associated subgroup
> has head-weight exceeding the Thue-irreducibility cap of the rule set, then positivity holds
> (multi-stable-letter Britton, syllable-shape argument as in M3).

The hypothesis is finitely checkable per machine. Note: Britton's lemma — including a
predicate-base version — is already fully machine-verified in this crate (`britton_lemma_full`,
`pred_britton_via_tower`), so the eventual formalization of this route has its engine banked.

### 5.2 Small-cancellation route (fallback)

Realize guard chunks as long comma-free codes so that cross-relator pieces are short relative to
relator length: `R ⊆ C′(1/6)`. Greendlinger's lemma then makes every nontrivial element of
`ncl(R)` contain more than half a relator — "derivations are locally rule-visible" — and the
positivity statement should follow by a small-cancellation version of Remmers' semigroup-diagram
technique (the geometry behind Adjan's embedding theorem). Blunter than §5.1 but rule-shape-robust.

### 5.3 Probe 0 target (propositional sandbox)

Language `{⊕, ∧, 1, 0}` with stroke-coded atoms — so Probe 0 is: *present the free Boolean ring's
equality as the positive trace of a f.p. group with semantic relators.* Machine: reversible
normalizer/replay to sorted ANF (Zhegalkin) — AC-sorting is sorting-network-shaped, reversible-
friendly; `x∧x → x` and `M⊕M → 0` are guarded multi-step walks (never naked schema relators).
Opcode families: guard motion; read/translate (M2/M3 shapes); compare/copy stroke-walks;
mint/retire blanks; finitely many concrete anchors (guard-hygienically padded). Lemma 1
(completeness) = machine engineering. Lemma 2 (soundness) = §5.1/§5.2 applied to the opcode set.
Payoff if it lands: **"the group of Boolean logic"** — every relator a readable tautology, word
problem on codes = propositional equivalence (co-NP-hard; the group is the proof system). A paper
in itself, and the Proof Factory tutorial world.

### 5.4 Escalation ladder (next steps)

- ~~M4 — mixed cycle words~~ **DONE, positivity holds** (§4.4; new global defect-flow mechanism).
- ~~M5′ — two-way motion~~ **DONE, positivity holds** (§4.5; return-collapse law, head-passing =
  completion = commutation, shuttle group = `ℤ² ∗ F(q)`). Full readback enumeration still to be
  written out mechanically.
- **M5 — mint/retire** (length-imbalanced rules): associated-subgroup elements of unequal lengths.
- **M6 — data-carrying states** (copy walks): state chunks per transported letter; many cycles.
- **M7 — two interacting loops** (two stable letters): first multi-HNN defect interaction.
- Then: assemble Probe 0's full opcode audit; prove Lemma 2 for the actual instruction set.

---

## 6. Literature anchors

Nearest neighbors (none answering the question): Adjan/Remmers cycle-free semigroup-in-group
embeddings; special monoids (Adjan, Makanin); Squier's homological finiteness obstructions (the
model for what a NO-proof would look like); Guba–Sapir diagram groups / Squier complexes (the
model machinery for derivation spaces); inverse-monoid presentation theory, E-unitarity
(Margolis–Meakin; one-relator inverse monoids, Ivanov–Margolis–Sapir); Bennett's reversible
computing; and the classical Novikov–Boone–Higman/Aanderaa–Cohen constructions whose *non-semantic*
scaffolding this program attempts to shed. The Miller-carrier H₂ theorem (sibling arc) shows the
naive carrier fails for homological reasons; nothing in the literature we know addresses finite
*semantic* bases.

## 7. Open problems

1. Head-cap positivity conjecture (§5.1) — prove for M4–M6 shapes; find the general statement.
2. Does SOME finite semantic basis exist for full propositional equivalence (Probe 0)?
3. The ZFC lift: does anything in §3–§5 obstruct at Σ₁-complete congruences? (No obstruction
   currently known; the skeleton is logic-agnostic.)
4. NO-direction: a Squier-style invariant separating finitely-semantically-based congruences from
   the Lindenbaum congruence — even a propositional-level obstruction would be a striking theorem.
5. Quantitative: if Probe 0 lands, how small is the Boolean-logic group? (Relator count and total
   symbols; compare the minimality discussion for the ZFC group.)
