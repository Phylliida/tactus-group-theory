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

### 3.5 The Laws of Semantic Machines (consolidated design discipline)

All mechanically auditable on a candidate `(f, R)` except Law P, which is the research theorem.

- **Law 0 — cycle-relator principle** (the master law): Tietze elimination turns every control
  cycle's NET EFFECT into a relator. The relator set the group actually sees = intended windows ∪
  cycle net-effects. Design so these coincide: audit the state graph's cycles, not just the rules.
- **Law 1 — affix hygiene:** each relator's two sides affix-disjoint (its free reduction IS the
  intended window); cross-relator pieces confined to guard-chunk boundaries (comma-free guards).
- **Law 2 — no absorption, injective actions:** no `uw = w` / `u = uw` shapes anywhere in the
  consequence-closure of the intended instruction algebra; generators act injectively on classes
  (reversible-machine discipline; evaluation only via replay with history).
- **Law 3 — trajectory-injectivity** (Law 0 instance): no two states connected by a net-trivial
  trajectory; turns must transduce (`qW = rW′`, `W ≠ W′`).
- **Law 4 — mint must move** (Law 0 instance): minting/retiring cycles have nonzero net head
  displacement (stationary pumps force `h = g⁻¹`).
- **Law 4′ — anchored erasure** (Law 0 instance, from §6.3): erasure/absorption cycles must
  straddle an anchor so their net cycle-relator stays state/anchor-carrying, never data-only —
  cycles LAUNDER certificates (`{|s = s′, |s′ = s}` nets `|| = 1`, poison, despite both rules
  being individually hygienic and semantically witnessed).
- **Law 5 — boot via encoding:** guard insertion lives in the wrapper `E` inside `f`, never in `R`
  (schema-level insertion relators trivialize the guard).
- **Law P — positivity** (the theorem, not an audit): the group trace on positive words equals
  the Thue congruence. Proven mechanisms so far: §4; general routes: §5.1, §5.2.
- **Law P′ — two-layer positivity** (`docs/law-p-prime.md`, 2026-07-04): when the machine has a
  witnessed whitelist `T` of data-only ε-tokens, plain positivity is FALSE (state-free words are
  Thue-inert but `⟨M1⟩ = ε` in `G`). Correct statement: `u = v` in `G` ⟺ `u ~ v` under
  `Thue(R) ∨ ≈_T`, with `≈_T` a finite Thue congruence `T̂` (the **M0 rung**, below M1). Two
  laws fell out, both mechanically confirmed: **consequence-closure** (the whitelist must contain
  derived tokens — e.g. `M1 = X0` from `{⟨M1⟩,⟨X0⟩}`, itself the collapsed schema `1∧u ↔ 0⊕u`,
  witnessed) and **rotation-closure** (whitelist tokens are CYCLIC words; naive `T̂` refuted by a
  bicyclic-monoid invariant, `⟩⟨M1 ↦ qp ≠ ε`). `positivity_mod(rules, toks)` generalizes Law P;
  plain positivity = empty token list.

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

> **✅ FORMALIZED — `src/m3_blinker.rs` 124/0 (2026-07-06).** `lemma_m3_positivity : positivity(m3_rules(), 4)`,
> both directions. The paper proof below is the route; formalization notes: `ffnf` fires `bq′→qa` (a Thue move) so
> `sub` is reduced; `rep=gap` (b-coset rep of an nf gap is the gap); `act_syls` = Britton normal form; the leading
> base is recovered by right-cancellation, base-faithfulness by the banked `britton_lemma_unconditional`.

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

**Theorem (M5′ positivity; proof completed in §4.5.1).** The positive trace of `ncl(R)`
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

#### 4.5.1 M5′ readback, full enumeration (debt paid — upgrades §4.5 to a complete proof)

**Item-walk model.** `G ≅ ℤ²(a,s) ∗ ⟨q⟩`; represent normal forms as reduced walks: moves
`U` (=q), `Dn` (=q⁻¹) and deposits in `ℕ²∖0` (components = (a-count, s-count)). Letter images:
`a: dep(1,0)`; `q: U`; `b: U·dep(1,0)·Dn`; `r: dep(0,1)·Dn`. Reduction: adjacent opposite moves
with nothing between cancel; adjacent deposits sum. **All deposits are strictly positive, so
deposits never vanish** — the only reductions are move-cancellations. Reduced walks = free-product
normal forms (maximal move-runs = q-syllables, deposits = ℤ²-syllables).

**Run images** (`n ≥ 1`): `a^n ↦ dep(n,0)`; `q^n ↦ Uⁿ`; `b^n ↦ U·dep(n,0)·Dn` (b|b telescopes);
`r^n ↦ (dep(0,1)·Dn)ⁿ` (no internal reduction).

**Junction table** (only nontrivial entries; all others concatenate cleanly):
`B|Q`: b-tail `Dn` cancels one `U` — for q-run length 1 the elevated deposit is exposed to the
next run; `R|Q`: r-tail `Dn` cancels one `U` — exposes `dep(0,1)`; `R|B`: r-tail `Dn` cancels
b-head `U`, deposits merge to `dep(n,1)·Dn`; cascades chain through `q¹`-runs only
(`rq¹rq¹… ↦ dep(0,c)`-chains; `q¹rb^n ↦ U·dep(n,1)·Dn`).

**Deterministic parser** (deposit context `(a-comp n, s-comp c, prev move, next move)` → run
readback; move-run lengths recover q-run lengths):

| context | reads back as |
|---|---|
| `dep(n,0)`, prev ∈ {start, Dn}, next ∈ {U, end} | `a^n` |
| `U^j·dep(n,0)·Dn` | `q^{j−1} b^n` |
| `U^j·dep(n,0)·U^t` (t≥1) | `q^{j−1} b^n q^{t+1−1}`-split, i.e. `q^{j−1} b^n q^{t}` with one U consumed |
| `dep(n,c≥1)·Dn` (prev ∉ U-elevation of a b) | `(rq)^{c−1} r b^n` |
| `dep(n,c≥1)·U^t` (t≥0, then next run) | `(rq)^{c−1} r b^n q^{t+1}` |
| `U^j·dep(n,1)·Dn` | `q^{j−1}·q¹ r b^n` (i.e. `q^j r b^n`) |

**The ambiguity ⇄ rule bijection** (why the parser is well-defined exactly on irreducibles):
each would-be double-reading is precisely one rule of the completed system, with the reducible
side excluded:
1. `qa` forbidden ⟺ a-deposits never merge across a cancelled `q¹` (kills the `…q¹a` reading;
   Thue-equivalent reading `…bq`-side survives).
2. `ar` forbidden ⟺ a-run deposits never acquire s-components rightward (kills `a^n r…`; the
   `r b^n`-side survives via the R|B merge).
3. `bq¹r` forbidden ⟺ the elevated pattern `U·dep(n,1)·Dn` has the UNIQUE reading `q¹ r b^n` —
   the excluded reading `b^n q r` is its head-passing partner (`bqr ~ qrb`), i.e. **the parser's
   last ambiguity is literally the completion rule.**
Hence `sub` is injective on irreducibles; with confluence, M5′ positivity is fully proven. ∎

### 4.6 M5 — mint/retire (length-imbalanced rules): the cycle-relator principle, and monsters that aren't dragons

**The cycle-relator principle (unifying law).** Tietze elimination makes every control cycle
contribute its NET EFFECT as a relator/associated word. Consequences already seen and new:
- M5′ return-collapse: cycle with net effect "state swap" ⟹ state identification.
- **Stationary pump poison:** `{q = pg, p = qh}` (mint in place, return) ⟹ `q = qhg` ⟹ `hg = 1`
  ⟹ `h = g⁻¹`: minted letters collapse to mutual inverses. Law: **mint must move** — minting/
  retiring cycles need nonzero net head displacement. (Sibling of trajectory-injectivity; both are
  "a cycle's collapsed relator is its net effect, and net effects must be intended instructions.")

**(a) Mint-with-motion** `{qa = gbq}` (read `a`, write `gb`, move): `G = HNN(F(a,b,g), q, ⟨a⟩→⟨gb⟩)`
— unequal-length associated words. Positivity holds by the cleanest head-cap yet: irreducibles
forbid `qa`, so syllables never start with `a`; a compensation `a^{−m}` with `m>0` leaves negative
letters (nothing to cancel into a non-`a`-start), with `m<0` creates an `a`-start; each junction is
pinned at the left edge of its right-hand syllable. All compensations vanish. ∎

**(b) The doubler** `{qa = a²q}` (duplicate transparent material while walking — semantically
legal: `σ⊕C ~ σ⊕C⊕C` for guard `C ≡ 0`): affix-disjoint, hygienic, and

> `G = ⟨a,q | qaq⁻¹ = a²⟩ = BS(1,2)`.

**Theorem.** Positivity holds for the doubler. *Proof (complete, short):* the affine
representation `a ↦ (t↦t+1)`, `q ↦ (t↦2t)` is faithful (`BS(1,2) ≅ ℤ[1/2] ⋊ ℤ`); a positive word
maps to `t ↦ 2^m t + N` with `m = #q` and `N = Σ_{a's} 2^{#q's to the left}` — exactly the Thue
invariant of `qa → a²q`; the normal form `a^N q^m` is determined by `(m, N)`. ∎
(`⟨a⟩` is exponentially distorted here — doubling walks are where exponential overhead lives,
consistent with the after-zfc-group discussion; soundness is unaffected.)

**(c) The ratio rule** `{qa² = a³q}` (2 guards ↦ 3 guards — semantically legal for `C ≡ 0`
bookkeeping): affix-disjoint, hygienic, and `G = BS(2,3)` — **non-Hopfian, non-residually-finite,
the canonical pathology.** Yet positivity holds: the presentation is Adjan cycle-free (left graph
edge `q–a`, right graph edge `a–q`, no cycles), so by **Adjan's embedding theorem** (Remmers'
geometric proof) the positive monoid embeds in the group. *The ambient group's pathology does not
leak into the positive trace.* Monsters are not dragons — twice over. (Adjan/Remmers is hereby
unlocked as a direct tool for cycle-free opcode shapes; §5.2's small-cancellation route is its
generalization for the non-cycle-free ones.)

**Lessons.** (i) Length imbalance per se is harmless (a) — even with self-reference (b) and
non-Hopfian ratios (c). (ii) The dangerous thing about mint/retire is only the stationary loop —
a design law, mechanically checkable on the state graph (cycle net-displacement ≠ 0). (iii) The
ANF machine's copying walks (which need doubling) are cleared. (iv) The group-theoretic wildness
of the ambient group (distortion, non-Hopficity) is orthogonal to trace-soundness — the program
does not need tame groups, only tame *traces*.

### 4.7 M6 — data-carrying states: couriers and unforgeable markers

**(a) The courier** (one carried datum): `R = { qa = p, pw = wp }` — pickup ("eat the `a`, hold
it" — a legal *definitional* shrink: affix-disjoint, `p` defined by rule 1) + carry (slide over
walls). Thue-symmetry gives drop for free (pickup reversed), so `qaww ~ wwqa`: transport works
with two rules. Complete system: `{qa→p, pw→wp}`, no critical pairs; irreducibles: no `qa`, `pw`.

*Group:* eliminate `p = qa`, set `u := qa`: `G = ⟨u,w | [u,w]⟩ ∗ ⟨a⟩ = ℤ² ∗ ℤ`, with the new
wrinkle that a GENERATOR has a cross-factor image: `q ↦ u·a⁻¹`.

**Theorem (courier positivity — complete).** Free-product NF as walk of ℤ²-blocks `(u-exp,
w-exp)` and `a`-syllables. Letter images: `a ↦ a`, `w ↦ (0,1)`, `p ↦ (1,0)`, `q ↦ (1,0)·a⁻¹`.
Positive words produce negative `a`-material ONLY via `q` — and always as isolated `a⁻¹`
(never mergeable: `qa` forbidden on one side, blocks separate `q`s on the other). So **`a⁻¹` is
an unforgeable `q`-marker**: parse = subtract `(1,0)` from the preceding block per marker; block
`(i,j)` reads `w^j p^{i}` (unique ordering since `pw` forbidden); sign of the `a`-syllable
distinguishes `p·a^k` from `q`. Each parse ambiguity is a rule (`qa`: the `a⁻¹a`-cancellation;
`pw`: block-order); irreducibility excludes exactly one side. ∎

**(b) The double courier** (two carried data sharing a wall): `R = {qa = p, qb = s, pw = wp,
sw = ws}`. Eliminating `u := qa, v := qb` (so `q = ua⁻¹`, `b = au⁻¹v`):

> `G = (F(u,v) × ℤ(w)) ∗ ℤ(a)` — the first **non-free, non-abelian factor** (`F₂ × ℤ`): shared
> walls become DIRECT-PRODUCT centrality; carried data becomes free-factor rank.

**Theorem (double-courier positivity — same architecture).** New readback features, each handled:
(i) `b ↦ a·u⁻¹·v` — `u⁻¹` is an unforgeable `b`-marker (only `b` emits it), and `b`'s `a`-head
merges into preceding `a`-runs with counts disambiguating; (ii) `w` is central in its factor, so
`w`-placement inside a `{p,s,w}`-block is lost in NF — restored exactly by the `pw`/`sw`
exclusions (`w`s must precede all `p,s` in an irreducible block), while the `p/s` ORDER is
preserved by `F₂`'s non-commutativity; (iii) the cancellation `sub(qb) = ua⁻¹·au⁻¹v = v =
sub(s)` is rule `qb = s` itself — forbidden side excluded. Every ambiguity is again a rule. ∎

**Phenomena.** (1) *Unforgeable markers:* positive words cannot fake negative letters, so the
free group's own signature system works FOR the parser — cross-factor images are a feature.
(2) Data-in-state costs nothing new structurally: carriers multiply free-factor rank; shared
infrastructure (walls) becomes centrality. (3) Definitional shrink rules (`qa = p`) are legal —
the Boolean-collapse shrink was fatal for its affix-sharing, not its shrinking.

### 4.9 M7 — interacting loops: the emergence hunt (both topologies cleared)

**(a) The ratio pair** — two self-loop transducers with different ratios on SHARED data:
`R = { qa = bq, ra = b²r }`. Complete (`#a` decreases, no critical pairs); irreducibles: no `qa`,
`ra`. Eliminating `b = qaq⁻¹` and setting the **comparison element** `t := q⁻¹r`:

> `G ≅ BS(1,2) ∗ ⟨q⟩` — the interaction of the two loops IS a Baumslag–Solitar relation
> (`tat⁻¹ = a²`) between the shared letter and the loop-comparison element.

*The emergence hunt.* The danger is BS-arithmetic (`ta = a²t`, `ta² = a⁴t`, …) manufacturing
deposit collisions beyond single rules. Walk/deposit analysis (items: `a: dep(a)`;
`q: U`; `b: U·dep(a)·D`; `r: U·dep(t)`, note `r` never comes down; `b`-tails are the ONLY `D`s,
hence the only mergers): merged deposits can only take the form **`aⁿ` or `aⁿ·t`** — `t` always
last — because `ra` is forbidden and nothing else appends `a`-material after a `t` at the same
height. These are exactly the BS-normal forms `(k,c) ∈ {(0,n),(1,n)}`, pairwise distinct, so
BS-arithmetic never fires inside a deposit. **The irreducibility condition `ra` IS the
BS-normal-form condition; rule 2 IS the BS relation** (`sub(ra) = q·ta = q·a²t = sub(b²r)` —
the one collision is the rule, forbidden side excluded). Height/multiplicity bookkeeping as in
§4.5.1 disambiguates cluster attribution (`U dep(aⁿt)` = `bⁿr`; `U dep(aⁿ) D` = `bⁿ`; baseline
deposits = `a`-runs; `U`-runs = `q`-runs). Positivity holds. ∎

**(b) The twin blinkers** — two M3-blinkers over the SAME data:
`R = {qa = bq′, q′a = bq, ra = br′, r′a = br}` ⟹ `G = ⟨a,b,q,r | qa²q⁻¹ = b², ra²r⁻¹ = b²⟩`:
a double HNN with IDENTICAL associated subgroups — the designed defect-exchange scenario
(`z := r⁻¹q` centralizes `a²`). And the exchange channel never opens: positive words contain no
stable-letter inverses, so there are NO pinches, every expression is Britton-reduced, and
compensations live at each junction separately — each junction's equation has the SAME form as
M3's (`hᵢ = a^{−2mᵢ}gᵢb^{2mᵢ₊₁}`), and M3's parity head-cap kills them all, junction by junction,
regardless of which stable letters flank the syllable. Positivity holds by M3's proof verbatim. ∎

**(c) The junction decoupling lemma** (the structural prize of the hunt). For one-state-per-side
rule shapes, spanning-tree elimination always gives positive letters *stable-positive* images
(each eliminated state solves as `s′ = x·s·y⁻¹` — base-letter inverses only). Hence positive
words are pinch-free, every expression is Britton-reduced over the multi-splitting, and
**compensations decouple per junction: multi-loop soundness reduces to single-loop mechanisms
applied at each junction independently.** Defect species from different stable letters cannot
exchange without pinches — the conspiracy channel doesn't exist for positive words. This
essentially completes the structural half of the general Lemma 2: eliminate, classify each
junction's splitting locally, apply the matching single-loop mechanism.

**Verdict.** The emergence hunt came back empty in both minimal interaction topologies; the
parser principle survived the boss room. Remaining risk classes (named, not yet hunted):
completion-divergent systems (infinite Knuth–Bendix — breaks the proof *architecture*, not
necessarily positivity) and data-data rule mixtures (state-free semantic commutations/braidings
interleaved with machine rules; note Garside theory covers braid-shaped cases). These become
**M8** if the Probe 0 opcode audit ever needs them.

### 4.8 Consolidation: the mechanism inventory

| Rung | System | Group | Proof mechanism | Law discovered |
|---|---|---|---|---|
| M1 | `gn = ng` | `F(a,b) ∗ ℤ²` | free-product normal form | — |
| M2 | `qa = bq′` | `F(q,a,b)` (Tietze-free) | complete rewriting + no-cancellation readback | — |
| M3 | blinker (2-cycle) | HNN `⟨a²⟩→⟨b²⟩` | **intrinsic Britton** + parity head-caps | irreducibility cap = unconsumed window letter |
| M4 | mixed cycle word | HNN `⟨ab⟩→⟨ba⟩` | **global defect flow** (masquerade → forced propagation → boundary annihilation) | conjugacy caveat; caps can be non-local |
| M5′ | shuttle (two-way) | `ℤ² ∗ F(q)` | free-product NF + **rule ⇄ ambiguity bijection** (§4.5.1, complete) | trajectory-injectivity; completion = commutation |
| M5 | mint/retire | HNN uneq. lengths; `BS(1,2)`; `BS(2,3)` | head-caps; **faithful affine invariant**; **Adjan/Remmers** | cycle-relator principle; mint-must-move |
| M6 | couriers (data-carrying states) | `ℤ² ∗ ℤ`; `(F₂×ℤ) ∗ ℤ` | free-product NF + **unforgeable negative markers** + centrality-restoration | parser principle promoted (§5.0) |
| M7 | interacting loops (shared data) | `BS(1,2) ∗ ℤ`; double HNN, equal assoc. | irreducibility = **BS normal form**; **junction decoupling** (pinch-free positives ⟹ per-junction single-loop caps) | interaction rule = BS relation; no defect-exchange channel |

Meta-observations: (1) six rungs, six distinct mechanisms — the conjecture keeps converting
attacks into tools, never into counterexamples; (2) every mechanism is a normal-form argument
against a structure obtained by *eliminating the control graph* (free / free-product / HNN /
affine) — suggesting the general Lemma-2 proof shape: eliminate the spanning tree, classify the
resulting splitting, run the matching normal-form argument with the machine's irreducibility
discipline as the cap; (3) ambient-group pathology (distortion, non-Hopficity) never leaked into
the trace; (4) every near-miss became a LAW (§3.5) rather than a wound.

---

## 5. The general program

### 5.0 The parser principle (the emergent-ambiguity reframe)

Confirmed across three architectures (shuttle §4.5, courier and double courier §4.7): `sub`
collapses exactly the rules (they are the relators), so **the parse ambiguities of a normal form
are generated by rule applications, and irreducibility excludes precisely one side of each rule.**
Therefore:

> **Positivity ⟺ no EMERGENT ambiguities** — no identifications of positive words arising from
> rule *interactions* that are not themselves generated by single rule applications.

This reframes the whole ladder: M1–M2 had no room for emergence; M3's parity argument and M4's
defect-flow argument are precisely proofs that an attempted emergent identification (the
`q′q ↔ qq′` phase swap) dies — locally in M3, globally at the boundary in M4; M5's monsters
threatened emergence through group pathology and failed; M5′/M6's proofs verify the
ambiguity⇄rule bijection directly. **Dragons, if any exist, ARE emergent ambiguities — and M7
(interacting control loops) is exactly the hunt for emergence between defects of different
stable letters.** The general Lemma 2 for Probe 0 takes the form: eliminate the control graph,
classify the splitting, exhibit the parser, and prove non-emergence by the mechanism matching
the splitting type (caps / defect flow / markers / centrality-restoration).

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
- ~~M5′ — two-way motion~~ **DONE, positivity holds, proof COMPLETE** (§4.5 + §4.5.1 readback
  enumeration; return-collapse law, head-passing = completion = commutation, shuttle group =
  `ℤ² ∗ F(q)`).
- ~~M5 — mint/retire~~ **DONE, positivity holds** (§4.6; cycle-relator principle + "mint must
  move" law; doubler = BS(1,2) sound via affine invariant; ratio rule = BS(2,3) sound via
  Adjan/Remmers — monsters aren't dragons).
- ~~M6 — data-carrying states~~ **DONE, positivity holds** (§4.7; couriers, unforgeable markers,
  shared walls = centrality; parser principle promoted to §5.0).
- ~~M7 — two interacting loops~~ **DONE, positivity holds in both topologies** (§4.9; ratio pair
  = `BS(1,2) ∗ ℤ` with irreducibility = BS normal form; twin blinkers = M3 per-junction; the
  **junction decoupling lemma** closes the structural half of general Lemma 2).
- **M8 (contingent):** completion-divergent systems; data-data rule mixtures (Garside-shaped) —
  only if the Probe 0 audit needs them.
- **NEXT: the Probe 0 opcode audit** — assemble the sorted-ANF instruction set (§5.3), check Laws
  0–5, classify each junction's splitting, assign mechanisms per §4.9(c).

---

## 6. The Probe 0 opcode audit (v1 — design-level, 2026-07-03)

Target: alphabet = structural letters `{X(⊕), M(∧), 1, 0, P, |}` + state/guard chunks; encoding
`f(σ) = code(E[σ̂])` (E = wrapper with WORK zone + empty SCRATCH zone; atoms in stroke form);
R = the families below. Canonical form: sorted ANF. Completeness = every code Thue-connected to
its canonical code (normalize; Thue symmetry makes "both reach canon" suffice). Soundness = Laws
0–5 audit + junction classification + per-junction mechanisms (licensed by §4.9(c)).

### 6.1 Two architecture corollaries derived from the Laws

- **No generic eraser.** `e·x = e` per letter forces `x = 1` (Law 2). Erasure exists ONLY as
  (i) uncompute-by-reversal (Thue symmetry makes builder rules erasers for free) and
  (ii) structured duplicate-pair cancellation (F7 below) whose every configuration remains a
  formula `≡`-equal to the whole.
- **The featured audit catch:** the constant-absorption schema as a naked rule `M1A ↔ A` is
  ILLEGAL (suffix-shared ⟹ collapsed relator `M·1`, i.e. `M = 1⁻¹` — Boolean-collapse-adjacent
  poison). The SAME semantic content as a guarded sweep step `s·M·1 = s′` (delete the unit-wrap
  in passing, state moves on) is legal, hygienic, and cycle-safe. One schema, two encodings,
  opposite verdicts — the audit discipline is not optional.

### 6.2 Opcode families, laws-check, junction classification

| Family | Content | Rule shape | Ladder type | Junction splitting | Verdict |
|---|---|---|---|---|---|
| F1 guard motion | states slide through structural letters | `qX = Xq` | M1 | ℤ²/central factors | ✅ |
| F2 sweep heads | read/translate steps | `qx = yq′` | M2–M4 | HNN, cap-friendly | ✅ |
| F3 couriers | monomial transport, sorting swaps | `qx = p`, `pw = wp` | M6 | free product + centrality | ✅ |
| F4 comparators | stroke-count zigzag (atom index compare) | blinker pairs + transducing turns | M3/M4 | HNN, parity caps + defect flow | ✅ (Law 3 at turns) |
| F5 copiers | subtree duplication into scratch | doubling walks | M5(b)/M7(a) | BS(1,k) junctions | ✅ (BS cleared) |
| F6 mint/retire | zone management | `q = gq′`-with-motion | M5(a) | unequal-length HNN | ✅ (Law 4) |
| F7 dual-erase | `M⊕M → 0`, `x∧x → x` dedup | two-track lockstep consumption | M7(b)-shaped | multi-HNN, synchronized | ⚠ per-junction OK by §4.9(c); **micro-witness design open** |
| F8 anchors | finitely many closed constant rules | concrete, guard-padded | — (leaves) | none (no cycles) | ✅ (Law 1 padding required) |
| F9 phase turns | sweep hand-offs | `qW = rW′`, `W ≠ W′` | — | tree edges | ✅ (Law 3) |

Cycle check (Law 0): state graph = phase sweeps + per-family loops; every cycle's net effect is
an intended macro (transport, compare-consume, copy, unit-deletion, zone growth) — no net-trivial
cycles, no stationary mints, by construction of the sweep discipline. **No data-data rules are
used anywhere** (every rule carries a state) ⟹ the Garside-shaped M8 class is avoided outright.
Completion-divergence (the other M8 class): unknown until the concrete rule list exists — audit
item for v2.

### 6.3 F7 micro-design (v1 closure of the theory-touching gap)

**The laundering disaster (a real poison, caught by the Law 0 audit).** First attempt: a
certificate-carrying eraser inside a `≡0` summand, alternating states for hygiene:
`|s = s′`, `|s′ = s`. Each rule is affix-disjoint and semantically witnessable — and the two-rule
CYCLE eliminates the states: `s = ||s ⟹ || = 1`. Stroke pairs become deletable in ALL contexts;
atom indices collapse mod 2; soundness dies. **Cycles launder certificates**: a state cannot
carry "I'm inside a zero summand" through a loop, because the group cancels the state around the
loop and keeps only the data-effect.

> **Law 4′ (anchor-straddling).** Every erasure/absorption cycle must straddle an anchor letter,
> so its NET cycle-relator remains state/anchor-carrying (e.g. `|sP| = sP`), never data-only.
> (Refines Laws 0/4: check not just that cycles displace, but that their net relators keep a
> non-data letter.)

The compliant eraser: a **fused comparator–eraser zigzag** at the seam of the duplicate pair —
delete one stroke left of the anchor, cross, delete one stroke right, return: rules
`|s = s₁`, `s₁P = Ps₃`, `s₃| = s₄`, `Ps₄ = sP`; net cycle-relator `|sP| = sP` (anchored ✓);
bidirectionally preserves the count-difference invariant (backwards it inserts on both sides),
so equal stays equal and unequal stays unequal. Junction types: M3/M4 zigzag class. The same
idiom handles monomial-spine consumption and the `0`-cleanup sweeps (`sX0 = s′`, per §6.1's
featured catch).

**The witness-liberation lemma (the gap-closer).** §6.3's old requirement — "every intermediate
configuration a genuine formula ≡ the whole" — is TOO STRONG and not required. Sem-membership of
a rule needs only ONE witness context in which both sides are codes of equivalent formulas; and
for any desynchronizing window (one copy shorter than its twin mid-erase), a **0-anchored
witness** exists: place the window inside a product with an explicit `0` conjunct — both sides'
formulas are `≡ 0` regardless of the desynchronization, hence equivalent. Intermediate
configurations of real derivations need not be codes at all (they never were, in any M-ladder
proof); global soundness is carried by positivity (Law P), not by configuration well-formedness.
This dissolves the value-synchronization tension entirely: lockstep erasure does not need
value-preserving intermediate formulas, only anchored cycles and the difference invariant.

**F7 verdict: CLOSED at design level.** Window set: fused zigzag eraser (above) + factor-fold
sweeps for spine alignment + guarded `0`-absorption; all rules affix-disjoint, one-state-per-side,
anchored cycles, 0-anchored witnesses; junctions all in the proven inventory. Remaining F7 work
is transcription (the concrete rule list), not design.

### 6.5 The concrete rule list (v1)

**`boolean-group-rules-v1.md`** — the complete machine at expansion-ready granularity: final
encoding (bracketed Polish + marked twins + placeholder), 4-pass architecture with termination
measures, 9-subroutine library (WALK/TURN/MATCH/COURIER/DUP/COMPARE/ERASE-PAIR/UNMARK/UNIT-SWEEPS)
with explicit schemas × index sets, pass programs, state inventory (≈45–55), expanded-count tally
(≈380–420 rules, all ∈ Sem), family-level audit (Laws 0–5 + 4′ + M8), and the spec for the
**expander/auditor tool** whose output IS the presentation, machine-checked against the laws.

### 6.4 Open engineering (the honest gaps, post-6.3)

1. ~~F7 micro-witnesses~~ **CLOSED at design level (§6.3)** — the old "every configuration ≡ the
   whole" requirement was too strong (witness-liberation lemma); remaining F7 work = rule-list
   transcription. NOTE: the Law 0 audit must now check Law 4′ (anchored cycle-relators) on the
   full rule list — the laundering eraser shows a hygienic, semantically-witnessed rule PAIR can
   still be poison as a cycle.
2. **Chunk realization layer:** states-as-transparent-chunks (comma-free code of `X·code(C_q)`
   blocks) — Law 1's cross-relator clause lives here; needs the concrete chunk assignment.
3. **Completeness proof:** that the machine actually normalizes every code (sweep termination,
   phase ordering) — standard machine-engineering, nothing conceptually open.
4. **Size estimate** (ties to the minimality discussion): ~30–60 states, order 10²–low-10³ rules
   for "the group of Boolean logic" v1 — before any optimization pass.

**Audit verdict v1: no soundness obstruction anywhere in the design; every junction type maps to
a proven ladder mechanism; the remaining work is construction, not theory** — with F7's
micro-witnesses the one spot where construction and theory still touch.

## 7. Literature anchors

Nearest neighbors (none answering the question): Adjan/Remmers cycle-free semigroup-in-group
embeddings; special monoids (Adjan, Makanin); Squier's homological finiteness obstructions (the
model for what a NO-proof would look like); Guba–Sapir diagram groups / Squier complexes (the
model machinery for derivation spaces); inverse-monoid presentation theory, E-unitarity
(Margolis–Meakin; one-relator inverse monoids, Ivanov–Margolis–Sapir); Bennett's reversible
computing; and the classical Novikov–Boone–Higman/Aanderaa–Cohen constructions whose *non-semantic*
scaffolding this program attempts to shed. The Miller-carrier H₂ theorem (sibling arc) shows the
naive carrier fails for homological reasons; nothing in the literature we know addresses finite
*semantic* bases.

## 8. Open problems

1. Head-cap positivity conjecture (§5.1) — prove for M4–M6 shapes; find the general statement.
2. Does SOME finite semantic basis exist for full propositional equivalence (Probe 0)?
3. The ZFC lift: does anything in §3–§5 obstruct at Σ₁-complete congruences? (No obstruction
   currently known; the skeleton is logic-agnostic.)
4. NO-direction: a Squier-style invariant separating finitely-semantically-based congruences from
   the Lindenbaum congruence — even a propositional-level obstruction would be a striking theorem.
5. Quantitative: if Probe 0 lands, how small is the Boolean-logic group? (Relator count and total
   symbols; compare the minimality discussion for the ZFC group.)

---

## 9. The ZFC lift (design sketch, 2026-07-03)

How the Boolean-logic construction extends to the full goal. Everything logic-agnostic carries
over unchanged: the Laws (0–5, 4′), the M-ladder mechanisms + junction decoupling, the parser
principle, the entire subroutine library (§6.5), the witness-liberation lemma (⊥-anchored
contexts replace 0-anchored). Three genuinely new layers:

### 9.1 No canonical forms ⟹ proof-replay completeness

ZFC-equivalence is Σ₁-complete: no normalize-to-canon architecture. Completeness becomes
**guess–verify–transmute–uncompute** (Thue symmetry makes guessing free: rules run backward
mint, forward erase):

> **Replay Completeness Lemma (to prove; the lift's Lemma 1).** Fix a Hilbert calculus. The
> congruence generated by: (i) the Probe-0 propositional engine over FOL-formulas-as-atoms;
> (ii) quantifier walks (α-renaming, ∀-distribution, prenex moves, vacuous-∀ with a free-variable
> check sweep); (iii) instantiation-equivalence `∀xφ ~ ∀xφ ∧ φ[t/x]` (an EQUIVALENCE, not an
> implication — the key observation making Hilbert steps semantic); (iv) finitely many
> axiom-conjunction rules `σ ~ σ∧θᵢ`; (v) the transmutation tautology `A∧(A↔B) ~ B∧(A↔B)`
> — contains provable-equivalence. *Replay:* conjoin axioms into a theorem store, drive MP as
> the propositional tautology `A∧(A→B) ~ A∧B` inside the store, instantiate via (iii), reach
> `σ ∧ Θ′ ∧ (σ↔τ)`, transmute by (v), uncompute the store by reversal — landing exactly at
> `f(τ)`.

### 9.2 Finitely many axioms: use NBG (or Tarski–Givant)

ZFC's schemas would need infinitely many axiom-conjunction rules. **NBG is finitely
axiomatizable and conservative over ZFC**: the group is properly "the NBG group," whose
set-sentence fragment realizes exactly ZFC-provable-equivalence — which is the stated goal
(`f(σ)=f(τ) ⟺ ZFC ⊢ σ↔τ` for set sentences). Tarski–Givant's equational form is the alternative
basis (shorter axioms, variable-free — worth a size comparison at rule-list time).

### 9.3 The theorem store, the ⊤-shielded yard, and anchored unshielding

New primitive: arbitrary material can be built letter-by-letter inside a shield `(· ∨ ⊤)` —
every construction step is an equivalence of wholes regardless of content. Axiom instances and
proof lines are yard-built, shape-verified by comparator walks (axiom-schema patterns; MP-line
matching; substitution-comparators checking `γ = φ[t/x]` against a LIVE `∀xφ` with
capture-avoiding α-walks). **Unshielding** — deleting the `∨⊤` wrapper around verified material —
is the dangerous step: sound at intended sites (the live `∀xφ` anchor certifies `Θ ⊢ γ`),
conditionally-sound elsewhere; it must be an anchored two-ended erasure walk, and nested shields
create a bracket-matching exit risk. **Law-candidate 6 (shield discipline):** one open yard at a
time / shields never nest — plus the Law 4′ cycle audit over the new
verify-unshield-composite cycles. Expect 1–2 new ladder rungs here (M8: nested-shield /
subst-comparator cycle classes) before the ZFC rule list is written.

### 9.4 The overhead bonus (convergence with after-zfc-group)

Because completeness is proof-REPLAY, derivation length is polynomial in the Hilbert proof
length (sweep-restart discipline: low-degree polynomial). The classical AC+Higman route has
non-elementary overhead and the after-zfc program (SBR/BOS) exists to repair it — **the
semantic-basis group gets the good overhead by design**, since it simulates proofs directly
rather than machines that search for them. If the program lands, the ZFC-2.0 group is
simultaneously: self-contained (every relator a theorem), readable (relators = logic schemas +
NBG axioms), and polynomial-overhead — all three axes of the original minimality discussion.

### 9.5 Estimates and sequencing

Size: propositional engine (~400) + quantifier walks (~100) + substitution machinery (~150) +
NBG axiom mints (~20 rules, long words) + store/yard control (~150) ⟹ **order 10³ rules,
~10⁴–10⁵ total symbols** ("a thick pamphlet"). States ~100–150. Sequencing: (1) Probe 0
expander/auditor + fuzzer (validates the whole methodology cheaply); (2) the M8 rungs
(shield + subst-comparator cycles); (3) Replay Completeness Lemma against a fixed calculus;
(4) the ZFC/NBG rule list, same expansion-ready style. The traditional AC+Higman arc (AGENDA)
remains a separate, nearly-finished, machine-checked artifact; this is its designed successor.
