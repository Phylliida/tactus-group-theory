# §3.3 machine bridge + Layer 0.5 infinite-gen representation — design pass

*Written 2026-06-25 (session 32), after Layer 2 completed (CS-6/CS-7,
`lemma_C_faithful_printable`). With Layers 1 and 2 done, the only arcs left in the AGENDA are
§3.3 (the machine bridge) and Layer 0.5 (CEER → f.g. `C`). This doc resolves the dependency
structure between them, records what is **unblocked + designed** (built this session) vs. what is a
**genuine foundational decision** (surfaced for Danielle), and grounds both in the existing code +
the located source material. It supersedes nothing; it is the missing map for the last two arcs.*

> **Standing rule honored** (`MESSAGES_FROM_USER.md` 2026-06-22): follow the textbook, do not
> reinvent. Below, the textbook route is Miller §4.1 (Layer 0.5) and Cohen §9.6 p.279 (the bridge);
> the two known *dragons* are documented so we don't re-walk them.

---

## 0. TL;DR

- **§3.3a is DONE this session** (`cohen_bridge.rs` 4/0, additive): the abstract Layer-2 relator
  predicate `is_S` is instantiated to its canonical value `S = { w_α(c) : (α,0)∈H₀(M) }` and both
  side conditions (`s_relators_valid`, `s_realizes`) are discharged. Headline:
  `lemma_C_faithful_printable_canonical` — **the printable f.p. `h3_pres` faithfully contains
  `C = ⟨c;S⟩` for the concrete machine set `H₀(M)`**. This is Higman's embedding theorem made fully
  explicit, for ANY modular machine `M`, with no abstract hypotheses. ZFC-independent.
- **The headline machine-iff `w_α(c)=1 in H₃ ⟺ (α,0)∈H₀(M)` is NOT closed by §3.3a**, and *cannot*
  be, from the canonical `S` alone: the forward `w_α(c)=1 in C ⟹ (α,0)∈H₀` is the statement that
  *C's word problem decides the c.e. set*, which is **Layer-0.5 content** (`ncl(S)` collapses more
  than `S`; see §2). The two arcs are genuinely sequential: **Layer 0.5 produces the real `C` (and
  its relator set `S`); §3.3-proper then ties that `S` to a machine.**
- **Layer 0.5's blocker** (infinite generators) is **less blocked than the AGENDA implies**: a
  working bespoke infinite-gen representation of the CEER group already exists and its *forward*
  direction is proven (`tactus-computability-theory/src/ceer_group.rs`), and both F∞↪F₂ crux
  families are banked (`conj_free_core`, `conj_free_b`). What remains is a genuine foundational
  decision (which representation to carry forward) + the Miller §4.1 HNN faithfulness. **Recommended:
  do NOT start the multi-week port unilaterally** (unsupervised session; this is the decision
  Danielle has gated for many sessions). Surface it + the cheap de-risking probe (§5).

---

## A. §3.3 — the machine bridge

### A.1 What the bridge is (Cohen §9.6, book p.279)

`C = ⟨c₁,…,cₙ ; S⟩` is the f.g. recursively-presented group; `S` is an r.e. set of relator words
on the c-block. The *word-numbering* `w_α(c)` (`word_numbering.rs`, DONE) enumerates c-words by `α`.
The bridge couples `S` to a modular machine `M`:

> **`w_α(c) ∈ S   ⟺   (α,0) ∈ H₀(M)`.**

The Layer-2 assembly carried `S` abstractly as `is_S : spec_fn(Word)->bool` with two side conditions
(`cohen_h2.rs`): `s_relators_valid` (S ⊆ c-words) and `s_realizes` (the bridge's ⟸ — H₀ ⟹ in S).

### A.2 §3.3a — the canonical instantiation (BUILT, `cohen_bridge.rs` 4/0)

`is_S_canonical(mm,n,m) := { w : ∃α. numbers_word(n,m,α) ∧ (α,0)∈H₀(M) ∧ w = w_α(c) }`.

- `s_relators_valid` ✓ — `lemma_w_c_is_c_word` (thin wrapper over the existing `lemma_w_c_in_block`:
  every `w_α(c)` letter has index in `[c_base, c_base+n)` = `c_symbol`).
- `s_realizes` ✓ — immediate, witness `β = α`.
- ⟹ `lemma_C_faithful_printable_canonical`: drops the two abstract hypotheses from CS-7.

**Why this is "designed, not reinvented":** the assembly plan (`cohen-section1-assembly-plan.md` §2)
already names exactly this — *"the §3.3 instantiation will discharge it."* The definition is forced
(it IS Cohen's word-numbering image of `H₀(M)`); there is no free choice. Additive + reversible.

### A.3 What §3.3a does NOT give, and why (the depth lives in Layer 0.5)

The headline `w_α(c)=1 in H₃ ⟺ (α,0)∈H₀`:
- ⟸ soundness `lemma_III` (DONE, `higman_consequences.rs`): `(α,0)∈H₀ ⟹ w_α(c)≡1 in h3_pres`.
- ⟹ faithfulness CS-7 gives `w_α(c)≡1 in h3_pres ⟹ w_α(c)≡1 in C`. To finish we need
  **`w_α(c)≡1 in C ⟹ (α,0)∈H₀`.** With the canonical `S` over a *free* c-group this is
  `w_α(c) ∈ ncl(S) ⟹ (α,0)∈H₀`, **false in general** — `ncl(S)` identifies more than `S`. It holds
  only because the *real* `C` (the Layer-0.5 HNN-embedded CEER group) has its word problem equal to
  the c.e. set *by construction*. So this step is Layer-0.5 content, not derivable from §3.3a.

**Consequence for sequencing.** §3.3-proper (the machine reduction ZFC-enumerator → `M`, item 2 of
AGENDA §3.3) presupposes the relator set `S` *of the real `C`*, which is produced by Layer 0.5. So
the genuine critical path is **Layer 0.5 first**. §3.3a is the only part that could be done now
(because it runs the bridge *backwards*: given any `M`, define `S` — yielding the general Higman
theorem, not yet the ZFC instance).

---

## B. Layer 0.5 — CEER → finitely generated `C`

### B.1 The two dragons (do not re-walk — `constructive-fp-group-scope.md`)

1. **The naive telescope is provably wrong.** `gₙ ↦ y⁻ⁿxyⁿ` into F₂ then imposing `g_a=g_b`
   collapses F₂ to ℤ×ℤ (`[x,y⁻¹]=1`) and kills *all* `gₙ`. The CEER relations cannot be imposed
   *inside* a free group; they must fire only on *declared* pairs. (This is the whole reason the
   construction routes through a machine encoding rather than a static embedding.)
2. **`machine_group_backward` — the old `external_body` crux — is now SLAIN.** It was the
   Boone–Novikov/Aanderaa–Cohen faithfulness "config equiv ⟹ valid machine trace", via Britton
   pinch-elimination. That is **exactly Layer 1's Theorem 1 ⟹-direction (the crux E), now DONE**
   (`lemma_theorem1`, `prop_v` 57/0). So the hardest historically-blocking piece is already paid for.

### B.2 The textbook route (Miller §4.1, `../verus-group-theory/CGTMiller.pdf` pp.53–54)

Input countable `C₀ = ⟨c₁,c₂,… | D⟩`; `L = C₀ ⋆ F₂`, `F₂=⟨a,b⟩`; free bases
`A=⟨b, cᵢa⁻ⁱbaⁱ⟩`, `B=⟨a, b⁻ⁱabⁱ⟩`; HNN `G=⟨…,t | D, t⁻¹bt=a, t⁻¹cᵢa⁻ⁱbaⁱt=b⁻ⁱabⁱ⟩`; `G` is
2-generated by `{a,t}`; `C₀ ↪ L ↪ G`. **Already banked, representation-independent:**
- `{a⁻ⁱbaⁱ}` free in F₂ — `conj_free_core.rs` 34/0 (`lemma_conj_family_free`).
- `{b⁻ⁱabⁱ}` free in F₂ — `conj_free_b.rs` 12/0 (`lemma_conj_family_b_free`).
- The free-word-problem bridge `≡_{free_group} ⟹ freely_equivalent` — `free_word_problem.rs` 4/0.

What is NOT yet built: stating `L = C₀ ⋆ F₂` and the `t`-HNN over the **infinitely generated** base,
and the faithfulness `C₀ ↪ G` (free-product + HNN base-embeds over ∞ generators).

### B.3 The infinite-gen representation — the foundational decision

The substrate's `Presentation`/`PredPresentation` both fix `num_generators: nat` (finite). The CEER
group and the intermediate `L` are ∞-generated. **But the blocker is softer than the AGENDA states:**

> **A working ∞-gen representation of the CEER group already EXISTS and its forward direction is
> proven** — `tactus-computability-theory/src/ceer_group.rs`: a *bespoke, self-contained* derivation
> system over an ∞-alphabet `CeerSymbol{Gen{index:nat},Inv{index:nat}}`, `CeerWord=Seq<CeerSymbol>`,
> with `ceer_group_equiv` (relators fire on `stage_declares(e,stage,a,b)` — recursively presented by
> construction) and `lemma_ceer_equiv_implies_group_equiv` (declared-equiv ⟹ group-equiv).

So the generators are *already* ℕ-indexed; "∞-gen" just means "no `word_valid` bound." Three
candidate representations for Layer 0.5 (this is the decision):

| Option | What | Pros | Cons |
|---|---|---|---|
| **(i) Extend the bespoke `ceer_group.rs`** | keep `CeerSymbol`/`CeerWord`/`ceer_group_equiv`; define the embedding `CeerWord → Word` (F₂/G alphabet) + prove faithfulness directly | reuses a proven forward half; no new general type; smallest surface; lives in the crate that needs it | bespoke (not the `pred_*` substrate); the AFP/Britton machinery is over `Presentation`, not `CeerWord` — base-embeds must be re-proven or bridged |
| **(ii) New general `InfPredPresentation{relators:spec_fn(Word)->bool}`** | a `pred_*`-style type with NO generator bound (`word_valid` vacuous; `Gen(g)` any `g:nat`); re-express the CEER group in it | uniform with the whole `pred_*` substrate; the FA-5..FA-9b precedent shows the elementary equiv algebra ports verbatim (relator-agnostic) | a third port of the AFP/Britton stack (the ~21k-line reserved commit) to ∞-gen — the genuine multi-week cost |
| **(iii) Modify `PredPresentation` to a `GenLimit{Finite(nat),Infinite}`** | one type, branch on the bound | one type | **rejected** — datatype change invalidates the ENTIRE pred substrate (base-hash, caching §3) + every `pred_*` module; non-additive, non-reversible; violates the project's discipline |

**Recommendation:** **(i) for the source group + a thin bridge, falling back to (ii) only where the
Britton/HNN base-embeds genuinely need it.** The Miller route's deep step is the HNN faithfulness
`C₀ ↪ G`; that is where (and only where) the AFP/Britton stack is invoked. The question is whether
that invocation can be localized to FINITE sub-presentations by **compactness** — exactly the trick
the CS-4b arc used (`lemma_cs4b_compactness`: a relation in the ∞ predicate base lives in a finite
slice). If yes, the ∞-gen base never needs the full AFP stack ported; only finite slices do (already
available). If no, option (ii)'s port is unavoidable. **This compactness question is the single
decisive unknown** and is cheap to probe (§5).

### B.4 The CEER group is FREE — a candidate simplification (validate, do not assume)

`⟨gₙ | g_a g_b⁻¹ : a~b⟩` imposes only `g_a = g_b`, so the group is the **free group on the
∼-classes** `ℕ/∼`. This *suggests* the embedding could be the already-proven `F∞ ↪ F₂` conj-family
rather than the general Miller HNN. **Caveats (why this is a candidate, not a decision):** (a) ∼ is
only c.e., so class representatives are not computable — the recursive presentation must be preserved
*without* deciding ∼, which is precisely why Higman routes through declared pairs (dragon #1); (b)
the bridge `w_α(c)∈S ⟺ (α,0)∈H₀(M)` must still come out in the right form; (c) Danielle's standing
rule says follow Miller, and a "cleverer free embedding" is the kind of off-textbook shortcut that
has burned the project before. **So: flag it as a possible reduction of the HNN to a free map, to be
checked against Miller §4.1 + the recursive-presentation requirement — NOT a reason to skip Layer
0.5.**

---

## C. The genuine decision for Danielle (surfaced, not taken)

This session built §3.3a (designed, forced, additive) and stopped at the foundational fork, which is
co-design-gated and which an unsupervised session must not take unilaterally:

1. **Representation** for Layer 0.5: extend bespoke `ceer_group.rs` (i) vs. general
   `InfPredPresentation` (ii). Recommendation: (i)+compactness, (ii) only if compactness fails.
2. **The compactness question** (§B.3): does the Miller HNN faithfulness localize to finite slices
   (reusing the proven AFP/Britton stack), or does it force a third ∞-gen port? Decisive for scope.
3. **The free-group simplification** (§B.4): is the CEER group's freeness a legitimate shortcut to
   `F∞↪F₂` (conj-families, DONE), or a dragon? Check against Miller + recursive-presentation.
4. **Sequencing**: confirm Layer 0.5 → §3.3-proper → §3.4 (print). §3.3a + soundness already give
   the *general* explicit Higman theorem today; ZFC needs Layer 0.5 first.

---

## D. Recommended next step (cheap, non-committing — mirrors the §4 Fork-A probe)

Before committing the multi-week Layer-0.5 build, run ONE de-risking probe that answers the
compactness question (§B.3) without porting anything heavy:

- **Probe:** state `L = C₀ ⋆ F₂` for the bespoke CEER group (option (i)) using the EXISTING finite
  `free_product` over a finite slice of c's, and check whether the embedding's faithfulness obligation
  for a *single fixed word* reduces (by compactness) to a finite sub-presentation already covered by
  the proven AFP machinery. Outcome positive ⟹ (i)+compactness route is real and the port is small;
  outcome negative ⟹ option (ii)'s ∞-gen AFP port is on the critical path (re-scope with Danielle).

This is the analog of session-12's `pred_presentation.rs` probe that de-risked Fork-A's foundational
layer (8/0 first try) without committing the tower port. **Do not proceed past the probe without
Danielle's go** (the standing co-design gate on the foundational representation decision).
