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

- **✅ THE §D PROBE RAN — POSITIVE (2026-06-25, session 33, `cohen_layer05_probe.rs` 10/0, commit
  1bea208, gate 2614/20 = additive no-regression).** The single decisive unknown (does Miller's HNN
  faithfulness localize to finite slices?) is now **machine-checked YES**. For a fixed word over a
  finite slice, the whole `C₀ ↪ L ↪ G` obligation reduces to a *legal finite `HNNData`* that plugs
  straight into the proven stack: free-product injectivity (`lemma_free_product_injective_left`) +
  finite Britton base-embed (`lemma_single_hnn_base_faithful`), with the HNN iso precondition reduced
  **generically** to two `is_free_family` facts on the columns (`lemma_iso_from_free_columns`).
  **Consequence: NO infinite-generator presentation type is on the critical path** (option (i)+
  compactness is real; (ii) is dead). The infinity survives only in (a) the done `ceer_group.rs`
  forward direction and (b) the meta-level `∀w ∃N` quantifier (needs no ∞-gen type). The **sole**
  genuinely-new math left for Layer 0.5 is the A-column basis `{b, cᵢa⁻ⁱbaⁱ}` being a free family
  in the free *product* `C₀⋆F₂` (the B-column `{a, b⁻ⁱabⁱ}` = pure-F₂ = banked `conj_family_b`).
  Decision-1/3 below collapse accordingly; only the *go-ahead to build* remains gated. See §D.

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

Session 32 built §3.3a and stopped at the foundational fork. **Session 33 ran the §D probe, which
answers decisions 2 and 3 empirically** (machine-checked + companion-confirmed) and collapses 1.
The fork is now nearly resolved; only the *go-ahead to spend the build effort* remains gated.

1. **Representation** for Layer 0.5: extend bespoke `ceer_group.rs` (i) vs. general
   `InfPredPresentation` (ii). **→ RESOLVED by the probe: (i)+compactness.** The probe shows the
   only place the AFP/Britton stack is invoked (the HNN faithfulness) localizes to finite slices
   reusing the *existing finite* `Presentation`/`free_product`/`HNNData`/Britton — so (ii)'s ∞-gen
   AFP port is NOT needed. The bespoke `ceer_group.rs` carries `C₀`; finite slices carry the rest.
2. **The compactness question** (§B.3): does Miller's HNN faithfulness localize to finite slices?
   **→ ANSWERED YES** (`cohen_layer05_probe.rs` 10/0; §D below). Decisive-for-scope unknown closed.
3. **The free-group simplification** (§B.4): legitimate `F∞↪F₂` shortcut or dragon? **→ DRAGON
   (confirmed).** `∼` is only c.e., so the basis `ℕ/∼` is not computable; using it would smuggle in
   deciding `C₀`'s word problem, collapsing the point of the construction. Follow Miller: carry
   `C₀`'s relators opaquely (as `decls`/the bespoke predicate). NOT a reason to skip Layer 0.5.
4. **Sequencing**: confirm Layer 0.5 → §3.3-proper → §3.4 (print). §3.3a + soundness already give
   the *general* explicit Higman theorem today; ZFC needs Layer 0.5 first. *(unchanged)*

**What is STILL gated (the only open decision):** the go-ahead to build Layer 0.5 itself — i.e. to
spend the effort on (a) the A-column free-product basis freeness `{b, cᵢa⁻ⁱbaⁱ}` free in `C₀⋆F₂`
(the one genuinely-new crux; B-column banked), (b) wiring the bespoke `ceer_group.rs` `C₀` through
the finite-slice machinery the probe validated, and (c) the `∀w ∃N` compactness assembly
(CS-4b-style). This is no longer a *direction* risk (the direction is settled + de-risked) but an
*effort* commitment, so it still wants Danielle's explicit go.

---

## D. The de-risking probe — ✅ DONE, POSITIVE (session 33)

> Ran the cheap non-committing probe (analog of session-12's `pred_presentation.rs` that de-risked
> Fork-A's foundational layer). **Result: POSITIVE.** Committed `cohen_layer05_probe.rs` (10/0,
> additive, gate 2614/20, no assume/admit/external_body, commit 1bea208).

**What the probe is (as run).** A finite slice of Miller's construction, stated with the *existing
finite* substrate and machine-checked end-to-end for a fixed word:
- `c0_slice(n, decls)` = `C₀^(N)` as a finite `Presentation` (N c-generators + opaque relators
  `decls` — recursively presented, NOT free; the §B.4 trap is avoided).
- `l_slice(n, decls) = free_product(c0_slice, free_group(2))` = `L^(N) = C₀^(N) ⋆ F₂`
  (a = Gen(n), b = Gen(n+1)).
- `miller_data(n, decls)` = the finite-association `HNNData` for `G^(N)` with associations
  `{(b,a)} ∪ {(cᵢa⁻ⁱbaⁱ, b⁻ⁱabⁱ) : i<N}`; `lemma_miller_data_valid` proves it is a legal
  `hnn_data_valid` datum.

**What it proves.**
- **Part A — generic reusable nugget** (`lemma_iso_from_free_columns`,
  `lemma_hnn_base_faithful_from_free_columns`): two free association columns ⟹ `hnn_associations_isomorphic`
  ⟹ `lemma_single_hnn_base_faithful` applies. Column-agnostic; this is what the real build consumes.
- **Part C — the headline** (`lemma_miller_slice_faithfulness_reduces`): for a fixed `C₀`-word `w`
  trivial in `G^(N)`, faithfulness descends to `w` trivial in `C₀^(N)`, **given only** that the two
  columns are free families in `L^(N)`. The free-product step (`lemma_free_product_injective_left`)
  and the finite-Britton step (Part A) are *fully discharged*.

**What it settles.** The whole per-word faithfulness obligation = `[free-product injectivity: HAVE]`
+ `[finite Britton base-embed: HAVE]` + `[two free-family facts]`. So Miller's HNN faithfulness
**localizes to finite slices** — option (i)+compactness is real, **no ∞-gen presentation port
needed** (decision-1/2 in §C closed). The **only** remaining new math is the A-column free-family
fact (B-column = banked).

### The Layer-0.5 build that the probe unlocks (pending Danielle's go)

The probe leaves a clean, de-risked ladder. NONE of it is a direction risk anymore; it is the
effort commitment §C flags as still gated.

1. **A-column freeness — the one new crux.** `is_free_family(C₀⋆F₂, {b, cᵢa⁻ⁱbaⁱ})`. A free-product
   normal-form argument: each `cᵢa⁻ⁱbaⁱ` is reduced alternating between `C₀` (the `cᵢ`) and `F₂`
   (the `a⁻ⁱbaⁱ`, whose central-`b` survival is the banked `conj_free_core` content). Likely the
   bulk of the work. (B-column `{a, b⁻ⁱabⁱ}` = `conj_free_b`, banked.)
2. **Carry the bespoke `C₀`.** Wire `ceer_group.rs`'s `CeerWord`/`ceer_group_equiv` (∞-alphabet,
   forward direction DONE) into the finite-slice `decls` view (a finite slice of declared pairs is a
   finite `Presentation`), so `c0_slice` instantiates to a genuine CEER slice.
3. **The `∀w ∃N` compactness assembly** (CS-4b-style): a finite derivation of `w=1 in G` uses
   finitely many relators ⟹ lives in `G^(N)` ⟹ Part C ⟹ `w=1 in C₀`. Reuse the
   `lemma_cs4b_compactness` pattern (`lemma_finite_step_from_pred` + relator-arm + induction core).
4. **Assemble `C = G = ⟨a,t | D̄⟩`** (2-generated, recursively presented) + faithfulness `C₀ ↪ C`;
   this `C` is Layer-2's input. Then §3.3-proper ties `S = D̄` to the machine.

**Do not start step 1 without Danielle's go** — the standing co-design gate is now narrowed to the
*effort* commitment (the direction + scope are settled and machine-validated).
