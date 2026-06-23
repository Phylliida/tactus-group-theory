# Brick 5 completeness — what the PRIMARY SOURCE actually says (2026-06-23)

Companion to `brick5-fork-reevaluation.md` (the Fork-B-is-undesigned finding) and
`brick5-completeness-plan.md`. Written after reading **Cohen, *Combinatorial Group Theory: A
Topological Approach*, pp.279–281** directly from the scanned PDF (per Danielle's standing
instruction in `MESSAGES_FROM_USER.md`: *"follow the textbook as closely as possible, don't
reinvent — reinventing leads to dragons; consult the reading when uncertain."*). The page images
are at PDF pp.284–286 (book pp.279–281, offset +5); extraction recipe in
`higman-embedding-blueprint.md` §top. This note records exactly how Cohen proves faithfulness, the
precise point where the formalization diverged, and an **evidence-based answer to scoping question
#2** (is predicate-Britton as hard as Fork-B?).

---

## 1. How Cohen ACTUALLY proves `C ↪ H₃` is faithful (book pp.280–281)

The faithfulness direction is **one sentence** on p.281, once the association isomorphisms are in
hand:

> *"It follows that there is an HNN extension `H₃` of `H₂` whose stable letters are `aᵢ` (1≤i≤2n)
> and `k`, the subgroups associated with `aᵢ` being `A` and `Aᵢ`, and the subgroups associated with
> `k` being `A₊` and `A₋`. Then `H₃` contains `C` …"*

That is the whole of it: **once the `aᵢ`- and `k`-associations are genuine isomorphisms of
subgroups of `H₂`, `H₃` is a genuine HNN extension, so the base `H₂` embeds in `H₃` (standard
base-embeds-in-HNN, a corollary of Britton), and `C ⊆ H₂` rides along.** There is **no Britton-peel
injectivity of the `aᵢ`/`k` level** in Cohen — that entire idea (C0–C5, map_a/map_b forward,
σ-saturation, the "virtual iso") is a formalization invention, not in the source.

All the real work is establishing the two association isomorphisms, and Cohen does each **cheaply**:

### 1a. `A ≅ Aᵢ` (p.280) — recognition + relabeling, NO Britton-peel
- `A = ⟨t, x, d, bⱼ (1≤j≤n), p⟩`. Cohen: *"A is just the HNN extension of the free group `F` with
  basis `{t,x,d,bⱼ}` with stable letter `p`, the relations being `p⁻¹ tα p = tα wα(b) d` for all
  α∈I."* — i.e. **`A` is itself an infinitely-presented p-HNN of a free group.**
- `Aᵢ = ⟨tᵢ, xᵐ, bᵢd, bⱼ, p⟩`. By **Proposition 1.34** (HNN-subgroup recognition) + the Layer-1
  intersection facts `⟨tᵢ,xᵐ⟩ ∩ ⟨tα : α∈I⟩ = ⟨t_β : β≡i mod m⟩` (Layer-1 **property (ii)**, DONE),
  `Aᵢ` is *also* an HNN of a free group `⟨tᵢ,xᵐ,bᵢd,bⱼ⟩` with stable letter `p`, relations
  `p⁻¹ t_β p = t_β w_β(b) d` for β∈I, β≡i mod m.
- *"Since `w_{αm+i}(b) = wα(b) bᵢ`, it is easy to see from this that there is an isomorphism from
  `A` to `Aᵢ` which maps each stated generator of `A` to the corresponding stated generator of
  `Aᵢ`."* — the iso is a **relabeling** of two HNN-of-free presentations whose relations correspond.

### 1b. `A₊ ≅ A₋` (pp.280–281) — von Dyck forward + c-killing endomorphism inverse
- `A₊ = ⟨U, d, bⱼ, p⟩`, `A₋ = ⟨U, d, bⱼcⱼ, p⟩`, with `U` = Layer-1 `g_subgens` (finite).
- By Prop 1.34 + the Layer-1 faithfulness fact `⟨U⟩ ∩ ⟨tα : α∈I⟩ = ⟨tα : α∈I, (α,0)∈H₀(M)⟩`
  (Layer-1 **property (vi)/(vii)**, DONE), `A₊` is the HNN of the free product `⟨U⟩ ∗ ⟨d,bⱼ⟩` with
  stable letter `p`, relations `p⁻¹ tα p = tα wα(b) d` for α∈I **with (α,0)∈H₀(M)**.
- **Inverse `A₋ → A₊`** = the endomorphism of `H₂` killing every `cⱼ` (fixes all else), restricted.
- **Forward `A₊ → A₋`** = the stated-gen correspondence; well-definedness is **von Dyck's theorem**:
  show `p⁻¹ tα p = tα wα(bc) d` for all α∈I with (α,0)∈H₀(M). Since the `cⱼ` commute with the `bᵢ`,
  `wα(bc) = wα(b) wα(c)`; and **`wα(c) = 1` in `C`** when (α,0)∈H₀(M) (the definition of `M` / the
  word-numbering bridge). So the relation reduces to `p⁻¹ tα p = tα wα(b) d`, which holds. ∎
- Two mutually-inverse homomorphisms ⟹ isomorphism. **No Britton-peel.**

---

## 2. The precise divergence

The formalization tried to prove the `aᵢ`/`k` isos by **direct Britton-peel injectivity over a
FINITE base presentation** (`h3_pres` / `h2_II` with only a *finite slice* of family (II)). Cohen
instead **recognizes `A/Aᵢ/A₊/A₋` as p-HNN extensions of free groups (Prop 1.34) over the
infinitely-presented `H₂`** and reads the isos off cheaply (relabeling; von Dyck + endo).

The previous sessions *correctly diagnosed* this (`brick5-completeness-plan.md:100–105`: *"Cohen's
HNN-recognition of `A` (Prop 1.34) needs the full family (II) … the recognition simply isn't
available at the literal intermediate level. C3-as-stated is a dead end"*) — but then pivoted to the
**virtual-iso Fork-B workaround** instead of supplying the full family (II). The re-evaluation
(`brick5-fork-reevaluation.md`) showed Fork-B's core is undesigned (it would need a "virtual
Britton's Lemma," research-level new math with no extant sketch — a textbook dragon).

**Conclusion: the textbook-faithful route is Fork-A** (represent the infinite family (II)); Fork-B
was the reinvention Danielle's standing message warns against.

---

## 3. Evidence-based answer to scoping question #2

> *"How hard is `britton_pred_lemma` (Britton over an infinite/predicate relator set)? If it is as
> hard as the Fork-B virtual engine, the pivot buys less."* — `brick5-fork-reevaluation.md` §3 Q2.

**Answer: it is STANDARD math, not Fork-B's undesigned new math — but a LARGE mechanical re-proof
with one genuine implementation risk.**

### Why it is standard (the math)
Britton's Lemma / base-embeds-in-HNN places **no requirement** on the base group's presentation
being finite. Its reduction (removing `t`-pinches) depends only on the associated subgroups being
genuinely isomorphic, not on finiteness of the base relators. Once the base carries family (II), the
`aᵢ`/`k` iso `hnn_associations_isomorphic` is **genuinely true** (provable by §1's recognition + von
Dyck + endo) — so the "universal iso over an arbitrary derivation" that
`lemma_single_step_preserves_syls` demands (the §1 obstruction in `brick5-fork-reevaluation.md`) is
**satisfiable**. No virtual Britton needed. *(Pure-group-theory sanity check passed.)*

### Implementation evidence (the code)
- `HNNData { base: Presentation, associations: Seq<(Word,Word)> }`. The **associations stay finite**
  — `A/Aᵢ/A₊/A₋` are *finitely generated* (U is finite). Only `base: Presentation` with
  `relators: Seq<Word>` (finite) is the wall — it cannot hold family (II).
- `hnn_associations_isomorphic` is defined via `equiv_in_presentation(base, …)` over the *finite*
  `a_words`/`b_words`. **Only the base-equivalence needs predicate support.**
- `britton_via_tower` (Lyndon–Schupp Ch IV): unfolds the HNN into an AFP **tower whose DEPTH is
  bounded by the word's stable-letter count** (finite per word), materializing a copy of the base
  relators at each level via `shift`. A base-relator derivation step is **stable-letter-free ⟹
  predicate-agnostic** (it acts inside one level's base copy, regardless of *which* base relator);
  only the hnn step uses the iso. So the proof *strategy* generalizes.

### The genuine residual risk (the gating unknown) — now CODE-LEVEL CONFIRMED
The **mechanical cost**: re-deriving `britton_via_tower` (8.7k lines) + `normal_form_afp_textbook`
(12.4k lines) so the base is a predicate presentation. **I checked how the machinery consumes
`base.relators`, and it is index/`Seq`-based throughout, NOT membership-based:**
- `data.base.relators.len()` (enumerate count) and `data.base.relators[r]` (index a specific
  relator) — `britton_via_tower.rs:282, 309–311, 1273, 1419, 1503`.
- the AFP free-product **builds** its relator list as `fp.relators = p1.relators ++
  shift(p2.relators)`, indexed by position (`k < p1.relators.len()` vs `k - p1.relators.len()`) —
  `amalgamated_free_product.rs:161–175`.
- the tower materializes each level as `shift_word(data.base.relators[r], k·ng)` over `r <
  base.relators.len()`.

**Verdict: a predicate base is NOT a parameter swap — it is a re-architecture.** Conceptually it is
clean (the base relators enter ONLY as `{ shift_word(w, k·ng) : P(w) }` = a shifted predicate, and
the tower depth is finite, so the tower's relator set is a finite union of shifted base-predicates +
finite junction relators). But mechanically, **every `relators[i]` / `relators.len()` site (dozens,
across the 21k lines) must be rewritten to predicate-membership form.** Keeping `PredPresentation`
*separate* from the finite `Presentation` protects the existing tower from regression but does NOT
save the proof cost — you re-derive the tower over the predicate. This matches the re-evaluation's
caution ("may be the bulk of the work") and is the honest cost of Fork-A. *(It is still far better
than Fork-B, whose core is undesigned new math — here the math is standard, only the labor is large.)*

### The finite-core escape hatch is a CONFIRMED dead end
One might hope to dodge predicate-Britton: `h3_pres` (FINITE) literally *is*
`HNN(H₂_fin, aᵢ, k | finite associations)` where `H₂_fin` = `h3_pres` minus the `aᵢ`/`k` stable
letters and their relations (= K_M relations + `bᵢcⱼ=cⱼbᵢ` + `p⁻¹tp=td`, all finite). The EXISTING
finite britton applies to this directly. **But** base-embeds-in-HNN needs the `aᵢ`/`k` associations
to be isos *in `H₂_fin`* — and in `H₂_fin` (no family (II)) they are exactly the **"virtual" isos**
that the C3.2/C4 sessions proved un-establishable (family (II) is a consequence of (I) only *with*
the `aᵢ` present — circular). So the finite core cannot host the iso; the infinitely-presented `H₂`
is genuinely required. This is *why* the previous sessions' route failed, restated cleanly.

---

## 4. Minimal infra shape (proposed — confirm with Danielle before building)

1. **A predicate base.** Either generalize `Presentation.relators` to `spec_fn(Word) -> bool` behind
   a new `PredPresentation` kept SEPARATE from the finite `Presentation` (so the 21k-line finite
   tower is untouched), or add a predicate-relator base only where used as `HNNData.base`.
2. **`equiv_in_pred_presentation`** + the predicate analog of `shift` (shift the relator predicate).
3. **`hnn_associations_isomorphic` over the predicate base** (associations stay a finite `Seq`).
4. **`britton_pred_lemma` / a base-embeds-in-HNN over a predicate base.** *Note:* we may need only
   the **embedding direction** (`H₂ ↪ H₃`), which could be lighter than the full predicate normal
   form — a scoping question for the co-design.
5. Layer-2 then follows Cohen §1: recognize `A/Aᵢ/A₊/A₋` (Prop 1.34 analog), read off the isos
   (relabeling; von Dyck + c-kill endo), apply base-embeds. **No `map_a`/`map_b` Britton-peel, no
   σ-orbit, no virtual iso.** The R1–R4 directional machinery becomes unnecessary for this route
   (it was solving a problem Cohen doesn't have).
6. **Force multiplier:** the same predicate-presentation infra unblocks **Layer 0.5** (state
   `L = C ⋆ F₂` over infinitely many `cᵢ`). One foundation, both frontiers — as
   `brick5-fork-reevaluation.md` §2 already argued.

### Concrete first brick (de-risk #2, non-committing)
The code survey above already shows the AFP/tower is index/`Seq`-based, so the residual question is
no longer "does it port?" (it doesn't, trivially) but **"how big is the predicate re-derivation, and
is the lighter embedding-only variant enough?"** The minimal non-committing probe:
1. Define `PredPresentation { num_generators, relators: spec_fn(Word)->bool }` and
   `equiv_in_pred_presentation` + predicate-`shift` (`Q_k(v) := P(unshift(v, k·ng))`). Signature
   only — no proofs.
2. State (not prove) `britton_pred_embeds`: the base-embeds direction
   (`w` over base gens, `w ≡ ε` in `hnn_pred_presentation` ⟹ `w ≡ ε` in base) — this is ALL Layer-2
   faithfulness needs; the full predicate normal form may be unnecessary.
3. Re-state `lemma_single_step_preserves_syls` over a predicate base and *attempt only its
   base-relator case* (stable-letter-free ⟹ should be predicate-agnostic). Whether this one case
   ports cleanly is the cheapest real signal of the re-derivation's tractability.

If (3) ports and (2)'s embedding-only statement looks self-contained, the full Fork-A build is
justified and scoped. If even (3) drags in the indexed AFP construction, the cost is genuinely
"re-derive the tower," and the co-design should weigh that against any alternative (e.g. a
Bass–Serre / action-based base-embeds proof that sidesteps the AFP normal form entirely).

---

## 5. What is SOLID vs PROPOSED (carry-over from the re-evaluation, sharpened)

- **SOLID (act on it):** Cohen's faithfulness uses Prop-1.34 recognition + cheap isos over an
  **infinitely-presented `H₂`**, NOT Britton-peel of the `aᵢ`/`k` level (§1, primary-source). The
  Fork-B virtual engine is undesigned (re-evaluation §1). The Layer-1 facts the recognition needs —
  properties (ii), (vi), (vii) — are **already DONE**. Predicate-Britton is standard math (§3).
- **PROPOSED (confirm with real Danielle before the build):** the Fork-A predicate-presentation
  foundation (§4). The gating unknown is now narrowed to **one concrete question** — does the
  AFP-tower `shift`/normal-form machinery generalize to a predicate base, or do we need the lighter
  embedding-only variant? — answerable by the §4 first-brick prototype.

---

## 6. Non-committing code-level sharpening of scoping #2 (2026-06-23, session 10)

A read-only investigation (no `.rs` touched) drilled past §3's *breadth* survey (how `base.relators`
is consumed across the tower) into the *depth* of the single lemma the Fork-B re-evaluation flagged
as the iso bottleneck — `lemma_single_step_preserves_syls` (`britton_via_tower.rs:8579`) — and read
the literal definition of `hnn_associations_isomorphic` (`hnn.rs:74`). Three machine-grounded results,
each **de-risking** the Fork-A scope:

### 6a. The gating lemma's base-relator branch is *substantively* predicate-agnostic
`lemma_single_step_preserves_syls` dispatches a relator-application step
(`lemma_relator_insert_preserves`, `:8388`) into a base branch and an HNN branch. In the **base
branch** (`:8440–8476`), `relator_index` enters in exactly **two** places, both with clean predicate
analogs:
  1. **Fetch the word** — `base_rel = data.base.relators[idx]`. Predicate analog: carry the relator
     *word* on the derivation step, gated by `P(word)`.
  2. **Assert triviality** — `lemma_relator_is_identity(data.base, idx)` ⟹ `equiv(base_rel, ε)`. That
     lemma (`presentation_lemmas.rs:347`) derives the relator's triviality from a **one-step
     `RelatorDelete` derivation** — i.e. it is just the *defining closure axiom* of a presentation.
     Predicate analog: a `RelatorDelete` carrying the word, firing on any `w` with `P(w)`. Trivial.

Everything downstream is **word-level and relator-set-agnostic**: `lemma_textbook_base_only`
(`:4984`, precondition = "`w` is stable-free", zero reference to relators) and
`lemma_trivial_middle_preserves_syls` (`:8158`, takes `middle` as a word with an "acts-trivially"
precondition, **no** reference to indices / cardinality / the relator set). So the hard substance of
the gating lemma **ports with no new math** — confirming §3's "standard math" verdict at the level of
the actual proof, not just the consumption-site census.

### 6b. The `hnn_associations_isomorphic` requirement is confined to the *finite* HNN branch — the Fork-B obstruction dissolves
The `hnn_associations_isomorphic(data)` precondition (the Fork-B re-evaluation §1 obstruction: "the
universal `∀w` iso over an arbitrary derivation") is consumed **only** in the HNN-relator branch
(`:8477–8500`, via `lemma_hnn_relator_preserves`), **never** in the base branch. Under Fork-A the HNN
associations stay finite and the iso is **genuinely true** (the base `H₂` carries family (II)), so the
universal requirement is **satisfiable** — exactly what Fork-B could not supply. The base branch,
where all the predicate-ness lives, is iso-free. Clean separation: predicate-ness ⊂ base; iso ⊂
finite HNN branch.

### 6c. Associations are INHERENTLY finite — no infinitely-generated-associated-subgroup machinery needed
The literal spec (`hnn.rs:74–83`):
```
let k = data.associations.len();              // a Seq length — FINITE by construction
forall|w| word_valid(w, k) ==>
    equiv_in_presentation(base, apply_embedding(a_words, w), ε)
    <==> equiv_in_presentation(base, apply_embedding(b_words, w), ε)
```
The iso side-condition quantifies over words on `k = associations.len()` generators and reduces
**entirely** to `equiv_in_presentation(data.base, ·, ε)`. It is **not even well-formed** for infinitely
many associations. So the H₃-level associations (`A↔Aᵢ`, `A₊↔A₋`, all between Cohen's *finitely
generated* `A=⟨t,x,d,bⱼ,p⟩` etc.) are finite generator-tuples; the **only** thing needing predicate
support is `data.base = H₂`'s relator set. A worry raised (and initially asserted by the companion
model) — "Prop-1.34 recognition forces infinitely-generated associated subgroups as a literal object"
— is a **false alarm**, refuted by the spec. The Prop-1.34 recognition is a *proof device* whose
formal residue is (i) Layer-1 properties (ii)/(vi)/(vii) [DONE] and (ii) the von-Dyck *biconditional*
above over the predicate base; injectivity (the "no-collapse" backward direction) comes free from the
inverse homomorphism (c-killing endo), **not** from a normal form on `A₊`. *(Companion model agreed on
the spec-grounded reading after the over-assertion was checked against the definition.)*

### Net effect on the decision
Scoping #2 splits into two questions, and 6a–6c **close the first**:
- **"Is predicate-Britton new math (a Fork-B-style dragon)?"** — **NO, confirmed at code level.** The
  gating lemma ports; the iso obstruction dissolves; associations stay finite; only the **base relator
  set** goes predicate. Standard math.
- **"How big is the mechanical labor?"** — **STILL OPEN, unchanged.** Re-deriving the index/`Seq`-based
  tower (`britton_via_tower.rs` + `normal_form_afp_textbook.rs`, ~21k lines) over a predicate base is
  the real cost (§3 verdict stands). The §4 first-brick prototype (steps 1–3, esp. porting the
  base-relator case of `lemma_single_step_preserves_syls` — which 6a shows *should* port) remains the
  cheapest way to measure it, and the lighter **embedding-only** variant (§4 step 4 / §4-probe step 2)
  may shrink it. This is the piece to weigh in the co-design.

---

## 7. Critical-path + relator-consumption census (2026-06-23, session 11)

A second read-only pass (no `.rs` touched, peer-reviewed against the local companion model) drilled
the §6 "STILL OPEN" labor question two levels deeper: (a) the **exact Britton entry point** Layer-2
faithfulness consumes and what it transitively needs, and (b) **where in the 21k lines the predicate
change actually lands** vs. ports untouched. Four code-grounded results.

### 7a. The embedding-only hope (§4 step 4) is largely FALSE — the normal form is on the critical path
Layer-2 faithfulness (`f_free_a1.rs:357`, B4) calls **exactly one** Britton entry point:
`lemma_single_hnn_base_faithful` (`machine_group.rs:4284`) — base-embeds-in-HNN, the *one* direction
Cohen's §1 needs. Its body (read in full) routes through three britton_via_tower lemmas:
`lemma_tower_textbook_chain_from_hnn_iso` (`:2086`), `lemma_hnn_derivation_to_tower_equiv`,
`lemma_copy_s_embeds` (`:2130`). **All three reach into `normal_form_afp_textbook`:** the chain calls
`lemma_iso_implies_apc` (action-preserves-canonical) and `copy_s_embeds` calls
`lemma_afp_injectivity` + `lemma_afp_injectivity_right`. So the embedding direction **rests on the AFP
normal-form injectivity** — you cannot drop the 12.4k-line normal form and keep base-embeds. *The §4
"embedding-only may be lighter" optimism is refuted for the normal form itself* (it may still skip the
two-sided/uniqueness packaging, but the core injectivity is load-bearing). Both files stay on the path.

### 7b. But the predicate change lands on a THIN, localized layer — not the 21k lines of math
Census of how the two big files touch **base** relators (the thing going predicate):
| File | indexed `.relators[i]` | `.relators.len()` | abstract `equiv_in_presentation` |
|---|---|---|---|
| `normal_form_afp_textbook.rs` (12.4k) | 10 | 5 | **215** |
| `britton_via_tower.rs` (8.7k) | 32 | 17 | **104** |

The ~319 abstract sites carry the actual normal-form/injectivity **mathematics** and use
`equiv_in_presentation(base,·,·)` as a **black box**. The 64 indexed/enumeration sites are where a
predicate base bites — and they **cluster**: in the normal form, ALL 15 sit in a **single** lemma
(`:6023–6058`, the "is the i-th AFP relator a `p1` relator or a shifted `p2` relator" case-split),
whose downstream consumer `lemma_g2_relator_acts_trivially` is **word-keyed, not index-keyed**. In the
tower, the 49 sites spread over **~11 functions, all in the relator-bookkeeping layer**
(`lemma_base_relator_in_tower`, `lemma_translate_relator_valid`, `lemma_net_level_get_relator`,
`lemma_relator_insert_preserves`, …) — materialize / translate / validate a relator at a tower level.
**None of the 64 sites are the injectivity argument itself.**

### 7c. The relator-by-INDEX lookup is localized to ONE spec fn — predicate-ification has a small genuinely-new core
`DerivationStep::RelatorInsert/Delete { position, relator_index: nat, inverted }` (`presentation.rs:35,37`)
carries the relator **by index**; the index→word lookup happens **only** inside `apply_step`
(`:68–78`, via `get_relator(p, idx, inverted)`). Everything above it — `derivation_produces`,
`derivation_valid`, `equiv_in_presentation`, and the closure lemmas `lemma_equiv_refl` /
`lemma_equiv_transitive` / `lemma_derivation_concat` (`:124–172`) — is **completely relator-set-agnostic**
(touches `.relators` zero times; only calls `apply_step`). So the predicate core is small and concrete:
change the step to carry the **word** guarded by `P(word)`, rewrite `apply_step`, and the entire
equivalence/derivation algebra ports **verbatim** under `Presentation → PredPresentation`. This is the
"genuinely-new but bounded" piece — a few hundred lines around `presentation.rs` / `presentation_lemmas.rs`,
**not** spread through the 21k.

### 7d. The peer's witness/decidability concern is real but CONFINED to relator-introduction sites
The companion model flagged the sharpest risk: with `relators: spec_fn(Word)->bool`, any proof that
relied on the solver to *find* a relator must now supply an explicit witness (`word` + `P(word)`).
**Code check: there are ZERO `choose|r|…relators` / `relators.contains` sites in either 21k-line file.**
The 319 abstract consumers never name a relator, so they incur **no** witness friction. The friction
lands **only** where a `RelatorInsert`/`Delete` step is *constructed* (i.e. a proof must say *which*
relator) — exactly the ~13 bookkeeping functions of 7b plus `lemma_relator_is_identity`
(`presentation_lemmas.rs:347`). There, "supply the word + `P(word)`" is precisely §6a's "trivial"
port (the defining closure axiom of a presentation). The peer's **second** caution stands honestly: a
*separate* parallel predicate tower still has to be made to **compile** — ~21k lines copied with the
type swapped is real keystroke/compile-fix labor even with **no new proof obligations** beyond 7c's
core + the 7b bookkeeping rewrites. "Mechanical" ≠ "free."

### Net (sharpens §6, does not overturn it)
The honest re-estimate of scoping #2's open half: predicate-Britton for the embedding direction is a
**large mechanical port, not a mathematical re-derivation**. Decomposition:
1. **Genuinely-new core (small, ~hundreds of lines):** `PredPresentation` + word-carrying
   `DerivationStep` + `apply_step` + the relator-introduction/`is_identity` axiom. (7c)
2. **Bounded rewrite (~13 functions):** the relator-bookkeeping layer + the one normal-form
   enumeration lemma, indexed→predicate-membership. (7b)
3. **Mechanical type-swap (~319 sites + the injectivity math):** `equiv_in_presentation →
   equiv_in_pred_presentation`; **no new math**, but real compile-fix labor on a parallel tower. (7b,7d)

The gating unknown narrows to **"how many compile-fix cycles does the type-swapped parallel port take?"**
— measurable, not open-ended. **Both this session and the peer independently converge on the same
cheapest probe:** predicate-ify ONE `equiv_in_presentation`-using lemma and watch whether SMT still
discharges it automatically; if it doesn't, the mechanical estimate is optimistic. This is the §4
first-brick prototype — the right first move.

---

## 8. The §4 first-brick prototype — RUN, result POSITIVE (2026-06-23, session 12)

The non-committing probe of §4 / §7's "cheapest signal" was **built and verified**:
`src/pred_presentation.rs` (commit `75ed225`), a faithful predicate-base port of the WHOLE of
`presentation.rs` — `PredPresentation { num_generators, relators: spec_fn(Word)->bool }`,
word-carrying `PredDerivationStep`, `apply_step_pred`, `pred_derivation_produces`,
`equiv_in_pred_presentation`, the closure algebra (`refl`/`concat`/`transitive`), and the genuinely-new
reversibility core (`invert_step_with_context_pred`, `lemma_pred_single_step_reversible`,
`lemma_pred_step_preserves_word_valid`, `lemma_pred_derivation_reversible`, `lemma_pred_equiv_symmetric`).

**Result: `8 verified, 0 errors` on the first try — identical to the original `presentation` module
(8/0).** Kept SEPARATE from the finite tower (`#[cfg(verus_keep_ghost)] pub mod pred_presentation`),
so reversible (delete file + line) and zero regression risk. What it empirically establishes:

- **The predicate type works in the tactus Lean backend.** `spec_fn(Word)->bool` as a struct field +
  `(p.relators)(w)` application + `#![trigger (p.relators)(w)]` all verify (consistent with the
  already-verified `tower_peel`/`kp_pinch` spec_fn usage). No closure-ABI friction at this layer.
- **§7c CONFIRMED at the code level:** the relator-set-agnostic algebra (`pred_derivation_produces`,
  `equiv`, refl, concat, transitive) ported **byte-for-byte modulo renames** and closed unchanged.
- **§6a + §7d CONFIRMED:** the word-carrying relator core ported with **no new math and no witness
  friction.** The `(p.relators)(relator)` guard, extracted from `apply_step_pred(...) == Some(_)`,
  feeds `word_valid` exactly as `presentation_valid` + the index bound did; inverting a
  `RelatorInsert{relator}` to `RelatorDelete{relator}` carries the SAME word ⟹ `P(relator)` preserved
  with NO `choose` — precisely §7d's prediction.

**What this DOES settle:** the *foundational* layer of scoping #2 — "is a predicate base + the
derivation/equivalence algebra mechanically portable with SMT still closing?" = **YES**, demonstrated,
not just argued. The "type swap + SMT still closes" hypothesis holds where the math is relator-agnostic
(the ~319 abstract consumers' substrate) and where the small genuinely-new core lives.

**What this does NOT settle (honest scope):** this is the self-contained `presentation.rs` core only.
It does NOT exercise (a) the indexed AFP/tower bookkeeping (~13 functions, the `shift` machinery,
`amalgamated_free_product.rs:161-175`), nor (b) `lemma_single_step_preserves_syls`'s full tower context,
nor (c) whether the ~319 abstract sites recompile without per-site fixes once the base type is swapped
under them. Those are the *bulk* of the labor and remain unmeasured — the probe de-risks the
foundation and the method, not the total cycle count. The honest re-estimate of §7's three-part
decomposition stands; part 1 (the genuinely-new core) is now **demonstrated tractable**.

**Decision status:** the *finding* (Fork-A's foundation ports cleanly) is solid — act on it. The
**multi-week full-build commitment remains Danielle's go/no-go** (it re-opens the 2026-06-21
co-designed fork). This session deliberately did NOT proceed past the non-committing probe into the
tower port. NEXT (pending Danielle's go): the next measurement up — port the base-relator case of
`lemma_single_step_preserves_syls` over a predicate base (§4-probe step 3 proper, which needs a
predicate `HNNData`/`shift`), the cheapest signal for part 2/3 of the labor.
