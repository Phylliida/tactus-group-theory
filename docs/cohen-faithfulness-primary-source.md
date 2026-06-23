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

### The genuine residual risk (the gating unknown)
The **mechanical cost**: re-proving / generalizing `britton_via_tower` (8.7k lines) +
`normal_form_afp_textbook` (12.4k lines) so the base is a predicate presentation. The math is
agnostic to finiteness, but the *existing formalization* may have finiteness baked into the AFP
normal-form mechanics — chiefly **how `shift`/the tower materializes a finite relator `Seq` per
level**, and any spot that enumerates `base.relators`. **This is the one thing a prototype must
check before committing the full build.**

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
Before the full build: **prototype `PredPresentation` + the predicate-shift, and attempt the
base-relator case of `lemma_single_step_preserves_syls` over it.** If the base-relator step ports
cleanly (it should — it's stable-letter-free), and `shift` generalizes to predicates without
choking on the AFP normal form, scope #2 is answered "tractable" and the full build is justified. If
the AFP machinery resists the predicate `shift`, that's the real cost signal and a reason to consider
the lighter "embedding-direction-only" variant.

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
