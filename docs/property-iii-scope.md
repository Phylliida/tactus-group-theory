# Property (iii) — the free-product normal-form arc (scoping, pre-build)

The faithfulness crux's gating prerequisite. Scoped 2026-06-12; build it next session.

## Exact goal

`hnn_associations_isomorphic(data)` for the quad data at tower level `qi`:
```
data.base    = b_m_upto(mm, qi)            // the GROWING tower base: 3+qi generators
associations = quad_associations(quad, m)  // k = 3
a_words = [ config_word(a,b),  xᵐ,   yᵐ  ]   (R-quad)   // = images of Gen0,Gen1,Gen2
b_words = [ config_word(c,0),  xᵐ²,  y   ]
GOAL:  ∀ w. word_valid(w,3) ⟹
   equiv(data.base, apply_embedding(a_words, w), ε)  ⟺  equiv(data.base, apply_embedding(b_words, w), ε)
```
`apply_embedding(images, w)` (benign.rs:86) = the substitution homomorphism: `Gen(i)↦images[i]`,
`Inv(i)↦inverse_word(images[i])`, concatenated. `a_words`/`b_words` use ONLY `t,x,y` (Gen0,1,2),
so `apply_embedding(a_words,w)` is always a **base_A-word**, whatever `w` is.

## KEY FINDING: no free-product normal form exists

`normal_form_free_product.rs` / `free_product.rs` give: `free_product`, `shift_word`,
`word_in_left/right`, `left_embeds`, `right_embeds`, `injective_left/right`, `reflects_left`, +
retraction homs. **There is NO normal-form function and NO general "free product of homs is
injective".** So the deep core's tooling must be either *built* or *worked around*. This is the
central design decision for next session.

## Two layers

### L1 — tower-base reduction (inductive on qi, Britton-based)

Since the embedded words are base_A-words, the iso over `b_m_upto(mm,qi)` reduces to the iso over
`base_A`, given **tower faithfulness on base_A**:
```
equiv(b_m_upto(mm,qi), W, ε)  ⟺  equiv(base_A, W, ε)     for any base_A-word W
```
- `⟸` (base_A ⟹ tower): the easy lift — `lemma_lift_to_bm` + `lemma_base_embeds_in_hnn` (already used in the forward steps).
- `⟹` (tower ⟹ base_A): tower FAITHFULNESS — a Britton consequence, needs the tower valid up to `qi`.
  This is **inductive on qi**: iso at level qi needs faithfulness at qi, which needs all isos at
  levels `< qi`. Clean induction: base `qi=0` is `b_m_upto(mm,0)==base_A` (L1 trivial → just L2);
  step assumes lower isos ⟹ tower-up-to-qi valid ⟹ base_A embeds faithfully ⟹ reduce to L2.
- **TODO at build:** find the britton_via_tower lemma that gives "base embeds faithfully in a valid
  HNN tower" from the per-level iso conditions (the consumer of `hnn_associations_isomorphic`).
  Likely already exists since the tower's whole point is Britton.

### L2 — the base_A iso (the mathematical core, level-independent)

`∀w. equiv(base_A, emb(a_words,w), ε) ⟺ equiv(base_A, emb(b_words,w), ε)`.
Both sides ⟺ **`w ≡ ε` in A**, because the substitution maps `φ_a, φ_b: A→A` are INJECTIVE:
- `φ_a`: Gen0↦config_word(a,b), Gen1↦xᵐ, Gen2↦yᵐ.  `= conj_{xᵃyᵇ} ∘ ψ_{m,m}`
- `φ_b`: Gen0↦config_word(c,0), Gen1↦xᵐ², Gen2↦y.   `= conj_{xᶜ} ∘ ψ_{m²,1}`
(`config_word(a,b) = (xᵃyᵇ)⁻¹ t (xᵃyᵇ)`; `xᵐ,yᵐ` are fixed by conjugation since `Z` is abelian.)
`φ injective ⟹ (emb(images,w) ≡ ε ⟺ w ≡ ε)`, so a-iso ⟺ w≡ε ⟺ b-iso.

#### A1 — conjugation invariance (tractable)
`emb(conj_g(images), w) ≡ ε ⟺ emb(images, w) ≡ ε`, where `conj_g(images)[i] = g⁻¹·images[i]·g`.
Route: prove `emb(conj_g(images), w) = g⁻¹ · emb(images,w) · g` (the substitution hom distributes;
conjugation of a product telescopes — like the brick-13 conjugation work), then `g⁻¹Wg ≡ ε ⟺ W ≡ ε`
via insert/delete cancelling pairs (cf. `lemma_conj_solve`, `lemma_cancel_pair_equiv_empty`).

#### A2 — scaling injectivity ψ_{p,q} (THE DEEP CORE)
`ψ_{p,q}: A→A, t↦t, x↦xᵖ, y↦yᵠ` is injective for `p,q ≥ 1`. Equivalently
`emb([t, xᵖ, yᵠ], w) ≡ ε ⟺ w ≡ ε`.
- **A2a — abelian (DONE, brick 30):** `⟨xᵖ,yᵠ⟩ ≅ ℤ²` faithfully — `lemma_x_pow_y_pow_trivial`
  extends to `x^{pi}·y^{qj} ≡ ε ⟹ i=j=0` (since `p,q>0`). The "middle Z-parts vanish" half.
- **A2b — free-product faithfulness (the crux):** `ψ` injective on the whole free product
  `⟨t⟩ * Z`, not just `Z`. The `t`-syllable structure must be preserved. **Needs new infra** — pick:
  - **(i)** build a free-product NORMAL FORM for `⟨t⟩ * Z` (every element = unique alternating
    `z₀ tᵉ¹ z₁ … tᵉⁿ zₙ`), then compute. Most general, most expensive.
  - **(ii)** build "**free product of injective homs is injective**": `ψ = id_{⟨t⟩} * μ` with
    `μ: Z→Z` (x↦xᵖ,y↦yᵠ) injective (A2a). Likely cheaper than full NF and reuses
    `left_embeds`/`right_embeds`/`reflects`. **Recommended first attempt.**
  - **(iii)** direct injectivity via the `reflects` toolbox + A2a (no general meta-theorem).
  De-risk: try (ii) on a small case before committing.

### L3 — assembly
A1 ∘ A2 ⟹ `φ_a, φ_b` injective ⟹ L2 ⟹ (with L1) `hnn_associations_isomorphic` for the quad,
both R and L. Then this validates the HNN tower levels → Britton applies → unlocks faithfulness E.

## Sub-brick plan (next session)

| # | brick | difficulty | tools |
|---|---|---|---|
| 1 | `apply_embedding` distributes over concat / conjugation; `conj_g(images)` helper | easy–mod | benign.rs emb defs, brick-13 conj |
| 2 | A1 conjugation invariance | mod | insert/delete cancelling pairs |
| 3 | A2a extend `x_pow_y_pow_trivial` to the `⟨xᵖ,yᵠ⟩` lattice | easy | brick 30 (done-ish) |
| 4 | **A2b free-product faithfulness of ψ** (route ii first) | **HARD — the core** | left/right_embeds, reflects, A2a |
| 5 | L2 assembly: φ_a, φ_b injective ⟹ base_A iso | mod | 1–4 |
| 6 | L1 tower-faithfulness reduction (find/adapt the tower lemma) | mod–hard | britton_via_tower API |
| 7 | property (iii) = `hnn_associations_isomorphic` for quad data, R + L | mod | 5+6 |

Brick 4 (A2b) is the genuine mountain; everything else is foothills. Recommended order: 1→2→3→5
(get the base_A iso modulo A2b), in parallel scope brick 4's route (ii), then 6→7.

machine_group.rs at scope time: 105 verified, 0 errors, 30 bricks.
