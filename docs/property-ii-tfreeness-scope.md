# Property (ii) / T-freeness — scoping pass

Goal of E's remaining two steps:
- **Step 2 (in_T_stable ⟹ in_T):** the pinch-out's config-invariant — a pinch middle `g`
  (product of configs, `∈ T`) that lies in `⟨a_gens⟩ = ⟨t(a,b), xᵐ, yᵐ⟩` must be a product of
  **matching-residue configs**, so the pinch-out result stays a product of configs. = **property (ii)**.
- **Step 3 (in_T ⟹ H₀):** a product of H₀-configs `≡_A config(α,β)` ⟹ `(α,β) ∈ H₀`. = config
  membership / T-freeness.

## Substrate recon (what exists)

- free_product: ONLY `injective_left` / `injective_right` / `reflects_left`. **No normal form,
  no uniqueness, no Kurosh.**
- Britton/act_hnn engine: `textbook_act_hnn`, syllable counts, `hnn_canonical_state`. The
  per-step act lemmas (`textbook_act_concat`/`decompose`/`single_stable`) are **private/opaque**
  (the ψ-injectivity arc deliberately *avoided* them — pivoted to the has_pinch spec level).
- ψ-injectivity precedent: cracked an analogous "needs NF" wall via **britton_lemma_full
  (has_pinch) + pinch-out + induction**, NOT normal-form machinery.

## ★ THE WIN: property (ii) does NOT need Kurosh ★

It reduces to tools **already built**: config-conjugation (brick 81) + the kill-t homomorphism /
exp-sum (bricks 29–30). The argument:

1. `g = emb(a_gens, uw) ∈ T`. The homomorphism `A → ⟨x,y⟩` (kill t: `t ↦ ε`) sends a config to
   ε, `xᵐ ↦ xᵐ`, `yᵐ ↦ yᵐ`. So `image(g) = x^{m·(net gen1 in uw)} y^{m·(net gen2 in uw)}`.
   `g ∈ T ⟹ image = ε ⟹` (since `⟨x,y⟩` abelian ≅ ℤ², m>0) **net gen1 = net gen2 = 0 in `uw`**.
2. With net `xᵐ`/`yᵐ` exponent 0, `emb(a_gens, uw)` is a **product of residue-(a,b) configs**:
   induction on `uw`, carrying an accumulated `xᵏᵐ yˡᵐ` conjugation; each `gen0` (= `t(a,b)`)
   emitted under accumulator `(km, lm)` becomes `config(a±km, b±lm)` — **residue (a,b)** — via
   config-conjugation (brick 81: `x⁻ᵐ·t(r,s)·xᵐ ≡ t(r+m,s)`, `y` analog). The `xᵐ`/`yᵐ` symbols
   only update the accumulator; net-0 ⟹ they fully cancel.
   - Worked check: `[gen1,gen0,gen1⁻¹] = xᵐ t(a,b) x⁻ᵐ = config(a−m, b)` ✓ residue (a,b).
   - `[t(a,b), xᵐ] = config(a,b)·config(a−m,b)⁻¹` ✓ both residue (a,b).
3. So `g ∈ T ∩ ⟨a_gens⟩ ⟹ g ≡` product of residue-(a,b) configs, and the pinch-out result
   `emb(b_gens, uw)` is likewise a product of configs (same induction on the b-side:
   `b_gens = [t(c,0), xᵐ², y]`, config-conjugation by `xᵐ²`/`y` also preserves config-ness),
   **machine-stepped** `(a,b)→(c,0)` — preserves H₀ (forward step from an H₀-config stays H₀).

Estimated ~6–10 bricks (an induction like the abelian sort, brick 38, but emitting configs).
**No free-product NF.** This was the part I'd feared most; it's tractable.

## Step 3 — config membership / freeness (the residual unknown)

`∏ H₀-configs ≡_A config(α,β) ⟹ (α,β) ∈ H₀`. Two sub-parts:
- **config-INJECTIVITY** `config(r,s) ≡_A config(r',s') ⟹ (r,s)=(r',s')`: tractable WITHOUT Kurosh
  — reduces to "centralizer of t in A is ⟨t⟩": `config(r,s) ≡ t ⟺ xʳyˢ commutes with t ⟺ xʳyˢ = ε`
  (free-factor centralizer; `xʳyˢ=ε ⟹ r=s=0` is brick 30 `lemma_x_pow_y_pow_trivial`). The
  centralizer fact is a free-product/HNN fact — likely via injective_left/right or a_as_hnn Britton.
- **product-freeness** (a net-1 product of configs reduces to a single config among them): this is
  the part that genuinely smells like T-freeness. **BUT** likely AVOIDABLE by restructuring: do
  E's induction to track H₀ *directly* through the pinch-outs (each pinch = one machine step;
  maintain "the configs reached are H₀"), so the base case is a single config (config-injectivity
  suffices) rather than a product. Needs design; the H₀-step-preservation is the forward relation
  (already proven, brick 16/19 territory).

## Recommendation

1. **Build property (ii)** via the config-conjugation route above (the big de-risk; ~6–10 bricks).
   First brick: `lemma_config_accumulator_emit` — `emb(a_gens, uw)` with net-0 = product of
   residue-(a,b) configs (induction carrying the xᵏᵐyˡᵐ accumulator).
2. Then assemble **Step 2** (pinch-out induction now closes — middle stays configs, H₀ preserved).
3. Then **Step 3**: build config-injectivity (centralizer route), and design the H₀-tracking
   induction to sidestep full product-freeness.

Net: the arc is **much more tractable than "needs Kurosh"** — property (ii), the feared core, is
config-conjugation + exp-sum, both already in hand.
