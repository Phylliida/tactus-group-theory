# ψ-injectivity (A2b) — the pinch-induction scope

The remaining mountain of property (iii) / obligation E. Goal **A2b**: the scaling
endomorphism `ψ_{p,q}` (t↦t, x↦xᵖ, y↦yᵠ, p,q≥1) is **injective** on `A = ⟨t,x,y|xy=yx⟩`:

> `apply_embedding(psi_images(p,q), w) ≡ ε in A  ∧  p,q ≥ 1  ⟹  w ≡ ε in A`.

Property (iii) needs the instances `ψ_{m,m}` (for φ_a) and `ψ_{m²,1}` (for φ_b). Both p,q≥1.

## Route: the double-HNN peel (Danielle's chosen HNN-view+Britton route)

`A = HNN(F, y; ⟨x⟩ identity iso)` and `F = ⟨t,x⟩ = HNN(⟨t⟩, x; trivial iso)`.

- **Step 1 — ψ_F injective on F** (the x-peel, over `f_as_hnn`, *trivial* associated subgroup).
- **Step 2 — ψ injective on A** (the y-peel, over `a_as_hnn`, `⟨x⟩` associated subgroup; the
  no-y base case is Step 1).

Do **Step 1 first** — its associated subgroup is trivial, which kills the hardest sub-problem
(see "the wall").

## Tools in hand (all verified)

- `britton_lemma_full(data,w)`: valid+iso+word_valid+`w≡ε`+`has_stable_letter` ⟹ `has_pinch`.
- `lemma_no_pinch_stable_nontrivial` (brick 45): the **contrapositive** — reduced + stable ⟹ `≢ε`.
- `lemma_psi_fixes_t_word` (brick 46): ψ fixes t-words pointwise (`is_t_word(w) ⟹ ψ(w)=~=w`).
- base-faithfulness both levels: `lemma_single_hnn_base_faithful` (A→F), `lemma_f_base_faithful`
  (F→⟨t⟩); bottom `lemma_t_power_nontrivial` (tⁿ≢ε).
- `has_pinch_at(data,w,i,j)`: adjacent-opposite stable @ i,j + `w[i+1..j]` in the associated
  subgroup (for `f_as_hnn` that subgroup is **trivial** ⟹ middle `≡ε` in `⟨t⟩`).
- `stable_count(data,w)` (pub). NOTE the syllable internals (`textbook_act_hnn`,
  `lemma_*_preserves_syls`, `lemma_no_pinch_action_nontrivial`) are **private** — `has_pinch` is
  the only handle, so pinch-correspondence at the `has_pinch` level is unavoidable.

## Step 1 structure (ψ_F injective on F)

Induct on `xcount(w)` = number of `x/x⁻¹` symbols in `w` (a word over {t,x}; define it).
- **xcount 0**: `w` is a t-word ⟹ `ψ_F(w)=~=w` (brick 46) ⟹ `ψ_F(w)≡ε ⟹ w≡ε`. ✓ trivial.
- **xcount ≥ 1**: `ψ_F(w)` has x (stable, p≥1). `ψ_F(w)≡ε` ⟹ `britton_lemma_full(f_as_hnn,ψ_F(w))`
  ⟹ `has_pinch` at (i,j): opposite x's with **middle `≡ε` in `⟨t⟩`** — and that middle is a
  t-word, so the middle condition is *automatically* about a trivial t-word (**no `⟨x⟩` issue at
  the F-level — this is the brick-46 payoff**). Then peel and recurse on a smaller `w`.

**The remaining difficulty at the F-level = symbol-position bookkeeping**: ψ_F sends each `x` to a
run `xᵖ`, so a pinch's `x@i`/`x⁻¹@j` in `ψ_F(w)` must be mapped back to the corresponding `x`'s in
`w` (at the boundary of two opposite x-runs with a trivial t-part between) to peel `w` itself.

**RECOMMENDED first brick**: avoid raw index surgery — prove the *reducedness-preservation*
invariant instead:
> **(P)** `w` over {t,x}, `!has_pinch(f_as_hnn, w)` ⟹ `!has_pinch(f_as_hnn, ψ_F(w))`.

Then ψ_F injectivity is clean: if `w` is reduced with ≥1 x, (P) + `lemma_no_pinch_stable_nontrivial`
give `ψ_F(w)≢ε`; so `ψ_F(w)≡ε` forces `w` reducible-or-t-word; reduce `w` (≡-preserving, fewer x)
and recurse. (P) still needs position reasoning but is contained and reusable. A direct
single-pinch-peel induction is the fallback.

## The wall (Step 2, A-level — defer until Step 1 done)

At `a_as_hnn` the associated subgroup is `⟨x⟩` (non-trivial). A y-pinch's middle `= ψ_F(fᵢ) ∈ ⟨x⟩`
must give `fᵢ ∈ ⟨x⟩`, i.e. **`ψ_F⁻¹(⟨x⟩) = ⟨x⟩`**. This is entangled with ψ_F injectivity + the
free-group fact `⟨x⟩ ∩ ⟨t,xᵖ⟩ = ⟨xᵖ⟩` (a power of x inside the free subgroup `⟨t,xᵖ⟩` is a power of
`xᵖ`). Likely needs a *simultaneous* induction (ψ_F injective AND `ψ_F⁻¹(⟨x⟩)=⟨x⟩` together) or a
dedicated free-subgroup-intersection lemma. **This is the genuinely hard remainder.** Note `ψ_{m²,1}`
(φ_b, q=1, y↦y) barely touches the y-level, so it may fall almost entirely to Step 1 — consider
proving the `ψ_{p,1}` case before the full `ψ_{p,q}`.

## Status

Foundations done (bricks 43–46): both base-faithfulness levels, the Britton contrapositive, and
the t-word base case. Next = `xcount` measure + invariant (P) for Step 1. Multi-session; Step 2's
`ψ_F⁻¹(⟨x⟩)=⟨x⟩` is the crux of the crux.
