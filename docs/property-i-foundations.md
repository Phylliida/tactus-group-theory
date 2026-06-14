# Property (i)–(iii) foundations — the bedrock map (felt out 2026-06-12)

The faithfulness crux is **property (iii)** = the quad-level `hnn_associations_isomorphic`
(unlocks Britton at quad levels). This doc maps what (iii) bottoms out in, what the substrate
gives, and what must be *built*. Result of feeling it out: the foundation is deeper than "use the
free-product toolbox" — it needs a stack of free-group/abelian word-problem infrastructure.

## The dependency chain, all the way down

```
(iii) quad iso  ⟸  (ii) basis of T∩⟨t(i,j),xᵐ,yᵐ⟩  ⟸  (i) T=⟨t⟩^A free on {t(r,s)}
                                                      ⟸  free-FACTOR triviality
                                                         (tⁿ≢ε; xᵖyᵠ≢ε unless 0)
                                                      ⟸  a WORD-PROBLEM INVARIANT
                                                         (none exists yet — must build)
```

## What the substrate gives (good)

- **brick 28**: `base_A() == free_product(⟨t⟩, ⟨x,y|xy=yx⟩)`. So the verified toolbox applies to A:
  `lemma_free_product_injective_left(p1,p2,w)` (w in left + ≡ε in FP ⟹ ≡ε in p1), `_injective_right`,
  `lemma_free_product_reflects_left`. Built on retraction homs (`fp_left_retraction` collapses the
  right factor, keeps the left) + `lemma_hom_preserves_equiv`.
- `abelianization.rs`: `lemma_abelianization_preserves_equiv` — but this is only the *inclusion*
  direction (adding relators ⟹ more things equal). It does NOT detect non-triviality.
- `reduction.rs`: free-reduction uniqueness — `lemma_reduces_to_reduced_unique`,
  `lemma_normal_form_is_reduced`, `lemma_reduced_is_own_normal_form`, `lemma_singleton_is_reduced`.
- `lemma_reduces_to_equiv` (presentation_lemmas:686): `reduces_to ⟹ equiv` — the EASY direction only.

## What's MISSING (the gap the feel-out found)

The toolbox reduces A-triviality to free-FACTOR triviality (`tⁿ≢ε` in `⟨t⟩`), but **nothing proves
that**:
- **No exponent-sum invariant.** (grep: none.)
- **No `equiv ⟹ reduces_to` bridge** (the reverse of `lemma_reduces_to_equiv`) — i.e. no "free
  groups have decidable word problem / equiv = free equality." `equiv_in_presentation(p,w1,w2)` is
  `∃ Derivation d. derivation_valid(p,d,w1,w2)`; only `reduces_to ⟹ equiv` exists.

So even `tⁿ ≢ ε` (the smallest property-(i) consequence) needs NEW foundational infra.

## The Derivation machinery (for building the invariant)

`enum DerivationStep`: `FreeReduce{position}` (remove an inverse pair), `FreeExpand{position,symbol}`
(insert an inverse pair), `RelatorInsert{position,relator_index,inverted}`,
`RelatorDelete{position,relator_index,inverted}`. `Derivation{steps: Seq<DerivationStep>}`.
`derivation_valid(p,d,start,end) := derivation_produces(p, d.steps, start) == Some(end)`.

## Recommended first brick: the exponent-sum invariant

Define `texp(w): int = Σ_i (w[i]==Gen(0) ? +1 : w[i]==Inv(0) ? -1 : 0)` (and generally `gexp(g,w)`
per generator `g`). Prove **`equiv_in_presentation(p, w1, w2) ∧ (∀ relator r ∈ p. gexp(g,r)==0)
⟹ gexp(g,w1) == gexp(g,w2)`**, by induction on `derivation_produces`: FreeReduce/FreeExpand change
the word by an inverse pair `[s, inv(s)]` whose `gexp` is 0; RelatorInsert/Delete add/remove a
relator (or inverse), each with `gexp` 0 by hypothesis. (For `pres_t` there are no relators, so only
the free moves occur; `base_A`'s single relator `[x,y]` has `texp = xexp = yexp = 0`, so this works
directly in A too, skipping the free-product detour for `tⁿ`.)

Immediate corollaries: `tⁿ ≢ ε` for n≥1 (`texp = n ≠ 0`); `x`/`y` independence on exponents.
This is a clean, self-contained ~1–2 brick piece — its own fresh start (needs `derivation_produces`
unfolding). It is necessary but NOT sufficient for (iii): exponent sums see the abelianization only.

## The deep layer above the invariant (property (iii) proper)

(iii) needs the FULL free-product normal form, not just exponent sums: a product of
`{t(a,b)^±, xᵐ^±, yᵐ^±}` is trivial in `⟨t⟩*Z` iff its free-product normal form is empty. Structure:
`t(a,b) = (xᵃyᵇ)⁻¹ t (xᵃyᵇ)` with `xᵃyᵇ ∈ Z` (abelian), so a product collapses to
`(z₀g⁻¹) tᵉ¹ z₁ tᵉ² … tᵉⁿ (g)` with `zᵢ ∈ ⟨xᵐ,yᵐ⟩`. Triviality ⟺ the t-syllable pattern cancels
AND each middle `zᵢ` vanishes — and the SAME abstract condition governs the b-side
(`{t(c,0)^±, xᵐ²^±, y^±}`), because `(xᵐ)ᵖ(yᵐ)ᵠ = 1 ⟺ p=q=0 ⟺ (xᵐ²)ᵖ(y)ᵠ = 1`. That last fact needs
the abelian right factor `Z = ℤ²` with `x,y` independent (an exponent fact via `injective_right`) +
free-product normal-form reasoning. This is the genuinely deep, multi-session core.

## Honest status

Property (iii) is **founded** (brick-28 toolbox) but sits on **several layers of unbuilt
infrastructure**: exp-sum invariant (next brick) → free-factor triviality → T-freeness (i) → basis
(ii) → the free-product normal-form argument (iii). Realistically the largest remaining arc of the
whole construction. The exp-sum invariant is the clean place to start the next session.
