# E2.B — Property (v) = `prop_v_holds`. The last hole feeding `lemma_vi`.

*The single remaining obligation of the property-(vi) collapse. After this, `lemma_vi`
(`A∩⟨T(M),rᵢ,lⱼ⟩=T(M)`, `tower_peel.rs` 18/0) becomes unconditional.*

## Statement (already pinned in `tower_peel.rs`)

```
prop_v_holds(mm) := ∀ qi<N, ∀ uw: word_valid(uw,3):
    in_TM(mm, emb(hnn_a_gens(quad_data(mm,qi)), uw)) ⟹ in_TM(mm, emb(hnn_b_gens(quad_data(mm,qi)), uw))
  ∧ in_TM(mm, emb(hnn_b_gens(quad_data(mm,qi)), uw)) ⟹ in_TM(mm, emb(hnn_a_gens(quad_data(mm,qi)), uw))
```

`quad_data(mm,qi).associations = quad_associations(mm.quads[qi], mm.m)`. For an R-quad `(a,b,c)`:
`a_gens = [t(a,b), xᵐ, yᵐ]`, `b_gens = [t(c,0), xᵐ², y]`. (L-quad: `[t(a,b),xᵐ,yᵐ] ↦ [t(0,c),x,yᵐ²]`.)
`emb(a_gens,uw)` is a base-A word (a product of `t(a,b)^{±}, x^{±m}, y^{±m}`) — call it `g`.

## The index map (DERIVED & verified against `quad_step`)

`φ` = conjugation by the stable letter (`p⁻¹·a_gen·p = b_gen`, already `lemma_stable_conj_factorization`).
On the residue class it acts by the **machine step itself**:

> For `(α,β)` with `α≡a, β≡b (mod m)`:  `φ(t(α,β)) = t(quad_step(q,m,α,β))`.

Derivation: write `α=u·m+a, β=v·m+b`. The residue telescoping (the `xᵐ/yᵐ` associations) gives
`t(α,β) = (xᵐ)^{-u}(yᵐ)^{-v} t(a,b) (xᵐ)^u (yᵐ)^v`. Apply `φ` (`t(a,b)↦t(c,0), xᵐ↦xᵐ², yᵐ↦y` for R):
`φ(t(α,β)) = (xᵐ²)^{-u}(y)^{-v} t(c,0) (xᵐ²)^u (y)^v = t(u·m²+c, v) = t(α',β')`, and
`quad_step(q,m,α,β) = (u·m²+c, v) = (α',β')`. ✓  The conjugation identities are exactly the (ii)⊇
machinery (`lemma_config_signed_in_G`, `conj_config_signed_by_x/y`) — reuse, do not re-derive.

Since `quad_step` IS `mm_yields` for a matching quad, `lemma_step_preserves_h0` gives
**`(α,β)∈H₀ ⟺ (α',β')∈H₀`** for free, both directions.

## The reduction (A→B; B→A symmetric via φ⁻¹)

Given `g = emb(a_gens,uw) ∈ T(M)`:
1. **`g` has trivial ⟨x,y⟩-image.** `in_TM(g) ⟹ gexp(1,g)=gexp(2,g)=0` (config words have
   `gexp(1)=gexp(2)=0`; `gexp` is base-A-equiv-invariant — `lemma_equiv_in_A_preserves_gexp`).
   *(Clean standalone brick: `lemma_in_TM_gexp_zero`.)*
2. **(ii)⊆** `lemma_ii_subset`: `g ∈ ⟨t(a,b),xᵐ,yᵐ⟩` + `gexp(1)=gexp(2)=0` ⟹
   `in_residue_class(a,b,m,g)` — `g ≡ ∏ t(r_k,s_k)^{±}`, each `r_k≡a, s_k≡b (mod m)`.  ✅ done.
3. **★ THE CRUX — T-free uniqueness:** `g ∈ T(M) = ⟨t(p,q):(p,q)∈H₀⟩` AND `g = ∏ t(r_k,s_k)`
   (residue basis) ⟹ **each `(r_k,s_k) ∈ H₀`.** Because `T = ⟨t⟩^A` is FREE on `{t(p,q)}` (property i,
   config-basis injectivity, `lemma_canw_eval_nontrivial` brick 108): the free-basis expression of `g`
   is unique, so the residue-basis letters that appear must be the H₀ ones. **This is the hard part** —
   property i gives single-word nontriviality; promoting it to full free-basis *uniqueness* (equal
   products ⟹ equal basis multiset, or a normal-form/length argument on the free group on `{t(r,s)}`)
   is the real work. Scope this against `free_product.rs` / the canonical-word normal form used by (i).
4. **Map each letter:** `φ(t(r_k,s_k)) = t(quad_step(q,m,r_k,s_k))` (index map above), and
   `(r_k,s_k)∈H₀ ⟹ quad_step(...)∈H₀` (`lemma_step_preserves_h0`).  So each `φ(t(r_k,s_k)) ∈ T(M)`.
5. **Reassemble:** `φ(g) = emb(b_gens,uw)` (the conjugation telescope, `lemma_stable_conj_factorization`)
   `= ∏ φ(t(r_k,s_k)) ∈ T(M)` (product-closure of `in_TM`, `lemma_product_in_subgroup_pred`). ∎

## Build order

1. **`lemma_in_TM_gexp_zero`** — small, self-contained, unblocks step 2. *(Easy — do first.)*
2. **Index-map lemma (iv)** — `φ(t(α,β)) = t(quad_step)` on the residue class, via (ii)⊇ conjugation
   identities + the residue telescoping. R and L cases. *(Moderate — mechanical, reuses (ii)⊇.)*
3. **T-free uniqueness (the crux)** — `∏ t(r_k,s_k) ∈ T(M) ⟹ each (r_k,s_k)∈H₀`. *(Hard — the
   genuinely new content; budget a focused session, reuse property-(i) normal-form machinery.)*
4. **Assemble `prop_v_holds`** — fuse 1–3 + `lemma_step_preserves_h0` + product-closure; both directions.
5. **Wire** — drop the `prop_v_holds` hypothesis from `lemma_vi`; it becomes unconditional.

## Risk notes

- The **T-free uniqueness** step (3) is the crux and the only deep piece. Everything else is reuse.
  If it stalls, the fallback (`docs/e2-faithfulness-scope.md`, direct pinch-decoding) re-enters — but
  only for property (v) now, not the whole route (the tower peel is already verified).
- Steps 1–2 are good momentum bricks and de-risk the easy 80% before the crux.
- The B→A direction needs `φ⁻¹` = conj by `p` the other way (`lemma_stable_conj_factorization_rev`);
  the residue class on the B-side is `⟨t(c,0)/t(0,c), xᵐ²/x, y/yᵐ²⟩` — mind the asymmetric powers.
