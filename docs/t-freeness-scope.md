# T-freeness (prop i) — scoping pass

After property (ii), tracing step 2 end-to-end showed the faithfulness home stretch still needs
**T-freeness** (paper prop i): `T = ⟨t⟩^A` is free on the config words `{config(r,s)}`. Property
(ii) cleared the residue-structure gate; T-freeness is the remaining deep theorem.

## The minimal fact we actually need

**Config-basis injectivity:** a *reduced* word in the config alphabet `{z_{r,s}}` maps to a
**nontrivial** element of `A` (equivalently: a product of configs `≡_A ε` ⟹ it freely reduces to
ε in the config basis). This single fact discharges both remaining obligations:

- **Step 3** (`in_T(config(α,β)) ⟹ (α,β)∈H₀`): take `config(α,β)⁻¹ · (product of H₀-configs) ≡_A ε`;
  by injectivity it freely reduces, so the leading `config(α,β)⁻¹` must cancel a config in the
  product ⟹ some H₀-config `= config(α,β)` ⟹ `(α,β)∈H₀`. (n=1 base: config-injectivity +
  the gexp(0) sign rules out the inverse case.)
- **Prop v / the H₀-tracking** (step 2): a pinch middle `g ∈ T(M) ∩ ⟨a_gens⟩` is re-expressed by
  property (ii) as residue-`(a,b)` configs; injectivity makes that factorization essentially
  unique, so those configs ARE the H₀-configs (machine-stepped to H₀ on the b-side).

## Route: HNN-view + Britton (the ψ-injectivity pattern — NOT Kurosh)

Substrate has **no free-product NF**, but the double-HNN view of `A` + Britton is all proven and
present (confirmed): `a_as_hnn` (`A = HNN(⟨t,x⟩, y; ⟨x⟩)`), `f_as_hnn` (`⟨t,x⟩ = HNN(⟨t⟩, x; ∅)`),
`lemma_no_pinch_stable_nontrivial` (Britton contrapositive), `lemma_pinch_out` (f-level, trivial
subgroup), `lemma_pinch_out_A` (a-level), `lemma_f_base_faithful` / `lemma_a_base_faithful`,
config-conjugation. This is the *exact* toolset that proved ψ_F/ψ_A injective (~20 bricks).

Two layers, because `config(r,s) = y⁻ˢ · h_r · yˢ` with `h_r = x⁻ʳ t xʳ ∈ F = ⟨t,x⟩`:

1. **F-level (s = 0):** the `h_r = x⁻ʳ t xʳ` are freely independent in `F`. Via `f_as_hnn` Britton:
   a between-syllable `tᵉ` (e≠0) is NOT in the trivial associated subgroup `⟨⟩`, so a reduced
   product of `h_r^{eⱼ}` has **no pinch** ⟹ nontrivial (`lemma_no_pinch_stable_nontrivial`).
   The cleanest self-contained first brick.
2. **y-level (general s):** a reduced config product's y-syllables don't pinch either — the
   F-elements sitting between opposite y's are `h_r^e ∉ ⟨x⟩` (the a-level associated subgroup),
   so `lemma_pinch_out_A`'s pinch precondition fails ⟹ no pinch ⟹ nontrivial. Mirrors Step 1 of
   ψ-injectivity (length/syllable induction + Corr + pinch-out).

## Formalization shape

- `config_letter` = `(r:int, s:int, sign:bool)`; a `Seq<config_letter>` is a config word.
- `reduced(w)` = no adjacent `z_{r,s} z_{r,s}⁻¹`.
- `config_word_eval(w)` = `concat_all` of the signed `sconfig(r,s)` (reuse `sconfig`, brick 82).
- **Goal:** `reduced(w) ∧ w.len() ≥ 1 ⟹ ¬ equiv(base_A, config_word_eval(w), ε)`.
- Bridge base_A ↔ a_hnn via the brick-41 Tietze bridge; descend a→F→⟨t⟩ via the base-faithful
  lemmas; bottom = `lemma_t_power_nontrivial` (tⁿ≢ε, brick 29b).

## Dependency tree (the whole remaining E)

```
config-basis injectivity (T-freeness core)   ← the deep piece, ~8-12 bricks, HNN+Britton
   ├── prop i  : in_T(config) ⟹ (α,β)∈H₀                    (step 3)
   └── prop v  : φ maps T(M)∩a_gens → T(M)∩b_gens, H₀-track  (uses injectivity + property ii)
          └── prop vi : A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M)  (Britton subgroup-intersection)
                 └── step 2 / E : t(α,β)∈⟨t,rᵢ,lⱼ⟩ ⟹ (α,β)∈H₀
                        └── F = Theorem 1 iff
```

## Estimate + recommendation

Comparable to ψ-injectivity: the home stretch is ~15-25 bricks, with **config-basis injectivity
the foundational ~8-12**. Every pattern is established (HNN+Britton, no-pinch-nontrivial, the
pinch-out/Corr/length-induction shape, config-conjugation). No new *kind* of difficulty — it's
the third climb up a wall we've now scaled twice (property ii, ψ-injectivity).

**First brick:** F-level config independence (s=0) — `h_r` freely independent in `⟨t,x⟩`, via
`f_as_hnn` Britton no-pinch. Self-contained, reuses `lemma_pinch_out` + `lemma_no_pinch_stable_
nontrivial`, and de-risks the whole y-level layer.
