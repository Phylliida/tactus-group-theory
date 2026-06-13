# Obligation E — faithfulness (the crux), and F — Theorem 1. Build plan.

Goal: the ⟹ direction of Theorem 1, `k_commutes(t(α,β)) ⟹ (α,β) ∈ H₀(M)`, then assemble
the full iff. The ⟸ direction is DONE (brick 19, `lemma_reaches_implies_k_commutes`).

## Tools in hand (tactus, proven)
- **`britton_lemma_full(data, w)`** (britton_via_tower.rs:8678): `hnn_data_valid ∧
  hnn_associations_isomorphic ∧ word_valid(w) ∧ w ≡ ε ∧ has_stable_letter(data,w) ⟹
  has_pinch(data, w)`. THE engine.
- **`has_pinch_at(data,w,i,j)`** (2392): adjacent-opposite stable letters at i,j with the middle
  `w.subrange(i+1,j)` in the associated subgroup. For `t·g·t⁻¹` (Gen,Inv): `g ∈ ⟨b_gens⟩`; for
  `t⁻¹·g·t` (Inv,Gen): `g ∈ ⟨a_gens⟩`.
- **`in_generated_subgroup(p, gens, w)`** (benign.rs:41): `∃ factors. factors_from_generators(gens,
  factors) ∧ concat_all(factors) ≡ w`. The subgroup-membership primitive.
- For `g_m`: `g_m_associations` is the IDENTITY iso, `a_gens = b_gens = [ [t], [r₀], [l₁], … ]`
  (single-symbol words: `Gen(0)` and every stable letter `Gen(3+i)`, NOT `x,y,k`). Call this
  `g_subgens(mm)`. The k generator is `Gen(3+|quads|) = ng_b` where `ng_b = b_m(mm).num_generators`.

## E1 — property (III) for k:  k_commutes(w) ⟹ w ∈ ⟨t, rᵢ, lⱼ⟩   [TRACTABLE — do first]
`k_commutes(w) = (g_m ⊢ [k]+w ≡ w+[k])`. Right-multiply by `inv(w+[k])`:
the **commutator** `C = [k] + w + [k⁻¹] + inverse_word(w)`  satisfies `g_m ⊢ C ≡ ε`.
`C` has the stable letter `k` (= `Gen(ng_b)`). Apply `britton_lemma_full(gdata, C)` ⟹ `has_pinch`.
When `w` has no `k` (true for `t(α,β)`, over `Gen0,1,2` only), the ONLY stable letters in `C` are
`k` at pos 0 and `k⁻¹` at pos `|w|+1`, so the pinch must be `has_pinch_at(gdata, C, 0, |w|+1)`
(the `t·g·t⁻¹` case) ⟹ `C.subrange(1,|w|+1) = w ∈ in_generated_subgroup(b_m, b_gens=g_subgens, w)`.
**Result:** `k_commutes(w) ∧ (w has no k) ⟹ in_generated_subgroup(b_m(mm), g_subgens(mm), w)`.
Sub-steps: build C + prove `≡ ε` from k_commutes; validity; `has_stable_letter`; argue the only
adjacent-opposite stable pair is (0,|w|+1); read off membership. Needs `hnn_associations_isomorphic(gdata)`
(identity iso — likely a 1-liner) + `has_stable_letter`/`has_adjacent_opposite_at` defs.

## E2 — the deep faithfulness:  t(α,β) ∈ ⟨t, rᵢ, lⱼ⟩ ⟹ (α,β) ∈ H₀(M)   [THE MONSTER]
This is what stalled the Z3 effort (`axiom_machine_group_backward`). `t(α,β) ∈ A` (only `t,x,y`)
AND `∈ ⟨t,rᵢ,lⱼ⟩` (a subgroup of the B(M) tower). Paper §2 route (properties (i),(ii),(vi),(vii)):
- **Property (II) / subgroup intersection (DOES NOT EXIST — must build from Britton):** at each HNN
  step adding stable letter `p` with associated subgroups `Aᵢ,A₋ᵢ` and `K ≤ H` with
  `φ(K∩Aᵢ)=K∩A₋ᵢ`: then `H ∩ ⟨K,p⟩ = K`. Proof = pinches preserve `⟨K,p⟩` (hypothesis) ⟹
  pinch-free form ⟹ Britton ⟹ if in `H` then no `p` ⟹ in `K`. Apply DOWN the B(M) tower, peeling
  one stable letter per level, from `⟨t,rᵢ,lⱼ⟩` to `A ∩ … = T(M) = ⟨t(α',β'):(α',β')∈H₀(M)⟩`.
- **Property (vii):** `⟨t,rᵢ,lⱼ⟩ = ⟨T(M),rᵢ,lⱼ⟩` (so the peel lands in `T(M)`). Uses the ⟸
  induction (brick 19 shows `t(α,β)∈⟨t,rᵢ,lⱼ⟩` for H₀ configs) + `t = t(0,0) ∈ T(M)`.
- **T freeness (property (i)) + free-factor fact:** `T = ⟨t⟩^A` is free on `{t(r,s)}`; `T(M)` is the
  subgroup on the subset `{t(r,s):(r,s)∈H₀}`; a free generator lying in a subset-generated subgroup
  of a free group is in the subset ⟹ `t(α,β)∈T(M) ⟹ (α,β)∈H₀`.
- Each association's `φ` on `Aᵢ = T(M)∩⟨t(a,b),xᵐ,yᵐ⟩` etc. needs property (v) (paper lines 227–232):
  `r⁻¹` maps `T(M)∩⟨t(a,b),xᵐ,yᵐ⟩ → T(M)∩⟨t(c,0),xᵐ²,y⟩` iso, because `(a,β)∈H₀ ⟺ (a',β')∈H₀`.

E2 is a multi-brick sub-project (build property-II generic, the tower peel, T-freeness). Expect it
to dominate the remaining work — honest estimate: the bulk of what's left.

## F — Theorem 1 (assemble the iff)
`k_commutes(t(α,β)) ⟺ (α,β)∈H₀(M)`: ⟸ = brick 19; ⟹ = E1 then E2 (note `t(α,β)` has no `k`,
so E1 applies). Then the headline: `[k, t(α,β)] = 1` is the word-problem instance, decidable-input,
trivial iff the machine halts to the origin.

## Build order
E1 (property III, tractable) → then E2 in pieces: (a) generic property-II subgroup-intersection
lemma via Britton; (b) T-freeness + free-factor membership; (c) tower peel `⟨t,rᵢ,lⱼ⟩ → T(M)`;
(d) glue to `(α,β)∈H₀`. → F.
