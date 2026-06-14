# E2.C — the property-II engine (the monster), decomposed against the real tactus machinery

Now grounded in the actual tools (read 2026-06-12): `britton_lemma_full`, `has_pinch_at`, the
property-III template `lemma_k_commutes_implies_subgroup`, and the `in_T`/`in_T_stable` predicates.

## What a pinch actually gives (the lever)

`has_pinch_at(data, w, i, j)` (britton_via_tower.rs:2392) =
`has_adjacent_opposite_at(data,w,i,j)` (the stable letters at i,j are an opposite pair with only
base-group content strictly between them) **AND** the segment `base_word = w.subrange(i+1, j)` lies
in the associated subgroup:
- `w[i]=Gen(ng), w[j]=Inv(ng)`  ⟹  `in_generated_subgroup(base, b_gens, base_word)`   (t·g·t⁻¹, g∈B)
- `w[i]=Inv(ng), w[j]=Gen(ng)`  ⟹  `in_generated_subgroup(base, a_gens, base_word)`   (t⁻¹·g·t, g∈A)

`britton_lemma_full(data,w)`: `hnn_data_valid` + `hnn_associations_isomorphic` + `word_valid` +
`w ≡ ε` + `has_stable_letter(data,w)`  ⟹  `has_pinch(data,w)`.

Property III worked because its word (the commutator `k·w·k⁻¹·w⁻¹`) had **exactly two** stable
letters, at the ends, so the pinch was forced to (0, 1+l) and read off in one shot. The monster's
word has **arbitrarily many** stable letters at unknown positions ⟹ we must *induct*.

## The faithful statement (paper property II, one HNN level)

For a single HNN level `HNN(H, p)` with associated subgroups `A₊ = ⟨a_gens⟩`, `A₋ = ⟨b_gens⟩`, iso
`φ`, and a subgroup `K ≤ H` satisfying the **compatibility** `φ(K ∩ A₊) = K ∩ A₋`:
> `g ∈ H (p-free) ∧ g ∈ ⟨K, p⟩  ⟹  g ∈ K.`

For us (top level, peeling the last stable letter): `H = b_m_upto(mm, nq-1)`-ish, `p = last r/l`,
`K`-membership = (a recursively defined) "product of H₀-config words and *lower* stable letters."
But the cleaner framing for our actual goal threads `K = T(M)` through the **whole** tower at once
(E2.D), so the generic lemma is best stated over an **abstract K-membership predicate**:
`Kmem: spec_fn(Word)->bool` that is (a) a subgroup (closed under product/inverse, contains ε),
(b) base-only (Kmem(w) ⟹ word has no p), (c) φ-compatible at this level.

## Representation: the ⟨K,p⟩-word

Mirror `in_T_stable`: `in_Kp(Kmem, p_idx, w) := ∃ factors. (∀i. Kmem(factors[i]) ∨ is±p(factors[i]))
∧ equiv(P, concat_all(factors), w)`. The induction **measure** = number of factors that are `±p`
(equivalently `net`/syllable count). Base case = 0 such factors ⟹ all factors are K-factors ⟹
`concat_all ∈ K` by Kmem-subgroup-closure ⟹ `g ∈ K`.

## The induction (the heart), as sub-bricks

- **C.1 — measure & base case.** Define the p-count of a factorization; if 0, `concat_all(factors)`
  is a K-product, so `g ∈ K`. (Uses Kmem product/inverse closure — for `K=T(M)` that's
  bricks 24-25, already done.) *Tractable.*
- **C.2 — a ⟨K,p⟩-word with a stable letter, ≡ a p-free `g`, HAS A PINCH.** Build
  `concat_all(factors) · g⁻¹ ≡ ε`; it has a stable letter (some `±p` factor; `g` is p-free);
  `britton_lemma_full` ⟹ pinch. *Mirrors property III's britton call.* *Tractable.*
- **C.3 — PINCH-OUT preserves ⟨K,p⟩ and drops the p-count (THE crux).** The pinch
  `p⁻¹·(base_word)·p` (or `p·_·p⁻¹`) has `base_word ∈ A₊` (resp `A₋`) by `has_pinch_at`. The
  word lies in `⟨K,p⟩`, so `base_word ∈ K ∩ A₊`; **φ-compatibility** ⟹ `φ(base_word) ∈ K ∩ A₋ ⊆ K`;
  splice it in, deleting the `p⁻¹…p`, giving a `⟨K,p⟩`-word with one fewer p, still `≡ g`. This is
  the genuinely new machinery (property III never re-spliced). *Hard — needs a "splice at a pinch"
  word-surgery lemma + the compatibility.*
- **C.4 — induct** on p-count: C.2 gives a pinch, C.3 removes it, recurse to C.1. *Tractable once
  C.3 lands.*

## E2.B — the φ-compatibility (the machine-specific input to C.3)

For each quadruple's association (e.g. R: `t(a,b)↦t(c,0)`, `xᵐ↦xᵐ²`, `yᵐ↦y`):
`T(M) ∩ A₊ ↔ T(M) ∩ A₋` under φ. Because: an element of `A₊ = ⟨t(a,b),xᵐ,yᵐ⟩` ∩ `T(M)` is (by the
paper's property (ii)) a product of `t(r,s)` with `r≡a, s≡b (mod m)`; it's in `T(M)` iff each such
`(r,s) ∈ H₀`; and `(r,s) ∈ H₀ ⟺ (machine-step image) ∈ H₀` (H₀ is step-invariant both ways, by
determinism). So φ (which sends `t(r,s) ↦ t(r',s')` along one machine step) maps the H₀ ones to H₀
ones. **Needs paper property (ii)** (basis of `T ∩ ⟨t(i,j),xᵐ,yᵐ⟩`) — itself not yet built — plus
H₀ step-invariance (close to brick 19's forward + the determinism in `mod_machine_wf`).

## Honest assessment

The monster is **C.3 + E2.B**. Everything else (C.1, C.2, C.4) is tractable and close to existing
patterns. C.3's word-surgery (splice φ(base_word) at the pinch position, re-derive the
factorization, drop the p) is new and fiddly; E2.B needs property (ii), which is a fresh free-group
fact about `T = ⟨t⟩^A`. Realistically several sessions.

## Recommended first sub-bricks (de-risk order)

1. **C.1 (base case)** — most self-contained; reuses T(M) closure (bricks 24-25). A clean win that
   pins the representation/measure. **Do first.**
2. **C.2 (pinch exists)** — direct reuse of the property-III britton call against `concat_all·g⁻¹`.
3. Then confront **C.3** (the splice) with C.1/C.2 in hand; tackle **E2.B** (and its property-(ii)
   prerequisite) in parallel as the machine-side input.

Fallback if C.3's abstract splice stalls: the direct pinch-decoding route (scope doc) — induct on
the witnessing word's stable count, each pinch = one machine step via brick-16 forward relation,
accumulating a computation to (0,0). Less faithful, murkier assembly, but sidesteps defining the
T(M)∩A subgroup intersections.
