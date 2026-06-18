# Property (II) / (vi) — the deep engine: full sub-arc plan

The hardest remaining piece of obligation E. Goal: **`A ∩ ⟨T(M), rᵢ, lⱼ⟩ = T(M)`** (property vi),
which gives `t(α,β) ∈ ⟨t,rᵢ,lⱼ⟩ ⟹ t(α,β) ∈ T(M) ⟹ (α,β) ∈ H₀(M)` (via vii + the proven T-free).
Source: Aanderaa–Cohen §2, property (II) (paper line 191), (iv)(v)(vi)(vii) (lines 216–235).

## The central structural finding (tower vs. multi-letter HNN)

`B(M)` is implemented in tactus as a **heterogeneous tower** (`b_m_upto`: `A → +r₁ → +r₂ → … → +lⱼ`,
each level a *different* `HNNData` per quad). But conceptually it is a **multiple HNN extension of the
single base `A`**: **every** stable letter `rᵢ,lⱼ` has its associated subgroup *inside `A`*
(`A_rᵢ = ⟨t(aᵢ,bᵢ), xᵐ, yᵐ⟩ ⊆ A`). That common-base structure is what makes property (II) work.

- `britton_lemma_full` is **single-`HNNData`** (one stable letter). The uniform-tower machinery
  (`tower_presentation`, `lemma_tower_injectivity_peel`) is for a *homogeneous* tower — does NOT
  directly model `B(M)`.
- **Multi-letter Britton for `B(M)` is obtained by top-down tower recursion:** the *topmost* stable
  letter present is a single HNN over `b_m_upto(level-1)`, so `britton_lemma_full` gives its pinch;
  if the top level has no stable letter, recurse down. So "some stable pair pinches" is reachable
  level-by-level with the single-HNN tool we already have.

## The pinch-elimination induction (the heart)

An element `w ∈ A ∩ ⟨T(M),rᵢ,lⱼ⟩`: it's a `⟨T(M),rᵢ,lⱼ⟩`-word (factors = `T(M)`-gens and stable
letters) and `w ≡ h` for a base word `h`. **Induct on the number of stable letters in `w`:**
- **0 stable:** `w ∈ ⟨T(M)-gens⟩ = T(M)`. Done.
- **≥1 stable:** `w·h⁻¹ ≡ ε` has a stable letter ⟹ (top-down Britton) `has_pinch` at some adjacent
  opposite stable pair `[sᵢ⁻¹]·a·[sᵢ]`. Two facts about the middle `a = w.subrange(i+1,j)`:
  1. **`a ∈ A_pᵢ`** — directly from `has_pinch_at`'s membership condition
     (`in_generated_subgroup(base, a_gens, a)`).
  2. **`a ∈ T(M)`** — because between two *adjacent* stable letters of a `⟨T(M),rᵢ,lⱼ⟩`-word, the
     segment is a product of `T(M)`-gen factors only (no stable between), hence in `⟨T(M)-gens⟩`.
  So `a ∈ T(M) ∩ A_pᵢ`. **Pinch it out:** `lemma_stable_conj_factorization` replaces `[sᵢ⁻¹]·a·[sᵢ]`
  with `φ(a)`, and **property (v)** gives `φ(a) ∈ T(M) ∩ A_{-pᵢ}`, so the new word `w' ≡ w` is still
  in `⟨T(M),rᵢ,lⱼ⟩` with one fewer stable pair. Apply the IH.

The subtle, must-build pieces are **(1b)** the "middle-is-a-`T(M)`-product" word-structure lemma, and
the **preservation** bookkeeping (φ(a) stays in `⟨T(M)⟩`).

## Sub-brick sequence

1. **Pinch-out helper** — given a pinch `[sᵢ⁻¹]·a·[sᵢ]` in `w` with `a ∈ ⟨a_gens⟩`, build
   `w' ≡ w` with the pair removed and `a` replaced by `φ(a)` (= `apply_embedding(b_gens, u)` for the
   `u` from `lemma_in_gen_implies_emb`), via `lemma_stable_conj_factorization`. *Moderate.*
2. **Middle-in-K** — in a `⟨K-gens ++ [stable]⟩`-word, the segment between adjacent stable letters is
   in `⟨K-gens⟩`. *Moderate* (factor-structure reasoning; new).
3. **Single-HNN property (II)** `lemma_base_inter_gen_eq(data, kgens, w)`: `hnn_data_valid` +
   the **φ-condition** [for every base word `v`: `v∈⟨kgens⟩ ∧ v∈⟨a_gens⟩ ⟹ φ(v)∈⟨kgens⟩`] +
   `word_valid(w, base.num_gens)` + `in_generated_subgroup(hnn_presentation(data), kgens++[stable], w)`
   ⟹ `in_generated_subgroup(data.base, kgens, w)`. Pinch-elimination induction (1)+(2). *HARD — the core.*
4. **Property (iv)** — the generator-map iso of `⟨t(i,j),xᵐ,yᵐ⟩` and of its `T`-intersection
   (from (iii)+(ii)). Needed to state (v). *Moderate.*
5. **Property (v)** — the φ-condition for `T(M)`: for the R-quad `(a,b,c)`, `t(α,β) ∈ T(M)∩A_r ⟺
   t(α',β') ∈ T(M)∩A_{-r}`, because the iso sends `t(α,β)↦t(α',β')` with `(α,β)→(α',β')` and
   `(α,β)∈H₀ ⟺ (α',β')∈H₀`. The reusable content: **machine-step-preserves-H₀** both directions.
   *Moderate* (rests on (ii)⊇ done + the forward step + H₀ definitions).
6. **Property (vi)** — `A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M)`: apply single-HNN (II) top-down the `B(M)` tower,
   K = `T(M)` at the base, φ-condition = (v). *Moderate–hard* (the tower recursion + bookkeeping).
7. **Property (vii)** — `⟨t,rᵢ,lⱼ⟩ = ⟨T(M),rᵢ,lⱼ⟩`: `⊇` since `t=t(0,0)∈T(M)`; `⊆` by the
   **forward-membership induction** `t(α,β)∈⟨t,rᵢ,lⱼ⟩ for (α,β)∈H₀` — *mirror the proven*
   `lemma_reaches_implies_k_commutes` (same induction, membership instead of k-commutation). *Moderate.*
8. **E** — chain (III) `[k,t]=1⟹t∈⟨t,rᵢ,lⱼ⟩` → (vii) → (vi) → (i, T-free) ⟹ `(α,β)∈H₀`. *Assembly.*
9. **F = Theorem 1** — `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)`: E (⟹) + the proven `lemma_reaches…` (⟸).

## Tools in hand vs. to build

- **In hand:** `britton_lemma_full`, `has_pinch`/`has_pinch_at` (its condition *is* the membership
  read-off), `lemma_stable_conj_factorization` (`sᵢ⁻¹·a·sᵢ ≡ φ(a)` — the pinch-out), `factors_to_word`/
  `lemma_in_gen_implies_emb` (factors↔embedding bridge), the membership closures (brick 109),
  property (III) (brick 110), the forward steps, T-free (i), the tower lift/peel lemmas.
- **To build:** pinch-out helper (1), middle-in-K (2), single-HNN property (II) (3, the core), (iv),
  (v), (vi) tower recursion, (vii) forward-membership, E, F.

## ★ REFINEMENT (after building sub-brick 1) — the real structure of the core

Building (1) and thinking harder clarified (2)/(3). The clean textbook proof works on the
**alternating form** `g = k₀ · p^{ε₁} · k₁ · … · p^{εₙ} · kₙ` (each `kᵢ ∈ K`), NOT on raw positional
sub-words:

- **Induct on `n` = the number of `p`-letters in this form** (a *factorization*-level count), not on
  the word's stable symbols.
- **`n ≥ 1`:** `g ∈ A` + Britton ⟹ a pinch `p^{εᵣ}·kᵣ·p^{ε_{r+1}}` with `εᵣ = -ε_{r+1}` and the
  K-block `kᵣ ∈ A_p`. Crucially `kᵣ` is a **single K-factor**, so `kᵣ ∈ K`; thus `kᵣ ∈ K ∩ A_p`,
  and **property (v)** gives `φ(kᵣ) ∈ K ∩ A_{-p}`. Replace `p^{εᵣ}·kᵣ·p^{ε_{r+1}}` by `φ(kᵣ) ∈ K`,
  merge into the neighbouring K-blocks ⟹ an alternating form with `n-1` p's, still `= g`. IH.
- **`n = 0`:** `g = k₀ ∈ K`. Done.

Two subtleties this exposes:
1. **`respects_equiv` is NOT enough for the induction.** `v' ≡ v ∈ ⟨K,p⟩` does preserve *set*
   membership, but it does **not** reduce the p-count of the *factorization* — and the n=0 base case
   needs a p-free factorization. So we must **construct the reduced alternating form explicitly**,
   which is exactly where **property (v)** is essential: it makes `φ(kᵣ)` land in `⟨K_gens⟩` so the
   new form is still a valid `⟨K_gens,p⟩`-factorization. (Property v is not optional plumbing — it's
   load-bearing here.)
2. **The factor↔position bridge is the crux (sub-brick 2).** Britton's pinch is *positional*
   (`has_pinch_at` at symbol indices); the alternating form is *factor-level*. The bridge:
   stable symbols of `g` ↔ the `p`-letters of the form (K-blocks have no stable symbols), so the
   pinch-middle = the K-block `kᵣ` between two p's. Build this as the alternating-form representation
   + "the segment between consecutive p's is a K-block" lemma.

**Revised sub-brick (3) = represent `g` in alternating form (embedding word `u` over `⟨K_gens,p⟩`
indices works) + the p-count induction above.** Sub-brick (2) is the factor↔position bridge feeding it.
Both genuinely intricate — this is the hardest remaining piece, on par with the no-pinch.

## Risk notes

- **Sub-brick 3 (single-HNN property II) is the crux** — the stable-count induction with preservation.
  Build (1) and (2) first as standalone helpers, then assemble (3).
- The **φ-condition statement** (sub-brick 3's precondition) should be quantified over base words
  (`v∈⟨kgens⟩ ∧ v∈⟨a_gens⟩ ⟹ φ(v)∈⟨kgens⟩`), NOT an explicit "intersection subgroup" object —
  keeps it in the `in_generated_subgroup` vocabulary we already have.
- **(vii) is cheap** (mirror `lemma_reaches…`); do it early for momentum and to confirm `T(M)`'s shape.
- Keep faithful to property (I)–(vii); the paper's pinch-elimination is the canonical route.
