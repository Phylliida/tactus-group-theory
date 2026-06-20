# E2.D — Property (vi) via the tower peel. The architectural steer.

*Decision record + build plan for `A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M)`, the convergence point of the
faithfulness crux. Supersedes the tower-handling sketches in `property-vi-plan.md` /
`property-II-plan.md` (those predate the finished abstract engine). Validated 2026-06-20 against
the live code + an independent review pass.*

---

## The decision: top-down tower peel, reusing the single-letter engine

`B(M)` is a **heterogeneous tower** of single-letter HNN steps (`b_m_upto`): level `l` adds stable
letter `Gen(2+l)` over `b_m_upto(l-1)`, carrying quad `l-1`'s associations. The load-bearing fact
(machine_group.rs:287): **every** stable letter's associated subgroup `A_{pₗ} = ⟨t(a,b),xᵐ,yᵐ⟩`
lives inside the *original base A*, not in the grown tower.

We already have a **verified single-letter** property-II engine, `lemma_property_ii(data, in_k, g)`
(`kp_pinch.rs`, E2.C, 21/0). The textbook's multi-letter property (II) is obtained — per
Aanderaa–Cohen and the old `property-II-plan.md` note — by **top-down tower recursion**, peeling one
stable letter per level. So the engine we have *is* the right tool; we do **not** re-derive a
multi-letter Britton. The remaining question was only *how* to wire the recursion. This is it.

### The ladder predicate

```
tmstable_pred_upto(mm, l) = |x| is_tm_gen(mm, x)
    || ∃ i. 0 ≤ i < l ∧ (x == [Gen(3+i)] || x == [Inv(3+i)])
in_TMstable_upto(mm, l, w) = in_subgroup_pred(b_m_upto(mm, l), tmstable_pred_upto(mm, l), w)
```

Endpoints are definitional:
- `in_TMstable_upto(mm, N, ·) = in_TMstable(mm, ·)`   (N = `mm.quads.len()`; full ⟨T(M),rᵢ,lⱼ⟩)
- `in_TMstable_upto(mm, 0, ·) = in_TM(mm, ·)`          (T(M) itself)

### The induction

```
lemma_vi_upto(mm, l, w):
    mod_machine_wf(mm) ∧ mm_terminal(mm,0,0) ∧ prop_v_holds(mm)
    ∧ in_TMstable_upto(mm, l, w) ∧ word_valid(w, 3)
  ⟹ in_TM(mm, w)                                       decreases l
```

- **l = 0:** `in_TMstable_upto(mm,0,w) = in_TM(mm,w)`. Done by definitional fold.
- **l ≥ 1:** Let `data_l = HNNData{ base: b_m_upto(mm,l-1), associations: quad_associations(mm.quads[l-1], mm.m) }`
  (so `hnn_presentation(data_l) = b_m_upto(mm,l)`, stable letter `pₗ = Gen(2+l)`). Instantiate
  `lemma_property_ii(data_l, in_k, w)` with **`in_k = in_TMstable_upto(mm, l-1, ·)`**:
  | property_ii hypothesis | discharge |
  |---|---|
  | `hnn_data_valid(data_l)` | `lemma_quad_associations_valid` + an HNN-validity wrapper |
  | `hnn_associations_isomorphic(data_l)` | `lemma_b_m_step_isomorphic(mm, l-1)` (already proven) |
  | `in_k(ε)` | empty factor list (`in_subgroup_pred` of `ε`) |
  | `in_k` respects `≡_{base}` | `lemma_in_subgroup_pred_respects_equiv` (base = `b_m_upto(l-1)`) |
  | `in_k` product-closed | `lemma_product_in_subgroup_pred` |
  | **H_ab / H_ba (φ-compat)** | **IH + property (v) + T(M)-lift** — see below |
  | `word_valid(w, l+2)` | `word_valid(w,3)` + `lemma_word_valid_mono` |
  | `in_kp_subgroup(data_l, in_k, w)` | **the conversion bridge** — see below |
  Conclusion `in_k(w) = in_TMstable_upto(mm,l-1,w)`; apply the IH `lemma_vi_upto(mm,l-1,w)` ⟹ `in_TM(mm,w)`.

`lemma_vi(mm, w)` = `lemma_vi_upto(mm, N, w)` after folding `in_TMstable_upto(N) = in_TMstable`.

### The φ-compatibility discharge (where IH + (v) meet — the crux of the wiring)

H_ab demands: `∀ uw. word_valid(uw,3) ∧ in_k(emb(a_gens(data_l),uw)) ⟹ in_k(emb(b_gens(data_l),uw))`.
- `A := emb(hnn_a_gens(data_l), uw)` is a word over base A: `a_gens = [t(a,b),xᵐ,yᵐ]` are all
  `word_valid(·,3)`, so `lemma_apply_embedding_valid` gives `word_valid(A,3)`.
- `in_k(A) ∧ word_valid(A,3)` ⟹ **IH** `lemma_vi_upto(mm,l-1,A)` ⟹ `in_TM(mm,A)`. (A ∈ T(M).)
- **property (v)** [`prop_v_holds`]: `in_TM(A) ⟹ in_TM(B)` where `B := emb(hnn_b_gens(data_l),uw)`,
  `b_gens` also `word_valid(·,3)`, so B is a base-A word and **cannot carry a stray stable letter**.
- **T(M)-lift** `lemma_in_TM_implies_TMstable_upto`: `in_TM(B) ⟹ in_k(B) = in_TMstable_upto(l-1,B)`.
  (Every `tm_pred` factor is a `tmstable_pred_upto(l-1)` factor; base-A `≡` lifts to `b_m_upto(l-1)` `≡`.)
H_ba is symmetric (uses the reverse half of `prop_v_holds`). **Soundness:** the IH call is at level
`l-1 < l` — well-founded by `decreases l`; it is used only to *satisfy a precondition* of the engine,
no circularity.

### The conversion bridge (nearly free)

`in_TMstable_upto(mm, l, w)` gives a factor list `factors`, each satisfying `tmstable_pred_upto(mm,l)`,
with `concat_all(factors) ≡_{b_m_upto(l)} w`. The **same list** witnesses
`in_kp_subgroup(data_l, in_k, w)`: case-split each factor `f`:
- `is_tm_gen(f)` — `in_k(f)` (T(M)-gen ⟹ `tmstable_pred_upto(l-1)`) and `word_valid(f, l+2)` (config
  word, valid over 3 ≤ l+2). ⟹ `is_kp_factor` (first disjunct).
- `f = [Gen(3+i)]/[Inv(3+i)]`, `i < l-1` — a *lower* stable letter: `in_k(f)` (single-gen subgroup
  member) and `word_valid(f, l+2)` (index `3+i ≤ l+1 < l+2`). ⟹ `is_kp_factor` (first disjunct).
- `f = [Gen(2+l)]/[Inv(2+l)]`, `i = l-1` — the **top** letter `pₗ`. ⟹ `is_kp_factor` (2nd/3rd disjunct).
Same presentation on both sides (`b_m_upto(l) = hnn_presentation(data_l)`). No regrouping needed —
property_ii's `lemma_kp_factors_to_kpword` does the run-collection internally.

---

## What remains as *isolated* math after this wiring lands

`prop_v_holds(mm)` — **property (v)**, the only hole. Per-quad, in membership form:

```
prop_v_holds(mm) := ∀ qi: 0≤qi<N, ∀ uw: word_valid(uw,3):
    let d = HNNData{ base: base_A(), associations: quad_associations(mm.quads[qi], mm.m) };
    ( in_TM(mm, emb(hnn_a_gens(d), uw)) ⟹ in_TM(mm, emb(hnn_b_gens(d), uw)) )  ∧  (reverse)
```

(Stated with `base: base_A()` since the associations live in A; the embeddings are base-A words, so
this is independent of the tower level it's used at — `data_l` and `d` share `quad_associations`.)

Property (v) = (ii)⊆ [done, `lemma_ii_subset`] + (iv) index-shift iso [**build**] + (v)-machine
[`lemma_step_preserves_h0`, done] + T-free [done]: an `emb(a_gens,uw) ∈ T(M)` is, by (ii)⊆ + T-free, a
product of `t(r,s)` with `r≡a,s≡b (mod m)` and each `(r,s)∈H₀`; (iv) maps `φ: t(r,s)↦t(r',s')`;
(v)-machine gives `(r,s)∈H₀ ⟺ (r',s')∈H₀`; so `emb(b_gens,uw)=φ(emb(a_gens,uw)) ∈ T(M)`.

### Recommended sequencing (revised from AGENDA §5)

1. **E2.D scaffolding + `lemma_vi_upto` (this plan), conditional on `prop_v_holds`.** Verified now;
   converts the vague "tower decision" into one verified induction + one precise remaining lemma.
2. **(iv)** — the index-shift iso (`φ(t(r,s)) = t(r',s')`, the (r,s)→(r',s') relation per quad/x/y).
3. **(v) / `prop_v_holds`** — fuse (ii)⊆ + (iv) + (v)-machine + T-free. Feed into `lemma_vi_upto`.
4. **(vii)⊆** — `lemma_vii_subset` is done (⟨t,rᵢ,lⱼ⟩ ⊆ ⟨T(M),rᵢ,lⱼ⟩); just chain it.
5. **E2.E** — `in_TM → H₀` (T-free read-off) + **E2.glue** (III→vii→vi→i) → **F** (Theorem 1 iff).

Step 1 is the de-risking move: it makes the architecture machine-checked and isolates (iv)+(v) as
the last genuinely-new math on Layer 1.
