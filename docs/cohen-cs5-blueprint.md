# CS-5 blueprint — the k von-Dyck iso `A₊ ≅ A₋` over the predicate base

*Written 2026-06-23 (session 24), after CS-4 completed (`cohen-cs4-architecture.md` §5).
Route confirmed with Danielle (companion model): **Route 1 — full Prop-1.34 recognition** for the
forward; the non-free `U`-base rules out a cheap predicate collapse. This doc is the build map.*

Read `docs/cohen-section1-assembly-plan.md` §4 (§1b) and `docs/cohen-faithfulness-primary-source.md`
§1b first — they are the primary-source description of exactly how Cohen proves the k-iso.

---

## 0. What CS-5 asks

The top HNN datum is `h3_pred_data(mm,n,m,is_S) = PredHNNData{ base: h3_pred_upto(2n),
associations: psi_assoc(mm,n) }` (`cohen_h3.rs`). The CS-5 target is

```
  hnn_pred_associations_isomorphic(h3_pred_data(mm,n,m,is_S))
```

which unfolds (`pred_hnn.rs`) to: for every word `w` valid over `|psi_assoc| = q+n+2` generators
(`q = |g_subgens|`),

```
  emb(a_col, w) ≡_{h3_pred_upto(2n)} ε   ⟺   emb(b_col, w) ≡_{h3_pred_upto(2n)} ε
```

where
- `a_col = psi_assoc.0 = [U_1..U_q,  d,  b_1..b_n,  p]`   (the A₊ stated gens),
- `b_col = psi_assoc.1 = [U_1..U_q,  d,  b_1c_1..b_nc_n,  p]`   (the A₋ stated gens),
- `U = g_subgens(mm)` (the Layer-1 machine subgroup gens — finite, **NON-FREE**).

`a_col`/`b_col` images are words over the h2-generators (U=machine `<nk`, d, b_j, p, c_j — all
`< h2_num_gens`), so they are BASE WORDS of the a-tower.

### Tower reduction (reuse CS-4e). By **base-faithfulness up the a-tower** — CS-4e's
`lemma_h3_pred_upto_base_faithful(mm,n,m,is_S,2n,u)` (needs `cs4_levels_iso(2n)` =
`lemma_cs4e_iso_upto(2n)`, DONE) — a word over h2-gens is trivial in `h3_pred_upto(2n)` iff in
`h2_pred`. So CS-5 reduces to the iso **over `h2_pred`**:

```
  emb(a_col, w) ≡_{h2_pred} ε   ⟺   emb(b_col, w) ≡_{h2_pred} ε        (★k)
```

This is the only place CS-5 is non-trivial. CS-5d packages `(★k)` back up to the top datum exactly
as CS-4e did.

---

## 1. The two directions (Cohen §1b)

### BACKWARD `b ⟹ a` — the c-killing endomorphism. **EASY (reuse CS-4b `s_strip`).**
`s_strip : h2_pred → h2_noS_pred` (`cohen_cs4b.rs`, kills every c gen, fixes every non-c gen,
already proven `is_valid_pred_homomorphism` + descends). Key fact: `s_strip ∘ b_col = a_col`
pointwise —
- U/d/p entries are c-free ⟹ `s_strip` fixes them (`lemma_strip_fixes_noc_word`) ⟹ `= a_col[i]`;
- `b_col[bc] = [b_j, c_j]` ⟹ `s_strip([b_j,c_j]) = [b_j]·ε = [b_j] = a_col[bc]`.

So `emb(b_col,w) ≡_{h2_pred} ε` ⟹ (hom preserves equiv) `s_strip(emb(b_col,w)) = emb(a_col,w)
≡_{h2_noS_pred} ε` ⟹ (relator monotonicity, `h2_noS ⊆ h2_pred`) `emb(a_col,w) ≡_{h2_pred} ε`. ∎

Generic helpers this needs (added in `cohen_cs5.rs`, kept out of shared modules):
- `lemma_apply_hom_pred_embedding_compose` — `apply_hom_pred(h, emb(imgs,w)) = emb(comp_pred(h,imgs),w)`
  (pred port of `free_basis::lemma_apply_hom_embedding_compose`).
- `lemma_pred_equiv_relator_mono` — `(∀w. p1.relators(w) ⟹ p2.relators(w)) ∧ same num_gens ⟹
  equiv(p1,a,b) ⟹ equiv(p2,a,b)` (derivation replay; the guard p1 accepts p2 also accepts).

### FORWARD `a ⟹ b` — von Dyck + recognition. **THE HARD ARC (Route 1, CS-4-map_a-scale).**
Cohen recognizes `A₊ = HNN(⟨U⟩∗⟨d,b_j⟩, p | R_α : (α,0)∈H₀(M))` (Prop 1.34 + Layer-1 property
(vi)/(vii): `⟨U⟩∩⟨t_α⟩ = ⟨t_α : (α,0)∈H₀⟩`), then:

1. **Recognition (HARD):** `emb(a_col,w) ≡_{h2_pred} ε ⟹ w ≡_{A₊_pres} ε`. This is the Prop-1.34
   faithfulness of `A₊`, the analog of CS-4's `lemma_map_a_forward` but with the non-free `U`-base
   and the H₀-restriction (where `lemma_theorem1` enters as the circularity-breaker). Likely via a
   **compactness bridge** (reuse CS-4b `lemma_cs4b_compactness` shape) to a finite slice, then a
   finite-slice recognition built from Layer-1 property (vi)/(vii)/`lemma_theorem1`.
2. **bc-von-Dyck (EASY, uses `s_realizes`):** `w ≡_{A₊_pres} ε ⟹ emb(b_col,w) ≡_{h2_pred} ε`, via
   `lemma_emb_respects_source_equiv_pred` with `src = A₊_pres`, `images = b_col`, the relator
   condition `emb(b_col, R_α) ≡_{h2_pred} ε` discharged for each `R_α` by:
   `emb(b_col, R_α) = p⁻¹ U_α p (U_α w_α(bc) d)⁻¹`,  `w_α(bc) = w_α(b) w_α(c)`
   (`lemma_w_bc_split`),  `w_α(c) ≡_{h2_pred} ε` (from `s_realizes`: `(α,0)∈H₀ ⟹ is_S(w_α(c)) ⟹`
   it is an `h2_pred` relator), and `p⁻¹ U_α p ≡ U_α w_α(b) d` (family (II), since `U_α = t_α` in
   `⟨U⟩` for `(α,0)∈H₀`). So `emb(b_col, R_α) ≡ ε`. ∎

`A₊_pres` and `U_α` (the U-word realizing `t_α`) are the structural choices; the H₀-restriction is
Layer-1 (`lemma_theorem1` + property (vi)/(vii)). **This is the genuine multi-session work.**

---

## 2. The realization hypothesis `s_realizes` (plan §2, deferred from CS-1)

`s_realizes(is_S, mm, n, m)` := `∀α. numbers_word(n,m,α) ∧ (α,0)∈H₀(M) ⟹ is_S(w_α(c))`
(`w_α(c) = w_c(c_base(nk),n,m,α)`). One direction of the §3.3 machine bridge; consumed ONLY by the
forward bc-von-Dyck. Defined in `cohen_h2.rs` next to `s_relators_valid`.

---

## 3. Brick sequence (bottom-up; each verifies & commits independently)

- **CS-5a — scaffold + generic helpers.** `s_realizes` (cohen_h2.rs); `k_a_col`/`k_b_col`
  (= psi_assoc cols) + lengths + validity; the two generic pred helpers
  (`lemma_apply_hom_pred_embedding_compose`, `lemma_pred_equiv_relator_mono`).
- **CS-5b — BACKWARD (c-kill).** `lemma_cs5_backward`: `(★k)` ⟸ via `s_strip` + compose +
  monotonicity. Self-contained, high confidence.
- **CS-5c — FORWARD (recognition + bc-von-Dyck).** The hard arc. bc-von-Dyck atom first
  (analog of CS-4a, the easy half), then the Prop-1.34 recognition (compactness + Layer-1).
- **CS-5d — tower lift + iso.** Package `(★k)` to `hnn_pred_associations_isomorphic(h3_pred_data)`
  via CS-4e's `lemma_h3_pred_upto_base_faithful` at `k=2n`. Mirror of `lemma_cs4e_iso_upto`'s top.

CS-5a/CS-5b are the FA-4-style high-confidence bricks (this session). CS-5c is the genuine work.
No verifier bypasses (standing rule).
