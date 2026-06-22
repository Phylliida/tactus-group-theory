# Brick 5 — C3.2: the b-augmented a-level recognition over `h3_II`

Companion to `brick5-completeness-plan.md` §4 C3.2. **C3.1 is DONE** (`h3_ii.rs` 14/0:
`lemma_h3_II_group_preserving`); this doc scopes the next arc — the genuine `tower_peel`-scale cost
of the completeness reroute. Written after studying the existing iso-recognition machinery
(2026-06-22).

---

## 1. The goal (the iso statement)

For each level `l` (`1 ≤ l ≤ 2n`), prove the a-level association is a subgroup isomorphism **over
the family-(II)-augmented base**:

```
lemma_phi_l_iso(mm, n, m, alphas, l):
  requires  1 ≤ l ≤ 2n,  2n < m,  ∀i. numbers_word(n,m,alphas[i]),  <alphas covers the needed β's>
  ensures   hnn_associations_isomorphic(HNNData {
                base: h3_II_upto(mm, n, m, alphas, (l-1) as nat),
                associations: phi_assoc(g_m(mm).num_generators, n, m, l),
            })
```

Unfolding `hnn_associations_isomorphic` (`hnn.rs:74`): with `k = phi_assoc.len() = n + 3` and

- `a_words` (stated gens) `= [t, x, d, b_1, …, b_n, p]`
- `b_words` (images)      `= [t_l = config(l,0), xᵐ, b_l·d, b_1, …, b_n, p]`

the goal is: **for every `w` valid over `k` generators,**
`emb(a_words, w) ≡_B ε  ⟺  emb(b_words, w) ≡_B ε`, where `B = h3_II_upto(l-1)`.

(Recall `b_l` here is the 2n-alphabet letter `alphabet_letter(b_base,n,l)` — `b_{n+i}=b_i⁻¹` — per
`h3.rs` `phi_assoc`; the `b_j↦b_j` block is the literal generators `1≤j≤n`.)

---

## 2. The template (what to copy)

This is **exactly** the shape the machine-group tower already discharges, but over a bigger base and
with the `d↦b_l·d` augmentation. Study, in order:

1. **`lemma_conj_scaling_trivial_iff`** (`machine_group.rs:6522`) — the keystone for a *single*
   config-word HNN over base `A=⟨t,x,y⟩` (3 gens):
   `emb([config(a,b), x^px, y^py], w) ≡_A ε ⟺ w ≡_A ε`. Proven via the scaling endomorphism
   `ψ: t↦t, x↦x^px, y↦y^py` being **injective** (`lemma_psi_A_injective`) + **relator-respecting**
   (`lemma_psi_respects_relator`), wired through `lemma_emb_respects_source_equiv`.
2. **`lemma_quad_data_iso`** (`prop_v.rs:803`) / **`lemma_r_step_associations_isomorphic`**
   (`machine_group.rs:6610`) — package (1) into `hnn_associations_isomorphic` for a quad step. The
   body: identify `a_words`/`b_words` (k=3), then `assert forall|w| … by { lemma_conj_scaling_trivial_iff(...) }`
   on BOTH sides (both reduce to `w ≡_A ε`, so the iff is immediate).
3. **`lemma_b_m_upto_faithful`** (`machine_group.rs:6668`) — the **tower** lift: builds the per-step
   iso INLINE from the IH down the B(M) tower (`decreases i`). This is the structural model for
   threading the φ_l iso down the h3_II a-tower (`lemma_h3_II_upto_relators` already gives the relator
   structure; the faithfulness lift mirrors `lemma_single_hnn_base_faithful` usage).

The two directions (mirror `lemma_conj_scaling_trivial_iff`'s body, lines ~6506–6517):
- **backward** (`w ≡_B ε ⟹ emb(b_words,w) ≡_B ε`): **von Dyck** — the images satisfy every base
  relator (`lemma_emb_respects_source_equiv` + per-relator check). The *easy-ish* half, BUT the
  per-relator check for the p-relator / a_i-relators is exactly where **family (II) is consumed**
  (the witness in §2.2ter reduces because the `β` relator `p⁻¹ t_β p ≡ t_β w_β(b) d` is present in
  `B`). This is why the base must be `h3_II_upto(l-1)`, not `h3_upto(l-1)`.
- **forward** (`emb(b_words,w) ≡_B ε ⟹ w ≡_B ε`): the **faithful/injective** half — the real cost.
  Reduces to the **b-augmented residue facts** (`prop_v`/`tower_peel` territory): the analog of
  `lemma_psi_A_injective` for the scaling-plus-`d↦b_l d` endomorphism, lifted to the tower base.

---

## 3. The b-augmented recognition (the novel content)

The machine-group `ψ` only scales `x,y`. Here the endomorphism also does `d ↦ b_l·d` and `t ↦ t_l`
(= `config(l,0)`, a conjugate-scaling in `x` by the digit `l`). Cohen's Prop 1.34 recognition of `A`
as `HNN(⟨t,x,d,b_j⟩, p | p⁻¹ t_β p = t_β w_β(b) d)` is what makes the stated-gen correspondence a
well-defined iso; `w_{αm+i}(b) = w_α(b) b_i` is the numbering identity that aligns `φ_l`'s images.

Concretely, the forward-direction crux is a **b-augmented `conj_scaling_trivial_iff`**:
`emb([config(l,0), xᵐ, b_l d, b_j, p], w) ≡_B ε ⟺ emb([t, x, d, b_j, p], w) ≡_B ε`. The `b_j`/`p`
coordinates pass through; the `t,x,d` coordinates are the scaling-plus-augmentation that needs the
residue facts. The base-swap COLLAPSE (§2.2bis) says this iso over `h3_II_upto(l-1)` reduces to the
iso over `h2_II` (the bottom) — so the heavy lifting is a SINGLE statement over `h2_II`, then lifted
through the a-tower by base-faithfulness (`lemma_single_hnn_base_faithful`, IH down the tower).

**Reuse inventory** (confirmed present):
- `lemma_apply_embedding_valid`, `lemma_emb_respects_source_equiv` (the von Dyck plumbing).
- `prop_v.rs`: the b-side residue reductions (`lemma_accumulator_inv`, `lemma_in_TM_canon_reduced`,
  the `(m²,1)/(1,m²)` asymmetric moduli) — the closest existing b-augmented residue machinery.
- `tower_peel.rs`: the down-the-tower instantiation pattern (`lemma_vi_upto`, `decreases l`).
- `lemma_single_hnn_base_faithful` / `lemma_quad_base_faithful` (base-faithfulness for the collapse).
- `free_basis.rs` `lemma_basis_elt_free` (the `{t_α w_α(b) d}` free basis = the p-level recognition,
  C2 — feeds the A₊ side; the a-level here is the A≅A_i side).

---

## 4. Brick decomposition (proposed)

1. **C3.2a — structural setup.** Define `lemma_phi_l_iso`'s `a_words`/`b_words`, `k = n+3`, validity
   over `B.num_generators` (mirror `lemma_phi_assoc_valid`). Reduce the iso to the per-`w`
   biconditional. *(Small; good shakedown.)*
2. **C3.2b — backward (von Dyck) over `h3_II`.** Images satisfy each `B`-relator. The h2/φ_{<l}
   relators: routine. The p-relator + a_i-relators: consume **family (II)** (`lemma_II` is already a
   relator of `B` via the splice — this is the payoff of C3.1). 
3. **C3.2c — the b-augmented `conj_scaling_trivial_iff` over `h2_II`** (the crux). The forward
   faithful direction at the bottom of the tower. Port `lemma_psi_A_injective` to the
   scaling-plus-`d↦b_l d` endomorphism, using the residue facts. THE real cost.
4. **C3.2d — tower lift.** Thread C3.2c up `h3_II_upto` via base-faithfulness + the §2.2bis collapse
   (mirror `lemma_b_m_upto_faithful` / `lemma_vi_upto`, `decreases l`). Yields `lemma_phi_l_iso`.

Then C2 (package `free_basis.rs` as the p-level/A₊ recognition) → C4 (Fork-B k-engine, consuming the
C3.2 a-isos + C2; transport back to `h3_pres` via `lemma_h3_II_group_preserving`) → C5.

---

## 5. Honest scope

C3.2 is comparable to a `tower_peel`/`prop_v` sub-arc (multi-session). The C3.1 foundation
(`lemma_same_group_iff`, `h3_II`, group-preservation) is in place and verified, so C3.2 can be built
and transported cleanly. No verifier bypasses (standing rule). Start with C3.2a (structural,
de-risks the setup), then C3.2b (where C3.1's family-(II) splice first pays off), saving the C3.2c
residue crux for a focused push.
