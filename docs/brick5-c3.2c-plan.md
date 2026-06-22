# Brick 5 — C3.2c: the bottom crux (b-augmented `conj_scaling_trivial_iff` over `h2_II`)

The single gating item of C3.2 (see `brick5-c3.2-plan.md` §4/§5). C3.2a (a_words/b_words backbone)
and C3.2d-infra (collapse halves) are DONE (`h3_ii.rs` 20/0); the tower lift (C3.2d) and von Dyck
(C3.2b) are both *inline pieces of the faithfulness induction whose bottom fact IS this crux* — so
none can close until C3.2c exists, and (standing rule) no `assume`-pinned skeleton is allowed.
Written 2026-06-22 after studying the machine-group template + a companion-model design review.

---

## 1. The exact statement

```
lemma_phi_l_iso_at_h2II(mm, n, m, alphas, l):
  requires 1 ≤ l ≤ 2n,  2n < m,  ∀i. numbers_word(n,m,alphas[i]),  <alphas ⊇ the β's w touches>
  ensures  hnn_associations_isomorphic(HNNData {
               base: h2_II(mm, n, m, alphas),
               associations: phi_assoc(g_m(mm).num_generators, n, m, l),
           })
```

Unfolds (with `k = n+4`, `a_words`/`b_words` from `lemma_phi_assoc_index`) to: **for every `w` valid
over `k`,** `emb(a_words,w) ≡_{h2_II} ε  ⟺  emb(b_words,w) ≡_{h2_II} ε`, where
- `a_words = [t, x, d, b_1..b_n, p]` (literal gens),
- `b_words = [t_l=config(l,0), xᵐ, b_l·d, b_1..b_n, p]` (φ_l images).

Both embeddings are `h2`-words (`lemma_phi_l_emb_h2_valid`, already verified).

---

## 2. The template — and where it breaks

The machine-group crux `lemma_conj_scaling_trivial_iff` (`machine_group.rs:6522`) proves
`emb([config(a,b),x^px,y^py], w) ≡_{base_A} ε ⟺ w ≡_{base_A} ε` via:
- `a_as_hnn()` (`machine_group.rs:3935`): `base_A = ⟨t,x,y|[x,y]⟩` recognized as `HNN(free ⟨t,x⟩, y |
  y⁻¹xy = x)` — **base FREE, association TRIVIAL (identity on ⟨x⟩), iso immediate**
  (`lemma_a_as_hnn_isomorphic`: `a_words =~= b_words`).
- conjugation-telescope `emb(aw,w) ≡ ig·pw·g` + `lemma_psi_A_injective` (Britton-peel over `a_as_hnn`).

**Three things break for the b-augmented case (why this is a `prop_v`-scale arc, not a copy):**
1. **The recognition free-base gens are SCATTERED, not a prefix.** ⟨t,x,d,b_j⟩ live at indices
   `0, 1, d_idx=nk+2n, b_idx=nk+n..nk+2n-1` — interleaved with `y=2` and the K_M machine gens
   `3..nk-1` which are NOT in the recognition subgroup. So there is no clean `pres_F` analog of
   `pres_tx`; the recognition is about a **subgroup of `h2_II`**, and `h2_II` itself carries relators
   (h2_pres + family_II). The `a_as_hnn` trick (free base, 0 relators) does not transcribe directly.
2. **The associations are NON-trivial and INFINITE.** Cohen Prop 1.34 recognizes the subgroup
   `A = ⟨t,x,d,b_j,p⟩` as `HNN(F=⟨t,x,d,b_j⟩, p | p⁻¹ t_β p = t_β w_β(b) d, β∈I)`. The associated
   subgroups are `⟨t_β : β∈I⟩` and `⟨t_β w_β(b) d : β∈I⟩` (NOT a single cyclic ⟨x⟩). The iso of the
   association is the **b-augmented residue content** (`prop_v`/`tower_peel` territory), not `=~=`.
   `I` is infinite; `h2_II` carries only the finite `β∈alphas` slice.
3. **φ_l augments `t↦t_l` (digit-scaling in x) AND `d↦b_l·d`.** The endomorphism whose injectivity we
   port from `lemma_psi_A_injective` is scaling-plus-augmentation, not pure scaling.

---

## 3. Sub-lemma ladder (ordered; maps existing infra + companion review)

The companion review (2026-06-22) recommended the **two-direction split (von Dyck + Britton
injectivity)** over the telescope ("the telescope is elegant on paper but a nightmare of induction
indices in a formal system" — plausible here given the augmentation), a **complexity-measure
induction** for the peel (p-count + base-segment length — matches `britton_via_tower`'s `decreases`),
and residue facts as a **standalone base lemma = the Britton-peel precondition**. Mapped to our infra:

**Phase A — residue / base layer (the real cost; reuse `prop_v`/`tower_peel`).**
- **A1 `lemma_tbeta_wb_residue_iso`**: the correspondence `t_β ↦ t_β w_β(b) d` extends to a subgroup
  iso `⟨t_β:β⟩ → ⟨t_β w_β(b) d:β⟩` over `F`. This IS the b-augmented residue fact. Reuse: the
  numbering identity `w_{αm+i}(b)=w_α(b)b_i` (`word_numbering.rs`), and the `prop_v` accumulator /
  `tower_peel` coordinate-survival machinery, lifted to the b-augmented subgroup. **Hardest brick.**
- **A2 `lemma_phi_scaling_injective_F`**: the φ_l endomorphism `t↦t_l, x↦xᵐ, d↦b_l d, b_j↦b_j` is
  injective on `F` (analog of `lemma_psi_A_injective`'s base step). Conjugation-telescope OK at this
  pure-free-group level (no p), so the telescope objection doesn't bite here.

**Phase B — HNN recognition layer.**
- **B1 `recog_data`**: the recognition HNN datum for the φ_l image subgroup over `h2_II` — the
  analog of `a_as_hnn`, but base = the (scattered-gen) free `F` realized inside `h2_II`, stable
  letter `p`, associations the finite `family_II`-slice. Validity + presentation facts (analog of
  `lemma_a_as_hnn_valid`/`_presentation`). **Decide here:** can we present the subgroup recognition
  directly, or must we go through `h2_II` (with its h2_pres relators) and quotient? The scattered
  gens (§2.1) make a clean `pres_F` impossible — likely route is to work in `h2_II` and use that
  `family_II` are *literal relators* (the C3.1 payoff) so the p-pinch resolves.
- **B2 `lemma_finite_beta_suffices`**: any `w`'s Britton p-analysis touches only finitely many β,
  all `∈ alphas` (the finite augmentation covers them). Makes "infinite I" rigorous as "the finite
  slice `h2_II` carries." (Companion's "Local Alphas"; our `h2_II` bakes the finite slice in already,
  so this may be a `requires alphas ⊇ betas(w)` side-condition rather than a separate lemma.)

**Phase C — the crux assembly.**
- **C1 von Dyck (`⟸`, = C3.2b at the bottom)**: `emb(b_words,w)` satisfies every relator the
  `a_words` (literal gens) satisfy in `h2_II`. The p-relator maps to a `family_II` relation — present
  literally in `h2_II` (C3.1). Via `lemma_emb_respects_source_equiv` against the recognition's relators.
- **C2 forward (`⟹`, faithful)**: Britton-peel `emb(b_words,w) ≡ ε` over `recog_data` using A1 (the
  residue iso = the peel's well-definedness precondition) + A2; descend to `F`-triviality, then back
  to `emb(a_words,w) ≡ ε`. Complexity-measure `decreases` (p-count, then base length).
- **C3 biconditional**: combine C1+C2; package as `lemma_phi_l_iso_at_h2II`.

Then C3.2d wraps this in the `decreases l` faithfulness induction (mirror `lemma_b_m_upto_faithful`)
to get `lemma_phi_l_iso` at every tower level.

---

## 4. First verified down-payment for the next session

Start with **A2** (`lemma_phi_scaling_injective_F`) or **B1**'s structural/validity facts — both are
self-contained, mirror an existing proven lemma (`lemma_psi_A_injective` base step / `lemma_a_as_hnn_valid`),
and de-risk the layer without the A1 residue depth. Save **A1** (the residue iso) for a focused push —
it is the genuine `prop_v`-scale content and should be budgeted as such. Do NOT start A1 at a session
tail; map its reuse of `prop_v`'s `lemma_accumulator_inv` / `tower_peel`'s coordinate survival first.
