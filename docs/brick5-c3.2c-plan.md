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
- **B1 `recog_data` — DONE** (`h3_ii.rs` 25/0, 2026-06-22). **Design resolved (w/ Danielle): recognize
  the WHOLE `h2_II` as a single `p`-HNN over `h1_base`, NOT a subgroup over free `F`.** The scattered-gen
  worry (§2.1) evaporates: we never isolate a free `F`. Key realization — `h2_pres = HNN(h1_base, p |
  p⁻¹ t p = td)` carries only the α=0 p-relation, and `h2_II = add_relators(h2_pres, family_II)` adds the
  family-(II) relators `(p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹`, which are EXACTLY more `p`-conjugation relations.
  Folding them into the HNN association list gives `recog_data = HNNData { base: h1_base, associations:
  p_assoc ++ family_II_assoc }` (where `family_II_assoc[i] = (config(β,0), t_β w_β(b) d)`, neither side
  touching `p`, so valid over `h1_num_gens = nk+2n+1`). Delivered:
  - `family_II_assoc`, `recog_data` (spec); `lemma_family_II_rhs_valid_h1` (rhs valid over H₁ gens).
  - `lemma_recog_data_valid` = analog of `lemma_a_as_hnn_valid`.
  - `lemma_recog_relator_is_family` (`hnn_relator(recog,1+j) = family_II_relator(alphas[j])`) +
    `lemma_recog_hnn_relators_split` (`hnn_relators(recog) =~= hnn_relators(h2_data) ++ family_II`).
  - **`lemma_recog_presentation`** = the headline: `hnn_presentation(recog_data) == h2_II` LITERALLY
    (analog of `lemma_a_as_hnn_presentation`). So Britton over `recog_data` applies directly to `h2_II`.
  **The "free-base fallacy" (Danielle, confirmed):** Britton's lemma needs ONLY the iso condition
  `hnn_associations_isomorphic(recog_data)` (= A1, the residue iso), never a free base. Non-freeness of
  `h1_base` bites in exactly ONE place — the A1 iso proof — and nowhere else.
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

## 3b. Sharpened ladder (post-B1, 2026-06-22)

B1's whole-group recognition (`h2_II == hnn_presentation(recog_data)`) reshapes the ladder. The old
A1/A2/B1/B2 split was written for the subgroup-over-free route; with the global `p`-HNN recognition the
crux becomes cleanly **"the φ_l endomorphism is faithful over `h2_II`"**, mirroring
`lemma_conj_scaling_trivial_iff` but with `base_A → h2_II` and `ψ (scale x,y) → φ_l (t↦t_l, x↦xᵐ, d↦b_l·d)`.

Key reframing: in the crux `emb(a_words,w) ≡_{h2_II} ε ⟺ emb(b_words,w) ≡_{h2_II} ε`, the a-side
`a_words=[t,x,d,b_j,p]` is the *identity-ish* embedding (each stated gen ↦ itself), so `emb(a_words,w)` is
just `w` relabeled into the real generators — a word in the subgroup `⟨t,x,d,b_j,p⟩`. The b-side is its
φ_l-image: **`emb(b_words,w) = subst(emb(a_words,w))`** where `subst` is the φ_l endomorphism on ALL
`h2_II` gens (t↦config(l,0), x↦xᵐ, d↦b_l·d, b_j↦b_j, p↦p; non-stated gens y/machine/c_j ↦ themselves).
So the crux = "subst faithful on `emb(a_words,w)`".

**Corrected next-bricks (gating order):**
1. **B1.5 — the subst-factoring bridge.** `emb(b_words,w) =~= apply_embedding(subst_images, emb(a_words,w))`
   (`subst_images` = a length-`h2_num_gens` image list fixing non-stated gens). Needs an `apply_embedding`
   composition lemma (`apply_embedding(f, apply_embedding(g,w)) =~= apply_embedding(f∘g, w)` with
   `(f∘g)[i] = apply_embedding(f, g[i])`) + concat/inverse homomorphism helpers. **Check first** for
   existing `lemma_apply_embedding_concat` / `_inverse` in `benign.rs`/`machine_group.rs`; build the
   composition lemma if absent. Self-contained pure combinatorics; both directions consume it.
2. **C1 — von Dyck (backward).** Via `lemma_emb_respects_source_equiv` with `src = h2_II`,
   `images = subst_images`: check subst respects each `h2_II` relator. EASY: `comm_relators` (subst fixes
   b,c). HARD: the K_M machine relators (config(l,0)/xᵐ must respect them — port the idea of
   `lemma_psi_respects_relator`) + the p-relation + `family_II` (the latter two = the **C3.1 payoff**,
   present as literal relators of `h2_II`). This is where family (II) is consumed.
3. **A1 — the residue iso = `hnn_associations_isomorphic(recog_data)`.** The genuine `prop_v`-scale content
   (`t_β ↦ t_β w_β(b) d` is a subgroup iso over `h1_base`). The focused multi-session push; map its reuse
   of `prop_v`'s `lemma_accumulator_inv` + `tower_peel`'s coordinate survival first. **Do NOT start at a
   session tail.**
4. **C2 — forward (faithful).** Britton-peel `p` over `recog_data` (B1 gives `h2_II = hnn_presentation(recog_data)`,
   so `britton_lemma_full` applies) using A1 as the iso precondition; descend to `h1_base`; then the
   scaling-injectivity on `{t,x,d,b_j}`.
5. **C3 — biconditional** = C1 + C2; package as `lemma_phi_l_iso_at_h2II`.

The original §3 A2 (`lemma_phi_scaling_injective_F`) and B2 (`lemma_finite_beta_suffices`) are subsumed:
A2's injectivity is now the base-descent tail of C2 (no free `F` to inject into); B2 becomes the
`requires alphas ⊇ betas(w)` side-condition baked into `h2_II`'s finite slice.

## 4. First verified down-payment for the next session

**B1 is DONE** (`h3_ii.rs` 25/0). Next, take **B1.5 (the subst-factoring bridge)** — self-contained,
unblocks BOTH crux directions, and surfaces whether the `apply_embedding` composition infra already
exists. Then **C1 (von Dyck)**, which is tractable for the easy relators and isolates exactly the
machine-relator-respect obligation. Save **A1** (the residue iso) for a focused push — it is the genuine
`prop_v`-scale content and should be budgeted as such. Do NOT start A1 at a session tail; map its reuse
of `prop_v`'s `lemma_accumulator_inv` / `tower_peel`'s coordinate survival first.
