# AGENDA — The ZFC Group

*A single roadmap from where we are to a printable finitely-presented group whose word problem
is ZFC-provable-equivalence. Maintained alongside the design docs in `docs/`.*

---

## 0. The Goal

Build, **as an explicit machine-checked construction**, a **finitely presented group `G`** and a
**computable map `f`** from first-order formulas to words on `G`'s generators such that

> **`ZFC ⊢ σ ↔ τ`   ⟺   `f(σ) = f(τ)` in `G`.**

I.e. a single finitely presented group whose *word problem is exactly ZFC-provable-equivalence* —
a foundation of mathematics folded into one group you could in principle **print on a page**.

**Why.** (1) *Minimal emergent primitives* — collapse all of ZFC's baggage (first-order logic,
membership, the infinite axiom schemas) into a finite set of generators + relators + one operation
(concatenate-and-cancel). (2) *The Proof Factory game* (`docs/proof-factory-game.md`) — relators are
crafting recipes, words are belt items, a proof is a factory reducing a formula-word to the
identity. Both need the **explicit, concrete** presentation, not a mere existence proof.

**Status of the goal.** A *non-constructive* version is **already verified**: in
`tactus-computability-theory`, `theorem_zfc_equiv_in_fp_group` (206 verified, 0 errors on Lean)
proves ZFC-provable-equiv ⟺ word problem of *some* f.p. group — but via `axiom_ceer_fp_embedding`
(`external_body`, exists-only, no presentation). **This agenda is the explicit replacement:** build
the actual Aanderaa–Cohen + Higman construction so the group is concrete and printable, removing
that axiom.

---

## 1. Architecture — the pipeline

```
  ZFC                                                         a finite presentation G,
   │  provable-equivalence is a c.e. equivalence relation       printable, with the map f
   ▼  (a CEER) on (codes of) formulas                                       ▲
 CEER  =  ⟨ gₙ | g_a g_b⁻¹ : a~b ⟩   (recursively presented, infinitely generated)
   │                                                                        │
   │  [Layer 0.5]  Higman–Neumann–Neumann: embed into a                     │
   ▼               FINITELY generated recursively presented group C         │
   C  =  ⟨ c₁,…,cₙ ; S ⟩   (S an r.e. set of relators)                     │
   │                                                                        │
   │  [Layer 2]  Higman embedding (Cohen §9.6): C ↪ H₃, a f.p. group        │
   │             via the word-numbering bridge  wα(c)∈S ⟺ (α,0)∈H₀(M)       │
   ▼                                                                        │
  H₃ = HNN(H₂, aᵢ, k)  ⊇  H₂ = HNN(H₁, p)  ⊇  H₁ = K_M × ⟨b_j⟩ × ⟨d⟩ ───────┘
   │                                                            (H₃ is G)
   │  [Layer 1]  K_M = G(M), the Aanderaa–Cohen machine group:
   ▼             realizes the c.e. set H₀(M) as a word-problem commutator
  Theorem 1:  [k, t(α,β)] = 1  in G(M)  ⟺  (α,β) ∈ H₀(M)   (the machine halts to the origin)
```

Reference: `docs/aanderaa-cohen-construction.md` (Layer 1), `docs/higman-embedding-blueprint.md`
(Layer 2), `docs/e2c-property-ii-design.md` (the faithfulness engine).

---

## 2. Current state (what is DONE)

- **Substrate — ALL ported to tactus/Lean & verified:** Britton's Lemma (`britton_via_tower`,
  194/0), HNN extensions, `benign`/embeddings, free products, `higman_operations`, the 12.4k-line
  `normal_form_afp_textbook`. Ghost math ported ~1:1.
- **ZFC → CEER (non-constructive) — DONE:** `tactus-computability-theory` 206/0, including
  `theorem_zfc_equiv_in_fp_group`. The ZFC-is-a-CEER and CEER-to-word-problem reasoning is verified
  (modulo the `axiom_ceer_fp_embedding` we are now making explicit + ~3 honest computability axioms).
- **Layer 1 construction (`machine_group.rs`, 385/0):** base `A=⟨t,x,y|xy=yx⟩`; config word
  `t(r,s)=y⁻ˢx⁻ʳ t xʳyˢ`; classic modular machine; `B(M)` tower; `G(M)`; the per-step forward
  conjugation in the real tower.
- **Theorem 1, the ⟸ direction — DONE** (`lemma_reaches_implies_k_commutes`, brick 19):
  `(α,β)∈H₀(M) ⟹ [k,t(α,β)]=1`. The whole forward simulation, machine→group.
- **Theorem 1, the ⟹ direction (the crux E) — DONE.** Full chain machine-checked: E1 (property III)
  → (vii) → (vi, unconditional) → E2.E. Assembled with ⟸ into the iff by `lemma_theorem1` (`prop_v.rs`
  57/0). **LAYER 1 COMPLETE: `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)`.** Sub-pieces:
  - **E1 (property III) DONE:** `[k,t(α,β)]=1 ⟹ t(α,β)∈⟨t,rᵢ,lⱼ⟩` (`lemma_k_commutes_implies_subgroup`).
  - **E2 (`t(α,β)∈⟨t,rᵢ,lⱼ⟩ ⟹ (α,β)∈H₀`) — under way** (`ii_subset.rs`, 31/0):
    - **(ii)⊆ DONE** — the structural decomposition + `lemma_ii_subset` (the hardest sub-brick so far).
    - **(vii) easy half DONE** — `(α,β)∈H₀ ⟹ t(α,β)∈⟨t,rᵢ,lⱼ⟩`.
    - **E2.C — the abstract property-II engine — COMPLETE** (`kp_pinch.rs` 21/0). `lemma_property_ii`:
      a stable-free base word in `⟨K,p⟩` lies in `K`, for any subgroup-closed φ-compatible `K` (abstract
      `in_k`). Full chain L1→L2→3c→junction→assembly (membership-fold + Britton core) verified.
    - **E2.D — property (vi) tower peel — VERIFIED, UNCONDITIONAL** (`tower_peel.rs` 21/0). `lemma_vi`:
      `A∩⟨T(M),rᵢ,lⱼ⟩=T(M)`, by instantiating E2.C down the B(M) tower (`lemma_vi_upto`, downward
      induction). `docs/e2d-tower-peel-plan.md`.
    - **E2.B — property (v) = `prop_v_holds` — DONE** (`prop_v.rs` 56/0, `lemma_prop_v_holds`). Both
      directions, all quads; discharges the φ-compat hole, making `lemma_vi` unconditional.
      `docs/property-v-tfree-architecture.md`.

---

## 3. The work remaining

### 3.1 — Finish Layer 1 `G(M)`: the faithfulness crux (E) ⟹ Theorem 1  ✅ **COMPLETE**
*Closed the headline `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)` — `lemma_theorem1` (`prop_v.rs` 57/0). Critical
path now moves to §3.2 (Layer 2: the Higman embedding `C ↪ H₃`).*

- [x] **E2.C — generic property-II (THE central engine) — ABSTRACT ENGINE COMPLETE (`kp_pinch` 21/0).**
        `docs/e2c-property-ii-design.md`. Engine lives in `kp_pinch.rs` (abstract over `in_k: spec_fn`),
        built on `machine_group`'s conjugation telescope (`lemma_stable_conj_factorization`). The duplicate
        engine that once sat in `ii_subset.rs` was pruned (2026-06-19) — see the design doc's "single
        source of truth". **Headline = `lemma_property_ii`**: `g` a stable-free base word ∧
        `in_kp_subgroup(data, in_k, g)` ⟹ `in_k(g)`, given K subgroup-closed (`in_k(ε)`/H_mul/H_resp) +
        φ-compatibility (H_ab/H_ba). **Remaining for E2.C = INSTANTIATION only:** discharge the five
        `in_k` hypotheses for `K=T(M)` (build-order step 5; H_ab/H_ba come from property (v) = E2.B, and
        the membership form `in_kp_subgroup` gets fed from (vii)/(vi) = E2.D).
  - [x] **L1 — pinch-elimination** DONE — `lemma_kp_eliminate_pinch` (+ `lemma_kp_phi_fwd/rev`,
        `lemma_kp_value_head_split`). Now also threads `kp_syllables_valid` (φ-helpers ensure
        `word_valid(phi, base.num_generators)`).
  - [x] **L2 — reduce to pinch-free** DONE — `lemma_kp_reduce_pinch_free` (induction on `kp_pcount`);
        also requires+preserves `kp_syllables_valid`.
  - [x] **no-KP-pinch ⟹ no-raw-pinch** (3c) + **junction** + **assembly** — ALL DONE.
    - [x] **3a/3b foundation** DONE — `kp_syllables_valid` (every syllable is a BASE word ⟹
          stable-free, since the stable letter is gen index `base.num_generators`) +
          `lemma_kp_value_word_valid` (so `W = kp_value(t, kp)` can feed `britton_lemma_full`).
    - [x] **3c — the structural core** (no-raw-pinch) DONE — `lemma_kp_no_raw_pinch`
          (`kp_syllables_valid ∧ kp_pinch_free ⟹ ¬has_pinch(data, kp_value(t, kp))`).
          Built witness-form via head-peeling induction `lemma_kp_raw_pinch_gives_kp_pinch` (a raw pinch
          of `W` yields a KP-pinch index), with modular helpers: `lemma_kp_first_stable` (head occupies
          positions `0..|head|`, all base/non-stable; position `|head|` is the first separator `p₀`),
          `lemma_kp_pinch_case_a` (pinch hits `p₀` ⟹ `kp_has_pinch_at(kp,0)`, middle `= k₀`),
          `lemma_kp_pinch_transfer_tail` (pinch past `p₀` ⟹ shifted raw pinch of `W' = kp_value(rest)`),
          `lemma_kp_pinch_lift` (`kp_has_pinch_at(rest,m) ⟹ kp_has_pinch_at(kp,m+1)`), plus
          `lemma_word_subrange_concat_right`, `lemma_base_word_index_no_stable`, `lemma_pinch_gens_eq`.
    - [x] **junction** DONE — `lemma_kp_junction` (`W` raw-pinch-free ∧ `u` stable-free ⟹ `W·u`
          raw-pinch-free) + `lemma_word_subrange_concat_left`.
    - [x] **assembly** DONE — split into the membership→KPWord conversion + the Britton core:
          - **step 1** = `lemma_kp_factors_to_kpword` — fold a kp-factor list (each factor a K-element
            base word, or `[p]`/`[p⁻¹]`) into the alternating KP-word with the *same value*; the
            membership form is `in_kp_subgroup`/`all_kp_factors`/`is_kp_factor`.
          - **steps 2–5** = `lemma_kp_property_ii_core` — L2 reduce → 3c+junction raw-pinch-free →
            `britton_lemma_full` (no pinch ⟹ no stable letter) → `tail` empty ⟹ `W = head ∈ K`, then
            `britton_lemma_unconditional` descends `W·g⁻¹ ≡ ε` to base ⟹ `W ≡_base g` ⟹ `in_k(g)`.
- [x] **(ii)⊇ DONE** (`ii_subset` 46/0) — `lemma_ii_superset`: the residue class
      `⟨t(r,s):r≡i,s≡j (mod m)⟩ ⊆ ⟨t(i,j),xᵐ,yᵐ⟩` (inverts (ii)⊆). Each residue gen `t(r,s)` is built
      as `x^{-(r-i)}·y^{-(s-j)}·t(i,j)·y^{s-j}·x^{r-i}` (`lemma_config_signed_in_G`, via the
      `conj_config_signed_by_x/y` lemmas), with the m-multiple conjugators placed by new generic power
      infra (`lemma_spow_{pos,neg,int}_mult_in_G`) and fed through a new generic closure
      (`lemma_pred_subgroup_in_generated`: a pred-subgroup ⊆ ⟨gens⟩ when each pred-elt is). Both
      directions of (ii) now hold. *(The "T∩" framing: residue ⊆ T(M) is separate, part of E2.glue.)*
- [x] **E2.D — property (vi) via the tower peel — VERIFIED, UNCONDITIONAL** (`tower_peel.rs` 21/0).
      `docs/e2d-tower-peel-plan.md`. `lemma_vi`: `A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M)` by **top-down tower
      peel** — a downward induction `lemma_vi_upto(l)` that instantiates the single-letter engine
      `lemma_property_ii` (E2.C) at each level with `in_k = in_TMstable_upto(l-1)`. The engine's
      φ-compat hypotheses (H_ab/H_ba) are discharged by **IH + property (v) + T(M)-lift**; membership
      via a near-free conversion bridge (same factor list). Ladder predicate `in_TMstable_upto`
      (level-0 = T(M), level-N = full); endpoint identities, closures, lift, extensionality all built.
      **`prop_v_holds` is now discharged (E2.B below), so `lemma_vi` requires only well-formedness +
      terminal origin — no remaining hole.**
- [x] **E2.B — property (v) = `prop_v_holds(mm)` — DONE** (`prop_v.rs` 56/0). `lemma_prop_v_holds(mm)`
      proves both directions for every quad, discharging the last hole of `lemma_vi`.
      `docs/property-v-tfree-architecture.md`. **A→B** (`lemma_prop_v_AtoB`): reduce `emb(a_gens,uw)∈T(M)`
      to a `canw_reduced` residue form (H₀∩residue `(a,b mod m)`), fold a single `U` over the 3 base
      gens, reconstruct both sides (`lemma_emb_aside_eq`), conjugate in the HNN, restrict to base A by
      base-faithfulness (`lemma_quad_base_faithful`/`lemma_single_hnn_base_faithful`), and land
      `emb(b_gens,U)` in T(M) via the forward `quad_step` (`lemma_step_preserves_h0`). **B→A**
      (`lemma_prop_v_BtoA`): mirror with the **asymmetric b-side** moduli `(m²,1)`/`(1,m²)` — the
      residue factorization comes straight from `lemma_accumulator_inv` (bypassing single-modulus
      ii_subset), `gexp=0` drops the trailing powers, a generic reduction core
      (`lemma_in_TM_canon_reduced`) + the T-free crux gives H₀∩residue, then the **reverse** conjugation
      (`lemma_stable_conj_factorization_rev`) + base-faithfulness lands `emb(a_gens,U)` at the
      `quad_step` PRE-image, in H₀ via the reverse of `step_preserves_h0` (it is an iff).
- [x] **(iv)** — the index-shift isomorphism: subsumed by the lockstep accumulator / `quad_step`
      relabel inside E2.B (no separate conjugation telescope needed).
- [x] **E2.E — T-freeness (property i) — DONE** (`config_reduce.rs` 36/0, `lemma_in_TM_config_implies_H0`):
      `in_TM(config(α,β)) ⟹ (α,β)∈H₀`. NOT the 8-12-brick free_product route `docs/t-freeness-scope.md`
      anticipated — the config-basis injectivity it needed is already proven (coordinate survival,
      `lemma_tfree_coord_restrict`), so this collapses to a ~30-line application: the reduced singleton
      `[{α,β,1}]` survives into any ≡_A H₀ factorization ⟹ `(α,β)` is one of the H₀ coords.
- [x] **E2.glue** — folded into F. `g_m_associations` are diagonal `(g,g)`, so E1's output
      `∈⟨g_subgens⟩` (.1 column) IS `∈⟨hnn_a_gens⟩` (.0 column), feeding `lemma_vii_subset` directly.
- [x] **F — THEOREM 1 (the iff) — DONE** (`prop_v.rs` 57/0, `lemma_theorem1`):
      `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)`. ⟸ = `lemma_reaches_implies_k_commutes`; ⟹ = E1 → (vii) → (vi) →
      E2.E. **LAYER 1 COMPLETE** — the whole machine→group faithfulness crux is machine-checked.

### 3.2 — Layer 2: the Higman embedding `C ↪ H₃`
*`docs/higman-embedding-blueprint.md` (Cohen §9.6). Build on the finished `G(M)=K_M`.*

- [ ] **Layer 0.5** — Higman–Neumann–Neumann: embed the (countable, recursively presented) CEER
      group into a **f.g.** recursively presented `C=⟨c₁,…,cₙ;S⟩`. (Locate Cohen's "Embedding
      Theorem", p.278.)
- [ ] **word-numbering bridge** — `wα(c)`, with `wα(c)∈S ⟺ (α,0)∈H₀(M)` (ties the relator set `S`
      to the machine, built from the reduction in §3.3).
- [x] **H₁ = K_M ∗ (C × ⟨b_j⟩) ∗ ⟨d⟩** — literal finite `h1_base` built (`h1.rs`), and
      **`{ tα wα(b) d : α∈I }` is a FREE BASIS — VERIFIED** (`free_basis.rs` 29/0,
      `lemma_basis_elt_free` + reconstruction `lemma_free_to_basis_elt`). This is Cohen
      p.279's "Mapping H₁ → K_M … Cor 1 to Prop 1.8". Structure:
  - **Abstract pullback engine** (Cohen Cor-1-to-Prop-1.8): `lemma_pullback_free`
    (φ-image of an `emb`-relation is a `φ∘emb`-relation) + `lemma_free_to_embedding` (F3:
    a freely-trivial word vanishes under any embedding) + composition/bridge helpers.
  - **F2 — config words `{t_α}` are a free family in `K_M`** (`lemma_config_emb_free`):
    descend `g_m → base_A` (`lemma_g_m_base_faithful`, peel diagonal k-layer + existing
    `lemma_b_m_equiv_faithful`) → identify the product with `canw_eval` of a CanonLetter
    sequence (`lemma_config_emb_eq_canw`) → Layer-1 `lemma_cw_reduce_trivial_empty` ⟹
    `cw_reduce = []` → the cons-step simulation `lemma_w_canon_free` (cw_cons exponent-merge
    ↔ `lemma_signed_power_add`; zero-cancellation ↔ free reduction) ⟹ `w ≡_free ε`.
  - **Assembly**: instantiate the engine at φ=`kill_hom`, whose image of `basis_elt` IS the
    config family (`lemma_comp_is_config_emb`, from `lemma_kill_on_basis_elt`), then F2.
- [ ] **H₂ = HNN(H₁, p | p⁻¹ tα p = tα wα(b) d)** — contains `C`. (Literal single-relation
      `h2.rs` built; the free basis above is the prerequisite for its HNN faithfulness.)
- [x] **H₃ = HNN(H₂, aᵢ (1≤i≤2n), k | aᵢ:A↔Aᵢ, k:A₊↔A₋)** — built as the literal finite
      presentation `h3_pres` (`h3.rs` 16/0), valid (`lemma_h3_pres_valid`).
- [x] **finiteness of relations (I) — SOUNDNESS DONE** (`higman_consequences.rs` 60/0,
      `docs/brick5-plan.md`). The infinite families (II)/(III) hold in the FINITE `h3_pres` as derived
      theorems: `lemma_II` (`p⁻¹t_α p ≡ t_α w_α(b) d`) and the **headline `lemma_III`
      (`(α,0)∈H₀(M) ⟹ w_α(c) ≡ 1`)** — Cohen's "(II),(III) are consequences of (I)", fully
      machine-checked. So `h3_pres` really is the finitely presented Higman group.
- [ ] **COMPLETENESS — `C ↪ H₃` faithful** (`docs/brick5-completeness-plan.md`, C0 started 62/0).
      The deep faithfulness direction. **Target CORRECTED** (2026-06-21, w/ Danielle): it is
      `h3_pres ⊢ w_α(c)=1 ⟹ w_α(c)=1 in C`, **NOT** `⟹ (α,0)∈H₀` (which conflates `S` with `ncl(S)`;
      the `(α,0)∈H₀` link lives in soundness + the §3.3 machine bridge, not in the group-theoretic
      proof). Two structural findings reshape the routing: (1) `S` is **infinite** ⟹ no literal
      `h3_with_S` Presentation ⟹ must use the **`kp_pinch` predicate engine**, not `britton` on a
      finite presentation; (2) the ψ (k-level) association is **non-iso in `h3_pres`** (free c's),
      refuted by exactly the `w_α(c)` family-(II) witnesses — adding `S` repairs it, so the predicate
      engine is mandatory. Bricks C0–C5; the crux C4 is a `tower_peel`-sized virtual-iso k-descent
      bottoming at `lemma_theorem1`. **C0 done**: `lemma_w_c_valid_h1`, `lemma_w_c_valid_h3_base`
      (`w_α(c)` is a base word of the k-HNN). **C1 done** (`higman_completeness.rs` 3/0): the **`in_C`
      predicate** = `w ∈ ncl(S)` over the k-HNN base `h3_upto(2n)` (explicit conjugate-product form;
      exactly the virtual-iso `britton_lemma_unconditional` output) + its 3 subgroup-closure props
      (`lemma_in_C_empty`/`_mul`/`_resp`) + the pinned `faithfulness_statement` signature. Co-design w/
      C4 resolved (peer-reviewed): **C4 = a DIRECT virtual-iso descent, NOT a `lemma_property_ii` reuse**
      (faithfulness's membership witness is the empty factor list, so the engine's `choose` is a
      liability); **one predicate** suffices (`ncl_B(S)∩c-words = ncl_{F(c)}(S)`, b commutes c).
      **C3-LITERAL REFUTED (2026-06-21, w/ Danielle):** the `φ_l` a-level iso does NOT hold over the
      literal `h3_upto(l-1)` — the a-levels are as "virtual" as the k-level (proof: base-swap collapse
      to `h2_pres` via `lemma_single_hnn_base_faithful` + an `l=1` Britton witness; root cause =
      Approach-(b) base lacks family (II), only derivable via the `a_i` in `lemma_IIa`/`lemma_II`).
      **REROUTE = finite family-(II) augmentation** `h3_II` (group-preserving via `lemma_II`), which
      makes the a-levels *literal* isos again and re-isolates virtuality to the single k-level (C4 stays
      the surgical Fork-B engine). **C3.0 DONE** (`base_swap.rs` 13/0): reflecting base-swap + the
      order-agnostic `lemma_same_group_iff` (mutual relator-derivability ⟹ same group). **C3.1 DONE**
      (`h3_ii.rs` 14/0): `h3_II` = bottom-augmented tower (`h2_II=add_relators(h2_pres,family_II)`,
      a-tower rebuilt, ψ on top) + the group-preservation iff `lemma_h3_II_group_preserving`
      (`equiv(h3_pres,·,·) ⟺ equiv(h3_II,·,·)`) via the flat splice `H+M` vs `H+family_II+M` discharged
      top-level by `lemma_same_group_iff` (the compositional route is impossible — `h2_II≠h2_pres` as
      groups). **C3.2a DONE** (`h3_ii.rs` 18/0): the a_words/b_words backbone — `lemma_phi_assoc_index`
      (explicit per-position `φ_l` pairs: `t↦t_l, x↦xᵐ, d↦b_l·d, b_j↦b_j, p↦p`), `phi_l_data` HNN datum +
      `lemma_phi_l_data_base`/`_valid` (`hnn_data_valid`, `k=n+4`, `base.num_gens=h2_num_gens+(l-1)`).
      **C3.2d INFRA DONE** (`h3_ii.rs` 20/0): the crux-independent collapse halves —
      `lemma_phi_l_emb_h2_valid` (both `φ_l` embeddings are `h2`-words, never touch an `a_i`/`k` letter ⟹
      can descend the a-tower) + `lemma_h2II_equiv_lifts_to_tower` (easy bottom→top, `lemma_base_embeds_in_hnn`
      up the tower). Studying `lemma_b_m_upto_faithful` clarified the architecture: `lemma_phi_l_iso` IS the
      single `decreases l` faithfulness induction (mirror `lemma_b_m_upto_faithful`, `base_A→h2_II`) that
      builds each φ-step iso INLINE from IH-descent + the bottom crux — so **C3.2c is the single gating
      item** (C3.2b/d are inline pieces that can't close without it; no `assume`-pin allowed).
      **C3.2c B1 DONE** (`h3_ii.rs` 25/0, 2026-06-22): **the recognition datum `recog_data`** —
      recognize the WHOLE `h2_II` as a single `p`-HNN over `h1_base` (NOT a subgroup over free `F`; the
      scattered-gen worry evaporates). `h2_II = h2_pres + family_II`, and family (II) are exactly extra
      `p`-conjugation associations, so `recog_data = HNN(h1_base, p | p_assoc ++ family_II_assoc)` and
      **`hnn_presentation(recog_data) == h2_II` LITERALLY** (`lemma_recog_presentation`, the analog of
      `lemma_a_as_hnn_presentation`) ⟹ Britton over `recog_data` applies directly to `h2_II`. Co-design
      w/ Danielle: the **"free-base fallacy"** — Britton needs ONLY the iso condition (A1), never a free
      base; non-freeness of `h1_base` bites in exactly one place (the A1 residue iso). The C3.2c crux now
      reframes cleanly as **"φ_l is a faithful endomorphism over `h2_II`"** (`emb(b_words,w) =
      subst(emb(a_words,w))`), mirroring `lemma_conj_scaling_trivial_iff` with `base_A→h2_II`.
      **C3.2c B1.5 DONE** (`h3_ii.rs` 28/0, 2026-06-22): the subst-factoring bridge — `compose_embeddings`
      + `lemma_apply_embedding_compose` (general `apply_embedding` composition) + `phi_l_subst` (φ_l as a
      full h2-gen substitution) + `lemma_phi_l_factor_through_subst` (`emb(b_words,w) =~=
      apply_embedding(phi_l_subst, emb(a_words,w))`). **ROUTING CORRECTED (w/ Danielle): von Dyck goes
      through the SUBGROUP A=HNN(F=free⟨t,x,d,b_j⟩, p | family II), NOT subst-as-h2_II-endo** ("subst
      respects all relators incl. K_M machine relators" = Route-A TRAP — would need φ_l to be an endo of
      G(M); machine relators are relations of the ambient group, not of A, so they never enter). **NEXT =
      F1** (`F=⟨t,x,d,b_j⟩` free in `h2_II`, the Route-B prerequisite; relate to `free_basis.rs`) → **A1**
      (the residue + p-conjugation iso, `prop_v`-scale focused push) → C-forward (Britton peel over
      recog_data) + C-backward (von Dyck over A's p-conjugations, the family-(II) payoff) → C3 →
      C2(p-level)/C4/C5. See `docs/brick5-c3.2c-plan.md` §3b (sharpened ladder, Route-B corrected).
      **F1 STARTED 2026-06-22** (`f_free.rs` 6/0, `docs/brick5-c3.2c-plan.md` §4 rewritten). **Route
      corrected**: NO retraction `K_M→⟨t,x⟩` exists (machine relators are config-conjugacy relations) —
      the projection-hom idea is impossible; `⟨t,x⟩` is free in K_M but not a retract. **Clean route
      (verified sound): "a free family extends by a free stable letter" = HNN with EMPTY associations**
      (pinch = adjacent `s…s⁻¹` with base-trivial middle; iso vacuous ⟹ `britton_lemma_full` applies,
      reusing Britton not an AFP spanning NF). DONE: `lemma_tx_free_in_g_m` (F1a, ⟨t,x⟩ free in K_M),
      `lemma_free_stable_is_free_product` (bridge), `lemma_apply_embedding_agree_prefix`,
      `lemma_free_group_equiv_mono`, `lemma_extend_free_no_stable` (B1 BASE CASE).
      **B1 COMPLETE 2026-06-22** (`f_free.rs` 18/0, `lemma_extend_free_by_stable` = THE reusable meat):
      a free family `gens` in `gp` extends by a free stable letter — `w` whose stable-extended embedding
      `apply_embedding(gens.push([s]), w)` is trivial in `gp ∗ ⟨s⟩` is itself trivial in
      `free_group(gens.len()+1)`. Length induction (port of `lemma_psi_F_injective`): base case
      delegates to `lemma_extend_free_no_stable`; the step uses `britton_lemma_full` (iso vacuous over
      empty associations) → `lemma_extend_pinch_descends` (pinch in `W` descends to pinch in `w`, port of
      `_pinch_descends`, threading the free-family hyp to convert the pinch middle's `gp`-triviality into
      free-triviality) → `lemma_free_stable_pinch_out` (generic pinch-out) → IH. The W↔w position
      correspondence is `lemma_extend_spanning` (port of `_spanning`), with the run-roles SWAPPED vs ψ_F:
      the stable gen maps to ONE stable letter (spanning fires on the stable peel), non-stable gens map to
      arbitrary stable-free runs (peeling strips a variable-length prefix). Support: `lemma_extend_stable_count_eq`
      (inner count of W = outer count of w, factor 1), `lemma_free_stable_{data_valid,data_isomorphic,of_free_group}`,
      `lemma_word_valid_no_inner_stable`, `lemma_trivial_in_empty_subgroup`. **PACKAGED** as `is_free_family`
      + `lemma_free_family_extends` (`is_free_family(gp,gens) ⟹ is_free_family(gp ∗ ⟨s⟩, gens.push([s]))`), the
      iterable B2 interface. **B2 SEED done** (`lemma_tx_is_free_family`: `[t,x]` free in `K_M` in `is_free_family`
      form, via F1a + `pres_tx==free_group(2)`).
      **B2 TOWER INDUCTION COMPLETE 2026-06-22** (`f_free_tower.rs` 9/0, NEW module). `free_stable_tower(gp,j)`
      = the j-fold empty-assoc HNN over `gp`; `free_stable_family(gp,gens,j)` = `gens` + the j adjoined top
      generators. **Headline `lemma_txbd_free_in_tower`**: `[t,x,b_1..b_n,d] = free_stable_family(g_m(mm),[t,x],n+1)`
      is a FREE family in `free_stable_tower(g_m(mm),n+1)`, AND that tower `== free_product(g_m(mm),free_group(n+1))`
      = `K_M ∗ F(b) ∗ ⟨d⟩`. Proof = `lemma_free_stable_tower_extends` (induction on j, each step the single-letter
      `lemma_free_family_extends`) seeded by `lemma_tx_is_free_family`. Closed forms pin the layout:
      `lemma_free_stable_tower_closed` (tower = `gp` + j gens, SAME relators), `lemma_free_stable_family_closed` +
      `lemma_txbd_family_layout` (`t,x` at `0,1`; `b_j` at `nk..nk+n-1`; `d` at `nk+n`; `nk=4+|quads|`),
      `lemma_free_stable_tower_is_free_product`.
      **B3 COMPLETE 2026-06-22** (`f_free_h1.rs` 11/0, NEW module). `F = [t,x,b_1..b_n,d]` is FREE in
      `h1_base` — `lemma_f_free_in_h1` (`is_free_family(h1_base(mm,n), f_h1_family(mm,n))`). The hom
      `kill_c : h1_base → free_stable_tower(g_m,n+1)` kills the `c`-block (↦ε), fixes K_M, shifts `b,d` down by
      `n` (`lemma_kill_c_hom_valid` — K_M relators fixed+trivial; each commutator `b_i c_j b_i⁻¹ c_j⁻¹ ↦
      b_i' b_i'⁻¹ ≡ ε` via `lemma_kill_c_on_comm_relator` + the index-keyed `_on_comm_idx`). Then
      `free_basis::lemma_pullback_free`: `comp_images(kill_c, f_h1_family) ==` B2's tower family
      (`lemma_comp_is_b2_family`), so B2's freeness (`lemma_txbd_free_in_tower`) descends `w` to free-triviality.
      `f_h1_family` = `[t,x]` + the literal `h1_base` b/d block `Gen(nk+n+i)` (`i=0..n`). **REMAINING = A1 =
      `hnn_associations_isomorphic(recog_data)`, then B4 (lift `h1_base ↪ h2_II`).** **A1 REFRAMED & DE-RISKED
      2026-06-22 (peer-confirmed, `docs/brick5-c3.2c-plan.md` §4.2 rewritten): NOT `prop_v`-scale after all.**
      `recog_data`'s two association columns are `config_emb(betas)` / `basis_emb(betas)` with `betas=[0]++alphas`
      (the `p_assoc` head `(t,td)` IS the α=0 case — VERIFIED: `config_word(0,0)=[Gen0]`, `w_b(_,0)=ε`). Both
      columns are **already-proven free families** (`lemma_config_emb_free` lifted to `h1_base` via the `kill_hom`
      retraction; `lemma_basis_elt_free` = the 29/0 headline, free in `h1_base` directly), so the HNN iso = both
      free + F3 (`lemma_free_to_embedding`) both ways, side-condition `betas.no_duplicates()`. The only new piece
      is the SHORT `kill_hom`-retraction lemma (K_M faithful in `h1_base`). `prop_v`/`tower_peel`/
      `lemma_accumulator_inv` are NOT needed (already spent inside `lemma_basis_elt_free`). A1 is a clean focused
      arc; §4.2 has the concrete sub-ladder.
      **A1 COMPLETE 2026-06-22** (`f_free_a1.rs` 8/0, NEW module — verified FIRST TRY).
      `lemma_recog_associations_isomorphic`: `hnn_associations_isomorphic(recog_data(mm,n,m,alphas))` holds
      (side-conditions `mod_machine_wf`, `2n<m`, `0∉alphas`, `alphas.no_duplicates()`, all `alphas` number
      words). Rungs: (1) `lemma_km_faithful_in_h1` — the SHORT genuinely-new `kill_hom` retraction (`K_M`-word
      trivial in `h1_base` ⟹ trivial in `g_m`, via `lemma_kill_hom_valid`+`lemma_hom_preserves_equiv`+
      `lemma_kill_fixes_low`); (2) `lemma_config_emb_free_in_h1` (config family free in `h1_base` = F2 lifted
      through the retraction); (3) the `betas=[0]++alphas` column correspondence (`lemma_a_col_eq_config_emb`/
      `_b_col_eq_basis_emb`, LITERAL seq-equal — `config_word(0,0)=[Gen0]`, `basis_elt(0)=td_word` via
      `w_c(_,0)=ε`, `family_II_rhs(αᵢ)=basis_elt(αᵢ)` via `h_w_b=w_b(b_base…)`) + the side facts
      (`lemma_betas_{index,numbers_word,no_duplicates}`, `numbers_word(n,m,0)=true`); (4) the iff assembly
      (forward `config_emb` free ⟹ `w` free ⟹ `lemma_free_to_basis_elt`; backward `lemma_basis_elt_free` ⟹
      `w` free ⟹ `lemma_free_to_embedding`). The de-risking held: the once-"hardest brick" was a clean ~190-line
      arc consuming the already-spent `lemma_basis_elt_free` machinery wholesale. **NEXT = B4** (`lemma_recog_data_valid`
      + A1 ⟹ Britton over `recog_data` applies to `h2_II`) → C-forward (Britton peel) + C-backward (von Dyck,
      the family-(II) payoff) → C3 biconditional `lemma_phi_l_iso_at_h2II` → C3.2d/C2/C4/C5.

### 3.3 — The ZFC bridge + instantiation
- [ ] **ZFC-provable-equiv is a CEER** — verified in `tactus-computability-theory` (reuse).
- [ ] **reduce the ZFC enumerator → a classic modular machine `M`** so that `H₀(M)` encodes the
      declared (ZFC-equivalent) pairs; this is the `wα(c)∈S ⟺ (α,0)∈H₀(M)` bridge's machine side.
- [ ] **instantiate** Layers 1+2 on that `M` and the CEER group ⟹ a concrete `H₃` with
      `[machine instance] = f` and `f(σ)=f(τ) ⟺ ZFC⊢σ↔τ`.

### 3.4 — Print it
- [ ] **extract the explicit presentation of `H₃`** (generators + finite relator list (I)) and the
      explicit `f: σ ↦ word`. The artifact: a printable group + map. (Then: the game can use it.)

---

## 4. Honest residual assumptions (to track / discharge)
- **`axiom_ceer_fp_embedding`** (`external_body`) — the thing this whole agenda makes explicit;
  removed once Layers 1+2 land.
- **~3 Church–Turing computability axioms** (`ceer_benign.rs:66`, `computable.rs:204`,
  `enumerator_computable.rs:54`) — legitimately-axiomatizable computability primitives; the project
  has been progressively deriving these. These are the *honest* assumptions, not bugs.
- Standing rule: **no `assume`/`admit`/`external_body`** beyond these; flag any new one.

---

## 5. Sequencing & honest effort notes
- **E2.C (the abstract property-II engine) is DONE & de-risked** (`kp_pinch` 21/0, `lemma_property_ii`).
- **E2.D (the tower peel = property (vi)) is DONE & UNCONDITIONAL** (`tower_peel` 21/0, `lemma_vi`).
- **E2.B (property (v) = `prop_v_holds`) is DONE** (`prop_v` 56/0, `lemma_prop_v_holds`). Both
  directions; the asymmetric b-side `(m²,1)` reduction was handled via `lemma_accumulator_inv` +
  a generic reduction core, NOT a single-modulus ii_subset rebuild. `lemma_vi` is now unconditional.
- **LAYER 1 COMPLETE** (`lemma_theorem1`, `prop_v` 57/0). E2.E was a ~30-line application of the
  config-basis injectivity (NOT the free_product route the old scope doc guessed); E2.glue folded into
  F via the diagonal `g_m_associations`. **Critical path now: §3.2 Layer 2 (Higman embedding `C ↪ H₃`).**
- **Fallback** (now only relevant if the *instantiation* snags, not the engine): the *direct
  pinch-decoding* route (each pinch = one machine step), noted in `docs/e2-faithfulness-scope.md`.
- Layer 1 (§3.1) is the bulk of the *novel* proof work. Layer 2 (§3.2) is intricate but follows a
  fixed blueprint. §3.3–3.4 are assembly once 1+2 exist.
- Keep Britton's proof **technique** faithful to the paper (the "deceptive dragons" rule); only the
  mechanics get the clean-Lean treatment.
