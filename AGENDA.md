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
- [ ] **H₁ = K_M × ⟨b_j⟩ × ⟨d⟩** (direct product; `{tα wα(b) d}` a free basis).
- [ ] **H₂ = HNN(H₁, p | p⁻¹ tα p = tα wα(b) d)** — contains `C`.
- [ ] **H₃ = HNN(H₂, aᵢ (1≤i≤2n), k | aᵢ:A↔Aᵢ, k:A₊↔A₋)** — **finitely presented, ⊇ C.**
- [ ] **finiteness of relations (I)** — show the infinite families (II)(III) are consequences of the
      finite set (the payoff: `H₃` really is finitely presented).

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
