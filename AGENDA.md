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

> **⚠ ARCHITECTURE RE-EVALUATION (2026-06-23) — read `docs/cohen-faithfulness-primary-source.md`
> THEN `docs/brick5-fork-reevaluation.md` FIRST.** The completeness route (Fork B / route-A
> word-restricted virtual iso) was found to have an UNDESIGNED CORE: the iso-consuming Britton calls
> route through `lemma_single_step_preserves_syls`, which needs the *universal* iso over an *arbitrary
> derivation* — not restrictable to a fixed word's pinch-middles — and "iso in the quotient" only
> feeds Britton circularly (would need a new "virtual Britton's Lemma", no extant sketch).
> **PRIMARY-SOURCE READING (2026-06-23, Cohen pp.279–281 read directly) CONFIRMS the pivot:** Cohen
> proves `C↪H₃` faithful with **NO Britton-peel of the `aᵢ`/`k` level** — he recognizes
> `A/Aᵢ/A₊/A₋` as p-HNN extensions of free groups (**Prop 1.34** + Layer-1 properties (ii)/(vi)/(vii),
> all DONE) over the **infinitely-presented `H₂`**, reads the isos off cheaply (relabeling; von Dyck +
> c-killing endomorphism), then base-embeds-in-HNN. The whole C0–C5 / map_a-map_b / σ-orbit / virtual
> iso arc is solving a problem Cohen doesn't have. RECOMMENDATION (pending real-Danielle confirmation):
> pivot to **Fork A** — a predicate/countable presentation foundation (ALSO the Layer-0.5 blocker; one
> foundation unblocks both). **Scoping #2 answered:** predicate-Britton is STANDARD math (not Fork-B's
> new virtual Britton); the only residual risk is whether the AFP-tower `shift`/normal-form machinery
> generalizes to a predicate base — answerable by a small non-committing prototype (see the
> primary-source note §4). The verified soundness (`lemma_III` etc.) and Layer 1 are untouched.
> **SHARPENED 2026-06-23 (primary-source note §7, code-grounded + peer-reviewed):** the embedding-only
> hope is largely false (base-embeds rests on the AFP injectivity, both 21k-line files stay on the
> path), BUT the predicate change lands on a THIN layer — the relator-by-index lookup is localized to
> ONE spec fn (`apply_step`; the whole equiv/derivation algebra above it is relator-agnostic and ports
> verbatim), the 64 indexed sites cluster in ~13 bookkeeping functions, the ~319 abstract
> `equiv_in_presentation` sites carry the math as a black box (ZERO relator-search sites ⟹ no witness
> friction), so Fork-A is a **large MECHANICAL port, not a mathematical re-derivation**. The gating
> unknown narrows to "how many compile-fix cycles does the type-swapped parallel tower take" —
> measurable by the §4 one-lemma prototype, still gated on Danielle's go/no-go.
>
> **HOLD RE-CONFIRMED 2026-06-23 (fresh session, no code touched):** no go/no-go has arrived — latest
> `MESSAGES_FROM_USER.md` is the 06-22 "follow the textbook, don't reinvent" reminder, which *reinforces*
> Fork-A but is not a decision. Working tree clean; baseline re-verified GREEN (`conj_free_core` 34/0
> under the Lean backend, toolchain intact). Surveyed the whole remaining tree: every Layer-2 and
> Layer-0.5 next-step routes through the SAME reserved foundational decision (the predicate/countable
> presentation); §3.3's machine reduction is premature + undocumented (an unconfirmed-direction dragon
> risk per Danielle's standing warning); the §4 prototype *is* the first brick of Fork-A. **Deliberately
> HELD — did not unilaterally start the gated prototype.** The decision is fully scoped (this block +
> `cohen-faithfulness-primary-source.md` §3–§7 + `brick5-fork-reevaluation.md`); there is nothing further
> to recon. Waiting on Danielle's Fork-A go/no-go.
>
> **§4 PROBE RUN 2026-06-23 (session 12) — RESULT POSITIVE, big-build still gated.** Since the decision
> was fully scoped with "nothing further to recon," the only non-redundant move (short of a 5th identical
> hold) was the *non-committing* de-risk probe the docs themselves designate as "the right first move" —
> and the 06-22 "consult the reading / follow the textbook" instruction now *points to* Fork-A (the
> reading was consulted; Cohen = Fork-A), so the probe IS textbook-following, not reinvention. Built
> `src/pred_presentation.rs` (commit `75ed225`): a faithful predicate-base port of the WHOLE of
> `presentation.rs` (`relators: spec_fn(Word)->bool`, word-carrying steps, the algebra, the reversibility
> core). **`8 verified, 0 errors` first try — identical to the original `presentation` 8/0**, kept
> SEPARATE from the tower (reversible, zero regression). Empirically CONFIRMS §7c (relator-agnostic
> algebra ports verbatim), §6a + §7d (word-carrying core ports with no new math / no `choose` witness
> friction), and that `spec_fn(Word)->bool` works in the Lean backend. **Settles the FOUNDATIONAL layer
> of scoping #2 = YES (demonstrated, not argued).** Does NOT settle the deeper tower bookkeeping
> (~13 indexed fns, `shift`, `lemma_single_step_preserves_syls`'s full context, recompile of the ~319
> abstract sites) — those are the *bulk* and stay unmeasured. **The multi-week full-build commitment
> remains Danielle's go/no-go** (re-opens the 2026-06-21 co-designed fork); deliberately did NOT proceed
> into the tower port. Full result in `cohen-faithfulness-primary-source.md` §8. NEXT (pending go) =
> next measurement up: predicate base-relator case of `lemma_single_step_preserves_syls` (needs a
> predicate `HNNData`/`shift`).

- [ ] **Layer 0.5** — Higman–Neumann–Neumann: embed the (countable, recursively presented) CEER
      group into a **f.g.** recursively presented `C=⟨c₁,…,cₙ;S⟩`. **SOURCE LOCATED 2026-06-23**:
      Cohen's book PDF is a SCANNED image (no text); use Miller `../verus-group-theory/CGTMiller.pdf`
      §4.1 Thm 4.1 (PDF pp.53–54) — exact construction `L=C⋆F₂`, free bases `A=⟨b,cᵢa⁻ⁱbaⁱ⟩`/`B=⟨a,
      b⁻ⁱabⁱ⟩`, HNN over `L` with `t`, 2-generated `G=⟨a,t|D̄⟩⊇C` (`docs/higman-embedding-blueprint.md`
      §"Build order" step 2). **⚠ BLOCKED on a foundational design decision (co-design w/ Danielle):**
      the input is **infinitely generated** (CEER's `gₙ`, n∈ℕ) but `Presentation.num_generators` is a
      finite `nat` — Layer 0.5 needs a representation for infinitely-generated groups before it can be
      stated. Crux foundational lemma = `{a⁻ⁱbaⁱ}` free in `F₂` (representation-independent — buildable
      now, a fresh from-scratch normal-form arc; the existing `f_free.rs` freeness descends via
      retractions, never computing a free normal form). **Bridge DONE** (`free_word_problem.rs` 4/0,
      `lemma_free_group_equiv_freely_equivalent`: `≡_{free_group(n)} ⟹ freely_equivalent`). **Counting
      infra DONE** (`conj_free.rs` 8/0: `count1`, `lemma_count1_emb`: `count1(φ(w))=|w|`).
      **✅ CRUX `{a⁻ⁱbaⁱ}`-FREE LEMMA COMPLETE 2026-06-23** (`conj_free_core.rs` 34/0,
      `lemma_conj_family_free`: `is_free_family(free_group(2), conj_family(k))`). Built via the
      **net-exponent invariant** (`docs/higman-embedding-blueprint.md` §"Build order" step 2, "central
      b survives"): `asum` = signed index-0 (a) exponent; `bsep(w)` = for every CONSECUTIVE inverse-pair
      of b-letters the a-exponent of the block between them is nonzero (so they can never be brought
      adjacent ⟹ never cancel). Chain: `bsep` forbids any b-cancellation (`lemma_bsep_no_b_cancel`) and
      survives removing any non-b pair (`lemma_reduce_preserves_bsep`, via prefix-`asum` + the removed
      pair having a-exponent 0) ⟹ `count1` is constant through the whole reduction to normal form
      (`lemma_count1_bsep_invariant`); base case `bsep(φ(w'))` for reduced `w'` (`lemma_bsep_emb`, head/tail
      induction — consecutive same-index source letters share a sign since `w'` is reduced); then the
      forward obligation `φ(w)≡_{F₂}ε ⟹ w≡_{free(k)}ε` reduces `w` to `w'=nf(w)`, pushes equiv through φ,
      uses the bridge to get `nf(φ(w'))=ε`, and `count1(ε)=count1(φ(w'))=|w'|` forces `w'=ε`. The crux is
      **representation-independent** (pure `F₂`), so it is done ahead of the infinitely-generated-`C` infra
      decision (still ⚠ BLOCKED, co-design w/ Danielle). **NEXT = the infinite-gen representation decision**
      (then `A`/`B` bases over the c's, `L=C⋆F₂`, the `t`-HNN `G`, 2-generation, `C↪G`).
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
- [x] **H₂ = HNN(H₁, p | p⁻¹ tα p = tα wα(b) d)** — contains `C` — **DONE** (`h2_faithful.rs` 4/0).
      `lemma_h2_associations_isomorphic` (the single p-association `(t,t·d)` is a subgroup iso) +
      `lemma_h1_faithful_in_h2_pres` (`H₁ ↪ H₂` faithful, hence `C ⊆ H₂` since `C ⊆ H₁`). Both are
      clean corollaries of A1 (`f_free_a1`) at the **empty index set**: `recog_data(…,[]) = h2_data`
      and `h2_II(…,[]) = h2_pres` (family (II) empty), so no new proof work — only the empty-index
      identification (`m` free; pick `m=2n+1`). The free basis was the prerequisite, consumed inside A1.
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
      arc consuming the already-spent `lemma_basis_elt_free` machinery wholesale.
      **B4 DONE 2026-06-22** (`f_free_a1.rs` 10/0, both first-try): A1's payoff. `lemma_h1_faithful_in_h2_II`
      (the reusable `h1_base ↪ h2_II` faithfulness = `lemma_single_hnn_base_faithful(recog_data,·)` with A1 +
      `lemma_recog_data_valid` discharging its preconditions + `lemma_recog_presentation` routing onto `h2_II`)
      + `lemma_f_free_in_h2_II` (`F=[t,x,b_j,d]` free in `h2_II`, compose B3 with the faithfulness). **NEXT =
      the C-forward / C-backward / C3 arc** — the substantial remaining work (a `tower_peel`-sized Britton-peel,
      best as a fresh arc). C-forward = Britton-peel `p` over `recog_data` (now valid via A1) to descend
      `emb(a_words,w)≡_{h2_II}ε`; C-backward = von Dyck over A's p-conjugations (family-(II) payoff, B3-based);
      C3 = biconditional `lemma_phi_l_iso_at_h2II` → C3.2d (`decreases l` induction) → C2/C4/C5.
      **C-ARC STARTED 2026-06-22** (`phi_l_iso.rs` 6/0, NEW module; design locked w/ Danielle in
      `docs/brick5-c3.2c-plan.md` §5). **Decision = Option A + a UNIFIED HNN lifting lemma** (faithfulness lifts
      base→HNN under an association-preserving embedding), instantiated for `map_a` (inclusion `F↪h1_base`) and
      `map_b` (φ_l), both chained through the abstract `P_A=HNN(F=free(n+3), p|family II over F)`; this avoids
      re-proving the pinch-descent twice. The crux = two faithful `P_A↪h2_II` embeddings (each = Britton-peel
      forward + von Dyck backward). DONE: **C-a** `lemma_phi_l_on_config_zero` (`φ_l(config(β,0))=config(mβ+l,0)`,
      the digit-scaling word identity) + **C-b full word core** (`lemma_phi_l_on_family_II_rhs` +
      `lemma_phi_l_on_family_II_lhs` ⟹ `lemma_phi_l_on_family_II_relator`: `φ_l(family_II_relator(β)) =~=
      family_II_relator(mβ+l)`, so `mβ+l∈alphas` makes the image a LITERAL h2_II relator = von-Dyck-b's
      homomorphism condition; via digit-scaling + b-block fixing `lemma_phi_l_fixes_w_b` + `φ_l(d)=b_l·d` +
      numbering snoc `lemma_w_b_snoc`) + the general reusable `lemma_apply_embedding_fixes`.
      **C-ARC SETUP COMPLETE 2026-06-22 (session 2)** — the lifting lemma's inputs are all built; only the
      Britton-peel itself (the bottleneck) + von-Dyck backwards remain. DONE this session (4 commits, all clean):
      (1) **`free_family_perm.rs` 4/0** — `lemma_free_family_permute` (free families invariant under generator
      reordering, via F3 + relabeling embeddings; Route-A "permute once" tool). (2) **`pa_data.rs` 2/0** —
      `pa_data(n,m,gammas)=HNN(free(n+3),p|family II over F)` + validity. **CORRECTION: over `gammas=betas(alphas)
      =[0]++alphas`, NOT `alphas`** (recog_data's assoc subgroups are over betas — A1 columns = config/basis_emb(betas),
      the α=0 head = p_assoc; P_A must match for the pinch to descend index-for-index). The `hnn_associations_isomorphic(pa_data)`
      iso is NOT needed (Britton runs over recog_data=TARGET, iso=A1 done). (3) **`phi_l_maps.rs` 4/0** —
      `lemma_map_a_faithful`: `a_words_F=[t,x,d,b_j]` free in h1_base (= ψ_a faithful) via permute(B3). map_a (full) =
      a_words_F.push([p]) = a_words. (4) **C-b group lift `phi_l_iso.rs` 10/0** — `lemma_phi_l_relator_equiv_empty`
      (`φ_l(relator(β))≡_{h2_II}ε` when mβ+l∈alphas) + `lemma_family_II_relator_in_h2_II`. **ASSOCIATION-PRESERVATION DONE** (`phi_l_maps.rs` 10/0, +3 commits): `lemma_a_words_relabel_wc` (the
      `w_c`-relabel b-block-shift induction = the hard atom) + `lemma_a_words_fixes_config` (a-column) +
      `lemma_a_words_on_pa_rhs` (b-column → `family_II_rhs`); full map `a_words=a_words_F.push([p])` defined.
      **VON-DYCK BACKWARDS COMPLETE 2026-06-22 (session 3)** (`phi_l_lift.rs` 5/0): generic
      `lemma_pa_von_dyck_backward` (P_A's free base ⟹ `src.relators` = the p-conjugation `hnn_relator`s ⟹
      `lemma_emb_respects_source_equiv` discharges the homomorphism condition) + both maps:
      `lemma_map_a_von_dyck_backward` (`lemma_a_words_on_hnn_relator` goal-i + `lemma_family_II_relator_head_in_h2_II`
      β=0 head) and `lemma_map_b_von_dyck_backward` (via B1.5 bridge + C-b relator core, finite-slice side
      condition `{l}∪{mα+l}⊆alphas`). `lemma_a_words_is_phi_col0` bridges `a_words` to `phi_assoc`'s `.0` column.
      **MAP_A FORWARD (FAITHFUL) COMPLETE 2026-06-22 (session 3) — THE BOTTLENECK CRACKED.** `lemma_map_a_forward`
      (`phi_l_pinch.rs` 16/0): `emb(a_words,w)≡_{h2_II}ε ⟹ w≡_{P_A}ε`, the Britton-peel injectivity. **KEY
      SIMPLIFICATION (peer-confirmed):** `a_words` maps every gen to a SINGLE gen (relabeling ρ), so it is
      length-preserving ⟹ the pinch-descent is SAME-INDEX (no template spanning/run analysis). Built bottom-up
      across `phi_l_forward.rs` (10/0, generic leaves) + `phi_l_pinch.rs` (16/0, map_a assembly):
      F1 `lemma_free_family_injective` (free family ⟹ injective on equiv) + F3 `lemma_apply_embedding_concat_all`
      + `lemma_cancel_inverse_to_equiv`; F2 `lemma_single_gen_relabel` (+ `_subrange`) + `lemma_a_words_relabel_sym`
      (ρ sends P_A stable Gen(n+3)↔recog stable Gen(p_idx), F-gens→non-stable); **F4 `lemma_intersection_property`**
      (the heart: ψ(u)∈⟨recog_gens=compose(ψ,pa_gens)⟩ ⟹ u∈⟨pa_gens⟩, via `lemma_subgroup_to_k_word` pullback +
      compose + injectivity — the deep pullback machinery already existed); the `a_words`/`a_words_F` bridge +
      column correspondence (`lemma_a_col/b_col_correspondence`: recog cols = `a_words_F`-images of pa cols over
      betas); per-side `lemma_middle_descent_a/_b`; `lemma_map_a_pinch_descends` (same-index); **generic
      `lemma_pd_pinch_out`** (non-trivial-association pinch-out via `lemma_stable_conj_factorization`/`_rev` —
      the piece the template's trivial-assoc case didn't need); and the `decreases stable_count` induction
      assembling britton_lemma_full + pinch-descent + pinch-out + emb-respects. **With the von-Dyck backward,
      map_a is a FAITHFUL embedding P_A↔h2_II (both directions).**
      **MAP_B FORWARD — (R') THE INDEX-TRACKING CORE COMPLETE 2026-06-22 (session 5, `r_prime.rs` ~52/0).**
      `lemma_r_prime` + `lemma_config_reflect_full` (= (R)): under σ-backward-saturation `sigma_backsat(bet,m,l)`
      (`∀b. (mβ+l)∈bet ⟹ β∈bet` — without it (R') is FALSE, §6 counterexample), `emb(φ_F,u)∈⟨config(bet)⟩ ⟹
      u∈⟨config(bet)⟩`.  This was THE hardest remaining piece (agenda: 'the irreducible index-tracking core ≈ the
      Layer-1 t-freeness/config-injectivity arc').  Architecture (`docs/brick5-c3.2c-plan.md` §7, companion-validated):
      kill_db retraction `G≡emb(φ',u)` → **CENTERPIECE coordinate-tracking** `lemma_phi_canon_invariant`
      (`x^{mE}·emb(φ',u) ≡ canw_eval(phi_canon_acc(u,E))·x^{m(E+xexp)}`, every config coord `≡ l (mod m)` =
      `cong_l`) → xexp=0 (gexp) → free→base_A → coord-restrict (reuse Layer-1 `lemma_tfree_coord_restrict`) +
      `lemma_sat_bridge` (coords ⊆ bet∩σ(ℤ) ⊆ σ(bet)) → free cw_reduce eval (kill_y retraction of base_A
      `lemma_cw_reduce_eval`) → reconstruction (`gsconfig` power-in-subgroup recursion).  Reused config_reduce's
      coordinate-SURVIVAL crux (no full normal-form uniqueness needed).
      **C3.2c BOTTOM CRUX COMPLETE 2026-06-22 (session 6): `lemma_phi_l_iso_at_h2II` VERIFIED.** The entire
      map_b-forward arc + the b-side reflection + C-asm landed (gate now 1731/20, +103 clean). New modules:
      **`r_prime_b.rs` 17/0** = the b-side (R)_b/(R')_b reflection over `pa_rhs` (Danielle's route: kill_db
      projection `pa_rhs↦config` → reuse a-side coord core `lemma_phi_prime_in_sigma_config` [=`lemma_r_prime`
      steps 2-7 extracted] → generic `lemma_free_family_subgroup_transfer` carrying the σ-restriction from the
      config_emb basis to the pa_rhs_emb basis; `lemma_pa_rhs_reflect_full` is the M2 b-column pinch-middle
      consumable, mirror of `lemma_config_reflect_full`). **`phi_l_mapb_fwd.rs` 8/0** = M2 + map_b fwd + C-asm:
      `lemma_mapb_pinch_descends` (the SPANNING pinch-descent, port of `lemma_extend_pinch_descends` since
      `φ_l_src=stable_emb(free(n+3),φ_F_family)`, middle reflected via (R) a/b) + `lemma_phi_l_src_on_pa_relator`
      (von-Dyck P_A→P_A) + `lemma_mapb_M2` (φ_l_src injective on P_A, Britton peel mirroring map_a fwd) +
      `lemma_map_b_forward` (= M1 factoring + map_a fwd + M2) + `lemma_phi_l_iso_at_h2II` (C-asm = map_a fwd/bwd
      + map_b fwd/bwd glued through `w≡_{P_A}ε`). Side conds = `sigma_backsat(betas)` + `sigma_fwdsat(betas)`
      (the σ-forward-saturation dual, new); finite-slice for map_b-bwd derived from fwd-sat + l≥1.
      **C3.2d (session 6): `phi_l_iso_tower.rs` 2/0 — [⚠ later found VACUOUS, see session-8 block below].** The a-tower
      lift: `lemma_h3_II_upto_faithful` (an h2-word trivial in `h3_II_upto(l)` ⟹ trivial in `h2_II`, a
      `decreases l` faithfulness induction DIRECTLY mirroring `lemma_b_m_upto_faithful`, inline-building the
      per-step iso from the bottom crux + IH-descent + `lemma_h2II_equiv_lifts_to_tower`) + `lemma_phi_l_iso`
      (the C3.2 GOAL: `hnn_associations_isomorphic(phi_l_data(..,l))` at every a-tower level, standalone).
      `sigma_sat_upto(alphas,m,l)` bundles the per-level σ-saturation side conditions. **[⚠ `sigma_sat_upto`
      later proven UNSATISFIABLE ⟹ these isos are vacuous; see the session-8 BLOCKER block below.]**
      **C4 σ-CLOSURE BLOCKER FOUND 2026-06-22 (session 7), `docs/brick5-c4-plan.md`.** The C3.2 side
      condition `sigma_sat_upto` is **UNSATISFIABLE for any finite `alphas`**: it requires `sigma_fwdsat`
      (forward-closure `σ(betas)⊆betas`), and since `betas∋0` and `σ_j(β)=mβ+j` strictly grows (appends a
      base-m digit), it forces an infinite chain — so the verified C3.2 isos are vacuous and C4 cannot use
      them. Two `sigma_fwdsat` consumers: **(a)** the b-side reflection `lemma_r_prime_b` — **FIXED
      backsat-only** (commit `28b2898`: coord-keyed selector via the strengthened `lemma_coords_in_sigma`,
      `lemma_phi_prime_canon`; r_prime 52/0, r_prime_b 25/0, no regression); **(b)** the von-Dyck
      `lemma_phi_l_src_on_pa_relator` (φ_l_src a self-ENDO of `P_A(bet)` needs `σγ∈bet`) — **THE REAL
      BLOCKER, not reflection-fixable**, intrinsic to "φ_l is an HNN association iso". **FIX = RETARGET
      `φ_l_src: P_A(bet)→P_A(σbet)`** (peer-confirmed): von-Dyck then automatic (σγ∈σbet by construction),
      pinch-descent middle natively in `⟨pa_rhs_emb(σbet)⟩` (intersection property, NO reflection — obviates
      (a)), and `alphas` = the BOUNDED σ-orbit (finite, satisfiable). Coupled multi-module cascade R1–R7
      (`docs/brick5-c4-plan.md` §4); bottleneck = R2 (rewrite the cross-index pinch-descent).
      **R1+R2+R3 DONE 2026-06-22** (`phi_l_mapb_fwd.rs` 17/0): the cross-index Britton-peel injectivity
      `φ_l_src: P_A(bet)↪P_A(σbet)` is COMPLETE, NO σ-saturation — the bottleneck is CRACKED. R1
      `lemma_phi_l_src_on_pa_relator_retarget` (von-Dyck automatic); R2 `lemma_{pa_rhs,config}_reflect_intersection`
      (σbet→bet via intersection property, replaces (R)/(R)_b) + `lemma_mapb_pinch_spanning_rt` +
      `lemma_mapb_pinch_descends_rt`; R3 `lemma_mapb_M2_rt`. Old self-endo chain kept (parallel; swap at R5/R6).
      **R4 DONE 2026-06-22** via a DIFFERENT route than the doc anticipated — the **direct `b_words` Britton
      peel** `lemma_map_b_forward_rt` (`phi_l_mapb_fwd.rs` 18/0): peel `b_words` directly over `recog_data`(=`h2_II`)
      composing `lemma_map_a_pinch_descends ∘ lemma_mapb_pinch_descends` (backsat-only), final target `betas(alphas)`,
      `sigma_fwdsat` eliminated; `sigma_sat_upto` redefined to `backsat + finite-slice (m·γ+l∈alphas)`.
      **❌ BLOCKER, REOPENED 2026-06-22 (session 8): C3.2 IS VACUOUS — the finite-slice is STILL UNSATISFIABLE.**
      The R4 redefinition merely RELOCATED the infinity: `sigma_sat_upto`'s finite-slice (`∀γ∈betas. m·γ+1∈alphas`)
      forces `1→m+1→m²+m+1→…`, an infinite chain into a finite `Seq` (MACHINE-CHECKED:
      `lemma_sigma_sat_upto_unsatisfiable`, `phi_l_iso_unsat.rs` 3/0). So `lemma_phi_l_iso` /
      `lemma_h3_II_upto_faithful` are **vacuously verified — C3.2 was NEVER actually done.** Root cause (confirmed
      w/ Danielle): a finite presentation cannot host the UNIVERSAL HNN iso — the von-Dyck-backward needs
      `family_II_relator(m·β+l)≡_base ε` for every β the base covers ⟹ `σ_l(alphas)⊆alphas` ⟹ infinite. The
      a-level associations are **virtual isos** (true in the group `h3_pres`, false in the base presentation), the
      SAME situation as the k-level — so **§2.2ter ("finite family-(II) makes a-levels LITERAL isos") is FALSE.**
      **REFRAME (Danielle-confirmed, `docs/brick5-c4-plan.md` §7): a-levels get the word-restricted virtual-iso /
      Fork-B treatment too; the R1–R4 directional machinery (map_a/map_b fwd+bwd, pinch-descents) is REUSABLE —
      only the universal-iso packaging (`lemma_phi_l_iso_at_h2II` ∀ww) + the `britton_lemma_full` tower lift are
      wrong.** **NEXT = a fresh C-reframe arc** (co-design engine sig w/ Danielle): (1) pin the word-restricted iso
      notion (quantified over a given finite set of association-words) = the Fork-B engine input for the WHOLE tower;
      (2) bounded σ-orbit `sigma_orbit(D,m,depth)` + its word-relative finite-slice (finite, satisfiable — build
      first to de-risk); (3) weaken+re-verify the directional lemmas to the word-relative slice; (4) word-restricted
      tower lift replacing `britton_lemma_full`. Then C3.2 (word-restricted), C2, C4 (k-level), C5 share one engine.
      **REFRAME STEP 2 DONE 2026-06-23 (session 9): the BOUNDED σ-ORBIT brick `sigma_orbit.rs` 13/0.** The
      de-risking combinatorial brick (`docs/brick5-c4-plan.md` §7.4 step 2): `sigma_orbit(d,m,n,depth)` =
      depth-stratified accumulation (`orbit(0)=d`, `orbit(k+1)=orbit(k) ++ σ-expand(orbit(k))`) as an explicit
      finite `Seq<nat>`. Proven: number-word preservation (`lemma_sigma_orbit_numbers_word`), depth-stratified
      σ-closure `lemma_sigma_orbit_closed_step` (`orbit(d)→orbit(d+1)` — a DAG, top layer never needs its own
      shifts ⟹ dodges the unsat forward-closure), monotonicity, and **the SATISFIABILITY WITNESS**
      (`lemma_sigma_slice_satisfiable` + `lemma_sigma_orbit_covers`: one finite `alphas` covers all `2n` tower
      levels). Pins the reframed `sigma_slice_ok(seed,alphas,m,n)` (seed DECOUPLED from alphas ⟹ no
      self-σ-image forcing) — the machine-checked refutation of the session-7/8 "even the bounded slice is
      vacuous". **ROUTE DECISION (peer-confirmed, `docs/brick5-c4-plan.md` §8): take ROUTE A = derivation-local
      / SURGICAL, NOT a full re-prove of `britton_via_tower`'s tower-textbook chain.** Peel a FIXED `w` by
      Britton, invoke the iso ONLY at the pinch-middles that arise. Index set is a-priori finite: Lyapunov bound
      (pinch count ≤ ½·stable-count of `w`, no step introduces stable letters ⟹ finitely many middles) + bounded
      index growth (each level-`l` pinch applies `φ_l:β↦σ_l(β)`, tower height `2n` ⟹ all indices ∈
      `sigma_orbit(L₀,m,n,2n)`, FINITE = exactly the brick). **NEXT (the co-design arc, do NOT guess the
      signature solo — wrong-sig burned 2 sessions): (1) shape of the word-restricted faithfulness lemma —
      precomputed word-set `iso_on(data,W)` vs. per-pinch obligation inside a fresh `decreases stable_count`
      peel (the latter matches route A + existing pinch-descents); (2) attach as a word-restricted analog of
      `lemma_single_hnn_base_faithful` (NOT re-prove `tower_textbook_chain`), replacing the vacuous
      `lemma_phi_l_iso_at_h2II`+`britton_lemma_full` calls in `phi_l_iso_tower.rs`; (3) side condition =
      `sigma_backsat` + `alphas ⊇ sigma_orbit(L₀,m,n,2n)` via `sigma_slice_ok`. C4 then picks the bounded
      orbit of `wα(c)`'s digits.** See `docs/brick5-c4-plan.md` §7–§8.

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
