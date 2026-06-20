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
- **Faithfulness (Theorem 1 ⟹, "the crux E") — IN PROGRESS:**
  - **E1 (property III) DONE:** `[k,t(α,β)]=1 ⟹ t(α,β)∈⟨t,rᵢ,lⱼ⟩` (`lemma_k_commutes_implies_subgroup`).
  - **E2 (`t(α,β)∈⟨t,rᵢ,lⱼ⟩ ⟹ (α,β)∈H₀`) — under way** (`ii_subset.rs`, 31/0):
    - **(ii)⊆ DONE** — the structural decomposition + `lemma_ii_subset` (the hardest sub-brick so far).
    - **(vii) easy half DONE** — `(α,β)∈H₀ ⟹ t(α,β)∈⟨t,rᵢ,lⱼ⟩`.
    - **E2.C design + representation DONE** — the `⟨K,p⟩`-word (KPWord) encoding.

---

## 3. The work remaining

### 3.1 — Finish Layer 1 `G(M)`: the faithfulness crux (E) ⟹ Theorem 1
*Critical path. Closes the headline `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)`.*

- [ ] **E2.C — generic property-II (THE central engine).** `docs/e2c-property-ii-design.md`.
        Engine lives in `kp_pinch.rs` (abstract over `in_k: spec_fn`), built on `machine_group`'s
        conjugation telescope (`lemma_stable_conj_factorization`). The duplicate engine that once
        sat in `ii_subset.rs` was pruned (2026-06-19) — see the design doc's "single source of truth".
  - [x] **L1 — pinch-elimination** DONE — `lemma_kp_eliminate_pinch` (+ `lemma_kp_phi_fwd/rev`,
        `lemma_kp_value_head_split`). `kp_pinch` 6/0.
  - [x] **L2 — reduce to pinch-free** DONE — `lemma_kp_reduce_pinch_free` (induction on `kp_pcount`).
  - [ ] **no-KP-pinch ⟹ no-raw-pinch** (DONE, see 3c) + **junction** + **assembly** — **← junction next.**
    - [x] **3a/3b foundation** DONE — `kp_syllables_valid` (every syllable is a BASE word ⟹
          stable-free, since the stable letter is gen index `base.num_generators`) +
          `lemma_kp_value_word_valid` (so `W = kp_value(t, kp)` can feed `britton_lemma_full`).
    - [x] **3c — the structural core** (no-raw-pinch) DONE — `lemma_kp_no_raw_pinch`
          (`kp_syllables_valid ∧ kp_pinch_free ⟹ ¬has_pinch(data, kp_value(t, kp))`), `kp_pinch` 16/0.
          Built witness-form via head-peeling induction `lemma_kp_raw_pinch_gives_kp_pinch` (a raw pinch
          of `W` yields a KP-pinch index), with modular helpers: `lemma_kp_first_stable` (head occupies
          positions `0..|head|`, all base/non-stable; position `|head|` is the first separator `p₀`),
          `lemma_kp_pinch_case_a` (pinch hits `p₀` ⟹ `kp_has_pinch_at(kp,0)`, middle `= k₀`),
          `lemma_kp_pinch_transfer_tail` (pinch past `p₀` ⟹ shifted raw pinch of `W' = kp_value(rest)`),
          `lemma_kp_pinch_lift` (`kp_has_pinch_at(rest,m) ⟹ kp_has_pinch_at(kp,m+1)`), plus
          `lemma_word_subrange_concat_right`, `lemma_base_word_index_no_stable`, `lemma_pinch_gens_eq`
          (bridges the inline `Seq::new` gen-lists of `has_pinch_at` to `hnn_a_gens`/`hnn_b_gens`).
    - [ ] **junction** (`W` raw-pinch-free ∧ `u` stable-free ⟹ `W·u` raw-pinch-free) — appending a
          `p`-free word adds no stable letters, so no adjacent-stable middle changes. **← current next
          brick.** (Reuse `lemma_base_word_no_stable` + the position helpers from 3c.)
    - [ ] **assembly** — (1) `g ∈ ⟨K,p⟩ ⟹ ∃ KPWord kp₀, kp_value ≡ g`; (2) L2 ⟹ pinch-free `kp`;
          (3) 3c+junction ⟹ `W·g⁻¹` raw-pinch-free; (4) `britton_lemma_full`: `≡ε ∧ raw-pinch-free
          ⟹ stable-free`; (5) stable-free ⟹ `tail` empty ⟹ `g ≡ head ∈ K`. E1
          (`lemma_k_commutes_implies_subgroup`) is the template for (3)–(4).
- [ ] **(ii)⊇** — residue configs ⊆ `T∩⟨t(i,j),xᵐ,yᵐ⟩` (inverts the move lemmas; completes (ii)).
- [ ] **(iv)** — the index-shift isomorphism of associated subgroups (HNN-validity backbone).
- [ ] **E2.B — property (v)** — the φ-compatibility: `rᵢ` maps `T(M)∩A₊ ↔ T(M)∩A₋`, because
      H₀-membership is **step-invariant** (machine determinism). This supplies L1's compatibility
      hypothesis for `K=T(M)`.
- [ ] **E2.D — property (vi) via the tower** — apply property-II down each B(M) level, peeling
      `rᵢ`/`lⱼ`, reducing `A∩⟨T(M),rᵢ,lⱼ⟩` to `T(M)`.
- [ ] **E2.E — T-freeness (property i) + free-factor membership** (the "last mile"): `T=⟨t⟩^A` is
      free on `{t(r,s)}`; `t(α,β)∈T(M)` ⟹ `(α,β)∈H₀`. Uses `free_product.rs`.
- [ ] **E2.glue** — `t(α,β)∈A ∧ ∈⟨t,rᵢ,lⱼ⟩` →(vii)→ `∈A∩⟨T(M),rᵢ,lⱼ⟩` →(vi)→ `∈T(M)` →(E2.E)→ `∈H₀`.
- [ ] **F — Theorem 1 (the iff):** assemble ⟸ (done) + ⟹ (E1∘E2) into
      `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)`. **Layer 1 complete.**

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
- **Critical path right now: §3.1 E2.C (L1).** It is the highest-uncertainty engine; everything in
  the abstract faithfulness route depends on it. De-risk it before investing further in E2.B/(iv)/E2.E.
- **Fallback** if L1's surgery won't formalize: the *direct pinch-decoding* route (each pinch = one
  machine step), noted in `docs/e2-faithfulness-scope.md`.
- Layer 1 (§3.1) is the bulk of the *novel* proof work. Layer 2 (§3.2) is intricate but follows a
  fixed blueprint. §3.3–3.4 are assembly once 1+2 exist.
- Keep Britton's proof **technique** faithful to the paper (the "deceptive dragons" rule); only the
  mechanics get the clean-Lean treatment.
