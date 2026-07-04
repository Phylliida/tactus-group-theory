# The Miller CEER carrier is NOT finitely presentable — formalization plan

*Opened 2026-07-03 (conversation with Danielle). Status: **NF-1 + NF-A core VERIFIED & COMMITTED**
(`src/carrier_not_fp.rs`, commit d10bdf2, module-scoped 31/0 with `miller_collapse_limit`; full-crate
gate re-check pending). What landed: `lemma_fin_equiv_lifts_to_pred` (NF-1, mirror of
`pred_to_finite`), `lemma_slice_equiv_monotone` + `lemma_trivial_in_some_slice` (slice plumbing over
the banked strip/extract/monotone toolkit, made `pub`), `relators_trivial_upto` +
`lemma_relators_in_common_slice` (common-slice induction), and the **NF-A headline
`lemma_carrier_not_fp_over_std_gens`** — the refutation is now conditional ONLY on the escape
hypothesis `limit_escapes_every_slice(fam)`. REMAINING = discharge the escape hypothesis
(NF-2a/2b/3/4 below), then v2 (NF-6) + ZFC instantiation (NF-7).*

## 0. The statement

Let `fam` be a collapsed-relator family (the `ceer_decls_fam` shape: stage-`M` declared pairs of a
CEER `~`, pushed to `{a,t}`-relators `D̄_M = { u_a·u_b⁻¹ }`), and `P_∞(fam) = ⟨a,t | ⋃_M D̄_M⟩` the
Layer-0.5 carrier presentation (GAP-1 item-3a object, `miller_collapse_limit.rs`).

> **Theorem (target).** If `~` is not finitely generated as an equivalence relation (in particular,
> if `~` has one infinite class — true for ZFC-provable-equivalence via `σ ~ ¬¬σ ~ ¬¬¬¬σ ~ …`),
> then the group presented by `P_∞(fam)` is **not finitely presentable**.
>
> - **v1 (fixed generators):** no finite `R: Seq<Word>` over `F(a,t)` presents the same group:
>   `¬∃R. ∀w,w'. equiv_in_presentation(pres(2,R),w,w') ⟺ equiv_in_pred_presentation(p_infty(fam),w,w')`.
> - **v2 (abstract group):** no finite presentation on ANY generator set is isomorphic to it
>   (mutually-inverse valid homomorphisms — the `miller_collapse_inject` iso technique).

Consequences worth recording: (a) the Higman machine scaffolding of Layer 2 is *necessary* for this
carrier, machine-checked — you cannot finitely present the scaffolding-free Lindenbaum carrier;
(b) directly feeds the minimality/after-zfc-group discussion. As far as we know **no proof assistant
has ever verified a non-finite-presentability result for an explicit f.g. group** (it is a
∀-over-all-presentations statement); the paper-math itself is folklore-adjacent (experts would prove
it; we know no reference), NOT a famous open problem — the open cousin is the "finite semantic
basis" question (see conversation record / after-zfc notes).

## 1. The discovery argument (H₂ — recorded, NOT the formalization route)

By-hand computation (2026-07-03): `C₀` is abstractly free on the `~`-classes, so `L = C₀⋆F₂` is
free and `H₂(L)=0`; Mayer–Vietoris for the HNN extension gives `H₂(G) ≅ ker(H₁(A) → H₁(L))`;
on Miller's free A-basis `{b, cᵢa⁻ⁱbaⁱ}` the map sends `e_b ↦ [b]−[a]`, `e_i ↦ [c_i]+[b]−[a]`,
so for every provably-equivalent pair `i~j` the difference `e_i − e_j` is a 2-cycle
(`[c_i]=[c_j]` in `H₁(L)`). Kernel `≅ ⊕_κ ℤ^(|κ|−1)` over the Lindenbaum classes κ — infinite rank
when any class is infinite. Every f.p. group is FP₂ and has f.g. `H₂`. ∎
(Same mechanism as the classical non-f.p.-ness of `ℤ≀ℤ`.) **H₂ is the CEER's redundancy,
materialized.** We do NOT formalize homology; the route below is derivation-combinatorial.

## 2. The combinatorial route (B.H. Neumann + banked Miller faithfulness)

Suppose finite `R` presents the same congruence as `P_∞(fam)`.

1. Each `r ∈ R` is trivial in `pres(2,R)` (one `RelatorDelete`), hence trivial in `P_∞`.
2. **Extract:** each such triviality derivation lives in a finite slice `p_le(fam, m_r)`
   (`lemma_extract_slice`, HAVE — needs `strip_empty_steps` preprocessing, HAVE). Let
   `m* = max_r m_r` (finitely many `r`). Monotonicity (`dbar_family_monotone`) stabilizes.
3. **Replay:** every `pres(2,R)`-equivalence holds in `p_le(fam, m*)` — replace each `R`-relator
   step by its slice derivation. This is the mirror of `lemma_pred_equiv_lifts_to_finite` (HAVE) /
   `lemma_fin_equiv_to_pred` (HAVE); expected to be an adaptation, not new math.
4. **Witness pair:** since `~` is not finitely generated as an equivalence, there is a declared
   pair `(α,β)` with `α ~ β` (so `u_α u_β⁻¹` trivial in `P_∞`, hence in `pres(2,R)`, hence by
   step 3 in `p_le(fam, m*)`) but `(α,β) ∉ closure(stage-m* pairs)`.
5. **Descend (the banked chain):** `p_le(fam,m*)`-triviality of `u_α u_β⁻¹`
   → finite lift (`lemma_pred_equiv_lifts_to_finite`-shape, as inside `lemma_pred_to_limit`, HAVE)
   → `lemma_collapse_injective` (GAP-1 item-2, HAVE) pulls back to `G^(m*)`
   → `lemma_miller_faithfulness` (HAVE, unconditional) descends to `c0_slice(m*)`
   → **[NF-2b, new]** `c0_slice`-triviality of `g_α g_β⁻¹` ⟹ `(α,β) ∈ closure(stage-m* pairs)`.
   Contradiction with 4. ∎

`lemma_pred_to_limit`'s proof body already chains extract→lift→collapse_injective→`G^(M)`; brick
NF-2 is substantially a refactor of that body plus `lemma_miller_faithfulness` plus NF-2b.

## 3. Brick ladder

| Brick | Content | Reuse | New math? |
|---|---|---|---|
| NF-1 | Replay: finite `R` all trivial in pred-pres `Q` ⟹ `pres(2,R)`-equiv ⊆ `Q`-equiv | `lemma_fin_equiv_to_pred`, congruence algebra (`pred_presentation_lemmas`) | no — derivation splice |
| NF-2a | Slice descent `p_le(fam,m)` → `c0_slice(m)` for c-words | body of `lemma_pred_to_limit` + `lemma_collapse_injective` + `lemma_miller_faithfulness` | no — refactor |
| NF-2b | `c0_slice` word problem on `g_αg_β⁻¹` words = equivalence closure of the declared pairs | untranslate machinery in `ceer_layer05_bridge.rs` (971 lines, stage-parametric pieces); or a fresh free-quotient normal-form argument | **the one new-ish proof** (backward direction) |
| NF-3 | Equivalence closure of `k` pairs has non-singleton classes of size ≤ `k+1`; a not-finitely-generated `~` escapes every finite stage | — | elementary combinatorics, new spec + induction |
| NF-4 | Hypothesis packaging: `ceer_not_finitely_generated(fam)` spec; infinite-class ⟹ it | — | trivial given NF-3 |
| NF-5 | **v1 headline** `lemma_carrier_not_fp_on_at` | NF-1..4 assembly | no |
| NF-6 | **v2** any-generator version via mutually-inverse homs + Tietze transport (B.H. Neumann's lemma) | `tietze.rs`, `lemma_same_group_iff` (`base_swap.rs`), `miller_collapse_inject` iso technique, `pred_to_finite` bridges | no — assembly, but the largest brick |
| NF-7 | ZFC instantiation: the infinite class `σ, ¬¬σ, …` needs uniform-in-σ proof objects of `σ↔¬¬σ` in the formalized ZFC proof system (computability crate) | zfc proof-checker infra | mechanical proof-template construction |

Sequencing: NF-3 (standalone, de-risks nothing but is clean) and NF-1 first; then NF-2 (2b is the
gating brick — design its statement before building); NF-5; then NF-6/NF-7 as separate sessions.
Rough estimate: v1 ≈ 3–5 sessions, v2 + ZFC instance ≈ 2–4 more. All additive, own modules
(`carrier_not_fp*.rs`), no changes to existing signatures anticipated.

## 4. Verified reuse map (grepped 2026-07-03)

- `lemma_extract_slice` — `miller_collapse_limit.rs:631`
- `strip_empty_steps` — `miller_collapse_limit.rs:105`
- `lemma_fin_equiv_to_pred` — `miller_collapse_limit.rs:429`
- `lemma_limit_commutation` — `miller_collapse_limit.rs:765`
- `lemma_pred_equiv_lifts_to_finite` — `pred_to_finite.rs:184`
- `lemma_collapse_injective` — `miller_collapse_inject.rs:815`
- `lemma_miller_faithfulness` — `cohen_layer05.rs:666`
- `lemma_c0_embeds_in_c_iff` — `cohen_layer05.rs:801`
- `lemma_same_group_iff` — `base_swap.rs:433`
- `lemma_ceer_native_embeds_in_c_iff` — `../tactus-computability-theory/src/ceer_layer05_bridge.rs:955`

## 5. Honest risk notes

- **NF-2b is the only brick with real proof-risk.** The backward direction ("trivial in the
  pair-relator quotient ⟹ pair in the closure") is a normal-form/valuation argument in a quotient
  of a free group. Candidate cheap route: define the retraction to the free group on classes
  (a `spec_fn` valuation collapsing each generator to its class representative), show every relator
  maps to ε and the valuation is derivation-invariant; then `g_αg_β⁻¹` trivial forces equal class
  representatives. This mirrors existing hom-transport lemmas (`lemma_hom_pred_preserves_equiv`).
- The v1 statement quantifies over ALL words `w,w'` for "same group"; check whether triviality-only
  (`w'=ε`) equivalence suffices throughout (it does for the contradiction — we only ever use
  `u_αu_β⁻¹ ≡ ε`), which weakens what we must assume about `R` and STRENGTHENS the theorem: no
  finite `R` even gets the *trivial words* right. State it that way.
- The H₂ argument (§1) is a by-hand check; if any formalization step surprises us, re-derive
  against it before trusting either.

---

## 6. NF-3 PROVEN + NF-2b PINNED (2026-07-04, `docs/law-p-prime.md` §8–§9)

- **NF-3 (escape combinatorics) — PROVEN on paper.** Weight bound `w(E) ≤ |E|` for the closure of
  a finite pair-list `E` (induction: each added pair raises the class-weight by ≤ 1), giving the
  class bound `|C| ≤ |E|+1` and hence the escape corollary (an infinite `~`-class over-fills every
  finite stage ⟹ some `~`-pair escapes the stage's closure). **Verus shape chosen: contraction
  induction** (contract the last pair `(a,b)` by `ρ=(b↦a)`; `k+2` distinct pairwise-related
  elements descend to `k+1` over `k−1` pairs — IH), avoiding partition formalization. Signature
  `lemma_closure_class_bound(ps, xs)` drafted; fully self-contained (no Miller machinery) — the
  warm-up brick before NF-2b.
- **NF-2b (the gating brick) — PINNED to signature level.** Backward direction via the
  **representative collapse**: `rep(ps,i)` = least closure-representative; `collapse_word` sends
  `gᵢ ↦ g_{rep(i)}`; every `c0_slice` relator collapses to a freely-trivial word (equal reps), so
  `collapse` transports slice-equivalence to FREE-group equivalence (shape of
  `lemma_hom_pred_preserves_equiv`, target free); then `g_αg_β⁻¹` slice-trivial ⟹ `rep(α)=rep(β)`
  ⟹ `in_closure(pairs(m),α,β)`. Chaining NF-3+NF-2b through the banked descent discharges
  `limit_escapes_every_slice` and makes NF-A unconditional.
