# CS-4 architecture finding — the a_i iso `A ≅ A_i` over the predicate base

*Written 2026-06-23 (session 19), a deep read-only scoping pass before touching any `.rs`.
Companion-model co-design confirmed the core point. This note **corrects the scope** of CS-4 as
stated in `cohen-section1-assembly-plan.md` §4/§5 ("`tower_peel`-scale; reduces to recognition +
relabeling + residue facts"). It does NOT — there is a substrate-expressivity wall that the plan did
not surface. The finding is captured here for a route decision (co-design w/ Danielle) before the
build, per the standing rule: don't go in undesigned directions (13k lines lost that way before).*

---

## 0. What CS-4 actually asks

For each a-level `l`, the single-letter datum
`data_l = PredHNNData{ base: h3_pred_upto(l-1), associations: phi_assoc(nk,n,m,l) }`.
`hnn_pred_associations_isomorphic(data_l)` unfolds (`pred_hnn.rs:102`) to: for every word `w` valid
over `k = phi_assoc.len() = n+4` generators,

```
  emb(a_col, w) ≡_{h3_pred_upto(l-1)} ε   ⟺   emb(b_col, w) ≡_{h3_pred_upto(l-1)} ε
```

where `a_col = phi_assoc(..).0 = [t, x, d, b_1..b_n, p]` (the literal stated gens) and
`b_col = phi_assoc(..).1 = [config(l,0), xᵐ, b_l·d, b_1..b_n, p] = φ_l(a_col)`.

By **base-faithfulness up the tower** (a word over h2-gens is trivial in `h3_pred_upto(l-1)` iff in
`h2_pred`, via `britton_lemma_unconditional` down the a-levels — needs levels `<l`'s isos, a clean
downward induction), this reduces to the iso **over `h2_pred` directly**. So the heart of CS-4 is:

```
  emb(a_col, w) ≡_{h2_pred} ε   ⟺   emb(b_col, w) ≡_{h2_pred} ε        (★)
```

---

## 1. The standard two-maps factoring (textbook = Cohen §1a)

Let `pa_pred` = the abstract `P_A = HNN(F, p | family (II))`, `F = free⟨t,x,d,b_j⟩` (n+3 gens),
written as a flat `PredPresentation` (base F is free ⟹ its only relators are the family-(II)
p-conjugations, an infinite predicate over all α∈I). Cohen recognizes both `A=⟨a_col⟩` and
`A_i=⟨b_col⟩` as copies of `pa_pred` (Prop 1.34). (★) then factors through `pa_pred`:

- **von Dyck (the EASY halves, now UNCONDITIONAL over the predicate base):**
  - `w ≡_{pa_pred} ε ⟹ emb(a_col, w) ≡_{h2_pred} ε` — `a_col` is the inclusion, so the image of
    `family_II_relator(α)` is *itself*, an `h2_pred` relator ⟹ `≡ ε`.
  - `w ≡_{pa_pred} ε ⟹ emb(b_col, w) ≡_{h2_pred} ε` — the image of `family_II_relator(α)` is
    `family_II_relator(mα+l)` (`lemma_phi_l_on_family_II_relator`, already proven in `phi_l_iso.rs`,
    base-independent), which is **also** an `h2_pred` relator (mα+l is a number word when α is and
    `1≤l≤2n<m`) ⟹ `≡ ε`. **No σ-slice side condition** — this is the predicate-base win that
    killed the finite-tower vacuity.
- **faithfulness (the HARD halves):**
  - `map_a` faithful: `emb(a_col, w) ≡_{h2_pred} ε ⟹ w ≡_{pa_pred} ε`.
  - `map_b` faithful: `emb(b_col, w) ≡_{h2_pred} ε ⟹ w ≡_{pa_pred} ε`.

Then (★) is: forward `a⟹b` = `map_a` faithful ∘ `b`-von-Dyck; backward `b⟹a` = `map_b` faithful ∘
`a`-von-Dyck. **Both faithfulness halves are genuinely needed** — von Dyck only handles `w` that is
already `pa_pred`-trivial; converting "emb trivial" *back* to "`w` `pa_pred`-trivial" is exactly
faithfulness. (No endo trick: unlike the k-iso's c-killing endomorphism — a genuine `H₂` hom — `φ_l`
maps `x↦xᵐ` and breaks the `K_M` machine relators, so it is NOT an `H₂` endomorphism; there is no
analogous shortcut for the a_i iso. Companion-confirmed.)

---

## 2. The wall: faithfulness needs a p-peel over an INFINITE-association HNN

`map_a` faithful is Prop-1.34 recognition of `A`: the only relations among `t,x,d,b_j,p` in `H₂` are
the family-(II) ones. To prove it you **peel `p`** from `emb(a_col,w)` over `H₂ = HNN(H₁, p | family
(II))`. But **family (II) is infinite**, so the associated subgroup of the p-HNN is the
**infinitely-generated** `A_p = ⟨t_α : α∈I⟩`, and a Britton pinch references membership in it.

The substrate's Britton (`pred_britton_via_tower::britton_lemma_unconditional`) is over a predicate
**base** but a **finite** `associations: Seq<(Word,Word)>` (`PredHNNData`). It cannot express an
HNN with infinitely many p-associations. The finite-tower attempt peeled `p` over
`recog_data = HNN(h1_base, p | family (II) FINITE slice over alphas)` and `britton_lemma_full`, and
got stuck because the slice cannot be σ-closed (`σ_l(γ)=mγ+l` strictly grows; `lemma_map_b_forward`
needs `sigma_fwdsat`, machine-refuted vacuous by `lemma_sigma_sat_upto_unsatisfiable`).

**So CS-4's faithfulness is NOT `tower_peel`-scale.** It needs infinite/predicate-association
handling. This is the textbook situation (Prop 1.34 over the *infinitely-presented* `H₂`), so it is
not a reinvention — but it is substantial substrate, not a residue-fact application.

---

## 2b. KEY DE-RISKING (same session, after reading the directional lemmas): the cross-index core is ALREADY REAL

The pessimism in §2 over-counted the wall. The session-7 **retarget** `φ_l_src : P_A(bet) ↪
P_A(σ_l(bet))` (R1–R3) is **DONE and NON-VACUOUS**:
- `lemma_mapb_M2_rt` (`phi_l_mapb_fwd.rs:1071`-ish, the R3 cross-index injectivity): from
  `φ_l_src(w) ≡_{pa_data(sigma_betas(bet))} ε` derives `w ≡_{pa_data(bet)} ε`. Preconditions =
  `bet` no-dup + number-words + `hnn_associations_isomorphic(pa_data(sigma_betas(bet)))` — **NO
  `sigma_fwdsat`**. Source slice `bet` and target `sigma_betas(bet) = {mγ+l : γ∈bet}` are *distinct*
  finite sets, so σ-INJECTIVITY (free) suffices; σ-closure never appears.
- `lemma_map_a_forward` (`phi_l_pinch.rs:773`) is REAL (preconds satisfiable).
- `lemma_pa_data_isomorphic` (`phi_l_mapb.rs:314`) gives `hnn_associations_isomorphic(pa_data(
  betas(alphas)))` for any valid `alphas` — discharges M2_rt's iso precond (modulo a small
  betas-vs-arbitrary-slice generalization).

**The session-8 vacuity was PACKAGING-ONLY** — `lemma_map_b_forward_rt`'s redefined `sigma_sat_upto`
finite-slice (`∀γ∈betas. mγ+l ∈ alphas`) and the tower lift `lemma_phi_l_iso`/
`lemma_h3_II_upto_faithful` forced ONE σ-closed `alphas` for the WHOLE tower (infinite). The
**predicate base removes exactly that** (every `family_II_relator(mγ+l)` is an `h2_pred` relator, so
no σ-closed `alphas` is needed). The core directional lemmas underneath were always real.

**Consequence: CS-4 needs NO new infinite-association Britton.** It reduces to a **compactness
bridge** (a finite `≡_{h2_pred} ε` derivation is valid in a finite slice `h2_II(D)`) feeding the
EXISTING real `lemma_map_a_forward` + `lemma_mapb_M2_rt`. Route 1 is the path; Route 2 is unnecessary.
Route 1 works entirely with **finite `pa_data` slices** — even `pa_pred` (flat infinite
`PredPresentation`) is NOT needed (the von-Dyck halves go `pa_data(slice) → h2_pred` directly).

## 3. Two candidate routes (the decision)

### Route 1 — compactness-to-finite for the FORWARD; relabeling-iso for the BACKWARD
A *finite* derivation witnessing `≡_{h2_pred} ε` uses only finitely many relators, so it is valid in
a **finite slice presentation** `h2_II(D)`. This lets the forward reuse the **real** (non-vacuous!)
`lemma_map_a_forward` (`phi_l_pinch.rs:773`; preconditions `!contains(0)/no_duplicates/numbers_word`
are satisfiable):

1. `lemma_pred_deriv_finite_support` (NEW, generic): a pred-derivation in `h2_pred` from `u` to `ε`
   is a derivation in the finite `Presentation` holding exactly its used relators.
2. strip `S` first via a CS-2-style c-retraction `ρ_c : h2_pred → h2_pred∖S` (fixes c-free words;
   `a_col`/`b_col` words are c-free), so the slice has only K_M + comm + family-(II) relators.
3. build `alphas` = the family-(II) indices used (dedup, drop 0 [it is in `h2_pres`], `numbers_word`
   holds for each), apply `lemma_map_a_forward` over `h2_II(alphas)` ⟹ `w ≡_{pa_data(betas)} ε`.
4. lift `pa_data(slice)`-triviality to `pa_pred` (easy forward — `pa_pred` has more relators).

**Backward (`map_b` faithful = `map_a` faithful + M2).** `emb(b_col,w) = emb(a_col, φ_l_src(w))`
(`lemma_mapb_factor_source`), so `map_a` faithful (via compactness, as above) gives
`φ_l_src(w) ≡_{pa_data(betas(D))} ε`; the residue is **M2 = `φ_l_src` injective**, which is **already
done and REAL**: `lemma_mapb_M2_rt` derives `w ≡_{pa_data(bet)} ε` from
`φ_l_src(w) ≡_{pa_data(sigma_betas(bet))} ε` with NO σ-closure (see §2b). So backward = compactness +
`lemma_map_a_forward` + `lemma_mapb_M2_rt` + the a-von-Dyck. ⚠ the one remaining wrinkle: matching
`sigma_betas(bet) ⊇ betas(D)` (pick `bet` = the σ_l-preimage indices) and confining/dropping any
"irrelevant" family-(II) relator over `η ∉ σ_l(I)` a derivation might insert+delete.

- **Pros:** reuses the big finite `map_a`-forward + the REAL `lemma_mapb_M2_rt`; **no new substrate**.
- **Cons:** the compactness bridge + slice bookkeeping are new generic lemmas; CS-4d's wrinkle is the
  one open proof-design unknown.

### Route 2 — a unified predicate/infinite-association Britton substrate (RETIRED unless §2b is wrong)
Build `PredHNNData`-with-**predicate** associations + its Britton lemma (≥ FA-9b-scale, multi-week).
Sound textbook fallback (σ-closure automatic over the infinite, σ-closed `I`), but **unnecessary**
given §2b — keep only as the fallback if CS-4d's wrinkle proves fatal.

---

## 4. Recommendation: EXECUTE Route 1 (no architectural go/no-go needed — it reuses proven machinery)

After §2b, Route 1 is a **compactness reduction** to the EXISTING, REAL finite directional lemmas,
not a gamble. Compactness ("a finite derivation uses finitely many relators") is standard math.
Concrete brick sequence:

- **CS-4a — von-Dyck over `h2_pred` (unconditional). ✅ DONE (`cohen_cs4.rs` 3/0, commit 32c1de1).**
  `lemma_family_II_relator_in_h2_pred` (ANY family-(II) relator of a number-word index is `≡_{h2_pred}
  ε` — the predicate-base win atom), `lemma_a_col_relator_trivial_pred` (`emb(a_col, hnn_relator(
  pa_data,j)) ≡_{h2_pred} ε`, via the base-independent `lemma_a_words_on_hnn_relator`),
  `lemma_b_col_relator_trivial_pred` (`emb(b_col, ·) ≡ ε` via `lemma_phi_l_factor_through_subst` +
  `lemma_phi_l_on_family_II_relator` digit-scaling + `lemma_sigma_numbers_word`). Unconditional — no
  `alphas` slice. Reuses only base-independent word identities + `lemma_pred_relator_is_identity`.
- **CS-4a′ — the von-Dyck "homomorphism extends" tool (finite-source → pred-target). ✅ DONE
  (`pred_emb_respects.rs` 7/0, commit 3d41331).** `lemma_emb_respects_source_equiv_pred(src:
  Presentation, tgt: PredPresentation, images, w1, w2)`: `w1 ≡_{src} w2` + `∀j. emb(images,
  src.relators[j]) ≡_{tgt} ε` ⟹ `emb(images, w1) ≡_{tgt} emb(images, w2)`. Port of
  `lemma_emb_respects_source_equiv` keeping `src` FINITE, `tgt` predicate. Built bottom-up: 4 pred
  atoms (`lemma_pred_delete_equiv_empty`/`lemma_pred_insert_equiv_empty`,
  `lemma_emb_inverse_pair_trivial_pred`, `lemma_emb_inverse_word_trivial_pred`) + 3 induction lemmas
  (`lemma_emb_step_respects_pred` [4 cases] / `_derivation_respects_pred` / the top). This is what
  CS-4c/d call with the CS-4a relator-trivialities (`src = pa_data`, `tgt = h2_pred`).
- **CS-4b — the compactness bridge (the genuinely new generic lemma). ✅ DONE
  (`cohen_cs4b.rs` 20/0, commit 1a3ac69).**
  `lemma_cs4b_compactness`: `equiv_in_pred_presentation(h2_pred,u,ε)` + `u` c-free ⟹
  `∃ finite alphas (number-words) . equiv_in_presentation(h2_II(alphas),u,ε)`.
  **Two stages, as designed:**
  (1) **S-strip** — the homomorphism `s_strip` (kill every c gen, fix every non-c gen) maps
  `h2_pred → h2_noS_pred` (the predicate base WITHOUT `S`): K_M / family-(II) relators (c-free) ↦
  themselves, comm relator `b_i c_j b_i⁻¹ c_j⁻¹` ↦ `b_i b_i⁻¹ ≡ ε`, S relator (pure-c) ↦ `ε`. Since
  `u` is c-free, `s_strip` FIXES it (`lemma_s_strip_descends`; this is the DUAL of CS-2's
  `c_retraction`, "kill c" instead of "keep c"). NB the architecture line above said "CS-2-style
  c-retraction ρ_c fixes u" — the actual fixer is the **non-c retraction** `s_strip` (CS-2's `ρ_c`
  KILLS c-free words; the one that FIXES them keeps non-c).
  (2) **compactness** — a finite `h2_noS_pred` derivation `u →* ε` uses finitely many relators, each
  K_M / comm / `family_II_relator(β)`. The generic single-step lifter `lemma_finite_step_from_pred`
  replays a pred step as a finite `Derivation` step (free moves verbatim; relator steps re-index by
  `choose`ing the word's index in the finite relator list); the relator-arm `lemma_relator_arm`
  threads `alphas` — K_M/comm keep `alphas` (they sit in `h2_pres`, present for every slice),
  family-(II) PUSHES `β` and lifts the tail's equivalence over the larger slice by `add_relator`
  monotonicity (`lemma_h2_II_extends_push` + `lemma_quotient_preserves_equiv`); the induction core
  `lemma_compactness_core` walks the derivation.
  **Output is number-word `alphas` only** — NOT no-dup / ∌0. Those normalizations (dropping the
  always-present `family_II_relator(0)` ∈ `h2_pres` + dedup via `relators_included`) belong to CS-4c
  where `lemma_map_a_forward`'s `!contains(0)/no_duplicates` preconditions are consumed; deferred.
  Generic; CS-5 reuses the bridge.
- **CS-4c — forward (a⟹b):** CS-4b → [normalize] → `lemma_map_a_forward` → CS-4a (b-von-Dyck).
  **PREP DONE (`cohen_cs4c.rs` 14/0, commit 7ea0be8): slice normalization.** CS-4b emits a
  number-word `alphas` that may have duplicates and the index `0`; `lemma_map_a_forward` wants
  `no_duplicates()` ∧ `!contains(0)`. `normalize_alphas` drops `0` + de-dups;
  `lemma_h2_II_normalize_equiv` lifts triviality to the normalized slice with all three properties.
  Equivalence preserved because the relator SET is unchanged — a dropped duplicate
  `family_II_relator(β)` is re-derived by the survivor, and `family_II_relator(0)` is ALREADY a
  relator of `h2_pres` (it equals the single `p`-HNN relator `p⁻¹ t p (td)⁻¹`, since
  `config_word(0,0)=[t]` and `w_b(0)=ε`; `lemma_family_II_relator_0_in_h2_pres`). **NB substrate
  quirk:** `relators_included`'s `forall i. ∃ j` does NOT fold under the tactus Lean backend
  (`assert(relators_included(..))` fails even with both conjuncts proven), so the equiv is replayed
  DIRECTLY (per-element `lemma_h2_II_relator_in_norm` + single-step + derivation induction), NOT via
  `lemma_relator_inclusion_preserves_equiv`. **✅ FORWARD WIRING DONE (session 21, `cohen_cs4c.rs`
  18/0, commit 87c4a67): `lemma_cs4c_forward`.** `emb(a_col,w) ≡_{h2_pred} ε ⟹ emb(b_col,w)
  ≡_{h2_pred} ε`, chained exactly as planned: (a) `lemma_emb_a_words_no_c` — `emb(a_words,w)` is
  c-free (every `a_col` image generator lands in `{0,1} ∪ [b_base,∞)`, all outside the c-block
  `[nk,nk+n)`; new atoms `lemma_no_c_single_gen` / `lemma_a_words_img_no_c`) + word-valid
  (`lemma_a_words_img_valid` + `lemma_apply_embedding_valid`); (b) `lemma_cs4b_compactness` → finite
  slice `alphas`; (c) `lemma_h2_II_normalize_equiv` → `norm` (no-dup/∌0/number-words); (d)
  `lemma_map_a_forward(norm, w)` → `w ≡_{pa_data(betas(norm))} ε`; (e) `lemma_emb_respects_source_equiv_pred`
  with `src = hnn_presentation(pa_data(betas(norm)))`, `tgt = h2_pred`, `images = b_words`, the relator
  condition discharged per-`j` by `lemma_b_col_relator_trivial_pred` (CS-4a) ⟹ `emb(b_col,w) ≡_{h2_pred}
  emb(b_col,ε)=ε`. First-try clean after the import fix; additive, no signature changes.
- **CS-4d — backward (b⟹a) — ⚠ THE OPEN WRINKLE, sharpened (session 21).** Plan: factor
  `emb(b_col,w)=emb(a_col,φ_l_src(w))` (`lemma_mapb_factor_source`, M1) → compactness+normalize+
  `lemma_map_a_forward` on `pw := emb(φ_l_src,w)` → `lemma_mapb_M2_rt` → CS-4a (a-von-Dyck via
  `lemma_emb_respects_source_equiv_pred` with `lemma_a_col_relator_trivial_pred`, ANY number-word
  slice — the final a-slice need NOT be σ-shaped, so the a-von-Dyck tail is free). **The blocker is
  the M2_rt input form.** `lemma_mapb_M2_rt` consumes `pw ≡_{pa_data(sigma_betas(bet))} ε`
  (`sigma_betas(bet)=[mβ+l : β∈bet]`), but compactness+`map_a_forward` only ever yields
  `pw ≡_{pa_data(betas(norm))} ε` with `betas(norm)=[0]++norm`. The **0-head** (β=0 = the intrinsic
  `p`-HNN relator `p⁻¹ t p (td)⁻¹`, config(0,0)=`[t]`) can NEVER equal a σ-image `mβ+l ≥ 1` (since
  `1≤l≤2n<m`), so `betas(norm) ⊄ sigma_betas(bet)` for ANY `bet` — the `sigma_betas(bet) ⊇ betas(D)`
  matching is structurally impossible at the 0-head. Worse, `pa_data(sigma_betas(bet))` has NO β=0
  association at all (it lacks the defining `C`-relation `t↦td`), so it is a different group; the
  forward succeeded only because the b-von-Dyck maps the 0-head relator to `family_II_relator(l)` (a
  number-word relator present in `h2_pred`), a luxury M2_rt's exact-σ-form input does not grant.
  **Resolution candidates (co-design w/ Danielle, per the "no undesigned directions" rule):** (1) an
  "irrelevant-relator" recognition lemma — for a `φ_l_src`-image word `pw`, `pw ≡_{pa_data(gammas)} ε
  ⟺ pw ≡_{pa_data(gammas ∩ σ-images)} ε` (the non-σ p-conjugations, incl. the 0-head, are never
  needed; this is Cohen Prop-1.34 recognition content, substantial); or (2) a 0-head-free `map_a`
  variant whose output slice carries no forced β=0 (refactor of the 234-line `map_a` arc). Both are
  multi-hundred-line efforts with design risk — NOT a mechanical wiring like CS-4c forward.
- **CS-4e — tower lift + iso:** package (★) at `h2_pred`, lift to `h3_pred_upto(l-1)` by
  base-faithfulness (`britton_lemma_unconditional` down the a-levels, downward induction on `l`).

---

## 5. One-line status

> **UPDATE (session 23): CS-4 COMPLETE.** CS-4d backward (`cohen_cs4c.rs::lemma_cs4d_backward`, 19/0)
> + CS-4e tower lift (`cohen_cs4e.rs::lemma_cs4e_iso_upto`, 3/0) are verified. The 0-head/σ-preimage
> wrinkle was resolved by `M2_general` (recognize the σ-restriction INSIDE the source-recursion via the
> §4.2 cores, `cohen_cs4d_recog.rs` + `r_prime_b.rs`), NOT at the slice level. §4.1 (general iso) turned
> out unneeded (S = betas(norm) is betas-form). Full crate gate: 2458 verified, 20 errors (all the
> pre-existing runtime/lake-spawn baseline). `hnn_pred_associations_isomorphic(cs4_data(l))` now holds
> for every a-level `1 ≤ l ≤ 2n`. See `docs/cohen-cs4d-blueprint.md` for the build map. NEXT = CS-5 (the
> `k` von-Dyck iso, independent) → `h3_pred` full iso → Higman C↪H₃ completeness.



CS-4 = (★). von-Dyck halves EASY/unconditional (predicate-base win). Faithfulness halves reuse the
REAL `lemma_map_a_forward` + `lemma_mapb_M2_rt` (the session-8 vacuity was packaging-only, §2b) via a
**compactness bridge** to finite slices — **NO new infinite-association substrate**. Session 19:
scoped + de-risked + docs corrected + **CS-4a (3/0) + CS-4a′ (7/0) DONE**. Session 20: **CS-4b
(compactness bridge) DONE** (`cohen_cs4b.rs` 20/0). Session 21: **CS-4c FORWARD (a⟹b) DONE**
(`cohen_cs4c.rs` 18/0, `lemma_cs4c_forward` = c-freeness + CS-4b + normalize + `lemma_map_a_forward`
+ b-von-Dyck push). **NEXT = CS-4d** (backward b⟹a) — but it is **BLOCKED on a real design question**,
NOT mechanical: the M2_rt input must be `pa_data(sigma_betas(bet))`-trivial, yet `map_a_forward` only
yields `pa_data(betas(norm))`-trivial, and the forced **0-head** β=0 is never a σ-image, so the
σ-preimage matching is structurally impossible (§4 CS-4d). Needs an irrelevant-relator recognition
lemma OR a 0-head-free `map_a` variant — co-design w/ Danielle before building. Then **CS-4e** (tower
lift via `britton_lemma_unconditional` down the a-levels).
