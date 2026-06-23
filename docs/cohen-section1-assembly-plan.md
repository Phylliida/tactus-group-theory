# Cohen §1 assembly — Layer-2 completeness `C ↪ H₃` over the PREDICATE base

*Written 2026-06-23 (session 18), after the normal-form arc (FA-5..FA-9b) completed: Britton's
lemma + base-embeds-in-HNN are now available over a predicate base (`pred_britton_via_tower.rs`,
`britton_lemma_unconditional`, 197/0). This is the **canonical** completeness route and it
**supersedes** `brick5-completeness-plan.md` (the Fork-B "virtual iso" C0–C5 / σ-orbit / map_a/map_b
arc — all of which were solving a problem Cohen does not have, see
`cohen-faithfulness-primary-source.md` §1–§2).*

Read `docs/cohen-faithfulness-primary-source.md` §1 first — it is the primary-source transcription
of exactly how Cohen proves faithfulness (book pp.280–281). This doc turns that into a concrete
brick plan against the tactus substrate.

---

## 0. The substrate that is now available

- **Predicate base presentations** (`pred_presentation.rs`): `PredPresentation { num_generators:
  nat, relators: spec_fn(Word)->bool }`, `equiv_in_pred_presentation`, `pred_presentation_valid`.
- **Predicate-base HNN** (`pred_hnn.rs`): `PredHNNData { base: PredPresentation, associations:
  Seq<(Word,Word)> }` — **finite** associations, single stable letter at `Gen(base.num_generators)`.
  `hnn_pred_presentation`, `hnn_pred_associations_isomorphic`, `hnn_pred_data_valid`,
  `lemma_base_embeds_in_pred_hnn` (easy forward).
- **THE KEYSTONE** (`pred_britton_via_tower.rs:2291`): `britton_lemma_unconditional(data, w)` —
  > `hnn_pred_data_valid(data) ∧ hnn_pred_associations_isomorphic(data) ∧ word_valid(w, base.num) ∧
  >  equiv_in_pred_presentation(hnn_pred_presentation(data), w, ε)  ⟹  equiv_in_pred_presentation(data.base, w, ε)`

  This **is** Cohen's "base-embeds-in-HNN" (a corollary of Britton). It is the only deep tool §1
  needs at each HNN level.
- **Predicate homomorphisms** (`pred_homomorphism.rs`): `PredHomomorphismData`, `apply_hom_pred`,
  `is_valid_pred_homomorphism`, `lemma_hom_pred_preserves_equiv` — the descent tool for the
  retraction (§3 step 2 below).

---

## 1. The construction over the predicate base

Cohen's tower, formalized with the **predicate base carrying the infinite relator families**. The
generator layout is **unchanged** from the finite tower (`layout.rs`): `c` at `c_base..c_base+n`,
`b` at `b_base..b_base+n`, `d` at `d_idx`, `p` at `p_idx`, `a_i` at `a_base..`, `k` at `k_top`.

- **`C = ⟨c₁..cₙ ; S⟩`** — `S` is an r.e. set of pure-c-word relators, carried as an **abstract
  predicate** `is_S : spec_fn(Word)->bool` (see §2 for why abstract + the realization hypothesis).
- **`h2_pred(mm,n,m,is_S)`** = H₂ as a `PredPresentation`. Generators = `h2_num_gens` (same as the
  finite `h2_pres`). Relator predicate =
  `g_m(mm).relators.contains(w)` (K_M, finite)
  `∨ comm_relators(nk,n).contains(w)` (the `b_i c_j = c_j b_i`, finite)
  `∨ is_S(w)` (C's relators — infinite)
  `∨ is_family_ii(mm,n,m,w)` (family (II) `p⁻¹ t_β p = t_β w_β(b) d` for **all** β∈I — infinite).
  This is exactly Cohen's H₂ = HNN(H₁, p | family (II)) **as a presentation** (we never need H₂ as a
  PredHNNData with infinitely many p-associations — see §3).
- **`h3_pred_upto(mm,n,m,is_S,l)`** = the single-letter PredHNN **tower** H₂ → +a₁ → … → +a_l
  (mirror of `h3_upto`): level `l` is `PredHNNData{ base: h3_pred_upto(..,l-1), associations:
  phi_assoc(nk,n,m,l) }`. Reuse the existing **S-independent** association word-lists `phi_assoc`
  (a_i), `psi_assoc` (k) verbatim from `h3.rs`.
- **`h3_pred(mm,n,m,is_S)`** = `PredHNNData{ base: h3_pred_upto(..,2n), associations: psi_assoc(mm,n) }`.
  `hnn_pred_presentation(h3_pred(..))` is H₃.

**Why finite associations suffice.** The a_i / k associations are between the *finitely generated*
subgroups A, A_i, A₊, A₋, so each is a finite stated-gen ↦ stated-gen list (`phi_assoc`/`psi_assoc`).
The ONLY infinite relator family (family (II)) lives in the **base** `h2_pred` (a predicate), not in
any association list. This is precisely the structure `pred_hnn` was built for
(`cohen-faithfulness-primary-source.md` §6c).

---

## 2. The one design decision: `S` is an abstract predicate + a realization hypothesis

`C = ⟨c;S⟩` and `M` are linked by the **machine bridge** (§3.3, not yet built): `M` is chosen so
`w_α(c) ∈ S ⟺ (α,0) ∈ H₀(M)`. For the *group-theoretic* §1 assembly we do **not** build the bridge;
we carry `S` as an abstract `is_S : spec_fn(Word)->bool` with two side conditions:

1. **Validity** `s_relators_valid(is_S, nk, n)`: `is_S(w) ⟹ w` is a word on the c-block only (all
   symbols `Gen/Inv(g)` with `c_base ≤ g < c_base+n`). Needed for `pred_presentation_valid(h2_pred)`
   and for the retraction (S relators map to themselves).
2. **Realization (one direction of the bridge)** `s_realizes(is_S, mm, n, m)`:
   `(α,0)∈H₀(M) ∧ numbers_word ⟹ is_S(w_α(c))`. Needed for the k-iso's von-Dyck-forward
   (`w_α(c)=1` must hold in the base, see §4). The §3.3 instantiation will discharge it.

This is faithful to Cohen (S is *given* by C; M *realizes* it) and composes cleanly with §3.3 and
Layer 0.5. It is **not** a reinvention — it is exactly the textbook factoring. *(Flagged for
Danielle: this is the only signature choice; everything else is forced by `layout.rs` + Cohen.)*

---

## 3. The faithfulness chain (the target)

Target (corrected, `brick5-completeness-plan.md` §1): `H₃ ⊢ w_α(c)=1 ⟹ C ⊢ w_α(c)=1`. Over the
predicate tower this factors into **two** steps, the second of which needs NO isomorphisms:

1. **Britton descent (needs the a_i + k isos).** `w_α(c)` is a base word of every tower level (pure
   c-letters, all `< p_idx < a_base < k_top`). Repeatedly apply `britton_lemma_unconditional` down
   the single-letter tower H₃ → +k⁻¹ → +a_{2n}⁻¹ → … → H₂: `w_α(c)=1 in H₃ ⟹ w_α(c)=1 in h2_pred`.
   Each level needs `hnn_pred_associations_isomorphic` of that level (§4).
2. **c-retraction descent (NO isos).** `w_α(c)=1 in h2_pred ⟹ w_α(c)=1 in C`, via the **retraction
   homomorphism** `ρ : h2_pred → c_pred` that fixes every `c_j` and kills (↦ε) every other
   generator (K_M gens, b_j, d, p). `ρ` is a valid hom: each K_M / family-(II) / single comm relator
   maps to ε (no surviving c's, or `c_j c_j⁻¹`), and each S relator is a pure-c word ↦ itself, which
   is `=1` in C by definition. Since `ρ(w_α(c)) = w_α(c)`, triviality transports. **This sidesteps
   the H₂→H₁ peel** (which would need an *infinite-association* Britton for the infinitely many
   p-associations — we never pay that cost). *(Soundness-checked with the peer model 2026-06-23.)*

`c_pred` = `PredPresentation{ num_generators: h2_num_gens, relators: is_S(w) ∨ (Gen(g)≡ε for every
non-c g) }`. For a pure-c word this presents exactly `⟨c;S⟩ = C` (the non-c killers Tietze-remove the
non-c generators). Final packaging detail; the math content is the retraction validity.

---

## 4. The hard arc: `hnn_pred_associations_isomorphic` at each tower level (Cohen §1a/§1b)

This is the substance, and the only place §1 is non-trivial. For each level the iso condition reduces
(by base-faithfulness up the tower: a word over h2-gens is trivial in `h3_pred_upto(l-1)` iff trivial
in `h2_pred`, via `britton_lemma_unconditional` applied down the a-levels — the "base-swap collapse",
now a HELP) to the iso **over `h2_pred` directly**, where it is GENUINELY true because `h2_pred`
carries the full family (II) + S.

- **a_i iso `A ≅ A_i` (Cohen §1a — relabeling, S-INDEPENDENT).** Recognize A and A_i as p-HNN-of-free
  over `h2_pred` (Prop 1.34 analog); the relabeling `t↦t_i, x↦xᵐ, d↦b_i d, b_j↦b_j, p↦p` corresponds
  the relations because `w_{αm+i}(b) = w_α(b)·b_i` (`lemma_w_b_snoc`, DONE). Reduces to the Layer-1
  residue facts (property (ii)/(v)/(vi), `prop_v`/`tower_peel`/`ii_subset`, all DONE) **b-augmented**.
- **k iso `A₊ ≅ A₋` (Cohen §1b — von Dyck + c-kill endo, USES S).** Forward A₊→A₋: stated-gen
  correspondence `U↦U, d↦d, b_j↦b_j c_j, p↦p`; well-defined by von Dyck — for each p-relation of A₊
  (`(α,0)∈H₀`) the image relation reduces via `w_α(bc)=w_α(b)w_α(c)` and `w_α(c)=1 in base`
  (the realization hypothesis §2 + `is_S` ⟹ `w_α(c)` is an `h2_pred` relator ⟹ `≡ε`). Backward
  A₋→A₊: the endomorphism killing every `c_j`. Two mutually inverse homs ⟹ iso. The A₊ recognition
  restricts the p-relations to `(α,0)∈H₀`, which is Layer-1's `t_α∈⟨U⟩ ⟺ (α,0)∈H₀` (`lemma_theorem1`,
  DONE — the single circularity-breaker).

The Prop-1.34 HNN-of-free recognition is the genuinely new group-theory work; everything it reduces
to (residue facts, free basis `lemma_basis_elt_free`, `lemma_theorem1`) is already proven in Layer 1.

---

## 5. Brick sequence (bottom-up; each verifies independently)

- **CS-1 — `cohen_h2.rs`: the predicate base + validity. ✅ DONE (3/0, commit b2a0363).**
  `is_family_ii`, `c_symbol`/`is_c_word`, `s_relators_valid`, `h2_pred_relator`, `h2_pred`;
  `lemma_h2_pred_valid` (`pred_presentation_valid(h2_pred)` under `s_relators_valid`). *(`s_realizes`
  deferred to CS-5, where the k-iso's von-Dyck-forward actually consumes it.)*
- **CS-2 — the c-retraction descent (§3 step 2). ✅ DONE (`cohen_retraction.rs` 16/0, commit 309a741).**
  `c_pred = ⟨c;S⟩`, `c_retraction` (ρ: c_j↦c_j, else↦ε); **headline `lemma_h2_pred_descends_to_c`**
  (pure-c `w` trivial in `h2_pred` ⟹ trivial in `C`). Via `lemma_c_retraction_valid` (every relator
  class ↦ identity), `lemma_rho_fixes_c_word`, `lemma_hom_pred_preserves_equiv`. The iso-free
  back-half is COMPLETE — no `p`-peel, no infinite-association Britton. Reusable atoms: `no_c_word`
  algebra, `lemma_w_c_in_block`, per-class no-c lemmas (`lemma_low_word_no_c`/`_config_word_no_c`/
  `_w_b_no_c`/`_family_ii_no_c`), `lemma_rho_kills_word`/`_fixes_c_word`/`_symbol_c`/`_symbol_noc`.
- **CS-3 — the tower scaffold. ✅ DONE (`cohen_h3.rs` 7/0, commit d4a7985).** `h3_pred_upto`
  (single-letter PredHNN tower, base `h2_pred`, level `l` adds `a_l` via `phi_assoc`), `h3_pred_data`
  (+k via `psi_assoc`), `h3_pred`; num-gens (`lemma_h3_pred_upto_num_generators`/`_num_generators`)
  + validity (`lemma_h3_pred_level_data_valid` [takes base-validity as hyp to break mutual recursion],
  `lemma_h3_pred_upto_valid`, `lemma_h3_pred_data_valid` = `hnn_pred_data_valid` for the top,
  `lemma_h3_pred_valid`). `phi_assoc`/`psi_assoc` + their validity reused verbatim from `h3.rs`.
- **CS-4 — the a_i iso (§4 §1a). ← IN SCOPING (see `cohen-cs4-architecture.md`, session 19).**
  `hnn_pred_associations_isomorphic` at each a-level. Reduces (base-faithfulness up the tower) to
  the iso `(★)` over `h2_pred`. **SCOPE CORRECTION (2026-06-23):** this is NOT `tower_peel`-scale.
  `(★)` factors via `pa_pred = P_A` into von-Dyck halves (EASY/unconditional — the predicate-base
  win, no σ-slice) + two **faithfulness** halves (`map_a`/`map_b` faithful = Prop-1.34 recognition
  of `A`/`A_i`). Faithfulness needs **peeling `p` over `H₂ = HNN(H₁, p | family (II))`**, whose
  associated subgroup `⟨t_α:α∈I⟩` is **infinitely generated** — the substrate's Britton is
  finite-association only. Two routes (`cohen-cs4-architecture.md` §3): **Route 1** = compactness-to
  -finite-slice (reuse the REAL `lemma_map_a_forward`) for the forward + a relabeling-iso
  `pa_data(G)≅pa_data(σ_l(G))` (needs σ-INJECTIVITY only, not the vacuous σ-closure) for the
  backward M2 — may avoid new substrate; **Route 2** = a unified predicate/infinite-association
  Britton (sound textbook fallback, FA-9b-scale+). **Held for the route decision** (prototype Route
  1's M2 wrinkle first — cheap + decisive). Shape-stable pieces (`pa_pred` def + validity; the
  von-Dyck halves) are safe to build under either route.
- **CS-5 — the k iso (§4 §1b).** von Dyck forward (uses `s_realizes` + `lemma_theorem1`) + c-kill
  endo backward.
- **CS-6 — assembly.** Britton descent (step 1) ∘ retraction (step 2) ⟹ `lemma_C_faithful`.
  Transport to the printable finite `h3_pres` via soundness (`lemma_III`: the predicate H₃ and the
  finite `h3_pres` are the same group — all predicate relators are consequences of finite set (I)).

CS-1/CS-2/CS-3 are FA-4-style "definitions + validity + retraction" bricks (port cleanly, high
confidence). CS-4/CS-5 are the genuine multi-session work. No verifier bypasses (standing rule).
