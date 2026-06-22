#[cfg(verus_keep_ghost)]
pub mod symbol;

#[cfg(verus_keep_ghost)]
pub mod word;

#[cfg(verus_keep_ghost)]
pub mod reduction;

#[cfg(verus_keep_ghost)]
pub mod presentation;

#[cfg(verus_keep_ghost)]
pub mod presentation_lemmas;

#[cfg(verus_keep_ghost)]
pub mod quotient;

#[cfg(verus_keep_ghost)]
pub mod benign;

// base_swap: the *reflecting* base-swap — adding relators that are already consequences of a
// presentation does not change the group. Foundation stone for the Brick-5 completeness reroute
// (C3.0): augment the Britton base with finite family-(II) relators (group-preserving via
// lemma_II), making the a-levels literal isos. See docs/brick5-completeness-plan.md §2.2ter.
#[cfg(verus_keep_ghost)]
pub mod base_swap;

#[cfg(verus_keep_ghost)]
pub mod hnn;

#[cfg(verus_keep_ghost)]
pub mod britton;

#[cfg(verus_keep_ghost)]
pub mod free_product;

#[cfg(verus_keep_ghost)]
pub mod homomorphism;

#[cfg(verus_keep_ghost)]
pub mod shortlex;

#[cfg(verus_keep_ghost)]
pub mod amalgamated_free_product;

#[cfg(verus_keep_ghost)]
pub mod normal_form_free_product;

#[cfg(verus_keep_ghost)]
pub mod normal_form_amalgamated;

#[cfg(verus_keep_ghost)]
pub mod abelianization;

#[cfg(verus_keep_ghost)]
pub mod concrete;

#[cfg(verus_keep_ghost)]
pub mod britton_infra;

#[cfg(verus_keep_ghost)]
pub mod finite;

#[cfg(verus_keep_ghost)]
pub mod completeness;

#[cfg(verus_keep_ghost)]
pub mod coset_group;

#[cfg(verus_keep_ghost)]
pub mod todd_coxeter;

#[cfg(verus_keep_ghost)]
pub mod runtime;

#[cfg(verus_keep_ghost)]
pub mod tower;

#[cfg(verus_keep_ghost)]
pub mod normal_form_afp_textbook;

#[cfg(verus_keep_ghost)]
pub mod britton_via_tower;

#[cfg(verus_keep_ghost)]
pub mod higman_operations;

#[cfg(verus_keep_ghost)]
pub mod tietze;

// machine_group: the Aanderaa–Cohen machine group (Layer 1 of the constructive
// finitely-presented-group-for-ZFC build). Fresh, faithful to the canonical
// construction (docs/aanderaa-cohen-construction.md) — replaces the superseded
// stub whose config word q_state·αᵃ·βᵇ was provably wrong.
#[cfg(verus_keep_ghost)]
pub mod machine_group;

// ii_subset: property (ii)⊆ structural-decomposition work — kept in its own module so its
// predicate-heavy in_residue_class goals don't pollute machine_group's triggers.
#[cfg(verus_keep_ghost)]
pub mod ii_subset;

// kp_pinch: E2.C / L1 — the ⟨K,p⟩ pinch-elimination engine (property II central core).
// Its own module to avoid trigger pollution / concurrent-edit churn with ii_subset.
#[cfg(verus_keep_ghost)]
pub mod kp_pinch;

// tower_peel: E2.D — property (vi) A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M) via the top-down tower peel,
// reusing the single-letter engine in kp_pinch.  See docs/e2d-tower-peel-plan.md.
#[cfg(verus_keep_ghost)]
pub mod tower_peel;

// config_reduce: E2.B — config reduction core (property (v) T-free uniqueness).
// Run-merge / zero-drop atoms → reduction function → ≡_A / coord lemmas → uniqueness.
// See docs/property-v-tfree-architecture.md.
#[cfg(verus_keep_ghost)]
pub mod config_reduce;

// prop_v: E2.B — property (v) assembly (prop_v_holds), consuming config_reduce + the quad wiring.
#[cfg(verus_keep_ghost)]
pub mod prop_v;

// word_numbering: Layer 2 / Brick 1 — pure word combinatorics for Cohen §9.6's α↔word numbering
// (w_α(c), w_α(b), w_α(bc) substitution maps + the numbering predicate I). Self-contained on
// symbol.rs / word.rs; abstract base-offsets leave the global layout to Brick 2 (h1.rs).
#[cfg(verus_keep_ghost)]
pub mod word_numbering;

// layout: Layer 2 / Brick 2 foundation — the global generator-index table for the Higman tower
// H₁ ⊆ H₂ ⊆ H₃ (K_M, c, b, d, p, a-block, k blocks). Pure arithmetic; reused across bricks 2–5.
#[cfg(verus_keep_ghost)]
pub mod layout;

// h1: Layer 2 / Brick 2 — the H₁-level finite generators/relators (word-numbering maps at the
// layout bases + the b_i c_j = c_j b_i commutator relators of set (I)). Approach (b): finite only.
#[cfg(verus_keep_ghost)]
pub mod h1;

// h2: Layer 2 / Brick 3 — the p-level HNN H₂ = HNN(H₁, p | p⁻¹ t p = t d). The single schematic
// p-relation of set (I); built over h1_base, stable letter at the layout's p slot.
#[cfg(verus_keep_ghost)]
pub mod h2;

// h3: Layer 2 / Brick 4 — the top of the tower H₃ = HNN(H₂; a_i, k | a_i:A↔A_i, k:A₊↔A₋). The
// finite a_i (φ_i) / k (ψ) HNN associations of set (I); iterated single-letter HNN over h2_pres.
#[cfg(verus_keep_ghost)]
pub mod h3;

// free_basis: Layer 2 / Brick 2 (deep half) — the FREE-BASIS LEMMA (blueprint p.279,
// Cohen Cor-1-to-Prop-1.8). The kill homomorphism φ:H₁→K_M + the abstract pullback engine
// (lemma_pullback_free) + F2 (config words {t_α} free in K_M, lemma_config_emb_free) ⟹
// "{t_α w_α(b) d} is a free basis of H₁" (lemma_basis_elt_free + lemma_free_to_basis_elt).
#[cfg(verus_keep_ghost)]
pub mod free_basis;

// higman_consequences: Layer 2 / Brick 5 — the Higman payoff. SOUNDNESS of the BRIDGE THEOREM
// COMPLETE (60/0): the headline `lemma_III` proves `(α,0)∈H₀(M) ⟹ h3_pres ⊢ w_α(c)=1` — Cohen's
// "(II),(III) are consequences of the finite set (I)", so h3_pres IS the f.p. Higman group. The c.e.
// set S={w_α(c)} is realized as H₃'s word problem among the c-gens. Completeness (⟹) is the remaining
// arc (see docs/brick5-plan.md: h3_pres = h3_with_S + benign/kp_pinch).
#[cfg(verus_keep_ghost)]
pub mod higman_consequences;

// higman_completeness: Layer 2 / Brick 5 COMPLETENESS — the `C ↪ H₃` faithful direction.
// Owns the `in_C` predicate (C1: `w ∈ ncl(S)` over the k-HNN base h3_upto(2n)) + its three
// subgroup-closure props, and (in progress) the Fork-B virtual-iso k-descent (C4) + assembly
// (C5). See docs/brick5-completeness-plan.md.
#[cfg(verus_keep_ghost)]
pub mod higman_completeness;
