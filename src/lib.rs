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
