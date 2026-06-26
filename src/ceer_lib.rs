// Clean export root for cross-crate use by tactus-computability-theory.
//
// Declares the full ghost dependency cone of `cohen_layer05` (Layer 0.5: the C0 -> C
// Miller embedding, lemma_c0_embeds_in_c_iff) so the computability crate can instantiate
// `decls_fam` with the CEER group's declared relators and consume the embedding iff.
//
// EXCLUDES the runtime/exec showcase (`runtime`, `todd_coxeter_rt`): those use `usize::MAX`,
// which the Lean backend's tactus_auto cannot compile (IntegerTypeBound(UnsignedMax)
// deferral) -> verification errors that would block the --compile .rlib step. The ghost
// SPEC layer of `todd_coxeter` (CosetTable, symbol_to_column, trace_word, ...) IS included
// (it is what normal_form_* depends on); the exec layer was split into `todd_coxeter_rt`.
//
// Built with --crate-name verus_group_theory so computability-theory's
//   use verus_group_theory::...
// resolves unchanged. This cone is verified error-free (run build-export.sh with -V cache).

#[cfg(verus_keep_ghost)] pub mod abelianization;
#[cfg(verus_keep_ghost)] pub mod amalgamated_free_product;
#[cfg(verus_keep_ghost)] pub mod base_swap;
#[cfg(verus_keep_ghost)] pub mod benign;
#[cfg(verus_keep_ghost)] pub mod britton_infra;
#[cfg(verus_keep_ghost)] pub mod britton_via_tower;
#[cfg(verus_keep_ghost)] pub mod cohen_layer05;
#[cfg(verus_keep_ghost)] pub mod cohen_layer05_probe;
#[cfg(verus_keep_ghost)] pub mod completeness;
#[cfg(verus_keep_ghost)] pub mod concrete;
#[cfg(verus_keep_ghost)] pub mod config_reduce;
#[cfg(verus_keep_ghost)] pub mod conj_free;
#[cfg(verus_keep_ghost)] pub mod conj_free_b;
#[cfg(verus_keep_ghost)] pub mod conj_free_core;
#[cfg(verus_keep_ghost)] pub mod coset_group;
#[cfg(verus_keep_ghost)] pub mod f_free;
#[cfg(verus_keep_ghost)] pub mod finite;
#[cfg(verus_keep_ghost)] pub mod free_basis;
#[cfg(verus_keep_ghost)] pub mod free_product;
#[cfg(verus_keep_ghost)] pub mod free_word_problem;
#[cfg(verus_keep_ghost)] pub mod h1;
#[cfg(verus_keep_ghost)] pub mod h2;
#[cfg(verus_keep_ghost)] pub mod h3;
#[cfg(verus_keep_ghost)] pub mod h3_ii;
#[cfg(verus_keep_ghost)] pub mod higman_consequences;
#[cfg(verus_keep_ghost)] pub mod higman_operations;
#[cfg(verus_keep_ghost)] pub mod hnn;
#[cfg(verus_keep_ghost)] pub mod homomorphism;
#[cfg(verus_keep_ghost)] pub mod ii_subset;
#[cfg(verus_keep_ghost)] pub mod kp_pinch;
#[cfg(verus_keep_ghost)] pub mod layout;
#[cfg(verus_keep_ghost)] pub mod machine_group;
#[cfg(verus_keep_ghost)] pub mod normal_form_afp_textbook;
#[cfg(verus_keep_ghost)] pub mod normal_form_amalgamated;
#[cfg(verus_keep_ghost)] pub mod normal_form_free_product;
#[cfg(verus_keep_ghost)] pub mod presentation;
#[cfg(verus_keep_ghost)] pub mod presentation_lemmas;
#[cfg(verus_keep_ghost)] pub mod prop_v;
#[cfg(verus_keep_ghost)] pub mod quotient;
#[cfg(verus_keep_ghost)] pub mod reduction;
#[cfg(verus_keep_ghost)] pub mod shortlex;
#[cfg(verus_keep_ghost)] pub mod symbol;
#[cfg(verus_keep_ghost)] pub mod tietze;
#[cfg(verus_keep_ghost)] pub mod todd_coxeter;
#[cfg(verus_keep_ghost)] pub mod tower;
#[cfg(verus_keep_ghost)] pub mod tower_peel;
#[cfg(verus_keep_ghost)] pub mod word;
#[cfg(verus_keep_ghost)] pub mod word_numbering;
