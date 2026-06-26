// Clean export root for cross-crate use by tactus-computability-theory.
//
// Declares the full ghost dependency cone of BOTH:
//   (1) `cohen_layer05` — Layer 0.5: the C0 -> C Miller embedding
//       (lemma_c0_embeds_in_c_iff), consumed by the computability crate to instantiate
//       `decls_fam` with the CEER group's declared relators and the embedding iff; and
//   (2) `cohen_cs7` / `cohen_bridge` — Layer 2: the printable Higman group faithfulness
//       (lemma_C_faithful_printable / lemma_C_faithful_printable_canonical), so a future
//       cross-crate session can collapse the direct-limit C onto the finite printable H3
//       and remove `axiom_ceer_fp_embedding`. Exposing it now (not yet USED downstream)
//       is mechanical export-surface prep that avoids a dependency scramble at design time.
//
// EXCLUDES the runtime/exec showcase (`runtime`, `todd_coxeter_rt`): those use `usize::MAX`,
// which the Lean backend's tactus_auto cannot compile (IntegerTypeBound(UnsignedMax)
// deferral) -> verification errors that would block the --compile .rlib step. The ghost
// SPEC layer of `todd_coxeter` (CosetTable, symbol_to_column, trace_word, ...) IS included
// (it is what normal_form_* depends on); the exec layer was split into `todd_coxeter_rt`.
// All modules below are pure ghost (no exec fn / usize::MAX / external_body), verified
// in the full crate; the .vir records the verified cone (see build-export.sh for the two
// known-tolerated lake-spawn div-lemma flakes that make up the export's residual baseline).
//
// Built with --crate-name verus_group_theory so computability-theory's
//   use verus_group_theory::...
// resolves unchanged. Run build-export.sh (with -V cache) to (re)build the .vir + .rlib.

#[cfg(verus_keep_ghost)] pub mod abelianization;
#[cfg(verus_keep_ghost)] pub mod amalgamated_free_product;
#[cfg(verus_keep_ghost)] pub mod base_swap;
#[cfg(verus_keep_ghost)] pub mod benign;
#[cfg(verus_keep_ghost)] pub mod britton_infra;
#[cfg(verus_keep_ghost)] pub mod britton_via_tower;
#[cfg(verus_keep_ghost)] pub mod cohen_bridge;
#[cfg(verus_keep_ghost)] pub mod cohen_cs4;
#[cfg(verus_keep_ghost)] pub mod cohen_cs4b;
#[cfg(verus_keep_ghost)] pub mod cohen_cs4c;
#[cfg(verus_keep_ghost)] pub mod cohen_cs4d;
#[cfg(verus_keep_ghost)] pub mod cohen_cs4d_recog;
#[cfg(verus_keep_ghost)] pub mod cohen_cs4e;
#[cfg(verus_keep_ghost)] pub mod cohen_cs5;
#[cfg(verus_keep_ghost)] pub mod cohen_cs5_recog;
#[cfg(verus_keep_ghost)] pub mod cohen_cs6;
#[cfg(verus_keep_ghost)] pub mod cohen_cs7;
#[cfg(verus_keep_ghost)] pub mod cohen_h2;
#[cfg(verus_keep_ghost)] pub mod cohen_h3;
#[cfg(verus_keep_ghost)] pub mod cohen_layer05;
#[cfg(verus_keep_ghost)] pub mod cohen_layer05_probe;
#[cfg(verus_keep_ghost)] pub mod cohen_retraction;
#[cfg(verus_keep_ghost)] pub mod completeness;
#[cfg(verus_keep_ghost)] pub mod concrete;
#[cfg(verus_keep_ghost)] pub mod config_reduce;
#[cfg(verus_keep_ghost)] pub mod conj_free;
#[cfg(verus_keep_ghost)] pub mod conj_free_b;
#[cfg(verus_keep_ghost)] pub mod conj_free_core;
#[cfg(verus_keep_ghost)] pub mod coset_group;
#[cfg(verus_keep_ghost)] pub mod f_free;
#[cfg(verus_keep_ghost)] pub mod f_free_a1;
#[cfg(verus_keep_ghost)] pub mod f_free_h1;
#[cfg(verus_keep_ghost)] pub mod f_free_tower;
#[cfg(verus_keep_ghost)] pub mod finite;
#[cfg(verus_keep_ghost)] pub mod free_basis;
#[cfg(verus_keep_ghost)] pub mod free_family_perm;
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
#[cfg(verus_keep_ghost)] pub mod pa_data;
#[cfg(verus_keep_ghost)] pub mod phi_l_forward;
#[cfg(verus_keep_ghost)] pub mod phi_l_iso;
#[cfg(verus_keep_ghost)] pub mod phi_l_lift;
#[cfg(verus_keep_ghost)] pub mod phi_l_mapb;
#[cfg(verus_keep_ghost)] pub mod phi_l_mapb_fwd;
#[cfg(verus_keep_ghost)] pub mod phi_l_maps;
#[cfg(verus_keep_ghost)] pub mod phi_l_pinch;
#[cfg(verus_keep_ghost)] pub mod pred_amalgamated_free_product;
#[cfg(verus_keep_ghost)] pub mod pred_britton_via_tower;
#[cfg(verus_keep_ghost)] pub mod pred_emb_respects;
#[cfg(verus_keep_ghost)] pub mod pred_free_product;
#[cfg(verus_keep_ghost)] pub mod pred_hnn;
#[cfg(verus_keep_ghost)] pub mod pred_homomorphism;
#[cfg(verus_keep_ghost)] pub mod pred_normal_form_afp_textbook;
#[cfg(verus_keep_ghost)] pub mod pred_normal_form_amalgamated;
#[cfg(verus_keep_ghost)] pub mod pred_presentation;
#[cfg(verus_keep_ghost)] pub mod pred_presentation_lemmas;
#[cfg(verus_keep_ghost)] pub mod pred_tower;
#[cfg(verus_keep_ghost)] pub mod presentation;
#[cfg(verus_keep_ghost)] pub mod presentation_lemmas;
#[cfg(verus_keep_ghost)] pub mod prop_v;
#[cfg(verus_keep_ghost)] pub mod quotient;
#[cfg(verus_keep_ghost)] pub mod reduction;
#[cfg(verus_keep_ghost)] pub mod r_prime;
#[cfg(verus_keep_ghost)] pub mod r_prime_b;
#[cfg(verus_keep_ghost)] pub mod shortlex;
#[cfg(verus_keep_ghost)] pub mod symbol;
#[cfg(verus_keep_ghost)] pub mod tietze;
#[cfg(verus_keep_ghost)] pub mod todd_coxeter;
#[cfg(verus_keep_ghost)] pub mod tower;
#[cfg(verus_keep_ghost)] pub mod tower_peel;
#[cfg(verus_keep_ghost)] pub mod word;
#[cfg(verus_keep_ghost)] pub mod word_numbering;
