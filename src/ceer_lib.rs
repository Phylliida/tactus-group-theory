// Clean export root for cross-crate use by tactus-computability-theory.
// Declares ONLY the group-theory modules the CEER->f.p.-group pipeline needs
// (a closed, fully-verified cone) — excludes the exec layer (runtime/todd_coxeter)
// so the .vir export doesn't hit the runtime Lean-backend panic, and excludes the
// Britton/normal-form showcase (not needed downstream). Built with
//   --crate-name verus_group_theory
// so computability-theory's `use verus_group_theory::...` resolves unchanged.
#[cfg(verus_keep_ghost)] pub mod symbol;
#[cfg(verus_keep_ghost)] pub mod word;
#[cfg(verus_keep_ghost)] pub mod reduction;
#[cfg(verus_keep_ghost)] pub mod presentation;
#[cfg(verus_keep_ghost)] pub mod presentation_lemmas;
#[cfg(verus_keep_ghost)] pub mod free_product;
#[cfg(verus_keep_ghost)] pub mod quotient;
#[cfg(verus_keep_ghost)] pub mod hnn;
#[cfg(verus_keep_ghost)] pub mod benign;
#[cfg(verus_keep_ghost)] pub mod amalgamated_free_product;
#[cfg(verus_keep_ghost)] pub mod tietze;
#[cfg(verus_keep_ghost)] pub mod higman_operations;
