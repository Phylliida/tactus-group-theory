// Layer 2 — Brick 5 COMPLETENESS, C3.2c / A1: the recognition-datum association isomorphism.
//
// `recog_data` (`h3_ii.rs`) recognizes the whole `h2_II` as a single `p`-HNN over `h1_base`, with
// associations `p_assoc ++ family_II_assoc`. Britton over that recognition needs only the iso
// condition `hnn_associations_isomorphic(recog_data)` — the "free-base fallacy": Britton never needs
// a free base, only that the `a_words ↦ b_words` correspondence is a subgroup iso.
//
// A1 (docs/brick5-c3.2c-plan.md §4.2) collapses that iso to an assembly of two ALREADY-PROVEN free
// families through F3 (`free_basis::lemma_free_to_embedding`):
//   • the `.0` column is `config_emb(betas)` with `betas = [0] ++ alphas` (the `p_assoc` head `(t,·)`
//     IS the α=0 case: `config_word(0,0) =~= [t]`),
//   • the `.1` column is `basis_emb(betas)` (the `p_assoc` head rhs `td` IS `basis_elt(0)` since
//     `w_b(_,0)=ε`; each `family_II_rhs(β) == basis_elt(β)` definitionally via `h_w_b = w_b(b_base…)`).
// Both columns are free in `h1_base` (`lemma_config_emb_free_in_h1` lifts F2 via the `kill_hom`
// retraction; `lemma_basis_elt_free` is the 29/0 headline), so the iff is "free ⟹ both trivial" both
// ways.
//
// THIS MODULE delivers the first two rungs (the genuinely-new SHORT pieces):
//   1. `lemma_km_faithful_in_h1`  — the `kill_hom` retraction: `K_M` embeds faithfully in `h1_base`.
//   2. `lemma_config_emb_free_in_h1` — config family free in `h1_base` (= F2 + the retraction).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::homomorphism::{apply_hom, lemma_hom_preserves_equiv};
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, lemma_g_m_num_generators, config_word,
    lemma_config_word_valid, lemma_word_valid_mono};
use crate::h1::h1_base;
use crate::benign::{apply_embedding, lemma_apply_embedding_valid};
use crate::free_basis::{kill_hom, lemma_kill_hom_valid, lemma_kill_fixes_low, config_emb,
    lemma_config_emb_free};
use crate::higman_operations::free_group;

verus! {

// ----------------------------------------------------------------------------
// A1, rung 1 — the `kill_hom` retraction:  K_M ↪ h1_base is faithful.
// ----------------------------------------------------------------------------

/// **`K_M` embeds faithfully in `h1_base`.** A `K_M`-word (`< nk` generators) that is trivial in
/// `h1_base` is already trivial in `K_M = g_m`. This is the one genuinely-new piece of A1: the
/// `kill_hom : h1_base → g_m` (identity on the K_M block, killing the c/b/d block) is a RETRACTION,
/// so equivalence in `h1_base` of a low word pushes down to `g_m`.
///
/// Proof: `kill_hom` is a valid homomorphism (`lemma_kill_hom_valid`), so it preserves equivalence
/// (`lemma_hom_preserves_equiv`): `φ(w) ≡_{g_m} φ(ε) = ε`. But `φ` fixes the low word `w`
/// (`lemma_kill_fixes_low`: `φ(w) =~= w`), so `w ≡_{g_m} ε`.
pub proof fn lemma_km_faithful_in_h1(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, g_m(mm).num_generators),
        equiv_in_presentation(h1_base(mm, n), w, empty_word()),
    ensures
        equiv_in_presentation(g_m(mm), w, empty_word()),
{
    let h = kill_hom(mm, n);
    lemma_kill_hom_valid(mm, n);                       // is_valid_homomorphism(h)
    assert(h.source == h1_base(mm, n) && h.target == g_m(mm));
    // φ preserves equivalence: φ(w) ≡_{g_m} φ(ε).
    lemma_hom_preserves_equiv(h, w, empty_word());
    // φ fixes the low word: φ(w) =~= w; and φ(ε) =~= ε.
    lemma_kill_fixes_low(mm, n, w);
    assert(apply_hom(h, empty_word()) =~= empty_word());
}

// ----------------------------------------------------------------------------
// A1, rung 2 — the config family is free in `h1_base`.
// ----------------------------------------------------------------------------

/// **`config_emb(alphas)` is a free family in `h1_base`.** `lemma_config_emb_free` already gives it
/// free in `K_M = g_m`; we LIFT to `h1_base` via the retraction `lemma_km_faithful_in_h1`. The
/// embedded product `apply_embedding(config_emb, w)` is a `K_M`-word (config words live on gens
/// 0–2 < nk), so triviality in `h1_base` descends to `g_m`, where F2 closes it.
pub proof fn lemma_config_emb_free_in_h1(mm: ModMachine, n: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        alphas.no_duplicates(),
        word_valid(w, alphas.len()),
        equiv_in_presentation(h1_base(mm, n),
            apply_embedding(config_emb(alphas), w), empty_word()),
    ensures
        equiv_in_presentation(free_group(alphas.len()), w, empty_word()),
{
    let emb = config_emb(alphas);
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                      // nk = 4 + |quads| ≥ 4 > 3
    // Each config word is valid over the base-A gens {0,1,2}, hence over nk.
    assert forall|i: int| 0 <= i < emb.len() implies word_valid(#[trigger] emb[i], nk) by {
        assert(emb[i] == config_word(alphas[i], 0));
        lemma_config_word_valid(alphas[i], 0);         // word_valid(·, 3)
        lemma_word_valid_mono(emb[i], 3, nk);          // 3 ≤ nk
    }
    // So the whole embedded product is a K_M word.
    lemma_apply_embedding_valid(emb, w, nk);
    // Retraction: ≡_{h1_base} ε  ⟹  ≡_{g_m} ε.
    lemma_km_faithful_in_h1(mm, n, apply_embedding(emb, w));
    // F2: the config family is free in g_m ⟹ w ≡_free ε.
    lemma_config_emb_free(mm, alphas, w);
}

} // verus!
