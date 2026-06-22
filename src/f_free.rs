// Layer 2 — Brick 5 COMPLETENESS, C3.2c / F1: the free subgroup `F = ⟨t, x, d, b_j⟩` of `h2_II`.
//
// `F1` (the Route-B prerequisite, docs/brick5-c3.2c-plan.md §3b): the subgroup
// `F = ⟨t, x, d, b_1..b_n⟩` is FREE in `h1_base` (hence in `h2_II`, the p-HNN over it).
// This is what makes `A = ⟨t,x,d,b_j,p⟩ = HNN(F free, p | family II)` a legitimate
// presentation of the subgroup `A`, so `A`'s only relations are the p-conjugations and the
// von Dyck (backward) crux direction reduces to "`φ_l` respects the `p`-conjugations".
//
// Mathematics: `h1_base = K_M ∗ (F(c) × F(b)) ∗ ⟨d⟩` (a free product, since we DON'T carry `C`'s
// relator set `S`).  `F = ⟨t,x⟩ * ⟨b_j⟩ * ⟨d⟩`, where `⟨t,x⟩` is free in `K_M`, `⟨b_j⟩` free in
// the middle factor, `⟨d⟩` free.  Subgroups of distinct free factors generate their free product,
// hence `F` is free.
//
// NOTE on the obstruction: there is NO retraction `K_M → ⟨t,x⟩` (the machine relators are
// conjugacy relations among config words that cannot be killed while fixing `t, x`), so the
// pullback engine of `free_basis.rs` (which needs a valid homomorphism on the whole source) does
// NOT apply with `t, x` preserved.  `⟨t,x⟩` is free in `K_M` but is not a RETRACT of it — its
// freeness is established by the FAITHFUL base embedding `base_A ↪ K_M` (`lemma_g_m_base_faithful`)
// composed with `base_A = HNN(⟨t,x⟩ free, y)` (`a_as_hnn`), NOT by a homomorphism.
//
// This module builds the pieces bottom-up.  First brick (F1a): `⟨t,x⟩` is free in `K_M = g_m`.

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::*;
use crate::machine_group::*;
use crate::free_basis::lemma_g_m_base_faithful;

verus! {

// ----------------------------------------------------------------------------
// F1a — `⟨t,x⟩` is free in `K_M = g_m`.
// ----------------------------------------------------------------------------

/// **F1a.** A word over `{t = Gen(0), x = Gen(1)}` that is trivial in `K_M = g_m(mm)` is already
/// trivial in the free group `pres_tx = free⟨t,x⟩` — i.e. `⟨t,x⟩` is free in `K_M`.
///
/// Chain: lift `word_valid(·,2) → (·,3)`; descend `g_m → base_A` (`lemma_g_m_base_faithful`);
/// transport `base_A → A`'s HNN presentation (Tietze bridge `lemma_base_A_to_a_hnn`); then peel
/// the `y`-HNN layer `base_A = HNN(pres_tx, y | y⁻¹xy = x)` with `lemma_single_hnn_base_faithful`
/// (the `a_as_hnn` datum is valid + association-isomorphic).
pub proof fn lemma_tx_free_in_g_m(mm: ModMachine, w: Word)
    requires
        mod_machine_wf(mm),
        word_valid(w, 2),
        equiv_in_presentation(g_m(mm), w, empty_word()),
    ensures
        equiv_in_presentation(pres_tx(), w, empty_word()),
{
    // w is a base_A word (gens {0,1} ⊆ {0,1,2}).
    lemma_word_valid_mono(w, 2, 3);
    // g_m → base_A.
    lemma_g_m_base_faithful(mm, w);
    // base_A → pres_tx (Tietze bridge + peel the y-HNN layer): exactly `lemma_a_base_faithful`.
    lemma_a_base_faithful(w);
}

} // verus!
