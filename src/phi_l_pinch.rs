// Layer 2 — Brick 5, C3.2c / the C-arc: `map_a`'s forward Britton-peel assembly.
//
// Wires the generic forward leaves (`phi_l_forward`: relabel facts + intersection property) to the
// concrete `recog_data` / `pa_data` columns: the column correspondence (`recog` columns are the
// `a_words_F`-images of `pa` columns), the pinch-descent (same-index, since `a_words` is a
// relabeling), and the forward injectivity induction.  See `docs/brick5-c3.2c-plan.md` §5.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{ModMachine, g_m, config_word, lemma_g_m_num_generators,
    lemma_config_word_valid, lemma_word_valid_mono};
use crate::benign::apply_embedding;
use crate::word_numbering::{w_c, numbers_word, lemma_w_c_valid};
use crate::f_free::lemma_apply_embedding_agree_prefix;
use crate::phi_l_maps::{a_words, a_words_F, lemma_a_words_fixes_config, lemma_a_words_on_pa_rhs};
use crate::pa_data::{pa_rhs, pa_b_base};
use crate::h3::lemma_single_gen_valid;
use crate::h3_ii::family_II_rhs;

verus! {

// ----------------------------------------------------------------------------
// The a_words / a_words_F agreement bridge + a_words_F column fixes.
// ----------------------------------------------------------------------------

/// **The relabeling bridge**: `a_words = a_words_F.push([p])`, so the two embeddings AGREE on every
/// word valid over `n+3` (the F-generators) — `apply_embedding(a_words, u) =~= apply_embedding(
/// a_words_F, u)`.  Lets the (pub) `a_words` column translations feed the `a_words_F`-based
/// intersection property (`a_words_F` is the free family in `h1_base`).
pub proof fn lemma_a_words_eq_a_words_F(mm: ModMachine, n: nat, u: Word)
    requires
        word_valid(u, (n + 3) as nat),
    ensures
        apply_embedding(a_words(mm, n), u) =~= apply_embedding(a_words_F(mm, n), u),
{
    let aw = a_words(mm, n);
    let awf = a_words_F(mm, n);
    // a_words = a_words_F.push(...) ⟹ len n+4, agrees with a_words_F on [0, n+3).
    assert(aw.len() == n + 4);
    assert(awf.len() == n + 3);
    assert forall|i: int| 0 <= i < n + 3 implies aw[i] == awf[i] by {}
    lemma_apply_embedding_agree_prefix(aw, awf, u, (n + 3) as nat);
}

/// **`a_words_F` fixes a config word**: `apply_embedding(a_words_F, config(γ,0)) =~= config(γ,0)`.
/// Bridges `lemma_a_words_fixes_config` (stated for `a_words`) to `a_words_F` (the free family).
pub proof fn lemma_a_words_F_fixes_config(mm: ModMachine, n: nat, gamma: nat)
    ensures
        apply_embedding(a_words_F(mm, n), config_word(gamma, 0)) =~= config_word(gamma, 0),
{
    lemma_config_word_valid(gamma, 0);                       // word_valid(config(γ,0), 3)
    lemma_word_valid_mono(config_word(gamma, 0), 3, (n + 3) as nat);
    lemma_a_words_eq_a_words_F(mm, n, config_word(gamma, 0));
    lemma_a_words_fixes_config(mm, n, gamma);
}

/// **`a_words_F` carries `pa_rhs` onto `family_II_rhs`**: `apply_embedding(a_words_F, pa_rhs(γ)) =~=
/// family_II_rhs(γ)`.  Bridges `lemma_a_words_on_pa_rhs` (stated for `a_words`) to `a_words_F`.
pub proof fn lemma_a_words_F_on_pa_rhs(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        apply_embedding(a_words_F(mm, n), pa_rhs(n, m, gamma)) =~= family_II_rhs(mm, n, m, gamma),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    // pa_rhs(γ) = config(γ,0) + w_c(3,n,m,γ) + [Gen2], valid over n+3.
    lemma_pa_rhs_valid_n3(mm, n, m, gamma);
    lemma_a_words_eq_a_words_F(mm, n, pa_rhs(n, m, gamma));
    lemma_a_words_on_pa_rhs(mm, n, m, gamma);
}

/// `pa_rhs(γ)` is valid over `n+3` (config uses `{0,1}`, the F-b-block `w_c(3,…)` sits in `[3,n+3)`,
/// `d = Gen(2) < n+3`).  (Re-derives the validity `pa_data` uses, without the full HNN datum.)
proof fn lemma_pa_rhs_valid_n3(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        word_valid(pa_rhs(n, m, gamma), (n + 3) as nat),
{
    let ng = (n + 3) as nat;
    lemma_config_word_valid(gamma, 0);
    lemma_word_valid_mono(config_word(gamma, 0), 3, ng);
    lemma_w_c_valid(pa_b_base(), n, m, gamma, ng);            // 3 + n ≤ n + 3
    lemma_single_gen_valid(2, ng);
    lemma_concat_word_valid(config_word(gamma, 0), w_c(pa_b_base(), n, m, gamma), ng);
    lemma_concat_word_valid(config_word(gamma, 0) + w_c(pa_b_base(), n, m, gamma),
        seq![Symbol::Gen(2)], ng);
    assert(pa_rhs(n, m, gamma) =~= (config_word(gamma, 0) + w_c(pa_b_base(), n, m, gamma))
        + seq![Symbol::Gen(2)]);
}

} // verus!
