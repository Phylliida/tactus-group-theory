// Layer 2 — Cohen §1 assembly, brick CS-6: the faithfulness assembly `C ↪ H₃`.
//
// `docs/cohen-section1-assembly-plan.md` §3. With CS-4 (the a_i isos, `lemma_cs4e_iso_upto`)
// and CS-5 (the k iso, `lemma_cs5_iso`) DONE, the Layer-2 completeness target
//
//     equiv(h3_pred, w, ε)  ⟹  equiv(c_pred, w, ε)        (w a pure-c word)
//
// follows by the two-step descent of plan §3:
//
//   1. **Britton descent** (needs the a_i + k isos).  `w` is a base word of every tower level
//      (pure c-letters, all `< p_idx < a_base < k_top`).  Peel the top `k` via
//      `britton_lemma_unconditional` (consumes `lemma_cs5_iso`), then peel the whole a-tower
//      H₃→+a_{2n}→…→H₂ via the base-faithfulness lemma `lemma_h3_pred_upto_base_faithful`
//      (consumes `lemma_cs4e_iso_upto` for the a-level isos — the induction is encapsulated
//      there).  Net: `equiv(h3_pred, w, ε) ⟹ equiv(h2_pred, w, ε)`.
//   2. **c-retraction descent** (NO isos).  `lemma_h2_pred_descends_to_c` lands `w` in `C`
//      via the retraction ρ that fixes every c_j and kills every other generator.  This
//      sidesteps the H₂→H₁ p-peel (which would need an *infinite-association* Britton).
//
// This is Cohen's faithfulness of `C = ⟨c;S⟩ ↪ H₃` over the PREDICATE base.  Additive (new
// module + one lib.rs line); no regression.

use vstd::prelude::*;
use crate::word::{Word, empty_word, word_valid};
use crate::symbol::symbol_valid;
use crate::pred_presentation::equiv_in_pred_presentation;
use crate::pred_hnn::hnn_pred_presentation;
use crate::pred_britton_via_tower::britton_lemma_unconditional;
use crate::machine_group::{ModMachine, mod_machine_wf, mm_terminal, g_m};
use crate::layout::h2_num_gens;
use crate::cohen_h2::{h2_pred, s_relators_valid, s_realizes, is_c_word, lemma_c_word_valid};
use crate::cohen_h3::{h3_pred, h3_pred_data, lemma_h3_pred_data_valid,
    lemma_h3_pred_upto_num_generators};
use crate::cohen_cs4e::{lemma_cs4e_iso_upto, lemma_h3_pred_upto_base_faithful};
use crate::cohen_cs5_recog::lemma_cs5_iso;
use crate::cohen_retraction::{c_pred, lemma_h2_pred_descends_to_c};

verus! {

// ============================================================================
// Step 1 — the Britton descent  H₃ ⟹ H₂  (consumes the a_i + k isos)
// ============================================================================

/// **CS-6 step 1 — Britton descent down the predicate H₃ tower.**  A word `w` over the
/// h2-generators that is trivial in `H₃ = hnn_pred_presentation(h3_pred_data)` is trivial in the
/// base `h2_pred`.  Two peels: the top `k`-HNN via `britton_lemma_unconditional` (its iso hypothesis
/// = `lemma_cs5_iso`), then the whole a-tower H₃→+a_{2n}→…→H₂ via `lemma_h3_pred_upto_base_faithful`
/// (its iso hypothesis = `lemma_cs4e_iso_upto` at `k=2n`; the per-level induction lives there).
pub proof fn lemma_h3_pred_descends_to_h2(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        s_realizes(is_S, mm, n, m),
        word_valid(w, h2_num_gens(g_m(mm).num_generators, n)),
        equiv_in_pred_presentation(h3_pred(mm, n, m, is_S), w, empty_word()),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), w, empty_word()),
{
    let nk = g_m(mm).num_generators;
    let data = h3_pred_data(mm, n, m, is_S);

    // h3_pred == hnn_pred_presentation(data), data.base == h3_pred_upto(2n).
    assert(h3_pred(mm, n, m, is_S) == hnn_pred_presentation(data));

    // Britton hypotheses for the top k-HNN.
    lemma_h3_pred_data_valid(mm, n, m, is_S);                 // hnn_pred_data_valid(data)
    lemma_cs5_iso(mm, n, m, is_S);                            // hnn_pred_associations_isomorphic(data)

    // word_valid(w, data.base.num_generators): base has h2_num_gens + 2n generators ⊇ h2_num_gens.
    lemma_h3_pred_upto_num_generators(mm, n, m, is_S, (2 * n) as nat);
    assert(data.base.num_generators == h2_num_gens(nk, n) + 2 * n);
    assert(word_valid(w, data.base.num_generators)) by {
        assert forall|i: int| 0 <= i < w.len()
            implies symbol_valid(#[trigger] w[i], data.base.num_generators) by {
            assert(symbol_valid(w[i], h2_num_gens(nk, n)));
        }
    }

    // Peel the top k: equiv(data.base = h3_pred_upto(2n), w, ε).
    britton_lemma_unconditional(data, w);

    // Peel the a-tower: equiv(h3_pred_upto(2n), w, ε) ⟺ equiv(h2_pred, w, ε).
    lemma_cs4e_iso_upto(mm, n, m, is_S, (2 * n) as nat);      // cs4_levels_iso(.., 2n)
    lemma_h3_pred_upto_base_faithful(mm, n, m, is_S, (2 * n) as nat, w);
}

// ============================================================================
// CS-6 — the faithfulness headline  C ↪ H₃  (over the predicate base)
// ============================================================================

/// **CS-6 — Layer-2 completeness `C ↪ H₃` (predicate base).**  A pure-c word `w` trivial in `H₃`
/// is trivial in `C = ⟨c;S⟩ = c_pred`.  This is Cohen's faithfulness of the Higman embedding,
/// machine-checked over the predicate tower: step 1 (`lemma_h3_pred_descends_to_h2`, Britton descent
/// using the CS-4/CS-5 isos) ∘ step 2 (`lemma_h2_pred_descends_to_c`, the c-retraction, no isos).
///
/// Together with the soundness direction (`lemma_III`: `(α,0)∈H₀ ⟹ w_α(c)≡1`) this gives the
/// equivalence `w_α(c)=1 in H₃ ⟺ (α,0)∈H₀(M)`, the bridge the ZFC-group construction is built on.
pub proof fn lemma_C_faithful(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        s_realizes(is_S, mm, n, m),
        is_c_word(g_m(mm).num_generators, n, w),
        equiv_in_pred_presentation(h3_pred(mm, n, m, is_S), w, empty_word()),
    ensures
        equiv_in_pred_presentation(c_pred(mm, n, m, is_S), w, empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_c_word_valid(nk, n, w);                        // word_valid(w, h2_num_gens)
    lemma_h3_pred_descends_to_h2(mm, n, m, is_S, w);     // equiv(h2_pred, w, ε)   [step 1]
    lemma_h2_pred_descends_to_c(mm, n, m, is_S, w);      // equiv(c_pred,  w, ε)   [step 2]
}

} // verus!
