// Layer 2 — Cohen §1 assembly, brick CS-4a: the von-Dyck halves over the PREDICATE base.
//
// `docs/cohen-cs4-architecture.md` §4. The a_i association iso `(★) emb(a_col,w) ≡_{h2_pred} ε ⟺
// emb(b_col,w) ≡_{h2_pred} ε` factors via `P_A = pa_data` into two faithfulness halves (the hard
// p-peel, CS-4c/d via the compactness bridge CS-4b) and two **von-Dyck** halves — the EASY direction
// of each map. This brick is the von-Dyck halves, and over the predicate base they are
// **UNCONDITIONAL**: the finite-tower versions (`lemma_a_words_relator_trivial` /
// `lemma_b_words_relator_trivial`, over `h2_II`) carried a `finite-slice` side condition
// (`m·γ+l ∈ alphas`) that caused the session-8 vacuity; here the slice is gone, because every
// family-(II) relator is an `h2_pred` relator (the predicate carries the FULL family (II)).
//
// The two column embeddings translate `pa_data`'s relators to `h2_pred` relators:
//   * `emb(a_col, hnn_relator(pa_data,j)) = family_II_relator(γⱼ)`   (`lemma_a_words_on_hnn_relator`,
//     a base-independent WORD identity), trivial in `h2_pred` since `γⱼ` is a number word;
//   * `emb(b_col, hnn_relator(pa_data,j)) = φ_l(family_II_relator(γⱼ)) = family_II_relator(m·γⱼ+l)`
//     (`lemma_phi_l_factor_through_subst` + `lemma_phi_l_on_family_II_relator`, both base-independent),
//     trivial in `h2_pred` since `m·γⱼ+l` is a number word (`lemma_sigma_numbers_word`).
//
// The key new (and unconditional) atom is `lemma_family_II_relator_in_h2_pred`: ANY family-(II)
// relator of a number-word index is `≡_{h2_pred} ε` — the predicate-base win that retires the
// σ-slice obstruction. Additive/reversible; no regression.

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::presentation_valid;
use crate::pred_presentation::equiv_in_pred_presentation;
use crate::pred_presentation_lemmas::lemma_pred_relator_is_identity;
use crate::hnn::{hnn_relator, hnn_relators, hnn_presentation};
use crate::machine_group::{ModMachine, g_m, lemma_g_m_num_generators};
use crate::benign::apply_embedding;
use crate::word_numbering::numbers_word;
use crate::britton_infra::lemma_hnn_presentation_valid;
use crate::pa_data::{pa_data, lemma_pa_data_shape, lemma_pa_data_valid};
use crate::h3::phi_assoc;
use crate::h3_ii::{phi_l_subst, family_II_relator, lemma_phi_l_factor_through_subst};
use crate::phi_l_maps::{a_words, lemma_a_words_is_phi_col0};
use crate::phi_l_lift::{b_words, lemma_a_words_on_hnn_relator};
use crate::phi_l_iso::lemma_phi_l_on_family_II_relator;
use crate::phi_l_mapb_fwd::lemma_sigma_numbers_word;
use crate::cohen_h2::{h2_pred, h2_pred_relator, is_family_ii};

verus! {

// ----------------------------------------------------------------------------
// The predicate-base win: every family-(II) relator is trivial in `h2_pred`
// ----------------------------------------------------------------------------

/// **Any family-(II) relator of a number-word index is `≡_{h2_pred} ε`.** `is_family_ii(mm,n,m,·)`
/// holds for `family_II_relator(η)` (witness `β=η`, `numbers_word(η)`), so it satisfies the
/// `h2_pred_relator` disjunction ⟹ it is an `h2_pred` relator ⟹ trivial. **Unconditional in `η`**
/// (no finite `alphas` slice) — the predicate base carries the full family (II). This single atom is
/// what removes the σ-forward-closure obstruction that made the finite-tower von-Dyck vacuous.
pub proof fn lemma_family_II_relator_in_h2_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, eta: nat,
)
    requires
        numbers_word(n, m, eta),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            family_II_relator(mm, n, m, eta), empty_word()),
{
    let p = h2_pred(mm, n, m, is_S);
    let r = family_II_relator(mm, n, m, eta);
    assert(is_family_ii(mm, n, m, r)) by {
        assert(numbers_word(n, m, eta) && r == family_II_relator(mm, n, m, eta));
    }
    assert(h2_pred_relator(mm, n, m, is_S, r));
    assert((p.relators)(r) == h2_pred_relator(mm, n, m, is_S, r));
    assert((p.relators)(r));
    lemma_pred_relator_is_identity(p, r);
}

// ----------------------------------------------------------------------------
// von-Dyck `a` (the inclusion column): `emb(a_col, ·)` respects `pa_data` relators
// ----------------------------------------------------------------------------

/// **von-Dyck-`a` per-relator condition over `h2_pred`**: `a_col = a_words` sends each
/// `pa_data(gammas)` relator to `ε` in `h2_pred`. `emb(a_words, hnn_relator(pd,j)) =~=
/// family_II_relator(γⱼ)` (the base-independent word identity `lemma_a_words_on_hnn_relator`), which
/// is `≡_{h2_pred} ε` by `lemma_family_II_relator_in_h2_pred`. The homomorphism (von Dyck) condition
/// for `map_a : P_A → h2_pred` — unconditional (no `alphas` slice).
pub proof fn lemma_a_col_relator_trivial_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, gammas: Seq<nat>, j: int,
)
    requires
        2 * n < m,
        0 <= j < gammas.len(),
        numbers_word(n, m, gammas[j]),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(a_words(mm, n), hnn_relator(pa_data(n, m, gammas), j)),
            empty_word()),
{
    lemma_a_words_on_hnn_relator(mm, n, m, gammas, j);
    assert(apply_embedding(a_words(mm, n), hnn_relator(pa_data(n, m, gammas), j))
        =~= family_II_relator(mm, n, m, gammas[j]));
    lemma_family_II_relator_in_h2_pred(mm, n, m, is_S, gammas[j]);
}

// ----------------------------------------------------------------------------
// von-Dyck `b` (the φ_l column): `emb(b_col, ·)` respects `pa_data` relators
// ----------------------------------------------------------------------------

/// **von-Dyck-`b` per-relator condition over `h2_pred`**: `b_col = b_words = φ_l(a_col)` sends each
/// `pa_data(gammas)` relator to `ε` in `h2_pred`. `emb(b_words, hr) = φ_l(emb(a_words, hr)) =
/// φ_l(family_II_relator(γⱼ)) =~= family_II_relator(m·γⱼ+l)` (digit-scaling; the B1.5 factoring bridge
/// `lemma_phi_l_factor_through_subst` + `lemma_phi_l_on_family_II_relator`, both base-independent),
/// `≡_{h2_pred} ε` since `m·γⱼ+l` is a number word (`lemma_sigma_numbers_word`). The homomorphism (von
/// Dyck) condition for `map_b : P_A → h2_pred` — **unconditional** (no `m·γ+l ∈ alphas` finite-slice).
pub proof fn lemma_b_col_relator_trivial_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat, gammas: Seq<nat>, j: int,
)
    requires
        2 * n < m,
        1 <= l <= 2 * n,
        0 <= j < gammas.len(),
        forall|i: int| 0 <= i < gammas.len() ==> numbers_word(n, m, #[trigger] gammas[i]),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(b_words(mm, n, m, l), hnn_relator(pa_data(n, m, gammas), j)),
            empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let gamma = gammas[j];
    assert(numbers_word(n, m, gamma));                  // from the forall precondition at i = j
    let bw = b_words(mm, n, m, l);
    let pd = pa_data(n, m, gammas);
    let src = hnn_presentation(pd);
    let subst = phi_l_subst(nk, n, m, l);
    let hr = hnn_relator(pd, j);

    // hr is a valid word over the P_A generators (n+4), needed by the factoring bridge.
    lemma_pa_data_shape(n, m, gammas);
    lemma_pa_data_valid(n, m, gammas);
    lemma_hnn_presentation_valid(pd);
    assert(src.relators =~= hnn_relators(pd)) by {
        assert(pd.base.relators == Seq::<Word>::empty());
    }
    assert(src.num_generators == n + 4);
    assert(src.relators[j] == hnn_relators(pd)[j]);
    assert(hnn_relators(pd)[j] == hnn_relator(pd, j));
    assert(word_valid(hr, (n + 4) as nat)) by {
        reveal(presentation_valid);
        assert(word_valid(src.relators[j], src.num_generators));
    }

    // emb(b_words, hr) = subst(emb(col0, hr)) ; col0 == a_words ; emb(a_words,hr) =~= family_II_relator(γ).
    lemma_a_words_is_phi_col0(mm, n, m, l);
    let col0 = Seq::new((n + 4) as nat, |i: int| phi_assoc(nk, n, m, l)[i].0);
    assert(col0 =~= a_words(mm, n));
    lemma_phi_l_factor_through_subst(mm, n, m, l, hr);
    assert(apply_embedding(col0, hr) == apply_embedding(a_words(mm, n), hr));
    lemma_a_words_on_hnn_relator(mm, n, m, gammas, j);
    assert(apply_embedding(col0, hr) =~= family_II_relator(mm, n, m, gamma));
    assert(apply_embedding(bw, hr) == apply_embedding(subst, family_II_relator(mm, n, m, gamma)));

    // φ_l(family_II_relator(γ)) =~= family_II_relator(m·γ+l).
    lemma_phi_l_on_family_II_relator(mm, n, m, l, gamma);
    assert(apply_embedding(bw, hr) =~= family_II_relator(mm, n, m, (m * gamma + l) as nat));

    // m·γ+l is a number word ⟹ its relator is trivial in h2_pred.
    lemma_sigma_numbers_word(n, m, l, gamma);
    lemma_family_II_relator_in_h2_pred(mm, n, m, is_S, (m * gamma + l) as nat);
}

} // verus!
