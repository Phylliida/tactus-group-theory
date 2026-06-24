// Layer 2 — Cohen §1 assembly, brick CS-4c (prep): the slice NORMALIZATION.
//
// `docs/cohen-cs4-architecture.md` §4. CS-4b's compactness bridge produces a finite slice
// `h2_II(alphas)` with `alphas` a list of NUMBER WORDS — but possibly with duplicates and with
// the index `0`. The forward faithfulness lemma `lemma_map_a_forward` (phi_l_pinch.rs) requires
// `alphas` to be `no_duplicates()` and `!contains(0)` (so `betas(alphas) = [0] ++ alphas` is a
// duplicate-free association list for `pa_data`). This brick is the normalization that bridges
// the two.
//
// `normalize_alphas(alphas)` drops `0` and de-duplicates. Equivalence is preserved because the
// relator SET is unchanged:
//   * dropping a duplicate `family_II_relator(β)` — the surviving copy still derives it;
//   * dropping `family_II_relator(0)` — it is ALREADY a relator of `h2_pres` (it equals the single
//     `p`-HNN relator `p⁻¹ t p (td)⁻¹`, since `config_word(0,0) = [t]` and `w_b(0) = ε`).
// Both are captured by `relators_included(h2_II(alphas), h2_II(normalize_alphas(alphas)))` +
// `lemma_relator_inclusion_preserves_equiv` (presentation_lemmas).
//
// Additive/reversible (new module + one lib.rs line); no regression.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::pred_presentation::equiv_in_pred_presentation;
use crate::base_swap::{lemma_add_relators_relators, lemma_single_step_equiv};
use crate::machine_group::*;
use crate::layout::*;
use crate::word_numbering::{numbers_word, w_b};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_valid};
use crate::h1::h1_base;
use crate::h2::{h2_pres, h2_data, td_word, p_assoc, lemma_h2_stable_letter};
use crate::hnn::{hnn_relators, hnn_relator, hnn_presentation, stable_letter, stable_letter_inv};
use crate::h3::{phi_assoc, lemma_phi_assoc_valid};
use crate::h3_ii::{h2_II, family_II, family_II_relator, family_II_lhs, family_II_rhs,
    lemma_phi_assoc_len};
use crate::phi_l_maps::{a_words, a_words_F};
use crate::phi_l_forward::lemma_a_words_single_gen;
use crate::phi_l_lift::b_words;
use crate::phi_l_pinch::{lemma_map_a_forward, lemma_a_words_img_valid};
use crate::pa_data::{pa_data, lemma_pa_data_shape, lemma_pa_data_valid};
use crate::britton_infra::lemma_hnn_presentation_valid;
use crate::f_free_a1::{betas, lemma_betas_index};
use crate::pred_emb_respects::lemma_emb_respects_source_equiv_pred;
use crate::cohen_h2::{h2_pred, lemma_h2_pred_valid, s_relators_valid, c_symbol};
use crate::cohen_retraction::{no_c_word, lemma_no_c_inverse, lemma_no_c_concat};
use crate::cohen_cs4::{lemma_b_col_relator_trivial_pred, lemma_a_col_relator_trivial_pred};
use crate::cohen_cs4b::lemma_cs4b_compactness;
use crate::phi_l_mapb::{phi_l_src, lemma_phi_l_src_valid, lemma_phi_l_src_len,
    lemma_mapb_factor_source, lemma_pa_data_isomorphic};
use crate::phi_l_mapb_fwd::lemma_mapb_M2_general;
use crate::cohen_cs4d::{bet_of, lemma_bet_of_number_words, lemma_bet_of_no_dup};

verus! {

// ============================================================================
// `normalize_alphas` — drop `0`, de-duplicate
// ============================================================================

/// Drop every `0` and every repeated entry, keeping first occurrences (recursion on `drop_last`).
pub open spec fn normalize_alphas(alphas: Seq<nat>) -> Seq<nat>
    decreases alphas.len(),
{
    if alphas.len() == 0 {
        Seq::<nat>::empty()
    } else {
        let rest = normalize_alphas(alphas.drop_last());
        let last = alphas.last();
        if last == 0 || rest.contains(last) {
            rest
        } else {
            rest.push(last)
        }
    }
}

// ----------------------------------------------------------------------------
// Pure-Seq properties of `normalize_alphas`
// ----------------------------------------------------------------------------

/// `normalize_alphas` never contains `0`.
pub proof fn lemma_normalize_no_zero(alphas: Seq<nat>)
    ensures
        !normalize_alphas(alphas).contains(0nat),
    decreases alphas.len(),
{
    if alphas.len() == 0 {
    } else {
        lemma_normalize_no_zero(alphas.drop_last());
        let rest = normalize_alphas(alphas.drop_last());
        let last = alphas.last();
        if last == 0 || rest.contains(last) {
        } else {
            assert(last != 0);
            assert forall|i: int| 0 <= i < rest.push(last).len()
                implies rest.push(last)[i] != 0 by {
                if i < rest.len() {
                    assert(rest.push(last)[i] == rest[i]);
                    assert(!rest.contains(0nat));
                } else {
                    assert(rest.push(last)[i] == last);
                }
            }
        }
    }
}

/// `normalize_alphas` is duplicate-free.
pub proof fn lemma_normalize_no_dup(alphas: Seq<nat>)
    ensures
        normalize_alphas(alphas).no_duplicates(),
    decreases alphas.len(),
{
    if alphas.len() == 0 {
    } else {
        lemma_normalize_no_dup(alphas.drop_last());
        let rest = normalize_alphas(alphas.drop_last());
        let last = alphas.last();
        if last == 0 || rest.contains(last) {
        } else {
            // rest no-dup ∧ !rest.contains(last) ⟹ rest.push(last) no-dup
            let big = rest.push(last);
            assert forall|i: int, j: int| 0 <= i < big.len() && 0 <= j < big.len() && i != j
                implies big[i] != big[j] by {
                if i < rest.len() && j < rest.len() {
                    assert(big[i] == rest[i] && big[j] == rest[j]);
                } else if i == rest.len() {
                    assert(big[i] == last);
                    assert(big[j] == rest[j]);
                    assert(rest.contains(rest[j]));    // j < rest.len()
                    assert(!rest.contains(last));
                } else {
                    assert(big[j] == last);
                    assert(big[i] == rest[i]);
                    assert(rest.contains(rest[i]));
                    assert(!rest.contains(last));
                }
            }
        }
    }
}

/// Every element of `normalize_alphas(alphas)` is an element of `alphas`.
pub proof fn lemma_normalize_elements_in(alphas: Seq<nat>)
    ensures
        forall|j: int| 0 <= j < normalize_alphas(alphas).len()
            ==> alphas.contains(#[trigger] normalize_alphas(alphas)[j]),
    decreases alphas.len(),
{
    if alphas.len() == 0 {
    } else {
        lemma_normalize_elements_in(alphas.drop_last());
        let rest = normalize_alphas(alphas.drop_last());
        let last = alphas.last();
        // every element of drop_last is an element of alphas
        assert forall|x: nat| alphas.drop_last().contains(x) implies alphas.contains(x) by {
            let k = choose|k: int| 0 <= k < alphas.drop_last().len() && alphas.drop_last()[k] == x;
            assert(alphas[k] == x);
        }
        assert(alphas.contains(last)) by { assert(alphas[alphas.len() - 1] == last); }
        if last == 0 || rest.contains(last) {
            assert forall|j: int| 0 <= j < rest.len()
                implies alphas.contains(#[trigger] rest[j]) by {
                assert(alphas.drop_last().contains(rest[j]));
            }
        } else {
            let big = rest.push(last);
            assert forall|j: int| 0 <= j < big.len()
                implies alphas.contains(#[trigger] big[j]) by {
                if j < rest.len() {
                    assert(big[j] == rest[j]);
                    assert(alphas.drop_last().contains(rest[j]));
                } else {
                    assert(big[j] == last);
                }
            }
        }
    }
}

/// Number-word membership is inherited (elements come from `alphas`).
pub proof fn lemma_normalize_number_words(alphas: Seq<nat>, n: nat, m: nat)
    requires
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        forall|j: int| 0 <= j < normalize_alphas(alphas).len()
            ==> numbers_word(n, m, #[trigger] normalize_alphas(alphas)[j]),
{
    lemma_normalize_elements_in(alphas);
    assert forall|j: int| 0 <= j < normalize_alphas(alphas).len()
        implies numbers_word(n, m, #[trigger] normalize_alphas(alphas)[j]) by {
        let x = normalize_alphas(alphas)[j];
        assert(alphas.contains(x));
        let k = choose|k: int| 0 <= k < alphas.len() && alphas[k] == x;
        assert(numbers_word(n, m, alphas[k]));
    }
}

/// A nonzero element of `alphas` survives normalization.
pub proof fn lemma_normalize_preserves_membership(alphas: Seq<nat>, beta: nat)
    requires
        beta != 0,
        alphas.contains(beta),
    ensures
        normalize_alphas(alphas).contains(beta),
    decreases alphas.len(),
{
    let rest = normalize_alphas(alphas.drop_last());
    let last = alphas.last();
    // alphas.contains(beta) ⟹ drop_last.contains(beta) ∨ beta == last
    if alphas.drop_last().contains(beta) {
        lemma_normalize_preserves_membership(alphas.drop_last(), beta);
        assert(rest.contains(beta));
        if last == 0 || rest.contains(last) {
        } else {
            let big = rest.push(last);
            let k = choose|k: int| 0 <= k < rest.len() && rest[k] == beta;
            assert(big[k] == beta);
        }
    } else {
        // beta must be the last element
        let k = choose|k: int| 0 <= k < alphas.len() && alphas[k] == beta;
        assert(k == alphas.len() - 1) by {
            if k < alphas.len() - 1 {
                assert(alphas.drop_last()[k] == beta);
                assert(alphas.drop_last().contains(beta));
            }
        }
        assert(last == beta);
        if last == 0 || rest.contains(last) {
            assert(rest.contains(beta));
        } else {
            let big = rest.push(last);
            assert(big[rest.len() as int] == last);
            assert(big.contains(last));
        }
    }
}

// ============================================================================
// `family_II_relator(0)` is already a relator of `h2_pres`
// ============================================================================

// local contains helpers (mirror cohen_cs4b)
proof fn lemma_cc_left(a: Seq<Word>, c: Seq<Word>, x: Word)
    requires a.contains(x),
    ensures (a + c).contains(x),
{
    let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
    assert((a + c)[i] == a[i]);
    assert(0 <= i < (a + c).len());
}

proof fn lemma_cc_right(a: Seq<Word>, c: Seq<Word>, x: Word)
    requires c.contains(x),
    ensures (a + c).contains(x),
{
    let i = choose|i: int| 0 <= i < c.len() && c[i] == x;
    assert((a + c)[a.len() + i] == c[i]);
    assert(0 <= a.len() + i < (a + c).len());
}

/// `family_II_relator(mm,n,m,0) = hnn_relator(h2_data, 0)` (the single `p`-HNN relator
/// `p⁻¹ t p (td)⁻¹`): `config_word(0,0) = [t]` and `w_b(0) = ε`.
pub proof fn lemma_family_II_relator_0_eq_hnn(mm: ModMachine, n: nat, m: nat)
    ensures
        family_II_relator(mm, n, m, 0) == hnn_relator(h2_data(mm, n), 0),
{
    let nk = g_m(mm).num_generators;
    let p = p_idx(nk, n);
    let d = d_idx(nk, n);
    let bb = b_base(nk, n);

    // config_word(0,0) = [Gen(0)]
    assert(symbol_power(Symbol::Inv(2), 0) =~= empty_word());
    assert(symbol_power(Symbol::Inv(1), 0) =~= empty_word());
    assert(symbol_power(Symbol::Gen(1), 0) =~= empty_word());
    assert(symbol_power(Symbol::Gen(2), 0) =~= empty_word());
    assert(config_word(0, 0) =~= seq![Symbol::Gen(0)]);

    // w_b(bb,n,m,0) = ε
    assert(w_b(bb, n, m, 0) =~= empty_word());

    // family_II_lhs(0) = [p⁻¹] + [Gen(0)] + [p]
    assert(family_II_lhs(mm, n, 0)
        =~= seq![Symbol::Inv(p)] + seq![Symbol::Gen(0)] + seq![Symbol::Gen(p)]);
    // family_II_rhs(0) = [Gen(0)] + [d] = td_word
    assert(family_II_rhs(mm, n, m, 0) =~= td_word(nk, n)) by {
        assert(td_word(nk, n) =~= seq![Symbol::Gen(0), Symbol::Gen(d)]);
        assert(family_II_rhs(mm, n, m, 0)
            =~= seq![Symbol::Gen(0)] + empty_word() + seq![Symbol::Gen(d)]);
    }

    // hnn_relator(h2_data, 0) = [p⁻¹] + [Gen(0)] + [p] + inverse(td_word)
    let hd = h2_data(mm, n);
    lemma_h2_stable_letter(mm, n);                  // stable_letter(hd) == Gen(p_idx)
    assert(stable_letter(hd) == Symbol::Gen(p));
    assert(hd.base.num_generators == p);            // stable_letter = Gen(base.num_generators)
    assert(stable_letter_inv(hd) == Symbol::Inv(p));
    assert(hd.associations[0] == (seq![Symbol::Gen(0)], td_word(nk, n))) by {
        assert(hd.associations == p_assoc(nk, n));
        assert(p_assoc(nk, n)[0] == (seq![Symbol::Gen(0)], td_word(nk, n)));
    }
    assert(hnn_relator(hd, 0)
        =~= seq![Symbol::Inv(p)] + seq![Symbol::Gen(0)] + seq![Symbol::Gen(p)]
            + inverse_word(td_word(nk, n)));

    assert(family_II_relator(mm, n, m, 0)
        =~= family_II_lhs(mm, n, 0) + inverse_word(family_II_rhs(mm, n, m, 0)));
    assert(inverse_word(family_II_rhs(mm, n, m, 0)) == inverse_word(td_word(nk, n)));
}

/// `family_II_relator(mm,n,m,0)` is a relator of `h2_pres` (it equals the single HNN relator).
pub proof fn lemma_family_II_relator_0_in_h2_pres(mm: ModMachine, n: nat, m: nat)
    ensures
        h2_pres(mm, n).relators.contains(family_II_relator(mm, n, m, 0)),
{
    let hd = h2_data(mm, n);
    lemma_family_II_relator_0_eq_hnn(mm, n, m);
    // hnn_relators(hd) = Seq::new(1, ..), element 0 = hnn_relator(hd,0)
    assert(hd.associations.len() == 1) by { assert(hd.associations == p_assoc(g_m(mm).num_generators, n)); }
    assert(hnn_relators(hd)[0] == hnn_relator(hd, 0));
    assert(hnn_relators(hd).contains(family_II_relator(mm, n, m, 0))) by {
        assert(hnn_relators(hd)[0] == family_II_relator(mm, n, m, 0));
        assert(0 <= 0 < hnn_relators(hd).len());
    }
    // h2_pres.relators = h1_base.relators + hnn_relators(hd)
    assert(h2_pres(mm, n).relators =~= h1_base(mm, n).relators + hnn_relators(hd));
    lemma_cc_right(h1_base(mm, n).relators, hnn_relators(hd), family_II_relator(mm, n, m, 0));
}

// ============================================================================
// Direct derivation replay `h2_II(alphas) → h2_II(normalize_alphas(alphas))`
// (sidesteps `relators_included`, whose `forall i. exists j` did not fold under
//  the Lean backend; a per-element membership + step replay is robust)
// ============================================================================

/// Per-element: a relator of the raw slice is a relator of the normalized slice. (`h2_pres` shared
/// prefix; family-(II) relators survive — `0` lands in `h2_pres`, nonzero `β`'s kept by `normalize`.)
pub proof fn lemma_h2_II_relator_in_norm(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, r: Word)
    requires
        h2_II(mm, n, m, alphas).relators.contains(r),
    ensures
        h2_II(mm, n, m, normalize_alphas(alphas)).relators.contains(r),
{
    let norm = normalize_alphas(alphas);
    let hp = h2_pres(mm, n).relators;
    let fa = family_II(mm, n, m, alphas);
    let fnorm = family_II(mm, n, m, norm);
    lemma_add_relators_relators(h2_pres(mm, n), fa);
    lemma_add_relators_relators(h2_pres(mm, n), fnorm);
    assert(h2_II(mm, n, m, alphas).relators == hp + fa);
    assert(h2_II(mm, n, m, norm).relators == hp + fnorm);
    lemma_family_II_relator_0_in_h2_pres(mm, n, m);

    let i = choose|i: int| 0 <= i < (hp + fa).len() && (hp + fa)[i] == r;
    if i < hp.len() {
        assert((hp + fa)[i] == hp[i]);
        assert(hp.contains(r));            // witness i
        lemma_cc_left(hp, fnorm, r);
    } else {
        let k = i - hp.len();
        assert((hp + fa)[i] == fa[k]);
        assert(fa[k] == family_II_relator(mm, n, m, alphas[k]));
        let beta = alphas[k];
        assert(alphas.contains(beta)) by { assert(alphas[k] == beta); }
        if beta == 0 {
            assert(hp.contains(r));        // r == family_II_relator(0) ∈ hp
            lemma_cc_left(hp, fnorm, r);
        } else {
            lemma_normalize_preserves_membership(alphas, beta);
            let jj = choose|jj: int| 0 <= jj < norm.len() && norm[jj] == beta;
            assert(fnorm[jj] == family_II_relator(mm, n, m, beta));
            assert(fnorm.contains(r)) by { assert(0 <= jj < fnorm.len()); }
            lemma_cc_right(hp, fnorm, r);
        }
    }
}

/// A single derivation step in the raw slice replays as a `≡` in the normalized slice.
proof fn lemma_h2_II_step_replay(
    mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word, step: DerivationStep, w2: Word,
)
    requires
        apply_step(h2_II(mm, n, m, alphas), w, step) == Some(w2),
    ensures
        equiv_in_presentation(h2_II(mm, n, m, normalize_alphas(alphas)), w, w2),
{
    let p1 = h2_II(mm, n, m, alphas);
    let p2 = h2_II(mm, n, m, normalize_alphas(alphas));
    lemma_add_relators_relators(h2_pres(mm, n), family_II(mm, n, m, alphas));
    lemma_add_relators_relators(h2_pres(mm, n), family_II(mm, n, m, normalize_alphas(alphas)));
    assert(p1.num_generators == p2.num_generators);
    match step {
        DerivationStep::FreeReduce { position } => {
            assert(apply_step(p2, w, step) == Some(w2));
            lemma_single_step_equiv(p2, w, step, w2);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            assert(apply_step(p2, w, step) == Some(w2));
            lemma_single_step_equiv(p2, w, step, w2);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            let r = p1.relators[relator_index as int];
            assert(p1.relators.contains(r));          // witness relator_index
            lemma_h2_II_relator_in_norm(mm, n, m, alphas, r);
            let j = choose|j: int| 0 <= j < p2.relators.len() && p2.relators[j] == r;
            let step2 = DerivationStep::RelatorInsert { position, relator_index: j as nat, inverted };
            assert(get_relator(p2, j as nat, inverted) == get_relator(p1, relator_index, inverted));
            assert(apply_step(p2, w, step2) == Some(w2));
            lemma_single_step_equiv(p2, w, step2, w2);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            let r = p1.relators[relator_index as int];
            assert(p1.relators.contains(r));
            lemma_h2_II_relator_in_norm(mm, n, m, alphas, r);
            let j = choose|j: int| 0 <= j < p2.relators.len() && p2.relators[j] == r;
            let step2 = DerivationStep::RelatorDelete { position, relator_index: j as nat, inverted };
            assert(get_relator(p2, j as nat, inverted) == get_relator(p1, relator_index, inverted));
            assert(apply_step(p2, w, step2) == Some(w2));
            lemma_single_step_equiv(p2, w, step2, w2);
        },
    }
}

/// A whole raw-slice derivation replays as a normalized-slice equivalence.
proof fn lemma_h2_II_deriv_replay(
    mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(h2_II(mm, n, m, alphas), steps, w1) == Some(w2),
    ensures
        equiv_in_presentation(h2_II(mm, n, m, normalize_alphas(alphas)), w1, w2),
    decreases steps.len(),
{
    let p2 = h2_II(mm, n, m, normalize_alphas(alphas));
    if steps.len() == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(p2, w1);
    } else {
        let step = steps.first();
        let next = apply_step(h2_II(mm, n, m, alphas), w1, step).unwrap();
        lemma_h2_II_step_replay(mm, n, m, alphas, w1, step, next);
        lemma_h2_II_deriv_replay(mm, n, m, alphas, steps.drop_first(), next, w2);
        lemma_equiv_transitive(p2, w1, next, w2);
    }
}

/// **CS-4c-prep headline — slice normalization.** A word trivial in the raw slice `h2_II(alphas)`
/// (number-word `alphas`) is trivial in `h2_II(normalize_alphas(alphas))`, which is `no_duplicates`,
/// `∌ 0`, and still all number words — the exact precondition shape `lemma_map_a_forward` consumes.
pub proof fn lemma_h2_II_normalize_equiv(
    mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w1: Word, w2: Word,
)
    requires
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        equiv_in_presentation(h2_II(mm, n, m, alphas), w1, w2),
    ensures
        normalize_alphas(alphas).no_duplicates(),
        !normalize_alphas(alphas).contains(0nat),
        forall|i: int| 0 <= i < normalize_alphas(alphas).len()
            ==> numbers_word(n, m, #[trigger] normalize_alphas(alphas)[i]),
        equiv_in_presentation(h2_II(mm, n, m, normalize_alphas(alphas)), w1, w2),
{
    lemma_normalize_no_dup(alphas);
    lemma_normalize_no_zero(alphas);
    lemma_normalize_number_words(alphas, n, m);
    let d = choose|d: Derivation| derivation_valid(h2_II(mm, n, m, alphas), d, w1, w2);
    lemma_h2_II_deriv_replay(mm, n, m, alphas, d.steps, w1, w2);
}

// ============================================================================
// CS-4c — the von-Dyck FORWARD wiring (`a ⟹ b`)
// ============================================================================
//
// `docs/cohen-cs4-architecture.md` §4 (CS-4c forward). The a_i iso half:
//
//   emb(a_col, w) ≡_{h2_pred} ε   ⟹   emb(b_col, w) ≡_{h2_pred} ε
//
// chained from the proven machinery:
//   (a) emb(a_col, w) is c-free (a_col = a_words has no c-block image) and word-valid;
//   (b) CS-4b compactness — a finite slice `alphas` with emb(a_col,w) ≡_{h2_II(alphas)} ε;
//   (c) normalize `alphas` (drop 0, de-dup) to meet `lemma_map_a_forward`'s preconditions;
//   (d) `lemma_map_a_forward` — the Britton-peel faithfulness of `map_a`: w ≡_{P_A = pa_data(betas)} ε;
//   (e) push that `P_A`-triviality into `h2_pred` through the `b_col = b_words` homomorphism
//       (`lemma_emb_respects_source_equiv_pred`), whose relator condition is the CS-4a b-von-Dyck
//       (`lemma_b_col_relator_trivial_pred`).

// ----------------------------------------------------------------------------
// c-freeness of `emb(a_words, w)`
// ----------------------------------------------------------------------------

/// A single generator outside the c-block `[c_base, c_base+n)` is a c-free word.
proof fn lemma_no_c_single_gen(nk: nat, n: nat, g: nat)
    requires
        g < nk || g >= nk + n,
    ensures
        no_c_word(nk, n, seq![Symbol::Gen(g)]),
{
    let w = seq![Symbol::Gen(g)];
    assert forall|k: int| 0 <= k < w.len() implies !c_symbol(nk, n, #[trigger] w[k]) by {
        assert(w[k] == Symbol::Gen(g));
        assert(generator_index(Symbol::Gen(g)) == g);
    }
}

/// Each `a_words` image is c-free: every column generator lands in `{0, 1} ∪ [b_base, ∞)`, all
/// strictly outside the c-block `[nk, nk+n)` (`c_base = nk`).
proof fn lemma_a_words_img_no_c(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < n + 4,
    ensures
        no_c_word(g_m(mm).num_generators, n, a_words(mm, n)[i]),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                          // nk = 4 + |quads| ≥ 4
    let aw = a_words(mm, n);
    let awf = a_words_F(mm, n);
    let head = seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(d_idx(nk, n))]];
    let tail = Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
    assert(awf == head + tail);
    assert(awf.len() == n + 3);
    assert(aw == awf.push(seq![Symbol::Gen(p_idx(nk, n))]));

    if i == n + 3 {
        assert(aw[i] == seq![Symbol::Gen(p_idx(nk, n))]);
        assert(p_idx(nk, n) == nk + 2 * n + 1);            // ≥ nk + n
        lemma_no_c_single_gen(nk, n, p_idx(nk, n));
    } else {
        assert(aw[i] == awf[i]);                           // push only adds index n+3
        if i == 0 {
            assert(awf[i] == head[0]);
            assert(aw[i] == seq![Symbol::Gen(0)]);
            lemma_no_c_single_gen(nk, n, 0);               // 0 < nk
        } else if i == 1 {
            assert(awf[i] == head[1]);
            assert(aw[i] == seq![Symbol::Gen(1)]);
            lemma_no_c_single_gen(nk, n, 1);               // 1 < nk
        } else if i == 2 {
            assert(awf[i] == head[2]);
            assert(aw[i] == seq![Symbol::Gen(d_idx(nk, n))]);
            assert(d_idx(nk, n) == nk + 2 * n);            // ≥ nk + n
            lemma_no_c_single_gen(nk, n, d_idx(nk, n));
        } else {
            assert(awf[i] == tail[i - 3]);
            assert(tail[i - 3] == seq![Symbol::Gen(b_idx(nk, n, ((i - 3) + 1) as nat))]);
            assert(((i - 3) + 1) as nat == (i - 2) as nat);
            assert(aw[i] == seq![Symbol::Gen(b_idx(nk, n, (i - 2) as nat))]);
            assert(b_idx(nk, n, (i - 2) as nat) == nk + n + (i - 3));   // ≥ nk + n
            lemma_no_c_single_gen(nk, n, b_idx(nk, n, (i - 2) as nat));
        }
    }
}

/// `emb(a_words, w)` is c-free for any `w` valid over the `P_A` generators (`n+4`). Each symbol's
/// image is a c-free single generator (`lemma_a_words_img_no_c`); inversion and concatenation
/// preserve c-freeness.
proof fn lemma_emb_a_words_no_c(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, (n + 4) as nat),
    ensures
        no_c_word(g_m(mm).num_generators, n, apply_embedding(a_words(mm, n), w)),
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let aw = a_words(mm, n);
    lemma_a_words_single_gen(mm, n);                       // aw.len() == n + 4
    if w.len() == 0 {
        assert(apply_embedding(aw, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, (n + 4) as nat)) by { assert(w[0] == s); }
        let gi = generator_index(s);
        assert(gi < n + 4);
        lemma_a_words_img_no_c(mm, n, gi as int);          // no_c_word(nk, n, aw[gi])
        assert(no_c_word(nk, n, apply_embedding_symbol(aw, s))) by {
            match s {
                Symbol::Gen(g) => {
                    assert(apply_embedding_symbol(aw, s) == aw[g as int]);
                },
                Symbol::Inv(g) => {
                    assert(apply_embedding_symbol(aw, s) == inverse_word(aw[g as int]));
                    lemma_no_c_inverse(nk, n, aw[g as int]);
                },
            }
        }
        assert(word_valid(rest, (n + 4) as nat)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(#[trigger] rest[k], (n + 4) as nat) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_emb_a_words_no_c(mm, n, rest);
        assert(apply_embedding(aw, w)
            =~= concat(apply_embedding_symbol(aw, s), apply_embedding(aw, rest)));
        lemma_no_c_concat(nk, n, apply_embedding_symbol(aw, s), apply_embedding(aw, rest));
    }
}

// ----------------------------------------------------------------------------
// CS-4c headline — the forward von-Dyck wiring
// ----------------------------------------------------------------------------

/// **CS-4c FORWARD (`a ⟹ b`).** If `emb(a_col, w) ≡_{h2_pred} ε` then `emb(b_col, w) ≡_{h2_pred} ε`
/// (the `⟹` half of the a_i association iso `(★)` over the predicate base). Chains CS-4b compactness
/// → slice normalization → `lemma_map_a_forward` (`map_a` faithful) → the `b_words` von-Dyck push
/// (`lemma_emb_respects_source_equiv_pred` with the CS-4a relator-triviality).
pub proof fn lemma_cs4c_forward(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat, w: Word,
)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        1 <= l <= 2 * n,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        word_valid(w, (n + 4) as nat),
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(a_words(mm, n), w), empty_word()),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(b_words(mm, n, m, l), w), empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let aw = a_words(mm, n);
    let bw = b_words(mm, n, m, l);
    let pw = apply_embedding(aw, w);

    // (a) pw is c-free and valid over h2_num_gens.
    lemma_emb_a_words_no_c(mm, n, w);                      // no_c_word(nk, n, pw)
    lemma_a_words_single_gen(mm, n);                       // aw.len() == n + 4
    assert forall|i: int| 0 <= i < aw.len()
        implies word_valid(#[trigger] aw[i], h2_num_gens(nk, n)) by {
        lemma_a_words_img_valid(mm, n, i);
    }
    assert(word_valid(w, aw.len()));                       // aw.len() == n + 4
    lemma_apply_embedding_valid(aw, w, h2_num_gens(nk, n));   // word_valid(pw, h2_num_gens)

    // (b) compactness: a finite slice `alphas` with pw ≡_{h2_II(alphas)} ε.
    lemma_cs4b_compactness(mm, n, m, is_S, pw);
    let alphas = choose|a: Seq<nat>|
        (forall|i: int| 0 <= i < a.len() ==> numbers_word(n, m, #[trigger] a[i]))
        && equiv_in_presentation(h2_II(mm, n, m, a), pw, empty_word());
    assert(forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]));
    assert(equiv_in_presentation(h2_II(mm, n, m, alphas), pw, empty_word()));

    // (c) normalize: no-dup, ∌0, number-words.
    lemma_h2_II_normalize_equiv(mm, n, m, alphas, pw, empty_word());
    let norm = normalize_alphas(alphas);

    // (d) map_a forward: w ≡_{P_A = pa_data(betas(norm))} ε.
    lemma_map_a_forward(mm, n, m, norm, w);
    let bet = betas(norm);
    let pd = pa_data(n, m, bet);
    let src = hnn_presentation(pd);
    assert(equiv_in_presentation(src, w, empty_word()));

    // (e) push through the `b_words` homomorphism into `h2_pred` (von-Dyck-b).
    lemma_betas_index(norm);
    assert forall|i: int| 0 <= i < bet.len() implies numbers_word(n, m, #[trigger] bet[i]) by {
        if i == 0 { assert(bet[0] == 0); } else { assert(bet[i] == norm[i - 1]); }
    }
    lemma_pa_data_shape(n, m, bet);                        // base gens n+3, |assocs| == |bet|
    lemma_pa_data_valid(n, m, bet);
    lemma_hnn_presentation_valid(pd);                      // presentation_valid(src)
    assert(src.relators =~= hnn_relators(pd)) by {
        assert(pd.base.relators == Seq::<Word>::empty());
    }
    assert(src.num_generators == n + 4);
    assert(src.relators.len() == bet.len());

    // b_words images valid over h2_num_gens (= h2_pred.num_generators).
    lemma_phi_assoc_len(nk, n, m, l);
    lemma_phi_assoc_valid(nk, n, m, l, h2_num_gens(nk, n));
    assert(bw.len() == n + 4);
    assert forall|i: int| 0 <= i < bw.len()
        implies word_valid(#[trigger] bw[i], h2_num_gens(nk, n)) by {
        assert(bw[i] == phi_assoc(nk, n, m, l)[i].1);      // fires assocs_valid
    }

    // each `src` relator maps to ε in `h2_pred` (CS-4a b-von-Dyck).
    assert forall|j: int| 0 <= j < src.relators.len() implies
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(bw, #[trigger] src.relators[j]), empty_word()) by {
        assert(src.relators[j] == hnn_relators(pd)[j]);
        assert(hnn_relators(pd)[j] == hnn_relator(pd, j));
        lemma_b_col_relator_trivial_pred(mm, n, m, is_S, l, bet, j);
    }

    lemma_h2_pred_valid(mm, n, m, is_S);
    assert(h2_pred(mm, n, m, is_S).num_generators == h2_num_gens(nk, n));
    assert(word_valid(empty_word(), src.num_generators));
    lemma_emb_respects_source_equiv_pred(src, h2_pred(mm, n, m, is_S), bw, w, empty_word());

    assert(apply_embedding(bw, empty_word()) =~= empty_word());
}

// ============================================================================
// CS-4d — the von-Dyck BACKWARD wiring (`b ⟹ a`) — the previously-blocked half
// ============================================================================
//
// `docs/cohen-cs4d-blueprint.md`. The `⟸` half of the a_i iso `(★)`:
//
//   emb(b_col, w) ≡_{h2_pred} ε   ⟹   emb(a_col, w) ≡_{h2_pred} ε
//
// Chained:
//   (M1) factor `emb(b_col, w) = emb(a_col, pw)`, `pw = emb(φ_l_src, w)` (lemma_mapb_factor_source);
//   (a–c) CS-4b compactness + normalize on `emb(a_col, pw)` (mirrors CS-4c forward, applied to `pw`);
//   (d) `lemma_map_a_forward` on `pw`: `pw ≡_{pa_data(betas(norm))} ε`;
//   (e–g) **M2_general** over the superset slice `S = betas(norm)` (the σ-recognition engine):
//         `w ≡_{pa_data(bet_of(S))} ε`.  The `iso(pa_data(S))` precondition is discharged by
//         `lemma_pa_data_isomorphic` since `S = betas(norm)` is betas-form (blueprint: §4.1 not needed);
//   (h) the a_col von-Dyck push (`lemma_emb_respects_source_equiv_pred` + CS-4a a-relator-triviality).

/// **CS-4d BACKWARD (`b ⟹ a`).** If `emb(a_col=a_words, w)`'s sibling `emb(b_col=b_words, w)` is
/// trivial in `h2_pred`, then `emb(a_col, w)` is too — closing the a_i association iso `(★)` over the
/// predicate base.  The piece that was blocked on the 0-head / σ-preimage design question, resolved by
/// recognizing the σ-restriction inside `M2_general` rather than at the slice level.
pub proof fn lemma_cs4d_backward(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat, w: Word,
)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        1 <= l <= 2 * n,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        word_valid(w, (n + 4) as nat),
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(b_words(mm, n, m, l), w), empty_word()),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(a_words(mm, n), w), empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let aw = a_words(mm, n);
    let bw = b_words(mm, n, m, l);
    let phi = phi_l_src(n, m, l);
    let pw = apply_embedding(phi, w);
    let apw = apply_embedding(aw, pw);

    // (M1) emb(b_words, w) = emb(a_words, pw) ⟹ emb(a_words, pw) ≡_{h2_pred} ε.
    lemma_mapb_factor_source(mm, n, m, l, w);
    assert(apply_embedding(bw, w) =~= apw);
    assert(equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), apw, empty_word()));

    // pw valid over n+4.
    lemma_phi_l_src_valid(n, m, l);
    lemma_phi_l_src_len(n, m, l);
    lemma_apply_embedding_valid(phi, w, (n + 4) as nat);

    // (a) apw is c-free and valid over h2_num_gens.
    lemma_emb_a_words_no_c(mm, n, pw);                     // no_c_word(nk, n, apw)
    lemma_a_words_single_gen(mm, n);                       // aw.len() == n + 4
    assert forall|i: int| 0 <= i < aw.len()
        implies word_valid(#[trigger] aw[i], h2_num_gens(nk, n)) by {
        lemma_a_words_img_valid(mm, n, i);
    }
    assert(word_valid(pw, aw.len()));                      // aw.len() == n + 4
    lemma_apply_embedding_valid(aw, pw, h2_num_gens(nk, n));  // word_valid(apw, h2_num_gens)

    // (b) compactness: a finite slice `alphas` with apw ≡_{h2_II(alphas)} ε.
    lemma_cs4b_compactness(mm, n, m, is_S, apw);
    let alphas = choose|a: Seq<nat>|
        (forall|i: int| 0 <= i < a.len() ==> numbers_word(n, m, #[trigger] a[i]))
        && equiv_in_presentation(h2_II(mm, n, m, a), apw, empty_word());
    assert(forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]));
    assert(equiv_in_presentation(h2_II(mm, n, m, alphas), apw, empty_word()));

    // (c) normalize: no-dup, ∌0, number-words.
    lemma_h2_II_normalize_equiv(mm, n, m, alphas, apw, empty_word());
    let norm = normalize_alphas(alphas);

    // (d) map_a forward on pw: pw ≡_{P_A = pa_data(betas(norm))} ε.
    lemma_map_a_forward(mm, n, m, norm, pw);
    let bigS = betas(norm);
    assert(equiv_in_presentation(hnn_presentation(pa_data(n, m, bigS)), pw, empty_word()));

    // (e) bigS = betas(norm) is no-dup + number-words (the M2_general superset slice S).
    lemma_betas_index(norm);
    assert forall|i: int| 0 <= i < bigS.len() implies numbers_word(n, m, #[trigger] bigS[i]) by {
        if i == 0 { assert(bigS[0] == 0); } else { assert(bigS[i] == norm[i - 1]); }
    }
    assert(bigS.no_duplicates()) by {
        assert forall|i: int, j: int|
            0 <= i < bigS.len() && 0 <= j < bigS.len() && i != j implies bigS[i] != bigS[j] by {
            if i == 0 {
                assert(bigS[j] == norm[j - 1]);
                assert(norm.contains(norm[j - 1]));
            } else if j == 0 {
                assert(bigS[i] == norm[i - 1]);
                assert(norm.contains(norm[i - 1]));
            } else {
                assert(bigS[i] == norm[i - 1] && bigS[j] == norm[j - 1]);
            }
        }
    }

    // (f) iso(pa_data(bigS)) — bigS = betas(norm) is betas-form (§4.1 not needed).
    lemma_pa_data_isomorphic(mm, n, m, norm);             // hnn_associations_isomorphic(pa_data(betas(norm)))

    // (g) M2_general: w ≡_{pa_data(bet_of(bigS))} ε.
    lemma_mapb_M2_general(mm, n, m, l, bigS, w);
    let bet = bet_of(bigS, m, l);
    let pd = pa_data(n, m, bet);
    let src = hnn_presentation(pd);
    assert(equiv_in_presentation(src, w, empty_word()));

    // (h) a_col von-Dyck push: w ≡_{pa_data(bet)} ε ⟹ emb(a_words, w) ≡_{h2_pred} ε.
    lemma_bet_of_number_words(bigS, n, m, l);             // bet number-words
    lemma_bet_of_no_dup(bigS, m, l);
    lemma_pa_data_shape(n, m, bet);
    lemma_pa_data_valid(n, m, bet);
    lemma_hnn_presentation_valid(pd);
    assert(src.relators =~= hnn_relators(pd)) by {
        assert(pd.base.relators == Seq::<Word>::empty());
    }
    assert(src.num_generators == n + 4);
    assert(src.relators.len() == bet.len());

    // each src relator maps to ε in h2_pred (CS-4a a-von-Dyck).
    assert forall|j: int| 0 <= j < src.relators.len() implies
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(aw, #[trigger] src.relators[j]), empty_word()) by {
        assert(src.relators[j] == hnn_relators(pd)[j]);
        assert(hnn_relators(pd)[j] == hnn_relator(pd, j));
        lemma_a_col_relator_trivial_pred(mm, n, m, is_S, bet, j);
    }

    lemma_h2_pred_valid(mm, n, m, is_S);
    assert(h2_pred(mm, n, m, is_S).num_generators == h2_num_gens(nk, n));
    assert(word_valid(empty_word(), src.num_generators));
    lemma_emb_respects_source_equiv_pred(src, h2_pred(mm, n, m, is_S), aw, w, empty_word());
    assert(apply_embedding(aw, empty_word()) =~= empty_word());
}

} // verus!
