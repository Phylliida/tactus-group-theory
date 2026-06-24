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
use crate::base_swap::{lemma_add_relators_relators, lemma_single_step_equiv};
use crate::machine_group::*;
use crate::layout::*;
use crate::word_numbering::{numbers_word, w_b};
use crate::h1::h1_base;
use crate::h2::{h2_pres, h2_data, td_word, p_assoc, lemma_h2_stable_letter};
use crate::hnn::{hnn_relators, hnn_relator, stable_letter, stable_letter_inv};
use crate::h3_ii::{h2_II, family_II, family_II_relator, family_II_lhs, family_II_rhs};

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

} // verus!
