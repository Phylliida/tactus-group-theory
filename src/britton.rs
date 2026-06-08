use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;

verus! {

//  ============================================================
//  Britton's Lemma (HNN Injectivity)
//  ============================================================
//
//  Britton's Lemma is the fundamental injectivity theorem for HNN extensions:
//
//    If w is a word using only base generators, and w ≡ ε in the HNN
//    extension G*, then w ≡ ε in the base group G.
//
//  Equivalently: the natural inclusion G → G* is injective.
//
//  This is the most technically demanding single theorem in combinatorial
//  group theory. The full proof requires analyzing derivation sequences
//  and showing that stable letters can always be eliminated from
//  derivations between base words.

//  ============================================================
//  Stable letter analysis
//  ============================================================

///  Count the number of stable letter symbols in a word.
///  Counts both Gen(n) and Inv(n) where n = data.base.num_generators.
pub open spec fn stable_letter_count(w: Word, n: nat) -> nat
    decreases w.len(),
{
    if w.len() == 0 {
        0
    } else {
        let rest_count = stable_letter_count(w.drop_first(), n);
        if generator_index(w.first()) == n {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

///  A word is a "base word" if it contains no stable letters.
pub open spec fn is_base_word(w: Word, n: nat) -> bool {
    stable_letter_count(w, n) == 0
}

///  A word using only base generators (word_valid for base) is a base word.
pub proof fn lemma_base_word_characterization(w: Word, n: nat)
    requires
        word_valid(w, n),
    ensures
        is_base_word(w, n),
    decreases w.len(),
{
    if w.len() > 0 {
        let rest = w.drop_first();
        assert(word_valid(rest, n)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(#[trigger] rest[i], n)
            by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_base_word_characterization(rest, n);
        assert(symbol_valid(w.first(), n));
        assert(generator_index(w.first()) < n);
    }
}

///  A base word that is word_valid for n+1 generators is word_valid for n generators.
///  (Combines: no stable letters at index n + all indices < n+1 → all indices < n.)
pub proof fn lemma_base_word_valid_downgrade(w: Word, n: nat)
    requires
        is_base_word(w, n),
        word_valid(w, n + 1),
    ensures
        word_valid(w, n),
    decreases w.len(),
{
    if w.len() > 0 {
        let rest = w.drop_first();

        //  First symbol has index < n+1 and index != n, so index < n
        assert(symbol_valid(w.first(), n + 1));
        assert(generator_index(w.first()) < n + 1);
        if generator_index(w.first()) == n {
            assert(stable_letter_count(w, n) >= 1);
            assert(false);
        }
        assert(generator_index(w.first()) < n);
        assert(symbol_valid(w.first(), n));

        //  Rest is also base word and valid for n+1
        assert(stable_letter_count(w, n) == stable_letter_count(rest, n));
        assert(is_base_word(rest, n));
        assert(word_valid(rest, n + 1)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(#[trigger] rest[i], n + 1)
            by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_base_word_valid_downgrade(rest, n);

        //  Combine: first symbol valid + rest valid → whole word valid
        assert forall|i: int| 0 <= i < w.len()
            implies symbol_valid(#[trigger] w[i], n)
        by {
            if i == 0 {
            } else {
                assert(w[i] == rest[i - 1]);
            }
        }
    }
}

///  The empty word is a base word.
pub proof fn lemma_empty_is_base_word(n: nat)
    ensures
        is_base_word(empty_word(), n),
{
}

//  ============================================================
//  Stable letter count properties
//  ============================================================

///  stable_letter_count is additive over concatenation.
pub proof fn lemma_stable_letter_count_concat(w1: Word, w2: Word, n: nat)
    ensures
        stable_letter_count(concat(w1, w2), n) ==
            stable_letter_count(w1, n) + stable_letter_count(w2, n),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        lemma_stable_letter_count_concat(w1.drop_first(), w2, n);
    }
}

///  If w[i] has generator_index == n, then stable_letter_count(w, n) >= 1.
pub proof fn lemma_symbol_contributes_to_count(w: Word, n: nat, i: int)
    requires
        0 <= i < w.len(),
        generator_index(w[i]) == n,
    ensures
        stable_letter_count(w, n) >= 1,
    decreases w.len(),
{
    if i == 0 {
        assert(w[0] == w.first());
    } else {
        assert(w.drop_first()[i - 1] == w[i]);
        lemma_symbol_contributes_to_count(w.drop_first(), n, i - 1);
    }
}

///  If stable_letter_count >= 1, there exists a witness position.
pub proof fn lemma_count_gives_witness(w: Word, n: nat)
    requires
        stable_letter_count(w, n) >= 1,
    ensures
        exists|j: int| 0 <= j < w.len() && generator_index(#[trigger] w[j]) == n,
    decreases w.len(),
{
    if generator_index(w.first()) == n {
        assert(w[0 as int] == w.first());
    } else {
        lemma_count_gives_witness(w.drop_first(), n);
        let j = choose|j: int| 0 <= j < w.drop_first().len()
            && generator_index(#[trigger] w.drop_first()[j]) == n;
        assert(w[j + 1] == w.drop_first()[j]);
    }
}

///  inverse_word preserves the existence of stable letters.
pub proof fn lemma_inverse_preserves_stable(w: Word, n: nat)
    requires
        stable_letter_count(w, n) >= 1,
    ensures
        stable_letter_count(inverse_word(w), n) >= 1,
    decreases w.len(),
{
    let rest = w.drop_first();
    let inv_rest = inverse_word(rest);
    let tail = Seq::<Symbol>::new(1, |_i: int| inverse_symbol(w.first()));

    if generator_index(w.first()) == n {
        //  inverse_symbol preserves generator_index
        match w.first() {
            Symbol::Gen(_) => {},
            Symbol::Inv(_) => {},
        }
        assert(tail[0 as int] == inverse_symbol(w.first()));
        lemma_symbol_contributes_to_count(tail, n, 0);
        lemma_stable_letter_count_concat(inv_rest, tail, n);
    } else {
        //  w.first() doesn't contribute, so count(rest, n) >= 1
        lemma_inverse_preserves_stable(rest, n);
        lemma_stable_letter_count_concat(inv_rest, tail, n);
    }
}

///  HNN relators contain stable letters.
pub proof fn lemma_hnn_relator_has_stable(data: HNNData, i: int)
    requires
        0 <= i < data.associations.len(),
    ensures
        stable_letter_count(hnn_relator(data, i), data.base.num_generators) >= 1,
{
    let r = hnn_relator(data, i);
    let n = data.base.num_generators;
    let t_inv_seq = Seq::<Symbol>::new(1, |_j: int| stable_letter_inv(data));
    let (a_i, b_i) = data.associations[i];
    let rest = a_i + Seq::<Symbol>::new(1, |_j: int| stable_letter(data))
        + inverse_word(b_i);
    assert(r =~= t_inv_seq + rest);
    assert(r[0 as int] == stable_letter_inv(data));
    assert(generator_index(stable_letter_inv(data)) == n);
    lemma_symbol_contributes_to_count(r, n, 0);
}

///  get_relator for an HNN relator index has stable letters.
pub proof fn lemma_get_relator_hnn_has_stable(data: HNNData, idx: nat, inverted: bool)
    requires
        idx >= data.base.relators.len(),
        idx < hnn_presentation(data).relators.len(),
    ensures
        stable_letter_count(
            get_relator(hnn_presentation(data), idx, inverted),
            data.base.num_generators,
        ) >= 1,
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    let hnn_idx = (idx - data.base.relators.len()) as int;

    assert(hp.relators[idx as int] == hnn_relators(data)[hnn_idx]);
    assert(hnn_relators(data)[hnn_idx] == hnn_relator(data, hnn_idx));

    lemma_hnn_relator_has_stable(data, hnn_idx);

    if inverted {
        lemma_inverse_preserves_stable(hp.relators[idx as int], n);
    }
}

//  ============================================================
//  T-free step classification
//  ============================================================

///  A derivation step between t-free words in G* is valid in G,
///  and produces the same result.
pub proof fn lemma_t_free_step_is_base_step(
    data: HNNData,
    w: Word,
    step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        is_base_word(w, data.base.num_generators),
        apply_step(hnn_presentation(data), w, step).is_some(),
        is_base_word(
            apply_step(hnn_presentation(data), w, step).unwrap(),
            data.base.num_generators,
        ),
    ensures
        apply_step(data.base, w, step) ==
            apply_step(hnn_presentation(data), w, step),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    let n = bp.num_generators;
    let w_prime = apply_step(hp, w, step).unwrap();

    match step {
        DerivationStep::FreeReduce { position } => {
            //  No presentation dependency
        },
        DerivationStep::FreeExpand { position, symbol } => {
            if generator_index(symbol) == n {
                //  symbol is stable → result has stable letters → contradiction
                let pair = Seq::<Symbol>::new(1, |_i: int| symbol)
                    + Seq::<Symbol>::new(1, |_i: int| inverse_symbol(symbol));
                let left = w.subrange(0, position);
                let right = w.subrange(position, w.len() as int);
                assert(w_prime =~= (left + pair) + right);
                assert(pair[0 as int] == symbol);
                lemma_symbol_contributes_to_count(pair, n, 0);
                lemma_stable_letter_count_concat(left, pair, n);
                lemma_stable_letter_count_concat(left + pair, right, n);
                assert(false);
            }
            assert(symbol_valid(symbol, n));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            if relator_index >= bp.relators.len() {
                let r = get_relator(hp, relator_index, inverted);
                lemma_get_relator_hnn_has_stable(data, relator_index, inverted);
                let left = w.subrange(0, position);
                let right = w.subrange(position, w.len() as int);
                assert(w_prime =~= (left + r) + right);
                lemma_stable_letter_count_concat(left, r, n);
                lemma_stable_letter_count_concat(left + r, right, n);
                assert(false);
            }
            assert(hp.relators[relator_index as int] == bp.relators[relator_index as int]);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            if relator_index >= bp.relators.len() {
                let r = get_relator(hp, relator_index, inverted);
                lemma_get_relator_hnn_has_stable(data, relator_index, inverted);
                lemma_count_gives_witness(r, n);
                let j = choose|j: int| 0 <= j < r.len()
                    && generator_index(#[trigger] r[j]) == n;
                assert(w.subrange(position, position + r.len() as int)[j] == r[j]);
                assert(w[(position + j) as int] == r[j]);
                lemma_symbol_contributes_to_count(w, n, (position + j) as int);
                assert(false);
            }
            assert(hp.relators[relator_index as int] == bp.relators[relator_index as int]);
        },
    }
}

//  ============================================================
//  T-free derivation
//  ============================================================

///  All intermediate words in a derivation are base words.
pub open spec fn all_intermediates_base(
    data: HNNData,
    steps: Seq<DerivationStep>,
    w: Word,
) -> bool
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;
    is_base_word(w, n) &&
    if steps.len() == 0 {
        true
    } else {
        match apply_step(hp, w, steps.first()) {
            Some(next) => all_intermediates_base(data, steps.drop_first(), next),
            None => true,
        }
    }
}

///  A t-free derivation in G* produces the same result in G.
pub proof fn lemma_t_free_derivation_is_base(
    data: HNNData,
    steps: Seq<DerivationStep>,
    w: Word,
)
    requires
        hnn_data_valid(data),
        all_intermediates_base(data, steps, w),
        derivation_produces(hnn_presentation(data), steps, w).is_some(),
    ensures
        derivation_produces(data.base, steps, w) ==
            derivation_produces(hnn_presentation(data), steps, w),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let hp = hnn_presentation(data);
        let n = data.base.num_generators;
        let step = steps.first();
        let w_next = apply_step(hp, w, step).unwrap();

        //  Unfold all_intermediates_base: first level gives is_base_word(w, n)
        //  and all_intermediates_base(data, steps.drop_first(), w_next)
        assert(all_intermediates_base(data, steps.drop_first(), w_next));
        //  Second level gives is_base_word(w_next, n)
        assert(is_base_word(w_next, n));

        lemma_t_free_step_is_base_step(data, w, step);
        lemma_t_free_derivation_is_base(data, steps.drop_first(), w_next);
    }
}

//  ============================================================
//  Britton's Lemma — Axiom
//  ============================================================
//
//  The full algebraic proof of Britton's Lemma involves:
//  1. Defining the "t-length" of intermediate words in a derivation
//  2. Showing each step changes t-count by at most 2
//  3. A "peak analysis" argument: if a derivation introduces then
//     removes stable letters, the segment can be simplified
//  4. Induction on the total t-exposure of the derivation
//
//  This proof is deferred. The axiom is strictly weaker than
//  axiom_higman_embedding and is a standard theorem in
//  combinatorial group theory.

} //  verus!
