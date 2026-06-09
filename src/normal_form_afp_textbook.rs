//  Textbook AFP injectivity via reduced sequences (Lyndon-Schupp Ch. IV).
//
//  Phase 1: Definitions only. All spec fns, no proof obligations.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::normal_form_amalgamated::{
    in_left_subgroup, in_right_subgroup,
    same_left_coset, same_right_coset,
    unshift_sym,
    identifications_isomorphic,
};
use crate::benign::*;
use crate::shortlex::*;

verus! {

//  ============================================================
//  Part A: Helpers
//  ============================================================

///  The K-word generators for the left factor (u_i words).
pub open spec fn a_words(data: AmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| data.identifications[i].0)
}

///  The K-word generators for the right factor (v_i words).
pub open spec fn b_words(data: AmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| data.identifications[i].1)
}

///  Number of identification generators.
pub open spec fn k_size(data: AmalgamatedData) -> nat {
    data.identifications.len() as nat
}

//  ============================================================
//  Part B: Shortlex-canonical coset representatives
//  ============================================================

///  Lex rank of a word with explicit base (alphabet size).
///  For word_valid(w, n): each symbol_to_column < 2*n.
///  With base = 2*n: this is a standard base-(2n) representation, injective on same-length words.
pub open spec fn word_lex_rank(w: Word) -> nat
    decreases w.len(),
{
    if w.len() == 0 { 0 }
    else {
        //  Use the word itself to provide a stable base.
        //  For proper injectivity, use word_lex_rank_base with explicit base.
        crate::todd_coxeter::symbol_to_column(w.first())
            + (2 * w.len() as nat) * word_lex_rank(w.drop_first())
    }
}

///  Lex rank with explicit base for injectivity proof.
pub open spec fn word_lex_rank_base(w: Word, base: nat) -> nat
    decreases w.len(),
{
    if w.len() == 0 { 0 }
    else {
        crate::todd_coxeter::symbol_to_column(w.first())
            + base * word_lex_rank_base(w.drop_first(), base)
    }
}

///  Lex rank with proper base is injective on same-length words.
proof fn lemma_word_lex_rank_base_injective(w1: Word, w2: Word, base: nat)
    requires
        w1.len() == w2.len(),
        word_lex_rank_base(w1, base) == word_lex_rank_base(w2, base),
        //  Each symbol's column < base (ensures proper base-n representation)
        forall|k: int| 0 <= k < w1.len() ==>
            crate::todd_coxeter::symbol_to_column(#[trigger] w1[k]) < base,
        forall|k: int| 0 <= k < w2.len() ==>
            crate::todd_coxeter::symbol_to_column(#[trigger] w2[k]) < base,
        base > 0,
    ensures
        w1 =~= w2,
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(w2.len() == 0);
        assert forall|k: int| 0 <= k < w1.len() implies w1[k] == w2[k] by {}
        return;
    } else {
        let col1 = crate::todd_coxeter::symbol_to_column(w1.first());
        let col2 = crate::todd_coxeter::symbol_to_column(w2.first());
        let rest_rank1 = word_lex_rank_base(w1.drop_first(), base);
        let rest_rank2 = word_lex_rank_base(w2.drop_first(), base);
        //  col1 + base * rest_rank1 == col2 + base * rest_rank2
        //  col1 < base, col2 < base. So col1 == (total) % base and rest_rank1 == (total) / base.
        //  col1 == col2 (mod base) and rest_rank1 == rest_rank2 (div base).
        assert(col1 < base);
        assert(col2 < base);
        //  col1 + base * rest1 == col2 + base * rest2
        //  → col1 - col2 == base * (rest2 - rest1)
        //  |col1 - col2| < base, |base * (rest2 - rest1)| is 0 or >= base
        //  So col1 == col2 and rest1 == rest2.
        assert(col1 == col2) by (nonlinear_arith)
            requires col1 + base * rest_rank1 == col2 + base * rest_rank2,
                     col1 < base, col2 < base;
        //  col1 == col2, so base * rest1 == base * rest2, so rest1 == rest2 (since base > 0)
        assert(base * rest_rank1 == base * rest_rank2) by (nonlinear_arith)
            requires col1 + base * rest_rank1 == col2 + base * rest_rank2,
                     col1 == col2;
        assert(rest_rank1 == rest_rank2) by (nonlinear_arith)
            requires base * rest_rank1 == base * rest_rank2, base > 0;
        //  col1 == col2 → w1.first() == w2.first() (symbol_to_column is injective on symbols)
        //  rest_rank1 == rest_rank2 → w1.rest =~= w2.rest (by IH)
        assert forall|k: int| 0 <= k < w1.drop_first().len()
            implies crate::todd_coxeter::symbol_to_column(#[trigger] w1.drop_first()[k]) < base
        by { assert(w1.drop_first()[k] == w1[k + 1]); }
        assert forall|k: int| 0 <= k < w2.drop_first().len()
            implies crate::todd_coxeter::symbol_to_column(#[trigger] w2.drop_first()[k]) < base
        by { assert(w2.drop_first()[k] == w2[k + 1]); }
        lemma_word_lex_rank_base_injective(w1.drop_first(), w2.drop_first(), base);
        //  w1.first() == w2.first(): from col1 == col2.
        //  symbol_to_column is injective: Gen(i) → 2*i, Inv(i) → 2*i+1. Different symbols → different columns.
        match w1.first() {
            Symbol::Gen(i1) => match w2.first() {
                Symbol::Gen(i2) => { assert(2 * i1 == 2 * i2); }
                Symbol::Inv(i2) => { assert(2 * i1 == 2 * i2 + 1); } //  impossible since even ≠ odd
            }
            Symbol::Inv(i1) => match w2.first() {
                Symbol::Gen(i2) => { assert(2 * i1 + 1 == 2 * i2); } //  impossible
                Symbol::Inv(i2) => { assert(2 * i1 + 1 == 2 * i2 + 1); }
            }
        }
        //  w1.first() == w2.first() and w1.drop_first() =~= w2.drop_first() → w1 =~= w2
        assert forall|k: int| 0 <= k < w1.len() implies w1[k] == w2[k] by {
            if k == 0 {} else { assert(w1[k] == w1.drop_first()[k - 1]); assert(w2[k] == w2.drop_first()[k - 1]); }
        }
    }
}

///  Does the left A-coset of g contain a valid word of length l?
pub open spec fn has_left_coset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l
}

///  The lex base for a given alphabet: 2*n + 1 ensures injectivity.
pub open spec fn lex_base(data: AmalgamatedData) -> nat {
    2 * data.p1.num_generators + 1
}

///  Does the coset contain a valid word of length l and lex rank r?
pub open spec fn has_left_coset_word_of_len_rank(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r
}

///  No coset word exists below length l (named recursive, avoids lambda issues).
pub open spec fn no_shorter_coset_word(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool
    decreases l,
{
    if l == 0 { true }
    else { !has_left_coset_word_of_len(data, g, (l - 1) as nat)
           && no_shorter_coset_word(data, g, (l - 1) as nat) }
}

///  l is the minimum coset length: has a word AND nothing shorter.
pub open spec fn is_min_coset_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    has_left_coset_word_of_len(data, g, l) && no_shorter_coset_word(data, g, l)
}

///  Minimum length of any valid word in g's left A-coset.
pub open spec fn left_min_coset_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] is_min_coset_len(data, g, l)
}

///  No coset word exists at length l with lex rank below r (named recursive).
pub open spec fn no_smaller_coset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_left_coset_word_of_len_rank(data, g, l, (r - 1) as nat)
           && no_smaller_coset_lex(data, g, l, (r - 1) as nat) }
}

///  r is the minimum lex rank at length l.
pub open spec fn is_min_coset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    has_left_coset_word_of_len_rank(data, g, l, r)
    && no_smaller_coset_lex(data, g, l, r)
}

///  Minimum lex rank at the minimum length.
pub open spec fn left_min_coset_lex(data: AmalgamatedData, g: Word) -> nat {
    let l = left_min_coset_len(data, g);
    choose|r: nat| #[trigger] is_min_coset_lex(data, g, l, r)
}

///  Canonical coset representative: the UNIQUE word with min length and min lex rank.
///  Three-step choose enables coset invariance via uniqueness.
pub open spec fn left_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = left_min_coset_len(data, g);
    let r = left_min_coset_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p1.num_generators)
        && same_left_coset(data, g, rep)
        && rep.len() == l
        && word_lex_rank_base(rep, lex_base(data)) == r
}

///  Does a K-word of length l exist that embeds to the target?
pub open spec fn has_left_h_witness_of_len(
    data: AmalgamatedData, target: Word, l: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

///  Min-length K-word witnessing the subgroup decomposition.
pub open spec fn left_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    choose|l: nat| #[trigger] has_left_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_left_h_witness_of_len(data, target, l2), l)
}

///  The lex base for K-words: 2*k + 1 ensures injectivity.
pub open spec fn h_lex_base(data: AmalgamatedData) -> nat {
    2 * k_size(data) + 1
}

///  Does a K-word of length l and lex rank r exist that embeds to the target?
pub open spec fn has_left_h_witness_of_len_rank(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

///  No h-witness exists at length l with lex rank below r (named recursive).
pub open spec fn no_smaller_h_lex(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_left_h_witness_of_len_rank(data, target, l, (r - 1) as nat)
           && no_smaller_h_lex(data, target, l, (r - 1) as nat) }
}

///  r is the minimum h-witness lex rank at length l.
pub open spec fn is_min_h_lex(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    has_left_h_witness_of_len_rank(data, target, l, r)
    && no_smaller_h_lex(data, target, l, r)
}

///  Minimum lex rank among K-words of minimum length.
pub open spec fn left_h_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = left_h_min_len(data, g);
    choose|r: nat| #[trigger] is_min_h_lex(data, target, l, r)
}

///  The subgroup part: canonical (min-length, min-lex) K-word h such that embed_a(h) ≡ inv(rep) * g.
///  Three-step choose enables h-part invariance under G₁-equivalence.
pub open spec fn left_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = left_h_min_len(data, g);
    let r = left_h_min_lex(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

///  Does the right B-coset of g contain a valid word of length l?
pub open spec fn has_right_coset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p2.num_generators)
        && same_right_coset(data, g, w) && w.len() == l
}

///  Minimum length of any valid word in g's right B-coset.
pub open spec fn right_min_coset_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] has_right_coset_word_of_len(data, g, l)
        && no_pred_below(|l2: nat| has_right_coset_word_of_len(data, g, l2), l)
}

///  Canonical right coset representative.
pub open spec fn right_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = right_min_coset_len(data, g);
    choose|rep: Word|
        word_valid(rep, data.p2.num_generators)
        && same_right_coset(data, g, rep)
        && rep.len() == l
}

///  Does a K-word of length l exist for the right decomposition?
pub open spec fn has_right_h_witness_of_len(
    data: AmalgamatedData, target: Word, l: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

///  Min-length K-word for right decomposition.
pub open spec fn right_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = right_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    choose|l: nat| #[trigger] has_right_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_right_h_witness_of_len(data, target, l2), l)
}

///  The subgroup part for G₂: min-length K-word.
pub open spec fn right_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = right_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = right_h_min_len(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

//  ============================================================
//  Part B1c: RIGHT cosets of A in G₁ (textbook Lyndon-Schupp convention)
//  ============================================================
//  The textbook decomposes g = h·c where h ∈ A (on LEFT) and c is a RIGHT
//  coset representative (on RIGHT). This means g·c⁻¹ ∈ A.
//  Using this convention, the action has clean inverse cancellation:
//    s⁻¹ · (embed_a(h') · c') = s⁻¹ · (s · h · c₁) = h · c₁

///  Two G₁-words are in the same RIGHT coset of A: w₁·w₂⁻¹ ∈ A.
pub open spec fn same_a_rcoset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_left_subgroup(data, concat(w1, inverse_word(w2)))
}

///  Does the right A-coset of g contain a valid word of length l?
pub open spec fn has_a_rcoset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_a_rcoset(data, g, w) && w.len() == l
}

///  No right-A-coset word below length l (named recursive).
pub open spec fn no_shorter_a_rcoset_word(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool
    decreases l,
{
    if l == 0 { true }
    else { !has_a_rcoset_word_of_len(data, g, (l - 1) as nat)
           && no_shorter_a_rcoset_word(data, g, (l - 1) as nat) }
}

///  l is the minimum right-A-coset length.
pub open spec fn is_min_a_rcoset_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    has_a_rcoset_word_of_len(data, g, l) && no_shorter_a_rcoset_word(data, g, l)
}

///  Minimum right-A-coset length.
pub open spec fn a_rcoset_min_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] is_min_a_rcoset_len(data, g, l)
}

///  Right-A-coset word of length l and lex rank r.
pub open spec fn has_a_rcoset_word_of_len_rank(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_a_rcoset(data, g, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r
}

///  No right-A-coset word at length l with lex rank below r.
pub open spec fn no_smaller_a_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_a_rcoset_word_of_len_rank(data, g, l, (r - 1) as nat)
           && no_smaller_a_rcoset_lex(data, g, l, (r - 1) as nat) }
}

///  r is the minimum right-A-coset lex rank at length l.
pub open spec fn is_min_a_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    has_a_rcoset_word_of_len_rank(data, g, l, r)
    && no_smaller_a_rcoset_lex(data, g, l, r)
}

///  Minimum lex rank at the minimum length for right A-coset.
pub open spec fn a_rcoset_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let l = a_rcoset_min_len(data, g);
    choose|r: nat| #[trigger] is_min_a_rcoset_lex(data, g, l, r)
}

///  Canonical right A-coset representative (textbook: c in g = h·c).
///  Three-step choose: min length, min lex rank, unique word.
pub open spec fn a_rcoset_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = a_rcoset_min_len(data, g);
    let r = a_rcoset_min_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p1.num_generators)
        && same_a_rcoset(data, g, rep)
        && rep.len() == l
        && word_lex_rank_base(rep, lex_base(data)) == r
}

///  Min-length K-word for right-coset h-part.
///  Target = g · inv(rep) (textbook: h = g · c⁻¹).
///  Reuses has_left_h_witness_of_len since the predicate structure is identical.
pub open spec fn a_rcoset_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    choose|l: nat| #[trigger] has_left_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_left_h_witness_of_len(data, target, l2), l)
}

///  Min lex rank for right-coset h-part.
pub open spec fn a_rcoset_h_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = a_rcoset_h_min_len(data, g);
    choose|r: nat| #[trigger] is_min_h_lex(data, target, l, r)
}

///  The textbook h-part: canonical K-word h such that embed_a(h) ≡ g · c⁻¹.
///  Three-step choose for invariance under G₁-equivalence.
pub open spec fn a_rcoset_h(data: AmalgamatedData, g: Word) -> Word {
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = a_rcoset_h_min_len(data, g);
    let r = a_rcoset_h_min_lex(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

//  ============================================================
//  Part B1d: RIGHT cosets of B in G₂ (textbook convention, mirrors A-cosets)
//  ============================================================

///  Two G₂-words in same RIGHT B-coset: w₁·w₂⁻¹ ∈ B.
pub open spec fn same_b_rcoset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_right_subgroup(data, concat(w1, inverse_word(w2)))
}

pub open spec fn has_b_rcoset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p2.num_generators)
        && same_b_rcoset(data, g, w) && w.len() == l
}

pub open spec fn no_shorter_b_rcoset_word(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool
    decreases l,
{
    if l == 0 { true }
    else { !has_b_rcoset_word_of_len(data, g, (l - 1) as nat)
           && no_shorter_b_rcoset_word(data, g, (l - 1) as nat) }
}

pub open spec fn is_min_b_rcoset_len(data: AmalgamatedData, g: Word, l: nat) -> bool {
    has_b_rcoset_word_of_len(data, g, l) && no_shorter_b_rcoset_word(data, g, l)
}

pub open spec fn b_rcoset_min_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] is_min_b_rcoset_len(data, g, l)
}

pub open spec fn has_b_rcoset_word_of_len_rank(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p2.num_generators)
        && same_b_rcoset(data, g, w) && w.len() == l
        && word_lex_rank_base(w, 2 * data.p2.num_generators + 1) == r
}

pub open spec fn no_smaller_b_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_b_rcoset_word_of_len_rank(data, g, l, (r - 1) as nat)
           && no_smaller_b_rcoset_lex(data, g, l, (r - 1) as nat) }
}

pub open spec fn is_min_b_rcoset_lex(data: AmalgamatedData, g: Word, l: nat, r: nat) -> bool {
    has_b_rcoset_word_of_len_rank(data, g, l, r)
    && no_smaller_b_rcoset_lex(data, g, l, r)
}

pub open spec fn b_rcoset_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let l = b_rcoset_min_len(data, g);
    choose|r: nat| #[trigger] is_min_b_rcoset_lex(data, g, l, r)
}

///  Canonical right B-coset representative (textbook: c in g = h·c for G₂).
pub open spec fn b_rcoset_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = b_rcoset_min_len(data, g);
    let r = b_rcoset_min_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p2.num_generators)
        && same_b_rcoset(data, g, rep)
        && rep.len() == l
        && word_lex_rank_base(rep, 2 * data.p2.num_generators + 1) == r
}

///  G₂ h-witness with lex rank (uses p2/b_words instead of p1/a_words).
pub open spec fn has_right_h_witness_of_len_rank(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

///  No G₂ h-witness at length l with lex rank below r.
pub open spec fn no_smaller_h_lex_g2(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_right_h_witness_of_len_rank(data, target, l, (r - 1) as nat)
           && no_smaller_h_lex_g2(data, target, l, (r - 1) as nat) }
}

pub open spec fn is_min_h_lex_g2(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    has_right_h_witness_of_len_rank(data, target, l, r)
    && no_smaller_h_lex_g2(data, target, l, r)
}

///  Scan for min G₂ h-lex rank.
proof fn lemma_scan_min_h_lex_g2(
    data: AmalgamatedData, target: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_right_h_witness_of_len_rank(data, target, l, bound),
        current <= bound,
        no_smaller_h_lex_g2(data, target, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_h_lex_g2(data, target, l, r),
    decreases bound - current,
{
    if has_right_h_witness_of_len_rank(data, target, l, current) {
        assert(is_min_h_lex_g2(data, target, l, current));
    } else {
        lemma_scan_min_h_lex_g2(data, target, l, current + 1, bound);
    }
}

///  Right B-coset h-part: target = g · inv(rep).
pub open spec fn b_rcoset_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    choose|l: nat| #[trigger] has_right_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_right_h_witness_of_len(data, target, l2), l)
}

pub open spec fn b_rcoset_h_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = b_rcoset_h_min_len(data, g);
    choose|r: nat| #[trigger] is_min_h_lex_g2(data, target, l, r)
}

///  The textbook h-part for G₂: canonical K-word h such that embed_b(h) ≡ g · c⁻¹.
pub open spec fn b_rcoset_h(data: AmalgamatedData, g: Word) -> Word {
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = b_rcoset_h_min_len(data, g);
    let r = b_rcoset_h_min_lex(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

//  ============================================================
//  Part B2: Well-ordering and transversal existence
//  ============================================================

///  No value less than m satisfies p (recursive, avoids quantifier trigger issues).
pub open spec fn no_pred_below(p: spec_fn(nat) -> bool, m: nat) -> bool
    decreases m,
{
    if m == 0 { true }
    else { !p((m - 1) as nat) && no_pred_below(p, (m - 1) as nat) }
}

///  m is the minimum of predicate p.
pub open spec fn is_nat_min(p: spec_fn(nat) -> bool, m: nat) -> bool {
    p(m) && no_pred_below(p, m)
}

///  Well-ordering: scan from `current` to `bound` to find the minimum of p.
proof fn lemma_nat_scan_for_min(p: spec_fn(nat) -> bool, current: nat, bound: nat)
    requires
        p(bound),
        current <= bound,
        no_pred_below(p, current),
    ensures
        exists|m: nat| current <= m && m <= bound && #[trigger] is_nat_min(p, m),
    decreases bound - current,
{
    if p(current) {
        assert(is_nat_min(p, current));
    } else {
        //  !p(current) && no_pred_below(p, current) => no_pred_below(p, current + 1)
        lemma_nat_scan_for_min(p, current + 1, bound);
    }
}

///  Well-ordering principle for nats: any inhabited predicate has a minimum.
pub proof fn lemma_nat_well_ordering(p: spec_fn(nat) -> bool, bound: nat)
    requires
        p(bound),
    ensures
        exists|m: nat| m <= bound && #[trigger] is_nat_min(p, m),
{
    //  no_pred_below(p, 0) is trivially true (base case of recursion)
    lemma_nat_scan_for_min(p, 0, bound);
}

///  The generated subgroup is closed under equivalence.
pub proof fn lemma_in_subgroup_equiv(
    p: Presentation, gens: Seq<Word>, w1: Word, w2: Word,
)
    requires
        in_generated_subgroup(p, gens, w1),
        equiv_in_presentation(p, w1, w2),
    ensures
        in_generated_subgroup(p, gens, w2),
{
    //  w1 is in subgroup: exists factors with concat_all(factors) ≡ w1
    //  w1 ≡ w2, so by transitivity: concat_all(factors) ≡ w2
    let factors: Seq<Word> = choose|factors: Seq<Word>|
        #[trigger] factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), w1);
    crate::presentation::lemma_equiv_transitive(
        p, concat_all(factors), w1, w2);
}

///  The left coset of g contains g itself (reflexivity).
proof fn lemma_same_left_coset_reflexive(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_left_coset(data, g, g),
{
    let inv_g = inverse_word(g);
    let product = concat(inv_g, g);
    let p1 = data.p1;
    let n1 = p1.num_generators;
    //  concat(inv(g), g) ≡ ε in G₁
    crate::presentation_lemmas::lemma_word_inverse_left(p1, g);
    //  ε is in the generated subgroup
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    //  We need: in_generated_subgroup(p1, a_words, product)
    //  = in_generated_subgroup(p1, a_words, concat(inv(g), g))
    //  From: ε ≡ product, and ε is in the subgroup
    //  Need symmetry: product ≡ ε => ε ≡ product (for equiv closure)
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g, n1);
    crate::word::lemma_concat_word_valid(inv_g, g, n1);
    //  product is word_valid
    //  Now get: equiv(ε, product) from equiv(product, ε) + symmetry
    //  Actually equiv(product, ε) is what lemma_word_inverse_left gives.
    //  For subgroup closure we need: in_subgroup(ε) && equiv(ε, product) => in_subgroup(product)
    //  lemma_equiv_symmetric gives equiv(ε, product) from equiv(product, ε)
    crate::presentation::lemma_equiv_symmetric(p1, product, empty_word());
    lemma_in_subgroup_equiv(p1, a_words(data), empty_word(), product);
}

//  ============================================================
//  Part C: Syllable type and reduced state
//  ============================================================

///  A syllable: a non-trivial coset representative from one factor.
pub struct Syllable {
    pub is_left: bool,
    pub rep: Word,
}

///  Well-formed reduced state.
pub open spec fn state_valid(data: AmalgamatedData, h: Word, syllables: Seq<Syllable>) -> bool {
    let k = k_size(data);
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;

    &&& word_valid(h, k)
    &&& (forall|i: int| 0 <= i < syllables.len() - 1 ==>
        (#[trigger] syllables[i]).is_left != (#[trigger] syllables[i + 1]).is_left)
    &&& (forall|i: int| 0 <= i < syllables.len() ==> ({
        let syl = #[trigger] syllables[i];
        if syl.is_left {
            word_valid(syl.rep, n1) && !(syl.rep =~= empty_word())
            && !in_left_subgroup(data, syl.rep)
        } else {
            word_valid(syl.rep, n2) && !(syl.rep =~= empty_word())
            && !in_right_subgroup(data, syl.rep)
        }
    }))
}

//  ============================================================
//  Part D: Single-symbol action
//  ============================================================

///  Apply a single G₁ symbol to the state (textbook Lyndon-Schupp Ch. IV).
///  product = s · embed_a(h) in G₁.
///  RIGHT coset decomposition: product ≡ embed_a(new_h) · new_rep (h on LEFT, rep on RIGHT).
///  This gives clean inverse cancellation: s⁻¹ · embed_a(h') · rep' = s⁻¹ · product.
pub open spec fn act_left_sym(
    data: AmalgamatedData,
    s: Symbol,  //  a G₁ symbol (gen_index < n1)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
    let new_h = a_rcoset_h(data, product);
    let new_rep = a_rcoset_rep(data, product);

    if new_rep =~= empty_word() {
        //  Product is in the subgroup
        (new_h, syllables)
    } else if syllables.len() == 0 || !syllables.first().is_left {
        //  Prepend new left syllable (different factor or empty)
        (new_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: new_rep }) + syllables)
    } else {
        //  Merge (textbook): compute s·h·u₁ and decompose once with RIGHT cosets.
        let full_product = concat(product, syllables.first().rep);
        let combined_h = a_rcoset_h(data, full_product);
        let merged_rep = a_rcoset_rep(data, full_product);

        if merged_rep =~= empty_word() {
            //  Merge absorbed into subgroup
            (combined_h, syllables.drop_first())
        } else {
            //  Replace first syllable
            (combined_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syllables.drop_first())
        }
    }
}

///  Apply a single G₂ symbol to the state (textbook, RIGHT B-coset decomposition).
///  Mirrors act_left_sym with b_rcoset_h/b_rcoset_rep instead of a_rcoset_h/a_rcoset_rep.
pub open spec fn act_right_sym(
    data: AmalgamatedData,
    s: Symbol,  //  a G₂ symbol (local, already unshifted)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let new_h = b_rcoset_h(data, product);
    let new_rep = b_rcoset_rep(data, product);

    if new_rep =~= empty_word() {
        (new_h, syllables)
    } else if syllables.len() == 0 || syllables.first().is_left {
        (new_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: new_rep }) + syllables)
    } else {
        //  Merge (textbook): compute g·h·u₁ and decompose once with RIGHT B-cosets.
        let full_product = concat(product, syllables.first().rep);
        let combined_h = b_rcoset_h(data, full_product);
        let merged_rep = b_rcoset_rep(data, full_product);

        if merged_rep =~= empty_word() {
            (combined_h, syllables.drop_first())
        } else {
            (combined_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syllables.drop_first())
        }
    }
}

///  Apply an AFP symbol to the state. Dispatches to left or right.
pub open spec fn act_sym(
    data: AmalgamatedData,
    s: Symbol,  //  AFP symbol (gen_index < n1+n2)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let n1 = data.p1.num_generators;
    if generator_index(s) < n1 {
        act_left_sym(data, s, h, syllables)
    } else {
        act_right_sym(data, unshift_sym(s, n1), h, syllables)
    }
}

///  Apply an AFP word to the state (left-to-right, one symbol at a time).
///  Apply an AFP word to the state (right-to-left, textbook LEFT action convention).
///  For a left action φ: G → Perm(S), φ(g₁·g₂) = φ(g₁) ∘ φ(g₂).
///  Processing right-to-left: last symbol first → gives φ(s₁·...·sₙ) = φ(s₁) ∘ ... ∘ φ(sₙ).
pub open spec fn act_word(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>)
    decreases w.len(),
{
    if w.len() == 0 {
        (h, syllables)
    } else {
        let (new_h, new_syls) = act_sym(data, w.last(), h, syllables);
        act_word(data, w.drop_last(), new_h, new_syls)
    }
}

//  ============================================================
//  Part E: Composition lemma
//  ============================================================

///  act_word(concat(w1, w2), h, syls) == act_word(w2, act_word(w1, h, syls)).
///  This is the fundamental composition property.
///  Composition: act_word(w1·w2, h, syls) = act_word(w1, act_word(w2, h, syls)).
///  With right-to-left processing: w2 is processed first, then w1 (textbook left action).
pub proof fn lemma_act_word_concat(
    data: AmalgamatedData,
    w1: Word, w2: Word,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, concat(w1, w2), h, syllables)
            == act_word(data, w1,
                act_word(data, w2, h, syllables).0,
                act_word(data, w2, h, syllables).1),
    decreases w2.len(),
{
    if w2.len() == 0 {
        //  concat(w1, ε) =~= w1 and act_word(ε, h, syls) = (h, syls)
        assert(concat(w1, w2) =~= w1) by {
            assert(w2.len() == 0);
            assert(concat(w1, w2).len() == w1.len());
            assert forall|k: int| 0 <= k < w1.len()
                implies concat(w1, w2)[k] == w1[k] by {}
        }
    } else {
        //  concat(w1, w2).last() == w2.last()
        //  concat(w1, w2).drop_last() =~= concat(w1, w2.drop_last())
        assert(concat(w1, w2).last() == w2.last()) by {
            let cw = concat(w1, w2);
            assert(cw.len() == w1.len() + w2.len());
            assert(cw[cw.len() - 1] == w2[w2.len() - 1]);
        }
        assert(concat(w1, w2).drop_last() =~= concat(w1, w2.drop_last())) by {
            let cw = concat(w1, w2);
            let rest = concat(w1, w2.drop_last());
            assert(cw.drop_last().len() == rest.len());
            assert forall|k: int| 0 <= k < rest.len()
                implies cw.drop_last()[k] == rest[k]
            by {
                if k < w1.len() as int {
                    assert(cw[k] == w1[k]);
                    assert(rest[k] == w1[k]);
                } else {
                    assert(cw[k] == w2[(k - w1.len() as int)]);
                    assert(rest[k] == w2.drop_last()[(k - w1.len() as int)]);
                }
            }
        }

        let (mid_h, mid_syls) = act_sym(data, w2.last(), h, syllables);
        //  IH: act_word(concat(w1, w2.drop_last()), mid_h, mid_syls)
        //     = act_word(w1, act_word(w2.drop_last(), mid_h, mid_syls))
        lemma_act_word_concat(data, w1, w2.drop_last(), mid_h, mid_syls);
    }
}

///  act_word of the empty word is the identity.
pub proof fn lemma_act_word_empty(
    data: AmalgamatedData,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, empty_word(), h, syllables) == (h, syllables),
{
    //  Direct from the definition: empty_word().len() == 0
}

//  ============================================================
//  Part F: Well-definedness — derivation steps
//  ============================================================

///  The action respects derivation: if w1 derives to w2 via steps,
///  then act_word(w1, h, syls) == act_word(w2, h, syls).
///
///  This follows from:
///    1. lemma_act_word_concat (composition)
///    2. Per-step: for each step type, the inserted/deleted pair acts trivially
///
///  For now, we state the derivation-level well-definedness and build up to it.
///  The per-step proofs (inverse pairs, relators) are the key lemmas.

///  If two words are equivalent in the AFP, they have the same action on any state.
///  This is the top-level well-definedness theorem.
///
///  Proof chain:
///    equiv_in_presentation(AFP, w1, w2)
///    => there exist derivation steps from w1 to w2
///    => each step preserves the action (by per-step lemmas)
///    => act_word(w1, ...) == act_word(w2, ...)
///
///  This will be proved once all per-step lemmas are in place.
///  For now, we build the infrastructure.

///  A single AFP-symbol word acts the same as act_sym.
pub proof fn lemma_act_word_single(
    data: AmalgamatedData,
    s: Symbol,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, Seq::new(1, |_i: int| s), h, syllables)
            == act_sym(data, s, h, syllables),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.last() == s);
    let rest = w.drop_last();
    assert(rest.len() == 0);
    assert(rest =~= empty_word()) by {
        assert(rest.len() == 0);
        assert(empty_word().len() == 0);
    }
    let (mid_h, mid_syls) = act_sym(data, s, h, syllables);
    //  act_word unfolds (right-to-left): w.len() != 0, so:
    //    act_word(w, h, syls) = act_word(rest, mid_h, mid_syls)
    //  rest =~= ε, so act_word(rest, ...) = (mid_h, mid_syls)
    assert(act_word(data, rest, mid_h, mid_syls) == (mid_h, mid_syls));
    assert(act_word(data, w, h, syllables) == (mid_h, mid_syls));
}

//  ============================================================
//  Part G: Per-step well-definedness helpers
//  ============================================================

///  Two AFP words produce the same action on any state.
pub open spec fn same_action(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    forall|h: Word, syllables: Seq<Syllable>|
        act_word(data, w1, h, syllables) == act_word(data, w2, h, syllables)
}

//  ============================================================
//  Part H: One-shot decomposition and faithfulness
//  ============================================================

///  For a G₁ word g, its one-shot state: decompose g directly into (h, rep).
///  If rep = ε, state is (h, []). If rep ≠ ε, state is (h, [left_syl(rep)]).
///  This is the "answer" the action should give for a G₁-word on the identity state.
pub open spec fn g1_decompose_state(
    data: AmalgamatedData,
    g: Word,
) -> (Word, Seq<Syllable>) {
    let rep = a_rcoset_rep(data, g);
    let h = a_rcoset_h(data, g);
    if rep =~= empty_word() {
        (h, Seq::empty())
    } else {
        (h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep }))
    }
}

///  The identity state decomposes to (ε, []).
pub proof fn lemma_g1_decompose_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        g1_decompose_state(data, empty_word())
            == (empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    reveal(presentation_valid);
    assert(word_valid(e, data.p1.num_generators)) by { assert(e.len() == 0); }

    //  ε is in the subgroup → a_rcoset_rep(ε) =~= ε
    crate::benign::lemma_identity_in_generated_subgroup(data.p1, a_words(data));
    lemma_a_rcoset_in_subgroup(data, e);

    //  a_rcoset_h(ε) =~= ε:
    assert(word_valid(e, k_size(data))) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_refl(data.p1, e);
    let target_e = concat(e, inverse_word(a_rcoset_rep(data, e)));
    //  target =~= ε (since rep =~= ε), so embed_a(ε) = ε ≡ target → witness at length 0
    assert(has_left_h_witness_of_len(data, target_e, 0nat));
    //  min len = 0 by forces_zero
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target_e, l);
    assert(pred_h(0nat));
    assert(no_pred_below(pred_h, 0nat));
    lemma_nat_well_ordering(pred_h, 0nat);
    let hl = a_rcoset_h_min_len(data, e);
    lemma_no_pred_below_forces_zero(pred_h, hl);
    //  hl == 0 → h has length 0
    //  lex at length 0: only ε with rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target_e, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target_e, 0nat, 0nat));
    lemma_scan_min_h_lex(data, target_e, 0, 0, 0);
    //  a_rcoset_h =~= ε (length 0 word)
}

///  If g ≡ ε in G₁, then inv(g) ≡ ε.
proof fn lemma_inv_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        equiv_in_presentation(data.p1, inverse_word(g), empty_word()),
{
    reveal(presentation_valid);
    let p1 = data.p1;
    let inv_g = inverse_word(g);
    //  g * inv(g) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(p1, g);
    //  g ≡ ε, so concat(g, inv(g)) ≡ concat(ε, inv(g)) by left-congruence
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g, empty_word(), inv_g);
    //  concat(ε, inv(g)) =~= inv(g)
    assert(concat(empty_word(), inv_g) =~= inv_g) by {
        let c = concat(empty_word(), inv_g);
        assert(c.len() == inv_g.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_g[k] by {}
    }
    //  We have:
    //    equiv(concat(g, inv_g), ε)                     -- from word_inverse_right
    //    equiv(concat(g, inv_g), concat(ε, inv_g))      -- from equiv_concat_left
    //  So by symmetry + transitivity:
    //    equiv(ε, concat(g, inv_g))
    //    equiv(concat(g, inv_g), concat(ε, inv_g))
    //    => equiv(ε, concat(ε, inv_g))
    crate::word::lemma_inverse_word_valid(g, p1.num_generators);
    crate::word::lemma_concat_word_valid(g, inv_g, p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(p1, concat(g, inv_g), empty_word());
    crate::presentation::lemma_equiv_transitive(
        p1, empty_word(), concat(g, inv_g), concat(empty_word(), inv_g));
    //  Now: equiv(ε, concat(ε, inv_g)) and concat(ε, inv_g) =~= inv_g
    //  So equiv(ε, inv_g), i.e., equiv(inv_g, ε) by symmetry
    crate::word::lemma_inverse_word_valid(g, p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(p1, empty_word(), inv_g);
}

///  If g ≡ ε in G₁, then g is in the left subgroup.
proof fn lemma_equiv_eps_in_subgroup(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        in_left_subgroup(data, g),
{
    reveal(presentation_valid);
    crate::benign::lemma_identity_in_generated_subgroup(data.p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p1, g, empty_word());
    lemma_in_subgroup_equiv(data.p1, a_words(data), empty_word(), g);
}

///  If g ≡ ε in G₁, then same_left_coset(g, ε).
proof fn lemma_same_coset_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        same_left_coset(data, g, empty_word()),
{
    reveal(presentation_valid);
    let inv_g = inverse_word(g);
    crate::word::lemma_inverse_word_valid(g, data.p1.num_generators);
    lemma_inv_equiv_eps(data, g);
    //  inv(g) ≡ ε and word_valid(inv(g), n1)
    lemma_equiv_eps_in_subgroup(data, inv_g);
    //  in_left_subgroup(data, inv(g))

    //  same_left_coset(g, ε) = in_left_subgroup(concat(inv(g), ε))
    //  concat(inv(g), ε) =~= inv(g), so same truth value
    assert(concat(inv_g, empty_word()) =~= inv_g) by {
        let c = concat(inv_g, empty_word());
        assert(c.len() == inv_g.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_g[k] by {}
    }
}

///  If g ≡ ε in G₁, then left_canonical_rep(g) = ε.
///  If g ≡ ε, then left_min_coset_len(g) == 0.
proof fn lemma_left_min_coset_len_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_min_coset_len(data, g) == 0,
{
    let e = empty_word();
    let n1 = data.p1.num_generators;

    //  ε is in g's coset (since g ≡ ε → same_left_coset(g, ε))
    lemma_same_coset_equiv_eps(data, g);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    //  ε has length 0 → has_left_coset_word_of_len(data, g, 0)
    assert(has_left_coset_word_of_len(data, g, 0nat));

    //  is_min_coset_len(data, g, 0) holds: has word at 0 + no_shorter
    assert(no_shorter_coset_word(data, g, 0nat));
    assert(is_min_coset_len(data, g, 0nat));

    let l = left_min_coset_len(data, g);
    //  l satisfies is_min_coset_len(data, g, l). has(g, 0) holds. By no_shorter_implies_ge: 0 >= l.
    lemma_no_shorter_coset_word_implies_ge(data, g, l, 0nat);
}

proof fn lemma_left_rep_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_canonical_rep(data, g) =~= empty_word(),
{
    lemma_left_min_coset_len_equiv_eps(data, g);
    //  left_min_coset_len(g) == 0

    let e = empty_word();
    lemma_same_coset_equiv_eps(data, g);
    assert(word_valid(e, data.p1.num_generators)) by { assert(e.len() == 0); }
    assert(word_lex_rank(e) == 0);

    //  ε has length 0 and lex rank 0, in g's coset
    assert(has_left_coset_word_of_len_rank(data, g, 0nat, 0nat));

    assert(no_smaller_coset_lex(data, g, 0nat, 0nat));
    assert(is_min_coset_lex(data, g, 0nat, 0nat));
    let lex_min = left_min_coset_lex(data, g);
    lemma_no_smaller_coset_lex_implies_ge(data, g, 0nat, lex_min, 0nat);
    //  lex_min == 0

    //  left_canonical_rep: choose with length 0, lex rank 0 → length 0 → it's ε.
}

///  If g ≡ ε in G₁, then left_h_part(g) = ε.
///  If g ≡ ε, then left_h_min_len(g) == 0.
proof fn lemma_left_h_min_len_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_h_min_len(data, g) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    reveal(presentation_valid);

    lemma_left_rep_equiv_eps(data, g);
    let rep = left_canonical_rep(data, g);
    //  rep =~= ε, so target = concat(inv(ε), g) =~= g
    let target = concat(inverse_word(rep), g);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= g) by {
        let c = concat(e, g);
        assert(c.len() == g.len());
        assert forall|j: int| 0 <= j < g.len() implies c[j] == g[j] by {}
    }

    //  ε is a length-0 K-word with embed_a(ε) = ε ≡ g ≡ target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_symmetric(p1, g, e);
    assert(has_left_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));
    let l = left_h_min_len(data, g);
    lemma_no_pred_below_forces_zero(pred, l);
}

proof fn lemma_left_h_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_h_part(data, g) =~= empty_word(),
{
    lemma_left_rep_equiv_eps(data, g);
    lemma_left_h_min_len_equiv_eps(data, g);
    //  left_h_min_len(g) == 0, so left_h_part(g) picks a K-word of length 0 → ε

    //  Show the choose is satisfiable (ε works):
    let e = empty_word();
    let k = k_size(data);
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= g) by {
        let c = concat(e, g);
        assert(c.len() == g.len());
        assert forall|j: int| 0 <= j < g.len() implies c[j] == g[j] by {}
    }
    reveal(presentation_valid);
    crate::presentation::lemma_equiv_symmetric(data.p1, g, e);

    //  Establish h-lex satisfiability: ε has lex rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target, 0nat, 0nat));
    assert(is_min_h_lex(data, target, 0nat, 0nat));
}

///  If g ≡ ε in G₁, then g1_decompose_state gives the identity state.
pub proof fn lemma_g1_decompose_trivial(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        g1_decompose_state(data, g)
            == (empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    let p1 = data.p1;
    reveal(presentation_valid);

    //  g ≡ ε → g is in the subgroup
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(p1, g, e);
    lemma_in_subgroup_equiv(p1, a_words(data), e, g);

    //  g in subgroup → a_rcoset_rep(g) =~= ε
    lemma_a_rcoset_in_subgroup(data, g);

    //  a_rcoset_h(g) =~= ε: target = concat(g, inv(ε)) =~= g ≡ ε
    assert(word_valid(e, k_size(data))) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_symmetric(p1, g, e);
    //  embed_a(ε) = ε ≡ g =~= target → witness at length 0
    let target_g = concat(g, inverse_word(a_rcoset_rep(data, g)));
    assert(has_left_h_witness_of_len(data, target_g, 0nat));
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target_g, l);
    assert(pred_h(0nat));
    assert(no_pred_below(pred_h, 0nat));
    lemma_nat_well_ordering(pred_h, 0nat);
    let hl = a_rcoset_h_min_len(data, g);
    lemma_no_pred_below_forces_zero(pred_h, hl);
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target_g, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target_g, 0nat, 0nat));
    lemma_scan_min_h_lex(data, target_g, 0, 0, 0);
}

//  ============================================================
//  Part H2: Converse faithfulness
//  ============================================================

///  The choose for left_canonical_rep is in g's coset.
///  left_min_coset_len(g) satisfies its choose predicate.
///  Scan for the minimum coset length, building no_shorter_coset_word.
proof fn lemma_scan_min_coset_len(
    data: AmalgamatedData, g: Word, current: nat, bound: nat,
)
    requires
        amalgamated_data_valid(data),
        has_left_coset_word_of_len(data, g, bound),
        current <= bound,
        no_shorter_coset_word(data, g, current),
    ensures
        exists|l: nat| current <= l && l <= bound && #[trigger] is_min_coset_len(data, g, l),
    decreases bound - current,
{
    if has_left_coset_word_of_len(data, g, current) {
        assert(is_min_coset_len(data, g, current));
    } else {
        lemma_scan_min_coset_len(data, g, current + 1, bound);
    }
}

proof fn lemma_left_min_coset_len_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        is_min_coset_len(data, g, left_min_coset_len(data, g)),
{
    //  g is in its own coset at length g.len()
    lemma_same_left_coset_reflexive(data, g);
    assert(has_left_coset_word_of_len(data, g, g.len() as nat));

    //  Scan from 0 to g.len() to find minimum with is_min_coset_len
    assert(no_shorter_coset_word(data, g, 0nat));
    lemma_scan_min_coset_len(data, g, 0, g.len() as nat);
    //  Now: exists l with is_min_coset_len(data, g, l)
    //  So left_min_coset_len's choose is satisfiable → result satisfies has_left_coset_word_of_len.
}

///  left_canonical_rep(g) satisfies all four choose properties:
///  in g's coset, word_valid, correct length, correct lex rank.
proof fn lemma_left_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_left_coset(data, g, left_canonical_rep(data, g)),
        word_valid(left_canonical_rep(data, g), data.p1.num_generators),
        left_canonical_rep(data, g).len() == left_min_coset_len(data, g),
        word_lex_rank_base(left_canonical_rep(data, g), lex_base(data)) == left_min_coset_lex(data, g),
{
    lemma_left_min_coset_len_satisfiable(data, g);
    lemma_left_min_coset_lex_satisfiable(data, g);
    //  Both chooses are satisfiable → left_canonical_rep's choose is satisfiable
    //  → the result satisfies all four predicate conjuncts
}

///  Converse: if same_left_coset(g, ε) and left_h_part(g) = ε, then g ≡ ε.
///
///  This relies on the left_h_part choose being satisfiable when g is in the
///  subgroup coset. When the predicate is satisfiable and the result is ε:
///    equiv(p1, embed_a(ε), concat(inv(ε), g)) = equiv(p1, ε, g).
///
///  Proving satisfiability requires: in_generated_subgroup → exists K-word
///  witness. This is the key infrastructure lemma connecting the two notions
///  of subgroup membership.
///
///  For now, this requires the satisfiability as a precondition.
///  TODO: prove satisfiability from in_left_subgroup.
pub proof fn lemma_g1_decompose_converse(
    data: AmalgamatedData, g: Word,
    //  The K-word witness: there exists h0 with embed_a(h0) ≡ g
    h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        left_canonical_rep(data, g) =~= empty_word(),
        left_h_part(data, g) =~= empty_word(),
        //  Witness: the choose predicate for left_h_part is satisfiable
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1, apply_embedding(a_words(data), h_witness), g),
    ensures
        equiv_in_presentation(data.p1, g, empty_word()),
{
    //  left_h_part(g) is a choose with a satisfiable predicate (h_witness works).
    //  The choose returned ε, so ε satisfies the predicate:
    //    equiv(p1, embed_a(ε), concat(inv(rep), g))
    //  With rep = ε: equiv(p1, ε, g).
    //  Hence g ≡ ε.

    //  The key: with a satisfiable choose, the result satisfies the predicate.
    //  embed_a(ε) = ε. concat(inv(ε), g) =~= g.
    //  So: equiv(p1, ε, g) holds.
    reveal(presentation_valid);
    assert(apply_embedding(a_words(data), empty_word()) =~= empty_word());
    assert(inverse_word(empty_word()) =~= empty_word()) by {
        assert(inverse_word(empty_word()).len() == 0);
    }
    assert(concat(inverse_word(left_canonical_rep(data, g)), g) =~= g) by {
        assert(inverse_word(left_canonical_rep(data, g)) =~= empty_word());
        let c = concat(empty_word(), g);
        assert(c.len() == g.len());
        assert forall|k: int| 0 <= k < g.len() implies c[k] == g[k] by {}
    }
    //  h_witness satisfies the left_h_part choose predicate at level left_h_min_len.
    //  First: show left_h_min_len's choose is satisfiable via h_witness.
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  h_witness has embed_a(h_witness) ≡ g. And target =~= g (since rep = ε).
    //  So embed_a(h_witness) ≡ target. This means h_witness witnesses
    //  has_left_h_witness_of_len(data, target, h_witness.len()).
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    //  Use nat well-ordering on has_left_h_witness_of_len
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  Establish h-lex satisfiability for the three-step choose
    lemma_left_h_min_lex_satisfiable(data, g, h_witness);

    //  Three-step choose satisfiable → left_h_part(g) satisfies its predicate.
    //  left_h_part(g) = ε → equiv(embed_a(ε), target) = equiv(ε, g)
    assert(word_valid(empty_word(), data.p1.num_generators)) by {
        assert(empty_word().len() == 0);
    }
    crate::presentation::lemma_equiv_symmetric(data.p1, empty_word(), g);
}

///  The empty word is shortlex-minimal: nothing is shortlex-smaller.
///  (Already proved in shortlex.rs as lemma_empty_shortlex_minimal.)

///  left_canonical_rep of the empty word (identity element) is the empty word.
///  Because: ε is in ε's coset (reflexive), and ε is shortlex-minimal.
///  If pred(0) is true and no_pred_below(pred, l) holds, then l must be 0.
///  Because no_pred_below(pred, l) for l > 0 requires !pred(l-1), and eventually !pred(0).
proof fn lemma_no_pred_below_forces_zero(pred: spec_fn(nat) -> bool, l: nat)
    requires
        no_pred_below(pred, l),
        pred(0nat),
    ensures
        l == 0,
    decreases l,
{
    if l == 0 {
    } else {
        //  no_pred_below(pred, l) = !pred(l-1) && no_pred_below(pred, l-1)
        //  By IH: no_pred_below(pred, l-1) && pred(0) → l-1 == 0
        lemma_no_pred_below_forces_zero(pred, (l - 1) as nat);
        //  l - 1 == 0, so l == 1. And no_pred_below(pred, 1) = !pred(0) && true = false.
        //  But no_pred_below(pred, l) = no_pred_below(pred, 1) is given as true. Contradiction.
    }
}

///  Transfer no_pred_below through implication: if pred2(l) → pred1(l) for all l,
///  and no_pred_below(pred1, n), then no_pred_below(pred2, n).
proof fn lemma_no_pred_below_transfer(
    pred1: spec_fn(nat) -> bool, pred2: spec_fn(nat) -> bool, n: nat,
)
    requires
        no_pred_below(pred1, n),
        forall|l: nat| pred2(l) ==> #[trigger] pred1(l),
    ensures
        no_pred_below(pred2, n),
    decreases n,
{
    if n == 0 {} else {
        lemma_no_pred_below_transfer(pred1, pred2, (n - 1) as nat);
    }
}

///  Transfer no_smaller_h_lex (A-side) to no_smaller_h_lex_g2 (B-side).
proof fn lemma_no_smaller_h_lex_transfer(
    data: AmalgamatedData, target_a: Word, target_b: Word, l: nat, r: nat,
)
    requires
        no_smaller_h_lex(data, target_a, l, r),
        forall|r2: nat| has_right_h_witness_of_len_rank(data, target_b, l, r2)
            ==> #[trigger] has_left_h_witness_of_len_rank(data, target_a, l, r2),
    ensures
        no_smaller_h_lex_g2(data, target_b, l, r),
    decreases r,
{
    if r == 0 {} else {
        lemma_no_smaller_h_lex_transfer(data, target_a, target_b, l, (r - 1) as nat);
    }
}

///  Extract all four choose properties from b_rcoset_h.
///  Mirrors lemma_left_h_part_full_props for the B-side.
proof fn lemma_b_rcoset_h_full_props(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let rep = b_rcoset_rep(data, g);
        let target = concat(g, inverse_word(rep));
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& h.len() == b_rcoset_h_min_len(data, g)
        &&& word_lex_rank_base(h, h_lex_base(data)) == b_rcoset_h_min_lex(data, g)
        &&& equiv_in_presentation(data.p2,
                apply_embedding(b_words(data), h), target)
    }),
{
    //  Mirror the A-side approach: satisfiable → nat_well_ordering → scan
    lemma_b_rcoset_h_satisfiable(data, g, h_witness);
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));

    //  min-len satisfiability: h_witness gives a witness → nat_well_ordering
    let pred_len = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred_len(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_len, h_witness.len() as nat);
    let l = b_rcoset_h_min_len(data, g);

    //  The choose for b_rcoset_h(g) returns word at length l (from full choose predicate)
    //  Extract a witness at length l from has_right_h_witness_of_len(target, l)
    let w_at_l: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), w), target);
    let wr = word_lex_rank_base(w_at_l, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex_g2(data, target, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target, l, 0, wr);
}

///  If no_smaller_h_lex_g2(target, l, m) and has_right_h_witness_of_len_rank(target, l, k),
///  then k >= m. (Analog of lemma_no_pred_below_implies_ge for the G₂ lex structure.)
proof fn lemma_no_smaller_g2_implies_ge(
    data: AmalgamatedData, target: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_h_lex_g2(data, target, l, m),
        has_right_h_witness_of_len_rank(data, target, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {} else {
        if k < m {
            lemma_no_smaller_g2_implies_ge(data, target, l, (m - 1) as nat, k);
        }
    }
}

///  left_min_coset_len for the empty word is 0.
proof fn lemma_left_min_coset_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_min_coset_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let n1 = data.p1.num_generators;

    //  ε is in its own coset with length 0
    lemma_same_left_coset_reflexive(data, e);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    assert(has_left_coset_word_of_len(data, e, 0nat));

    //  no_shorter_coset_word(data, ε, 0) is true (base case of recursion)
    assert(no_shorter_coset_word(data, e, 0nat));

    //  So is_min_coset_len(data, ε, 0) holds — the choose is satisfiable at l = 0.
    assert(is_min_coset_len(data, e, 0nat));

    let l = left_min_coset_len(data, e);
    //  l satisfies is_min_coset_len(data, ε, l), which includes no_shorter_coset_word.
    //  has_left_coset_word_of_len(data, ε, 0) holds. By no_shorter_implies_ge: 0 >= l. So l == 0.
    lemma_no_shorter_coset_word_implies_ge(data, e, l, 0nat);
}

pub proof fn lemma_left_rep_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_canonical_rep(data, empty_word()) =~= empty_word(),
{
    let n1 = data.p1.num_generators;
    let e = empty_word();

    lemma_left_min_coset_len_identity(data);
    //  left_min_coset_len(ε) == 0

    lemma_same_left_coset_reflexive(data, e);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }

    //  ε has lex rank 0:
    assert(word_lex_rank(e) == 0);

    //  has_left_coset_word_of_len_rank(data, ε, 0, 0) — ε witnesses it
    assert(has_left_coset_word_of_len_rank(data, e, 0nat, 0nat));

    //  is_min_coset_lex(data, ε, 0, 0): has word at (0, 0) + no smaller lex
    assert(no_smaller_coset_lex(data, e, 0nat, 0nat));
    assert(is_min_coset_lex(data, e, 0nat, 0nat));

    let lex_min = left_min_coset_lex(data, e);
    //  lex_min satisfies is_min_coset_lex(ε, 0, lex_min).
    //  has(ε, 0, 0) holds. By no_smaller_implies_ge: 0 >= lex_min. So lex_min == 0.
    lemma_no_smaller_coset_lex_implies_ge(data, e, 0nat, lex_min, 0nat);
    //  left_min_coset_lex(ε) == 0

    //  left_canonical_rep(ε): choose with length 0, lex rank 0.
    //  Any word of length 0 is ε. The choose result has length 0 → it's ε.
}

///  left_h_part of the empty word is the empty K-word.
///  Because: left_canonical_rep(ε) = ε, so inv(rep) ++ ε = ε.
///  embed_a(ε) = ε ≡ ε in G₁. And ε is the shortlex-min such K-word.
///  left_h_min_len for the empty word is 0.
proof fn lemma_left_h_min_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_h_min_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    lemma_left_rep_identity(data);

    //  target = concat(inv(rep), ε) =~= ε (since rep = ε)
    let rep = left_canonical_rep(data, e);
    let target = concat(inverse_word(rep), e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }

    //  ε is a K-word of length 0 with embed_a(ε) = ε ≡ ε = target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_refl(p1, e);
    assert(has_left_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));

    let l = left_h_min_len(data, e);
    lemma_no_pred_below_forces_zero(pred, l);
}

pub proof fn lemma_left_h_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_h_part(data, empty_word()) =~= empty_word(),
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    lemma_left_rep_identity(data);
    lemma_left_h_min_len_identity(data);

    //  left_h_min_len(ε) == 0
    let l = left_h_min_len(data, e);
    assert(l == 0);

    let rep = left_canonical_rep(data, e);
    let target = concat(inverse_word(rep), e);

    //  ε satisfies the predicate (makes the choose satisfiable):
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }
    crate::presentation::lemma_equiv_refl(p1, e);

    //  Establish h-lex satisfiability: ε has lex rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target, 0nat, 0nat));
    assert(is_min_h_lex(data, target, 0nat, 0nat));
    //  left_h_min_lex's choose is satisfiable → three-step choose satisfiable

    //  The choose is satisfiable → result h satisfies: h.len() == 0
    let h = left_h_part(data, e);
    //  h.len() == l == 0, so h =~= ε
}

///  b_rcoset_h_min_len of ε is 0 (mirrors lemma_left_h_min_len_identity for B-side).
proof fn lemma_b_rcoset_h_min_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        b_rcoset_h_min_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p2 = data.p2;
    reveal(presentation_valid);

    //  b_rcoset_rep(ε) = ε
    lemma_identity_in_generated_subgroup(p2, b_words(data));
    lemma_b_rcoset_in_subgroup(data, e);

    //  target =~= ε
    let rep = b_rcoset_rep(data, e);
    let target = concat(e, inverse_word(rep));
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }

    //  ε is a K-word of length 0 with embed_b(ε) ≡ target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(b_words(data), e) =~= e);
    crate::presentation::lemma_equiv_refl(p2, e);
    assert(has_right_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));

    let l = b_rcoset_h_min_len(data, e);
    lemma_no_pred_below_forces_zero(pred, l);
}

///  Establish h-part satisfiability for right B-coset decomposition.
///  Mirrors lemma_a_rcoset_h_satisfiable for G₂.
pub proof fn lemma_b_rcoset_h_satisfiable(data: AmalgamatedData, g: Word, h_witness: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let rep = b_rcoset_rep(data, g);
        let target = concat(g, inverse_word(rep));
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& equiv_in_presentation(data.p2,
                apply_embedding(b_words(data), h), target)
    }),
{
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));

    //  h_witness witnesses has_right_h_witness_of_len(target, h_witness.len())
    assert(has_right_h_witness_of_len(data, target, h_witness.len() as nat));

    //  Nat well-ordering → b_rcoset_h_min_len satisfiable
    let pred_h = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  h-lex satisfiability (scan for min lex at min length)
    let l = b_rcoset_h_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex_g2(data, target, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target, l, 0, wr);
}

///  b_rcoset_h of the empty word is ε (mirrors lemma_left_h_identity for the B-side).
pub proof fn lemma_b_rcoset_h_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        b_rcoset_h(data, empty_word()) =~= empty_word(),
{
    let e = empty_word();
    let k = k_size(data);
    let p2 = data.p2;
    reveal(presentation_valid);

    //  b_rcoset_rep(ε) = ε
    lemma_identity_in_generated_subgroup(p2, b_words(data));
    lemma_b_rcoset_in_subgroup(data, e);
    lemma_b_rcoset_h_min_len_identity(data);

    let l = b_rcoset_h_min_len(data, e);
    assert(l == 0);

    let rep = b_rcoset_rep(data, e);
    let target = concat(e, inverse_word(rep));

    //  ε satisfies the predicate
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(b_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }
    crate::presentation::lemma_equiv_refl(p2, e);

    //  Establish h-lex satisfiability: ε has lex rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_right_h_witness_of_len_rank(data, target, 0nat, 0nat));
    assert(no_smaller_h_lex_g2(data, target, 0nat, 0nat));
    assert(is_min_h_lex_g2(data, target, 0nat, 0nat));

    //  The choose gives h with h.len() == 0, so h =~= ε
}

///  The identity state (ε, []) is canonical.
pub proof fn lemma_identity_state_canonical(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        is_canonical_state(data, empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    let syls = Seq::<Syllable>::empty();

    //  word_valid(ε, k_size)
    assert(word_valid(e, k_size(data)));

    //  left_h_part(embed_a(ε)) =~= ε
    assert(apply_embedding(a_words(data), e) =~= e);
    lemma_left_h_identity(data);

    //  b_rcoset_h(embed_b(ε)) =~= ε
    assert(apply_embedding(b_words(data), e) =~= e);
    lemma_b_rcoset_h_identity(data);

    //  Syllable conditions: vacuously true for empty syls
}

///  Inserting a word at a position preserves the action if the word acts trivially
///  on ALL states (universal version).
pub proof fn lemma_insert_trivial_preserves_action(
    data: AmalgamatedData,
    prefix: Word, middle: Word, suffix: Word,
    h: Word, syllables: Seq<Syllable>,
)
    requires
        same_action(data, middle, empty_word()),
    ensures
        act_word(data, concat(prefix, concat(middle, suffix)), h, syllables)
            == act_word(data, concat(prefix, suffix), h, syllables),
{
    //  Right-to-left: suffix processed first, then middle, then prefix.
    //  concat(prefix, middle·suffix) → act_word(prefix, act_word(middle·suffix, h, syls))
    //  middle·suffix → act_word(middle, act_word(suffix, h, syls))
    //  Since middle ≡ ε (same_action): act_word(middle, sh, ss) = act_word(ε, sh, ss) = (sh, ss)
    lemma_act_word_concat(data, prefix, concat(middle, suffix), h, syllables);
    let (sh, ss) = act_word(data, suffix, h, syllables);
    lemma_act_word_concat(data, middle, suffix, h, syllables);
    lemma_act_word_concat(data, prefix, suffix, h, syllables);
}

///  Inserting a word preserves the action when the word acts trivially on the
///  SPECIFIC intermediate state (targeted version for canonical states).
///  Inserting a trivially-acting middle word preserves the action.
///  With right-to-left processing: suffix processed first, then middle acts on that state.
pub proof fn lemma_insert_trivial_at_state(
    data: AmalgamatedData,
    prefix: Word, middle: Word, suffix: Word,
    h: Word, syllables: Seq<Syllable>,
)
    requires ({
        let (sh, ss) = act_word(data, suffix, h, syllables);
        act_word(data, middle, sh, ss) == (sh, ss)
    }),
    ensures
        act_word(data, concat(prefix, concat(middle, suffix)), h, syllables)
            == act_word(data, concat(prefix, suffix), h, syllables),
{
    lemma_act_word_concat(data, prefix, concat(middle, suffix), h, syllables);
    let (sh, ss) = act_word(data, suffix, h, syllables);
    lemma_act_word_concat(data, middle, suffix, h, syllables);
    lemma_act_word_concat(data, prefix, suffix, h, syllables);
}

//  ============================================================
//  Part I: AFP injectivity theorem
//  ============================================================

///  The inverse pair word [s, inv(s)].
///  The inverse pair word [inv(s), s]. With right-to-left processing, this applies s first
///  then inv(s), giving φ(inv(s)) ∘ φ(s) = φ(inv(s)·s) = φ(ε) = identity.
///  Note: action_well_defined quantifies over ALL symbols s, so this covers both orderings.
pub open spec fn inverse_pair_word(s: Symbol) -> Word {
    Seq::new(1, |_j: int| inverse_symbol(s)) + Seq::new(1, |_j: int| s)
}

///  A specific relator acts trivially on a specific state.
pub open spec fn relator_acts_trivially(
    data: AmalgamatedData, r: Word, h: Word, syls: Seq<Syllable>,
) -> bool {
    act_word(data, r, h, syls) == (h, syls)
}

///  State canonicity: h is a valid K-word AND is the canonical representative
///  for its subgroup equivalence class (matching textbook element-level states).
///  The action always produces canonical K-words (from left_h_part choose).
///  The identity state (ε, []) satisfies this: left_h_part(embed_a(ε)) = left_h_part(ε) =~= ε.
pub open spec fn is_canonical_state(data: AmalgamatedData, h: Word, syls: Seq<Syllable>) -> bool {
    word_valid(h, k_size(data))
    && left_h_part(data, apply_embedding(a_words(data), h)) =~= h
    && b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h
    //  Left syllable reps are canonical, word_valid, and non-identity (textbook reduced sequence)
    && (forall|j: int| #![trigger syls[j]]
        0 <= j < syls.len() && syls[j].is_left ==> (
        word_valid(syls[j].rep, data.p1.num_generators)
        && a_rcoset_rep(data, syls[j].rep) =~= syls[j].rep
        && !(syls[j].rep =~= empty_word())))
    //  Right syllable reps: canonical, word_valid, non-identity (mirrors left)
    && (forall|j: int| #![trigger syls[j]]
        0 <= j < syls.len() && !syls[j].is_left ==> (
        word_valid(syls[j].rep, data.p2.num_generators)
        && b_rcoset_rep(data, syls[j].rep) =~= syls[j].rep
        && !(syls[j].rep =~= empty_word())))
    //  Alternating: adjacent syllables from different factors (textbook reduced sequence)
    && (forall|j: int| #![trigger syls[j]]
        0 <= j < syls.len() - 1 ==> syls[j].is_left != syls[j + 1].is_left)
}

///  The action of a single symbol preserves canonical state (h is word_valid for k).
///  This follows from left_h_part and right_h_part always producing word_valid K-words.
///
///  For now we state this as a spec-level property that the action preserves.
///  A full inductive proof requires showing act_sym preserves word_valid(h, k),
///  which follows from the choose predicates of left_h_part/right_h_part.
pub open spec fn action_preserves_canonical(data: AmalgamatedData) -> bool {
    let n = data.p1.num_generators + data.p2.num_generators;
    forall|w: Word, h: Word, syls: Seq<Syllable>|
        word_valid(w, n) && is_canonical_state(data, h, syls) ==>
        #[trigger] is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1)
}

///  The action is well-defined on canonical states:
///  every AFP relator and inverse pair acts trivially.
pub open spec fn action_well_defined(data: AmalgamatedData) -> bool {
    let afp = amalgamated_free_product(data);
    //  Every AFP relator acts trivially on canonical states
    &&& (forall|i: nat, inverted: bool, h: Word, syls: Seq<Syllable>|
        i < afp.relators.len() && is_canonical_state(data, h, syls) ==>
        #[trigger] relator_acts_trivially(data, get_relator(afp, i, inverted), h, syls))
    //  Every inverse pair of a valid AFP symbol acts trivially on canonical states
    &&& (forall|s: Symbol, h: Word, syls: Seq<Syllable>|
        symbol_valid(s, afp.num_generators) && is_canonical_state(data, h, syls) ==>
        #[trigger] relator_acts_trivially(data, inverse_pair_word(s), h, syls))
}

///  Derivation-level well-definedness: a full derivation preserves the action.
pub proof fn lemma_act_word_deriv(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
    h: Word,
    syllables: Seq<Syllable>,
)
    requires
        action_well_defined(data),
        action_preserves_canonical(data),
        amalgamated_data_valid(data),
        is_canonical_state(data, h, syllables),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        word_valid(w1, amalgamated_free_product(data).num_generators),
    ensures
        act_word(data, w1, h, syllables) == act_word(data, w2, h, syllables),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let afp = amalgamated_free_product(data);
        let step = steps.first();
        let w_mid = apply_step(afp, w1, step).unwrap();

        //  Connect afp.num_generators == n1 + n2 for action_preserves_canonical trigger
        crate::amalgamated_free_product::lemma_add_relators_num_generators(
            crate::free_product::free_product(data.p1, data.p2),
            crate::amalgamated_free_product::amalgamation_relators(data));

        //  Per-step: act_word(w1, h, syls) == act_word(w_mid, h, syls)
        //  Each step inserts/deletes a relator or free pair at some position.
        //  By lemma_act_word_concat: we split at the position.
        //  The inserted/deleted part acts trivially (from action_well_defined).
        //  So the action is preserved.

        //  For now: the action_well_defined condition plus the composition lemma
        //  gives us the per-step result. Each step type:
        //    FreeReduce: deletes pair [s, inv(s)] → pair acts trivially
        //    FreeExpand: inserts pair [s, inv(s)] → pair acts trivially
        //    RelatorInsert: inserts relator → relator acts trivially
        //    RelatorDelete: deletes relator → relator acts trivially

        //  The insertion/deletion at a position is handled by lemma_insert_trivial_preserves_action.
        //  We need to match the step type and extract the position + relator/pair.

        //  With right-to-left processing: suffix is processed FIRST, then the middle
        //  (pair/relator), then the prefix. So the trivial-action check uses the suffix state.
        match step {
            DerivationStep::FreeReduce { position } => {
                //  w1 has [s, inv(s)] at position. inverse_pair_word(inv(s)) = [s, inv(s)].
                let s2 = w1[(position + 1) as int];
                let pair = inverse_pair_word(s2);
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position + 2, w1.len() as int);
                assert(w1 =~= concat(prefix, concat(pair, suffix))) by {
                    assert(w1.len() == concat(prefix, concat(pair, suffix)).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, concat(pair, suffix))[k]
                    by { if k < position {} else if k < position + 2 {} else {} }
                }
                assert(w_mid =~= concat(prefix, suffix));
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(symbol_valid(s2, afp.num_generators));
                assert(relator_acts_trivially(data, inverse_pair_word(s2), sh, ss));
                assert(act_word(data, pair, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, pair, suffix, h, syllables);
            },
            DerivationStep::FreeExpand { position, symbol } => {
                //  Inserts [symbol, inv(symbol)]. inverse_pair_word(inv(symbol)) = [symbol, inv(symbol)].
                let pair = inverse_pair_word(inverse_symbol(symbol));
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position, w1.len() as int);
                assert(w_mid =~= concat(prefix, concat(pair, suffix)));
                assert(w1 =~= concat(prefix, suffix)) by {
                    assert(w1.len() == concat(prefix, suffix).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, suffix)[k]
                    by { if k < position {} else {} }
                }
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(symbol_valid(inverse_symbol(symbol), afp.num_generators));
                assert(relator_acts_trivially(data, inverse_pair_word(inverse_symbol(symbol)), sh, ss));
                assert(act_word(data, pair, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, pair, suffix, h, syllables);
            },
            DerivationStep::RelatorInsert { position, relator_index, inverted } => {
                let r = get_relator(afp, relator_index, inverted);
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position, w1.len() as int);
                assert(w_mid =~= concat(prefix, concat(r, suffix)));
                assert(w1 =~= concat(prefix, suffix)) by {
                    assert(w1.len() == concat(prefix, suffix).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, suffix)[k]
                    by { if k < position {} else {} }
                }
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(relator_acts_trivially(data,
                    get_relator(afp, relator_index, inverted), sh, ss));
                assert(act_word(data, r, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, r, suffix, h, syllables);
            },
            DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                let r = get_relator(afp, relator_index, inverted);
                let rlen = r.len();
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position + rlen as int, w1.len() as int);
                assert(w1 =~= concat(prefix, concat(r, suffix))) by {
                    assert(w1.len() == concat(prefix, concat(r, suffix)).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, concat(r, suffix))[k]
                    by {
                        if k < position {} else if k < position + rlen as int {
                            assert(w1.subrange(position, position + rlen as int) == r);
                        } else {}
                    }
                }
                assert(w_mid =~= concat(prefix, suffix));
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(relator_acts_trivially(data,
                    get_relator(afp, relator_index, inverted), sh, ss));
                assert(act_word(data, r, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, r, suffix, h, syllables);
            },
        }

        //  Each branch established: act_word(w1, h, syls) == act_word(w_mid, h, syls)
        //  IH: need word_valid(w_mid, n) for the recursive call.
        crate::amalgamated_free_product::lemma_amalgamated_valid(data);
        crate::presentation::lemma_step_preserves_word_valid_pres(
            afp, w1, step, w_mid);
        lemma_act_word_deriv(data, steps.drop_first(), w_mid, w2, h, syllables);
    }
}

///  The action preserves canonical state for a single symbol.
///  act_sym produces h from left_h_part or right_h_part, which are choose results
///  satisfying word_valid(h, k). So the output h is word_valid.
///
///  Note: this requires the left_h_part and right_h_part choose predicates to be
///  satisfiable for the products encountered. This is guaranteed when the
///  starting state is canonical and the transversal decomposition exists.
///
///  For the identity state and action-produced states, satisfiability holds.
///  We take it as a precondition for now.
proof fn lemma_action_preserves_canonical(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syls: Seq<Syllable>,
)
    requires
        action_preserves_canonical(data),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators + data.p2.num_generators),
    ensures
        is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1),
{
    //  Direct from action_preserves_canonical spec.
}

//  ============================================================
//  Part I1a: RIGHT A-coset h-part equiv invariance
//  ============================================================

///  RIGHT A-coset h-part min-len equiv: if targets are equivalent, min-len matches.
proof fn lemma_a_rcoset_h_min_len_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        a_rcoset_rep(data, g1) =~= a_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(g1, inverse_word(a_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(g2, inverse_word(a_rcoset_rep(data, g2)))),
    ensures
        a_rcoset_h_min_len(data, g1) == a_rcoset_h_min_len(data, g2),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep1 = a_rcoset_rep(data, g1);
    let rep2 = a_rcoset_rep(data, g2);
    let target1 = concat(g1, inverse_word(rep1));
    let target2 = concat(g2, inverse_word(rep2));
    reveal(presentation_valid);

    //  rep word_valid from rcoset_rep_props
    lemma_a_rcoset_rep_props(data, g1);
    lemma_a_rcoset_rep_props(data, g2);

    //  target1 ≡ target2 (from g1 ≡ g2 and inv(rep1) =~= inv(rep2))
    crate::word::lemma_inverse_word_valid(rep1, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(rep1), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(rep2), n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g1, g2, inverse_word(rep1));

    let l1 = a_rcoset_h_min_len(data, g1);
    let l2 = a_rcoset_h_min_len(data, g2);

    //  Satisfiability: has_left_h_witness_of_len(target1, hw1.len()) etc.
    assert(has_left_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_left_h_witness_of_len(data, target2, h_witness2.len() as nat));

    //  Get min-len chooses to fire
    let pred1 = |l: nat| has_left_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_left_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    //  Transfer: l1 works for target2 (via h_witness_transfer)
    assert(has_left_h_witness_of_len(data, target1, l1));
    lemma_h_witness_transfer(data, target1, target2, l1);
    //  Transfer: l2 works for target1
    crate::presentation::lemma_equiv_symmetric(p1, target1, target2);
    lemma_h_witness_transfer(data, target2, target1, l2);

    //  Bidirectional ≥: no_pred_below(pred1, l1) + pred2(l1) → l1 ≥ l2 (and vice versa)
    //  no_pred_below gives: nothing shorter than l1 for pred1
    //  But pred2(l1) holds → l1 ≥ l2 (from l2's minimality)
    //  This follows from the choose semantics + no_pred_below
    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  RIGHT A-coset h-part equiv invariance: if g₁ ≡ g₂ and reps match, h-parts match.
///  Mirrors lemma_b_rcoset_h_equiv_invariant for A-cosets.
#[verifier::rlimit(40)]
pub proof fn lemma_a_rcoset_h_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        a_rcoset_rep(data, g1) =~= a_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(g1, inverse_word(a_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(g2, inverse_word(a_rcoset_rep(data, g2)))),
    ensures
        a_rcoset_h(data, g1) =~= a_rcoset_h(data, g2),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep1 = a_rcoset_rep(data, g1);
    let target1 = concat(g1, inverse_word(rep1));
    let target2 = concat(g2, inverse_word(a_rcoset_rep(data, g2)));
    reveal(presentation_valid);

    //  Min-len equality
    lemma_a_rcoset_h_min_len_equiv(data, g1, g2, h_witness1, h_witness2);
    let l = a_rcoset_h_min_len(data, g1);

    //  Satisfiability for both
    lemma_a_rcoset_h_satisfiable(data, g1, h_witness1);
    lemma_a_rcoset_h_satisfiable(data, g2, h_witness2);

    //  rep word_valid
    lemma_a_rcoset_rep_props(data, g1);
    lemma_a_rcoset_rep_props(data, g2);

    //  target1 ≡ target2
    crate::word::lemma_inverse_word_valid(rep1, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(rep1), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(a_rcoset_rep(data, g2)), n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g1, g2, inverse_word(rep1));

    //  Establish min-len choose satisfiability via h-witnesses
    assert(has_left_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_left_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred_len1 = |l: nat| has_left_h_witness_of_len(data, target1, l);
    let pred_len2 = |l: nat| has_left_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred_len1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred_len2, h_witness2.len() as nat);
    //  Now the min-len choose is satisfiable → l = a_rcoset_h_min_len fires
    assert(has_left_h_witness_of_len(data, target1, l));
    assert(has_left_h_witness_of_len(data, target2, l));
    let w1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target1);
    let w2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target2);
    let wr1 = word_lex_rank_base(w1, h_lex_base(data));
    let wr2 = word_lex_rank_base(w2, h_lex_base(data));

    //  Lex satisfiability: scan to establish min-lex
    assert(has_left_h_witness_of_len_rank(data, target1, l, wr1));
    assert(no_smaller_h_lex(data, target1, l, 0nat));
    lemma_scan_min_h_lex(data, target1, l, 0, wr1);
    assert(has_left_h_witness_of_len_rank(data, target2, l, wr2));
    assert(no_smaller_h_lex(data, target2, l, 0nat));
    lemma_scan_min_h_lex(data, target2, l, 0, wr2);

    let rw1 = a_rcoset_h(data, g1);
    let rw2 = a_rcoset_h(data, g2);
    let r1 = a_rcoset_h_min_lex(data, g1);
    let r2 = a_rcoset_h_min_lex(data, g2);

    //  Transfer: rw1 witnesses for target1 → also for target2
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw1), target1, target2);
    crate::presentation::lemma_equiv_symmetric(p1, target1, target2);
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw2), target2, target1);

    //  Bidirectional ≥ on lex rank
    lemma_no_smaller_h_lex_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_implies_ge(data, target1, l, r1, r2);
    //  r1 == r2

    //  Lex rank injectivity → same word
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw1[k]) < base
    by { assert(symbol_valid(rw1[k], k_size(data))); match rw1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw2[k]) < base
    by { assert(symbol_valid(rw2[k], k_size(data))); match rw2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw1, rw2, base);
}

//  ============================================================
//  Part I1b: One-shot action and relator triviality
//  ============================================================

///  One-shot G₁ action: apply a full G₁ word g to syllables via a single coset decomposition.
///  This is act_left_sym generalized from a single symbol to a full word product.
///  The key property: this depends only on the G₁-equivalence class of g.
pub open spec fn g1_one_shot_action(
    data: AmalgamatedData,
    g: Word,       //  full G₁ product (e.g., concat(w, embed_a(h)))
    syls: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let rep = a_rcoset_rep(data, g);
    let h_new = a_rcoset_h(data, g);

    if rep =~= empty_word() {
        (h_new, syls)
    } else if syls.len() == 0 || !syls.first().is_left {
        (h_new, Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep }) + syls)
    } else {
        let full = concat(g, syls.first().rep);
        let merged_rep = a_rcoset_rep(data, full);
        let merged_h = a_rcoset_h(data, full);
        if merged_rep =~= empty_word() {
            (merged_h, syls.drop_first())
        } else {
            (merged_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syls.drop_first())
        }
    }
}

///  One-shot on embed_a(h) returns (h, syls) for canonical h.
///  Because embed_a(h) is in the subgroup when h is A-canonical.
proof fn lemma_one_shot_identity(
    data: AmalgamatedData, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
    ensures
        g1_one_shot_action(data, apply_embedding(a_words(data), h), syls) == (h, syls),
{
    let embed_h = apply_embedding(a_words(data), h);
    let n1 = data.p1.num_generators;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  embed_a(h) is in the A-subgroup → rep = ε
    lemma_apply_embedding_in_subgroup(data.p1, a_words(data), h);
    lemma_a_rcoset_in_subgroup(data, embed_h);
    //  a_rcoset_rep(embed_h) =~= ε

    //  h-part = h (from is_canonical_state: left_h_part(embed_a(h)) =~= h)
    //  a_rcoset_h involves the same choose as left_h_part (via the target)
    //  Since rep = ε, target = concat(embed_h, inv(ε)) = embed_h
    //  is_canonical_state gives: left_h_part(embed_a(h)) =~= h
    //  We need: a_rcoset_h(embed_h) =~= h
    //  This follows from the h-part equiv invariance on embed_h
    //  embed_h ≡ embed_h (reflexivity) + left_h_part =~= h (canonical)
    crate::presentation::lemma_equiv_refl(data.p1, embed_h);
    lemma_subgroup_rcoset_restore(data, embed_h, h);
}

///  One-shot on a subgroup element g ≡ embed_a(h) returns (h, syls) for canonical h.
///  This is the special case needed for relator triviality:
///  if r ≡ ε in G₁, then concat(r, embed_a(h)) ≡ embed_a(h), so the one-shot gives (h, syls).
proof fn lemma_one_shot_subgroup_restore(
    data: AmalgamatedData, g: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        is_canonical_state(data, h, syls),
        equiv_in_presentation(data.p1, g, apply_embedding(a_words(data), h)),
    ensures
        g1_one_shot_action(data, g, syls) == (h, syls),
{
    let embed_h = apply_embedding(a_words(data), h);
    let n1 = data.p1.num_generators;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  g ≡ embed_a(h) ∈ A-subgroup → a_rcoset_rep(g) =~= ε
    lemma_apply_embedding_in_subgroup(data.p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(data.p1, g, embed_h);
    lemma_in_subgroup_equiv(data.p1, a_words(data), embed_h, g);
    lemma_a_rcoset_in_subgroup(data, g);

    //  a_rcoset_h(g) =~= h (by subgroup_rcoset_restore)
    lemma_subgroup_rcoset_restore(data, g, h);
}

///  Prepend-cancel: peeling off coset rep c from product p and prepending as syllable
///  gives the same one-shot result. Takes new_syls as parameter to avoid lambda mismatch.
#[verifier::rlimit(60)]
proof fn lemma_one_shot_prepend_cancel(
    data: AmalgamatedData, p: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(p, data.p1.num_generators),
        word_valid(c, data.p1.num_generators),
        !(c =~= empty_word()),
        a_rcoset_rep(data, c) =~= c,
        !(a_rcoset_rep(data, concat(p, inverse_word(c))) =~= empty_word()),
        syls.len() == 0 || !syls.first().is_left,
        new_syls.len() > 0,
        new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g1_one_shot_action(data, concat(p, inverse_word(c)), new_syls)
            == g1_one_shot_action(data, p, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let q = concat(p, inverse_word(c));
    reveal(presentation_valid);

    //  concat(q, c) = concat(p·c⁻¹, c) ≡ p via left inverse cancellation
    crate::word::lemma_inverse_word_valid(c, n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n1);
    crate::word::lemma_concat_word_valid(q, c, n1);

    //  Associativity: concat(q, c) =~= concat(p, concat(inv(c), c))
    assert(concat(q, c) =~= concat(p, concat(inverse_word(c), c))) by {
        let lhs = concat(q, c);
        let rhs = concat(p, concat(inverse_word(c), c));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < p.len() as int {} else {
                let j = k - p.len() as int;
                if j < inverse_word(c).len() as int {} else {}
            }
        }
    }
    //  inv(c) · c ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p1, c);
    //  concat(p, concat(inv(c), c)) ≡ concat(p, ε) =~= p
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, p, concat(inverse_word(c), c), empty_word());
    assert(concat(p, empty_word()) =~= p) by {
        assert(concat(p, empty_word()).len() == p.len());
        assert forall|k: int| 0 <= k < p.len() implies concat(p, empty_word())[k] == p[k] by {}
    }
    crate::word::lemma_concat_word_valid(inverse_word(c), c, n1);
    crate::word::lemma_concat_word_valid(p, concat(inverse_word(c), c), n1);
    //  concat(p, ε) =~= p → equiv via equiv_refl
    crate::presentation::lemma_equiv_refl(p1, concat(p, empty_word()));
    //  Now chain: concat(p, inv(c)·c) ≡ concat(p, ε) ≡ p (=~= gives ≡ automatically)
    //  Since concat(q, c) =~= concat(p, inv(c)·c), Z3 derives equiv(concat(q, c), p).

    //  Coset invariance: concat(q, c) ≡ p → same coset → same rep
    lemma_same_a_rcoset_from_equiv(data, concat(q, c), p);
    lemma_a_rcoset_rep_invariant(data, concat(q, c), p);

    //  H-part invariance: derive h-witnesses, then call equiv invariant
    lemma_a_rcoset_rep_props(data, concat(q, c));
    lemma_a_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, concat(q, c)), n1);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, p), n1);
    crate::word::lemma_concat_word_valid(concat(q, c), inverse_word(a_rcoset_rep(data, concat(q, c))), n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(a_rcoset_rep(data, p)), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(concat(q, c), inverse_word(a_rcoset_rep(data, concat(q, c)))));
    lemma_subgroup_to_k_word(p1, a_words(data), concat(p, inverse_word(a_rcoset_rep(data, p))));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(concat(q, c), inverse_word(a_rcoset_rep(data, concat(q, c)))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(p, inverse_word(a_rcoset_rep(data, p))));
    assert(a_words(data).len() == k_size(data));
    lemma_a_rcoset_h_equiv_invariant(data, concat(q, c), p, hw1, hw2);

    //  rep_q ≠ ε (precondition): merge case. concat(q, c) is the merge product.
    //  Z3 sees: merge rep = a_rcoset_rep(concat(q,c)) =~= a_rcoset_rep(p), etc.
}

///  Subgroup-prepend: when q ∈ A (rep = ε), prepending c as syllable = one-shot of concat(q, c).
///  Handles the subgroup sub-case that prepend-cancel doesn't cover.
///  one_shot(q, [Syl(left, c)] + syls) = one_shot(concat(q, c), syls)
#[verifier::rlimit(300)]
///  Part A (G₁): coset setup — target_p ≡ target_q via rep invariant.
proof fn lemma_one_shot_subgroup_prepend_setup(
    data: AmalgamatedData, q: Word, c: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(q, data.p1.num_generators),
        word_valid(c, data.p1.num_generators),
        !(c =~= empty_word()),
        a_rcoset_rep(data, c) =~= c,
        a_rcoset_rep(data, q) =~= empty_word(),
    ensures ({
        let p = concat(q, c);
        let target_q = concat(q, inverse_word(a_rcoset_rep(data, q)));
        let target_p = concat(p, inverse_word(a_rcoset_rep(data, p)));
        &&& target_q =~= q
        &&& equiv_in_presentation(data.p1, target_p, target_q)
        &&& a_rcoset_rep(data, p) =~= c
        &&& word_valid(p, data.p1.num_generators)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let p = concat(q, c);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    lemma_a_rcoset_rep_props(data, q);
    crate::presentation::lemma_equiv_refl(p1, q);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(q, inverse_word(a_rcoset_rep(data, q))), q);
    crate::word::lemma_inverse_word_valid(c, n1);
    crate::word::lemma_concat_word_valid(q, c, n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n1);
    lemma_right_cancel(p1, q, c);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(concat(q, c), inverse_word(c)), q);
    lemma_in_subgroup_equiv(p1, a_words(data), q, concat(p, inverse_word(c)));
    lemma_a_rcoset_rep_invariant(data, p, c);

    let target_q = concat(q, inverse_word(a_rcoset_rep(data, q)));
    assert(target_q =~= q) by {
        assert(a_rcoset_rep(data, q) =~= empty_word());
        assert(inverse_word(empty_word()).len() == 0);
        assert(concat(q, inverse_word(a_rcoset_rep(data, q))).len() == q.len());
        assert forall|k: int| 0 <= k < q.len()
            implies concat(q, inverse_word(a_rcoset_rep(data, q)))[k] == q[k] by {}
    }

    lemma_a_rcoset_rep_props(data, p);
    let target_p = concat(p, inverse_word(a_rcoset_rep(data, p)));
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, p), n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(a_rcoset_rep(data, p)), n1);
    crate::word::lemma_concat_word_valid(q, inverse_word(a_rcoset_rep(data, q)), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(q, inverse_word(a_rcoset_rep(data, q))));
    lemma_subgroup_to_k_word(p1, a_words(data), concat(p, inverse_word(a_rcoset_rep(data, p))));
    assert(a_words(data).len() == k_size(data));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(p, inverse_word(a_rcoset_rep(data, p))));
    crate::benign::lemma_apply_embedding_valid(a_words(data), hw2, n1);
    crate::presentation::lemma_equiv_symmetric(p1,
        apply_embedding(a_words(data), hw2), target_p);
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), hw2), target_p, target_q);
    crate::presentation::lemma_equiv_transitive(p1,
        target_p, apply_embedding(a_words(data), hw2), target_q);
}

///  Part B (G₁): h equality — show a_rcoset_h(q) =~= a_rcoset_h(p).
proof fn lemma_one_shot_subgroup_prepend_h_eq(
    data: AmalgamatedData, q: Word, p: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(q, data.p1.num_generators),
        word_valid(p, data.p1.num_generators),
        ({
            let target_q = concat(q, inverse_word(a_rcoset_rep(data, q)));
            let target_p = concat(p, inverse_word(a_rcoset_rep(data, p)));
            &&& target_q =~= q
            &&& equiv_in_presentation(data.p1, target_p, target_q)
        }),
    ensures
        a_rcoset_h(data, q) =~= a_rcoset_h(data, p),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    lemma_a_rcoset_rep_props(data, q);
    lemma_a_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, q), n1);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, p), n1);
    crate::word::lemma_concat_word_valid(q, inverse_word(a_rcoset_rep(data, q)), n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(a_rcoset_rep(data, p)), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(q, inverse_word(a_rcoset_rep(data, q))));
    lemma_subgroup_to_k_word(p1, a_words(data), concat(p, inverse_word(a_rcoset_rep(data, p))));
    assert(a_words(data).len() == k_size(data));

    let target_q = concat(q, inverse_word(a_rcoset_rep(data, q)));
    let target_p = concat(p, inverse_word(a_rcoset_rep(data, p)));

    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw), target_q);
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw), target_p);

    //  Min-len equality
    let pred_q = |l: nat| has_left_h_witness_of_len(data, target_q, l);
    let pred_p = |l: nat| has_left_h_witness_of_len(data, target_p, l);
    assert(has_left_h_witness_of_len(data, target_q, hw1.len() as nat));
    assert(has_left_h_witness_of_len(data, target_p, hw2.len() as nat));
    lemma_nat_well_ordering(pred_q, hw1.len() as nat);
    lemma_nat_well_ordering(pred_p, hw2.len() as nat);
    let l_q = a_rcoset_h_min_len(data, q);
    let l_p = a_rcoset_h_min_len(data, p);
    assert(has_left_h_witness_of_len(data, target_q, l_q));
    crate::presentation::lemma_equiv_symmetric(p1, target_p, target_q);
    lemma_h_witness_transfer(data, target_q, target_p, l_q);
    lemma_h_witness_transfer(data, target_p, target_q, l_p);
    lemma_no_pred_below_implies_ge(pred_p, l_p, l_q);
    lemma_no_pred_below_implies_ge(pred_q, l_q, l_p);

    //  Lex rank equality
    lemma_a_rcoset_h_satisfiable(data, q, hw1);
    lemma_a_rcoset_h_satisfiable(data, p, hw2);
    let rw_q = a_rcoset_h(data, q);
    let rw_p = a_rcoset_h(data, p);
    let r_q = a_rcoset_h_min_lex(data, q);
    let r_p = a_rcoset_h_min_lex(data, p);
    assert(has_left_h_witness_of_len(data, target_p, l_q));
    let w_q: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target_q);
    let w_p: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target_p);
    let wr_q = word_lex_rank_base(w_q, h_lex_base(data));
    let wr_p = word_lex_rank_base(w_p, h_lex_base(data));
    assert(has_left_h_witness_of_len_rank(data, target_q, l_q, wr_q));
    assert(has_left_h_witness_of_len_rank(data, target_p, l_q, wr_p));
    assert(no_smaller_h_lex(data, target_q, l_q, 0nat));
    assert(no_smaller_h_lex(data, target_p, l_q, 0nat));
    lemma_scan_min_h_lex(data, target_q, l_q, 0, wr_q);
    lemma_scan_min_h_lex(data, target_p, l_q, 0, wr_p);

    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw_q), target_q, target_p);
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw_p), target_p, target_q);
    lemma_no_smaller_h_lex_implies_ge(data, target_p, l_q, r_p, r_q);
    lemma_no_smaller_h_lex_implies_ge(data, target_q, l_q, r_q, r_p);

    //  Injectivity
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw_q.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_q[k]) < base
    by { assert(symbol_valid(rw_q[k], k_size(data))); match rw_q[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw_p.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_p[k]) < base
    by { assert(symbol_valid(rw_p[k], k_size(data))); match rw_p[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw_q, rw_p, base);
}

///  Main (G₁): combines setup + h equality to prove action equality.
proof fn lemma_one_shot_subgroup_prepend(
    data: AmalgamatedData, q: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(q, data.p1.num_generators),
        word_valid(c, data.p1.num_generators),
        !(c =~= empty_word()),
        a_rcoset_rep(data, c) =~= c,
        a_rcoset_rep(data, q) =~= empty_word(),
        syls.len() == 0 || !syls.first().is_left,
        new_syls.len() > 0,
        new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g1_one_shot_action(data, q, new_syls)
            == g1_one_shot_action(data, concat(q, c), syls),
{
    let p = concat(q, c);
    lemma_one_shot_subgroup_prepend_setup(data, q, c);
    crate::word::lemma_concat_word_valid(q, c, data.p1.num_generators);
    lemma_one_shot_subgroup_prepend_h_eq(data, q, p);
}

///  One-shot G₁-invariance: if g ≡ g' in G₁ with same syllables, one-shot gives same result.
///  Combines rep invariance + h-part invariance for the full tuple.
#[verifier::rlimit(40)]
proof fn lemma_one_shot_g1_invariant(
    data: AmalgamatedData, g: Word, g_prime: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(g_prime, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, g_prime),
        //  First syl (if left) must be word_valid in G₁ for the merge case
        (syls.len() > 0 && syls.first().is_left
            ==> word_valid(syls.first().rep, data.p1.num_generators)),
    ensures
        g1_one_shot_action(data, g, syls) == g1_one_shot_action(data, g_prime, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    reveal(presentation_valid);

    //  Rep invariance
    lemma_same_a_rcoset_from_equiv(data, g, g_prime);
    lemma_a_rcoset_rep_invariant(data, g, g_prime);

    //  H-part invariance (need h-witnesses)
    lemma_a_rcoset_rep_props(data, g);
    lemma_a_rcoset_rep_props(data, g_prime);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, g), n1);
    crate::word::lemma_concat_word_valid(g, inverse_word(a_rcoset_rep(data, g)), n1);
    crate::word::lemma_concat_word_valid(g_prime, inverse_word(a_rcoset_rep(data, g_prime)), n1);
    lemma_subgroup_to_k_word(p1, a_words(data),
        concat(g, inverse_word(a_rcoset_rep(data, g))));
    lemma_subgroup_to_k_word(p1, a_words(data),
        concat(g_prime, inverse_word(a_rcoset_rep(data, g_prime))));
    assert(a_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(g, inverse_word(a_rcoset_rep(data, g))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(g_prime, inverse_word(a_rcoset_rep(data, g_prime))));
    lemma_a_rcoset_h_equiv_invariant(data, g, g_prime, hw1, hw2);

    //  Merge case: if rep ≠ ε and first syl left, need full product equiv too
    if !(a_rcoset_rep(data, g) =~= empty_word()) && syls.len() > 0 && syls.first().is_left {
        let c1 = syls.first().rep;
        crate::word::lemma_concat_word_valid(g, c1, n1);
        crate::word::lemma_concat_word_valid(g_prime, c1, n1);
        crate::presentation_lemmas::lemma_equiv_concat_left(p1, g, g_prime, c1);
        lemma_same_a_rcoset_from_equiv(data, concat(g, c1), concat(g_prime, c1));
        lemma_a_rcoset_rep_invariant(data, concat(g, c1), concat(g_prime, c1));
        //  Full product h-part invariance (rep_props BEFORE inverse_word_valid)
        lemma_a_rcoset_rep_props(data, concat(g, c1));
        lemma_a_rcoset_rep_props(data, concat(g_prime, c1));
        crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, concat(g, c1)), n1);
        crate::word::lemma_concat_word_valid(concat(g, c1),
            inverse_word(a_rcoset_rep(data, concat(g, c1))), n1);
        crate::word::lemma_concat_word_valid(concat(g_prime, c1),
            inverse_word(a_rcoset_rep(data, concat(g_prime, c1))), n1);
        lemma_subgroup_to_k_word(p1, a_words(data),
            concat(concat(g, c1), inverse_word(a_rcoset_rep(data, concat(g, c1)))));
        lemma_subgroup_to_k_word(p1, a_words(data),
            concat(concat(g_prime, c1), inverse_word(a_rcoset_rep(data, concat(g_prime, c1)))));
        let hw3: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(concat(g, c1), inverse_word(a_rcoset_rep(data, concat(g, c1)))));
        let hw4: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(concat(g_prime, c1), inverse_word(a_rcoset_rep(data, concat(g_prime, c1)))));
        lemma_a_rcoset_h_equiv_invariant(data, concat(g, c1), concat(g_prime, c1), hw3, hw4);
    }
}

///  One-shot step composition: one_shot of the full product equals one_shot applied after
///  the single-symbol step. Handles all three cases (subgroup, prepend, merge).
///  one_shot(concat(w, g_s), syls) = one_shot(concat(w, embed_a(h_s)), syls_s)
///  where (h_s, syls_s) = one_shot(g_s, syls) = act_left_sym(s, h, syls).
///  Helper: derive concat(w, embed_a(h_s)) ≡ concat(concat(w, g_s), inv(rep_s))
///  from the rcoset decomposition embed_a(h_s) · rep_s ≡ g_s.
proof fn lemma_embed_hs_equiv_chain(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        a_rcoset_h(data, g_s) =~= h_s,
    ensures ({
        let n1 = data.p1.num_generators;
        let rep_s = a_rcoset_rep(data, g_s);
        let embed_hs = apply_embedding(a_words(data), h_s);
        &&& equiv_in_presentation(data.p1, concat(w, embed_hs),
                concat(concat(w, g_s), inverse_word(rep_s)))
        &&& word_valid(concat(w, embed_hs), n1)
        &&& word_valid(concat(concat(w, g_s), inverse_word(rep_s)), n1)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep_s = a_rcoset_rep(data, g_s);
    let embed_hs = apply_embedding(a_words(data), h_s);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);

    lemma_a_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n1);
    crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(g_s, inverse_word(rep_s)));
    assert(a_words(data).len() == k_size(data));
    let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(g_s, inverse_word(rep_s)));
    lemma_rcoset_decomposition(data, g_s, hw_s);

    //  embed_a(h_s) · rep_s ≡ g_s → embed_a(h_s) ≡ g_s · inv(rep_s)
    crate::word::lemma_concat_word_valid(embed_hs, rep_s, n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        concat(embed_hs, rep_s), g_s, inverse_word(rep_s));
    crate::word::lemma_concat_word_valid(concat(embed_hs, rep_s), inverse_word(rep_s), n1);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        concat(g_s, inverse_word(rep_s)));
    lemma_right_cancel(p1, embed_hs, rep_s);
    crate::presentation::lemma_equiv_transitive(p1,
        concat(g_s, inverse_word(rep_s)),
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        embed_hs);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(g_s, inverse_word(rep_s)), embed_hs);
    //  embed_hs ≡ concat(g_s, inv(rep_s))

    crate::presentation_lemmas::lemma_equiv_concat_right(p1, w, embed_hs,
        concat(g_s, inverse_word(rep_s)));
    crate::word::lemma_concat_word_valid(w, embed_hs, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n1);
    assert(concat(w, concat(g_s, inverse_word(rep_s))) =~=
           concat(concat(w, g_s), inverse_word(rep_s))) by {
        let lhs = concat(w, concat(g_s, inverse_word(rep_s)));
        let rhs = concat(concat(w, g_s), inverse_word(rep_s));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }
}

///  Step case 2 (prepend): uses equiv chain helper + prepend/subgroup dispatch.
#[verifier::rlimit(50)]
proof fn lemma_one_shot_step_prepend(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        syls.len() == 0 || !syls.first().is_left,
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let rep_s = a_rcoset_rep(data, g_s);
    let n1 = data.p1.num_generators;
    reveal(presentation_valid);
    lemma_embed_hs_equiv_chain(data, w, g_s, h_s);
    lemma_a_rcoset_rep_idempotent(data, g_s);
    lemma_a_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n1);
    let peeled = concat(concat(w, g_s), inverse_word(rep_s));
    //  syls_s is the prepend result: [Syl(left, rep_s)] + syls. Help Z3 see this.
    let prepend_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep_s }) + syls;
    assert(syls_s =~= prepend_syls);
    assert(syls_s.first().is_left);
    assert(word_valid(rep_s, n1));
    //  Step 1: one_shot(concat(w, embed_hs), syls_s) = one_shot(peeled, syls_s)
    lemma_one_shot_g1_invariant(data,
        concat(w, apply_embedding(a_words(data), h_s)), peeled, syls_s);
    //  Step 2a: congruence — one_shot(peeled, syls_s) = one_shot(peeled, prepend_syls)
    assert(g1_one_shot_action(data, peeled, syls_s)
        == g1_one_shot_action(data, peeled, prepend_syls));
    //  Step 2b: cancel — one_shot(peeled, prepend_syls) = one_shot(concat(w, g_s), syls)
    //  Use g1_invariant to bridge: one_shot(peeled, prepend_syls) = one_shot(concat(w, g_s), syls)
    //  via prepend_cancel/subgroup_prepend, then combine with step 1 + 2a.
    //  Now pass syls_s directly (avoids lambda closure mismatch):
    if a_rcoset_rep(data, peeled) =~= empty_word() {
        lemma_one_shot_subgroup_prepend(data, peeled, rep_s, syls, syls_s);
        //  subgroup_prepend gives: one_shot(peeled, syls_s) == one_shot(concat(peeled, rep_s), syls)
        //  Need: concat(peeled, rep_s) ≡ concat(w, g_s) → g1_invariant
        crate::word::lemma_concat_word_valid(peeled, rep_s, n1);
        //  concat(peeled, rep_s) = concat(concat(w, g_s), inv(rep_s), rep_s) ≡ concat(w, g_s)
        crate::presentation_lemmas::lemma_word_inverse_left(data.p1, rep_s);
        crate::word::lemma_concat_word_valid(inverse_word(rep_s), rep_s, n1);
        crate::presentation_lemmas::lemma_equiv_concat_right(data.p1, concat(w, g_s),
            concat(inverse_word(rep_s), rep_s), empty_word());
        assert(concat(concat(w, g_s), empty_word()) =~= concat(w, g_s)) by {
            assert(concat(concat(w, g_s), empty_word()).len() == concat(w, g_s).len());
            assert forall|k: int| 0 <= k < concat(w, g_s).len()
                implies concat(concat(w, g_s), empty_word())[k] == concat(w, g_s)[k] by {}
        }
        assert(concat(peeled, rep_s) =~= concat(concat(w, g_s), concat(inverse_word(rep_s), rep_s))) by {
            let lhs = concat(peeled, rep_s);
            let rhs = concat(concat(w, g_s), concat(inverse_word(rep_s), rep_s));
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < concat(w, g_s).len() as int {} else {
                    let j = k - concat(w, g_s).len() as int;
                    if j < inverse_word(rep_s).len() as int {} else {}
                }
            }
        }
        crate::presentation::lemma_equiv_refl(data.p1, concat(concat(w, g_s), empty_word()));
        lemma_one_shot_g1_invariant(data, concat(peeled, rep_s), concat(w, g_s), syls);
    } else {
        lemma_one_shot_prepend_cancel(data, concat(w, g_s), rep_s, syls, syls_s);
    }
}

///  Step case 3 (merge): first syl is left, full = g_s · c1.
///  Bridge helper: concat(peeled, rep) ≡ concat(w, full) when peeled = concat(concat(w, full), inv(rep)).
proof fn lemma_peeled_concat_bridge(
    data: AmalgamatedData, w_full: Word, rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w_full, data.p1.num_generators),
        word_valid(rep, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1,
            concat(concat(w_full, inverse_word(rep)), rep), w_full),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let peeled = concat(w_full, inverse_word(rep));
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(rep, n1);
    crate::word::lemma_concat_word_valid(w_full, inverse_word(rep), n1);
    crate::word::lemma_concat_word_valid(peeled, rep, n1);

    //  concat(peeled, rep) =~= concat(w_full, concat(inv(rep), rep))
    assert(concat(peeled, rep) =~= concat(w_full, concat(inverse_word(rep), rep))) by {
        let lhs = concat(peeled, rep);
        let rhs = concat(w_full, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_full.len() as int {} else {
                let j = k - w_full.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }
    //  inv(rep) · rep ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p1, rep);
    crate::word::lemma_concat_word_valid(inverse_word(rep), rep, n1);
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, w_full,
        concat(inverse_word(rep), rep), empty_word());
    assert(concat(w_full, empty_word()) =~= w_full) by {
        assert(concat(w_full, empty_word()).len() == w_full.len());
        assert forall|k: int| 0 <= k < w_full.len()
            implies concat(w_full, empty_word())[k] == w_full[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p1, concat(w_full, empty_word()));
}

///  Step merge replaced sub-case: merged_rep ≠ ε → uses prepend cancel.
#[verifier::rlimit(100)]
proof fn lemma_one_shot_step_merge_replaced(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        syls.len() > 0 && syls.first().is_left,
        word_valid(syls.first().rep, data.p1.num_generators),
        syls.drop_first().len() == 0 || !syls.drop_first().first().is_left,
        a_rcoset_rep(data, syls.first().rep) =~= syls.first().rep,
        !(syls.first().rep =~= empty_word()),
        !({
            let full = concat(g_s, syls.first().rep);
            a_rcoset_rep(data, full) =~= empty_word()
        }),
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_hs = apply_embedding(a_words(data), h_s);
    let c1 = syls.first().rep;
    let full = concat(g_s, c1);
    let merged_rep = a_rcoset_rep(data, full);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);
    crate::word::lemma_concat_word_valid(g_s, c1, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(w, embed_hs, n1);
    crate::word::lemma_concat_word_valid(w, full, n1);
    lemma_a_rcoset_rep_props(data, full);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(full, inverse_word(merged_rep)));
    assert(a_words(data).len() == k_size(data));
    let hw_f: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(full, inverse_word(merged_rep)));
    lemma_a_rcoset_h_satisfiable(data, full, hw_f);
    lemma_rcoset_decomposition(data, full, hw_f);

    crate::presentation_lemmas::lemma_equiv_concat_right(p1, w, embed_hs,
        concat(full, inverse_word(merged_rep)));
    assert(concat(w, concat(full, inverse_word(merged_rep))) =~=
           concat(concat(w, full), inverse_word(merged_rep))) by {
        let lhs = concat(w, concat(full, inverse_word(merged_rep)));
        let rhs = concat(concat(w, full), inverse_word(merged_rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < full.len() as int {} else {}
            }
        }
    }
    lemma_a_rcoset_rep_idempotent(data, full);
    crate::word::lemma_concat_word_valid(concat(w, full), inverse_word(merged_rep), n1);
    let peeled_mr = concat(concat(w, full), inverse_word(merged_rep));
    lemma_one_shot_g1_invariant(data, concat(w, embed_hs), peeled_mr, syls_s);
    //  Help Z3: the merge product concat(concat(w, g_s), c1) =~= concat(w, full)
    assert(concat(concat(w, g_s), c1) =~= concat(w, full)) by {
        let lhs = concat(concat(w, g_s), c1);
        let rhs = concat(w, full);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }

    //  Sub-split: concat(w, g_s) could be in subgroup
    if a_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
        lemma_one_shot_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
    }

    if a_rcoset_rep(data, peeled_mr) =~= empty_word() {
        lemma_one_shot_subgroup_prepend(data, peeled_mr, merged_rep, syls.drop_first(), syls_s);
        //  Bridge: concat(peeled_mr, merged_rep) ≡ concat(w, full) via helper
        crate::word::lemma_concat_word_valid(peeled_mr, merged_rep, n1);
        lemma_peeled_concat_bridge(data, concat(w, full), merged_rep);
        lemma_one_shot_g1_invariant(data, concat(peeled_mr, merged_rep), concat(w, full), syls.drop_first());
    } else {
        lemma_one_shot_prepend_cancel(data, concat(w, full), merged_rep, syls.drop_first(), syls_s);
    }
}

///  Step case 3 (merge): dispatches to absorbed/replaced.
#[verifier::rlimit(150)]
proof fn lemma_one_shot_step_merge(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        syls.len() > 0 && syls.first().is_left,
        word_valid(syls.first().rep, data.p1.num_generators),
        a_rcoset_rep(data, syls.first().rep) =~= syls.first().rep,
        !(syls.first().rep =~= empty_word()),
        syls.drop_first().len() == 0 || !syls.drop_first().first().is_left,
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_hs = apply_embedding(a_words(data), h_s);
    let c1 = syls.first().rep;
    let full = concat(g_s, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);
    crate::word::lemma_concat_word_valid(g_s, c1, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(w, embed_hs, n1);
    crate::word::lemma_concat_word_valid(w, full, n1);

    //  h_s = a_rcoset_h(full). Get decomposition.
    lemma_a_rcoset_rep_props(data, full);
    let merged_rep = a_rcoset_rep(data, full);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(full, inverse_word(merged_rep)));
    assert(a_words(data).len() == k_size(data));
    let hw_f: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(full, inverse_word(merged_rep)));
    lemma_a_rcoset_h_satisfiable(data, full, hw_f);
    lemma_rcoset_decomposition(data, full, hw_f);
    //  embed_a(h_s) · merged_rep ≡ full

    //  concat(w, g_s, c1) =~= concat(w, full)
    assert(concat(concat(w, g_s), c1) =~= concat(w, full)) by {
        let lhs = concat(concat(w, g_s), c1);
        let rhs = concat(w, full);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }

    if merged_rep =~= empty_word() {
        //  Merge absorbed: embed_a(h_s) ≡ full
        crate::presentation_lemmas::lemma_equiv_concat_right(p1, w, embed_hs, full);
        crate::presentation::lemma_equiv_symmetric(p1, concat(w, embed_hs), concat(w, full));
        //  RHS = one_shot(concat(w, embed_hs), syls_s) = one_shot(concat(w, full), syls_s)
        lemma_one_shot_g1_invariant(data, concat(w, embed_hs), concat(w, full), syls_s);
        //  LHS = one_shot(concat(w, g_s), syls). Sub-split on rep(concat(w, g_s)):
        if a_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
            //  concat(w, g_s) ∈ A → use subgroup_prepend:
            //  one_shot(concat(w, g_s), syls) = one_shot(concat(concat(w, g_s), c1), syls.drop_first())
            //                                 = one_shot(concat(w, full), syls.drop_first())
            lemma_one_shot_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
        }
        //  If rep ≠ ε: Z3 should see the merge branch and compute the result directly
        return;
    } else {
        lemma_one_shot_step_merge_replaced(data, w, g_s, h_s, syls, syls_s);
    }
}

///  One-shot step composition: dispatches to subgroup/prepend/merge case helpers.
proof fn lemma_one_shot_step(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        is_canonical_state(data, h_s, syls_s),
        (syls.len() > 0 && syls.first().is_left ==> word_valid(syls.first().rep, data.p1.num_generators)),
        (syls.len() > 0 && syls.first().is_left ==> a_rcoset_rep(data, syls.first().rep) =~= syls.first().rep),
        (syls.len() > 0 && syls.first().is_left ==> !(syls.first().rep =~= empty_word())),
        (syls.len() > 0 && syls.first().is_left ==>
            (syls.drop_first().len() == 0 || !syls.drop_first().first().is_left)),
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let rep_s = a_rcoset_rep(data, g_s);
    reveal(presentation_valid);

    if rep_s =~= empty_word() {
        //  Case 1 (subgroup): embed_a(h_s) ≡ g_s → g1_invariant
        let n1 = data.p1.num_generators;
        let p1 = data.p1;
        assert forall|i: int| 0 <= i < a_words(data).len()
            implies word_valid(#[trigger] a_words(data)[i], n1)
        by { assert(word_valid(data.identifications[i].0, n1)); }
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);
        crate::word::lemma_concat_word_valid(w, g_s, n1);
        crate::word::lemma_concat_word_valid(w, apply_embedding(a_words(data), h_s), n1);
        lemma_a_rcoset_rep_props(data, g_s);
        crate::word::lemma_inverse_word_valid(rep_s, n1);
        crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n1);
        lemma_subgroup_to_k_word(p1, a_words(data), concat(g_s, inverse_word(rep_s)));
        assert(a_words(data).len() == k_size(data));
        let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(g_s, inverse_word(rep_s)));
        lemma_rcoset_decomposition(data, g_s, hw_s);
        crate::presentation_lemmas::lemma_equiv_concat_right(p1, w,
            apply_embedding(a_words(data), h_s), g_s);
        crate::presentation::lemma_equiv_symmetric(p1,
            concat(w, apply_embedding(a_words(data), h_s)), concat(w, g_s));
        lemma_one_shot_g1_invariant(data,
            concat(w, apply_embedding(a_words(data), h_s)), concat(w, g_s), syls_s);
        return;
    }

    if syls.len() == 0 || !syls.first().is_left {
        lemma_one_shot_step_prepend(data, w, g_s, h_s, syls, syls_s);
    } else {
        lemma_one_shot_step_merge(data, w, g_s, h_s, syls, syls_s);
    }
}

///  Main theorem: act_word of a G₁-only word equals the one-shot action.
///  Proof by induction on w.len(), using the step composition.
#[verifier::rlimit(50)]
pub proof fn lemma_act_word_eq_one_shot(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators),
        action_preserves_canonical(data),
    ensures
        act_word(data, w, h, syls)
            == g1_one_shot_action(data,
                concat(w, apply_embedding(a_words(data), h)), syls),
    decreases w.len(),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    if w.len() == 0 {
        //  act_word(ε, h, syls) = (h, syls). one_shot(embed_a(h), syls) = (h, syls).
        assert(concat(w, embed_h) =~= embed_h) by {
            assert(w.len() == 0);
            assert(concat(w, embed_h).len() == embed_h.len());
            assert forall|k: int| 0 <= k < embed_h.len()
                implies concat(w, embed_h)[k] == embed_h[k] by {}
        }
        lemma_one_shot_identity(data, h, syls);
    } else {
        //  w = concat(w.drop_last(), [w.last()]). Right-to-left: process w.last() first.
        let s = w.last();
        let w_prime = w.drop_last();
        let g_s = concat(Seq::new(1, |_i: int| s), embed_h);

        //  act_word(w, h, syls) = act_word(w', h_s, syls_s)
        let (h_s, syls_s) = act_sym(data, s, h, syls);

        //  (h_s, syls_s) is canonical: act_sym(s, h, syls) = act_word([s], h, syls)
        let s_word = Seq::new(1, |_i: int| s);
        lemma_act_word_single(data, s, h, syls);
        //  action_preserves_canonical with w = [s]
        assert(is_canonical_state(data, h_s, syls_s)) by {
            assert(is_canonical_state(data,
                act_word(data, s_word, h, syls).0,
                act_word(data, s_word, h, syls).1));
        }

        //  w' is word_valid (drop_last preserves word_valid)
        assert(word_valid(w_prime, n1)) by {
            assert forall|k: int| 0 <= k < w_prime.len()
                implies symbol_valid(#[trigger] w_prime[k], n1) by {
                    assert(w_prime[k] == w[k]);
                }
        }

        //  IH: act_word(w', h_s, syls_s) = one_shot(concat(w', embed_a(h_s)), syls_s)
        lemma_act_word_eq_one_shot(data, w_prime, h_s, syls_s);

        //  Now connect: one_shot(concat(w', embed_a(h_s)), syls_s) = one_shot(concat(w, embed_a(h)), syls)
        //  w = concat(w', [s]) so concat(w, embed_a(h)) = concat(w', concat([s], embed_a(h))) = concat(w', g_s)
        assert(concat(w, embed_h) =~= concat(w_prime, g_s)) by {
            let lhs = concat(w, embed_h);
            let rhs = concat(w_prime, g_s);
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < w_prime.len() as int {
                    assert(lhs[k] == w[k]);
                    assert(rhs[k] == w_prime[k]);
                } else if k == w_prime.len() as int {
                    assert(lhs[k] == w[k]);
                    assert(rhs[k] == g_s[0]);
                } else {
                    let j = k - w_prime.len() as int - 1;
                    assert(lhs[k] == embed_h[j]);
                    assert(rhs[k] == g_s[(k - w_prime.len() as int)]);
                }
            }
        }

        //  Step composition: one_shot(concat(w', g_s), syls) = one_shot(concat(w', embed_a(h_s)), syls_s)
        //  Left syls word_valid in G₁ (from canonical state)
        lemma_one_shot_step(data, w_prime, g_s, h_s, syls, syls_s);
    }
}

///  G₁ relator triviality: if w ≡ ε in G₁, then act_word(w, h, syls) = (h, syls).
pub proof fn lemma_g1_relator_acts_trivially(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators),
        equiv_in_presentation(data.p1, w, empty_word()),
        action_preserves_canonical(data),
    ensures
        act_word(data, w, h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  act_word = one_shot
    lemma_act_word_eq_one_shot(data, w, h, syls);

    //  concat(w, embed_a(h)) ≡ concat(ε, embed_a(h)) = embed_a(h) (since w ≡ ε)
    crate::presentation_lemmas::lemma_equiv_concat_left(data.p1, w, empty_word(), embed_h);
    assert(concat(empty_word(), embed_h) =~= embed_h) by {
        assert(concat(empty_word(), embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(empty_word(), embed_h)[k] == embed_h[k] by {}
    }
    crate::word::lemma_concat_word_valid(w, embed_h, n1);

    //  one_shot(embed_a(h), syls) = (h, syls)
    lemma_one_shot_subgroup_restore(data, concat(w, embed_h), h, syls);
}

//  ============================================================
//  Part I1c: G₂ one-shot action and relator triviality
//  Mirrors G₁ approach with b_rcoset instead of a_rcoset.
//  ============================================================

///  One-shot G₂ action: mirrors g1_one_shot_action with b_rcoset.
///  Syllable prepend/merge uses is_left=false (right syllables) instead of true.
pub open spec fn g2_one_shot_action(
    data: AmalgamatedData,
    g: Word,       //  full G₂-local product (e.g., concat(w_local, embed_b(h)))
    syls: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let rep = b_rcoset_rep(data, g);
    let h_new = b_rcoset_h(data, g);

    if rep =~= empty_word() {
        (h_new, syls)
    } else if syls.len() == 0 || syls.first().is_left {
        (h_new, Seq::new(1, |_i: int| Syllable { is_left: false, rep: rep }) + syls)
    } else {
        let full = concat(g, syls.first().rep);
        let merged_rep = b_rcoset_rep(data, full);
        let merged_h = b_rcoset_h(data, full);
        if merged_rep =~= empty_word() {
            (merged_h, syls.drop_first())
        } else {
            (merged_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syls.drop_first())
        }
    }
}

///  G₂ one-shot on g ≡ embed_b(h) returns (h, syls) for canonical h.
proof fn lemma_g2_one_shot_subgroup_restore(
    data: AmalgamatedData, g: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        is_canonical_state(data, h, syls),
        equiv_in_presentation(data.p2, g, apply_embedding(b_words(data), h)),
    ensures
        g2_one_shot_action(data, g, syls) == (h, syls),
{
    let embed_h = apply_embedding(b_words(data), h);
    let n2 = data.p2.num_generators;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  g ≡ embed_b(h) ∈ B-subgroup → b_rcoset_rep(g) = ε
    lemma_apply_embedding_in_subgroup_g2(data.p2, b_words(data), h);
    crate::presentation::lemma_equiv_symmetric(data.p2, g, embed_h);
    lemma_in_subgroup_equiv(data.p2, b_words(data), embed_h, g);
    lemma_b_rcoset_in_subgroup(data, g);

    //  b_rcoset_h(g) =~= h
    assert(is_canonical_state(data, h, Seq::<Syllable>::empty())) by {
        assert(Seq::<Syllable>::empty().len() == 0int);
    }
    crate::presentation::lemma_equiv_symmetric(data.p2, g, embed_h);
    lemma_subgroup_rcoset_restore_g2(data, g, h);
}

///  B-coset h-part min-len equiv for GENERAL reps (mirrors A-coset version).
proof fn lemma_b_rcoset_h_min_len_equiv_general(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        b_rcoset_rep(data, g1) =~= b_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h_min_len(data, g1) == b_rcoset_h_min_len(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep1 = b_rcoset_rep(data, g1);
    let target1 = concat(g1, inverse_word(rep1));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));
    reveal(presentation_valid);

    lemma_b_rcoset_rep_props(data, g1);
    lemma_b_rcoset_rep_props(data, g2);
    crate::word::lemma_inverse_word_valid(rep1, n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(rep1), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(b_rcoset_rep(data, g2)), n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, g1, g2, inverse_word(rep1));

    let l1 = b_rcoset_h_min_len(data, g1);
    let l2 = b_rcoset_h_min_len(data, g2);

    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    assert(has_right_h_witness_of_len(data, target1, l1));
    lemma_h_witness_transfer_g2(data, target1, target2, l1);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    lemma_h_witness_transfer_g2(data, target2, target1, l2);
    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  B-coset h-part equiv invariant for GENERAL reps (mirrors A-coset version).
#[verifier::rlimit(60)]
pub proof fn lemma_b_rcoset_h_equiv_invariant_general(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        b_rcoset_rep(data, g1) =~= b_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h(data, g1) =~= b_rcoset_h(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let target1 = concat(g1, inverse_word(b_rcoset_rep(data, g1)));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));
    reveal(presentation_valid);

    lemma_b_rcoset_h_min_len_equiv_general(data, g1, g2, h_witness1, h_witness2);
    let l = b_rcoset_h_min_len(data, g1);

    lemma_b_rcoset_rep_props(data, g1);
    lemma_b_rcoset_rep_props(data, g2);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g1), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(b_rcoset_rep(data, g1)), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(b_rcoset_rep(data, g2)), n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, g1, g2,
        inverse_word(b_rcoset_rep(data, g1)));

    //  Establish h-witness satisfiability for min-len
    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);
    assert(has_right_h_witness_of_len(data, target1, l));
    assert(has_right_h_witness_of_len(data, target2, l));

    //  Lex scan
    let w1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target1);
    let w2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target2);
    let wr1 = word_lex_rank_base(w1, h_lex_base(data));
    let wr2 = word_lex_rank_base(w2, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target1, l, wr1));
    assert(has_right_h_witness_of_len_rank(data, target2, l, wr2));
    assert(no_smaller_h_lex_g2(data, target1, l, 0nat));
    assert(no_smaller_h_lex_g2(data, target2, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target1, l, 0, wr1);
    lemma_scan_min_h_lex_g2(data, target2, l, 0, wr2);

    let rw1 = b_rcoset_h(data, g1);
    let rw2 = b_rcoset_h(data, g2);
    let r1 = b_rcoset_h_min_lex(data, g1);
    let r2 = b_rcoset_h_min_lex(data, g2);

    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw1), target1, target2);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw2), target2, target1);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target1, l, r1, r2);

    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw1[k]) < base
    by { assert(symbol_valid(rw1[k], k_size(data))); match rw1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw2[k]) < base
    by { assert(symbol_valid(rw2[k], k_size(data))); match rw2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw1, rw2, base);
}

///  G₂ one-shot G₂-invariance: if g ≡ g' in G₂, same one-shot result.
#[verifier::rlimit(60)]
proof fn lemma_g2_one_shot_g2_invariant(
    data: AmalgamatedData, g: Word, g_prime: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(g_prime, data.p2.num_generators),
        equiv_in_presentation(data.p2, g, g_prime),
        (syls.len() > 0 && !syls.first().is_left
            ==> word_valid(syls.first().rep, data.p2.num_generators)),
    ensures
        g2_one_shot_action(data, g, syls) == g2_one_shot_action(data, g_prime, syls),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    lemma_same_b_rcoset_from_equiv(data, g, g_prime);
    lemma_b_rcoset_rep_invariant(data, g, g_prime);

    lemma_b_rcoset_rep_props(data, g);
    lemma_b_rcoset_rep_props(data, g_prime);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g), n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(b_rcoset_rep(data, g)), n2);
    crate::word::lemma_concat_word_valid(g_prime, inverse_word(b_rcoset_rep(data, g_prime)), n2);
    lemma_subgroup_to_k_word(p2, b_words(data),
        concat(g, inverse_word(b_rcoset_rep(data, g))));
    lemma_subgroup_to_k_word(p2, b_words(data),
        concat(g_prime, inverse_word(b_rcoset_rep(data, g_prime))));
    assert(b_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(g, inverse_word(b_rcoset_rep(data, g))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(g_prime, inverse_word(b_rcoset_rep(data, g_prime))));
    lemma_b_rcoset_h_equiv_invariant_general(data, g, g_prime, hw1, hw2);

    if !(b_rcoset_rep(data, g) =~= empty_word()) && syls.len() > 0 && !syls.first().is_left {
        let c1 = syls.first().rep;
        crate::word::lemma_concat_word_valid(g, c1, n2);
        crate::word::lemma_concat_word_valid(g_prime, c1, n2);
        crate::presentation_lemmas::lemma_equiv_concat_left(p2, g, g_prime, c1);
        lemma_same_b_rcoset_from_equiv(data, concat(g, c1), concat(g_prime, c1));
        lemma_b_rcoset_rep_invariant(data, concat(g, c1), concat(g_prime, c1));
        lemma_b_rcoset_rep_props(data, concat(g, c1));
        lemma_b_rcoset_rep_props(data, concat(g_prime, c1));
        crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, concat(g, c1)), n2);
        crate::word::lemma_concat_word_valid(concat(g, c1),
            inverse_word(b_rcoset_rep(data, concat(g, c1))), n2);
        crate::word::lemma_concat_word_valid(concat(g_prime, c1),
            inverse_word(b_rcoset_rep(data, concat(g_prime, c1))), n2);
        lemma_subgroup_to_k_word(p2, b_words(data),
            concat(concat(g, c1), inverse_word(b_rcoset_rep(data, concat(g, c1)))));
        lemma_subgroup_to_k_word(p2, b_words(data),
            concat(concat(g_prime, c1), inverse_word(b_rcoset_rep(data, concat(g_prime, c1)))));
        let hw3: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(concat(g, c1), inverse_word(b_rcoset_rep(data, concat(g, c1)))));
        let hw4: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(concat(g_prime, c1), inverse_word(b_rcoset_rep(data, concat(g_prime, c1)))));
        lemma_b_rcoset_h_equiv_invariant_general(data, concat(g, c1), concat(g_prime, c1), hw3, hw4);
    }
}

///  G₂ prepend-cancel: mirrors lemma_one_shot_prepend_cancel with b_rcoset.
#[verifier::rlimit(60)]
proof fn lemma_g2_prepend_cancel(
    data: AmalgamatedData, p: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(p, data.p2.num_generators),
        word_valid(c, data.p2.num_generators),
        !(c =~= empty_word()),
        b_rcoset_rep(data, c) =~= c,
        !(b_rcoset_rep(data, concat(p, inverse_word(c))) =~= empty_word()),
        syls.len() == 0 || syls.first().is_left,
        new_syls.len() > 0,
        !new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g2_one_shot_action(data, concat(p, inverse_word(c)), new_syls)
            == g2_one_shot_action(data, p, syls),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let q = concat(p, inverse_word(c));
    reveal(presentation_valid);

    crate::word::lemma_inverse_word_valid(c, n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n2);
    crate::word::lemma_concat_word_valid(q, c, n2);
    assert(concat(q, c) =~= concat(p, concat(inverse_word(c), c))) by {
        let lhs = concat(q, c);
        let rhs = concat(p, concat(inverse_word(c), c));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < p.len() as int {} else {
                let j = k - p.len() as int;
                if j < inverse_word(c).len() as int {} else {}
            }
        }
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p2, c);
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, p, concat(inverse_word(c), c), empty_word());
    assert(concat(p, empty_word()) =~= p) by {
        assert(concat(p, empty_word()).len() == p.len());
        assert forall|k: int| 0 <= k < p.len() implies concat(p, empty_word())[k] == p[k] by {}
    }
    crate::word::lemma_concat_word_valid(inverse_word(c), c, n2);
    crate::word::lemma_concat_word_valid(p, concat(inverse_word(c), c), n2);
    crate::presentation::lemma_equiv_refl(p2, concat(p, empty_word()));
    //  concat(q, c) ≡ p

    lemma_same_b_rcoset_from_equiv(data, concat(q, c), p);
    lemma_b_rcoset_rep_invariant(data, concat(q, c), p);

    lemma_b_rcoset_rep_props(data, concat(q, c));
    lemma_b_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, concat(q, c)), n2);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, p), n2);
    crate::word::lemma_concat_word_valid(concat(q, c), inverse_word(b_rcoset_rep(data, concat(q, c))), n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(b_rcoset_rep(data, p)), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(concat(q, c), inverse_word(b_rcoset_rep(data, concat(q, c)))));
    lemma_subgroup_to_k_word(p2, b_words(data), concat(p, inverse_word(b_rcoset_rep(data, p))));
    assert(b_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(concat(q, c), inverse_word(b_rcoset_rep(data, concat(q, c)))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(p, inverse_word(b_rcoset_rep(data, p))));
    lemma_b_rcoset_h_equiv_invariant_general(data, concat(q, c), p, hw1, hw2);
}

///  G₂ subgroup-prepend: when q ∈ B, prepending c = one-shot of concat(q, c).
#[verifier::rlimit(200)]
///  Part A: coset setup — target_p ≡ target_q via rep invariant.
proof fn lemma_g2_subgroup_prepend_setup(
    data: AmalgamatedData, q: Word, c: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(q, data.p2.num_generators),
        word_valid(c, data.p2.num_generators),
        !(c =~= empty_word()),
        b_rcoset_rep(data, c) =~= c,
        b_rcoset_rep(data, q) =~= empty_word(),
    ensures ({
        let p = concat(q, c);
        let target_q = concat(q, inverse_word(b_rcoset_rep(data, q)));
        let target_p = concat(p, inverse_word(b_rcoset_rep(data, p)));
        &&& target_q =~= q
        &&& equiv_in_presentation(data.p2, target_p, target_q)
        &&& b_rcoset_rep(data, p) =~= c
        &&& word_valid(p, data.p2.num_generators)
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let p = concat(q, c);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    lemma_b_rcoset_rep_props(data, q);
    crate::presentation::lemma_equiv_refl(p2, q);
    lemma_in_subgroup_equiv(p2, b_words(data),
        concat(q, inverse_word(b_rcoset_rep(data, q))), q);
    crate::word::lemma_inverse_word_valid(c, n2);
    crate::word::lemma_concat_word_valid(q, c, n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n2);
    lemma_right_cancel(p2, q, c);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(concat(q, c), inverse_word(c)), q);
    lemma_in_subgroup_equiv(p2, b_words(data), q, concat(p, inverse_word(c)));
    lemma_b_rcoset_rep_invariant(data, p, c);

    //  target_q =~= q
    let target_q = concat(q, inverse_word(b_rcoset_rep(data, q)));
    assert(target_q =~= q) by {
        assert(b_rcoset_rep(data, q) =~= empty_word());
        assert(inverse_word(empty_word()).len() == 0);
        assert(concat(q, inverse_word(b_rcoset_rep(data, q))).len() == q.len());
        assert forall|k: int| 0 <= k < q.len()
            implies concat(q, inverse_word(b_rcoset_rep(data, q)))[k] == q[k] by {}
    }

    //  target_p ≡ target_q
    lemma_b_rcoset_rep_props(data, p);
    let target_p = concat(p, inverse_word(b_rcoset_rep(data, p)));
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, p), n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(b_rcoset_rep(data, p)), n2);
    crate::word::lemma_concat_word_valid(q, inverse_word(b_rcoset_rep(data, q)), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(q, inverse_word(b_rcoset_rep(data, q))));
    lemma_subgroup_to_k_word(p2, b_words(data), concat(p, inverse_word(b_rcoset_rep(data, p))));
    assert(b_words(data).len() == k_size(data));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(p, inverse_word(b_rcoset_rep(data, p))));
    //  Chain: equiv(embed(hw2), target_p) [from decomposition]
    //         equiv(embed(hw2), target_q) [from transitive through target_p → target_q via target_q =~= q]
    //  We need: equiv(target_p, target_q)
    //  = equiv_symmetric(embed(hw2), target_p) → equiv(target_p, embed(hw2))
    //  + equiv_transitive(target_p, embed(hw2), target_q)
    crate::benign::lemma_apply_embedding_valid(b_words(data), hw2, n2);
    crate::presentation::lemma_equiv_symmetric(p2,
        apply_embedding(b_words(data), hw2), target_p);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), hw2), target_p, target_q);
    crate::presentation::lemma_equiv_transitive(p2,
        target_p, apply_embedding(b_words(data), hw2), target_q);
}

///  Part B: h equality — show b_rcoset_h(q) =~= b_rcoset_h(p) via min-len + lex rank.
proof fn lemma_g2_subgroup_prepend_h_eq(
    data: AmalgamatedData, q: Word, p: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(q, data.p2.num_generators),
        word_valid(p, data.p2.num_generators),
        ({
            let target_q = concat(q, inverse_word(b_rcoset_rep(data, q)));
            let target_p = concat(p, inverse_word(b_rcoset_rep(data, p)));
            &&& target_q =~= q
            &&& equiv_in_presentation(data.p2, target_p, target_q)
        }),
    ensures
        b_rcoset_h(data, q) =~= b_rcoset_h(data, p),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    lemma_b_rcoset_rep_props(data, q);
    lemma_b_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, q), n2);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, p), n2);
    crate::word::lemma_concat_word_valid(q, inverse_word(b_rcoset_rep(data, q)), n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(b_rcoset_rep(data, p)), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(q, inverse_word(b_rcoset_rep(data, q))));
    lemma_subgroup_to_k_word(p2, b_words(data), concat(p, inverse_word(b_rcoset_rep(data, p))));
    assert(b_words(data).len() == k_size(data));

    let target_q = concat(q, inverse_word(b_rcoset_rep(data, q)));
    let target_p = concat(p, inverse_word(b_rcoset_rep(data, p)));

    //  Min-len equality
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw), target_q);
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw), target_p);
    let pred_q = |l: nat| has_right_h_witness_of_len(data, target_q, l);
    let pred_p = |l: nat| has_right_h_witness_of_len(data, target_p, l);
    assert(has_right_h_witness_of_len(data, target_q, hw1.len() as nat));
    assert(has_right_h_witness_of_len(data, target_p, hw2.len() as nat));
    lemma_nat_well_ordering(pred_q, hw1.len() as nat);
    lemma_nat_well_ordering(pred_p, hw2.len() as nat);
    let l_q = b_rcoset_h_min_len(data, q);
    let l_p = b_rcoset_h_min_len(data, p);
    assert(has_right_h_witness_of_len(data, target_q, l_q));
    //  We have equiv(target_p, target_q) from requires. Get the reverse:
    crate::presentation::lemma_equiv_symmetric(p2, target_p, target_q);
    //  Now: equiv(target_q, target_p)
    lemma_h_witness_transfer_g2(data, target_q, target_p, l_q);
    lemma_h_witness_transfer_g2(data, target_p, target_q, l_p);
    lemma_no_pred_below_implies_ge(pred_p, l_p, l_q);
    lemma_no_pred_below_implies_ge(pred_q, l_q, l_p);

    //  Lex rank equality
    let rw_q = b_rcoset_h(data, q);
    let rw_p = b_rcoset_h(data, p);
    let r_q = b_rcoset_h_min_lex(data, q);
    let r_p = b_rcoset_h_min_lex(data, p);
    assert(has_right_h_witness_of_len(data, target_p, l_q));
    let wq: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target_q);
    let wp: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target_p);
    let wrq = word_lex_rank_base(wq, h_lex_base(data));
    let wrp = word_lex_rank_base(wp, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target_q, l_q, wrq));
    assert(has_right_h_witness_of_len_rank(data, target_p, l_q, wrp));
    assert(no_smaller_h_lex_g2(data, target_q, l_q, 0nat));
    assert(no_smaller_h_lex_g2(data, target_p, l_q, 0nat));
    lemma_scan_min_h_lex_g2(data, target_q, l_q, 0, wrq);
    lemma_scan_min_h_lex_g2(data, target_p, l_q, 0, wrp);

    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw_q), target_q, target_p);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw_p), target_p, target_q);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target_p, l_q, r_p, r_q);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target_q, l_q, r_q, r_p);

    //  Injectivity
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw_q.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_q[k]) < base
    by { assert(symbol_valid(rw_q[k], k_size(data))); match rw_q[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw_p.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_p[k]) < base
    by { assert(symbol_valid(rw_p[k], k_size(data))); match rw_p[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw_q, rw_p, base);
}

///  Main: combines setup + h equality to prove action equality.
proof fn lemma_g2_subgroup_prepend(
    data: AmalgamatedData, q: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(q, data.p2.num_generators),
        word_valid(c, data.p2.num_generators),
        !(c =~= empty_word()),
        b_rcoset_rep(data, c) =~= c,
        b_rcoset_rep(data, q) =~= empty_word(),
        syls.len() == 0 || syls.first().is_left,
        new_syls.len() > 0,
        !new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g2_one_shot_action(data, q, new_syls)
            == g2_one_shot_action(data, concat(q, c), syls),
{
    let p = concat(q, c);
    lemma_g2_subgroup_prepend_setup(data, q, c);
    crate::word::lemma_concat_word_valid(q, c, data.p2.num_generators);
    lemma_g2_subgroup_prepend_h_eq(data, q, p);
}

///  G₂ embed equiv chain: derive concat(w, embed_b(h_s)) ≡ concat(concat(w, g_s), inv(rep_s)).
proof fn lemma_g2_embed_hs_equiv_chain(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(w, data.p2.num_generators),
        word_valid(g_s, data.p2.num_generators),
        word_valid(h_s, k_size(data)),
        !(b_rcoset_rep(data, g_s) =~= empty_word()),
        b_rcoset_h(data, g_s) =~= h_s,
    ensures ({
        let n2 = data.p2.num_generators;
        let rep_s = b_rcoset_rep(data, g_s);
        let embed_hs = apply_embedding(b_words(data), h_s);
        &&& equiv_in_presentation(data.p2, concat(w, embed_hs),
                concat(concat(w, g_s), inverse_word(rep_s)))
        &&& word_valid(concat(w, embed_hs), n2)
        &&& word_valid(concat(concat(w, g_s), inverse_word(rep_s)), n2)
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep_s = b_rcoset_rep(data, g_s);
    let embed_hs = apply_embedding(b_words(data), h_s);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_s, n2);

    lemma_b_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n2);
    crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(g_s, inverse_word(rep_s)));
    assert(b_words(data).len() == k_size(data));
    let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(g_s, inverse_word(rep_s)));
    lemma_b_rcoset_decomposition(data, g_s, hw_s);

    //  embed_b(h_s) · rep_s ≡ g_s → embed_b(h_s) ≡ g_s · inv(rep_s)
    crate::word::lemma_concat_word_valid(embed_hs, rep_s, n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2,
        concat(embed_hs, rep_s), g_s, inverse_word(rep_s));
    crate::word::lemma_concat_word_valid(concat(embed_hs, rep_s), inverse_word(rep_s), n2);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        concat(g_s, inverse_word(rep_s)));
    lemma_right_cancel(p2, embed_hs, rep_s);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(g_s, inverse_word(rep_s)),
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        embed_hs);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(g_s, inverse_word(rep_s)), embed_hs);
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, w, embed_hs,
        concat(g_s, inverse_word(rep_s)));
    crate::word::lemma_concat_word_valid(w, embed_hs, n2);
    crate::word::lemma_concat_word_valid(w, g_s, n2);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n2);
    assert(concat(w, concat(g_s, inverse_word(rep_s))) =~=
           concat(concat(w, g_s), inverse_word(rep_s))) by {
        let lhs = concat(w, concat(g_s, inverse_word(rep_s)));
        let rhs = concat(concat(w, g_s), inverse_word(rep_s));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }
}

///  G₂ peeled bridge: concat(peeled, rep) ≡ w_full.
proof fn lemma_g2_peeled_bridge(
    data: AmalgamatedData, w_full: Word, rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(w_full, data.p2.num_generators),
        word_valid(rep, data.p2.num_generators),
    ensures
        equiv_in_presentation(data.p2,
            concat(concat(w_full, inverse_word(rep)), rep), w_full),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let peeled = concat(w_full, inverse_word(rep));
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(rep, n2);
    crate::word::lemma_concat_word_valid(w_full, inverse_word(rep), n2);
    crate::word::lemma_concat_word_valid(peeled, rep, n2);
    assert(concat(peeled, rep) =~= concat(w_full, concat(inverse_word(rep), rep))) by {
        let lhs = concat(peeled, rep);
        let rhs = concat(w_full, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_full.len() as int {} else {
                let j = k - w_full.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p2, rep);
    crate::word::lemma_concat_word_valid(inverse_word(rep), rep, n2);
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, w_full,
        concat(inverse_word(rep), rep), empty_word());
    assert(concat(w_full, empty_word()) =~= w_full) by {
        assert(concat(w_full, empty_word()).len() == w_full.len());
        assert forall|k: int| 0 <= k < w_full.len()
            implies concat(w_full, empty_word())[k] == w_full[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p2, concat(w_full, empty_word()));
}

///  G₂ step composition: one_shot(concat(w, g_s), syls) = one_shot(concat(w, embed_b(h_s)), syls_s).
///  Handles subgroup/prepend/merge cases. Mirrors lemma_one_shot_step for G₂.
#[verifier::rlimit(200)]
proof fn lemma_g2_one_shot_step(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(w, data.p2.num_generators),
        word_valid(g_s, data.p2.num_generators),
        word_valid(h_s, k_size(data)),
        g2_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        is_canonical_state(data, h_s, syls_s),
        (syls.len() > 0 && !syls.first().is_left ==> word_valid(syls.first().rep, data.p2.num_generators)),
        (syls.len() > 0 && !syls.first().is_left ==> b_rcoset_rep(data, syls.first().rep) =~= syls.first().rep),
        (syls.len() > 0 && !syls.first().is_left ==> !(syls.first().rep =~= empty_word())),
        (syls.len() > 0 && !syls.first().is_left ==>
            (syls.drop_first().len() == 0 || syls.drop_first().first().is_left)),
    ensures
        g2_one_shot_action(data, concat(w, g_s), syls)
            == g2_one_shot_action(data, concat(w, apply_embedding(b_words(data), h_s)), syls_s),
{
    let rep_s = b_rcoset_rep(data, g_s);
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_s, n2);
    crate::word::lemma_concat_word_valid(w, g_s, n2);
    crate::word::lemma_concat_word_valid(w, apply_embedding(b_words(data), h_s), n2);

    if rep_s =~= empty_word() {
        //  Case 1 (subgroup): embed_b(h_s) ≡ g_s → g2_invariant
        lemma_b_rcoset_rep_props(data, g_s);
        crate::word::lemma_inverse_word_valid(rep_s, n2);
        crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n2);
        lemma_subgroup_to_k_word(p2, b_words(data), concat(g_s, inverse_word(rep_s)));
        assert(b_words(data).len() == k_size(data));
        let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(g_s, inverse_word(rep_s)));
        lemma_b_rcoset_decomposition(data, g_s, hw_s);
        crate::presentation_lemmas::lemma_equiv_concat_right(p2, w,
            apply_embedding(b_words(data), h_s), g_s);
        crate::presentation::lemma_equiv_symmetric(p2,
            concat(w, apply_embedding(b_words(data), h_s)), concat(w, g_s));
        lemma_g2_one_shot_g2_invariant(data,
            concat(w, apply_embedding(b_words(data), h_s)), concat(w, g_s), syls_s);
        return;
    }

    //  rep_s ≠ ε. Need b_rcoset_h(g_s) =~= h_s for the equiv chain.
    //  This follows from the precondition g2_one_shot_action(g_s, syls) == (h_s, syls_s)
    //  and the fact that in the prepend branch, h_s = b_rcoset_h(g_s).
    //  In the merge branch, h_s = b_rcoset_h(full). Either way, the chain needs h_s.
    //  For prepend: b_rcoset_h(g_s) is the h-component.
    //  For merge: b_rcoset_h(concat(g_s, c1)) is the h-component.
    //  The embed_hs_equiv_chain only works for the prepend case where h_s = b_rcoset_h(g_s).
    //  For the merge case, we need a different equiv chain.
    //  Let me dispatch based on whether we're in prepend or merge.
    if syls.len() == 0 || syls.first().is_left {
        //  Prepend case: h_s = b_rcoset_h(g_s)
        lemma_g2_embed_hs_equiv_chain(data, w, g_s, h_s);
    }
    lemma_b_rcoset_rep_idempotent(data, g_s);
    lemma_b_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n2);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n2);
    let peeled = concat(concat(w, g_s), inverse_word(rep_s));

    if syls.len() == 0 || syls.first().is_left {
        //  Case 2 (prepend): syls_s = [Syl(false, rep_s)] + syls
        assert(!syls_s.first().is_left);
        assert(word_valid(rep_s, n2));
        lemma_g2_one_shot_g2_invariant(data,
            concat(w, apply_embedding(b_words(data), h_s)), peeled, syls_s);
        if b_rcoset_rep(data, peeled) =~= empty_word() {
            lemma_g2_subgroup_prepend(data, peeled, rep_s, syls, syls_s);
            //  Bridge: concat(peeled, rep_s) ≡ concat(w, g_s)
            crate::word::lemma_concat_word_valid(peeled, rep_s, n2);
            lemma_g2_peeled_bridge(data, concat(w, g_s), rep_s);
            lemma_g2_one_shot_g2_invariant(data, concat(peeled, rep_s), concat(w, g_s), syls);
        } else {
            lemma_g2_prepend_cancel(data, concat(w, g_s), rep_s, syls, syls_s);
        }
        return;
    } else {
        //  Case 3 (merge): delegate to helper
        lemma_g2_one_shot_step_merge(data, w, g_s, h_s, syls, syls_s);
    }
}

///  Case 3 (merge) of g2_one_shot_step: first syl is right.
proof fn lemma_g2_one_shot_step_merge(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(w, data.p2.num_generators),
        word_valid(g_s, data.p2.num_generators),
        word_valid(h_s, k_size(data)),
        g2_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        is_canonical_state(data, h_s, syls_s),
        !(b_rcoset_rep(data, g_s) =~= empty_word()),
        syls.len() > 0 && !syls.first().is_left,
        word_valid(syls.first().rep, data.p2.num_generators),
        b_rcoset_rep(data, syls.first().rep) =~= syls.first().rep,
        !(syls.first().rep =~= empty_word()),
        (syls.drop_first().len() == 0 || syls.drop_first().first().is_left),
    ensures
        g2_one_shot_action(data, concat(w, g_s), syls)
            == g2_one_shot_action(data, concat(w, apply_embedding(b_words(data), h_s)), syls_s),
{
    let rep_s = b_rcoset_rep(data, g_s);
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_s, n2);
    crate::word::lemma_concat_word_valid(w, g_s, n2);
    crate::word::lemma_concat_word_valid(w, apply_embedding(b_words(data), h_s), n2);

    lemma_b_rcoset_rep_idempotent(data, g_s);
    lemma_b_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n2);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n2);

    let c1 = syls.first().rep;
    let full = concat(g_s, c1);
    crate::word::lemma_concat_word_valid(g_s, c1, n2);
    crate::word::lemma_concat_word_valid(w, full, n2);

    lemma_b_rcoset_rep_props(data, full);
    let merged_rep = b_rcoset_rep(data, full);
    crate::word::lemma_inverse_word_valid(merged_rep, n2);
    crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(full, inverse_word(merged_rep)));
    assert(b_words(data).len() == k_size(data));
    let hw_f: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(full, inverse_word(merged_rep)));
    lemma_b_rcoset_decomposition(data, full, hw_f);

    assert(concat(concat(w, g_s), c1) =~= concat(w, full)) by {
        let lhs = concat(concat(w, g_s), c1);
        let rhs = concat(w, full);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }

    let embed_hs = apply_embedding(b_words(data), h_s);

    if merged_rep =~= empty_word() {
        crate::presentation_lemmas::lemma_equiv_concat_right(p2, w, embed_hs, full);
        crate::presentation::lemma_equiv_symmetric(p2, concat(w, embed_hs), concat(w, full));
        lemma_g2_one_shot_g2_invariant(data, concat(w, embed_hs), concat(w, full), syls_s);
        if b_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
            lemma_g2_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
        }
    } else {
        crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n2);
        crate::word::lemma_concat_word_valid(embed_hs, merged_rep, n2);
        crate::presentation_lemmas::lemma_equiv_concat_left(p2,
            concat(embed_hs, merged_rep), full, inverse_word(merged_rep));
        crate::word::lemma_concat_word_valid(concat(embed_hs, merged_rep), inverse_word(merged_rep), n2);
        crate::presentation::lemma_equiv_symmetric(p2,
            concat(concat(embed_hs, merged_rep), inverse_word(merged_rep)),
            concat(full, inverse_word(merged_rep)));
        lemma_right_cancel(p2, embed_hs, merged_rep);
        crate::presentation::lemma_equiv_transitive(p2,
            concat(full, inverse_word(merged_rep)),
            concat(concat(embed_hs, merged_rep), inverse_word(merged_rep)),
            embed_hs);
        crate::presentation::lemma_equiv_symmetric(p2,
            concat(full, inverse_word(merged_rep)), embed_hs);
        crate::presentation_lemmas::lemma_equiv_concat_right(p2, w, embed_hs,
            concat(full, inverse_word(merged_rep)));
        assert(concat(w, concat(full, inverse_word(merged_rep))) =~=
               concat(concat(w, full), inverse_word(merged_rep))) by {
            let lhs = concat(w, concat(full, inverse_word(merged_rep)));
            let rhs = concat(concat(w, full), inverse_word(merged_rep));
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < w.len() as int {} else {
                    let j = k - w.len() as int;
                    if j < full.len() as int {} else {}
                }
            }
        }
        lemma_b_rcoset_rep_idempotent(data, full);
        crate::word::lemma_concat_word_valid(concat(w, full), inverse_word(merged_rep), n2);
        let peeled_mr = concat(concat(w, full), inverse_word(merged_rep));
        lemma_g2_one_shot_g2_invariant(data, concat(w, embed_hs), peeled_mr, syls_s);
        if b_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
            lemma_g2_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
        }
        if b_rcoset_rep(data, peeled_mr) =~= empty_word() {
            lemma_g2_subgroup_prepend(data, peeled_mr, merged_rep, syls.drop_first(), syls_s);
            crate::word::lemma_concat_word_valid(peeled_mr, merged_rep, n2);
            lemma_g2_peeled_bridge(data, concat(w, full), merged_rep);
            lemma_g2_one_shot_g2_invariant(data, concat(peeled_mr, merged_rep), concat(w, full), syls.drop_first());
        } else {
            lemma_g2_prepend_cancel(data, concat(w, full), merged_rep, syls.drop_first(), syls_s);
        }
    }
}

///  G₂ act_word = one-shot: for G₂-local word w, act_word(shift(w), h, syls) = g2_one_shot(concat(w, embed_b(h)), syls).
#[verifier::rlimit(150)]
pub proof fn lemma_act_word_eq_g2_one_shot(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p2.num_generators),
        action_preserves_canonical(data),
    ensures
        act_word(data, shift_word(w, data.p1.num_generators), h, syls)
            == g2_one_shot_action(data,
                concat(w, apply_embedding(b_words(data), h)), syls),
    decreases w.len(),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let w_shifted = shift_word(w, n1);
    let embed_h = apply_embedding(b_words(data), h);

    assert(word_valid(embed_h, n2)) by {
        reveal(presentation_valid);
        assert forall|i: int| 0 <= i < b_words(data).len()
            implies word_valid(#[trigger] b_words(data)[i], n2)
        by { assert(word_valid(data.identifications[i].1, n2)); }
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    }

    if w.len() == 0 {
        assert(w_shifted =~= empty_word()) by {
            assert(w_shifted.len() == 0);
        }
        assert(concat(w, embed_h) =~= embed_h) by {
            assert(w.len() == 0);
            assert(concat(w, embed_h).len() == embed_h.len());
            assert forall|k: int| 0 <= k < embed_h.len()
                implies concat(w, embed_h)[k] == embed_h[k] by {}
        }
        crate::presentation::lemma_equiv_refl(data.p2, embed_h);
        lemma_g2_one_shot_subgroup_restore(data, embed_h, h, syls);
        return;
    }

    let s = w.last();
    let w_prime = w.drop_last();
    let s_shifted = crate::free_product::shift_symbol(s, n1);
    let s_word_shifted = Seq::new(1, |_i: int| s_shifted);

    assert(w_shifted =~= concat(shift_word(w_prime, n1), s_word_shifted)) by {
        let lhs = w_shifted;
        let rhs = concat(shift_word(w_prime, n1), s_word_shifted);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_prime.len() as int {} else {}
        }
    }

    let (h_s, syls_s) = act_sym(data, s_shifted, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    assert(is_canonical_state(data, h_s, syls_s)) by {
        assert(is_canonical_state(data,
            act_word(data, s_word_shifted, h, syls).0,
            act_word(data, s_word_shifted, h, syls).1));
    }

    assert(word_valid(w_prime, n2)) by {
        assert forall|k: int| 0 <= k < w_prime.len()
            implies symbol_valid(#[trigger] w_prime[k], n2) by {
                assert(w_prime[k] == w[k]);
            }
    }

    lemma_act_word_concat(data, shift_word(w_prime, n1), s_word_shifted, h, syls);
    lemma_act_word_eq_g2_one_shot(data, w_prime, h_s, syls_s);

    //  Connect: one_shot(concat(w', embed_b(h_s)), syls_s) = one_shot(concat(w, embed_b(h)), syls)
    let g_s = concat(Seq::new(1, |_i: int| s), embed_h);
    assert(concat(w, embed_h) =~= concat(w_prime, g_s)) by {
        let lhs = concat(w, embed_h);
        let rhs = concat(w_prime, g_s);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_prime.len() as int {} else if k == w_prime.len() as int {} else {
                let j = k - w_prime.len() as int - 1;
            }
        }
    }

    //  Step composition
    crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s), embed_h, n2);
    lemma_g2_one_shot_step(data, w_prime, g_s, h_s, syls, syls_s);
}

///  G₂ relator triviality: if w ≡ ε in G₂, act_word(shift(w), h, syls) = (h, syls).
pub proof fn lemma_g2_relator_acts_trivially(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p2.num_generators),
        equiv_in_presentation(data.p2, w, empty_word()),
        action_preserves_canonical(data),
    ensures
        act_word(data, shift_word(w, data.p1.num_generators), h, syls) == (h, syls),
{
    let n2 = data.p2.num_generators;
    let embed_h = apply_embedding(b_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    lemma_act_word_eq_g2_one_shot(data, w, h, syls);

    crate::word::lemma_concat_word_valid(w, embed_h, n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(data.p2, w, empty_word(), embed_h);
    assert(concat(empty_word(), embed_h) =~= embed_h) by {
        assert(concat(empty_word(), embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(empty_word(), embed_h)[k] == embed_h[k] by {}
    }

    lemma_g2_one_shot_subgroup_restore(data, concat(w, embed_h), h, syls);
}

//  ============================================================
//  Part I1d: Identification relator triviality
//  ============================================================

///  If concat(a, inv(b)) ≡ ε in G, then a ≡ b.
///  Proof: right-multiply by b → a·(inv(b)·b) ≡ a, and (a·inv(b))·b ≡ b.
///  Symmetry + transitivity gives a ≡ b.
proof fn lemma_diff_trivial_implies_equiv(
    p: Presentation, a: Word, b: Word,
)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        equiv_in_presentation(p, concat(a, inverse_word(b)), empty_word()),
    ensures
        equiv_in_presentation(p, a, b),
{
    let n = p.num_generators;
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(b, n);
    crate::word::lemma_concat_word_valid(a, inv_b, n);
    //  Chain 1: (a · inv(b)) · b ≡ ε · b = b
    crate::presentation_lemmas::lemma_equiv_concat_left(p,
        concat(a, inv_b), empty_word(), b);
    //  Chain 2: inv(b) · b ≡ ε → a · (inv(b) · b) ≡ a · ε = a
    crate::presentation_lemmas::lemma_word_inverse_left(p, b);
    crate::presentation_lemmas::lemma_equiv_concat_right(p,
        a, concat(inv_b, b), empty_word());
    //  Both converge on m = concat(concat(a, inv(b)), b):
    //    ≡ b (chain 1) and ≡ a (chain 2, via assoc =~=)
    //  Symmetry + transitivity: a ≡ b
    crate::word::lemma_concat_word_valid(inv_b, b, n);
    crate::word::lemma_concat_word_valid(a, concat(inv_b, b), n);
    //  Z3 needs explicit associativity for Seq concat
    assert(concat(a, concat(inv_b, b)) =~= concat(concat(a, inv_b), b));
    crate::presentation::lemma_equiv_symmetric(p,
        concat(a, concat(inv_b, b)), a);
    crate::presentation::lemma_equiv_transitive(p,
        a, concat(a, concat(inv_b, b)), b);
}

///  Helper: establish embed_b(k_diff) ≡ ε in G₂ from the one-shot decomposition.
proof fn lemma_ident_g2_diff_trivial(
    data: AmalgamatedData, h_prime: Word, k_combined: Word, k_diff: Word, g2_product: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h_prime, k_size(data)),
        word_valid(k_combined, k_size(data)),
        word_valid(k_diff, k_size(data)),
        word_valid(g2_product, data.p2.num_generators),
        k_diff =~= concat(h_prime, inverse_word(k_combined)),
        apply_embedding(b_words(data), k_combined) =~= g2_product,
        b_rcoset_rep(data, g2_product) =~= empty_word(),
        b_rcoset_h(data, g2_product) =~= h_prime,
    ensures
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), k_diff), empty_word()),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    crate::benign::lemma_apply_embedding_concat(b_words(data), h_prime, inverse_word(k_combined));
    crate::benign::lemma_apply_embedding_valid(b_words(data), k_combined, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::benign::lemma_apply_embedding_inverse(b_words(data), k_combined);

    let embed_b_kcomb = apply_embedding(b_words(data), k_combined);
    let embed_b_hprime = apply_embedding(b_words(data), h_prime);
    crate::word::lemma_inverse_word_valid(embed_b_kcomb, n2);
    crate::word::lemma_concat_word_valid(embed_b_hprime, inverse_word(embed_b_kcomb), n2);

    //  Use k_combined directly as h_witness for decomposition (no need for subgroup_to_k_word)
    lemma_b_rcoset_rep_props(data, g2_product);

    //  Precondition for b_rcoset_decomposition: equiv(embed_b(k_combined), concat(g2_product, inv(rep)))
    //  Since rep =~= ε: concat(g2_product, inv(ε)) =~= g2_product =~= embed_b(k_combined)
    assert(inverse_word(b_rcoset_rep(data, g2_product)) =~= empty_word());
    assert(concat(g2_product, inverse_word(b_rcoset_rep(data, g2_product))) =~= g2_product);
    crate::presentation::lemma_equiv_refl(p2, apply_embedding(b_words(data), k_combined));
    lemma_b_rcoset_decomposition(data, g2_product, k_combined);
    //  gives: equiv(concat(embed_b(b_rcoset_h(g2_product)), b_rcoset_rep(g2_product)), g2_product)
    //  Since b_rcoset_h =~= h_prime and rep =~= ε: equiv(embed_b_hprime, embed_b_kcomb)

    //  embed_b(h') · inv(embed_b(k_combined)) ≡ embed_b(k_combined) · inv(embed_b(k_combined)) ≡ ε
    crate::presentation_lemmas::lemma_equiv_concat_left(p2,
        embed_b_hprime, embed_b_kcomb, inverse_word(embed_b_kcomb));
    crate::presentation_lemmas::lemma_word_inverse_right(p2, embed_b_kcomb);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(embed_b_hprime, inverse_word(embed_b_kcomb)),
        concat(embed_b_kcomb, inverse_word(embed_b_kcomb)),
        empty_word());
    //  embed_b(k_diff) =~= concat(embed_b_hprime, inv(embed_b_kcomb)) ≡ ε
    crate::benign::lemma_apply_embedding_valid(b_words(data), k_diff, n2);
}

///  Helper: transfer identification isomorphism → g1_product ≡ embed_a(h).
proof fn lemma_ident_g1_product_equiv(
    data: AmalgamatedData, i: int, h: Word, h_prime: Word,
    k_combined: Word, k_diff: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(h_prime, k_size(data)),
        word_valid(k_combined, k_size(data)),
        word_valid(k_diff, k_size(data)),
        0 <= i < data.identifications.len() as int,
        identifications_isomorphic(data),
        k_diff =~= concat(h_prime, inverse_word(k_combined)),
        k_combined =~= concat(Seq::new(1, |_j: int| Symbol::Inv(i as nat)), h),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), k_diff), empty_word()),
    ensures ({
        let u_i = data.identifications[i].0;
        let embed_a_h = apply_embedding(a_words(data), h);
        let embed_a_hprime = apply_embedding(a_words(data), h_prime);
        equiv_in_presentation(data.p1,
            concat(u_i, embed_a_hprime), embed_a_h)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let u_i = data.identifications[i].0;
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    //  Step A: Transfer embed_b(k_diff) ≡ ε in G₂ → embed_a(k_diff) ≡ ε in G₁
    //  identifications_isomorphic gives the biconditional for any K-word
    //  Z3 should fire the forall with w = k_diff (word_valid(k_diff, k_size(data)) is a precondition)

    //  Step B: embed_a(k_diff) =~= concat(embed_a(h'), inv(embed_a(k_combined)))
    crate::benign::lemma_apply_embedding_concat(a_words(data), h_prime, inverse_word(k_combined));
    crate::benign::lemma_apply_embedding_inverse(a_words(data), k_combined);
    crate::benign::lemma_apply_embedding_valid(a_words(data), k_combined, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    let embed_a_h = apply_embedding(a_words(data), h);
    let embed_a_hprime = apply_embedding(a_words(data), h_prime);
    let embed_a_kcomb = apply_embedding(a_words(data), k_combined);
    crate::word::lemma_inverse_word_valid(embed_a_kcomb, n1);

    //  Step C: embed_a(h') ≡ embed_a(k_combined) (from a·inv(b) ≡ ε → a ≡ b)
    //  embed_a(k_diff) =~= concat(embed_a(h'), inv(embed_a(k_combined))) ≡ ε (from step A+B)
    crate::word::lemma_concat_word_valid(embed_a_hprime, inverse_word(embed_a_kcomb), n1);
    lemma_diff_trivial_implies_equiv(p1, embed_a_hprime, embed_a_kcomb);

    //  Step D: embed_a(k_combined) =~= concat(inv(u_i), embed_a(h))
    let k_inv_i = Seq::new(1, |_j: int| Symbol::Inv(i as nat));
    crate::benign::lemma_apply_embedding_concat(a_words(data), k_inv_i, h);
    assert(apply_embedding(a_words(data), k_inv_i) =~= inverse_word(u_i)) by {
        reveal_with_fuel(crate::benign::apply_embedding, 2);
        assert(a_words(data)[i] == u_i);
    }
    //  So embed_a(k_combined) =~= concat(inv(u_i), embed_a(h))
    //  And from step C: embed_a(h') ≡ embed_a(k_combined) =~= concat(inv(u_i), embed_a(h))

    //  Step E: concat(u_i, embed_a(h')) ≡ embed_a(h)
    crate::word::lemma_inverse_word_valid(u_i, n1);
    crate::word::lemma_concat_word_valid(u_i, embed_a_hprime, n1);
    crate::word::lemma_concat_word_valid(inverse_word(u_i), embed_a_h, n1);
    crate::word::lemma_concat_word_valid(u_i, concat(inverse_word(u_i), embed_a_h), n1);

    //  u_i · embed_a(h') ≡ u_i · embed_a(k_combined) =~= u_i · concat(inv(u_i), embed_a(h))
    crate::presentation_lemmas::lemma_equiv_concat_right(p1,
        u_i, embed_a_hprime, embed_a_kcomb);

    //  u_i · inv(u_i) ≡ ε → (u_i · inv(u_i)) · embed_a(h) ≡ ε · embed_a(h) = embed_a(h)
    crate::presentation_lemmas::lemma_word_inverse_right(p1, u_i);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        concat(u_i, inverse_word(u_i)), empty_word(), embed_a_h);
    //  Z3 needs explicit associativity for Seq concat
    assert(concat(u_i, concat(inverse_word(u_i), embed_a_h))
        =~= concat(concat(u_i, inverse_word(u_i)), embed_a_h));

    //  Chain: concat(u_i, embed_a(h')) ≡ concat(u_i, concat(inv(u_i), embed_a(h))) ≡ embed_a(h)
    crate::presentation::lemma_equiv_transitive(p1,
        concat(u_i, embed_a_hprime),
        concat(u_i, concat(inverse_word(u_i), embed_a_h)),
        embed_a_h);
}

///  Helper: build the K-word difference and prove g1_product ≡ embed_a(h) via isomorphism.
///  Extracted from the main identification relator proof to reduce rlimit pressure.
proof fn lemma_ident_isomorphism_transfer(
    data: AmalgamatedData, i: int, h: Word, h_prime: Word, g2_product: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(h_prime, k_size(data)),
        word_valid(g2_product, data.p2.num_generators),
        0 <= i < data.identifications.len() as int,
        identifications_isomorphic(data),
        b_rcoset_rep(data, g2_product) =~= empty_word(),
        b_rcoset_h(data, g2_product) =~= h_prime,
        apply_embedding(b_words(data),
            concat(Seq::new(1, |_j: int| Symbol::Inv(i as nat)), h)) =~= g2_product,
    ensures ({
        let u_i = data.identifications[i].0;
        let embed_a_h = apply_embedding(a_words(data), h);
        let embed_a_hprime = apply_embedding(a_words(data), h_prime);
        equiv_in_presentation(data.p1, concat(u_i, embed_a_hprime), embed_a_h)
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let v_i = data.identifications[i].1;
    let inv_vi = inverse_word(v_i);
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    let k_inv_i = Seq::new(1, |_j: int| Symbol::Inv(i as nat));
    let k_combined = concat(k_inv_i, h);
    assert(word_valid(k_combined, k_size(data))) by {
        assert(word_valid(k_inv_i, k_size(data))) by {
            assert forall|k: int| 0 <= k < k_inv_i.len()
                implies symbol_valid(#[trigger] k_inv_i[k], k_size(data)) by {}
        }
        assert forall|k: int| 0 <= k < k_combined.len()
            implies symbol_valid(#[trigger] k_combined[k], k_size(data)) by {
                if k < 1 {} else {}
            }
    }

    let k_diff = concat(h_prime, inverse_word(k_combined));
    crate::word::lemma_inverse_word_valid(k_combined, k_size(data));
    assert(word_valid(k_diff, k_size(data))) by {
        assert forall|k: int| 0 <= k < k_diff.len()
            implies symbol_valid(#[trigger] k_diff[k], k_size(data)) by {
                if k < h_prime.len() as int {} else {}
            }
    }

    lemma_ident_g2_diff_trivial(data, h_prime, k_combined, k_diff, g2_product);
    lemma_ident_g1_product_equiv(data, i, h, h_prime, k_combined, k_diff);
}

///  Identification relator triviality: u_i · inv(shift(v_i)) acts trivially.
///  This is the mathematical heart — uses identifications_isomorphic.
///
///  Proof sketch:
///  1. inv(shift(v_i)) acts via G₂: product inv(v_i)·embed_b(h) ∈ B → (h', syls)
///  2. u_i acts via G₁: product u_i·embed_a(h') ∈ A → (h'', syls)
///  3. By identification isomorphism: embed_a(h') ≡ inv(u_i)·embed_a(h) in G₁
///  4. So u_i·embed_a(h') ≡ embed_a(h) → h'' = h
#[verifier::rlimit(300)]
pub proof fn lemma_identification_relator_acts_trivially(
    data: AmalgamatedData, i: int, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        0 <= i < data.identifications.len() as int,
        identifications_isomorphic(data),
        action_preserves_canonical(data),
    ensures
        act_word(data, amalgamation_relator(data, i), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let (u_i, v_i) = (data.identifications[i].0, data.identifications[i].1);
    let shifted_v = shift_word(v_i, n1);
    let relator = amalgamation_relator(data, i);
    //  relator = concat(u_i, inverse_word(shifted_v))
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  Step 1: process inv(shift(v_i)) via G₂ one-shot
    //  inv(shift(v_i)) = shift(inv(v_i)) (shift commutes with inverse)
    //  shift(inv(v_i)) =~= inv(shift(v_i)): shift commutes with inverse
    crate::free_product::lemma_shift_inverse_word(v_i, n1);

    //  Decompose relator: u_i · shift(inv(v_i))
    //  Right-to-left: process shift(inv(v_i)) first, then u_i
    lemma_act_word_concat(data, u_i, inverse_word(shifted_v), h, syls);

    //  inv(v_i) ≡ ε in G₂? No — but inv(v_i) IS in the B-subgroup.
    //  The act_word of shift(inv(v_i)) uses the G₂ one-shot.
    crate::word::lemma_inverse_word_valid(v_i, n2);
    lemma_act_word_eq_g2_one_shot(data, inverse_word(v_i), h, syls);
    //  act_word(shift(inv(v_i)), h, syls) = g2_one_shot(concat(inv(v_i), embed_b(h)), syls)

    let embed_h_b = apply_embedding(b_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    let inv_vi = inverse_word(v_i);
    let g2_product = concat(inv_vi, embed_h_b);
    crate::word::lemma_concat_word_valid(inv_vi, embed_h_b, n2);

    //  g2_product ∈ B → b_rcoset_rep = ε
    lemma_generator_in_generated_subgroup(p2, b_words(data), i);
    lemma_subgroup_inverse(p2, b_words(data), v_i);
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_subgroup_concat(p2, b_words(data), inv_vi, embed_h_b);
    lemma_b_rcoset_in_subgroup(data, g2_product);

    //  g2_one_shot gives (h', syls) where h' = b_rcoset_h(g2_product)
    let (h_prime, syls_prime) = g2_one_shot_action(data, g2_product, syls);
    //  h_prime = b_rcoset_h(g2_product) since rep = ε (subgroup case)
    assert(h_prime == b_rcoset_h(data, g2_product));
    assert(syls_prime == syls);

    //  Establish h_prime is canonical via action_preserves_canonical
    lemma_action_preserves_canonical(data, shift_word(inverse_word(v_i), n1), h, syls);
    //  gives is_canonical_state(data, h_prime, syls_prime) → word_valid(h_prime, k_size(data))

    //  Step 2: u_i via G₁ one-shot on (h', syls')
    assert(word_valid(u_i, n1));
    lemma_act_word_eq_one_shot(data, u_i, h_prime, syls_prime);
    //  act_word(u_i, h', syls') = g1_one_shot(concat(u_i, embed_a(h')), syls')

    //  Key: show concat(u_i, embed_a(h')) ≡ embed_a(h) via K-word isomorphism transfer
    //  embed_b(k_combined) =~= g2_product needs the Seq::new embedding fact
    assert(apply_embedding(b_words(data),
        concat(Seq::new(1, |_j: int| Symbol::Inv(i as nat)), h)) =~= g2_product) by {
        let k_inv_i = Seq::new(1, |_j: int| Symbol::Inv(i as nat));
        crate::benign::lemma_apply_embedding_concat(b_words(data), k_inv_i, h);
        assert(apply_embedding(b_words(data), k_inv_i) =~= inv_vi) by {
            reveal_with_fuel(crate::benign::apply_embedding, 2);
            assert(b_words(data)[i] == v_i);
        }
    }
    lemma_ident_isomorphism_transfer(data, i, h, h_prime, g2_product);

    //  g1_product ≡ embed_a(h) → one_shot_subgroup_restore gives (h, syls)
    let embed_h_prime_a = apply_embedding(a_words(data), h_prime);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    let g1_product = concat(u_i, embed_h_prime_a);
    crate::word::lemma_concat_word_valid(u_i, embed_h_prime_a, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    lemma_one_shot_subgroup_restore(data, g1_product, h, syls_prime);
}

//  ============================================================
//  Part I1e: Assembly — action_well_defined proof
//  ============================================================

///  concat(inv(r), r) acts trivially via inverse pair decomposition.
///  Induction: r = [s] + r_rest → concat(inv(r), r) =~= concat(inv(r_rest), concat(inv_pair(s), r_rest))
///  → remove inv_pair(s) (trivially-acting) → concat(inv(r_rest), r_rest) → IH.
#[verifier::rlimit(200)]
proof fn lemma_inv_r_concat_r_trivial(
    data: AmalgamatedData, r: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        action_preserves_canonical(data),
        word_valid(r, amalgamated_free_product(data).num_generators),
    ensures
        act_word(data, concat(inverse_word(r), r), h, syls) == (h, syls),
    decreases r.len(),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let fp = crate::free_product::free_product(data.p1, data.p2);
    crate::amalgamated_free_product::lemma_add_relators_num_generators(fp,
        crate::amalgamated_free_product::amalgamation_relators(data));
    assert(amalgamated_free_product(data).num_generators == n1 + n2);

    if r.len() == 0 {
        assert(concat(inverse_word(r), r) =~= empty_word());
        lemma_act_word_empty(data, h, syls);
    } else {
        let s = r.first();
        let r_rest = r.drop_first();
        let s_word = Seq::new(1, |_i: int| s);

        //  inv(r) =~= concat(inv(r_rest), [inv(s)]) (from lemma_inverse_concat)
        crate::word::lemma_inverse_concat(s_word, r_rest);

        //  Key =~=: concat(inv(r), r) =~= concat(inv(r_rest), concat(inv_pair(s), r_rest))
        let inv_pair = inverse_pair_word(s);
        assert(concat(inverse_word(r), r)
            =~= concat(inverse_word(r_rest), concat(inv_pair, r_rest)));

        //  The intermediate state after processing r_rest is canonical
        let (sh, ss) = act_word(data, r_rest, h, syls);
        lemma_action_preserves_canonical(data, r_rest, h, syls);

        //  inv_pair(s) acts trivially on the canonical intermediate state
        assert(symbol_valid(s, n1 + n2));
        assert(generator_index(s) < n1 + n2);
        if generator_index(s) < n1 {
            lemma_inverse_pair_g1(data, s, sh, ss);
        } else {
            lemma_inverse_pair_g2(data, s, sh, ss);
        }

        //  Remove the inverse pair
        lemma_insert_trivial_at_state(data,
            inverse_word(r_rest), inv_pair, r_rest, h, syls);

        //  IH: concat(inv(r_rest), r_rest) acts trivially
        assert(word_valid(r_rest, n1 + n2));
        lemma_inv_r_concat_r_trivial(data, r_rest, h, syls);
    }
}

///  If r acts trivially on a specific canonical state, then inv(r) acts trivially on that state too.
///  Proof: concat(inv(r), r) acts trivially (inverse pairs).
///  act_word(concat(inv(r), r), h, syls) = act_word(inv(r), act_word(r, h, syls)) = act_word(inv(r), (h, syls)) = (h, syls).
proof fn lemma_trivial_action_inverse(
    data: AmalgamatedData, r: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        action_preserves_canonical(data),
        word_valid(r, amalgamated_free_product(data).num_generators),
        act_word(data, r, h, syls) == (h, syls),
    ensures
        act_word(data, inverse_word(r), h, syls) == (h, syls),
{
    lemma_inv_r_concat_r_trivial(data, r, h, syls);
    lemma_act_word_concat(data, inverse_word(r), r, h, syls);
}

///  The action is well-defined: all AFP relators and inverse pairs act trivially.
///  The output of a_rcoset_h satisfies the left_h_part fixed-point condition.
///  Uses equiv invariance: embed_a(h) ≡ target_r, and left_h_part is equiv-invariant.
proof fn lemma_a_rcoset_h_left_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures ({
        let h = a_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& left_h_part(data, apply_embedding(a_words(data), h)) =~= h
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    reveal(presentation_valid);

    lemma_a_rcoset_h_satisfiable(data, g, h_witness);
    let h = a_rcoset_h(data, g);
    let rep = a_rcoset_rep(data, g);
    let target_r = concat(g, inverse_word(rep));
    let embed_h = apply_embedding(a_words(data), h);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  target_r ∈ A and word_valid
    lemma_a_rcoset_rep_props(data, g);
    crate::word::lemma_inverse_word_valid(rep, n1);
    crate::word::lemma_concat_word_valid(g, inverse_word(rep), n1);

    //  embed_a(h) ∈ A → both reps = ε
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_h);
    //  target_r ∈ A → both reps = ε
    lemma_in_subgroup_both_reps_eps(data, target_r);

    //  Use left_h_part equiv invariance: embed_a(h) ≡ target_r → left_h_part equal
    //  h_witness for embed_a(h): h (reflexive)
    crate::presentation::lemma_equiv_refl(p1, embed_h);
    //  h_witness for target_r: h (embed_a(h) ≡ target_r)
    //  Need equiv(embed_a(h), concat(inv(left_canonical_rep(embed_h)), embed_h)) = equiv(embed_a(h), embed_h) [since rep=ε]
    //  And equiv(embed_a(h), concat(inv(left_canonical_rep(target_r)), target_r)) = equiv(embed_a(h), target_r) [since rep=ε]
    lemma_left_h_part_equiv_invariant(data, embed_h, target_r, h, h);
    //  left_h_part(embed_a(h)) =~= left_h_part(target_r)

    //  Now: left_h_part(target_r) uses target = target_r (since rep=ε)
    //  And: a_rcoset_h(g) uses target = target_r (by definition)
    //  BOTH left_h_min_len and a_rcoset_h_min_len compute on has_left_h_witness_of_len(data, target_r, l)
    //  (since concat(inv(ε), target_r) =~= target_r =~= concat(g, inv(rep)))
    //  So left_h_part(target_r) and a_rcoset_h(g) pick the same h.
    //  Z3 needs help seeing the internal targets are =~=:
    assert(concat(inverse_word(left_canonical_rep(data, target_r)), target_r) =~= target_r);
    assert(concat(g, inverse_word(a_rcoset_rep(data, g))) =~= target_r);
    //  Therefore: left_h_part(target_r) =~= a_rcoset_h(g) = h
    assert(left_h_part(data, target_r) =~= h);
    //  And from equiv invariance: left_h_part(embed_a(h)) =~= left_h_part(target_r) =~= h
}

///  A-witness transfer: if there's an A-side h-witness of length l for embed_a(h0),
///  then there's a B-side h-witness of length l for embed_b(h0).
///  Uses identifications_isomorphic to transfer between G₁ and G₂ equiv classes.
proof fn lemma_a_witness_to_b_witness(
    data: AmalgamatedData, h0: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(h0, k_size(data)),
        has_left_h_witness_of_len(data, apply_embedding(a_words(data), h0), l),
    ensures
        has_right_h_witness_of_len(data, apply_embedding(b_words(data), h0), l),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    //  Extract A-witness: h' with embed_a(h') ≡ embed_a(h0) in G₁, h'.len() == l
    let h_prime: Word = choose|h: Word| word_valid(h, k) && h.len() == l
        && equiv_in_presentation(p1, apply_embedding(a_words(data), h),
            apply_embedding(a_words(data), h0));

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  embed_a(h') ≡ embed_a(h0) → embed_a(concat(h', inv(h0))) ≡ ε in G₁
    //  Step: a ≡ b → a·b⁻¹ ≡ ε
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h0, n1);
    crate::word::lemma_inverse_word_valid(apply_embedding(a_words(data), h0), n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        apply_embedding(a_words(data), h_prime),
        apply_embedding(a_words(data), h0),
        inverse_word(apply_embedding(a_words(data), h0)));
    crate::presentation_lemmas::lemma_word_inverse_right(p1,
        apply_embedding(a_words(data), h0));
    crate::presentation::lemma_equiv_transitive(p1,
        concat(apply_embedding(a_words(data), h_prime),
               inverse_word(apply_embedding(a_words(data), h0))),
        concat(apply_embedding(a_words(data), h0),
               inverse_word(apply_embedding(a_words(data), h0))),
        empty_word());

    //  embed_a(concat(h', inv(h0))) =~= concat(embed_a(h'), inv(embed_a(h0)))
    crate::word::lemma_inverse_word_valid(h0, k);
    crate::benign::lemma_apply_embedding_concat(a_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(a_words(data), h0);

    //  So: equiv(embed_a(concat(h', inv(h0))), ε) in G₁
    let diff = concat(h_prime, inverse_word(h0));
    assert(word_valid(diff, k)) by {
        assert forall|j: int| 0 <= j < diff.len()
            implies symbol_valid(#[trigger] diff[j], k)
        by { if j < h_prime.len() as int {} else {} }
    }

    //  By identifications_isomorphic: equiv(embed_b(diff), ε) in G₂
    //  (identifications_isomorphic quantifies over word_valid(w, k))

    //  equiv(embed_b(diff), ε) → equiv(embed_b(h'), embed_b(h0)) in G₂
    crate::benign::lemma_apply_embedding_concat(b_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(b_words(data), h0);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h0, n2);
    crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h0), n2);
    crate::word::lemma_concat_word_valid(
        apply_embedding(b_words(data), h_prime),
        inverse_word(apply_embedding(b_words(data), h0)), n2);
    lemma_diff_trivial_implies_equiv(p2,
        apply_embedding(b_words(data), h_prime),
        apply_embedding(b_words(data), h0));

    //  h' is a B-witness: word_valid(h', k) && h'.len() == l && equiv(embed_b(h'), embed_b(h0)) in G₂
    assert(has_right_h_witness_of_len(data, apply_embedding(b_words(data), h0), l));
}

///  Reverse transfer: B-witness → A-witness.
proof fn lemma_b_witness_to_a_witness(
    data: AmalgamatedData, h0: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(h0, k_size(data)),
        has_right_h_witness_of_len(data, apply_embedding(b_words(data), h0), l),
    ensures
        has_left_h_witness_of_len(data, apply_embedding(a_words(data), h0), l),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    let h_prime: Word = choose|h: Word| word_valid(h, k) && h.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), h),
            apply_embedding(b_words(data), h0));

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  embed_b(h') ≡ embed_b(h0) → embed_b(concat(h', inv(h0))) ≡ ε in G₂
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h0, n2);
    crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h0), n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2,
        apply_embedding(b_words(data), h_prime),
        apply_embedding(b_words(data), h0),
        inverse_word(apply_embedding(b_words(data), h0)));
    crate::presentation_lemmas::lemma_word_inverse_right(p2,
        apply_embedding(b_words(data), h0));
    crate::presentation::lemma_equiv_transitive(p2,
        concat(apply_embedding(b_words(data), h_prime),
               inverse_word(apply_embedding(b_words(data), h0))),
        concat(apply_embedding(b_words(data), h0),
               inverse_word(apply_embedding(b_words(data), h0))),
        empty_word());

    crate::word::lemma_inverse_word_valid(h0, k);
    crate::benign::lemma_apply_embedding_concat(b_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(b_words(data), h0);

    let diff = concat(h_prime, inverse_word(h0));
    assert(word_valid(diff, k)) by {
        assert forall|j: int| 0 <= j < diff.len()
            implies symbol_valid(#[trigger] diff[j], k)
        by { if j < h_prime.len() as int {} else {} }
    }

    //  By identifications_isomorphic (reverse direction): equiv(embed_a(diff), ε) in G₁
    crate::benign::lemma_apply_embedding_concat(a_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(a_words(data), h0);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h0, n1);
    crate::word::lemma_inverse_word_valid(apply_embedding(a_words(data), h0), n1);
    crate::word::lemma_concat_word_valid(
        apply_embedding(a_words(data), h_prime),
        inverse_word(apply_embedding(a_words(data), h0)), n1);
    lemma_diff_trivial_implies_equiv(p1,
        apply_embedding(a_words(data), h_prime),
        apply_embedding(a_words(data), h0));

    assert(has_left_h_witness_of_len(data, apply_embedding(a_words(data), h0), l));
}

///  Helper: b_rcoset_h_min_len(embed_b(h)) == h.len() when h = left_h_part(embed_a(h)).
///  Uses A↔B witness transfer + no_pred_below.
#[verifier::rlimit(200)]
proof fn lemma_b_min_len_eq(
    data: AmalgamatedData, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(h, k_size(data)),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
    ensures
        b_rcoset_h_min_len(data, apply_embedding(b_words(data), h)) == h.len(),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    let embed_b_h = apply_embedding(b_words(data), h);
    let embed_a_h = apply_embedding(a_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  embed_b(h) ∈ B → rep = ε
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_b_h);

    let target_bh = concat(embed_b_h, inverse_word(b_rcoset_rep(data, embed_b_h)));
    assert(target_bh =~= embed_b_h);

    //  h is a B-witness at h.len() → min_len <= h.len()
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    let pred_b = |l2: nat| has_right_h_witness_of_len(data, target_bh, l2);
    assert(pred_b(h.len() as nat));
    lemma_nat_well_ordering(pred_b, h.len() as nat);

    //  h.len() is the A-min-len → no B-witness shorter than h.len()
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_a_h);
    let target_lh = concat(inverse_word(left_canonical_rep(data, embed_a_h)), embed_a_h);
    assert(target_lh =~= embed_a_h);
    crate::presentation::lemma_equiv_refl(p1, embed_a_h);
    lemma_left_h_part_full_props(data, embed_a_h, h);
    let pred_a = |l2: nat| has_left_h_witness_of_len(data, target_lh, l2);
    assert(pred_a(h.len() as nat));
    lemma_nat_well_ordering(pred_a, h.len() as nat);

    //  Transfer: pred_b(l) → pred_a(l)
    assert forall|l: nat| pred_b(l) implies #[trigger] pred_a(l) by {
        lemma_b_witness_to_a_witness(data, h, l);
    }
    lemma_no_pred_below_transfer(pred_a, pred_b, h.len() as nat);
    //  no_pred_below(pred_b, h.len()) + pred_b(h.len()) → h.len() satisfies the choose predicate

    //  Uniqueness: b_rcoset_h_min_len's choose also satisfies, mutual exclusion → equal
    let bl = b_rcoset_h_min_len(data, embed_b_h);
    //  bl satisfies the choose predicate (from satisfiability via nat_well_ordering)
    //  → pred_b(bl) && no_pred_below(pred_b, bl)
    //  Mutual exclusion: bl >= h.len() (from no_pred_below(pred_b, bl) + pred_b(h.len()))
    //                    h.len() >= bl (from no_pred_below(pred_b, h.len()) + pred_b(bl))
    lemma_no_pred_below_implies_ge(pred_b, h.len() as nat, bl);
    lemma_no_pred_below_implies_ge(pred_b, bl, h.len() as nat);
}

///  a_rcoset_h output satisfies the b_rcoset_h fixed-point condition.
///  Uses: witness transfer (A↔B) + lex rank injectivity to show the B-choose gives h.
#[verifier::rlimit(200)]
pub proof fn lemma_a_rcoset_h_b_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures ({
        let h = a_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    lemma_a_rcoset_h_satisfiable(data, g, h_witness);
    let h = a_rcoset_h(data, g);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    let embed_b_h = apply_embedding(b_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  embed_b(h) ∈ B → b_rcoset_rep = ε
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_b_h);

    //  h is a B-witness → b_rcoset_h satisfiable
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    lemma_b_rcoset_h_satisfiable(data, embed_b_h, h);
    let h_b = b_rcoset_h(data, embed_b_h);
    //  h_b: word_valid, h_b.len() == b_rcoset_h_min_len, equiv(embed_b(h_b), embed_b_h)
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_b, n2);

    //  Strategy: show h and h_b have same length AND same lex rank → same word (by injectivity)

    //  Step 1: h_b.len() <= h.len() (h is a B-candidate, h_b is B-min-len)
    //  (This follows from b_rcoset_h_min_len being the minimum.)

    //  Step 2: h.len() <= h_b.len() (transfer h_b to A-side, h is A-min-len)
    assert(has_right_h_witness_of_len(data, embed_b_h, h_b.len() as nat));
    lemma_b_witness_to_a_witness(data, h, h_b.len() as nat);
    //  Now: has_left_h_witness_of_len(embed_a(h), h_b.len())

    //  Step 3: length equality
    lemma_a_rcoset_h_left_canonical(data, g, h_witness);
    lemma_b_min_len_eq(data, h);
    //  Get h_b's full props to connect h_b.len() to b_rcoset_h_min_len
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    lemma_b_rcoset_h_full_props(data, embed_b_h, h);
    assert(h_b.len() == h.len());
    let target_bh = concat(embed_b_h, inverse_word(b_rcoset_rep(data, embed_b_h)));
    assert(target_bh =~= embed_b_h);
    let hl = h.len() as nat;

    //  Setup for lex transfer
    let embed_a_h = apply_embedding(a_words(data), h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_a_h);
    crate::presentation::lemma_equiv_refl(p1, embed_a_h);
    lemma_left_h_part_full_props(data, embed_a_h, h);
    let target_lh = concat(inverse_word(left_canonical_rep(data, embed_a_h)), embed_a_h);
    assert(target_lh =~= embed_a_h);

    //  Step 4: Same lex rank (both are min-lex at the same length for the same equiv class)
    //  Transfer at rank level: the rank-level B-witness at h_b's lex ↔ A-witness at same lex
    //  Since A and B witnesses at each (len, rank) coincide, the min-lex must agree too.
    //  h has lex == left_h_min_lex(embed_a_h) and h_b has lex == b_rcoset_h_min_lex(embed_b_h).
    //  Both are min-lex over the same set of K-words → same lex → same word.

    //  Use lex rank injectivity: same length + same lex rank → same word
    //  h and h_b satisfy the same B-choose predicate at (len, lex)
    //  h_b IS the choose result → h_b has len == bl and lex == br
    //  h satisfies the B-predicate too (equiv(embed_b(h), embed_b_h) by reflexivity)
    //  Both have len == bl. If lex(h) == lex(h_b), then h =~= h_b by injectivity.
    //  lex(h_b) == br (from choose). lex(h) >= br (from min-lex: h_b is min).
    //  But also: h is in the B-witness set at (bl, lex(h)). Transfer to A-side:
    //  h is in A-witness set at (bl, lex(h)). h is the A-min-lex at length bl.
    //  Step 4: Same lex rank — same pattern at the rank level
    //  A-side: has_left_h_witness_of_len_rank(target_lh, h.len(), lex(h))
    //  B-side: has_right_h_witness_of_len_rank(target_bh, h.len(), lex(h_b))
    //  Transfer at rank level: pred_b_rank(r) → pred_a_rank(r)
    //  + no_pred_below on A-side → no_pred_below on B-side
    //  → min lex for B == min lex for A == lex(h)

    let hl = h.len() as nat;
    let pred_a_rank = |r: nat| has_left_h_witness_of_len_rank(data, target_lh, hl, r);
    let pred_b_rank = |r: nat| has_right_h_witness_of_len_rank(data, target_bh, hl, r);

    //  h is a B-witness at (hl, lex(h))
    let hr = word_lex_rank_base(h, h_lex_base(data));
    assert(pred_b_rank(hr));

    //  Transfer: pred_b_rank(r) → pred_a_rank(r)
    assert forall|r: nat| pred_b_rank(r) implies #[trigger] pred_a_rank(r) by {
        //  Extract h'' from B-witness: embed_b(h'') ≡ embed_b(h), h''.len() == hl, lex == r
        let h_r: Word = choose|hw: Word| word_valid(hw, k) && hw.len() == hl
            && word_lex_rank_base(hw, h_lex_base(data)) == r
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw), target_bh);
        //  Transfer h_r from B to A
        crate::benign::lemma_apply_embedding_valid(b_words(data), h_r, n2);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
        crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h), n2);
        crate::presentation_lemmas::lemma_equiv_concat_left(p2,
            apply_embedding(b_words(data), h_r), apply_embedding(b_words(data), h),
            inverse_word(apply_embedding(b_words(data), h)));
        crate::presentation_lemmas::lemma_word_inverse_right(p2, apply_embedding(b_words(data), h));
        crate::presentation::lemma_equiv_transitive(p2,
            concat(apply_embedding(b_words(data), h_r), inverse_word(apply_embedding(b_words(data), h))),
            concat(apply_embedding(b_words(data), h), inverse_word(apply_embedding(b_words(data), h))),
            empty_word());
        crate::word::lemma_inverse_word_valid(h, k);
        crate::benign::lemma_apply_embedding_concat(b_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(b_words(data), h);
        let diff = concat(h_r, inverse_word(h));
        assert(word_valid(diff, k)) by {
            assert forall|j: int| 0 <= j < diff.len()
                implies symbol_valid(#[trigger] diff[j], k) by {
                    if j < h_r.len() as int {} else {}
                }
        }
        //  identifications_isomorphic: embed_b(diff) ≡ ε → embed_a(diff) ≡ ε
        //  → embed_a(h_r) ≡ embed_a(h) → h_r is an A-witness
        crate::benign::lemma_apply_embedding_concat(a_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(a_words(data), h);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_r, n1);
        crate::word::lemma_inverse_word_valid(apply_embedding(a_words(data), h), n1);
        crate::word::lemma_concat_word_valid(
            apply_embedding(a_words(data), h_r),
            inverse_word(apply_embedding(a_words(data), h)), n1);
        lemma_diff_trivial_implies_equiv(p1,
            apply_embedding(a_words(data), h_r), embed_a_h);
    }

    //  Transfer no_smaller_h_lex from A to B using the dedicated transfer lemma
    //  A-side: no_smaller_h_lex(target_lh, hl, hr) — from left_h_part_full_props
    //  Need: B-rank transfer forall
    assert forall|r2: nat| has_right_h_witness_of_len_rank(data, target_bh, hl, r2)
        implies #[trigger] has_left_h_witness_of_len_rank(data, target_lh, hl, r2)
    by {
        //  Same proof as pred_b_rank → pred_a_rank but at rank level
        let h_r: Word = choose|hw: Word| word_valid(hw, k) && hw.len() == hl
            && word_lex_rank_base(hw, h_lex_base(data)) == r2
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw), target_bh);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h_r, n2);
        crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h), n2);
        crate::presentation_lemmas::lemma_equiv_concat_left(p2,
            apply_embedding(b_words(data), h_r), apply_embedding(b_words(data), h),
            inverse_word(apply_embedding(b_words(data), h)));
        crate::presentation_lemmas::lemma_word_inverse_right(p2, apply_embedding(b_words(data), h));
        crate::presentation::lemma_equiv_transitive(p2,
            concat(apply_embedding(b_words(data), h_r), inverse_word(apply_embedding(b_words(data), h))),
            concat(apply_embedding(b_words(data), h), inverse_word(apply_embedding(b_words(data), h))),
            empty_word());
        crate::word::lemma_inverse_word_valid(h, k);
        crate::benign::lemma_apply_embedding_concat(b_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(b_words(data), h);
        let diff = concat(h_r, inverse_word(h));
        assert(word_valid(diff, k)) by {
            assert forall|j: int| 0 <= j < diff.len()
                implies symbol_valid(#[trigger] diff[j], k) by {
                    if j < h_r.len() as int {} else {}
                }
        }
        crate::benign::lemma_apply_embedding_concat(a_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(a_words(data), h);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_r, n1);
        crate::word::lemma_inverse_word_valid(embed_a_h, n1);
        crate::word::lemma_concat_word_valid(
            apply_embedding(a_words(data), h_r), inverse_word(embed_a_h), n1);
        lemma_diff_trivial_implies_equiv(p1, apply_embedding(a_words(data), h_r), embed_a_h);
    }
    //  Establish no_smaller_h_lex on A-side from left_h_min_lex satisfiability
    lemma_left_h_min_lex_satisfiable(data, embed_a_h, h);
    assert(no_smaller_h_lex(data, target_lh, hl, hr));
    lemma_no_smaller_h_lex_transfer(data, target_lh, target_bh, hl, hr);

    //  Now: pred_b_rank(hr) && no_smaller_h_lex_g2(target_bh, hl, hr)
    //  Assert is_min_h_lex_g2 to establish the unique B-min-lex
    assert(is_min_h_lex_g2(data, target_bh, hl, hr));
    //  Scan gives us the satisfiability of the min-lex choose
    assert(no_smaller_h_lex_g2(data, target_bh, hl, 0nat));
    lemma_scan_min_h_lex_g2(data, target_bh, hl, 0, hr);
    //  Now b_rcoset_h_min_lex(embed_b_h) is satisfiable
    //  And hr satisfies both has_.. and no_smaller → hr IS the min → lex(h_b) == hr
    //  From the choose: h_b.lex == b_rcoset_h_min_lex. And b_rcoset_h_min_lex == hr (unique min).
    //  Use no_smaller_h_lex_g2 uniqueness: if two values satisfy is_min, they're equal
    //  Extract br's full choose properties via b_rcoset_h_full_props
    lemma_b_rcoset_h_full_props(data, embed_b_h, h);
    //  full_props ensures: h_b.len() == b_rcoset_h_min_len(embed_b_h) = hl
    //                     word_lex_rank_base(h_b, base) == b_rcoset_h_min_lex(embed_b_h) = br
    //                     equiv(embed_b(h_b), target_bh)
    //  Extract br (full_props already called above)
    let br = b_rcoset_h_min_lex(data, embed_b_h);
    assert(h_b.len() == hl);
    assert(word_lex_rank_base(h_b, h_lex_base(data)) == br);
    assert(has_right_h_witness_of_len_rank(data, target_bh, hl, br));
    assert(no_smaller_h_lex_g2(data, target_bh, hl, 0nat));
    lemma_scan_min_h_lex_g2(data, target_bh, hl, 0, br);
    //  hr has witness (h is B-witness at hr)
    assert(has_right_h_witness_of_len_rank(data, target_bh, hl, hr));
    //  Mutual exclusion: hr >= br AND br >= hr → hr == br
    lemma_no_smaller_g2_implies_ge(data, target_bh, hl, hr, br);
    lemma_no_smaller_g2_implies_ge(data, target_bh, hl, br, hr);

    //  Step 5: Apply lex rank injectivity
    assert(h_lex_base(data) > 0);
    assert forall|j: int| 0 <= j < h.len() implies
        crate::todd_coxeter::symbol_to_column(#[trigger] h[j]) < h_lex_base(data)
    by { assert(symbol_valid(h[j], k)); }
    assert forall|j: int| 0 <= j < h_b.len() implies
        crate::todd_coxeter::symbol_to_column(#[trigger] h_b[j]) < h_lex_base(data)
    by { assert(symbol_valid(h_b[j], k)); }
    lemma_word_lex_rank_base_injective(h, h_b, h_lex_base(data));
}

///  B-side self-consistency: b_rcoset_h output satisfies b_rcoset_h fixed point.
///  Mirrors lemma_a_rcoset_h_left_canonical for G₂.
pub proof fn lemma_b_rcoset_h_b_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    lemma_b_rcoset_h_satisfiable(data, g, h_witness);
    let h = b_rcoset_h(data, g);
    let rep = b_rcoset_rep(data, g);
    let target_r = concat(g, inverse_word(rep));
    let embed_h = apply_embedding(b_words(data), h);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    lemma_b_rcoset_rep_props(data, g);
    crate::word::lemma_inverse_word_valid(rep, n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(rep), n2);

    //  embed_b(h) ∈ B → both reps = ε
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_h);
    //  target_r ∈ B
    lemma_b_rcoset_in_subgroup(data, target_r);

    //  Use b_rcoset_h equiv invariance: embed_b(h) ≡ target_r → b_rcoset_h equal
    crate::presentation::lemma_equiv_refl(p2, embed_h);
    lemma_b_rcoset_h_equiv_invariant(data, embed_h, target_r, h, h);
    //  b_rcoset_h(embed_b(h)) =~= b_rcoset_h(target_r)

    //  b_rcoset_h(target_r) uses same target as b_rcoset_h(g) when both ∈ B
    assert(concat(inverse_word(b_rcoset_rep(data, target_r)), target_r) =~= target_r);
    assert(concat(g, inverse_word(b_rcoset_rep(data, g))) =~= target_r);
    assert(b_rcoset_h(data, target_r) =~= h);
}

///  B-side cross: b_rcoset_h output satisfies left_h_part fixed point.
///  Mirrors lemma_a_rcoset_h_b_canonical (uses identifications_isomorphic for A↔B transfer).
#[verifier::rlimit(200)]
proof fn lemma_b_rcoset_h_left_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& left_h_part(data, apply_embedding(a_words(data), h)) =~= h
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    lemma_b_rcoset_h_satisfiable(data, g, h_witness);
    let h = b_rcoset_h(data, g);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    //  Step 3: left_h_min_len(embed_a(h)) == h.len()
    //  b_rcoset_h_b_canonical gives: b_rcoset_h(embed_b(h)) =~= h
    lemma_b_rcoset_h_b_canonical(data, g, h_witness);

    //  A-min-len == h.len() (symmetric to lemma_b_min_len_eq but A↔B swapped)
    //  h is an A-witness at h.len()
    let embed_a_h = apply_embedding(a_words(data), h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_a_h);
    let target_lh = concat(inverse_word(left_canonical_rep(data, embed_a_h)), embed_a_h);
    assert(target_lh =~= embed_a_h);
    crate::presentation::lemma_equiv_refl(p1, embed_a_h);

    let pred_a = |l2: nat| has_left_h_witness_of_len(data, target_lh, l2);
    assert(pred_a(h.len() as nat));
    lemma_nat_well_ordering(pred_a, h.len() as nat);

    //  Transfer: pred_a(l) → pred_b(l)
    let embed_b_h = apply_embedding(b_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_b_h);
    let target_bh = concat(embed_b_h, inverse_word(b_rcoset_rep(data, embed_b_h)));
    assert(target_bh =~= embed_b_h);
    let pred_b = |l2: nat| has_right_h_witness_of_len(data, target_bh, l2);

    assert forall|l: nat| pred_a(l) implies #[trigger] pred_b(l) by {
        lemma_a_witness_to_b_witness(data, h, l);
    }

    //  B-side: h.len() is the B-min-len (h = b_rcoset_h(embed_b_h) =~= h by b_canonical)
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    lemma_b_rcoset_h_full_props(data, embed_b_h, h);
    let bl = b_rcoset_h_min_len(data, embed_b_h);
    assert(bl == h.len());

    //  no_pred_below(pred_b, h.len()) → transfer → no_pred_below(pred_a, h.len())
    assert(pred_b(h.len() as nat));
    lemma_nat_well_ordering(pred_b, h.len() as nat);
    assert forall|l: nat| pred_a(l) implies #[trigger] pred_b(l) by {
        lemma_a_witness_to_b_witness(data, h, l);
    }
    //  But I need the REVERSE: no_pred_below(pred_b, h.len()) → transfer to A
    //  pred_a(l) → pred_b(l), so !pred_b(l) → !pred_a(l)
    //  no_pred_below(pred_b, h.len()) → no_pred_below(pred_a, h.len())
    //  Wait, that's backwards. I need pred_b → pred_a for the transfer.
    //  Actually: I need no_pred_below on A at h.len().
    //  From the B-side: pred_b has no_pred_below at bl = h.len().
    //  And pred_a(l) → pred_b(l). Contrapositive: !pred_b(l) → !pred_a(l).
    //  So no_pred_below(pred_b, h.len()) → no_pred_below(pred_a, h.len()).
    //  But lemma_no_pred_below_transfer goes: no_pred_below(pred1, n) + (pred2 → pred1) → no_pred_below(pred2, n)
    //  I need: no_pred_below(pred_b, h.len()) + (pred_a → pred_b) → no_pred_below(pred_a, h.len())
    //  This is: no_pred_below(major, n) + (minor → major) → no_pred_below(minor, n)
    //  Yes! pred_a is "minor" (implies pred_b "major"). no_pred_below(pred_b) → no_pred_below(pred_a).
    lemma_no_pred_below_transfer(pred_b, pred_a, h.len() as nat);

    //  Now: pred_a(h.len()) && no_pred_below(pred_a, h.len())
    //  Uniqueness: left_h_min_len(embed_a_h) == h.len()
    let al = left_h_min_len(data, embed_a_h);
    lemma_no_pred_below_implies_ge(pred_a, h.len() as nat, al);
    lemma_no_pred_below_implies_ge(pred_a, al, h.len() as nat);
    assert(al == h.len());

    //  Now left_h_part_full_props: left_h_part(embed_a_h) has len = al = h.len()
    lemma_left_h_part_full_props(data, embed_a_h, h);

    //  Same lex (symmetric rank transfer)
    let hr = word_lex_rank_base(h, h_lex_base(data));
    let ar = left_h_min_lex(data, embed_a_h);
    lemma_left_h_min_lex_satisfiable(data, embed_a_h, h);
    //  is_min_h_lex(target_lh, al, ar) → no_smaller_h_lex(target_lh, al, ar)
    assert(no_smaller_h_lex(data, target_lh, al, ar));
    assert(has_left_h_witness_of_len_rank(data, target_lh, al, hr));
    lemma_no_smaller_h_lex_implies_ge(data, target_lh, al, ar, hr);
    //  ar <= hr. Also hr <= ar (h is A-witness, ar is A-min). Let me get hr <= ar.
    assert(has_left_h_witness_of_len_rank(data, target_lh, al, ar));
    //  hr is the B-min-lex at bl = h.len(). Transfer: A-rank → B-rank at same len.
    //  Actually simpler: h IS the left_h_part output, so hr == ar.
    //  From full_props: word_lex_rank_base(left_h_part(embed_a_h), base) == ar
    //  And left_h_part(embed_a_h).len() == al == h.len()
    //  Need: left_h_part(embed_a_h) =~= h. This follows from lex injectivity!
    let h_a = left_h_part(data, embed_a_h);
    assert(h_a.len() == h.len());
    assert(word_lex_rank_base(h_a, h_lex_base(data)) == ar);

    //  Both h and h_a: same length, A-witnesses, h_a is min-lex
    //  h is also an A-witness at (h.len(), hr) → ar <= hr
    //  h_a is min-lex → no_smaller_h_lex at ar → hr >= ar (from above)
    //  And ar is A-min → ar <= hr
    //  So ar == hr (both are min at same length)
    //  Actually: ar is the min, hr is h's rank. h is a valid A-witness.
    //  no_smaller_h_lex at ar + h is witness at hr → hr >= ar.
    //  And no_smaller_h_lex at hr... we need the reverse.
    //  Let's use lex injectivity on h_a and h:
    //  Same length, ar == hr (need this), base valid → h_a =~= h.
    //  But we don't know ar == hr yet...
    //  Actually: from full_props, the choose for left_h_min_lex gives
    //  ar = left_h_min_lex. And the choose for left_h_part uses ar.
    //  h_a satisfies: equiv(embed_a(h_a), target_lh). And h satisfies the same.
    //  h_a has rank ar. h has rank hr. ar <= hr (from no_smaller at ar + h is witness at hr).
    //  Need hr <= ar. This needs no_smaller at hr.
    //  But we don't have no_smaller_h_lex at hr directly.
    //  Instead: use the B-side. h has B-min-lex at h.len() too. Transfer...
    //  This is getting circular. Let me use a simpler approach.
    //  Since pred_a == pred_b on equiv classes (from iso), and the lex is on K-words (same for both),
    //  the min-lex should be the same.
    //  Actually, just use the same pattern as lemma_a_rcoset_h_b_canonical.
    //  Full_props gives h_a.lex == ar. I need h.lex == ar too.
    //  From B-side full_props: h.lex == b_rcoset_h_min_lex(embed_b_h).
    //  Transfer at rank level: B-min-lex == A-min-lex.
    //  This is the same chain as in the A→B proof. Let me just assert.

    //  Actually let me try: h is the B-choose result, so it has B-min-lex.
    //  Transfer at rank level makes B-min-lex == A-min-lex. So h.lex == A-min-lex == ar.
    //  Then h_a and h have same length and same lex → same word by injectivity.
    //  hr >= ar (from no_smaller_h_lex at ar + h is A-witness at hr)
    //  ar >= hr: from B-side, hr is B-min-lex. Transfer B-rank to A gives A-witness at hr.
    //    no_smaller_h_lex at ar means ar <= any A-witness rank. So ar <= hr... wait, that's same direction.
    //    Actually: the B-full_props gives hr as the B-min-lex at bl.
    //    And pred_b_rank(ar) via transfer. So ar >= br_min = hr.
    //    Wait, br_min = b_rcoset_h_min_lex(embed_b_h) = hr (from B full_props: h.lex == min_lex).
    //    And no_smaller_h_lex_g2(target_bh, bl, hr). A-witness at ar exists.
    //    Transfer: A-rank ar → B-rank ar. So has_right_h_witness_of_len_rank(target_bh, bl, ar).
    //    no_smaller_g2 at hr + B-witness at ar → ar >= hr.
    //  Combined: ar >= hr AND hr >= ar → ar == hr.
    //  h is the B-choose result with lex hr. h_a is the A-choose result with lex ar.
    //  Both at same length. h satisfies A-predicate (equiv(embed_a(h), target_lh) from iso transfer).
    //  no_smaller_h_lex at ar → ar <= hr.
    //  h_a satisfies B-predicate (equiv(embed_b(h_a), target_bh) from iso transfer).
    //  no_smaller_h_lex_g2 at hr → hr <= ar. (need no_smaller_g2 at hr)
    //  But I don't have no_smaller_h_lex_g2 at hr in this context.
    //  Let me use the B full_props which should give no_smaller_g2.
    let br = b_rcoset_h_min_lex(data, embed_b_h);
    assert(br == hr); //  h IS b_rcoset_h, so h.lex == b_min_lex
    //  no_smaller_g2 at br = hr
    lemma_scan_min_h_lex_g2(data, target_bh, bl, 0, hr);
    //  Transfer: A-witness at ar → B-witness at ar
    assert(has_left_h_witness_of_len_rank(data, target_lh, al, ar));
    assert forall|r2: nat| has_left_h_witness_of_len_rank(data, target_lh, al, r2)
        implies #[trigger] has_right_h_witness_of_len_rank(data, target_bh, bl, r2)
    by {
        let h_r: Word = choose|hw: Word| word_valid(hw, k) && hw.len() == al
            && word_lex_rank_base(hw, h_lex_base(data)) == r2
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw), target_lh);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_r, n1);
        crate::word::lemma_inverse_word_valid(embed_a_h, n1);
        crate::presentation_lemmas::lemma_equiv_concat_left(p1,
            apply_embedding(a_words(data), h_r), embed_a_h, inverse_word(embed_a_h));
        crate::presentation_lemmas::lemma_word_inverse_right(p1, embed_a_h);
        crate::presentation::lemma_equiv_transitive(p1,
            concat(apply_embedding(a_words(data), h_r), inverse_word(embed_a_h)),
            concat(embed_a_h, inverse_word(embed_a_h)), empty_word());
        crate::word::lemma_inverse_word_valid(h, k);
        crate::benign::lemma_apply_embedding_concat(a_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(a_words(data), h);
        let diff = concat(h_r, inverse_word(h));
        assert(word_valid(diff, k)) by {
            assert forall|j: int| 0 <= j < diff.len()
                implies symbol_valid(#[trigger] diff[j], k) by {
                    if j < h_r.len() as int {} else {}
                }
        }
        crate::benign::lemma_apply_embedding_concat(b_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(b_words(data), h);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h_r, n2);
        crate::word::lemma_inverse_word_valid(embed_b_h, n2);
        crate::word::lemma_concat_word_valid(
            apply_embedding(b_words(data), h_r), inverse_word(embed_b_h), n2);
        lemma_diff_trivial_implies_equiv(p2, apply_embedding(b_words(data), h_r), embed_b_h);
    }
    lemma_no_smaller_g2_implies_ge(data, target_bh, bl, hr, ar);
    //  ar >= hr  AND  hr >= ar  →  ar == hr
    assert(ar == hr);

    assert(h_a =~= h) by {
        assert(h_a.len() == h.len());
        assert(word_lex_rank_base(h_a, h_lex_base(data)) == word_lex_rank_base(h, h_lex_base(data)));
        assert(h_lex_base(data) > 0);
        assert forall|j: int| 0 <= j < h.len() implies
            crate::todd_coxeter::symbol_to_column(#[trigger] h[j]) < h_lex_base(data)
        by { assert(symbol_valid(h[j], k)); }
        assert forall|j: int| 0 <= j < h_a.len() implies
            crate::todd_coxeter::symbol_to_column(#[trigger] h_a[j]) < h_lex_base(data)
        by { assert(symbol_valid(h_a[j], k)); }
        lemma_word_lex_rank_base_injective(h_a, h, h_lex_base(data));
    }
}

///  act_sym preserves canonical: the h-part is canonical from the 4 lemmas,
///  and syllable structure is preserved by the action definition.
///  For now, proves the h-part conditions. Syllable conditions follow from
///  the action spec (each rep is a choose result = canonical, alternation maintained).
///
///  This lemma + induction on word length gives action_preserves_canonical.
///  To keep the proof tractable, we focus on the h-part conditions (the hard part)
///  and note that syllable conditions are structural.
#[verifier::rlimit(300)]
proof fn lemma_act_sym_h_canonical(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        symbol_valid(s, data.p1.num_generators + data.p2.num_generators),
    ensures ({
        let (h_out, _syls_out) = act_sym(data, s, h, syls);
        &&& word_valid(h_out, k_size(data))
        &&& left_h_part(data, apply_embedding(a_words(data), h_out)) =~= h_out
        &&& b_rcoset_h(data, apply_embedding(b_words(data), h_out)) =~= h_out
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    if generator_index(s) < n1 {
        //  G₁ symbol: act_left_sym
        let embed_h = apply_embedding(a_words(data), h);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s), embed_h, n1);

        //  h_witness for a_rcoset_h(product):
        //  concat(product, inv(rep)) ∈ A → subgroup_to_k_word
        lemma_a_rcoset_rep_props(data, product);
        let rep = a_rcoset_rep(data, product);
        crate::word::lemma_inverse_word_valid(rep, n1);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep), n1);
        lemma_subgroup_to_k_word(p1, a_words(data), concat(product, inverse_word(rep)));
        let hw: Word = choose|hw: Word| word_valid(hw, k)
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(product, inverse_word(rep)));

        //  a_rcoset_h output is canonical for both A and B
        lemma_a_rcoset_h_left_canonical(data, product, hw);
        lemma_a_rcoset_h_b_canonical(data, product, hw);

        //  The action's h_out = a_rcoset_h(product) in ALL subcases (subgroup/prepend/merge)
        //  because act_left_sym uses a_rcoset_h for the subgroup/prepend cases,
        //  and a_rcoset_h of the full product for merge cases.
        //  Actually: for merge, h_out = a_rcoset_h(full_product) where full_product = concat(product, c1).
        //  Need a DIFFERENT h_witness for that case!
        //  For now, the subgroup case covers h_out = a_rcoset_h(product).

        //  Merge case: h_out = a_rcoset_h(concat(product, syls.first().rep))
        if !(rep =~= empty_word()) && syls.len() > 0 && syls.first().is_left {
            let full_product = concat(product, syls.first().rep);
            crate::word::lemma_concat_word_valid(product, syls.first().rep, n1);
            lemma_a_rcoset_rep_props(data, full_product);
            let merged_rep = a_rcoset_rep(data, full_product);
            crate::word::lemma_inverse_word_valid(merged_rep, n1);
            crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n1);
            lemma_subgroup_to_k_word(p1, a_words(data), concat(full_product, inverse_word(merged_rep)));
            let hw2: Word = choose|hw: Word| word_valid(hw, k)
                && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                    concat(full_product, inverse_word(merged_rep)));
            lemma_a_rcoset_h_left_canonical(data, full_product, hw2);
            lemma_a_rcoset_h_b_canonical(data, full_product, hw2);
        }
    } else {
        //  G₂ symbol: act_right_sym (mirrors G₁ with b_rcoset)
        let s_local = unshift_sym(s, n1);
        let embed_h = apply_embedding(b_words(data), h);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
        let product = concat(Seq::new(1, |_i: int| s_local), embed_h);
        crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s_local), embed_h, n2);

        lemma_b_rcoset_rep_props(data, product);
        let rep = b_rcoset_rep(data, product);
        crate::word::lemma_inverse_word_valid(rep, n2);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep), n2);
        lemma_subgroup_to_k_word(p2, b_words(data), concat(product, inverse_word(rep)));
        let hw: Word = choose|hw: Word| word_valid(hw, k)
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(product, inverse_word(rep)));

        lemma_b_rcoset_h_b_canonical(data, product, hw);
        lemma_b_rcoset_h_left_canonical(data, product, hw);

        if !(rep =~= empty_word()) && syls.len() > 0 && !syls.first().is_left {
            let full_product = concat(product, syls.first().rep);
            crate::word::lemma_concat_word_valid(product, syls.first().rep, n2);
            lemma_b_rcoset_rep_props(data, full_product);
            let merged_rep = b_rcoset_rep(data, full_product);
            crate::word::lemma_inverse_word_valid(merged_rep, n2);
            crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n2);
            lemma_subgroup_to_k_word(p2, b_words(data), concat(full_product, inverse_word(merged_rep)));
            let hw2: Word = choose|hw: Word| word_valid(hw, k)
                && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                    concat(full_product, inverse_word(merged_rep)));
            lemma_b_rcoset_h_b_canonical(data, full_product, hw2);
            lemma_b_rcoset_h_left_canonical(data, full_product, hw2);
        }
    }
}

///  Prove action_preserves_canonical from identifications_isomorphic.
///  This is the key result that closes Gap 1.
///
///  The h-part canonical conditions (word_valid, left_h_part, b_rcoset_h) are proven
///  by the 4 canonical lemmas + lemma_act_sym_h_canonical.
///
///  The syllable conditions (word_valid reps, canonical reps, non-identity, alternation)
///  follow from the action definition: each rep comes from a_rcoset_rep/b_rcoset_rep
///  (canonical by definition + idempotent), and alternation is maintained by construction.
///
///  Full proof requires ~50 more lines of syllable case analysis.
///  For now, we state the result and note it follows from proven infrastructure.
///
///  KEY INFRASTRUCTURE ALL VERIFIED (0 assumes):
///  - lemma_act_sym_h_canonical ✓ (h-part conditions 1-3)
///  - lemma_a_rcoset_rep_idempotent / lemma_b_rcoset_rep_idempotent ✓ (rep canonical)
///  - lemma_a_rcoset_rep_props / lemma_b_rcoset_rep_props ✓ (rep word_valid)
///
///  Proof: induction on w.len(). Base: act_word(ε) = identity. Step: act_sym preserves canonical.
///  act_sym h-part from lemma_act_sym_h_canonical. Syllables: structural from action definition.
#[verifier::rlimit(500)]
///  Full act_sym preserves canonical (h-part + syllables).
///  h-part from lemma_act_sym_h_canonical. Syllables: case analysis on subgroup/prepend/merge.
#[verifier::rlimit(500)]
///  G₁ case of act_sym_preserves_canonical.
proof fn lemma_act_sym_preserves_canonical_g1(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        symbol_valid(s, data.p1.num_generators + data.p2.num_generators),
        generator_index(s) < data.p1.num_generators,
    ensures
        is_canonical_state(data,
            act_sym(data, s, h, syls).0,
            act_sym(data, s, h, syls).1),
{
    let n1 = data.p1.num_generators;
    reveal(presentation_valid);
    lemma_act_sym_h_canonical(data, s, h, syls);

    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep = a_rcoset_rep(data, product);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s), embed_h, n1);

    if rep =~= empty_word() {
    } else if syls.len() == 0 || !syls.first().is_left {
        lemma_a_rcoset_rep_props(data, product);
        lemma_a_rcoset_rep_idempotent(data, product);
    } else {
        let full = concat(product, syls.first().rep);
        crate::word::lemma_concat_word_valid(product, syls.first().rep, n1);
        if !(a_rcoset_rep(data, full) =~= empty_word()) {
            lemma_a_rcoset_rep_props(data, full);
            lemma_a_rcoset_rep_idempotent(data, full);
        }
    }
}

///  G₂ case of act_sym_preserves_canonical.
proof fn lemma_act_sym_preserves_canonical_g2(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        symbol_valid(s, data.p1.num_generators + data.p2.num_generators),
        generator_index(s) >= data.p1.num_generators,
    ensures
        is_canonical_state(data,
            act_sym(data, s, h, syls).0,
            act_sym(data, s, h, syls).1),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    reveal(presentation_valid);
    lemma_act_sym_h_canonical(data, s, h, syls);

    let s_local = unshift_sym(s, n1);
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s_local), embed_h);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s_local), embed_h, n2);

    if b_rcoset_rep(data, product) =~= empty_word() {
    } else if syls.len() == 0 || syls.first().is_left {
        lemma_b_rcoset_rep_props(data, product);
        lemma_b_rcoset_rep_idempotent(data, product);
    } else {
        let full = concat(product, syls.first().rep);
        crate::word::lemma_concat_word_valid(product, syls.first().rep, n2);
        if !(b_rcoset_rep(data, full) =~= empty_word()) {
            lemma_b_rcoset_rep_props(data, full);
            lemma_b_rcoset_rep_idempotent(data, full);
        }
    }
}

///  act_sym preserves canonical state. Dispatches to G₁/G₂ cases.
proof fn lemma_act_sym_preserves_canonical(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        symbol_valid(s, data.p1.num_generators + data.p2.num_generators),
    ensures
        is_canonical_state(data,
            act_sym(data, s, h, syls).0,
            act_sym(data, s, h, syls).1),
{
    if generator_index(s) < data.p1.num_generators {
        lemma_act_sym_preserves_canonical_g1(data, s, h, syls);
    } else {
        lemma_act_sym_preserves_canonical_g2(data, s, h, syls);
    }
}

///  Prove action_preserves_canonical by induction on word length.
#[verifier::rlimit(200)]
///  Inductive proof: act_word preserves canonical for word_valid words.
#[verifier::rlimit(200)]
proof fn lemma_action_preserves_canonical_from_iso(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators + data.p2.num_generators),
    ensures
        is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let n = data.p1.num_generators + data.p2.num_generators;
        let s = w.last();
        let w_prefix = w.drop_last();
        let (h1, syls1) = act_sym(data, s, h, syls);

        //  s is word_valid since w is word_valid
        assert(symbol_valid(s, n));
        lemma_act_sym_preserves_canonical(data, s, h, syls);

        //  w_prefix is word_valid
        assert(word_valid(w_prefix, n)) by {
            assert forall|k: int| 0 <= k < w_prefix.len()
                implies symbol_valid(#[trigger] w_prefix[k], n)
            by { assert(w_prefix[k] == w[k]); }
        }

        //  IH
        lemma_action_preserves_canonical_from_iso(data, w_prefix, h1, syls1);
    }
}

///  identifications_isomorphic implies action_preserves_canonical (universal statement).
pub proof fn lemma_iso_implies_apc(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
    ensures
        action_preserves_canonical(data),
{
    assert forall|w: Word, h: Word, syls: Seq<Syllable>|
        is_canonical_state(data, h, syls) &&
        word_valid(w, data.p1.num_generators + data.p2.num_generators)
    implies
        is_canonical_state(data, act_word(data, w, h, syls).0, act_word(data, w, h, syls).1)
    by {
        lemma_action_preserves_canonical_from_iso(data, w, h, syls);
    }
}

pub proof fn lemma_action_well_defined_proof(
    data: AmalgamatedData,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        action_preserves_canonical(data),
    ensures
        action_well_defined(data),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let afp = amalgamated_free_product(data);
    let fp = crate::free_product::free_product(data.p1, data.p2);

    //  AFP relators = fp.relators + amalgamation_relators
    crate::normal_form_amalgamated::lemma_add_relators_concat(fp, crate::amalgamated_free_product::amalgamation_relators(data));
    //  afp.relators =~= fp.relators + amalgamation_relators(data)

    let fp_len = fp.relators.len();
    let p1_len = data.p1.relators.len();
    let p2_len = data.p2.relators.len();
    let k = data.identifications.len();
    reveal(presentation_valid);

    //  Part 1: Every AFP relator (and its inverse) acts trivially
    assert forall|i: nat, inverted: bool, h: Word, syls: Seq<Syllable>|
        i < afp.relators.len() && is_canonical_state(data, h, syls)
        implies #[trigger] relator_acts_trivially(data, get_relator(afp, i, inverted), h, syls)
    by {
        let r = afp.relators[i as int];
        if (i as int) < p1_len {
            //  G₁ relator: r = p1.relators[i] ≡ ε in G₁
            assert(r == data.p1.relators[i as int]);
            crate::presentation_lemmas::lemma_relator_is_identity(data.p1, i as int);
            if !inverted {
                lemma_g1_relator_acts_trivially(data, r, h, syls);
            } else {
                lemma_inv_equiv_eps(data, r);
                crate::word::lemma_inverse_word_valid(r, n1);
                lemma_g1_relator_acts_trivially(data, inverse_word(r), h, syls);
            }
        } else if (i as int) < p1_len + p2_len {
            //  G₂ relator: r = shift(p2.relators[i - p1_len]) ≡ ε in G₂
            let j = (i as int) - p1_len;
            assert(r == crate::free_product::shift_word(data.p2.relators[j], n1));
            crate::presentation_lemmas::lemma_relator_is_identity(data.p2, j);
            if !inverted {
                lemma_g2_relator_acts_trivially(data, data.p2.relators[j], h, syls);
            } else {
                //  inv(shift(r_j)) =~= shift(inv(r_j)) and inv(r_j) ≡ ε in G₂
                crate::word::lemma_inverse_word_valid(data.p2.relators[j], n2);
                lemma_equiv_inverse(data.p2, data.p2.relators[j], empty_word());
                crate::free_product::lemma_shift_inverse_word(data.p2.relators[j], n1);
                lemma_g2_relator_acts_trivially(data, inverse_word(data.p2.relators[j]), h, syls);
            }
        } else {
            //  Identification relator: r = amalgamation_relator(data, i - fp_len)
            let j = (i as int) - fp_len;
            assert(0 <= j < k);
            //  word_valid(r, n1+n2) from presentation_valid(afp)
            crate::amalgamated_free_product::lemma_amalgamated_valid(data);
            crate::amalgamated_free_product::lemma_add_relators_num_generators(fp,
                crate::amalgamated_free_product::amalgamation_relators(data));
            assert(word_valid(r, n1 + n2));
            if !inverted {
                lemma_identification_relator_acts_trivially(data, j, h, syls);
            } else {
                //  Forward: r acts trivially
                lemma_identification_relator_acts_trivially(data, j, h, syls);
                //  Inverse: inv(r) acts trivially (from forward + inverse pair decomposition)
                lemma_trivial_action_inverse(data, r, h, syls);
            }
        }
    }

    //  Part 2: Every inverse pair of valid AFP symbols acts trivially
    assert forall|s: Symbol, h: Word, syls: Seq<Syllable>|
        symbol_valid(s, afp.num_generators) && is_canonical_state(data, h, syls)
        implies #[trigger] relator_acts_trivially(data, inverse_pair_word(s), h, syls)
    by {
        crate::amalgamated_free_product::lemma_add_relators_num_generators(fp,
            crate::amalgamated_free_product::amalgamation_relators(data));
        if generator_index(s) < n1 {
            lemma_inverse_pair_g1(data, s, h, syls);
        } else {
            lemma_inverse_pair_g2(data, s, h, syls);
        }
    }
}

///  AFP injectivity: if w is a G₁-word and w ≡ ε in the AFP, then w ≡ ε in G₁.
///  This is the main theorem of the textbook one-shot proof (Lyndon-Schupp Ch. IV).
pub proof fn lemma_afp_injectivity(
    data: AmalgamatedData,
    w: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        action_preserves_canonical(data),
        word_valid(w, data.p1.num_generators),
        equiv_in_presentation(amalgamated_free_product(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    lemma_identity_state_canonical(data);
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let afp = amalgamated_free_product(data);
    let h0 = empty_word();
    let syls0 = Seq::<Syllable>::empty();
    reveal(presentation_valid);

    //  Step 1: action_well_defined
    lemma_action_well_defined_proof(data);

    //  Step 2: w is word_valid for AFP (weaken from n1 to n1+n2)
    crate::amalgamated_free_product::lemma_add_relators_num_generators(
        crate::free_product::free_product(data.p1, data.p2),
        crate::amalgamated_free_product::amalgamation_relators(data));
    assert(word_valid(w, (n1 + n2) as nat)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], (n1 + n2) as nat)
        by {}
    }

    //  Step 3: extract derivation from AFP equivalence, derive action equality
    let steps: Seq<DerivationStep> = choose|steps: Seq<DerivationStep>|
        #[trigger] derivation_produces(afp, steps, w) == Some(empty_word());
    lemma_act_word_deriv(data, steps, w, empty_word(), h0, syls0);
    //  act_word(w, ε, []) = act_word(ε, ε, [])
    lemma_act_word_empty(data, h0, syls0);
    //  act_word(w, ε, []) = (ε, [])

    //  Step 4: connect to G₁ one-shot
    lemma_act_word_eq_one_shot(data, w, h0, syls0);
    //  act_word(w, ε, []) = g1_one_shot_action(concat(w, embed_a(ε)), [])
    //  embed_a(ε) = ε, concat(w, ε) =~= w
    //  g1_one_shot_action(w, []) = (ε, [])
    //  This forces a_rcoset_rep(w) =~= ε and a_rcoset_h(w) =~= ε

    //  Step 5: extract w ∈ A from a_rcoset_rep(w) =~= ε
    lemma_a_rcoset_rep_props(data, w);
    //  same_a_rcoset(data, w, ε) → in_left_subgroup(data, w)

    //  Step 6: get K-word witness from subgroup membership
    lemma_subgroup_to_k_word(data.p1, a_words(data), w);
    let h_witness: Word = choose|hw: Word|
        word_valid(hw, k_size(data))
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), hw), w);

    //  Step 7: feed witness to a_rcoset_h_satisfiable
    //  Precondition: equiv(embed_a(h_witness), concat(w, inv(rep)))
    //  Since rep =~= ε: concat(w, inv(ε)) =~= w, and we have equiv(embed_a(h_witness), w)
    lemma_a_rcoset_h_satisfiable(data, w, h_witness);
    //  ensures: equiv(embed_a(a_rcoset_h(data, w)), concat(w, inv(rep))) = equiv(embed_a(ε), w) = equiv(ε, w)

    //  Step 8: w ≡ ε by symmetry
    crate::presentation::lemma_equiv_symmetric(data.p1, empty_word(), w);
}

///  AFP right-factor injectivity: if shift(w, n1) ≡ ε in the AFP, then w ≡ ε in G₂.
///  Mirrors lemma_afp_injectivity for the right factor via G₂ one-shot.
pub proof fn lemma_afp_injectivity_right(
    data: AmalgamatedData,
    w: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        action_preserves_canonical(data),
        word_valid(w, data.p2.num_generators),
        equiv_in_presentation(amalgamated_free_product(data), shift_word(w, data.p1.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.p2, w, empty_word()),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let afp = amalgamated_free_product(data);
    let h0 = empty_word();
    let syls0 = Seq::<Syllable>::empty();
    reveal(presentation_valid);

    //  Identity state is canonical
    lemma_identity_state_canonical(data);

    //  action_well_defined
    lemma_action_well_defined_proof(data);

    //  word_valid for AFP
    crate::amalgamated_free_product::lemma_add_relators_num_generators(
        crate::free_product::free_product(data.p1, data.p2),
        crate::amalgamated_free_product::amalgamation_relators(data));
    assert(word_valid(shift_word(w, n1), n1 + n2)) by {
        assert forall|k: int| 0 <= k < shift_word(w, n1).len()
            implies symbol_valid(#[trigger] shift_word(w, n1)[k], n1 + n2)
        by {
            match w[k] {
                Symbol::Gen(i) => {}
                Symbol::Inv(i) => {}
            }
        }
    }

    //  Derivation → action equality
    let steps: Seq<DerivationStep> = choose|steps: Seq<DerivationStep>|
        #[trigger] derivation_produces(afp, steps, shift_word(w, n1)) == Some(empty_word());
    lemma_act_word_deriv(data, steps, shift_word(w, n1), empty_word(), h0, syls0);
    lemma_act_word_empty(data, h0, syls0);
    //  act_word(shift(w, n1), ε, []) = (ε, [])

    //  G₂ one-shot
    lemma_act_word_eq_g2_one_shot(data, w, h0, syls0);
    //  act_word(shift(w, n1), ε, []) = g2_one_shot(concat(w, embed_b(ε)), [])
    //  embed_b(ε) = ε → g2_one_shot(w, []) = (ε, [])

    //  Extract b_rcoset_rep(w) =~= ε, b_rcoset_h(w) =~= ε
    //  → w ∈ B → h_witness → b_rcoset_h_satisfiable → equiv(ε, w)
    lemma_b_rcoset_rep_props(data, w);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  w ∈ B (from b_rcoset_rep = ε → in_right_subgroup)
    lemma_subgroup_to_k_word(data.p2, b_words(data), w);
    let h_witness: Word = choose|hw: Word|
        word_valid(hw, k_size(data))
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), hw), w);

    lemma_b_rcoset_h_satisfiable(data, w, h_witness);
    //  equiv(embed_b(b_rcoset_h(w)), concat(w, inv(rep))) = equiv(embed_b(ε), w) = equiv(ε, w)

    crate::presentation::lemma_equiv_symmetric(data.p2, empty_word(), w);
}

//  ============================================================
//  Part I2: Choose property extraction
//  ============================================================

///  Scan from current to bound to find minimum h-witness lex rank at length l.
proof fn lemma_scan_min_h_lex(
    data: AmalgamatedData, target: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_left_h_witness_of_len_rank(data, target, l, bound),
        current <= bound,
        no_smaller_h_lex(data, target, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_h_lex(data, target, l, r),
    decreases bound - current,
{
    if has_left_h_witness_of_len_rank(data, target, l, current) {
        assert(is_min_h_lex(data, target, l, current));
    } else {
        lemma_scan_min_h_lex(data, target, l, current + 1, bound);
    }
}

///  Establish h-lex satisfiability from a K-word witness.
///  After calling, left_h_min_lex's choose is satisfiable,
///  and the three-step left_h_part choose is satisfiable.
proof fn lemma_left_h_min_lex_satisfiable(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(inverse_word(left_canonical_rep(data, g)), g)),
    ensures ({
        let rep = left_canonical_rep(data, g);
        let target = concat(inverse_word(rep), g);
        let l = left_h_min_len(data, g);
        is_min_h_lex(data, target, l, left_h_min_lex(data, g))
    }),
{
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  Establish left_h_min_len satisfiability
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    let l = left_h_min_len(data, g);
    //  l satisfies: has_left_h_witness_of_len(target, l) → extract witness at length l
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_left_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex(data, target, l, 0nat));
    lemma_scan_min_h_lex(data, target, l, 0, wr);
}

//  ============================================================
//  Part I2: Right A-coset infrastructure (scanning + satisfiability)
//  ============================================================

///  Scan for minimum right-A-coset length.
proof fn lemma_scan_a_rcoset_len(
    data: AmalgamatedData, g: Word, current: nat, bound: nat,
)
    requires
        has_a_rcoset_word_of_len(data, g, bound),
        current <= bound,
        no_shorter_a_rcoset_word(data, g, current),
    ensures
        exists|l: nat| current <= l && l <= bound
            && #[trigger] is_min_a_rcoset_len(data, g, l),
    decreases bound - current,
{
    if has_a_rcoset_word_of_len(data, g, current) {
        assert(is_min_a_rcoset_len(data, g, current));
    } else {
        lemma_scan_a_rcoset_len(data, g, current + 1, bound);
    }
}

///  Scan for minimum right-A-coset lex rank.
proof fn lemma_scan_a_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_a_rcoset_word_of_len_rank(data, g, l, bound),
        current <= bound,
        no_smaller_a_rcoset_lex(data, g, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_a_rcoset_lex(data, g, l, r),
    decreases bound - current,
{
    if has_a_rcoset_word_of_len_rank(data, g, l, current) {
        assert(is_min_a_rcoset_lex(data, g, l, current));
    } else {
        lemma_scan_a_rcoset_lex(data, g, l, current + 1, bound);
    }
}

///  Right-A-coset rep satisfiability: a_rcoset_rep's choose is satisfiable.
///  Requires: g is word_valid in G₁ (g itself is in its own right A-coset).
proof fn lemma_a_rcoset_rep_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        is_min_a_rcoset_len(data, g, a_rcoset_min_len(data, g)),
        is_min_a_rcoset_lex(data, g, a_rcoset_min_len(data, g), a_rcoset_min_lex(data, g)),
{
    //  g is in its own right A-coset at length g.len()
    //  same_a_rcoset(g, g) = in_left_subgroup(concat(g, inv(g)))
    //  concat(g, inv(g)) ≡ ε by word_inverse_right → in subgroup (identity is in subgroup)
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g, data.p1.num_generators);
    crate::word::lemma_concat_word_valid(g, inverse_word(g), data.p1.num_generators);

    //  concat(g, inv(g)) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(data.p1, g);
    //  ε is in subgroup, concat(g,inv(g)) ≡ ε → in_left_subgroup by equiv
    crate::benign::lemma_identity_in_generated_subgroup(data.p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p1, concat(g, inverse_word(g)), empty_word());
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        empty_word(), concat(g, inverse_word(g)));
    assert(has_a_rcoset_word_of_len(data, g, g.len() as nat));

    //  Scan for min length
    assert(no_shorter_a_rcoset_word(data, g, 0nat));
    lemma_scan_a_rcoset_len(data, g, 0, g.len() as nat);

    //  Scan for min lex rank at min length
    let l = a_rcoset_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_a_rcoset(data, g, w) && w.len() == l;
    let wr = word_lex_rank_base(w, lex_base(data));
    assert(has_a_rcoset_word_of_len_rank(data, g, l, wr));
    assert(no_smaller_a_rcoset_lex(data, g, l, 0nat));
    lemma_scan_a_rcoset_lex(data, g, l, 0, wr);
}

///  If no_shorter_a_rcoset_word(g, l) and has_a_rcoset_word_of_len(g, 0), then l == 0.
proof fn lemma_no_shorter_a_rcoset_word_forces_zero(
    data: AmalgamatedData, g: Word, l: nat,
)
    requires
        no_shorter_a_rcoset_word(data, g, l),
        has_a_rcoset_word_of_len(data, g, 0nat),
    ensures
        l == 0,
    decreases l,
{
    if l > 0 {
        //  no_shorter_a_rcoset_word(g, l) → !has(g, l-1) && no_shorter(g, l-1)
        //  By IH: l-1 == 0 → !has(g, 0). Contradiction with has(g, 0).
        lemma_no_shorter_a_rcoset_word_forces_zero(data, g, (l - 1) as nat);
    }
}

///  If g is in the subgroup A, then a_rcoset_rep(g) =~= ε.
pub proof fn lemma_a_rcoset_in_subgroup(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        in_left_subgroup(data, g),
    ensures
        a_rcoset_rep(data, g) =~= empty_word(),
{
    let e = empty_word();
    let n1 = data.p1.num_generators;

    //  same_a_rcoset(g, ε) = in_left_subgroup(concat(g, inv(ε)))
    //  concat(g, inv(ε)) =~= g, which is in subgroup
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(concat(g, inverse_word(e)) =~= g) by {
        assert(concat(g, e).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, e)[k] == g[k] by {}
    }
    crate::presentation::lemma_equiv_refl(data.p1, g);
    lemma_in_subgroup_equiv(data.p1, a_words(data), g, concat(g, inverse_word(e)));

    //  ε is in same rcoset → has_a_rcoset_word_of_len(g, 0)
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    assert(has_a_rcoset_word_of_len(data, g, 0nat));
    assert(no_shorter_a_rcoset_word(data, g, 0nat));
    lemma_scan_a_rcoset_len(data, g, 0, 0);
    //  a_rcoset_min_len(g) must be 0 (the only satisfying value)
    let l = a_rcoset_min_len(data, g);
    lemma_no_shorter_a_rcoset_word_forces_zero(data, g, l);
    //  l == 0 → a_rcoset_min_len(g) == 0

    //  ε at lex rank 0 is the only word of length 0
    assert(word_lex_rank_base(e, lex_base(data)) == 0nat);
    assert(has_a_rcoset_word_of_len_rank(data, g, 0nat, 0nat));
    assert(no_smaller_a_rcoset_lex(data, g, 0nat, 0nat));
    lemma_scan_a_rcoset_lex(data, g, 0, 0, 0);
    //  a_rcoset_rep has length 0 → =~= ε
}

///  If g is in the subgroup A, both left and right coset reps are ε.
proof fn lemma_in_subgroup_both_reps_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        in_left_subgroup(data, g),
    ensures
        a_rcoset_rep(data, g) =~= empty_word(),
        left_canonical_rep(data, g) =~= empty_word(),
{
    let e = empty_word();
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    //  Right coset rep = ε
    lemma_a_rcoset_in_subgroup(data, g);
    //  Left coset rep = ε: same_left_coset(g, ε) via inv(g) ∈ A
    crate::word::lemma_inverse_word_valid(g, n1);
    lemma_subgroup_inverse(p1, a_words(data), g);
    assert(concat(inverse_word(g), e) =~= inverse_word(g)) by {
        assert(concat(inverse_word(g), e).len() == inverse_word(g).len());
        assert forall|k: int| 0 <= k < inverse_word(g).len()
            implies concat(inverse_word(g), e)[k] == inverse_word(g)[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p1, inverse_word(g));
    lemma_in_subgroup_equiv(p1, a_words(data),
        inverse_word(g), concat(inverse_word(g), e));
    //  same_left_coset(g, ε) established
    lemma_left_rep_identity(data);
    lemma_left_rep_props(data, g);
    lemma_left_rep_coset_invariant(data, g, e);
}

///  Extract right-A-coset rep properties.
pub proof fn lemma_a_rcoset_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_a_rcoset(data, g, a_rcoset_rep(data, g)),
        word_valid(a_rcoset_rep(data, g), data.p1.num_generators),
        a_rcoset_rep(data, g).len() == a_rcoset_min_len(data, g),
        word_lex_rank_base(a_rcoset_rep(data, g), lex_base(data)) == a_rcoset_min_lex(data, g),
{
    lemma_a_rcoset_rep_satisfiable(data, g);
}

///  Establish h-part satisfiability for right A-coset decomposition.
///  The target is g · inv(rep) instead of inv(rep) · g, but the h-witness
///  infrastructure (has_left_h_witness_of_len etc.) works for any target.
proof fn lemma_a_rcoset_h_satisfiable(data: AmalgamatedData, g: Word, h_witness: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures ({
        let rep = a_rcoset_rep(data, g);
        let target = concat(g, inverse_word(rep));
        let h = a_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h), target)
    }),
{
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));

    //  h_witness witnesses has_left_h_witness_of_len(target, h_witness.len())
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    //  Nat well-ordering → a_rcoset_h_min_len satisfiable
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  h-lex satisfiability (manual scan with right-coset target)
    let l = a_rcoset_h_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_left_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex(data, target, l, 0nat));
    lemma_scan_min_h_lex(data, target, l, 0, wr);
}

///  Extract the key property of left_h_part: embed_a(h) ≡ concat(inv(rep), g) in G₁.
///  Requires a witness K-word to prove the choose is satisfiable.
proof fn lemma_left_h_part_props(
    data: AmalgamatedData,
    g: Word,
    h_witness: Word,  //  any K-word with embed ≡ target
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(inverse_word(left_canonical_rep(data, g)), g)),
    ensures ({
        let rep = left_canonical_rep(data, g);
        let h = left_h_part(data, g);
        let target = concat(inverse_word(rep), g);
        &&& word_valid(h, k_size(data))
        &&& equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h), target)
    }),
{
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  h_witness satisfies the left_h_min_len choose predicate:
    //  has_left_h_witness_of_len(data, target, h_witness.len())
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    //  By nat well-ordering: left_h_min_len's choose is satisfiable
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  Establish h-lex satisfiability for the three-step choose
    lemma_left_h_min_lex_satisfiable(data, g, h_witness);

    //  left_h_min_len + left_h_min_lex satisfiable → left_h_part's choose is satisfiable
    //  → result has the properties.
}

//  ============================================================
//  Part J0: Embedding subgroup membership + h-witness existence
//  ============================================================

///  apply_embedding(gens, h) is in the generated subgroup of gens.
///  Proof by induction on h.len(): each symbol gives a generator or its inverse,
///  and the subgroup is closed under concat and inverse.
pub proof fn lemma_apply_embedding_in_subgroup(
    p: Presentation, gens: Seq<Word>, h: Word,
)
    requires
        presentation_valid(p),
        word_valid(h, gens.len()),
        forall|i: int| 0 <= i < gens.len()
            ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, apply_embedding(gens, h)),
    decreases h.len(),
{
    if h.len() == 0 {
        assert(apply_embedding(gens, h) =~= empty_word());
        crate::benign::lemma_identity_in_generated_subgroup(p, gens);
    } else {
        let s = h.first();
        let rest = h.drop_first();
        let head = apply_embedding_symbol(gens, s);
        let tail = apply_embedding(gens, rest);

        //  IH: tail is in subgroup
        lemma_apply_embedding_in_subgroup(p, gens, rest);

        //  head is a generator or inverse of generator → in subgroup
        match s {
            Symbol::Gen(i) => {
                assert(head == gens[i as int]);
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
            }
            Symbol::Inv(i) => {
                assert(head == inverse_word(gens[i as int]));
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
                crate::word::lemma_inverse_word_valid(gens[i as int], p.num_generators);
                lemma_subgroup_inverse(p, gens, gens[i as int]);
            }
        }

        //  concat(head, tail) is in subgroup
        lemma_subgroup_concat(p, gens, head, tail);
    }
}

///  For any valid G₁-word g, there exists a K-word h with embed_a(h) ≡ target,
///  where target = inv(rep) · g. This follows from same_left_coset(g, rep),
///  subgroup closure under inverse, and subgroup_to_k_word.
pub proof fn lemma_h_witness_exists(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
    ensures
        exists|h: Word| word_valid(h, k_size(data))
            && equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h),
                concat(inverse_word(left_canonical_rep(data, g)), g)),
{
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  same_left_coset(g, rep) from left_rep_props
    lemma_left_rep_props(data, g);
    //  same_left_coset(g, rep) = in_left_subgroup(inv(g) · rep)
    //  inv(inv(g) · rep) = inv(rep) · g = target
    //  subgroup closed under inverse → target ∈ subgroup

    //  word_valid for inv(g), rep, concat(inv(g), rep), etc.
    let n1 = data.p1.num_generators;
    crate::word::lemma_inverse_word_valid(g, n1);
    crate::word::lemma_concat_word_valid(inverse_word(g), rep, n1);

    //  in_left_subgroup(concat(inv(g), rep))
    //  → lemma_subgroup_inverse → in_left_subgroup(inverse_word(concat(inv(g), rep)))
    //  inverse_word(concat(inv(g), rep)) =~= concat(inverse_word(rep), inverse_word(inverse_word(g)))
    //    =~= concat(inverse_word(rep), g) = target

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    lemma_subgroup_inverse(data.p1, a_words(data),
        concat(inverse_word(g), rep));

    //  Show inverse_word(concat(inv(g), rep)) =~= target
    crate::word::lemma_inverse_concat(inverse_word(g), rep);
    crate::word::lemma_inverse_involution(g);
    //  Chain: inverse_word(concat(inv(g), rep))
    //    =~= concat(inv(rep), inv(inv(g)))   [by inverse_concat]
    //    =~= concat(inv(rep), g)             [by inverse_involution on g]
    //    == target
    let inv_concat = inverse_word(concat(inverse_word(g), rep));
    assert(inv_concat =~= concat(inverse_word(rep), inverse_word(inverse_word(g))));
    assert(inverse_word(inverse_word(g)) =~= g);
    //  Help Z3 see the element-wise equality
    assert forall|k: int| 0 <= k < target.len()
        implies inv_concat[k] == target[k]
    by {
        if k < inverse_word(rep).len() {
            assert(inv_concat[k] == inverse_word(rep)[k]);
        } else {
            let j = k - inverse_word(rep).len() as int;
            assert(inv_concat[k] == inverse_word(inverse_word(g))[j]);
            assert(target[k] == g[j]);
        }
    }
    assert(inv_concat =~= target);
    //  in_generated_subgroup(p1, a_words, inv_concat) and inv_concat =~= target
    //  → in_generated_subgroup(p1, a_words, target)

    assert(in_generated_subgroup(data.p1, a_words(data), target));
    lemma_subgroup_to_k_word(data.p1, a_words(data), target);
    //  a_words(data).len() == k_size(data)
    assert(a_words(data).len() == k_size(data));
}

//  ============================================================
//  Part J: Per-relator triviality — inverse pairs on identity
//  ============================================================

///  Helper: act_sym of a G₁ symbol with a_rcoset_rep = ε gives (h', []).
proof fn lemma_act_sym_subgroup_identity(
    data: AmalgamatedData,
    s: Symbol,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), empty_word())) =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s),
            apply_embedding(a_words(data), empty_word()));
        let h1 = a_rcoset_h(data, product);
        act_sym(data, s, empty_word(), Seq::<Syllable>::empty())
            == (h1, Seq::<Syllable>::empty())
    }),
{
    //  act_sym dispatches to act_left_sym since gen_index(s) < n1.
    //  act_left_sym: product = concat([s], embed_a(ε)), a_rcoset_rep = ε → (h1, [])
}

///  Inverse pair [s, inv(s)] acts trivially on identity state,
///  when s is in the left subgroup (left_canonical_rep = ε).
///  Takes a K-word witness for the subgroup decomposition.
///  Inverse pair on identity: now uses right A-coset decomposition.
///  Superseded by lemma_inverse_pair_g1_subcase_a for the general case.
proof fn lemma_inverse_pair_identity_case1(
    data: AmalgamatedData,
    s: Symbol,
    h_wit: Word,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), empty_word())) =~= empty_word(),
        word_valid(h_wit, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_wit),
            concat(Seq::new(1, |_i: int| s), empty_word())),
    ensures
        act_word(data, inverse_pair_word(s), empty_word(), Seq::<Syllable>::empty())
            == (empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    let p1 = data.p1;
    let n1 = p1.num_generators;
    reveal(presentation_valid);

    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let product1 = concat(s_word, apply_embedding(a_words(data), e));
    assert(apply_embedding(a_words(data), e) =~= e);
    let h1 = a_rcoset_h(data, product1);

    //  Step 1: act_sym(s, ε, []) = (h1, []) since a_rcoset_rep = ε
    lemma_act_sym_subgroup_identity(data, s);

    //  Step 2: decompose via composition
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, e, Seq::<Syllable>::empty());
    lemma_act_word_single(data, s, e, Seq::<Syllable>::empty());
    lemma_act_word_single(data, inv_s, h1, Seq::<Syllable>::empty());

    //  embed_a(h1) ≡ product1 · inv(rep) = product1 (since rep = ε)
    assert(product1 =~= s_word) by {
        assert(product1.len() == s_word.len());
        assert forall|k: int| 0 <= k < s_word.len() implies product1[k] == s_word[k] by {}
    }
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    //  h_wit witnesses the h-part satisfiability
    //  target = concat(product1, inv(a_rcoset_rep(product1))) =~= product1 =~= s_word
    assert(concat(product1, inverse_word(a_rcoset_rep(data, product1))) =~= product1) by {
        assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
        let c = concat(product1, e);
        assert(c.len() == product1.len());
        assert forall|k: int| 0 <= k < product1.len() implies c[k] == product1[k] by {}
    }
    lemma_a_rcoset_h_satisfiable(data, product1, h_wit);

    //  embed_a(h1) ≡ product1
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h1, n1);

    //  product2 = [inv(s)] · embed_a(h1) ≡ [inv(s)] · product1 ≡ [inv(s)] · [s] ≡ ε
    let product2 = concat(inv_s_word, apply_embedding(a_words(data), h1));
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, inv_s_word, apply_embedding(a_words(data), h1), product1);

    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= e);
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p1, s_word);
    crate::presentation::lemma_equiv_transitive(p1, product2,
        concat(inv_s_word, product1), e);

    //  product2 ≡ ε → product2 is in the subgroup
    crate::word::lemma_concat_word_valid(inv_s_word,
        apply_embedding(a_words(data), h1), n1);
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(p1, product2, e);
    lemma_in_subgroup_equiv(p1, a_words(data), e, product2);

    //  product2 in subgroup → a_rcoset_rep(product2) =~= ε
    lemma_a_rcoset_in_subgroup(data, product2);

    //  a_rcoset_h(product2) =~= ε: need h_min_len = 0
    assert(word_valid(e, k_size(data))) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    let target_p2 = concat(product2, inverse_word(a_rcoset_rep(data, product2)));
    //  target =~= product2 (since rep = ε) ≡ ε → equiv(ε, target)
    crate::presentation::lemma_equiv_symmetric(p1, product2, e);
    assert(has_left_h_witness_of_len(data, target_p2, 0nat));
    let pred_p2 = |l: nat| has_left_h_witness_of_len(data, target_p2, l);
    assert(pred_p2(0nat));
    assert(no_pred_below(pred_p2, 0nat));
    lemma_nat_well_ordering(pred_p2, 0nat);
    let hl_p2 = a_rcoset_h_min_len(data, product2);
    lemma_no_pred_below_forces_zero(pred_p2, hl_p2);
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target_p2, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target_p2, 0nat, 0nat));
    lemma_scan_min_h_lex(data, target_p2, 0, 0, 0);
    //  a_rcoset_h(product2) has length 0 → =~= ε
}

///  For a single G₁ symbol s: act_word([s], ε, []) = g1_decompose_state([s]).
///  This connects the symbol-by-symbol action to the one-shot decomposition.
pub proof fn lemma_act_single_eq_decompose(
    data: AmalgamatedData,
    s: Symbol,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
    ensures
        act_word(data, Seq::new(1, |_i: int| s), empty_word(), Seq::<Syllable>::empty())
            == g1_decompose_state(data, Seq::new(1, |_i: int| s)),
{
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);

    //  act_word([s], ε, []) = act_sym(s, ε, [])
    lemma_act_word_single(data, s, e, Seq::<Syllable>::empty());

    //  act_sym(s, ε, []) = act_left_sym(s, ε, []) since gen_index(s) < n1

    //  act_left_sym uses right-coset decomposition:
    //    product = concat([s], embed_a(ε)) = concat([s], ε) =~= [s]
    //    h' = a_rcoset_h(product), rep' = a_rcoset_rep(product)

    //  g1_decompose_state([s]) uses the same right-coset fns.
    //  Since product =~= [s]: the rcoset reps and h-parts are the same.
    assert(apply_embedding(a_words(data), e) =~= e);
    let product = concat(s_word, apply_embedding(a_words(data), e));
    assert(product =~= s_word) by {
        assert(product.len() == s_word.len());
        assert forall|k: int| 0 <= k < s_word.len()
            implies product[k] == s_word[k] by {}
    }
    //  product =~= s_word → a_rcoset_rep(product) == a_rcoset_rep(s_word)
    //  and a_rcoset_h(product) == a_rcoset_h(s_word)
}

//  ============================================================
//  Part K: Bridge — in_generated_subgroup ↔ apply_embedding
//  ============================================================

///  If w is in the generated subgroup, there exists a K-word whose embedding ≡ w.
///  This bridges in_generated_subgroup (existential over factors) to
///  apply_embedding (K-word based).
///
///  Proof: in_generated_subgroup gives factors with concat_all(factors) ≡ w.
///  Each factor = gens[i] or inv(gens[i]). Map to K-word: Gen(i) or Inv(i).
///  Then apply_embedding produces the same word as concat_all.
pub proof fn lemma_subgroup_to_k_word(
    p: Presentation,
    gens: Seq<Word>,
    w: Word,
)
    requires
        in_generated_subgroup(p, gens, w),
    ensures
        exists|h: Word|
            word_valid(h, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h), w),
{
    //  Extract factors witness
    let factors: Seq<Word> = choose|factors: Seq<Word>|
        #[trigger] factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), w);

    //  Build the K-word from the factors by induction
    lemma_factors_to_k_word_exists(p, gens, factors);
    //  Now: exists|h| word_valid(h, gens.len()) && equiv(embed(h), concat_all(factors))

    //  Chain: embed(h) ≡ concat_all(factors) ≡ w
    let h: Word = choose|h: Word| word_valid(h, gens.len())
        && equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors));
    crate::presentation::lemma_equiv_transitive(p,
        apply_embedding(gens, h), concat_all(factors), w);
}

///  Helper: given factors from generators, construct a K-word with matching embedding.
proof fn lemma_factors_to_k_word_exists(
    p: Presentation,
    gens: Seq<Word>,
    factors: Seq<Word>,
)
    requires
        factors_from_generators(gens, factors),
    ensures
        exists|h: Word|
            word_valid(h, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
        //  h = ε: word_valid(ε, anything) and embed(ε) = ε = concat_all([])
        let h = empty_word();
        assert(word_valid(h, gens.len())) by { assert(h.len() == 0); }
        assert(apply_embedding(gens, h) =~= empty_word());
        assert(concat_all(factors) =~= empty_word());
        crate::presentation::lemma_equiv_refl(p, empty_word());
        //  Witness the exists: h = ε satisfies both conditions
        assert(equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)));
    } else {
        //  IH on rest
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_factors_to_k_word_exists(p, gens, rest);
        //  exists|h_rest| word_valid(h_rest, gens.len()) && equiv(embed(h_rest), concat_all(rest))

        let h_rest: Word = choose|h_rest: Word| word_valid(h_rest, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h_rest), concat_all(rest));

        //  First factor: is_generator_or_inverse(gens, factors.first())
        //  So factors.first() = gens[i] or inv(gens[i]) for some i < gens.len()
        let first = factors.first();
        let i: nat = choose|i: nat| i < gens.len()
            && (first =~= gens[i as int] || first =~= inverse_word(gens[i as int]));

        //  Construct the K-word: [sym] ++ h_rest
        let sym = if first =~= gens[i as int] { Symbol::Gen(i) } else { Symbol::Inv(i) };
        let h = Seq::new(1, |_j: int| sym) + h_rest;

        //  word_valid(h, gens.len()): sym has gen_index = i < gens.len(), rest is word_valid by IH
        assert(word_valid(h, gens.len())) by {
            assert(symbol_valid(sym, gens.len()));
            assert forall|k: int| 0 <= k < h.len()
                implies symbol_valid(h[k], gens.len())
            by {
                if k == 0 {
                } else {
                    assert(h[k] == h_rest[k - 1]);
                }
            }
        }

        //  embed(h) = concat(embed_sym(sym), embed(h_rest))
        //           = concat(first, embed(h_rest))
        //           ≡ concat(first, concat_all(rest))   [by IH on h_rest]
        //           = concat_all(factors)

        //  embed_sym(sym) =~= first
        assert(apply_embedding_symbol(gens, sym) =~= first);

        //  Unfold apply_embedding(gens, h) one level:
        //  h = [sym] ++ h_rest, so h.first() = sym, h.drop_first() =~= h_rest
        assert(h.len() > 0);
        assert(h.first() == sym);
        assert(h.drop_first() =~= h_rest) by {
            let d = h.drop_first();
            assert(d.len() == h_rest.len());
            assert forall|k: int| 0 <= k < h_rest.len()
                implies d[k] == h_rest[k] by {}
        }
        //  apply_embedding(gens, h) = concat(embed_sym(h.first()), embed(h.drop_first()))
        //                           = concat(embed_sym(sym), embed(h_rest))
        //                           = concat(first, embed(h_rest))

        //  IH gives: equiv(embed(h_rest), concat_all(rest))
        //  By right-congruence: concat(first, embed(h_rest)) ≡ concat(first, concat_all(rest))
        crate::presentation_lemmas::lemma_equiv_concat_right(p, first,
            apply_embedding(gens, h_rest), concat_all(rest));

        //  concat(first, concat_all(rest)) = concat_all(factors)
        //  So: equiv(concat(first, embed(h_rest)), concat_all(factors))
        //  And: apply_embedding(gens, h) =~= concat(first, embed(h_rest))
        //  Therefore: equiv(apply_embedding(gens, h), concat_all(factors))
        assert(equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)));
    }
}

///  concat_all distributes over sequence append.
proof fn lemma_concat_all_append(xs: Seq<Word>, ys: Seq<Word>)
    ensures
        concat_all(xs + ys) =~= concat(concat_all(xs), concat_all(ys)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert((xs + ys) =~= ys) by {
            assert((xs + ys).len() == ys.len());
            assert forall|k: int| 0 <= k < ys.len()
                implies (xs + ys)[k] == ys[k] by {}
        }
        assert(concat_all(xs) =~= empty_word());
        assert(concat(empty_word(), concat_all(ys)) =~= concat_all(ys)) by {
            let c = concat(empty_word(), concat_all(ys));
            assert(c.len() == concat_all(ys).len());
            assert forall|k: int| 0 <= k < c.len()
                implies c[k] == concat_all(ys)[k] by {}
        }
    } else {
        //  concat_all(xs ++ ys) = concat(xs.first(), concat_all(xs.drop_first() ++ ys))
        assert((xs + ys).first() == xs.first());
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys) by {
            let lhs = (xs + ys).drop_first();
            let rhs = xs.drop_first() + ys;
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < rhs.len()
                implies lhs[k] == rhs[k] by {}
        }
        //  IH: concat_all(xs.drop_first() ++ ys) =~= concat(concat_all(xs.drop_first()), concat_all(ys))
        lemma_concat_all_append(xs.drop_first(), ys);
        //  concat_all(xs) = concat(xs.first(), concat_all(xs.drop_first()))
        //  concat(concat_all(xs), concat_all(ys)) = concat(concat(xs.first(), concat_all(xs.drop_first())), concat_all(ys))
        //  By concat associativity: = concat(xs.first(), concat(concat_all(xs.drop_first()), concat_all(ys)))
        //  = concat(xs.first(), concat_all(xs.drop_first() ++ ys)) [by IH]
        //  = concat_all(xs ++ ys)
    }
}

///  Generated subgroup is closed under concatenation.
pub proof fn lemma_subgroup_concat(
    p: Presentation, gens: Seq<Word>, a: Word, b: Word,
)
    requires
        in_generated_subgroup(p, gens, a),
        in_generated_subgroup(p, gens, b),
    ensures
        in_generated_subgroup(p, gens, concat(a, b)),
{
    //  Extract factor witnesses
    let fa: Seq<Word> = choose|fa: Seq<Word>|
        #[trigger] factors_from_generators(gens, fa)
        && equiv_in_presentation(p, concat_all(fa), a);
    let fb: Seq<Word> = choose|fb: Seq<Word>|
        #[trigger] factors_from_generators(gens, fb)
        && equiv_in_presentation(p, concat_all(fb), b);

    //  Combined factors: fa ++ fb
    let fab = fa + fb;
    assert(factors_from_generators(gens, fab)) by {
        assert forall|k: int| 0 <= k < fab.len()
            implies is_generator_or_inverse(gens, #[trigger] fab[k])
        by {
            if k < fa.len() {
                assert(fab[k] == fa[k]);
            } else {
                assert(fab[k] == fb[k - fa.len()]);
            }
        }
    }

    //  concat_all(fab) =~= concat(concat_all(fa), concat_all(fb))
    lemma_concat_all_append(fa, fb);
    //  concat(concat_all(fa), concat_all(fb)) ≡ concat(a, b) by congruence
    crate::presentation_lemmas::lemma_equiv_concat(p,
        concat_all(fa), a, concat_all(fb), b);
    //  Since concat_all(fab) =~= concat(concat_all(fa), concat_all(fb)) (extensional eq = eq for Seq),
    //  and equiv(concat(concat_all(fa), concat_all(fb)), concat(a, b)),
    //  we get equiv(concat_all(fab), concat(a, b)).
}

///  Inverse preserves equivalence: if a ≡ b then inv(a) ≡ inv(b).
///  Split into two helpers to stay within rlimit.
proof fn lemma_equiv_inverse_helper(
    p: Presentation, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, a, b),
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        //  concat(inv(b), a) ≡ ε
        equiv_in_presentation(p, concat(inverse_word(b), a), empty_word()),
{
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(b, p.num_generators);
    //  inv(b) * b ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p, b);
    //  a ≡ b → concat(inv(b), a) ≡ concat(inv(b), b) by right-congruence
    crate::presentation_lemmas::lemma_equiv_concat_right(p, inv_b, a, b);
    //  ε ≡ concat(inv(b), b) by symmetry
    crate::word::lemma_concat_word_valid(inv_b, b, p.num_generators);
    crate::presentation::lemma_equiv_symmetric(p, concat(inv_b, b), empty_word());
    //  concat(inv(b), a) ≡ concat(inv(b), b) ≡... need direction.
    //  We have: equiv(concat(inv_b, a), concat(inv_b, b)) from right-congruence
    //  And: equiv(concat(inv_b, b), ε) from word_inverse_left
    //  Transitivity: equiv(concat(inv_b, a), ε)
    crate::presentation::lemma_equiv_transitive(p,
        concat(inv_b, a), concat(inv_b, b), empty_word());
}

pub proof fn lemma_equiv_inverse(
    p: Presentation, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, a, b),
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        equiv_in_presentation(p, inverse_word(a), inverse_word(b)),
{
    let inv_a = inverse_word(a);
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(a, p.num_generators);
    crate::word::lemma_inverse_word_valid(b, p.num_generators);

    //  From helper: concat(inv(b), a) ≡ ε
    lemma_equiv_inverse_helper(p, a, b);

    //  concat(concat(inv(b), a), inv(a)) ≡ concat(ε, inv(a)) by left-congruence
    crate::word::lemma_concat_word_valid(inv_b, a, p.num_generators);
    crate::presentation_lemmas::lemma_equiv_concat_left(p,
        concat(inv_b, a), empty_word(), inv_a);
    //  LHS ≡ concat(ε, inv(a)) =~= inv(a)

    //  a * inv(a) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(p, a);
    //  concat(inv(b), concat(a, inv(a))) ≡ concat(inv(b), ε) by right-congruence
    crate::presentation_lemmas::lemma_equiv_concat_right(p, inv_b,
        concat(a, inv_a), empty_word());
    //  RHS ≡ concat(inv(b), ε) =~= inv(b)

    //  Key: concat(concat(inv(b), a), inv(a)) =~= concat(inv(b), concat(a, inv(a))) [seq assoc]
    //  From above: LHS ≡ inv(a) and RHS ≡ inv(b)
    //  Since LHS =~= RHS: inv(a) ≡ LHS =~= RHS ≡ inv(b)
    //  i.e., equiv(inv(a), inv(b)) by the chain.

    //  Step by step for Z3:
    //  equiv(concat(concat(inv_b, a), inv_a), concat(ε, inv_a))  [from left-congruence]
    //  equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))  [from right-congruence]
    //  These two LHS expressions are =~= (seq associativity)
    //  So: equiv(concat(inv_b, concat(a, inv_a)), concat(ε, inv_a)) by chain:
    //    concat(inv_b, concat(a, inv_a)) =~= concat(concat(inv_b, a), inv_a) ≡ concat(ε, inv_a)
    //  And: equiv(concat(inv_b, ε), concat(ε, inv_a)) by transitivity with above
    //    concat(inv_b, ε) ≡ concat(inv_b, concat(a, inv_a)) ≡ concat(ε, inv_a)
    //  And concat(inv_b, ε) =~= inv_b and concat(ε, inv_a) =~= inv_a
    //  So equiv(inv_b, inv_a), hence equiv(inv_a, inv_b) by symmetry.

    //  Explicit chain: connect the two congruence results through seq associativity.
    //  We have:
    //    (A) equiv(concat(concat(inv_b, a), inv_a), concat(ε, inv_a))  [left-cong]
    //    (B) equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))  [right-cong]
    //  And concat(concat(inv_b, a), inv_a) =~= concat(inv_b, concat(a, inv_a)) [assoc]

    //  From (A): symmetry gives equiv(concat(ε, inv_a), concat(concat(inv_b, a), inv_a))
    //  =~= equiv(concat(ε, inv_a), concat(inv_b, concat(a, inv_a)))
    //  Then transitivity with (B): equiv(concat(ε, inv_a), concat(inv_b, ε))
    //  word_valid for intermediate expressions
    crate::word::lemma_concat_word_valid(concat(inv_b, a), inv_a, p.num_generators);
    crate::word::lemma_concat_word_valid(a, inv_a, p.num_generators);
    //  Symmetry on (A): equiv(concat(ε, inv_a), concat(concat(inv_b, a), inv_a))
    crate::presentation::lemma_equiv_symmetric(p,
        concat(concat(inv_b, a), inv_a), concat(empty_word(), inv_a));
    //  Transitivity: concat(ε, inv_a) ≡ concat(concat(inv_b,a), inv_a) =~= concat(inv_b, concat(a,inv_a)) ≡ concat(inv_b, ε)
    //  The middle =~= (assoc) is automatic for Z3 since Seq =~= implies ==.
    //  But the symmetry gave equiv(concat(ε, inv_a), concat(concat(inv_b,a), inv_a))
    //  And (B) gives equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))
    //  These connect via assoc: concat(concat(inv_b,a), inv_a) =~= concat(inv_b, concat(a, inv_a))
    //  Seq associativity: concat(concat(x,y),z) =~= concat(x, concat(y,z))
    assert(concat(concat(inv_b, a), inv_a) =~= concat(inv_b, concat(a, inv_a))) by {
        let lhs = concat(concat(inv_b, a), inv_a);
        let rhs = concat(inv_b, concat(a, inv_a));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_b.len() {} else if k < inv_b.len() + a.len() {} else {}
        }
    }
    crate::presentation::lemma_equiv_transitive(p,
        concat(empty_word(), inv_a),
        concat(concat(inv_b, a), inv_a),
        concat(inv_b, empty_word()));
    //  Now: equiv(concat(ε, inv_a), concat(inv_b, ε))
    //  concat(ε, inv_a) =~= inv_a and concat(inv_b, ε) =~= inv_b
    //  So equiv(inv_a, inv_b). Z3 should handle the =~= substitution.
    assert(concat(empty_word(), inv_a) =~= inv_a) by {
        let c = concat(empty_word(), inv_a);
        assert(c.len() == inv_a.len());
        assert forall|k: int| 0 <= k < inv_a.len() implies c[k] == inv_a[k] by {}
    }
    assert(concat(inv_b, empty_word()) =~= inv_b) by {
        let c = concat(inv_b, empty_word());
        assert(c.len() == inv_b.len());
        assert forall|k: int| 0 <= k < inv_b.len() implies c[k] == inv_b[k] by {}
    }
}

///  Generated subgroup is closed under equivalence (already proved as lemma_in_subgroup_equiv).

///  Reverse a sequence of words and invert each element.
pub open spec fn reverse_invert_factors(factors: Seq<Word>) -> Seq<Word>
    decreases factors.len(),
{
    if factors.len() == 0 {
        Seq::empty()
    } else {
        reverse_invert_factors(factors.drop_first())
            + Seq::new(1, |_i: int| inverse_word(factors.first()))
    }
}

///  Each factor in reverse_invert_factors is still a generator-or-inverse.
proof fn lemma_reverse_invert_preserves_generators(
    gens: Seq<Word>, factors: Seq<Word>,
)
    requires
        factors_from_generators(gens, factors),
    ensures
        factors_from_generators(gens, reverse_invert_factors(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_reverse_invert_preserves_generators(gens, rest);
        let rif = reverse_invert_factors(factors);
        let rif_rest = reverse_invert_factors(rest);
        let inv_first = inverse_word(factors.first());
        assert forall|k: int| 0 <= k < rif.len()
            implies is_generator_or_inverse(gens, #[trigger] rif[k])
        by {
            if k < rif_rest.len() {
                assert(rif[k] == rif_rest[k]);
            } else {
                assert(rif[k] == inv_first);
                //  inv_first = inv(factors.first())
                //  factors.first() is is_generator_or_inverse(gens, ...)
                //  So exists i: factors.first() == gens[i] or factors.first() == inv(gens[i])
                //  Case 1: factors.first() == gens[i] → inv_first == inv(gens[i])
                //    → is_generator_or_inverse(gens, inv_first) with the inv case ✓
                //  Case 2: factors.first() == inv(gens[i]) → inv_first == inv(inv(gens[i]))
                //    inv(inv(gens[i])) =~= gens[i] by inverse involution
                //    → is_generator_or_inverse(gens, inv_first) with the direct case ✓
                let i: nat = choose|i: nat| i < gens.len()
                    && (factors.first() =~= gens[i as int]
                        || factors.first() =~= inverse_word(gens[i as int]));
                if factors.first() =~= gens[i as int] {
                    //  inv_first = inv(gens[i]) → is_gen_or_inv
                } else {
                    //  inv_first = inv(inv(gens[i])) =~= gens[i]
                    crate::word::lemma_inverse_involution(gens[i as int]);
                }
            }
        }
    }
}

///  concat_all of factors_from_generators produces a word_valid word.
proof fn lemma_concat_all_word_valid(
    gens: Seq<Word>, factors: Seq<Word>, n: nat,
)
    requires
        factors_from_generators(gens, factors),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], n),
    ensures
        word_valid(concat_all(factors), n),
    decreases factors.len(),
{
    if factors.len() == 0 {
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_concat_all_word_valid(gens, rest, n);
        //  factors.first() is word_valid: it's gens[i] or inv(gens[i])
        let first = factors.first();
        let i: nat = choose|i: nat| i < gens.len()
            && (first =~= gens[i as int] || first =~= inverse_word(gens[i as int]));
        if first =~= inverse_word(gens[i as int]) {
            crate::word::lemma_inverse_word_valid(gens[i as int], n);
        }
        crate::word::lemma_concat_word_valid(first, concat_all(rest), n);
    }
}

///  concat_all of reverse_invert_factors ≡ inverse_word of concat_all.
proof fn lemma_reverse_invert_is_inverse(
    p: Presentation, factors: Seq<Word>,
)
    ensures
        equiv_in_presentation(p,
            concat_all(reverse_invert_factors(factors)),
            inverse_word(concat_all(factors))),
    decreases factors.len(),
{
    if factors.len() == 0 {
        //  All three expressions evaluate to ε when factors is empty:
        let rif = reverse_invert_factors(factors);
        let ca = concat_all(factors);
        assert(rif.len() == 0);
        assert(concat_all(rif) =~= empty_word());
        assert(ca =~= empty_word());
        assert(inverse_word(ca) =~= empty_word()) by {
            assert(inverse_word(empty_word()).len() == 0);
        }
        crate::presentation::lemma_equiv_refl(p, concat_all(rif));
        //  Explicitly assert the postcondition using bound variables:
        assert(equiv_in_presentation(p, concat_all(rif), inverse_word(ca)));
        return;
    } else {
        let rest = factors.drop_first();
        let first = factors.first();
        let inv_first = inverse_word(first);
        let rif_rest = reverse_invert_factors(rest);

        lemma_reverse_invert_is_inverse(p, rest);
        crate::word::lemma_inverse_concat(first, concat_all(rest));
        lemma_concat_all_append(rif_rest, Seq::new(1, |_i: int| inv_first));
        crate::presentation_lemmas::lemma_equiv_concat_left(p,
            concat_all(rif_rest), inverse_word(concat_all(rest)), inv_first);
        //  Connect to postcondition:
        //  Postcondition LHS = concat_all(reverse_invert_factors(factors))
        //    = concat_all(rif_rest ++ [inv_first])  [by def of reverse_invert_factors]
        //    =~= concat(concat_all(rif_rest), concat_all([inv_first]))  [by concat_all_append]
        //    =~= concat(concat_all(rif_rest), inv_first)  [concat_all of singleton]
        //  Key =~= chain for the postcondition:
        //  LHS of postcondition: concat_all(reverse_invert_factors(factors))
        //  reverse_invert_factors(factors) = rif_rest ++ [inv_first] by definition
        //  concat_all_append gave:
        //    concat_all(rif_rest ++ singleton) =~= concat(concat_all(rif_rest), concat_all(singleton))
        //  concat_all(singleton) where singleton = [inv_first]:
        let singleton = Seq::new(1, |_i: int| inv_first);
        assert(singleton.len() == 1);
        assert(singleton.first() == inv_first);
        let singleton_rest = singleton.drop_first();
        assert(singleton_rest.len() == 0);
        assert(concat_all(singleton_rest) =~= empty_word());
        //  concat_all(singleton) = concat(singleton.first(), concat_all(singleton.drop_first()))
        //                        = concat(inv_first, ε)
        assert(concat(inv_first, empty_word()) =~= inv_first) by {
            let c = concat(inv_first, empty_word());
            assert(c.len() == inv_first.len());
            assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_first[k] by {}
        }
        //  So: LHS =~= concat(concat_all(rif_rest), inv_first)

        //  RHS of postcondition: inverse_word(concat_all(factors))
        //  = inverse_word(concat(first, concat_all(rest))) [concat_all unfolds]
        //  =~= concat(inverse_word(concat_all(rest)), inv_first) [from inverse_concat]

        //  equiv_concat_left gave:
        //    equiv(concat(concat_all(rif_rest), inv_first), concat(inv(concat_all(rest)), inv_first))
        //  LHS =~= postcondition LHS (shown above)
        //  RHS =~= postcondition RHS (from inverse_concat)
        //  So: equiv(postcondition LHS, postcondition RHS). QED.
        return;
    }
}

///  Generated subgroup is closed under inverse.
pub proof fn lemma_subgroup_inverse(
    p: Presentation, gens: Seq<Word>, w: Word,
)
    requires
        in_generated_subgroup(p, gens, w),
        presentation_valid(p),
        word_valid(w, p.num_generators),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, inverse_word(w)),
{
    let n = p.num_generators;
    let fa: Seq<Word> = choose|fa: Seq<Word>|
        #[trigger] factors_from_generators(gens, fa)
        && equiv_in_presentation(p, concat_all(fa), w);

    let rif = reverse_invert_factors(fa);
    lemma_reverse_invert_preserves_generators(gens, fa);
    lemma_reverse_invert_is_inverse(p, fa);
    //  concat_all(rif) ≡ inv(concat_all(fa))

    //  concat_all(fa) is word_valid (each factor is gens[i] or inv(gens[i]), all word_valid):
    lemma_concat_all_word_valid(gens, fa, n);

    //  inv(concat_all(fa)) ≡ inv(w) by lemma_equiv_inverse:
    lemma_equiv_inverse(p, concat_all(fa), w);

    //  Chain: concat_all(rif) ≡ inv(concat_all(fa)) ≡ inv(w)
    crate::word::lemma_inverse_word_valid(concat_all(fa), n);
    crate::word::lemma_inverse_word_valid(w, n);
    crate::presentation::lemma_equiv_transitive(p,
        concat_all(rif), inverse_word(concat_all(fa)), inverse_word(w));

    //  in_generated_subgroup(concat_all(rif)): rif satisfies factors_from_generators, and
    //  concat_all(rif) ≡ concat_all(rif) by reflexivity.
    crate::presentation::lemma_equiv_refl(p, concat_all(rif));
    assert(in_generated_subgroup(p, gens, concat_all(rif)));
    //  + equiv(concat_all(rif), inv(w)) → in_generated_subgroup(inv(w))
    lemma_in_subgroup_equiv(p, gens, concat_all(rif), inverse_word(w));
}

//  ============================================================
//  Part K2: Coset invariance — same coset → same canonical rep
//  ============================================================

///  same_left_coset is symmetric.
proof fn lemma_same_left_coset_symmetric(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        same_left_coset(data, g2, g1),
{
    //  same_left_coset(g1, g2) = in_left_subgroup(concat(inv(g1), g2))
    //  same_left_coset(g2, g1) = in_left_subgroup(concat(inv(g2), g1))
    //  concat(inv(g2), g1) = inv(concat(inv(g1), g2)) approximately
    //  inv(concat(inv(g1), g2)) = concat(inv(g2), inv(inv(g1))) = concat(inv(g2), g1)
    //  So: in_left_subgroup(concat(inv(g2), g1)) follows from
    //      in_left_subgroup(concat(inv(g1), g2)) + subgroup inverse closure.

    let diff12 = concat(inverse_word(g1), g2);
    //  in_left_subgroup(diff12) is given.
    //  inv(diff12) = inv(concat(inv(g1), g2)) =~= concat(inv(g2), inv(inv(g1)))
    //             =~= concat(inv(g2), g1) [by inverse involution]
    crate::word::lemma_inverse_concat(inverse_word(g1), g2);
    //  inv(diff12) =~= concat(inv(g2), inv(inv(g1)))
    crate::word::lemma_inverse_involution(g1);
    //  inv(inv(g1)) =~= g1

    //  inv(diff12) =~= concat(inv(g2), g1)
    let diff21 = concat(inverse_word(g2), g1);

    //  in_left_subgroup(diff12) → in_left_subgroup(inv(diff12)) by subgroup inverse
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g1, data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(g1), g2, data.p1.num_generators);
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], data.p1.num_generators) by {
        assert(word_valid(data.identifications[i].0, data.p1.num_generators));
    }
    lemma_subgroup_inverse(data.p1, a_words(data), diff12);
    //  in_left_subgroup(inv(diff12))
    //  inv(diff12) =~= diff21, so in_left_subgroup(diff21)
}

///  same_left_coset is transitive.
proof fn lemma_same_left_coset_transitive(
    data: AmalgamatedData, g1: Word, g2: Word, g3: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        same_left_coset(data, g2, g3),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        word_valid(g3, data.p1.num_generators),
    ensures
        same_left_coset(data, g1, g3),
{
    //  same_left_coset(g1, g2) = in_left_subgroup(inv(g1) * g2)
    //  same_left_coset(g2, g3) = in_left_subgroup(inv(g2) * g3)
    //  same_left_coset(g1, g3) = in_left_subgroup(inv(g1) * g3)
    //  inv(g1) * g3 = inv(g1) * g2 * inv(g2) * g3
    //  = (inv(g1)*g2) * (inv(g2)*g3)
    //  Both factors are in the subgroup → product is in the subgroup (by concat closure).
    let d12 = concat(inverse_word(g1), g2);
    let d23 = concat(inverse_word(g2), g3);

    //  in_left_subgroup(d12) && in_left_subgroup(d23)
    //  → in_left_subgroup(concat(d12, d23)) by subgroup_concat
    lemma_subgroup_concat(data.p1, a_words(data), d12, d23);
    //  concat(d12, d23) = concat(concat(inv(g1), g2), concat(inv(g2), g3))
    //                   =~= concat(inv(g1), concat(g2, concat(inv(g2), g3)))
    //                   and g2 * inv(g2) ≡ ε...
    //  Actually: concat(d12, d23) ≡ inv(g1) * g2 * inv(g2) * g3 ≡ inv(g1) * g3 (group theory)
    //  So in_left_subgroup(concat(d12, d23)) and concat(d12, d23) ≡ inv(g1)*g3
    //  → in_left_subgroup(inv(g1)*g3) by equiv closure.

    //  The equiv: concat(d12, d23) ≡ concat(inv(g1), g3) because:
    //  d12 * d23 = inv(g1)*g2*inv(g2)*g3
    //  g2*inv(g2) ≡ ε, so inv(g1)*g2*inv(g2)*g3 ≡ inv(g1)*g3.
    //  Formally: by right inverse of g2 + congruence.
    crate::presentation_lemmas::lemma_word_inverse_right(data.p1, g2);
    //  g2 * inv(g2) ≡ ε
    //  concat(d12, d23) = concat(concat(inv(g1), g2), concat(inv(g2), g3))
    //  ≡ concat(inv(g1), concat(g2, concat(inv(g2), g3))) [assoc]
    //  ≡ concat(inv(g1), concat(concat(g2, inv(g2)), g3)) [assoc]
    //  ≡ concat(inv(g1), concat(ε, g3)) [g2*inv(g2) ≡ ε congruence]
    //  = concat(inv(g1), g3) [concat(ε, g3) =~= g3]
    //  This chain needs several transitivity + congruence steps.
    //  For now: use lemma_in_subgroup_equiv to bridge.
    let d13 = concat(inverse_word(g1), g3);
    let p1 = data.p1;
    crate::word::lemma_inverse_word_valid(g1, p1.num_generators);
    crate::word::lemma_inverse_word_valid(g2, p1.num_generators);

    //  Step 1: g2 * inv(g2) ≡ ε → concat(concat(g2, inv(g2)), g3) ≡ concat(ε, g3)
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        concat(g2, inverse_word(g2)), empty_word(), g3);

    //  Step 2: seq assoc + =~= to get equiv(concat(g2, concat(inv(g2), g3)), g3)
    assert(concat(concat(g2, inverse_word(g2)), g3)
        =~= concat(g2, concat(inverse_word(g2), g3))) by {
        let l = concat(concat(g2, inverse_word(g2)), g3);
        let r = concat(g2, concat(inverse_word(g2), g3));
        assert(l.len() == r.len());
        assert forall|k: int| 0 <= k < l.len() implies l[k] == r[k]
        by { if k < g2.len() {} else if k < g2.len() + inverse_word(g2).len() {} else {} }
    }
    assert(concat(empty_word(), g3) =~= g3) by {
        let c = concat(empty_word(), g3);
        assert(c.len() == g3.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == g3[k] by {}
    }
    //  Now Z3 has equiv(concat(g2, concat(inv(g2), g3)), g3)

    //  Step 3: right-congruence with inv(g1):
    crate::presentation_lemmas::lemma_equiv_concat_right(p1,
        inverse_word(g1),
        concat(g2, concat(inverse_word(g2), g3)),
        g3);
    //  LHS of the equiv =~= concat(d12, d23) by seq associativity:
    assert(concat(inverse_word(g1), concat(g2, concat(inverse_word(g2), g3)))
        =~= concat(d12, d23)) by {
        let l = concat(inverse_word(g1), concat(g2, concat(inverse_word(g2), g3)));
        let r = concat(d12, d23);
        assert(l.len() == r.len());
        assert forall|k: int| 0 <= k < l.len() implies l[k] == r[k] by {
            if k < inverse_word(g1).len() {}
            else if k < inverse_word(g1).len() + g2.len() {}
            else {}
        }
    }
    //  So: equiv(concat(d12, d23), d13).
    lemma_in_subgroup_equiv(p1, a_words(data), concat(d12, d23), d13);
}

///  If no_pred_below(pred, m) and pred(k), then k >= m.
///  Contrapositive: if k < m, then !pred(k) (from no_pred_below).
proof fn lemma_no_pred_below_implies_ge(pred: spec_fn(nat) -> bool, m: nat, k: nat)
    requires
        no_pred_below(pred, m),
        pred(k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else {
        if k == (m - 1) as nat {
            //  no_pred_below(pred, m) = !pred(m-1) && ... But pred(k) = pred(m-1). Contradiction.
        } else if k < (m - 1) as nat {
            //  no_pred_below(pred, m) = !pred(m-1) && no_pred_below(pred, m-1)
            lemma_no_pred_below_implies_ge(pred, (m - 1) as nat, k);
        }
    }
}

///  If no_shorter_coset_word(g, m) and has_left_coset_word_of_len(g, k), then k >= m.
proof fn lemma_no_shorter_coset_word_implies_ge(
    data: AmalgamatedData, g: Word, m: nat, k: nat,
)
    requires
        no_shorter_coset_word(data, g, m),
        has_left_coset_word_of_len(data, g, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else {
        if k == (m - 1) as nat {
            //  no_shorter_coset_word(g, m) = !has(g, m-1) && ... But has(g, k) = has(g, m-1). Contradiction.
        } else if k < (m - 1) as nat {
            lemma_no_shorter_coset_word_implies_ge(data, g, (m - 1) as nat, k);
        }
    }
}

///  Helper: if same_left_coset(g1, g2), then has_left_coset_word_of_len(g1, l) iff has_...(g2, l).
///  Specifically: has_left_coset_word_of_len(g2, l) → has_left_coset_word_of_len(g1, l).
proof fn lemma_coset_word_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        has_left_coset_word_of_len(data, g2, l),
    ensures
        has_left_coset_word_of_len(data, g1, l),
{
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g2, w) && w.len() == l;
    lemma_same_left_coset_transitive(data, g1, g2, w);
}

///  Min-length coset invariance: same coset → same min length.
proof fn lemma_left_min_len_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_min_coset_len(data, g1) == left_min_coset_len(data, g2),
{
    let l1 = left_min_coset_len(data, g1);
    let l2 = left_min_coset_len(data, g2);

    //  Satisfiability: both chooses are satisfiable
    lemma_left_min_coset_len_satisfiable(data, g1);
    lemma_left_min_coset_len_satisfiable(data, g2);

    //  Transfer: coset word at l2 for g2 → also for g1 (and vice versa)
    lemma_coset_word_transfer(data, g1, g2, l2);
    //  has_left_coset_word_of_len(g1, l2) — so pred1(l2) holds
    lemma_same_left_coset_symmetric(data, g1, g2);
    lemma_coset_word_transfer(data, g2, g1, l1);
    //  has_left_coset_word_of_len(g2, l1) — so pred2(l1) holds

    //  The choose returned l1 satisfying is_min_coset_len(g1, l1).
    //  Since the choose is satisfiable (from above), l1 satisfies the full predicate.
    //  is_min_coset_len includes no_shorter_coset_word. These are NAMED spec fns, Z3 can extract.
    assert(is_min_coset_len(data, g1, l1));
    assert(no_shorter_coset_word(data, g1, l1));
    lemma_no_shorter_coset_word_implies_ge(data, g1, l1, l2);

    assert(is_min_coset_len(data, g2, l2));
    assert(no_shorter_coset_word(data, g2, l2));
    lemma_no_shorter_coset_word_implies_ge(data, g2, l2, l1);
    //  l1 >= l2 && l2 >= l1 → l1 == l2
}

///  If no_smaller_coset_lex and has_word_of_len_rank, then rank >= min.
proof fn lemma_no_smaller_coset_lex_implies_ge(
    data: AmalgamatedData, g: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_coset_lex(data, g, l, m),
        has_left_coset_word_of_len_rank(data, g, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else {
        if k == (m - 1) as nat {
        } else if k < (m - 1) as nat {
            lemma_no_smaller_coset_lex_implies_ge(data, g, l, (m - 1) as nat, k);
        }
    }
}

///  Scan for min lex rank at a given length.
proof fn lemma_scan_min_coset_lex(
    data: AmalgamatedData, g: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_left_coset_word_of_len_rank(data, g, l, bound),
        current <= bound,
        no_smaller_coset_lex(data, g, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_coset_lex(data, g, l, r),
    decreases bound - current,
{
    if has_left_coset_word_of_len_rank(data, g, l, current) {
        assert(is_min_coset_lex(data, g, l, current));
    } else {
        lemma_scan_min_coset_lex(data, g, l, current + 1, bound);
    }
}

///  Lex satisfiability: left_min_coset_lex's choose is satisfiable.
proof fn lemma_left_min_coset_lex_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        is_min_coset_lex(data, g, left_min_coset_len(data, g), left_min_coset_lex(data, g)),
{
    lemma_left_min_coset_len_satisfiable(data, g);
    let l = left_min_coset_len(data, g);
    //  has_left_coset_word_of_len(g, l) → exists w with right length
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l;
    //  w has lex rank word_lex_rank_base(w, lex_base(data))
    let wr = word_lex_rank_base(w, lex_base(data));
    assert(has_left_coset_word_of_len_rank(data, g, l, wr));
    assert(no_smaller_coset_lex(data, g, l, 0nat));
    lemma_scan_min_coset_lex(data, g, l, 0, wr);
}

///  Lex transfer: coset word at (l, r) for g2 → also for g1.
proof fn lemma_coset_lex_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat, r: nat,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        has_left_coset_word_of_len_rank(data, g2, l, r),
    ensures
        has_left_coset_word_of_len_rank(data, g1, l, r),
{
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g2, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r;
    lemma_same_left_coset_transitive(data, g1, g2, w);
}

///  Lex invariance: same coset → same min lex rank (at the same length).
proof fn lemma_left_min_lex_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_min_coset_lex(data, g1) == left_min_coset_lex(data, g2),
{
    lemma_left_min_len_coset_invariant(data, g1, g2);
    let l = left_min_coset_len(data, g1);
    //  l == left_min_coset_len(g2)

    let r1 = left_min_coset_lex(data, g1);
    let r2 = left_min_coset_lex(data, g2);

    lemma_left_min_coset_lex_satisfiable(data, g1);
    lemma_left_min_coset_lex_satisfiable(data, g2);

    //  Transfer: lex word at (l, r2) for g2 → also for g1 (and vice versa)
    lemma_coset_lex_transfer(data, g1, g2, l, r2);
    lemma_same_left_coset_symmetric(data, g1, g2);
    lemma_coset_lex_transfer(data, g2, g1, l, r1);

    //  r1 has no_smaller_coset_lex(g1, l, r1). has(g1, l, r2) holds. → r2 >= r1.
    assert(is_min_coset_lex(data, g1, l, r1));
    assert(no_smaller_coset_lex(data, g1, l, r1));
    lemma_no_smaller_coset_lex_implies_ge(data, g1, l, r1, r2);

    assert(is_min_coset_lex(data, g2, l, r2));
    assert(no_smaller_coset_lex(data, g2, l, r2));
    lemma_no_smaller_coset_lex_implies_ge(data, g2, l, r2, r1);
}

///  Coset invariance: same_left_coset(g1, g2) → left_canonical_rep(g1) =~= left_canonical_rep(g2).
///  Proof: same min length (above) → same min lex rank (similar) → same word (lex rank injective).
pub proof fn lemma_left_rep_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_canonical_rep(data, g1) =~= left_canonical_rep(data, g2),
{
    lemma_left_min_len_coset_invariant(data, g1, g2);
    lemma_left_min_lex_coset_invariant(data, g1, g2);
    let l = left_min_coset_len(data, g1);
    let r = left_min_coset_lex(data, g1);

    //  Both reps satisfy: len == l, lex_rank_base == r (same l and r).
    lemma_left_rep_props(data, g1);
    lemma_left_rep_props(data, g2);
    let rep1 = left_canonical_rep(data, g1);
    let rep2 = left_canonical_rep(data, g2);

    //  rep1.len() == l && word_lex_rank_base(rep1, base) == r
    //  rep2.len() == l && word_lex_rank_base(rep2, base) == r
    //  By lex rank injectivity: rep1 =~= rep2.
    let base = lex_base(data);
    //  Need: symbol_to_column < base for all symbols in rep1 and rep2.
    //  word_valid(rep_i, n) means generator_index < n, so symbol_to_column < 2*n < 2*n+1 = base.
    assert forall|k: int| 0 <= k < rep1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep1[k]) < base
    by {
        assert(symbol_valid(rep1[k], data.p1.num_generators));
        match rep1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert forall|k: int| 0 <= k < rep2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep2[k]) < base
    by {
        assert(symbol_valid(rep2[k], data.p1.num_generators));
        match rep2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    //  The chooses are satisfiable (from left_rep_props).
    //  So rep1 and rep2 satisfy their predicates, including lex rank == r.
    //  Explicitly assert the lex rank equality:
    assert(word_lex_rank_base(rep1, base) == r);
    assert(word_lex_rank_base(rep2, base) == r);
    assert(word_lex_rank_base(rep1, base) == word_lex_rank_base(rep2, base));
    assert(base > 0) by { assert(lex_base(data) == 2 * data.p1.num_generators + 1); }
    lemma_word_lex_rank_base_injective(rep1, rep2, base);
}

//  ============================================================
//  Part K3: action_preserves_canonical
//  ============================================================

///  act_word preserves word_valid(h, k) by induction on word length.
///  Base: act_word(ε, h, syls) = (h, syls), preserves trivially.
///  Step: act_word([s] ++ rest, h, syls) = act_word(rest, act_sym(s, h, syls)).
///    Need: act_sym preserves word_valid(h, k).
///    act_sym dispatches to act_left_sym or act_right_sym.
///    Both produce h from left_h_part or right_h_part (choose with word_valid in predicate).
///    The merge case produces concat(merged_h, new_h) — both word_valid → concat is word_valid.
///
///  The choose satisfiability is the key: we need the products encountered
///  during the action to have decompositions. This holds because any valid
///  word in G₁ (or G₂) has a coset decomposition.
///
///  For now: we take action_preserves_canonical as a precondition.
///  The proof requires showing choose satisfiability at each step,
///  which follows the same lemma_nat_well_ordering + choose extraction pattern.

///  For a G₁-word w ≡ ε in G₁ acting on identity state:
///  act_word(w, ε, []) gives a state whose decomposition matches the identity.
///
///  This combines the action-to-decompose connection (for single symbols, already proved)
///  with the equivalence chain. The full multi-symbol connection is the remaining gap.
///
///  For now, we provide the key building blocks. The full act-to-decompose induction
///  is deferred — it requires showing the transversal decomposition is compatible
///  with the step-by-step merging logic.

///  AFP injectivity from the textbook reduced-sequence action.
///
///  If:
///    - The action is well-defined (relators and inverse pairs act trivially)
///    - w is a G₁-word equivalent to ε in the AFP
///    - There exists a K-word witness for the decomposition (for the converse)
///
///  Then: w ≡ ε in G₁.
///  AFP injectivity: if w is a G₁-word and w ≡ ε in the AFP, and we know
///  the canonical rep and h-part are trivial (from action well-definedness),
///  then w ≡ ε in G₁.
///
///  The full chain: action_well_defined + derivation → act(w) = identity
///                  → left_canonical_rep(w) = ε, left_h_part(w) = ε
///                  → w ≡ ε in G₁ (by converse)
///
///  The act-to-decompose connection is needed to eliminate the rep/h preconditions.
///  For now, the rep = ε and h = ε conditions come from the action analysis.
pub proof fn lemma_afp_injectivity_textbook(
    data: AmalgamatedData,
    w: Word,
    h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(w, data.p1.num_generators),
        //  The decomposition gives identity (from action well-definedness + derivation)
        left_canonical_rep(data, w) =~= empty_word(),
        left_h_part(data, w) =~= empty_word(),
        //  Decomposability witness: the left_h_part choose is satisfiable
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1, apply_embedding(a_words(data), h_witness), w),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    lemma_g1_decompose_converse(data, w, h_witness);
}

//  ============================================================
//  Part L: H-part equivalence invariance
//  ============================================================

///  Transfer h-witnesses between equivalent targets.
///  If target1 ≡ target2 and there's a K-word h with embed_a(h) ≡ target1,
///  then embed_a(h) ≡ target2 too (by transitivity).
proof fn lemma_h_witness_transfer(
    data: AmalgamatedData, target1: Word, target2: Word, l: nat,
)
    requires
        has_left_h_witness_of_len(data, target1, l),
        equiv_in_presentation(data.p1, target1, target2),
        presentation_valid(data.p1),
    ensures
        has_left_h_witness_of_len(data, target2, l),
{
    let h: Word = choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), h), target1);
    crate::presentation::lemma_equiv_transitive(
        data.p1, apply_embedding(a_words(data), h), target1, target2);
}

///  Transfer h-witness with lex rank between equivalent targets.
proof fn lemma_h_witness_rank_transfer(
    data: AmalgamatedData, target1: Word, target2: Word, l: nat, r: nat,
)
    requires
        has_left_h_witness_of_len_rank(data, target1, l, r),
        equiv_in_presentation(data.p1, target1, target2),
        presentation_valid(data.p1),
    ensures
        has_left_h_witness_of_len_rank(data, target2, l, r),
{
    let h: Word = choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), h), target1);
    crate::presentation::lemma_equiv_transitive(
        data.p1, apply_embedding(a_words(data), h), target1, target2);
}

///  If no_smaller_h_lex(target, l, m) and has_h_witness_rank(target, l, k), then k >= m.
proof fn lemma_no_smaller_h_lex_implies_ge(
    data: AmalgamatedData, target: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_h_lex(data, target, l, m),
        has_left_h_witness_of_len_rank(data, target, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else if k == m - 1 {
        //  no_smaller_h_lex says !has_rank(k) but we have has_rank(k) → contradiction
    } else if k < m - 1 {
        lemma_no_smaller_h_lex_implies_ge(data, target, l, (m - 1) as nat, k);
    }
}

///  If g1 ≡ g2 in G₁, then same_left_coset(g1, g2).
///  Proof: inv(g1) · g2 ≡ inv(g1) · g1 ≡ ε, and ε is in the subgroup.
proof fn lemma_same_left_coset_from_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
    ensures
        same_left_coset(data, g1, g2),
{
    //  inv(g1) · g2 ≡ inv(g1) · g1 ≡ ε
    crate::presentation::lemma_equiv_symmetric(data.p1, g1, g2);
    crate::presentation_lemmas::lemma_equiv_concat_right(
        data.p1, inverse_word(g1), g2, g1);
    crate::presentation_lemmas::lemma_word_inverse_left(data.p1, g1);
    crate::presentation::lemma_equiv_transitive(data.p1,
        concat(inverse_word(g1), g2), concat(inverse_word(g1), g1), empty_word());

    //  ε is in the subgroup (empty factors)
    let empty_factors = Seq::<Word>::empty();
    assert(crate::benign::factors_from_generators(a_words(data), empty_factors));
    assert(crate::benign::concat_all(empty_factors) =~= empty_word());
    crate::presentation::lemma_equiv_refl(data.p1, empty_word());
    //  equiv(ε, inv(g1) · g2) by symmetry
    crate::word::lemma_inverse_word_valid(g1, data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(g1), g2, data.p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(data.p1,
        concat(inverse_word(g1), g2), empty_word());
    assert(in_generated_subgroup(data.p1, a_words(data), empty_word()));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        empty_word(), concat(inverse_word(g1), g2));
}

///  Helper: derive target1 ≡ target2 from g1 ≡ g2 (using coset rep invariance).
proof fn lemma_targets_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
    ensures ({
        let target1 = concat(inverse_word(left_canonical_rep(data, g1)), g1);
        let target2 = concat(inverse_word(left_canonical_rep(data, g2)), g2);
        equiv_in_presentation(data.p1, target1, target2)
    }),
{
    let rep1 = left_canonical_rep(data, g1);
    let rep2 = left_canonical_rep(data, g2);
    //  rep1 =~= rep2 by coset invariance
    lemma_left_rep_props(data, g1);
    lemma_left_rep_props(data, g2);
    lemma_same_left_coset_from_equiv(data, g1, g2);
    lemma_left_rep_coset_invariant(data, g1, g2);
    //  rep1 =~= rep2, so inverse_word(rep1) =~= inverse_word(rep2)
    //  equiv(inv(rep1), inv(rep2)) by refl (same word)
    crate::presentation::lemma_equiv_refl(data.p1, inverse_word(rep1));
    //  target1 ≡ target2 by equiv_concat
    crate::presentation_lemmas::lemma_equiv_concat(
        data.p1, inverse_word(rep1), inverse_word(rep2), g1, g2);
}

///  Min h-length is invariant under G₁-equivalence of the input word.
///  If g1 ≡ g2 in G₁, then left_h_min_len(g1) == left_h_min_len(g2).
proof fn lemma_left_h_min_len_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(inverse_word(left_canonical_rep(data, g1)), g1)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(inverse_word(left_canonical_rep(data, g2)), g2)),
    ensures
        left_h_min_len(data, g1) == left_h_min_len(data, g2),
{
    let target1 = concat(inverse_word(left_canonical_rep(data, g1)), g1);
    let target2 = concat(inverse_word(left_canonical_rep(data, g2)), g2);

    //  target1 ≡ target2
    lemma_targets_equiv(data, g1, g2);

    //  Establish satisfiability for both sides
    assert(has_left_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_left_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_left_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_left_h_witness_of_len(data, target2, l);
    assert(pred1(h_witness1.len() as nat));
    assert(pred2(h_witness2.len() as nat));
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    let l1 = left_h_min_len(data, g1);
    let l2 = left_h_min_len(data, g2);

    //  Transfer: has_witness(target1, l1) → has_witness(target2, l1)
    lemma_h_witness_transfer(data, target1, target2, l1);
    //  Transfer: has_witness(target2, l2) → has_witness(target1, l2)
    lemma_left_rep_props(data, g1);
    crate::word::lemma_inverse_word_valid(left_canonical_rep(data, g1), data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(left_canonical_rep(data, g1)), g1, data.p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(data.p1, target1, target2);
    lemma_h_witness_transfer(data, target2, target1, l2);

    //  Bidirectional ≥
    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  Min h-lex rank is invariant under G₁-equivalence.
proof fn lemma_left_h_min_lex_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(inverse_word(left_canonical_rep(data, g1)), g1)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(inverse_word(left_canonical_rep(data, g2)), g2)),
    ensures
        left_h_min_lex(data, g1) == left_h_min_lex(data, g2),
{
    let target1 = concat(inverse_word(left_canonical_rep(data, g1)), g1);
    let target2 = concat(inverse_word(left_canonical_rep(data, g2)), g2);

    //  target1 ≡ target2
    lemma_targets_equiv(data, g1, g2);

    //  l1 == l2
    lemma_left_h_min_len_equiv_invariant(data, g1, g2, h_witness1, h_witness2);
    let l = left_h_min_len(data, g1);

    //  Establish lex satisfiability for both
    lemma_left_h_min_lex_satisfiable(data, g1, h_witness1);
    lemma_left_h_min_lex_satisfiable(data, g2, h_witness2);

    let r1 = left_h_min_lex(data, g1);
    let r2 = left_h_min_lex(data, g2);

    //  Transfer: has_rank(target1, l, r1) → has_rank(target2, l, r1)
    assert(is_min_h_lex(data, target1, l, r1));
    assert(is_min_h_lex(data, target2, l, r2));
    lemma_h_witness_rank_transfer(data, target1, target2, l, r1);
    lemma_left_rep_props(data, g1);
    crate::word::lemma_inverse_word_valid(left_canonical_rep(data, g1), data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(left_canonical_rep(data, g1)), g1, data.p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(data.p1, target1, target2);
    lemma_h_witness_rank_transfer(data, target2, target1, l, r2);

    //  Bidirectional ≥
    assert(no_smaller_h_lex(data, target1, l, r1));
    assert(no_smaller_h_lex(data, target2, l, r2));
    lemma_no_smaller_h_lex_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_implies_ge(data, target1, l, r1, r2);
}

///  Extract all four choose properties from left_h_part.
proof fn lemma_left_h_part_full_props(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(inverse_word(left_canonical_rep(data, g)), g)),
    ensures ({
        let rep = left_canonical_rep(data, g);
        let h = left_h_part(data, g);
        let target = concat(inverse_word(rep), g);
        &&& word_valid(h, k_size(data))
        &&& h.len() == left_h_min_len(data, g)
        &&& word_lex_rank_base(h, h_lex_base(data)) == left_h_min_lex(data, g)
        &&& equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h), target)
    }),
{
    lemma_left_h_part_props(data, g, h_witness);
    lemma_left_h_min_lex_satisfiable(data, g, h_witness);
}

///  H-part is invariant under G₁-equivalence:
///  if g1 ≡ g2 in G₁, then left_h_part(g1) =~= left_h_part(g2).
pub proof fn lemma_left_h_part_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(inverse_word(left_canonical_rep(data, g1)), g1)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(inverse_word(left_canonical_rep(data, g2)), g2)),
    ensures
        left_h_part(data, g1) =~= left_h_part(data, g2),
{
    //  min len and min lex are both invariant
    lemma_left_h_min_len_equiv_invariant(data, g1, g2, h_witness1, h_witness2);
    lemma_left_h_min_lex_equiv_invariant(data, g1, g2, h_witness1, h_witness2);
    let l = left_h_min_len(data, g1);
    let r = left_h_min_lex(data, g1);

    //  Both h-parts satisfy: len == l, lex_rank == r
    lemma_left_h_part_full_props(data, g1, h_witness1);
    lemma_left_h_part_full_props(data, g2, h_witness2);
    let h1 = left_h_part(data, g1);
    let h2 = left_h_part(data, g2);

    //  By lex rank injectivity on K-words
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < h1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h1[k]) < base
    by {
        assert(symbol_valid(h1[k], k_size(data)));
        match h1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert forall|k: int| 0 <= k < h2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h2[k]) < base
    by {
        assert(symbol_valid(h2[k], k_size(data)));
        match h2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(h1, h2, base);
}

//  ============================================================
//  Part M: General inverse pair triviality for G₁ symbols
//  ============================================================

///  Helper: [inv(s)] · embed_a(left_h_part([s]·embed_a(h))) ≡ embed_a(h)
///  when left_canonical_rep([s]·embed_a(h)) = ε (product in subgroup).
///  [inv(s)] · embed_a(a_rcoset_h(product)) ≡ embed_a(h)
///  when a_rcoset_rep(product) = ε (product in subgroup, right-coset convention).
proof fn lemma_inv_s_h_prime_equiv_embed_h(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word(),
    ensures ({
        let embed_h = apply_embedding(a_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let h_prime = a_rcoset_h(data, product);
        let embed_h_prime = apply_embedding(a_words(data), h_prime);
        let product2 = concat(Seq::new(1, |_i: int| inverse_symbol(s)), embed_h_prime);
        equiv_in_presentation(data.p1, product2, embed_h)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    reveal(presentation_valid);

    //  word_valid setup
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  Right-coset h-part: embed_a(h') ≡ product · inv(rep) = product (since rep = ε)
    //  target = concat(product, inv(ε)) =~= product
    assert(concat(product, inverse_word(e)) =~= product) by {
        assert(inverse_word(e).len() == 0);
        assert(concat(product, inverse_word(e)).len() == product.len());
        assert forall|k: int| 0 <= k < product.len()
            implies concat(product, inverse_word(e))[k] == product[k] by {}
    }
    //  product ∈ A (from a_rcoset_rep = ε): derive in_left_subgroup
    lemma_a_rcoset_rep_props(data, product);
    //  same_a_rcoset(product, ε) → in_left_subgroup(concat(product, inv(ε)))
    crate::presentation::lemma_equiv_refl(p1, product);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(product, inverse_word(a_rcoset_rep(data, product))),
        product);
    //  in_left_subgroup(product) established

    //  Both reps = ε
    lemma_in_subgroup_both_reps_eps(data, product);
    //  left_canonical_rep(product) =~= ε, a_rcoset_rep(product) =~= ε
    //  So left target = inv(ε)·product =~= product =~= product·inv(ε) = right target

    //  Get h-witness from left-coset infrastructure
    lemma_h_witness_exists(data, product);
    let hw: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, product)), product));
    //  hw satisfies equiv(embed_a(hw), left_target). left_target =~= product =~= right_target.
    //  So hw also witnesses for right target.
    lemma_a_rcoset_h_satisfiable(data, product, hw);
    let h_prime = a_rcoset_h(data, product);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);

    //  embed_a(h') ≡ product (since target = concat(product, inv(ε)) =~= product)
    //  product2 = [inv(s)] · embed_a(h') ≡ [inv(s)] · product = [inv(s)]·[s]·embed_a(h)
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, inv_s_word, embed_h_prime, product);

    //  [inv(s)]·[s] ≡ ε (free reduction)
    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= e);
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p1, s_word);

    //  Associativity + cancellation
    assert(concat(inv_s_word, concat(s_word, embed_h)) =~=
           concat(concat(inv_s_word, s_word), embed_h)) by {
        let lhs = concat(inv_s_word, concat(s_word, embed_h));
        let rhs = concat(concat(inv_s_word, s_word), embed_h);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { if k < 2 {} else {} }
        }
    }
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, concat(inv_s_word, s_word), e, embed_h);
    assert(concat(e, embed_h) =~= embed_h) by {
        assert(concat(e, embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len() implies concat(e, embed_h)[k] == embed_h[k] by {}
    }
    assert(concat(inv_s_word, product) =~= concat(concat(inv_s_word, s_word), embed_h));

    crate::presentation::lemma_equiv_transitive(p1,
        concat(inv_s_word, embed_h_prime),
        concat(concat(inv_s_word, s_word), embed_h),
        embed_h);
    return;
}

///  Helper: embed_a(h) is in the trivial left coset (canonical rep = ε).
proof fn lemma_embed_in_trivial_coset(data: AmalgamatedData, h: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
    ensures
        same_left_coset(data, apply_embedding(a_words(data), h), empty_word()),
        left_canonical_rep(data, apply_embedding(a_words(data), h)) =~= empty_word(),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let embed_h = apply_embedding(a_words(data), h);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_inverse_word_valid(embed_h, n1);

    //  embed_a(h) ∈ subgroup → inv(embed_a(h)) ∈ subgroup
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_subgroup_inverse(p1, a_words(data), embed_h);

    //  same_left_coset(embed_h, ε) = in_left_subgroup(concat(inv(embed_h), ε))
    //  concat(inv(embed_h), ε) =~= inv(embed_h), which is in subgroup
    assert(concat(inverse_word(embed_h), e) =~= inverse_word(embed_h)) by {
        assert(concat(inverse_word(embed_h), e).len() == inverse_word(embed_h).len());
        assert forall|k: int| 0 <= k < inverse_word(embed_h).len()
            implies concat(inverse_word(embed_h), e)[k] == inverse_word(embed_h)[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p1, inverse_word(embed_h));
    lemma_in_subgroup_equiv(p1, a_words(data),
        inverse_word(embed_h), concat(inverse_word(embed_h), e));

    //  left_canonical_rep(embed_h) =~= left_canonical_rep(ε) =~= ε
    lemma_left_rep_identity(data);
    lemma_left_rep_props(data, embed_h);
    lemma_left_rep_coset_invariant(data, embed_h, e);
    return;
}

///  Helper: when product2 ≡ embed_a(h) and both are in the subgroup,
///  a_rcoset_rep(product2) =~= ε and a_rcoset_h(product2) =~= h (for canonical h).
proof fn lemma_subgroup_rcoset_restore(
    data: AmalgamatedData, product2: Word, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(product2, data.p1.num_generators),
        equiv_in_presentation(data.p1, product2, apply_embedding(a_words(data), h)),
        is_canonical_state(data, h, Seq::<Syllable>::empty()),
    ensures
        a_rcoset_rep(data, product2) =~= empty_word(),
        a_rcoset_h(data, product2) =~= h,
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  embed_h in subgroup. product2 ≡ embed_h → product2 in subgroup
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p1, product2, embed_h);
    lemma_in_subgroup_equiv(p1, a_words(data), embed_h, product2);

    //  product2 in subgroup → both reps = ε
    lemma_in_subgroup_both_reps_eps(data, product2);
    lemma_in_subgroup_both_reps_eps(data, embed_h);

    //  left_h_part invariance: product2 ≡ embed_h, both left reps = ε
    //  → left_h_part(product2) =~= left_h_part(embed_h)
    lemma_h_witness_exists(data, product2);
    lemma_h_witness_exists(data, embed_h);
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, product2)), product2));
    let hw_eh: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, embed_h)), embed_h));
    lemma_left_h_part_equiv_invariant(data, product2, embed_h, hw2, hw_eh);
    //  left_h_part(product2) =~= left_h_part(embed_h) =~= h (by is_canonical_state)
    //  Since both reps = ε: a_rcoset_h = left_h_part (same target)
}

///  Subcase A: G₁ inverse pair when product = [s]·embed_a(h) is in the subgroup (rep = ε).
proof fn lemma_inverse_pair_g1_subcase_a(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word(),
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  Split [s, inv(s)] into [s] ++ [inv(s)]
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);
    let h_prime = a_rcoset_h(data, product);
    lemma_act_word_single(data, inv_s, h_prime, syls);

    //  product2 ≡ embed_a(h) (from helper — uses right-coset convention)
    lemma_inv_s_h_prime_equiv_embed_h(data, s, h);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let product2 = concat(inv_s_word, embed_h_prime);

    //  product2 word_valid + in subgroup → reps = ε, h-part = h
    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
    //  h_prime word_valid from rcoset_h_satisfiable
    lemma_a_rcoset_rep_props(data, product);
    crate::presentation::lemma_equiv_refl(p1, product);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(product, inverse_word(a_rcoset_rep(data, product))), product);
    lemma_in_subgroup_both_reps_eps(data, product);
    lemma_h_witness_exists(data, product);
    let hw_p: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, product)), product));
    lemma_a_rcoset_h_satisfiable(data, product, hw_p);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n1);

    //  Use helper for the restore
    lemma_subgroup_rcoset_restore(data, product2, h);
}

///  Right-coset decomposition identity: embed_a(a_rcoset_h(g)) · a_rcoset_rep(g) ≡ g.
///  This is the textbook identity g = h·c at the word level.
pub proof fn lemma_rcoset_decomposition(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures
        equiv_in_presentation(data.p1,
            concat(apply_embedding(a_words(data), a_rcoset_h(data, g)),
                   a_rcoset_rep(data, g)),
            g),
        word_valid(a_rcoset_h(data, g), k_size(data)),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let h = a_rcoset_h(data, g);
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    //  embed_a(h) ≡ target = g·inv(rep) from h-part satisfiability
    lemma_a_rcoset_h_satisfiable(data, g, h_witness);

    //  concat(embed_a(h), rep) ≡ concat(g·inv(rep), rep) [by equiv_concat_left]
    lemma_a_rcoset_rep_props(data, g);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, embed_h, target, rep);

    //  concat(g·inv(rep), rep) =~= concat(g, concat(inv(rep), rep)) [associativity]
    crate::word::lemma_inverse_word_valid(rep, n1);
    assert(concat(concat(g, inverse_word(rep)), rep) =~=
           concat(g, concat(inverse_word(rep), rep))) by {
        let lhs = concat(concat(g, inverse_word(rep)), rep);
        let rhs = concat(g, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < g.len() as int {} else {
                let j = k - g.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }

    //  concat(inv(rep), rep) ≡ ε [word_inverse_left]
    crate::presentation_lemmas::lemma_word_inverse_left(p1, rep);

    //  concat(g, concat(inv(rep), rep)) ≡ concat(g, ε) [equiv_concat_right]
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, g, concat(inverse_word(rep), rep), empty_word());

    //  concat(g, ε) =~= g
    assert(concat(g, empty_word()) =~= g) by {
        assert(concat(g, empty_word()).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, empty_word())[k] == g[k] by {}
    }

    //  Chain: concat(embed_h, rep) ≡ concat(target, rep) =~= concat(g, concat(inv(rep), rep))
    //         ≡ concat(g, ε) =~= g
    crate::presentation::lemma_equiv_transitive(p1,
        concat(embed_h, rep),
        concat(g, concat(inverse_word(rep), rep)),
        g);
    return;
}

///  General helper: [inv(s)] · embed_a(a_rcoset_h(product)) · a_rcoset_rep(product) ≡ embed_a(h)
///  where product = [s]·embed_a(h). Works for all subcases (rep = ε or rep ≠ ε).
proof fn lemma_inv_s_rcoset_product_equiv(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p1.num_generators,
    ensures ({
        let embed_h = apply_embedding(a_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let h_prime = a_rcoset_h(data, product);
        let embed_h_prime = apply_embedding(a_words(data), h_prime);
        let rep_prime = a_rcoset_rep(data, product);
        let full = concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)), embed_h_prime), rep_prime);
        &&& equiv_in_presentation(data.p1, full, embed_h)
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  h-witness from subgroup structure
    lemma_a_rcoset_rep_props(data, product);
    crate::word::lemma_inverse_word_valid(rep_prime, n1);
    crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(product, inverse_word(rep_prime)));
    let hw_r: Word = choose|hw: Word| word_valid(hw, a_words(data).len())
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(product, inverse_word(rep_prime)));
    assert(a_words(data).len() == k_size(data));

    //  embed_a(h') · rep' ≡ product
    lemma_rcoset_decomposition(data, product, hw_r);
    let h_prime = a_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);

    //  [inv(s)] · (embed_a(h')·rep') ≡ [inv(s)] · product
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, inv_s_word, concat(embed_h_prime, rep_prime), product);

    //  Associativity: [inv(s)]·embed_h'·rep' =~= [inv(s)]·(embed_h'·rep')
    let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
    assert(full =~= concat(inv_s_word, concat(embed_h_prime, rep_prime))) by {
        let lhs = full;
        let rhs = concat(inv_s_word, concat(embed_h_prime, rep_prime));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_h_prime.len() as int {} else {}
            }
        }
    }

    //  [inv(s)]·product = [inv(s)]·[s]·embed_h → free reduction → embed_h
    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= e);
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p1, s_word);
    assert(concat(inv_s_word, concat(s_word, embed_h)) =~=
           concat(concat(inv_s_word, s_word), embed_h)) by {
        let lhs = concat(inv_s_word, concat(s_word, embed_h));
        let rhs = concat(concat(inv_s_word, s_word), embed_h);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { if k < 2 {} else {} }
        }
    }
    crate::presentation_lemmas::lemma_equiv_concat_left(
        p1, concat(inv_s_word, s_word), e, embed_h);
    assert(concat(e, embed_h) =~= embed_h) by {
        assert(concat(e, embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(e, embed_h)[k] == embed_h[k] by {}
    }
    assert(concat(inv_s_word, product) =~= concat(concat(inv_s_word, s_word), embed_h));

    //  Chain: full =~= [inv(s)]·(embed_h'·rep') ≡ [inv(s)]·product
    //         =~= ([inv(s)]·[s])·embed_h ≡ ε·embed_h =~= embed_h
    crate::presentation::lemma_equiv_transitive(p1,
        concat(inv_s_word, concat(embed_h_prime, rep_prime)),
        concat(concat(inv_s_word, s_word), embed_h),
        embed_h);
    return;
}

///  Helper for subcase B: the merge step.
///  Given that act_word([s, inv(s)], h, syls) unfolds to
///  act_sym(inv(s), h', [Syl(left, rep')] + syls) where the merge gives (h, syls).
proof fn lemma_inverse_pair_g1_subcase_b_merge(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let h_prime = a_rcoset_h(data, product);
        let rep_prime = a_rcoset_rep(data, product);
        let embed_h_prime = apply_embedding(a_words(data), h_prime);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        &&& a_rcoset_rep(data, full_product2) =~= empty_word()
        &&& a_rcoset_h(data, full_product2) =~= h
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    let s_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  General helper gives: [inv(s)]·embed_a(h')·rep' ≡ embed_a(h) + word_valid(h')
    lemma_inv_s_rcoset_product_equiv(data, s, h);

    let h_prime = a_rcoset_h(data, product);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);

    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n1);
    lemma_a_rcoset_rep_props(data, product);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n1);
    lemma_subgroup_rcoset_restore(data, full_product2, h);
}

///  Subgroup left cancellation: if x ∈ A and concat(x, y) ∈ A, then y ∈ A.
proof fn lemma_subgroup_left_cancel(
    p: Presentation, gens: Seq<Word>, x: Word, y: Word,
)
    requires
        presentation_valid(p),
        word_valid(x, p.num_generators),
        word_valid(y, p.num_generators),
        in_generated_subgroup(p, gens, x),
        in_generated_subgroup(p, gens, concat(x, y)),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, y),
{
    //  inv(x) ∈ A, concat(x,y) ∈ A → concat(inv(x), concat(x,y)) ∈ A
    crate::word::lemma_inverse_word_valid(x, p.num_generators);
    lemma_subgroup_inverse(p, gens, x);
    crate::word::lemma_concat_word_valid(x, y, p.num_generators);
    lemma_subgroup_concat(p, gens, inverse_word(x), concat(x, y));
    //  concat(inv(x), concat(x,y)) ≡ y
    crate::presentation_lemmas::lemma_word_inverse_left(p, x);
    crate::presentation_lemmas::lemma_equiv_concat_left(p, concat(inverse_word(x), x), empty_word(), y);
    assert(concat(inverse_word(x), concat(x, y)) =~=
           concat(concat(inverse_word(x), x), y)) by {
        let lhs = concat(inverse_word(x), concat(x, y));
        let rhs = concat(concat(inverse_word(x), x), y);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inverse_word(x).len() as int {} else {
                let j = k - inverse_word(x).len() as int;
                if j < x.len() as int {} else {}
            }
        }
    }
    assert(concat(empty_word(), y) =~= y) by {
        assert(concat(empty_word(), y).len() == y.len());
        assert forall|k: int| 0 <= k < y.len()
            implies concat(empty_word(), y)[k] == y[k] by {}
    }
    lemma_in_subgroup_equiv(p, gens,
        concat(inverse_word(x), concat(x, y)), y);
}

///  The inverse step's product is NOT in the subgroup when rep' ≠ ε.
///  Proof by contradiction: if product_inv ∈ A, then inv(rep') ∈ A → rep' ∈ A → product ∈ A → rep' = ε.
proof fn lemma_inv_step_rep_nonzero(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let h_prime = a_rcoset_h(data, product);
        let product_inv = concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(a_words(data), h_prime));
        !(a_rcoset_rep(data, product_inv) =~= empty_word())
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    //  Get h_prime and product_inv
    lemma_inv_s_rcoset_product_equiv(data, s, h);
    let h_prime = a_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let product_inv = concat(inv_s_word, embed_h_prime);

    //  Proof by contradiction: assume a_rcoset_rep(product_inv) =~= ε
    //  Then product_inv ∈ A. We'll show this implies rep' =~= ε, contradiction.
    if a_rcoset_rep(data, product_inv) =~= empty_word() {
        //  product_inv ∈ A
        assert(word_valid(inv_s_word, n1)) by {
            assert forall|k: int| 0 <= k < inv_s_word.len()
                implies symbol_valid(#[trigger] inv_s_word[k], n1) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n1);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

        lemma_a_rcoset_rep_props(data, product_inv);
        crate::presentation::lemma_equiv_refl(p1, product_inv);
        lemma_in_subgroup_equiv(p1, a_words(data),
            concat(product_inv, inverse_word(a_rcoset_rep(data, product_inv))), product_inv);
        //  product_inv ∈ A

        //  embed_a(h') · rep' ≡ product (from rcoset decomposition)
        lemma_a_rcoset_rep_props(data, product);
        crate::word::lemma_inverse_word_valid(rep_prime, n1);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n1);
        lemma_subgroup_to_k_word(p1, a_words(data), concat(product, inverse_word(rep_prime)));
        let hw_r: Word = choose|hw: Word| word_valid(hw, a_words(data).len())
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(product, inverse_word(rep_prime)));
        assert(a_words(data).len() == k_size(data));
        lemma_rcoset_decomposition(data, product, hw_r);
        //  concat(embed_a(h'), rep') ≡ product

        //  [inv(s)] · embed_a(h') · rep' ≡ embed_a(h) (from general helper)
        //  Already have: concat(concat(inv_s_word, embed_h_prime), rep_prime) ≡ embed_a(h)
        let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        //  full ≡ embed_a(h) ∈ A → full ∈ A
        lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
        crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n1);
        crate::presentation::lemma_equiv_symmetric(p1, full, embed_h);
        lemma_in_subgroup_equiv(p1, a_words(data), embed_h, full);

        //  full = concat(product_inv, rep_prime). product_inv ∈ A and full ∈ A
        //  → rep_prime ∈ A (by left cancellation)
        lemma_subgroup_left_cancel(p1, a_words(data), product_inv, rep_prime);

        //  rep' ∈ A → product ∈ A:
        //  same_a_rcoset(product, rep') gives product·inv(rep') ∈ A
        //  rep' ∈ A → concat(product·inv(rep'), rep') ∈ A by subgroup_concat
        //  And concat(product·inv(rep'), rep') ≡ product → product ∈ A
        lemma_subgroup_concat(p1, a_words(data),
            concat(product, inverse_word(rep_prime)), rep_prime);

        //  concat(concat(product, inv(rep')), rep') ≡ product (assoc + inv cancellation)
        assert(concat(concat(product, inverse_word(rep_prime)), rep_prime) =~=
               concat(product, concat(inverse_word(rep_prime), rep_prime))) by {
            let lhs = concat(concat(product, inverse_word(rep_prime)), rep_prime);
            let rhs = concat(product, concat(inverse_word(rep_prime), rep_prime));
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < product.len() as int {} else {
                    let j = k - product.len() as int;
                    if j < inverse_word(rep_prime).len() as int {} else {}
                }
            }
        }
        crate::presentation_lemmas::lemma_word_inverse_left(p1, rep_prime);
        crate::presentation_lemmas::lemma_equiv_concat_right(
            p1, product, concat(inverse_word(rep_prime), rep_prime), empty_word());
        assert(concat(product, empty_word()) =~= product) by {
            assert(concat(product, empty_word()).len() == product.len());
            assert forall|k: int| 0 <= k < product.len()
                implies concat(product, empty_word())[k] == product[k] by {}
        }
        let s_word = Seq::new(1, |_i: int| s);
        assert(word_valid(s_word, n1)) by {
            assert forall|k: int| 0 <= k < s_word.len()
                implies symbol_valid(#[trigger] s_word[k], n1) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
        lemma_in_subgroup_equiv(p1, a_words(data),
            concat(concat(product, inverse_word(rep_prime)), rep_prime), product);
        //  product ∈ A → a_rcoset_rep(product) =~= ε
        lemma_a_rcoset_in_subgroup(data, product);
        //  But rep' = a_rcoset_rep(product) ≠ ε. Contradiction!
    }
}

///  Helper: When the merge case of act_left_sym produces merged_rep = ε,
///  the result is (combined_h, syllables.drop_first()).
///  This is a small focused helper to help Z3 unfold act_left_sym.
proof fn lemma_act_left_sym_merge_absorbed(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        syllables.first().is_left,
        a_rcoset_rep(data,
            concat(concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)),
                   syllables.first().rep))
            =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        act_left_sym(data, s, h, syllables)
            == (a_rcoset_h(data, full_product), syllables.drop_first())
    }),
{
    //  Z3 unfolds act_left_sym: rep ≠ ε, first syl left → merge case
    //  merged_rep = ε → (combined_h, syllables.drop_first())
}

///  Subcase B: G₁ inverse pair when rep' ≠ ε and first syllable is not left (prepend).
///  After s: (h', [Syl(left, rep')] + syls). After inv(s): merge absorbs → (h, syls).
proof fn lemma_inverse_pair_g1_subcase_b(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syls.len() == 0 || !syls.first().is_left,
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    let h_prime = a_rcoset_h(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  Split [s, inv(s)] into [s] ++ [inv(s)]
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);
    //  act_word([s], h, syls) = (h', [Syl(left, rep')] + syls) [since rep' ≠ ε, not left first]

    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep_prime }) + syls;
    lemma_act_word_single(data, inv_s, h_prime, new_syls);

    //  Merge helper gives: a_rcoset_rep(full_product2) = ε, a_rcoset_h(full_product2) = h
    lemma_inverse_pair_g1_subcase_b_merge(data, s, h, syls);

    //  Help Z3 with the unfolding
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let product_inv = concat(inv_s_word, embed_h_prime);
    let rep_inv = a_rcoset_rep(data, product_inv);
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == rep_prime);
    assert(new_syls.drop_first() =~= syls);

    //  Help Z3 see the full_product2 matches the merge product in act_left_sym
    let full_product2 = concat(product_inv, rep_prime);
    assert(full_product2 == concat(concat(inv_s_word, embed_h_prime), rep_prime));

    //  Prove rep_inv ≠ ε (product_inv not in subgroup)
    lemma_inv_step_rep_nonzero(data, s, h);

    //  Use the merge helper to establish act_left_sym result
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    lemma_act_left_sym_merge_absorbed(data, inv_s, h_prime, new_syls);
    //  act_left_sym(inv_s, h', new_syls) = (a_rcoset_h(full_product2), new_syls.drop_first()) = (h, syls)
}

//  ============================================================
//  Part N: Right A-coset rep invariance (parallel to left coset)
//  ============================================================

///  4-part cancellation: concat(concat(a, inv(b)), concat(b, c)) ≡ concat(a, c).
///  Used for right A-coset transitivity: a·inv(b)·b·c ≡ a·c.
proof fn lemma_four_part_cancel(
    p: Presentation, a: Word, b: Word, c: Word,
)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        word_valid(c, p.num_generators),
    ensures
        equiv_in_presentation(p,
            concat(concat(a, inverse_word(b)), concat(b, c)),
            concat(a, c)),
{
    crate::word::lemma_inverse_word_valid(b, p.num_generators);
    //  inv(b)·b ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p, b);
    //  concat(inv(b), concat(b, c)) =~= concat(concat(inv(b), b), c) [associativity]
    assert(concat(inverse_word(b), concat(b, c)) =~=
           concat(concat(inverse_word(b), b), c)) by {
        let lhs = concat(inverse_word(b), concat(b, c));
        let rhs = concat(concat(inverse_word(b), b), c);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inverse_word(b).len() as int {} else {
                let j = k - inverse_word(b).len() as int;
                if j < b.len() as int {} else {}
            }
        }
    }
    //  concat(concat(inv(b), b), c) ≡ concat(ε, c) =~= c
    crate::presentation_lemmas::lemma_equiv_concat_left(
        p, concat(inverse_word(b), b), empty_word(), c);
    assert(concat(empty_word(), c) =~= c) by {
        assert(concat(empty_word(), c).len() == c.len());
        assert forall|k: int| 0 <= k < c.len()
            implies concat(empty_word(), c)[k] == c[k] by {}
    }
    //  concat(inv(b), concat(b, c)) =~= concat(concat(inv(b), b), c) → equiv by refl
    crate::word::lemma_concat_word_valid(b, c, p.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(b), concat(b, c), p.num_generators);
    crate::presentation::lemma_equiv_refl(p, concat(inverse_word(b), concat(b, c)));
    //  Now: equiv(lhs, concat(concat(inv(b), b), c)) since lhs =~= rhs
    //  And: concat(concat(inv(b), b), c) ≡ concat(ε, c) from equiv_concat_left
    //  Chain through concat(ε, c) =~= c
    //  concat(a, concat(inv(b), concat(b, c))) ≡ concat(a, c) [equiv_concat_right]
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p, a, concat(inverse_word(b), concat(b, c)), c);
    //  concat(concat(a, inv(b)), concat(b, c)) =~= concat(a, concat(inv(b), concat(b, c))) [associativity]
    assert(concat(concat(a, inverse_word(b)), concat(b, c)) =~=
           concat(a, concat(inverse_word(b), concat(b, c)))) by {
        let lhs = concat(concat(a, inverse_word(b)), concat(b, c));
        let rhs = concat(a, concat(inverse_word(b), concat(b, c)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < a.len() as int {} else {
                let j = k - a.len() as int;
                if j < inverse_word(b).len() as int {} else {}
            }
        }
    }
}

///  Transfer: same rcoset → coset words transfer.
proof fn lemma_a_rcoset_word_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
        has_a_rcoset_word_of_len(data, g1, l),
    ensures
        has_a_rcoset_word_of_len(data, g2, l),
{
    //  Extract witness w with same_a_rcoset(g1, w) && w.len() == l
    let n1 = data.p1.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g1, w) && w.len() == l;

    //  word_valid setup (needed before subgroup lemmas)
    crate::word::lemma_inverse_word_valid(g1, n1);
    crate::word::lemma_inverse_word_valid(g2, n1);
    crate::word::lemma_inverse_word_valid(w, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(w), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n1);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], data.p1.num_generators)
    by { assert(word_valid(data.identifications[i].0, data.p1.num_generators)); }

    lemma_subgroup_inverse(data.p1, a_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    //  inv(concat(g1, inv(g2))) =~= concat(inv(inv(g2)), inv(g1)) =~= concat(g2, inv(g1))
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert(inverse_word(inverse_word(g2)) =~= g2);
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by {
            if k < g2.len() as int {} else {}
        }
    }
    crate::presentation::lemma_equiv_refl(data.p1, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        inv_pair, concat(g2, inverse_word(g1)));

    //  concat(g2·inv(g1), g1·inv(w)) in subgroup (from subgroup_concat above)
    lemma_subgroup_concat(data.p1, a_words(data),
        concat(g2, inverse_word(g1)),
        concat(g1, inverse_word(w)));

    //  Now: concat(g2, inv(g1))·concat(g1, inv(w)) ≡ concat(g2, inv(w))
    //  by associativity + inv(g1)·g1 cancellation
    //  concat(concat(g2, inv(g1)), concat(g1, inv(w)))
    //  =~= concat(g2, concat(inv(g1), concat(g1, inv(w))))
    //  =~= concat(g2, concat(concat(inv(g1), g1), inv(w)))
    //  ≡ concat(g2, concat(ε, inv(w))) =~= concat(g2, inv(w))

    //  concat(g2·inv(g1), g1·inv(w)) ≡ g2·inv(w) by 4-part cancellation
    lemma_four_part_cancel(data.p1, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
    //  same_a_rcoset(g2, w) → has_a_rcoset_word_of_len(g2, l)
}

///  Transfer with rank: same rcoset → rank witnesses transfer.
proof fn lemma_a_rcoset_word_rank_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat, r: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
        has_a_rcoset_word_of_len_rank(data, g1, l, r),
    ensures
        has_a_rcoset_word_of_len_rank(data, g2, l, r),
{
    //  Extract the rank witness from g1's coset
    let n1 = data.p1.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g1, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r;
    //  w is in g1's rcoset → also in g2's rcoset (by transitivity)
    //  same_a_rcoset(g1, w) and same_a_rcoset(g1, g2) → same_a_rcoset(g2, w)
    lemma_same_a_rcoset_symmetric(data, g1, g2);
    //  same_a_rcoset(g2, g1) + same_a_rcoset(g1, w) → same_a_rcoset(g2, w)
    //  Use the transfer infrastructure from lemma_a_rcoset_word_transfer
    //  Actually, we just need: same_a_rcoset(g2, w) = in_left_subgroup(g2·inv(w))
    //  From same_a_rcoset(g2, g1) + same_a_rcoset(g1, w):
    //    g2·inv(g1) ∈ A and g1·inv(w) ∈ A → (g2·inv(g1))·(g1·inv(w)) ∈ A
    //    ≡ g2·inv(w) ∈ A. So same_a_rcoset(g2, w).
    lemma_subgroup_concat(data.p1, a_words(data),
        concat(g2, inverse_word(g1)),
        concat(g1, inverse_word(w)));
    crate::word::lemma_inverse_word_valid(w, n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n1);
    //  4-part cancellation: concat(g2·inv(g1), g1·inv(w)) ≡ g2·inv(w)
    lemma_four_part_cancel(data.p1, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
}

///  No shorter → ≥ for right A-cosets.
proof fn lemma_no_shorter_a_rcoset_word_implies_ge(
    data: AmalgamatedData, g: Word, m: nat, k: nat,
)
    requires
        no_shorter_a_rcoset_word(data, g, m),
        has_a_rcoset_word_of_len(data, g, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else if k == m - 1 {
    } else if k < m - 1 {
        lemma_no_shorter_a_rcoset_word_implies_ge(data, g, (m - 1) as nat, k);
    }
}

///  same_a_rcoset is symmetric.
proof fn lemma_same_a_rcoset_symmetric(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
    ensures
        same_a_rcoset(data, g2, g1),
{
    let n1 = data.p1.num_generators;
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::word::lemma_inverse_word_valid(g2, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n1);
    lemma_subgroup_inverse(data.p1, a_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by { if k < g2.len() as int {} else {} }
    }
    crate::word::lemma_inverse_word_valid(g1, n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n1);
    crate::presentation::lemma_equiv_refl(data.p1, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        inv_pair, concat(g2, inverse_word(g1)));
}

///  Right A-coset rep invariance: same_a_rcoset → same a_rcoset_rep.
pub proof fn lemma_a_rcoset_rep_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
    ensures
        a_rcoset_rep(data, g1) =~= a_rcoset_rep(data, g2),
{
    let n1 = data.p1.num_generators;
    //  Satisfiability for both
    lemma_a_rcoset_rep_satisfiable(data, g1);
    lemma_a_rcoset_rep_satisfiable(data, g2);
    let l1 = a_rcoset_min_len(data, g1);
    let l2 = a_rcoset_min_len(data, g2);

    //  Transfer in both directions → bidirectional ≥ → equal
    lemma_a_rcoset_word_transfer(data, g1, g2, l1);
    lemma_same_a_rcoset_symmetric(data, g1, g2);
    lemma_a_rcoset_word_transfer(data, g2, g1, l2);

    //  Bidirectional ≥
    lemma_no_shorter_a_rcoset_word_implies_ge(data, g2, l2, l1);
    lemma_no_shorter_a_rcoset_word_implies_ge(data, g1, l1, l2);
    //  l1 == l2
    let l = l1;

    //  Lex rank: same argument
    let w1: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g1, w) && w.len() == l;
    let wr1 = word_lex_rank_base(w1, lex_base(data));
    assert(has_a_rcoset_word_of_len_rank(data, g1, l, wr1));
    assert(no_smaller_a_rcoset_lex(data, g1, l, 0nat));
    lemma_scan_a_rcoset_lex(data, g1, l, 0, wr1);
    let w2: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g2, w) && w.len() == l;
    let wr2 = word_lex_rank_base(w2, lex_base(data));
    assert(has_a_rcoset_word_of_len_rank(data, g2, l, wr2));
    assert(no_smaller_a_rcoset_lex(data, g2, l, 0nat));
    lemma_scan_a_rcoset_lex(data, g2, l, 0, wr2);

    let r1 = a_rcoset_min_lex(data, g1);
    let r2 = a_rcoset_min_lex(data, g2);
    //  Transfer rank witnesses via explicit helper
    lemma_a_rcoset_word_rank_transfer(data, g1, g2, l, r1);
    lemma_a_rcoset_word_rank_transfer(data, g2, g1, l, r2);
    lemma_no_smaller_a_rcoset_lex_implies_ge(data, g2, l, r2, r1);
    lemma_no_smaller_a_rcoset_lex_implies_ge(data, g1, l, r1, r2);
    //  r1 == r2

    //  Rep invariance by lex rank injectivity
    lemma_a_rcoset_rep_props(data, g1);
    lemma_a_rcoset_rep_props(data, g2);
    let rep1 = a_rcoset_rep(data, g1);
    let rep2 = a_rcoset_rep(data, g2);
    let base = lex_base(data);
    assert forall|k: int| 0 <= k < rep1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep1[k]) < base
    by {
        assert(symbol_valid(rep1[k], n1));
        match rep1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert forall|k: int| 0 <= k < rep2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep2[k]) < base
    by {
        assert(symbol_valid(rep2[k], n1));
        match rep2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert(base > 0) by { assert(lex_base(data) == 2 * data.p1.num_generators + 1); }
    lemma_word_lex_rank_base_injective(rep1, rep2, base);
}

///  No smaller right A-coset lex implies ≥.
proof fn lemma_no_smaller_a_rcoset_lex_implies_ge(
    data: AmalgamatedData, g: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_a_rcoset_lex(data, g, l, m),
        has_a_rcoset_word_of_len_rank(data, g, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else if k == m - 1 {
    } else if k < m - 1 {
        lemma_no_smaller_a_rcoset_lex_implies_ge(data, g, l, (m - 1) as nat, k);
    }
}

//  ============================================================
//  Part O: Inverse pair subcase C (merge with existing left syllable)
//  ============================================================

///  Free reduction: [inv(s)]·[s]·w ≡ w for any word w.
proof fn lemma_inv_s_s_cancel(
    p: Presentation, s: Symbol, w: Word,
)
    requires
        presentation_valid(p),
        word_valid(w, p.num_generators),
        generator_index(s) < p.num_generators,
    ensures
        equiv_in_presentation(p,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                   concat(Seq::new(1, |_i: int| s), w)),
            w),
{
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= empty_word());
    }
    //  [inv(s)]·[s] ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p, s_word);
    //  concat(concat(inv_s, s), w) ≡ concat(ε, w) =~= w
    crate::presentation_lemmas::lemma_equiv_concat_left(
        p, concat(inv_s_word, s_word), empty_word(), w);
    assert(concat(empty_word(), w) =~= w) by {
        assert(concat(empty_word(), w).len() == w.len());
        assert forall|k: int| 0 <= k < w.len()
            implies concat(empty_word(), w)[k] == w[k] by {}
    }
    //  Associativity: [inv(s)]·([s]·w) =~= ([inv(s)]·[s])·w
    assert(concat(inv_s_word, concat(s_word, w)) =~=
           concat(concat(inv_s_word, s_word), w)) by {
        let lhs = concat(inv_s_word, concat(s_word, w));
        let rhs = concat(concat(inv_s_word, s_word), w);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { if k < 2 {} else {} }
        }
    }
    //  =~= chains are automatic, ≡ needs transitive through concat(ε, w)
    crate::word::lemma_concat_word_valid(inv_s_word, concat(s_word, w), p.num_generators);
    assert(word_valid(s_word, p.num_generators)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], p.num_generators) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, w, p.num_generators);
    crate::word::lemma_inverse_word_valid(s_word, p.num_generators);
    crate::presentation::lemma_equiv_refl(p, concat(inv_s_word, concat(s_word, w)));
    crate::presentation::lemma_equiv_transitive(p,
        concat(inv_s_word, concat(s_word, w)),
        concat(concat(inv_s_word, s_word), w),
        concat(empty_word(), w));
}

///  Key for subcase C: [inv(s)]·embed_a(combined_h)·merged_rep ≡ embed_a(h)·c₁
///  where full_product = [s]·embed_a(h)·c₁ is the merge product.
proof fn lemma_inv_s_rcoset_merge_equiv(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        generator_index(s) < data.p1.num_generators,
    ensures ({
        let n1 = data.p1.num_generators;
        let embed_h = apply_embedding(a_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let full_product = concat(product, c1);
        let combined_h = a_rcoset_h(data, full_product);
        let embed_ch = apply_embedding(a_words(data), combined_h);
        let merged_rep = a_rcoset_rep(data, full_product);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full = concat(concat(inv_s_word, embed_ch), merged_rep);
        &&& equiv_in_presentation(data.p1, full, concat(embed_h, c1))
        &&& word_valid(combined_h, k_size(data))
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let full_product = concat(product, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
    crate::word::lemma_concat_word_valid(product, c1, n1);

    //  Rcoset decomposition of full_product: embed_a(combined_h)·merged_rep ≡ full_product
    lemma_a_rcoset_rep_props(data, full_product);
    let merged_rep = a_rcoset_rep(data, full_product);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(full_product, inverse_word(merged_rep)));
    let hw: Word = choose|hw: Word| word_valid(hw, a_words(data).len())
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(full_product, inverse_word(merged_rep)));
    assert(a_words(data).len() == k_size(data));
    lemma_rcoset_decomposition(data, full_product, hw);
    let combined_h = a_rcoset_h(data, full_product);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    let embed_ch = apply_embedding(a_words(data), combined_h);

    //  [inv(s)]·(embed_a(ch)·merged_rep) ≡ [inv(s)]·full_product
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, inv_s_word, concat(embed_ch, merged_rep), full_product);

    //  [inv(s)]·full_product = [inv(s)]·[s]·embed_a(h)·c1 ≡ embed_a(h)·c1
    //  full_product = concat(product, c1) = concat(concat(s_word, embed_h), c1)
    //  [inv(s)]·concat(concat(s_word, embed_h), c1) =~= [inv(s)]·[s]·concat(embed_h, c1) by associativity
    assert(concat(inv_s_word, concat(concat(s_word, embed_h), c1)) =~=
           concat(inv_s_word, concat(s_word, concat(embed_h, c1)))) by {
        let lhs = concat(inv_s_word, concat(concat(s_word, embed_h), c1));
        let rhs = concat(inv_s_word, concat(s_word, concat(embed_h, c1)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else {
                let j = k - 1;
                if j < s_word.len() as int {} else {
                    let j2 = j - s_word.len() as int;
                    if j2 < embed_h.len() as int {} else {}
                }
            }
        }
    }
    //  [inv(s)]·[s]·concat(embed_h, c1) ≡ concat(embed_h, c1) by lemma_inv_s_s_cancel
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    lemma_inv_s_s_cancel(p1, s, concat(embed_h, c1));

    //  Associativity: [inv(s)]·embed_ch·merged_rep =~= [inv(s)]·(embed_ch·merged_rep)
    let full = concat(concat(inv_s_word, embed_ch), merged_rep);
    assert(full =~= concat(inv_s_word, concat(embed_ch, merged_rep))) by {
        let lhs = full;
        let rhs = concat(inv_s_word, concat(embed_ch, merged_rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_ch.len() as int {} else {}
            }
        }
    }

    //  Chain: full =~= [inv(s)]·(embed_ch·merged_rep) ≡ [inv(s)]·full_product
    //         =~= [inv(s)]·[s]·(embed_h·c1) ≡ embed_h·c1
    crate::presentation::lemma_equiv_transitive(p1,
        concat(inv_s_word, concat(embed_ch, merged_rep)),
        concat(inv_s_word, concat(s_word, concat(embed_h, c1))),
        concat(embed_h, c1));
    return;
}

///  Textbook key property: embed_a(h)·c₁ decomposes as (h, c₁) when h is canonical
///  and c₁ is a canonical right A-coset rep (c₁ = a_rcoset_rep(c₁)).
///  Proof: embed_a(h) ∈ A doesn't change the right coset: A·(embed_a(h)·c₁) = A·c₁.
proof fn lemma_rcoset_decompose_subgroup_times_rep(
    data: AmalgamatedData, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        //  h is canonical
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        //  c₁ is a canonical right A-coset rep
        a_rcoset_rep(data, c1) =~= c1,
    ensures
        a_rcoset_rep(data, concat(apply_embedding(a_words(data), h), c1)) =~= c1,
        a_rcoset_h(data, concat(apply_embedding(a_words(data), h), c1)) =~= h,
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(embed_h, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);

    //  same_a_rcoset(product, c1): need product·inv(c1) ∈ A
    //  product·inv(c1) = embed_a(h)·c1·inv(c1) ≡ embed_a(h)
    //  embed_a(h) ∈ A → product·inv(c1) ∈ A
    crate::word::lemma_inverse_word_valid(c1, n1);
    crate::word::lemma_concat_word_valid(product, inverse_word(c1), n1);
    crate::presentation_lemmas::lemma_word_inverse_right(p1, c1);
    //  embed_h · c1 · inv(c1) ≡ embed_h · ε ≡ embed_h
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, embed_h, concat(c1, inverse_word(c1)), empty_word());
    assert(concat(embed_h, empty_word()) =~= embed_h) by {
        assert(concat(embed_h, empty_word()).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(embed_h, empty_word())[k] == embed_h[k] by {}
    }
    //  Associativity: concat(embed_h, concat(c1, inv(c1))) =~= concat(concat(embed_h, c1), inv(c1)) = concat(product, inv(c1))
    assert(concat(embed_h, concat(c1, inverse_word(c1))) =~= concat(product, inverse_word(c1))) by {
        let lhs = concat(embed_h, concat(c1, inverse_word(c1)));
        let rhs = concat(concat(embed_h, c1), inverse_word(c1));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < embed_h.len() as int {} else {
                let j = k - embed_h.len() as int;
                if j < c1.len() as int {} else {}
            }
        }
    }
    //  Chain: product·inv(c1) =~= embed_h·(c1·inv(c1)) ≡ embed_h·ε =~= embed_h
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(embed_h, concat(c1, inverse_word(c1))), embed_h);
    lemma_in_subgroup_equiv(p1, a_words(data), embed_h, concat(product, inverse_word(c1)));
    //  same_a_rcoset(product, c1) established

    //  Right A-coset rep invariance: a_rcoset_rep(product) =~= a_rcoset_rep(c1) = c1
    lemma_a_rcoset_rep_invariant(data, product, c1);
    //  a_rcoset_rep(product) =~= c1 ✓

    //  H-part: target = product·inv(c1) ≡ embed_a(h)
    //  canonical h-part for target ≡ embed_a(h) is h (by canonicality + h-part invariance)
    //  Need: a_rcoset_h(product) =~= h
    //  a_rcoset_h(product) has target = product·inv(a_rcoset_rep(product)) =~= product·inv(c1) ≡ embed_a(h)
    //  The canonical K-word for embed_a(h) is h (from is_canonical_state precondition)
    //  So a_rcoset_h(product) =~= left_h_part(embed_a(h)) =~= h

    //  Establish: product·inv(c1) ≡ embed_a(h) → product and embed_a(h) are in same subgroup equiv class
    //  Use lemma_in_subgroup_both_reps_eps on embed_a(h) to get left_canonical_rep(embed_a(h)) = ε
    lemma_in_subgroup_both_reps_eps(data, embed_h);

    //  product·inv(c1) ≡ embed_a(h) → left_h_part equiv invariance
    //  Both have left_canonical_rep = ε (since both in subgroup)
    lemma_in_subgroup_both_reps_eps(data, concat(product, inverse_word(c1)));

    //  h-part invariance: left_h_part(product·inv(c1)) =~= left_h_part(embed_a(h)) =~= h
    lemma_h_witness_exists(data, concat(product, inverse_word(c1)));
    lemma_h_witness_exists(data, embed_h);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, concat(product, inverse_word(c1)))),
                   concat(product, inverse_word(c1))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, embed_h)), embed_h));
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(embed_h, concat(c1, inverse_word(c1))), embed_h);
    lemma_left_h_part_equiv_invariant(data, concat(product, inverse_word(c1)), embed_h, hw1, hw2);
    //  left_h_part(product·inv(c1)) =~= left_h_part(embed_a(h)) =~= h

    //  Since a_rcoset_rep(product) =~= c1 and left reps = ε:
    //  a_rcoset target = product·inv(c1) = left target (when left rep = ε)
    //  So a_rcoset_h(product) = left_h_part(product·inv(c1)) =~= h
}

///  If g1 ≡ g2, then same_a_rcoset(g1, g2).
pub proof fn lemma_same_a_rcoset_from_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
    ensures
        same_a_rcoset(data, g1, g2),
{
    let p1 = data.p1;
    let n1 = p1.num_generators;
    //  concat(g1, inv(g2)) ≡ concat(g1, inv(g1)) ≡ ε ∈ A
    crate::word::lemma_inverse_word_valid(g1, n1);
    crate::word::lemma_inverse_word_valid(g2, n1);
    crate::presentation::lemma_equiv_symmetric(p1, g1, g2);
    lemma_equiv_inverse(p1, g2, g1);
    crate::presentation::lemma_equiv_refl(p1, g1);
    crate::presentation_lemmas::lemma_equiv_concat(p1,
        g1, g1, inverse_word(g2), inverse_word(g1));
    crate::presentation_lemmas::lemma_word_inverse_right(p1, g1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g1), n1);
    crate::presentation::lemma_equiv_transitive(p1,
        concat(g1, inverse_word(g2)),
        concat(g1, inverse_word(g1)),
        empty_word());
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n1);
    crate::presentation::lemma_equiv_symmetric(p1, concat(g1, inverse_word(g2)), empty_word());
    lemma_in_subgroup_equiv(p1, a_words(data),
        empty_word(), concat(g1, inverse_word(g2)));
}

///  Helper: When the merge case of act_left_sym produces merged_rep ≠ ε,
///  the result replaces the first syllable.
proof fn lemma_act_left_sym_merge_replaced(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        syllables.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
            let full_product = concat(product, syllables.first().rep);
            a_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        let merged_rep = a_rcoset_rep(data, full_product);
        act_left_sym(data, s, h, syllables)
            == (a_rcoset_h(data, full_product),
                Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syllables.drop_first())
    }),
{
    //  Z3 unfolds act_left_sym: rep ≠ ε, first syl left → merge case
    //  merged_rep ≠ ε → replace first syllable
}

///  H-part through equivalence: if g ≡ embed_a(h)·c where c is canonical rep,
///  then a_rcoset_h(g) =~= h (when h is canonical).
///  Uses: target = g·inv(c) ≡ embed_a(h) → subgroup h-part invariance.
proof fn lemma_a_rcoset_h_from_equiv(
    data: AmalgamatedData, g: Word, h: Word, c: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(h, k_size(data)),
        word_valid(c, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, concat(apply_embedding(a_words(data), h), c)),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        a_rcoset_rep(data, c) =~= c,
        a_rcoset_rep(data, g) =~= c,
    ensures
        a_rcoset_h(data, g) =~= h,
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_inverse_word_valid(c, n1);

    //  target_g = g·inv(a_rcoset_rep(g)) = g·inv(c)
    //  target_ehc = (embed_h·c)·inv(c) ≡ embed_h (by word_inverse_right + assoc)
    //  g ≡ embed_h·c → g·inv(c) ≡ (embed_h·c)·inv(c) ≡ embed_h

    //  So target_g ≡ embed_h. Both in subgroup (embed_h ∈ A).
    //  By in_subgroup_both_reps_eps: both left reps = ε.
    //  By left_h_part_equiv_invariant on the targets:
    //  left_h_part(target_g) =~= left_h_part(embed_h) =~= h.
    //  Since a_rcoset_rep(g) =~= c and left_canonical_rep(target_g) = ε:
    //  a_rcoset_h(g) = left_h_part(target_g) (same target, same choose).

    //  target_g ≡ embed_h:
    //  g ≡ embed_h·c → g·inv(c) ≡ (embed_h·c)·inv(c) by concat_left
    crate::word::lemma_concat_word_valid(g, inverse_word(c), n1);
    crate::word::lemma_concat_word_valid(embed_h, c, n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g, concat(embed_h, c), inverse_word(c));
    //  g·inv(c) ≡ (embed_h·c)·inv(c) by equiv_concat_right
    //  (embed_h·c)·inv(c) ≡ embed_h by four_part_cancel(embed_h, c, ε)... no, by word_inverse_right
    crate::presentation_lemmas::lemma_word_inverse_right(p1, c);
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, embed_h,
        concat(c, inverse_word(c)), empty_word());
    assert(concat(embed_h, empty_word()) =~= embed_h) by {
        assert(concat(embed_h, empty_word()).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(embed_h, empty_word())[k] == embed_h[k] by {}
    }
    //  (embed_h·c)·inv(c) =~= embed_h·(c·inv(c)) ≡ embed_h·ε =~= embed_h
    assert(concat(concat(embed_h, c), inverse_word(c)) =~=
           concat(embed_h, concat(c, inverse_word(c)))) by {
        let lhs = concat(concat(embed_h, c), inverse_word(c));
        let rhs = concat(embed_h, concat(c, inverse_word(c)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < embed_h.len() as int {} else {
                let j = k - embed_h.len() as int;
                if j < c.len() as int {} else {}
            }
        }
    }
    crate::word::lemma_concat_word_valid(concat(embed_h, c), inverse_word(c), n1);
    crate::presentation::lemma_equiv_refl(p1, concat(concat(embed_h, c), inverse_word(c)));
    crate::presentation::lemma_equiv_transitive(p1,
        concat(concat(embed_h, c), inverse_word(c)),
        concat(embed_h, concat(c, inverse_word(c))),
        embed_h);
    crate::presentation::lemma_equiv_transitive(p1,
        concat(g, inverse_word(c)), concat(concat(embed_h, c), inverse_word(c)), embed_h);

    //  Both targets ∈ subgroup → both reps = ε → left_h_part invariance applies
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p1, concat(g, inverse_word(c)), embed_h);
    lemma_in_subgroup_equiv(p1, a_words(data), embed_h, concat(g, inverse_word(c)));
    lemma_in_subgroup_both_reps_eps(data, concat(g, inverse_word(c)));
    lemma_in_subgroup_both_reps_eps(data, embed_h);

    //  left_h_part invariance: left_h_part(target_g) =~= left_h_part(embed_h) =~= h
    lemma_h_witness_exists(data, concat(g, inverse_word(c)));
    lemma_h_witness_exists(data, embed_h);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, concat(g, inverse_word(c)))),
                   concat(g, inverse_word(c))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, embed_h)), embed_h));
    lemma_left_h_part_equiv_invariant(data, concat(g, inverse_word(c)), embed_h, hw1, hw2);
}

///  Right cancellation: concat(concat(a, b), inv(b)) ≡ a.
pub proof fn lemma_right_cancel(p: Presentation, a: Word, b: Word)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        equiv_in_presentation(p, concat(concat(a, b), inverse_word(b)), a),
{
    crate::word::lemma_inverse_word_valid(b, p.num_generators);
    crate::presentation_lemmas::lemma_word_inverse_right(p, b);
    crate::presentation_lemmas::lemma_equiv_concat_right(p, a,
        concat(b, inverse_word(b)), empty_word());
    assert(concat(a, empty_word()) =~= a) by {
        assert(concat(a, empty_word()).len() == a.len());
        assert forall|k: int| 0 <= k < a.len()
            implies concat(a, empty_word())[k] == a[k] by {}
    }
    //  assoc: concat(concat(a, b), inv(b)) =~= concat(a, concat(b, inv(b)))
    assert(concat(concat(a, b), inverse_word(b)) =~=
           concat(a, concat(b, inverse_word(b)))) by {
        let lhs = concat(concat(a, b), inverse_word(b));
        let rhs = concat(a, concat(b, inverse_word(b)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < a.len() as int {} else {
                let j = k - a.len() as int;
                if j < b.len() as int {} else {}
            }
        }
    }
    crate::word::lemma_concat_word_valid(a, b, p.num_generators);
    crate::word::lemma_concat_word_valid(concat(a, b), inverse_word(b), p.num_generators);
    //  Chain through concat(a, ε): first equiv, then =~= to a
    crate::word::lemma_concat_word_valid(a, concat(b, inverse_word(b)), p.num_generators);
    crate::word::lemma_concat_word_valid(a, empty_word(), p.num_generators);
    crate::presentation::lemma_equiv_refl(p, concat(a, concat(b, inverse_word(b))));
    //  concat(a, concat(b, inv(b))) ≡ concat(a, ε) =~= a. Two-step chain.
}

///  Idempotency: a_rcoset_rep(a_rcoset_rep(g)) =~= a_rcoset_rep(g).
pub proof fn lemma_a_rcoset_rep_idempotent(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
    ensures
        a_rcoset_rep(data, a_rcoset_rep(data, g)) =~= a_rcoset_rep(data, g),
{
    let rep = a_rcoset_rep(data, g);
    lemma_a_rcoset_rep_props(data, g);
    lemma_same_a_rcoset_symmetric(data, g, rep);
    lemma_a_rcoset_rep_invariant(data, rep, g);
}

///  Helper: the inverse step for C2 — directly establishes act_left_sym via merge_replaced.
///  Requires rep_inv ≠ ε as a precondition (caller provides via case split).
proof fn lemma_c2_inverse_merge_step(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word, combined_h: Word,
    merged_rep: Word, rest_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p1.num_generators),
        generator_index(s) < data.p1.num_generators,
        !(c1 =~= empty_word()),
        !(merged_rep =~= empty_word()),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        a_rcoset_rep(data, c1) =~= c1,
        equiv_in_presentation(data.p1,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)), merged_rep),
            concat(apply_embedding(a_words(data), h), c1)),
        //  The inverse product is NOT in the subgroup
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)))
            =~= empty_word()),
    ensures ({
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep }) + rest_syls;
        act_left_sym(data, inverse_symbol(s), combined_h, new_syls)
            == (h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + rest_syls)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep }) + rest_syls;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    let embed_ch = apply_embedding(a_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_ch), merged_rep, n1);

    //  full_inv ≡ embed_a(h)·c₁ → rcoset rep = c₁ ≠ ε
    let full_inv = concat(concat(inv_s_word, embed_ch), merged_rep);
    lemma_same_a_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_a_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));

    //  Explicitly connect merge_replaced preconditions to local variables
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    assert(!(a_rcoset_rep(data, full_inv) =~= empty_word()));
    //  full_inv = concat(product, first_rep) in merge_replaced's terms
    assert(full_inv == concat(concat(Seq::new(1, |_i: int| inv_s), apply_embedding(a_words(data), combined_h)), new_syls.first().rep));

    //  H-part: a_rcoset_h(full_inv) =~= h (from equiv invariance)
    lemma_a_rcoset_h_from_equiv(data, full_inv, h, c1);

    //  merge_replaced: rep_inv ≠ ε, first syl left, merged_rep ≠ ε
    lemma_act_left_sym_merge_replaced(data, inv_s, combined_h, new_syls);
    //  Result: (a_rcoset_h(full_inv), [Syl(left, a_rcoset_rep(full_inv))] + rest)
    //        = (h, [Syl(left, c₁)] + rest)
}

///  Subcase C: G₁ inverse pair when rep' ≠ ε and first syllable IS left (merge).
///  Forward: merge [s]·embed_a(h)·c₁ → (combined_h, merged_syls).
///  Inverse: [inv(s)]·embed_a(combined_h)·merged_rep ≡ embed_a(h)·c₁ → decompose → (h, c₁, rest).
///
///  C2 rep_inv=ε branch: show merged_rep =~= c₁ and product_inv ≡ embed_a(h).
proof fn lemma_c2_rep_zero_branch(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
    combined_h: Word, merged_rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p1.num_generators),
        generator_index(s) < data.p1.num_generators,
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        a_rcoset_rep(data, c1) =~= c1,
        !(merged_rep =~= empty_word()),
        a_rcoset_rep(data, merged_rep) =~= merged_rep, //  idempotency (caller provides)
        a_rcoset_rep(data, concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(a_words(data), combined_h))) =~= empty_word(), //  product_inv ∈ A
        equiv_in_presentation(data.p1,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)), merged_rep),
            concat(apply_embedding(a_words(data), h), c1)),
    ensures
        merged_rep =~= c1,
        equiv_in_presentation(data.p1,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)),
            apply_embedding(a_words(data), h)),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let embed_ch = apply_embedding(a_words(data), combined_h);
    let product_inv = concat(inv_s_word, embed_ch);
    let full_inv = concat(product_inv, merged_rep);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_inverse_word_valid(c1, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    crate::word::lemma_concat_word_valid(product_inv, merged_rep, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);

    //  Step 1: full_inv·inv(merged_rep) ≡ product_inv ∈ A → same_a_rcoset(full_inv, merged_rep)
    lemma_right_cancel(p1, product_inv, merged_rep);
    lemma_a_rcoset_rep_props(data, product_inv);
    crate::presentation::lemma_equiv_refl(p1, product_inv);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(product_inv, inverse_word(a_rcoset_rep(data, product_inv))), product_inv);
    crate::word::lemma_concat_word_valid(full_inv, inverse_word(merged_rep), n1);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(full_inv, inverse_word(merged_rep)), product_inv);
    lemma_in_subgroup_equiv(p1, a_words(data), product_inv,
        concat(full_inv, inverse_word(merged_rep)));

    //  Step 2: a_rcoset_rep(merged_rep) =~= c₁ via invariant chain
    lemma_same_a_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_same_a_rcoset_symmetric(data, full_inv, merged_rep);
    lemma_a_rcoset_rep_invariant(data, merged_rep, full_inv);
    lemma_a_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));
    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);
    //  a_rcoset_rep(merged_rep) =~= a_rcoset_rep(full_inv) =~= c₁
    //  With idempotency precondition: merged_rep =~= a_rcoset_rep(merged_rep) =~= c₁

    //  Step 3: product_inv ≡ embed_a(h) via right cancellation
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, full_inv, concat(embed_h, c1), inverse_word(c1));
    lemma_right_cancel(p1, product_inv, c1);
    lemma_right_cancel(p1, embed_h, c1);
    crate::presentation::lemma_equiv_transitive(p1,
        product_inv, concat(concat(product_inv, c1), inverse_word(c1)),
        concat(concat(embed_h, c1), inverse_word(c1)));
    crate::presentation::lemma_equiv_transitive(p1,
        product_inv, concat(concat(embed_h, c1), inverse_word(c1)), embed_h);
}


#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g1_subcase_c2(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        syls.first().is_left,
        //  Sub-subcase: merged_rep ≠ ε
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
            let full_product = concat(product, syls.first().rep);
            a_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = a_rcoset_h(data, full_product);
    let merged_rep = a_rcoset_rep(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  Split and compose
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);
    //  Forward: merged_rep ≠ ε → state = (combined_h, [Syl(left, merged_rep)] + syls.drop_first())
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
        + syls.drop_first();
    lemma_act_word_single(data, inv_s, combined_h, new_syls);

    //  c1 word_valid and c1 ≠ ε from is_canonical_state
    assert(word_valid(c1, n1));
    assert(!(c1 =~= e));
    crate::word::lemma_concat_word_valid(product, c1, n1);

    //  Forward step: merge_replaced
    lemma_act_left_sym_merge_replaced(data, s, h, syls);

    //  [inv(s)]·embed_a(combined_h)·merged_rep ≡ embed_a(h)·c₁
    lemma_inv_s_rcoset_merge_equiv(data, s, h, c1);

    //  Decompose embed_a(h)·c₁: rep = c₁, h-part = h (textbook key property)
    assert(a_rcoset_rep(data, c1) =~= c1);
    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  generator_index for dispatch
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    //  Setup for inverse step
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    assert(new_syls.drop_first() =~= syls.drop_first());

    let embed_ch = apply_embedding(a_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    let product_inv = concat(inv_s_word, embed_ch);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    lemma_a_rcoset_rep_props(data, full_product);
    crate::word::lemma_concat_word_valid(product_inv, merged_rep, n1);

    //  full_inv ≡ embed_a(h)·c₁ → same rcoset → rep(full_inv) =~= c₁ ≠ ε
    let full_inv = concat(product_inv, merged_rep);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    lemma_same_a_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_a_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));
    //  a_rcoset_rep(full_inv) =~= a_rcoset_rep(embed_a(h)·c₁) =~= c₁ ≠ ε

    //  Idempotency: a_rcoset_rep(merged_rep) =~= merged_rep
    lemma_a_rcoset_rep_idempotent(data, full_product);

    //  syls = [Syl(left, c₁)] + syls.drop_first()
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + syls.drop_first()) by {
        assert(syls.len() == 1 + syls.drop_first().len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + syls.drop_first())[k]
        by { if k == 0 {} else {} }
    }

    //  Case split: both branches give (h, syls)
    let rep_inv = a_rcoset_rep(data, product_inv);
    if rep_inv =~= e {
        //  rep_inv = ε: merged_rep =~= c₁ + product_inv ≡ embed_a(h)
        lemma_c2_rep_zero_branch(data, s, h, c1, combined_h, merged_rep);
        //  → subgroup restore gives h-part = h, and new_syls =~= syls
        lemma_subgroup_rcoset_restore(data, product_inv, h);
        return;
    }

    //  rep_inv ≠ ε: merge → (h, [Syl(left, c₁)] + rest) = (h, syls)
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    lemma_c2_inverse_merge_step(data, s, h, c1, combined_h, merged_rep, syls.drop_first());
}

///  Subcase C1: merge with merged_rep = ε (full product in subgroup).
///  Forward: merge absorbs → (combined_h, syls.drop_first()).
///  Inverse: product_inv ≡ embed_a(h)·c₁, rep_inv = c₁ ≠ ε → PREPEND c₁ → (h, syls).
///  Alternating ensures the inverse step prepends (not merges again).
proof fn lemma_inverse_pair_g1_subcase_c1(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        syls.first().is_left,
        //  Sub-subcase: merged_rep = ε (absorbed)
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
            let full_product = concat(product, syls.first().rep);
            a_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = a_rcoset_h(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
    assert(word_valid(c1, n1));
    assert(!(c1 =~= e));
    crate::word::lemma_concat_word_valid(product, c1, n1);

    //  Split and compose
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);

    //  Forward: merge absorbed → state = (combined_h, syls.drop_first())
    lemma_act_left_sym_merge_absorbed(data, s, h, syls);
    let rest = syls.drop_first();
    lemma_act_word_single(data, inv_s, combined_h, rest);

    //  [inv(s)]·embed_a(combined_h)·ε ≡ embed_a(h)·c₁
    lemma_inv_s_rcoset_merge_equiv(data, s, h, c1);

    //  product_inv ≡ embed_a(h)·c₁ (since merged_rep = ε: concat(product_inv, ε) =~= product_inv)
    let embed_ch = apply_embedding(a_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    let product_inv = concat(inv_s_word, embed_ch);

    //  Decompose embed_a(h)·c₁: rep = c₁, h-part = h
    assert(a_rcoset_rep(data, c1) =~= c1);
    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  rep_inv =~= c₁ ≠ ε (from equiv invariance)
    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    lemma_same_a_rcoset_from_equiv(data, product_inv, concat(embed_h, c1));
    lemma_a_rcoset_rep_invariant(data, product_inv, concat(embed_h, c1));
    //  a_rcoset_rep(product_inv) =~= c₁ ≠ ε

    //  h-part: a_rcoset_h(product_inv) =~= h
    lemma_a_rcoset_h_from_equiv(data, product_inv, h, c1);

    //  generator_index for dispatch
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    //  Alternating: syls[0] is left → syls[1] (if exists) is right → rest starts with right or is empty
    //  So the inverse step PREPENDS (not merges)
    assert(rest.len() == 0 || !rest.first().is_left) by {
        if rest.len() > 0 {
            //  syls[0].is_left and alternating → syls[1].is_left != syls[0].is_left → !syls[1].is_left
            assert(syls[0].is_left);
            assert(syls[0].is_left != syls[1].is_left);
            assert(rest.first() == syls[1]);
        }
    }

    //  Inverse step: PREPEND c₁ → (h, [Syl(left, c₁)] + rest) = (h, syls)
    //  syls = [Syl(left, c₁)] + rest
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + rest) by {
        assert(syls.len() == 1 + rest.len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + rest)[k]
        by { if k == 0 {} else {} }
    }
}

///  Complete G₁ inverse pair triviality: [s, inv(s)] acts trivially on ALL canonical states.
///  Dispatches to subcases A, B, C1, C2 based on the action's branch conditions.
pub proof fn lemma_inverse_pair_g1(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep = a_rcoset_rep(data, product);

    if rep =~= empty_word() {
        //  Subcase A: product in subgroup
        lemma_inverse_pair_g1_subcase_a(data, s, h, syls);
    } else if syls.len() == 0 || !syls.first().is_left {
        //  Subcase B: prepend new syllable
        lemma_inverse_pair_g1_subcase_b(data, s, h, syls);
    } else {
        //  Subcases C: merge with existing left syllable
        let full_product = concat(product, syls.first().rep);
        let merged_rep = a_rcoset_rep(data, full_product);
        if merged_rep =~= empty_word() {
            //  C1: merge absorbed
            lemma_inverse_pair_g1_subcase_c1(data, s, h, syls);
        } else {
            //  C2: merge replaced
            lemma_inverse_pair_g1_subcase_c2(data, s, h, syls);
        }
    }
}

//  ============================================================
//  Part P: Right B-coset infrastructure (mirrors Part N for A-cosets)
//  ============================================================

///  Scan for min right-B-coset length.
proof fn lemma_scan_b_rcoset_len(
    data: AmalgamatedData, g: Word, current: nat, bound: nat,
)
    requires
        has_b_rcoset_word_of_len(data, g, bound),
        current <= bound,
        no_shorter_b_rcoset_word(data, g, current),
    ensures
        exists|l: nat| current <= l && l <= bound
            && #[trigger] is_min_b_rcoset_len(data, g, l),
    decreases bound - current,
{
    if has_b_rcoset_word_of_len(data, g, current) {
        assert(is_min_b_rcoset_len(data, g, current));
    } else { lemma_scan_b_rcoset_len(data, g, current + 1, bound); }
}

///  Scan for min right-B-coset lex rank.
proof fn lemma_scan_b_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_b_rcoset_word_of_len_rank(data, g, l, bound),
        current <= bound,
        no_smaller_b_rcoset_lex(data, g, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_b_rcoset_lex(data, g, l, r),
    decreases bound - current,
{
    if has_b_rcoset_word_of_len_rank(data, g, l, current) {
        assert(is_min_b_rcoset_lex(data, g, l, current));
    } else { lemma_scan_b_rcoset_lex(data, g, l, current + 1, bound); }
}

///  Right-B-coset rep satisfiability.
proof fn lemma_b_rcoset_rep_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
    ensures
        is_min_b_rcoset_len(data, g, b_rcoset_min_len(data, g)),
        is_min_b_rcoset_lex(data, g, b_rcoset_min_len(data, g), b_rcoset_min_lex(data, g)),
{
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g, data.p2.num_generators);
    crate::word::lemma_concat_word_valid(g, inverse_word(g), data.p2.num_generators);
    crate::presentation_lemmas::lemma_word_inverse_right(data.p2, g);
    crate::benign::lemma_identity_in_generated_subgroup(data.p2, b_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p2, concat(g, inverse_word(g)), empty_word());
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        empty_word(), concat(g, inverse_word(g)));
    assert(has_b_rcoset_word_of_len(data, g, g.len() as nat));
    assert(no_shorter_b_rcoset_word(data, g, 0nat));
    lemma_scan_b_rcoset_len(data, g, 0, g.len() as nat);
    let l = b_rcoset_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, data.p2.num_generators)
        && same_b_rcoset(data, g, w) && w.len() == l;
    let wr = word_lex_rank_base(w, 2 * data.p2.num_generators + 1);
    assert(has_b_rcoset_word_of_len_rank(data, g, l, wr));
    assert(no_smaller_b_rcoset_lex(data, g, l, 0nat));
    lemma_scan_b_rcoset_lex(data, g, l, 0, wr);
}

///  Extract right-B-coset rep properties.
pub proof fn lemma_b_rcoset_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
    ensures
        same_b_rcoset(data, g, b_rcoset_rep(data, g)),
        word_valid(b_rcoset_rep(data, g), data.p2.num_generators),
        b_rcoset_rep(data, g).len() == b_rcoset_min_len(data, g),
        word_lex_rank_base(b_rcoset_rep(data, g), 2 * data.p2.num_generators + 1) == b_rcoset_min_lex(data, g),
{
    lemma_b_rcoset_rep_satisfiable(data, g);
}

///  No shorter → ≥ for right B-cosets.
proof fn lemma_no_shorter_b_rcoset_word_implies_ge(
    data: AmalgamatedData, g: Word, m: nat, k: nat,
)
    requires
        no_shorter_b_rcoset_word(data, g, m),
        has_b_rcoset_word_of_len(data, g, k),
    ensures k >= m,
    decreases m,
{
    if m == 0 {} else if k == m - 1 {} else if k < m - 1 {
        lemma_no_shorter_b_rcoset_word_implies_ge(data, g, (m - 1) as nat, k);
    }
}

proof fn lemma_no_shorter_b_rcoset_word_forces_zero(
    data: AmalgamatedData, g: Word, l: nat,
)
    requires
        no_shorter_b_rcoset_word(data, g, l),
        has_b_rcoset_word_of_len(data, g, 0nat),
    ensures l == 0,
    decreases l,
{
    if l > 0 { lemma_no_shorter_b_rcoset_word_forces_zero(data, g, (l - 1) as nat); }
}

///  No smaller B-coset lex implies ≥.
proof fn lemma_no_smaller_b_rcoset_lex_implies_ge(
    data: AmalgamatedData, g: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_b_rcoset_lex(data, g, l, m),
        has_b_rcoset_word_of_len_rank(data, g, l, k),
    ensures k >= m,
    decreases m,
{
    if m == 0 {} else if k == m - 1 {} else if k < m - 1 {
        lemma_no_smaller_b_rcoset_lex_implies_ge(data, g, l, (m - 1) as nat, k);
    }
}

///  If g is in the B-subgroup, then b_rcoset_rep(g) =~= ε.
pub proof fn lemma_b_rcoset_in_subgroup(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        in_right_subgroup(data, g),
    ensures
        b_rcoset_rep(data, g) =~= empty_word(),
{
    let e = empty_word();
    let n2 = data.p2.num_generators;
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(concat(g, inverse_word(e)) =~= g) by {
        assert(concat(g, e).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, e)[k] == g[k] by {}
    }
    crate::presentation::lemma_equiv_refl(data.p2, g);
    lemma_in_subgroup_equiv(data.p2, b_words(data), g, concat(g, inverse_word(e)));
    assert(word_valid(e, n2)) by { assert(e.len() == 0); }
    assert(has_b_rcoset_word_of_len(data, g, 0nat));
    assert(no_shorter_b_rcoset_word(data, g, 0nat));
    lemma_scan_b_rcoset_len(data, g, 0, 0);
    let l = b_rcoset_min_len(data, g);
    lemma_no_shorter_b_rcoset_word_forces_zero(data, g, l);
    assert(word_lex_rank_base(e, 2 * n2 + 1) == 0nat);
    assert(has_b_rcoset_word_of_len_rank(data, g, 0nat, 0nat));
    assert(no_smaller_b_rcoset_lex(data, g, 0nat, 0nat));
    lemma_scan_b_rcoset_lex(data, g, 0, 0, 0);
}

///  same_b_rcoset is symmetric.
proof fn lemma_same_b_rcoset_symmetric(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
    ensures
        same_b_rcoset(data, g2, g1),
{
    let n2 = data.p2.num_generators;
    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::word::lemma_inverse_word_valid(g2, n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n2);
    lemma_subgroup_inverse(data.p2, b_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by { if k < g2.len() as int {} else {} }
    }
    crate::word::lemma_inverse_word_valid(g1, n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n2);
    crate::presentation::lemma_equiv_refl(data.p2, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        inv_pair, concat(g2, inverse_word(g1)));
}

///  If g1 ≡ g2 in G₂, then same_b_rcoset(g1, g2).
pub proof fn lemma_same_b_rcoset_from_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
    ensures
        same_b_rcoset(data, g1, g2),
{
    let p2 = data.p2;
    let n2 = p2.num_generators;
    crate::word::lemma_inverse_word_valid(g1, n2);
    crate::word::lemma_inverse_word_valid(g2, n2);
    crate::presentation::lemma_equiv_symmetric(p2, g1, g2);
    lemma_equiv_inverse(p2, g2, g1);
    crate::presentation::lemma_equiv_refl(p2, g1);
    crate::presentation_lemmas::lemma_equiv_concat(p2,
        g1, g1, inverse_word(g2), inverse_word(g1));
    crate::presentation_lemmas::lemma_word_inverse_right(p2, g1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g1), n2);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(g1, inverse_word(g2)),
        concat(g1, inverse_word(g1)),
        empty_word());
    crate::benign::lemma_identity_in_generated_subgroup(p2, b_words(data));
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n2);
    crate::presentation::lemma_equiv_symmetric(p2, concat(g1, inverse_word(g2)), empty_word());
    lemma_in_subgroup_equiv(p2, b_words(data),
        empty_word(), concat(g1, inverse_word(g2)));
}

///  Transfer: same B-rcoset → coset words transfer.
proof fn lemma_b_rcoset_word_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
        has_b_rcoset_word_of_len(data, g1, l),
    ensures
        has_b_rcoset_word_of_len(data, g2, l),
{
    let n2 = data.p2.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n2)
        && same_b_rcoset(data, g1, w) && w.len() == l;
    crate::word::lemma_inverse_word_valid(g1, n2);
    crate::word::lemma_inverse_word_valid(g2, n2);
    crate::word::lemma_inverse_word_valid(w, n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(w), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n2);
    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    lemma_subgroup_inverse(data.p2, b_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by { if k < g2.len() as int {} else {} }
    }
    crate::presentation::lemma_equiv_refl(data.p2, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        inv_pair, concat(g2, inverse_word(g1)));
    lemma_subgroup_concat(data.p2, b_words(data),
        concat(g2, inverse_word(g1)), concat(g1, inverse_word(w)));
    lemma_four_part_cancel(data.p2, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
}

///  Transfer with rank for B-rcosets.
proof fn lemma_b_rcoset_word_rank_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat, r: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
        has_b_rcoset_word_of_len_rank(data, g1, l, r),
    ensures
        has_b_rcoset_word_of_len_rank(data, g2, l, r),
{
    let n2 = data.p2.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n2) && same_b_rcoset(data, g1, w) && w.len() == l
        && word_lex_rank_base(w, 2 * n2 + 1) == r;
    lemma_same_b_rcoset_symmetric(data, g1, g2);
    lemma_subgroup_concat(data.p2, b_words(data),
        concat(g2, inverse_word(g1)),
        concat(g1, inverse_word(w)));
    crate::word::lemma_inverse_word_valid(w, n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n2);
    lemma_four_part_cancel(data.p2, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
}

///  B-rcoset rep invariance: same_b_rcoset → same b_rcoset_rep.
pub proof fn lemma_b_rcoset_rep_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
    ensures
        b_rcoset_rep(data, g1) =~= b_rcoset_rep(data, g2),
{
    let n2 = data.p2.num_generators;
    lemma_b_rcoset_rep_satisfiable(data, g1);
    lemma_b_rcoset_rep_satisfiable(data, g2);
    let l1 = b_rcoset_min_len(data, g1);
    let l2 = b_rcoset_min_len(data, g2);
    lemma_b_rcoset_word_transfer(data, g1, g2, l1);
    lemma_same_b_rcoset_symmetric(data, g1, g2);
    lemma_b_rcoset_word_transfer(data, g2, g1, l2);
    lemma_no_shorter_b_rcoset_word_implies_ge(data, g2, l2, l1);
    lemma_no_shorter_b_rcoset_word_implies_ge(data, g1, l1, l2);
    let l = l1;
    //  Lex rank transfer (same pattern as A-coset)
    let w1: Word = choose|w: Word| word_valid(w, n2) && same_b_rcoset(data, g1, w) && w.len() == l;
    let wr1 = word_lex_rank_base(w1, 2 * n2 + 1);
    assert(has_b_rcoset_word_of_len_rank(data, g1, l, wr1));
    assert(no_smaller_b_rcoset_lex(data, g1, l, 0nat));
    lemma_scan_b_rcoset_lex(data, g1, l, 0, wr1);
    let w2: Word = choose|w: Word| word_valid(w, n2) && same_b_rcoset(data, g2, w) && w.len() == l;
    let wr2 = word_lex_rank_base(w2, 2 * n2 + 1);
    assert(has_b_rcoset_word_of_len_rank(data, g2, l, wr2));
    assert(no_smaller_b_rcoset_lex(data, g2, l, 0nat));
    lemma_scan_b_rcoset_lex(data, g2, l, 0, wr2);
    let r1 = b_rcoset_min_lex(data, g1);
    let r2 = b_rcoset_min_lex(data, g2);
    //  Transfer rank witnesses via explicit helper
    lemma_b_rcoset_word_rank_transfer(data, g1, g2, l, r1);
    lemma_b_rcoset_word_rank_transfer(data, g2, g1, l, r2);
    lemma_no_smaller_b_rcoset_lex_implies_ge(data, g2, l, r2, r1);
    lemma_no_smaller_b_rcoset_lex_implies_ge(data, g1, l, r1, r2);
    //  Lex rank injectivity
    lemma_b_rcoset_rep_props(data, g1);
    lemma_b_rcoset_rep_props(data, g2);
    let rep1 = b_rcoset_rep(data, g1);
    let rep2 = b_rcoset_rep(data, g2);
    let base = 2 * n2 + 1;
    assert forall|k: int| 0 <= k < rep1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep1[k]) < base
    by { assert(symbol_valid(rep1[k], n2)); match rep1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rep2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep2[k]) < base
    by { assert(symbol_valid(rep2[k], n2)); match rep2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0);
    lemma_word_lex_rank_base_injective(rep1, rep2, base);
}

///  Idempotency of b_rcoset_rep.
pub proof fn lemma_b_rcoset_rep_idempotent(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
    ensures
        b_rcoset_rep(data, b_rcoset_rep(data, g)) =~= b_rcoset_rep(data, g),
{
    let rep = b_rcoset_rep(data, g);
    lemma_b_rcoset_rep_props(data, g);
    lemma_same_b_rcoset_symmetric(data, g, rep);
    lemma_b_rcoset_rep_invariant(data, rep, g);
}

//  ============================================================
//  Part Q: G₂ inverse pair helpers (mirrors Part M/O for G₁)
//  ============================================================

///  embed_b(h) is in the B-generated subgroup (mirrors lemma_apply_embedding_in_subgroup).
pub proof fn lemma_apply_embedding_in_subgroup_g2(
    p: Presentation, gens: Seq<Word>, h: Word,
)
    requires
        presentation_valid(p),
        word_valid(h, gens.len()),
        forall|i: int| 0 <= i < gens.len()
            ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, apply_embedding(gens, h)),
    decreases h.len(),
{
    if h.len() == 0 {
        assert(apply_embedding(gens, h) =~= empty_word());
        crate::benign::lemma_identity_in_generated_subgroup(p, gens);
    } else {
        let s = h.first();
        let rest = h.drop_first();
        let head = apply_embedding_symbol(gens, s);
        let tail = apply_embedding(gens, rest);
        lemma_apply_embedding_in_subgroup_g2(p, gens, rest);
        match s {
            Symbol::Gen(i) => {
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
            }
            Symbol::Inv(i) => {
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
                crate::word::lemma_inverse_word_valid(gens[i as int], p.num_generators);
                lemma_subgroup_inverse(p, gens, gens[i as int]);
            }
        }
        lemma_subgroup_concat(p, gens, head, tail);
    }
}

///  Right B-coset decomposition identity: embed_b(h)·rep ≡ g (textbook g = h·c for G₂).
pub proof fn lemma_b_rcoset_decomposition(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures
        equiv_in_presentation(data.p2,
            concat(apply_embedding(b_words(data), b_rcoset_h(data, g)),
                   b_rcoset_rep(data, g)),
            g),
        word_valid(b_rcoset_h(data, g), k_size(data)),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    //  h-part satisfiability: reuse the h-witness pattern
    assert(has_right_h_witness_of_len(data, target, h_witness.len() as nat));
    let pred_h = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);
    //  h-lex satisfiability
    let l = b_rcoset_h_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex_g2(data, target, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target, l, 0, wr);

    let h = b_rcoset_h(data, g);
    let embed_h = apply_embedding(b_words(data), h);
    lemma_b_rcoset_rep_props(data, g);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  embed_b(h)·rep ≡ target·rep = (g·inv(rep))·rep ≡ g
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, embed_h, target, rep);
    crate::word::lemma_inverse_word_valid(rep, n2);
    assert(concat(concat(g, inverse_word(rep)), rep) =~=
           concat(g, concat(inverse_word(rep), rep))) by {
        let lhs = concat(concat(g, inverse_word(rep)), rep);
        let rhs = concat(g, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < g.len() as int {} else {
                let j = k - g.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p2, rep);
    crate::word::lemma_concat_word_valid(g, concat(inverse_word(rep), rep), n2);
    crate::presentation::lemma_equiv_refl(p2, concat(g, concat(inverse_word(rep), rep)));
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, g,
        concat(inverse_word(rep), rep), empty_word());
    assert(concat(g, empty_word()) =~= g) by {
        assert(concat(g, empty_word()).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, empty_word())[k] == g[k] by {}
    }
    crate::presentation::lemma_equiv_transitive(p2,
        concat(embed_h, rep),
        concat(g, concat(inverse_word(rep), rep)),
        g);
}

///  Free reduction for G₂: [inv(s)]·[s]·w ≡ w in G₂.
proof fn lemma_inv_s_s_cancel_g2(
    data: AmalgamatedData, s: Symbol, w: Word,
)
    requires
        presentation_valid(data.p2),
        word_valid(w, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
    ensures
        equiv_in_presentation(data.p2,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                   concat(Seq::new(1, |_i: int| s), w)),
            w),
{
    lemma_inv_s_s_cancel(data.p2, s, w);
}

///  G₂ general helper: [inv(s)]·embed_b(b_rcoset_h(product))·b_rcoset_rep(product) ≡ embed_b(h)
///  where product = [s]·embed_b(h). Works for all subcases.
proof fn lemma_inv_s_rcoset_product_equiv_g2(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p2.num_generators,
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let h_prime = b_rcoset_h(data, product);
        let embed_h_prime = apply_embedding(b_words(data), h_prime);
        let rep_prime = b_rcoset_rep(data, product);
        let full = concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)), embed_h_prime), rep_prime);
        &&& equiv_in_presentation(data.p2, full, embed_h)
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(s_word, embed_h);
    let rep_prime = b_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);

    //  h-witness from subgroup structure
    lemma_b_rcoset_rep_props(data, product);
    crate::word::lemma_inverse_word_valid(rep_prime, n2);
    crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(product, inverse_word(rep_prime)));
    let hw_r: Word = choose|hw: Word| word_valid(hw, b_words(data).len())
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(product, inverse_word(rep_prime)));
    assert(b_words(data).len() == k_size(data));

    //  embed_b(h')·rep' ≡ product
    lemma_b_rcoset_decomposition(data, product, hw_r);
    let h_prime = b_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    let embed_h_prime = apply_embedding(b_words(data), h_prime);

    //  [inv(s)]·(embed_b(h')·rep') ≡ [inv(s)]·product
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p2, inv_s_word, concat(embed_h_prime, rep_prime), product);

    //  Associativity
    let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
    assert(full =~= concat(inv_s_word, concat(embed_h_prime, rep_prime))) by {
        let lhs = full;
        let rhs = concat(inv_s_word, concat(embed_h_prime, rep_prime));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_h_prime.len() as int {} else {}
            }
        }
    }

    //  [inv(s)]·[s]·embed_h ≡ embed_h
    crate::word::lemma_concat_word_valid(embed_h_prime, rep_prime, n2);
    lemma_inv_s_s_cancel(p2, s, embed_h);
    assert(concat(inv_s_word, product) =~= concat(inv_s_word, concat(s_word, embed_h)));

    crate::presentation::lemma_equiv_transitive(p2,
        concat(inv_s_word, concat(embed_h_prime, rep_prime)),
        concat(inv_s_word, concat(s_word, embed_h)),
        embed_h);
    return;
}

///  G₂ merge equiv: [inv(s)]·embed_b(combined_h)·merged_rep ≡ embed_b(h)·c₁
proof fn lemma_inv_s_rcoset_merge_equiv_g2(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let embed_ch = apply_embedding(b_words(data), combined_h);
        let merged_rep = b_rcoset_rep(data, full_product);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full = concat(concat(inv_s_word, embed_ch), merged_rep);
        &&& equiv_in_presentation(data.p2, full, concat(embed_h, c1))
        &&& word_valid(combined_h, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(s_word, embed_h);
    let full_product = concat(product, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);
    crate::word::lemma_concat_word_valid(product, c1, n2);

    //  Rcoset decomposition of full_product
    lemma_b_rcoset_rep_props(data, full_product);
    let merged_rep = b_rcoset_rep(data, full_product);
    crate::word::lemma_inverse_word_valid(merged_rep, n2);
    crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(full_product, inverse_word(merged_rep)));
    let hw: Word = choose|hw: Word| word_valid(hw, b_words(data).len())
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(full_product, inverse_word(merged_rep)));
    assert(b_words(data).len() == k_size(data));
    lemma_b_rcoset_decomposition(data, full_product, hw);
    let combined_h = b_rcoset_h(data, full_product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    let embed_ch = apply_embedding(b_words(data), combined_h);

    //  [inv(s)]·(embed_b(ch)·mr) ≡ [inv(s)]·full_product ≡ embed_h·c1
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p2, inv_s_word, concat(embed_ch, merged_rep), full_product);
    assert(concat(inv_s_word, concat(concat(s_word, embed_h), c1)) =~=
           concat(inv_s_word, concat(s_word, concat(embed_h, c1)))) by {
        let lhs = concat(inv_s_word, concat(concat(s_word, embed_h), c1));
        let rhs = concat(inv_s_word, concat(s_word, concat(embed_h, c1)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { let j = k - 1; if j < s_word.len() as int {} else {
                let j2 = j - s_word.len() as int;
                if j2 < embed_h.len() as int {} else {}
            }}
        }
    }
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);
    lemma_inv_s_s_cancel(p2, s, concat(embed_h, c1));
    let full = concat(concat(inv_s_word, embed_ch), merged_rep);
    assert(full =~= concat(inv_s_word, concat(embed_ch, merged_rep))) by {
        let lhs = full; let rhs = concat(inv_s_word, concat(embed_ch, merged_rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_ch.len() as int {} else {}
            }
        }
    }
    crate::presentation::lemma_equiv_transitive(p2,
        concat(inv_s_word, concat(embed_ch, merged_rep)),
        concat(inv_s_word, concat(s_word, concat(embed_h, c1))),
        concat(embed_h, c1));
}

///  Z3 helper: act_right_sym merge absorbed.
proof fn lemma_act_right_sym_merge_absorbed(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        !syllables.first().is_left,
        b_rcoset_rep(data,
            concat(concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)),
                   syllables.first().rep))
            =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        act_right_sym(data, s, h, syllables)
            == (b_rcoset_h(data, full_product), syllables.drop_first())
    }),
{
}

///  Z3 helper: act_right_sym merge replaced.
proof fn lemma_act_right_sym_merge_replaced(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        !syllables.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syllables.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        let merged_rep = b_rcoset_rep(data, full_product);
        act_right_sym(data, s, h, syllables)
            == (b_rcoset_h(data, full_product),
                Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syllables.drop_first())
    }),
{
}

///  G₂ h-witness transfer between equivalent targets.
proof fn lemma_h_witness_transfer_g2(
    data: AmalgamatedData, target1: Word, target2: Word, l: nat,
)
    requires
        has_right_h_witness_of_len(data, target1, l),
        equiv_in_presentation(data.p2, target1, target2),
        presentation_valid(data.p2),
    ensures
        has_right_h_witness_of_len(data, target2, l),
{
    let h: Word = choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), h), target1);
    crate::presentation::lemma_equiv_transitive(
        data.p2, apply_embedding(b_words(data), h), target1, target2);
}

///  No smaller G₂ h-lex implies ≥.
proof fn lemma_no_smaller_h_lex_g2_implies_ge(
    data: AmalgamatedData, target: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_h_lex_g2(data, target, l, m),
        has_right_h_witness_of_len_rank(data, target, l, k),
    ensures k >= m,
    decreases m,
{
    if m == 0 {} else if k == m - 1 {} else if k < m - 1 {
        lemma_no_smaller_h_lex_g2_implies_ge(data, target, l, (m - 1) as nat, k);
    }
}

///  G₂ h-min-len equality: targets ≡ → same min h-len.
proof fn lemma_b_rcoset_h_min_len_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        b_rcoset_rep(data, g1) =~= empty_word(),
        b_rcoset_rep(data, g2) =~= empty_word(),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h_min_len(data, g1) == b_rcoset_h_min_len(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let target1 = concat(g1, inverse_word(b_rcoset_rep(data, g1)));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));

    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    assert(pred1(h_witness1.len() as nat));
    assert(pred2(h_witness2.len() as nat));
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    let l1 = b_rcoset_h_min_len(data, g1);
    let l2 = b_rcoset_h_min_len(data, g2);

    lemma_h_witness_transfer_g2(data, target1, target2, l1);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g1), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(b_rcoset_rep(data, g1)), n2);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    lemma_h_witness_transfer_g2(data, target2, target1, l2);

    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  G₂ h-part equiv invariance: if g1 ≡ g2 in G₂ and both in B-subgroup,
///  then b_rcoset_h gives same result.
proof fn lemma_b_rcoset_h_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        //  Both in B-subgroup (reps = ε)
        b_rcoset_rep(data, g1) =~= empty_word(),
        b_rcoset_rep(data, g2) =~= empty_word(),
        //  H-witnesses for satisfiability
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h(data, g1) =~= b_rcoset_h(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let target1 = concat(g1, inverse_word(b_rcoset_rep(data, g1)));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));

    //  Min-len equality from helper
    lemma_b_rcoset_h_min_len_equiv(data, g1, g2, h_witness1, h_witness2);
    let l = b_rcoset_h_min_len(data, g1);

    //  Lex: h-lex satisfiability + transfer
    //  Need h-witness satisfiability for min_len
    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    assert(pred1(h_witness1.len() as nat));
    assert(pred2(h_witness2.len() as nat));
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);
    //  Now has_right_h_witness_of_len(target1, l) and (target2, l) hold (from choose satisfiability)
    //  Extract witnesses at min length
    let w1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target1);
    let wr1 = word_lex_rank_base(w1, h_lex_base(data));
    //  has_right_h_witness_of_len_rank: exists witness with len l and rank wr1
    assert(has_right_h_witness_of_len_rank(data, target1, l, wr1));
    assert(no_smaller_h_lex_g2(data, target1, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target1, l, 0, wr1);

    let w2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target2);
    let wr2 = word_lex_rank_base(w2, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target2, l, wr2));
    assert(no_smaller_h_lex_g2(data, target2, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target2, l, 0, wr2);

    let r1 = b_rcoset_h_min_lex(data, g1);
    let r2 = b_rcoset_h_min_lex(data, g2);
    //  Transfer rank witnesses (explicit — Z3 can't see existential transfer automatically)
    //  w1 has equiv(embed_b(w1), target1) ≡ target2, so w1 witnesses for target2 too
    let rep1_word = b_rcoset_h(data, g1);
    let rep2_word = b_rcoset_h(data, g2);
    //  For r1: the rep1_word satisfies the predicate for target1. By equiv: also for target2.
    //  For r2: symmetric.
    //  Use: h_witness_transfer_g2 at the rank level
    //  Actually: the existential witnesses have the right lex rank. The equiv of targets transfers them.
    //  The key: if embed_b(w) ≡ target1 and target1 ≡ target2, then embed_b(w) ≡ target2 (transitivity).
    //  So the SAME K-word w witnesses for target2 with the same len and lex rank.
    //  Z3 should see this via the transitivity in the existential.
    //  Let's try extracting the witness explicitly:
    let rw1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && word_lex_rank_base(w, h_lex_base(data)) == r1
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target1);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw1), target1, target2);
    let rw2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && word_lex_rank_base(w, h_lex_base(data)) == r2
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target2);
    //  target2 ≡ target1 (symmetric of target1 ≡ target2)
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g1), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(b_rcoset_rep(data, g1)), n2);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw2), target2, target1);

    //  Bidirectional ≥ on lex
    lemma_no_smaller_h_lex_g2_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target1, l, r1, r2);
    //  r1 == r2

    //  Lex rank injectivity → same word
    let h1 = b_rcoset_h(data, g1);
    let h2 = b_rcoset_h(data, g2);
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < h1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h1[k]) < base
    by { assert(symbol_valid(h1[k], k_size(data))); match h1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < h2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h2[k]) < base
    by { assert(symbol_valid(h2[k], k_size(data))); match h2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(h1, h2, base);
}

///  G₂ h-witness exists for any G₂-word.
pub proof fn lemma_h_witness_exists_g2(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
    ensures
        exists|h: Word| word_valid(h, k_size(data))
            && equiv_in_presentation(data.p2,
                apply_embedding(b_words(data), h),
                concat(g, inverse_word(b_rcoset_rep(data, g)))),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    reveal(presentation_valid);

    lemma_b_rcoset_rep_props(data, g);
    crate::word::lemma_inverse_word_valid(g, n2);
    crate::word::lemma_inverse_word_valid(rep, n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(rep), n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(g), n2);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    //  same_b_rcoset(g, rep) → g·inv(rep) ∈ B → subgroup_to_k_word → witness
    lemma_subgroup_to_k_word(p2, b_words(data), target);
    assert(b_words(data).len() == k_size(data));
}

///  G₂ h-part from equiv: if g ≡ embed_b(h)·c and both canonical, then b_rcoset_h(g) =~= h.
proof fn lemma_b_rcoset_h_from_equiv(
    data: AmalgamatedData, g: Word, h: Word, c: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(h, k_size(data)),
        word_valid(c, data.p2.num_generators),
        equiv_in_presentation(data.p2, g, concat(apply_embedding(b_words(data), h), c)),
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h, //  h B-canonical
        b_rcoset_rep(data, c) =~= c,
        b_rcoset_rep(data, g) =~= c,
    ensures
        b_rcoset_h(data, g) =~= h,
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_inverse_word_valid(c, n2);

    //  target_g = g·inv(c) ≡ (embed_h·c)·inv(c) ≡ embed_h (by right_cancel + concat_left)
    crate::word::lemma_concat_word_valid(g, inverse_word(c), n2);
    crate::word::lemma_concat_word_valid(embed_h, c, n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, g, concat(embed_h, c), inverse_word(c));
    lemma_right_cancel(p2, embed_h, c);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(g, inverse_word(c)), concat(concat(embed_h, c), inverse_word(c)), embed_h);

    //  Both g·inv(c) and embed_h are ≡ embed_h, both ∈ B-subgroup
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p2, concat(g, inverse_word(c)), embed_h);
    lemma_in_subgroup_equiv(p2, b_words(data), embed_h, concat(g, inverse_word(c)));
    lemma_b_rcoset_in_subgroup(data, concat(g, inverse_word(c)));
    lemma_b_rcoset_in_subgroup(data, embed_h);

    //  h-part invariance: both targets ≡ embed_h, both reps = ε
    //  b_rcoset_h_min_len, b_rcoset_h_min_lex are the same for both (bidirectional transfer)
    //  lex rank injectivity → same word
    lemma_h_witness_exists_g2(data, concat(g, inverse_word(c)));
    lemma_h_witness_exists_g2(data, embed_h);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(concat(g, inverse_word(c)),
                   inverse_word(b_rcoset_rep(data, concat(g, inverse_word(c))))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(embed_h, inverse_word(b_rcoset_rep(data, embed_h))));
    lemma_b_rcoset_h_equiv_invariant(data, concat(g, inverse_word(c)), embed_h, hw1, hw2);
}

///  G₂ subgroup restore: if product2 ≡ embed_b(h) and h canonical, then reps = ε, h-part = h.
proof fn lemma_subgroup_rcoset_restore_g2(
    data: AmalgamatedData, product2: Word, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(product2, data.p2.num_generators),
        equiv_in_presentation(data.p2, product2, apply_embedding(b_words(data), h)),
        is_canonical_state(data, h, Seq::<Syllable>::empty()),
    ensures
        b_rcoset_rep(data, product2) =~= empty_word(),
        b_rcoset_h(data, product2) =~= h,
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h_b = apply_embedding(b_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  product2 ∈ B-subgroup
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p2, product2, embed_h_b);
    lemma_in_subgroup_equiv(p2, b_words(data), embed_h_b, product2);
    lemma_b_rcoset_in_subgroup(data, product2);
    lemma_b_rcoset_in_subgroup(data, embed_h_b);

    //  H-part invariance: both targets ≡ embed_b(h) → same canonical K-word
    lemma_h_witness_exists_g2(data, product2);
    lemma_h_witness_exists_g2(data, embed_h_b);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(product2, inverse_word(b_rcoset_rep(data, product2))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(embed_h_b, inverse_word(b_rcoset_rep(data, embed_h_b))));
    lemma_b_rcoset_h_equiv_invariant(data, product2, embed_h_b, hw1, hw2);
    //  b_rcoset_h(product2) =~= b_rcoset_h(embed_h_b)
    //  b_rcoset_h(embed_h_b) =~= h (by is_canonical_state + the fact that both conventions agree on subgroup elements)
    //  TODO: need to connect b_rcoset_h(embed_h_b) to h through the canonicality condition
}

///  G₂ decompose: embed_b(h)·c₁ → (h, c₁) when both canonical.
proof fn lemma_b_rcoset_decompose_subgroup_times_rep(
    data: AmalgamatedData, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h, //  h A-canonical
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h, //  h B-canonical
        b_rcoset_rep(data, c1) =~= c1, //  c₁ canonical
    ensures
        b_rcoset_rep(data, concat(apply_embedding(b_words(data), h), c1)) =~= c1,
        b_rcoset_h(data, concat(apply_embedding(b_words(data), h), c1)) =~= h,
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(embed_h, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);

    //  same_b_rcoset(product, c1): product·inv(c1) = embed_h·c1·inv(c1) ≡ embed_h ∈ B
    crate::word::lemma_inverse_word_valid(c1, n2);
    lemma_right_cancel(p2, embed_h, c1);
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    crate::word::lemma_concat_word_valid(product, inverse_word(c1), n2);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(concat(embed_h, c1), inverse_word(c1)), embed_h);
    lemma_in_subgroup_equiv(p2, b_words(data), embed_h,
        concat(product, inverse_word(c1)));

    //  Rep invariance: b_rcoset_rep(product) =~= b_rcoset_rep(c1) =~= c1
    lemma_b_rcoset_rep_invariant(data, product, c1);

    //  H-part: use lemma_b_rcoset_h_from_equiv
    //  product ≡ embed_h·c1, b_rcoset_rep(product) =~= c1, h B-canonical
    crate::presentation::lemma_equiv_refl(p2, product);
    lemma_b_rcoset_h_from_equiv(data, product, h, c1);
}

//  ============================================================
//  Part R: G₂ inverse pair subcases + dispatch
//  ============================================================

///  G₂ subcase A helper: establish product2 ≡ embed_b(h) and word_valid.
proof fn lemma_g2_subcase_a_setup(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p2.num_generators,
        b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let product2 = concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), h_prime));
        &&& equiv_in_presentation(data.p2, product2, apply_embedding(b_words(data), h))
        &&& word_valid(product2, data.p2.num_generators)
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);
    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    lemma_inv_s_rcoset_product_equiv_g2(data, s, h);
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let h_prime = b_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(word_valid(inv_s_word, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(inv_s_word, apply_embedding(b_words(data), h_prime), n2);
}

///  G₂ subcase A: rep = ε.
proof fn lemma_inverse_pair_g2_subcase_a(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word(),
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    reveal(presentation_valid);

    //  Composition + single-step
    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let h_prime = b_rcoset_h(data, product);
    lemma_act_word_single(data, inverse_symbol(s_shifted), h_prime, syls);

    //  Setup + restore (from helpers)
    lemma_g2_subcase_a_setup(data, s, h);
    lemma_subgroup_rcoset_restore_g2(data,
        concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), h_prime)), h);
}

///  G₂ version: if rep' = b_rcoset_rep(product) ≠ ε, then the inverse product is NOT in B.
///  Mirrors lemma_inv_step_rep_nonzero with b_words/p2/b_rcoset.
///  Proof by contradiction: if product_inv ∈ B, then rep' ∈ B (by left cancellation),
///  hence product ∈ B, contradicting rep' ≠ ε.
proof fn lemma_inv_step_rep_nonzero_g2(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let product_inv = concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), h_prime));
        !(b_rcoset_rep(data, product_inv) =~= empty_word())
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = b_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    //  Get h_prime and product_inv
    lemma_inv_s_rcoset_product_equiv_g2(data, s, h);
    let h_prime = b_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    let embed_h_prime = apply_embedding(b_words(data), h_prime);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let product_inv = concat(inv_s_word, embed_h_prime);

    //  Proof by contradiction: assume b_rcoset_rep(product_inv) =~= ε
    if b_rcoset_rep(data, product_inv) =~= empty_word() {
        //  product_inv ∈ B
        assert(word_valid(inv_s_word, n2)) by {
            assert forall|k: int| 0 <= k < inv_s_word.len()
                implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n2);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

        lemma_b_rcoset_rep_props(data, product_inv);
        crate::presentation::lemma_equiv_refl(p2, product_inv);
        lemma_in_subgroup_equiv(p2, b_words(data),
            concat(product_inv, inverse_word(b_rcoset_rep(data, product_inv))), product_inv);
        //  product_inv ∈ B

        //  embed_b(h') · rep' ≡ product (from rcoset decomposition)
        lemma_b_rcoset_rep_props(data, product);
        let s_word = Seq::new(1, |_i: int| s);
        assert(word_valid(s_word, n2)) by {
            assert forall|k: int| 0 <= k < s_word.len()
                implies symbol_valid(#[trigger] s_word[k], n2) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(s_word, embed_h, n2);
        crate::word::lemma_inverse_word_valid(rep_prime, n2);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n2);
        lemma_subgroup_to_k_word(p2, b_words(data), concat(product, inverse_word(rep_prime)));
        let hw_r: Word = choose|hw: Word| word_valid(hw, b_words(data).len())
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(product, inverse_word(rep_prime)));
        assert(b_words(data).len() == k_size(data));
        lemma_b_rcoset_decomposition(data, product, hw_r);

        //  [inv(s)] · embed_b(h') · rep' ≡ embed_b(h) (from general helper)
        let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        //  full ≡ embed_b(h) ∈ B → full ∈ B
        lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
        crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n2);
        crate::presentation::lemma_equiv_symmetric(p2, full, embed_h);
        lemma_in_subgroup_equiv(p2, b_words(data), embed_h, full);

        //  full = concat(product_inv, rep_prime). product_inv ∈ B and full ∈ B
        //  → rep_prime ∈ B (by left cancellation)
        lemma_subgroup_left_cancel(p2, b_words(data), product_inv, rep_prime);

        //  rep' ∈ B → product ∈ B:
        lemma_subgroup_concat(p2, b_words(data),
            concat(product, inverse_word(rep_prime)), rep_prime);

        //  concat(concat(product, inv(rep')), rep') ≡ product
        assert(concat(concat(product, inverse_word(rep_prime)), rep_prime) =~=
               concat(product, concat(inverse_word(rep_prime), rep_prime))) by {
            let lhs = concat(concat(product, inverse_word(rep_prime)), rep_prime);
            let rhs = concat(product, concat(inverse_word(rep_prime), rep_prime));
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < product.len() as int {} else {
                    let j = k - product.len() as int;
                    if j < inverse_word(rep_prime).len() as int {} else {}
                }
            }
        }
        crate::presentation_lemmas::lemma_word_inverse_left(p2, rep_prime);
        crate::presentation_lemmas::lemma_equiv_concat_right(
            p2, product, concat(inverse_word(rep_prime), rep_prime), empty_word());
        assert(concat(product, empty_word()) =~= product) by {
            assert(concat(product, empty_word()).len() == product.len());
            assert forall|k: int| 0 <= k < product.len()
                implies concat(product, empty_word())[k] == product[k] by {}
        }
        lemma_in_subgroup_equiv(p2, b_words(data),
            concat(concat(product, inverse_word(rep_prime)), rep_prime), product);
        //  product ∈ B → b_rcoset_rep(product) =~= ε
        lemma_b_rcoset_in_subgroup(data, product);
        //  But rep' = b_rcoset_rep(product) ≠ ε. Contradiction!
    }
}

///  G₂ subcase B merge helper: extracts the heavy equiv + restore chain.
///  Mirrors lemma_inverse_pair_g1_subcase_b_merge with b_words/p2/b_rcoset.
proof fn lemma_inverse_pair_g2_subcase_b_merge(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let rep_prime = b_rcoset_rep(data, product);
        let embed_h_prime = apply_embedding(b_words(data), h_prime);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        &&& b_rcoset_rep(data, full_product2) =~= empty_word()
        &&& b_rcoset_h(data, full_product2) =~= h
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = b_rcoset_rep(data, product);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    let s_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);

    //  General helper: [inv(s)]·embed_b(h')·rep' ≡ embed_b(h) + word_valid(h')
    lemma_inv_s_rcoset_product_equiv_g2(data, s, h);

    let h_prime = b_rcoset_h(data, product);
    let embed_h_prime = apply_embedding(b_words(data), h_prime);
    let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);

    assert(word_valid(inv_s_word, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n2);
    lemma_b_rcoset_rep_props(data, product);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n2);

    //  is_canonical_state(data, h, []) follows from is_canonical_state(data, h, syls)
    assert(is_canonical_state(data, h, Seq::<Syllable>::empty())) by {
        assert(Seq::<Syllable>::empty().len() == 0int);
    }
    lemma_subgroup_rcoset_restore_g2(data, full_product2, h);
}

///  G₂ subcase B complete inverse step: combines merge + rep_nonzero + merge_absorbed
///  into one helper to keep the main function lightweight.
proof fn lemma_g2_b_complete_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() == 0 || syls.first().is_left,
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let rep_prime = b_rcoset_rep(data, product);
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: rep_prime }) + syls;
        act_right_sym(data, inverse_symbol(s), h_prime, new_syls) == (h, syls)
    }),
{
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let rep_prime = b_rcoset_rep(data, product);
    let h_prime = b_rcoset_h(data, product);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: rep_prime }) + syls;

    lemma_inverse_pair_g2_subcase_b_merge(data, s, h, syls);
    lemma_inv_step_rep_nonzero_g2(data, s, h);

    assert(!new_syls.first().is_left);
    assert(new_syls.first().rep == rep_prime);
    assert(new_syls.drop_first() =~= syls);
    assert(generator_index(inverse_symbol(s)) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    lemma_act_right_sym_merge_absorbed(data, inverse_symbol(s), h_prime, new_syls);
}

///  G₂ subcase B: rep ≠ ε, first syllable is left or empty (prepend).
#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g2_subcase_b(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() == 0 || syls.first().is_left,
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let h_prime = b_rcoset_h(data, product);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: b_rcoset_rep(data, product) }) + syls;

    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    lemma_act_word_single(data, inverse_symbol(s_shifted), h_prime, new_syls);
    lemma_g2_b_complete_inverse_step(data, s, h, syls);
}

///  G₂ C1 inverse step helper: establishes that after the merge-absorbed forward step,
///  the inverse product decomposes as (rep = c₁, h-part = h).
///  Extracts the heavy merge_equiv + rep invariance + h-part chain.
proof fn lemma_g2_c1_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
        !(c1 =~= empty_word()),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h,
        b_rcoset_rep(data, c1) =~= c1,
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, c1);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let embed_ch = apply_embedding(b_words(data), combined_h);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let product_inv = concat(inv_s_word, embed_ch);
        &&& b_rcoset_rep(data, product_inv) =~= c1
        &&& b_rcoset_h(data, product_inv) =~= h
        &&& word_valid(combined_h, k_size(data))
        &&& word_valid(product_inv, data.p2.num_generators)
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let full_product = concat(product, c1);
    let combined_h = b_rcoset_h(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    let s_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);
    crate::word::lemma_concat_word_valid(product, c1, n2);

    //  [inv(s)]·embed_b(combined_h)·ε ≡ embed_b(h)·c₁ (since merged_rep = ε)
    lemma_inv_s_rcoset_merge_equiv_g2(data, s, h, c1);

    let embed_ch = apply_embedding(b_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(word_valid(inv_s_word, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    let product_inv = concat(inv_s_word, embed_ch);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);

    //  Rep invariance: product_inv ≡ embed_b(h)·c₁ → same_b_rcoset → rep = c₁
    lemma_same_b_rcoset_from_equiv(data, product_inv, concat(embed_h, c1));
    lemma_b_rcoset_rep_invariant(data, product_inv, concat(embed_h, c1));
    lemma_b_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  H-part: b_rcoset_h(product_inv) =~= h
    lemma_b_rcoset_h_from_equiv(data, product_inv, h, c1);
}

///  G₂ C1 complete inverse step: combines inverse_step + alternating + syls reconstruction.
proof fn lemma_g2_c1_complete_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let c1 = syls.first().rep;
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let rest = syls.drop_first();
        act_right_sym(data, inverse_symbol(s), combined_h, rest) == (h, syls)
    }),
{
    let c1 = syls.first().rep;
    let rest = syls.drop_first();

    //  Inverse step decomposition: rep(product_inv) = c₁, h-part = h
    lemma_g2_c1_inverse_step(data, s, h, c1);

    //  Alternating: syls[0] is right → syls[1] is left → rest starts with left
    assert(rest.len() == 0 || rest.first().is_left) by {
        if rest.len() > 0 {
            assert(!syls[0].is_left);
            assert(syls[0].is_left != syls[1].is_left);
            assert(rest.first() == syls[1]);
        }
    }

    //  syls = [Syl(false, c₁)] + rest
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + rest) by {
        assert(syls.len() == 1 + rest.len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + rest)[k]
        by { if k == 0 {} else {} }
    }
}

///  G₂ subcase C1: merge absorbed (merged_rep = ε).
#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g2_subcase_c1(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    let c1 = syls.first().rep;
    let combined_h = b_rcoset_h(data, concat(concat(Seq::new(1, |_i: int| s),
        apply_embedding(b_words(data), h)), c1));

    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    lemma_act_right_sym_merge_absorbed(data, s, h, syls);
    lemma_act_word_single(data, inverse_symbol(s_shifted), combined_h, syls.drop_first());
    lemma_g2_c1_complete_inverse_step(data, s, h, syls);
    assert(generator_index(inverse_symbol(s_shifted)) >= n1);
}

///  G₂ C2 helper: rep_inv = ε branch → merged_rep =~= c₁ and product_inv ≡ embed_b(h).
///  Mirrors lemma_c2_rep_zero_branch with b_words/p2/b_rcoset.
proof fn lemma_c2_rep_zero_branch_g2(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
    combined_h: Word, merged_rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h,
        b_rcoset_rep(data, c1) =~= c1,
        !(merged_rep =~= empty_word()),
        b_rcoset_rep(data, merged_rep) =~= merged_rep, //  idempotency
        b_rcoset_rep(data, concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), combined_h))) =~= empty_word(),
        equiv_in_presentation(data.p2,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)), merged_rep),
            concat(apply_embedding(b_words(data), h), c1)),
    ensures
        merged_rep =~= c1,
        equiv_in_presentation(data.p2,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)),
            apply_embedding(b_words(data), h)),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(b_words(data), h);
    let embed_ch = apply_embedding(b_words(data), combined_h);
    let product_inv = concat(inv_s_word, embed_ch);
    let full_inv = concat(product_inv, merged_rep);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_inverse_word_valid(merged_rep, n2);
    crate::word::lemma_inverse_word_valid(c1, n2);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n2);
    crate::word::lemma_concat_word_valid(product_inv, merged_rep, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);

    //  Step 1: full_inv·inv(merged_rep) ≡ product_inv ∈ B → same_b_rcoset(full_inv, merged_rep)
    lemma_right_cancel(p2, product_inv, merged_rep);
    lemma_b_rcoset_rep_props(data, product_inv);
    crate::presentation::lemma_equiv_refl(p2, product_inv);
    lemma_in_subgroup_equiv(p2, b_words(data),
        concat(product_inv, inverse_word(b_rcoset_rep(data, product_inv))), product_inv);
    crate::word::lemma_concat_word_valid(full_inv, inverse_word(merged_rep), n2);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(full_inv, inverse_word(merged_rep)), product_inv);
    lemma_in_subgroup_equiv(p2, b_words(data), product_inv,
        concat(full_inv, inverse_word(merged_rep)));

    //  Step 2: b_rcoset_rep(merged_rep) =~= c₁ via invariant chain
    lemma_same_b_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_same_b_rcoset_symmetric(data, full_inv, merged_rep);
    lemma_b_rcoset_rep_invariant(data, merged_rep, full_inv);
    lemma_b_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));
    lemma_b_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  Step 3: product_inv ≡ embed_b(h) via right cancellation
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, full_inv, concat(embed_h, c1), inverse_word(c1));
    lemma_right_cancel(p2, product_inv, c1);
    lemma_right_cancel(p2, embed_h, c1);
    crate::presentation::lemma_equiv_transitive(p2,
        product_inv, concat(concat(product_inv, c1), inverse_word(c1)),
        concat(concat(embed_h, c1), inverse_word(c1)));
    crate::presentation::lemma_equiv_transitive(p2,
        product_inv, concat(concat(embed_h, c1), inverse_word(c1)), embed_h);
}

///  G₂ C2 helper: rep_inv ≠ ε branch → act_right_sym merges to give (h, [Syl(false, c₁)] + rest).
///  Mirrors lemma_c2_inverse_merge_step with b_words/p2/b_rcoset.
proof fn lemma_c2_inverse_merge_step_g2(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word, combined_h: Word,
    merged_rep: Word, rest_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
        !(c1 =~= empty_word()),
        !(merged_rep =~= empty_word()),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h,
        b_rcoset_rep(data, c1) =~= c1,
        equiv_in_presentation(data.p2,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)), merged_rep),
            concat(apply_embedding(b_words(data), h), c1)),
        //  The inverse product is NOT in the subgroup
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)))
            =~= empty_word()),
    ensures ({
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep }) + rest_syls;
        act_right_sym(data, inverse_symbol(s), combined_h, new_syls)
            == (h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + rest_syls)
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(b_words(data), h);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep }) + rest_syls;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    lemma_b_rcoset_decompose_subgroup_times_rep(data, h, c1);
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    let embed_ch = apply_embedding(b_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n2);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_ch), merged_rep, n2);

    //  full_inv ≡ embed_b(h)·c₁ → rcoset rep = c₁ ≠ ε
    let full_inv = concat(concat(inv_s_word, embed_ch), merged_rep);
    lemma_same_b_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_b_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));

    //  Connect merge_replaced preconditions
    assert(!new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    assert(!(b_rcoset_rep(data, full_inv) =~= empty_word()));
    assert(full_inv == concat(concat(Seq::new(1, |_i: int| inv_s),
        apply_embedding(b_words(data), combined_h)), new_syls.first().rep));

    //  H-part: b_rcoset_h(full_inv) =~= h
    lemma_b_rcoset_h_from_equiv(data, full_inv, h, c1);

    //  merge_replaced
    lemma_act_right_sym_merge_replaced(data, inv_s, combined_h, new_syls);
}

///  G₂ C2 complete inverse step: handles merge_equiv + case split + dispatch.
///  Extracts all heavy logic from the main C2 function.
proof fn lemma_g2_c2_complete_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let c1 = syls.first().rep;
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let merged_rep = b_rcoset_rep(data, full_product);
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
            + syls.drop_first();
        act_right_sym(data, inverse_symbol(s), combined_h, new_syls) == (h, syls)
    }),
{
    let n2 = data.p2.num_generators;
    let e = empty_word();
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = b_rcoset_h(data, full_product);
    let merged_rep = b_rcoset_rep(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    assert(word_valid(c1, n2));
    assert(!(c1 =~= e));
    let s_local_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_local_word, n2)) by {
        assert forall|k: int| 0 <= k < s_local_word.len()
            implies symbol_valid(#[trigger] s_local_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_local_word, embed_h, n2);
    crate::word::lemma_concat_word_valid(product, c1, n2);

    //  [inv(s)]·embed_b(combined_h)·merged_rep ≡ embed_b(h)·c₁
    lemma_inv_s_rcoset_merge_equiv_g2(data, s, h, c1);

    //  Idempotency: b_rcoset_rep(merged_rep) =~= merged_rep
    lemma_b_rcoset_rep_idempotent(data, full_product);

    //  syls = [Syl(false, c₁)] + syls.drop_first()
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + syls.drop_first()) by {
        assert(syls.len() == 1 + syls.drop_first().len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + syls.drop_first())[k]
        by { if k == 0 {} else {} }
    }

    //  Setup for case split
    let embed_ch = apply_embedding(b_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    let inv_s_local = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(word_valid(inv_s_local, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_local.len()
            implies symbol_valid(#[trigger] inv_s_local[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    let product_inv = concat(inv_s_local, embed_ch);
    crate::word::lemma_concat_word_valid(inv_s_local, embed_ch, n2);
    lemma_b_rcoset_rep_props(data, full_product);

    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
        + syls.drop_first();

    let rep_inv = b_rcoset_rep(data, product_inv);
    if rep_inv =~= e {
        lemma_c2_rep_zero_branch_g2(data, s, h, c1, combined_h, merged_rep);
        assert(is_canonical_state(data, h, Seq::<Syllable>::empty())) by {
            assert(Seq::<Syllable>::empty().len() == 0int);
        }
        lemma_subgroup_rcoset_restore_g2(data, product_inv, h);
        return;
    }

    //  rep_inv ≠ ε: merge
    lemma_c2_inverse_merge_step_g2(data, s, h, c1, combined_h, merged_rep, syls.drop_first());
}

///  G₂ subcase C2: merge replaced (merged_rep ≠ ε).
#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g2_subcase_c2(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word_shifted = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = b_rcoset_h(data, full_product);
    let merged_rep = b_rcoset_rep(data, full_product);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
        + syls.drop_first();

    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word_shifted, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word_shifted, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word_shifted, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word_shifted, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    lemma_act_right_sym_merge_replaced(data, s, h, syls);
    lemma_act_word_single(data, inverse_symbol(s_shifted), combined_h, new_syls);
    lemma_g2_c2_complete_inverse_step(data, s, h, syls);
    assert(generator_index(inverse_symbol(s_shifted)) >= n1);
}

///  Complete G₂ inverse pair triviality.
///  For ANY G₂ symbol s (shifted, gen_index >= n1) and ANY canonical state: [s, inv(s)] acts trivially.
pub proof fn lemma_inverse_pair_g2(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) >= data.p1.num_generators,
        generator_index(s) < data.p1.num_generators + data.p2.num_generators,
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let s_local = unshift_sym(s, n1);
    //  s_local has gen_index < n2
    //  act_sym(s, ...) = act_right_sym(s_local, ...)
    //  The inverse pair [s, inv(s)] processes via act_sym → act_right_sym for each symbol

    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s_local), embed_h);
    let rep = b_rcoset_rep(data, product);

    if rep =~= empty_word() {
        lemma_inverse_pair_g2_subcase_a(data, s_local, h, syls);
    } else if syls.len() == 0 || syls.first().is_left {
        lemma_inverse_pair_g2_subcase_b(data, s_local, h, syls);
    } else {
        let full_product = concat(product, syls.first().rep);
        let merged_rep = b_rcoset_rep(data, full_product);
        if merged_rep =~= empty_word() {
            lemma_inverse_pair_g2_subcase_c1(data, s_local, h, syls);
        } else {
            lemma_inverse_pair_g2_subcase_c2(data, s_local, h, syls);
        }
    }
    //  Connect s_local shifted back to s
    assert(inverse_pair_word(s) == inverse_pair_word(
        match s_local { Symbol::Gen(i) => Symbol::Gen(i + n1),
                        Symbol::Inv(i) => Symbol::Inv(i + n1) }));
}

} //  verus!
