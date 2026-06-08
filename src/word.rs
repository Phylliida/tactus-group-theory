use vstd::prelude::*;
use crate::symbol::*;

verus! {

/// A word is a finite sequence of symbols.
/// The empty word represents the group identity.
pub type Word = Seq<Symbol>;

/// The empty word (identity element).
pub open spec fn empty_word() -> Word {
    Seq::empty()
}

/// Concatenation of two words.
pub open spec fn concat(w1: Word, w2: Word) -> Word {
    w1 + w2
}

/// The formal inverse of a word: reverse and invert each symbol.
/// (s₁ s₂ ... sₙ)⁻¹ = sₙ⁻¹ ... s₂⁻¹ s₁⁻¹
pub open spec fn inverse_word(w: Word) -> Word
    decreases w.len(),
{
    if w.len() == 0 {
        empty_word()
    } else {
        inverse_word(w.drop_first()) + Seq::new(1, |_i: int| inverse_symbol(w.first()))
    }
}

/// Length of the inverse word equals the original.
pub proof fn lemma_inverse_word_len(w: Word)
    ensures
        inverse_word(w).len() == w.len(),
    decreases w.len(),
{
    if w.len() > 0 {
        lemma_inverse_word_len(w.drop_first());
    }
}

/// All symbols in a word are valid for a group with `n` generators.
pub open spec fn word_valid(w: Word, n: nat) -> bool {
    forall|i: int| 0 <= i < w.len() ==> symbol_valid(#[trigger] w[i], n)
}

/// The inverse of the empty word is empty.
pub proof fn lemma_inverse_empty()
    ensures
        inverse_word(empty_word()) == empty_word(),
{
}

/// Inverse of a single-symbol word.
pub proof fn lemma_inverse_singleton(s: Symbol)
    ensures
        inverse_word(Seq::new(1, |_i: int| s)) =~= Seq::new(1, |_i: int| inverse_symbol(s)),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.first() == s);
    assert(w.drop_first() =~= empty_word());
    assert(inverse_word(w) =~= inverse_word(empty_word()) + Seq::new(1, |_i: int| inverse_symbol(s)));
    assert(inverse_word(empty_word()) =~= empty_word());
}

/// Inverse distributes over concatenation (reversed).
/// (w1 · w2)⁻¹ = w2⁻¹ · w1⁻¹
pub proof fn lemma_inverse_concat(w1: Word, w2: Word)
    ensures
        inverse_word(concat(w1, w2)) =~= concat(inverse_word(w2), inverse_word(w1)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(inverse_word(w1) =~= empty_word());
        assert(concat(inverse_word(w2), empty_word()) =~= inverse_word(w2));
    } else {
        // w1 = first · rest
        let first = w1.first();
        let rest = w1.drop_first();
        // concat(w1, w2) = first · concat(rest, w2)
        assert(concat(w1, w2).drop_first() =~= concat(rest, w2));
        assert(concat(w1, w2).first() == first);

        // IH: inverse(concat(rest, w2)) =~= concat(inverse(w2), inverse(rest))
        lemma_inverse_concat(rest, w2);

        // inverse(w1) = inverse(rest) · inv(first)
        // inverse(concat(w1, w2)) = inverse(concat(rest, w2)) · inv(first)
        //                         = concat(inverse(w2), inverse(rest)) · inv(first)
        //                         = concat(inverse(w2), inverse(rest) · inv(first))
        //                         = concat(inverse(w2), inverse(w1))
        let inv_first = Seq::new(1, |_i: int| inverse_symbol(first));
        assert(inverse_word(w1) =~= inverse_word(rest) + inv_first);
        assert(inverse_word(concat(w1, w2)) =~= (inverse_word(w2) + inverse_word(rest)) + inv_first);
        assert(concat(inverse_word(w2), inverse_word(w1)) =~= inverse_word(w2) + (inverse_word(rest) + inv_first));
        // Seq concat is associative
        assert(((inverse_word(w2) + inverse_word(rest)) + inv_first) =~= (inverse_word(w2) + (inverse_word(rest) + inv_first)));
    }
}

/// Inverse is an involution: (w⁻¹)⁻¹ = w.
pub proof fn lemma_inverse_involution(w: Word)
    ensures
        inverse_word(inverse_word(w)) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let first = w.first();
        let rest = w.drop_first();
        let inv_first = Seq::new(1, |_i: int| inverse_symbol(first));

        // inverse(w) = inverse(rest) · inv(first)
        lemma_inverse_involution(rest);

        // inverse(inverse(w)) = inverse(inverse(rest) · inv(first))
        //                     = inverse(inv(first)) · inverse(inverse(rest))    by lemma_inverse_concat
        //                     = first · rest = w                                 by IH
        lemma_inverse_concat(inverse_word(rest), inv_first);

        // inverse(inv(first)) = [first]
        lemma_inverse_singleton(inverse_symbol(first));
        crate::symbol::lemma_inverse_involution(first);
        assert(inverse_word(inv_first) =~= Seq::new(1, |_i: int| first));

        assert(w =~= Seq::new(1, |_i: int| first) + rest);
    }
}

/// Concatenation with the empty word (right identity).
pub proof fn lemma_concat_empty_right(w: Word)
    ensures
        concat(w, empty_word()) =~= w,
{
}

/// Concatenation with the empty word (left identity).
pub proof fn lemma_concat_empty_left(w: Word)
    ensures
        concat(empty_word(), w) =~= w,
{
}

/// Concatenation is associative.
pub proof fn lemma_concat_assoc(w1: Word, w2: Word, w3: Word)
    ensures
        concat(concat(w1, w2), w3) =~= concat(w1, concat(w2, w3)),
{
}

/// Length of concatenation is sum of lengths.
pub proof fn lemma_concat_len(w1: Word, w2: Word)
    ensures
        concat(w1, w2).len() == w1.len() + w2.len(),
{
}

/// inverse_word preserves word_valid.
pub proof fn lemma_inverse_word_valid(w: Word, n: nat)
    requires word_valid(w, n),
    ensures word_valid(inverse_word(w), n),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        let rest = w.drop_first();
        assert(word_valid(rest, n)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(rest[i], n) by { assert(rest[i] == w[i + 1]); }
        }
        lemma_inverse_word_valid(rest, n);
        let inv_rest = inverse_word(rest);
        let inv_first = inverse_symbol(w.first());
        assert(inverse_word(w) =~= inv_rest + seq![inv_first]);
        lemma_inverse_preserves_valid(w.first(), n);
        assert forall|i: int| 0 <= i < inverse_word(w).len()
            implies symbol_valid(inverse_word(w)[i], n)
        by {
            if i < inv_rest.len() {
                assert(inverse_word(w)[i] == inv_rest[i]);
            } else {
                assert(inverse_word(w)[i] == inv_first);
            }
        }
    }
}

/// Concatenation preserves word_valid.
pub proof fn lemma_concat_word_valid(w1: Word, w2: Word, n: nat)
    requires word_valid(w1, n), word_valid(w2, n),
    ensures word_valid(concat(w1, w2), n),
{
    assert forall|k: int| 0 <= k < concat(w1, w2).len()
        implies symbol_valid(concat(w1, w2)[k], n)
    by {
        if k < w1.len() {
            assert(concat(w1, w2)[k] == w1[k]);
        } else {
            assert(concat(w1, w2)[k] == w2[k - w1.len()]);
        }
    }
}

} // verus!
