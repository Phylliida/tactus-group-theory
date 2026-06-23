// Layer 0.5 crux — THE CORE "central b survives" of the `{a⁻ⁱbaⁱ}`-free lemma (Miller §4.1).
//
// This module finishes the foundational lemma started in `conj_free.rs` / `free_word_problem.rs`:
// the family `conj_family(k) = {a⁻ⁱbaⁱ : 0 ≤ i < k}` is FREE in `F₂ = free_group(2)`
// (a = Gen(0), b = Gen(1)).
//
// THE INVARIANT (`docs/higman-embedding-blueprint.md` §"Build order" step 2, "the net-exponent
// invariant"): a free reduction step removes an `a a⁻¹` (index-0) pair; this preserves the SIGNED
// sum of index-0 symbols (`asum`) between any two fixed CONSECUTIVE b-letters.  Two b's can only
// cancel if they become adjacent (their `a`-block empties ⟹ `asum` between them = 0) AND have
// opposite sign — but `asum = 0` forces equal source index, and a reduced source word then forces
// equal sign.  So no φ-image reduction ever cancels a b ⟹ `count1(normal_form(φ(w'))) = |w'| > 0`.
//
// `bsep(w)` captures the invariant; it is preserved by removing any NON-b inverse pair (such a pair
// has `asum 0` and leaves the b-set untouched), and it forbids any b-cancellation outright — so
// `count1` is constant along the whole reduction to normal form.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::conj_free::*;

verus! {

// ----------------------------------------------------------------------------
// `asum` — the signed count of index-0 (`a`) symbols: +1 per Gen(0), −1 per Inv(0), 0 otherwise.
// This is the "a-exponent", a homomorphism F → ℤ, invariant under free reduction.
// ----------------------------------------------------------------------------

/// The signed value of a single symbol towards the a-exponent.
pub open spec fn asym(s: Symbol) -> int {
    match s {
        Symbol::Gen(i) => if i == 0 { 1int } else { 0int },
        Symbol::Inv(i) => if i == 0 { -1int } else { 0int },
    }
}

/// The a-exponent of a word: signed sum of its index-0 symbols.
pub open spec fn asum(w: Word) -> int
    decreases w.len(),
{
    if w.len() == 0 {
        0int
    } else {
        asym(w.first()) + asum(w.drop_first())
    }
}

/// `asym(inverse_symbol(s)) == -asym(s)`.
pub proof fn lemma_asym_inverse(s: Symbol)
    ensures
        asym(inverse_symbol(s)) == -asym(s),
{
    match s { Symbol::Gen(i) => {}, Symbol::Inv(i) => {} }
}

/// A b-letter (index 1) contributes 0 to the a-exponent.
pub proof fn lemma_asym_b(s: Symbol)
    requires
        generator_index(s) == 1,
    ensures
        asym(s) == 0,
{
    match s { Symbol::Gen(i) => {}, Symbol::Inv(i) => {} }
}

/// `asum` of a single-symbol word.
pub proof fn lemma_asum_single(w: Word, s: Symbol)
    requires
        w.len() == 1,
        w[0] == s,
    ensures
        asum(w) == asym(s),
{
    assert(w.first() == s);
    assert(w.drop_first() =~= empty_word());
    assert(asum(w.drop_first()) == 0);
}

/// `asum` is additive over concatenation.
pub proof fn lemma_asum_concat(a: Word, b: Word)
    ensures
        asum(a + b) == asum(a) + asum(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        let first = a.first();
        assert((a + b).first() == first);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_asum_concat(a.drop_first(), b);
    }
}

/// A length-2 inverse pair has a-exponent 0 (whatever its index).
pub proof fn lemma_asum_inverse_pair_zero(pair: Word, s1: Symbol, s2: Symbol)
    requires
        pair.len() == 2,
        pair[0] == s1,
        pair[1] == s2,
        is_inverse_pair(s1, s2),
    ensures
        asum(pair) == 0,
{
    assert(pair.first() == s1);
    assert(pair.drop_first().len() == 1);
    assert(pair.drop_first()[0] == s2);
    lemma_asum_single(pair.drop_first(), s2);
    // asum(pair) = asym(s1) + asym(s2) = asym(s1) + asym(inverse_symbol(s1)) = 0.
    assert(s2 == inverse_symbol(s1));
    lemma_asym_inverse(s1);
}

// ----------------------------------------------------------------------------
// `count1` of `reduce_at` — removing a NON-b pair leaves the b-count unchanged.
// ----------------------------------------------------------------------------

/// `count1` of a length-2 word with both symbols non-b is 0.
pub proof fn lemma_count1_pair_non_b(pair: Word, s1: Symbol, s2: Symbol)
    requires
        pair.len() == 2,
        pair[0] == s1,
        pair[1] == s2,
        generator_index(s1) != 1,
        generator_index(s2) != 1,
    ensures
        count1(pair) == 0,
{
    assert(pair.first() == s1);
    assert(pair.drop_first().len() == 1);
    assert(pair.drop_first()[0] == s2);
    lemma_count1_single(pair.drop_first(), s2);
}

/// **Removing a non-b inverse pair preserves the b-count.**  `count1(reduce_at(w, i)) == count1(w)`
/// whenever the cancelled pair at `i` is not a b-letter (index ≠ 1).
pub proof fn lemma_count1_reduce_non_b(w: Word, i: int)
    requires
        has_cancellation_at(w, i),
        generator_index(w[i]) != 1,
    ensures
        count1(reduce_at(w, i)) == count1(w),
{
    // w[i+1] is the inverse of w[i], so also index ≠ 1.
    assert(w[i + 1] == inverse_symbol(w[i]));
    assert(generator_index(w[i + 1]) != 1) by {
        match w[i] { Symbol::Gen(_) => {}, Symbol::Inv(_) => {} }
    }
    let pre = w.subrange(0, i);
    let pair = w.subrange(i, i + 2);
    let post = w.subrange(i + 2, w.len() as int);
    // w = pre + pair + post.
    assert(w =~= pre + pair + post);
    assert(reduce_at(w, i) =~= pre + post);
    // count1(pair) == 0.
    assert(pair.len() == 2 && pair[0] == w[i] && pair[1] == w[i + 1]);
    lemma_count1_pair_non_b(pair, w[i], w[i + 1]);
    lemma_count1_concat(pre + pair, post);
    lemma_count1_concat(pre, pair);
    lemma_count1_concat(pre, post);
}

} // verus!
