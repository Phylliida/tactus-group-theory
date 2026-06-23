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

// ----------------------------------------------------------------------------
// `bsep` — the net-exponent invariant.
// ----------------------------------------------------------------------------

/// A symbol is a `b`-letter (generator index 1).
pub open spec fn is_b(s: Symbol) -> bool {
    generator_index(s) == 1
}

/// `p` and `q` are CONSECUTIVE b-positions of `w`: both are b-letters, `p < q`, and no b-letter
/// lies strictly between them.
pub open spec fn consec_b(w: Word, p: int, q: int) -> bool {
    0 <= p < q < w.len()
    && is_b(w[p]) && is_b(w[q])
    && (forall|m: int| p < m < q ==> !is_b(w[m]))
}

/// **The net-exponent invariant.**  For every pair of consecutive b-letters that form an inverse
/// pair, the a-exponent of the block strictly between them is nonzero — so they can never be
/// brought adjacent (their `a`-block can never empty) and thus never cancel.
pub open spec fn bsep(w: Word) -> bool {
    forall|p: int, q: int| (#[trigger] consec_b(w, p, q)) && is_inverse_pair(w[p], w[q])
        ==> asum(w.subrange(p + 1, q)) != 0
}

/// **No b-cancellation under `bsep`.**  Every cancellable pair of `w` is a non-b pair.
pub proof fn lemma_bsep_no_b_cancel(w: Word, i: int)
    requires
        bsep(w),
        has_cancellation_at(w, i),
    ensures
        generator_index(w[i]) != 1,
{
    if generator_index(w[i]) == 1 {
        // w[i+1] is the inverse of w[i], hence also a b-letter.
        assert(w[i + 1] == inverse_symbol(w[i]));
        assert(is_b(w[i + 1])) by {
            match w[i] { Symbol::Gen(_) => {}, Symbol::Inv(_) => {} }
        }
        // i, i+1 are consecutive b-letters (nothing strictly between) forming an inverse pair.
        assert(consec_b(w, i, i + 1));
        assert(is_inverse_pair(w[i], w[i + 1]));
        // The block between them is empty, so its a-exponent is 0 — contradicting bsep.
        assert(w.subrange(i + 1, i + 1) =~= empty_word());
        assert(asum(w.subrange(i + 1, i + 1)) == 0);
        assert(false);
    }
}

// ----------------------------------------------------------------------------
// Preservation of `bsep` under removing a non-b inverse pair.
// ----------------------------------------------------------------------------

/// The preimage in `w` of a `reduce_at(w, i)` position: skip the removed two-symbol hole at `i`.
pub open spec fn pre_pos(i: int, k: int) -> int {
    if k < i { k } else { k + 2 }
}

/// `reduce_at(w, i)[k] == w[pre_pos(i, k)]` for every position `k` of the reduct.
pub proof fn lemma_reduce_elem(w: Word, i: int, k: int)
    requires
        has_cancellation_at(w, i),
        0 <= k < reduce_at(w, i).len(),
    ensures
        reduce_at(w, i)[k] == w[pre_pos(i, k)],
{
    lemma_reduce_at_elements(w, i);
}

/// Consecutive b-letters of `reduce_at(w, i)` pull back to consecutive b-letters of `w` (when the
/// removed pair is not a b-pair, so the b-set is untouched).
proof fn lemma_consec_b_preimage(w: Word, i: int, p: int, q: int)
    requires
        has_cancellation_at(w, i),
        generator_index(w[i]) != 1,
        consec_b(reduce_at(w, i), p, q),
    ensures
        consec_b(w, pre_pos(i, p), pre_pos(i, q)),
        reduce_at(w, i)[p] == w[pre_pos(i, p)],
        reduce_at(w, i)[q] == w[pre_pos(i, q)],
{
    let red = reduce_at(w, i);
    let ph = pre_pos(i, p);
    let qh = pre_pos(i, q);
    // The removed pair is non-b at both positions.
    assert(w[i + 1] == inverse_symbol(w[i]));
    assert(!is_b(w[i]));
    assert(!is_b(w[i + 1])) by {
        match w[i] { Symbol::Gen(_) => {}, Symbol::Inv(_) => {} }
    }
    lemma_reduce_elem(w, i, p);
    lemma_reduce_elem(w, i, q);
    // Endpoints: b-letters, in range, p̂ < q̂.
    assert(red.len() == w.len() - 2);
    assert(is_b(w[ph]) && is_b(w[qh]));
    assert(0 <= ph < qh < w.len());
    // No b strictly between p̂ and q̂.
    assert forall|mh: int| ph < mh < qh implies !is_b(w[mh]) by {
        // mh ≠ i, i+1 (those are non-b); map mh back to a reduct position m with p < m < q.
        if mh != i && mh != i + 1 {
            let m = if mh < i { mh } else { mh - 2 };
            assert(0 <= m < red.len());
            lemma_reduce_elem(w, i, m);
            assert(red[m] == w[mh]);
            assert(p < m < q);          // pre_pos order-reflecting
            assert(!is_b(red[m]));
        }
    }
}

/// The a-exponent of a subrange splits via prefixes: `asum(w[a..b]) = asum(w[0..b]) − asum(w[0..a])`.
proof fn lemma_asum_subrange_split(w: Word, a: int, b: int)
    requires
        0 <= a <= b <= w.len(),
    ensures
        asum(w.subrange(a, b)) == asum(w.subrange(0, b)) - asum(w.subrange(0, a)),
{
    assert(w.subrange(0, b) =~= w.subrange(0, a) + w.subrange(a, b));
    lemma_asum_concat(w.subrange(0, a), w.subrange(a, b));
}

/// The prefix a-exponent of the reduct equals a prefix a-exponent of `w` (the removed pair, having
/// a-exponent 0, contributes nothing to prefixes that reach past the hole).
proof fn lemma_pa_reduce(w: Word, i: int, k: int)
    requires
        has_cancellation_at(w, i),
        0 <= k <= reduce_at(w, i).len(),
    ensures
        asum(reduce_at(w, i).subrange(0, k))
            == asum(w.subrange(0, if k <= i { k } else { k + 2 })),
{
    let red = reduce_at(w, i);
    lemma_reduce_at_elements(w, i);
    if k <= i {
        assert(red.subrange(0, k) =~= w.subrange(0, k)) by {
            assert forall|j: int| #![trigger red.subrange(0, k)[j]]
                0 <= j < red.subrange(0, k).len()
                implies red.subrange(0, k)[j] == w.subrange(0, k)[j] by {
                assert(red.subrange(0, k)[j] == red[j]);
                assert(red[j] == w[j]);   // j < k <= i
            }
        }
    } else {
        let pre = w.subrange(0, i);
        let pair = w.subrange(i, i + 2);
        let post = w.subrange(i + 2, k + 2);
        assert(red.subrange(0, k) =~= pre + post) by {
            assert forall|j: int| #![trigger red.subrange(0, k)[j]]
                0 <= j < red.subrange(0, k).len()
                implies red.subrange(0, k)[j] == (pre + post)[j] by {
                assert(red.subrange(0, k)[j] == red[j]);
                if j < i {
                    assert(red[j] == w[j]);
                    assert((pre + post)[j] == pre[j]);
                } else {
                    assert(red[j] == w[j + 2]);
                    assert((pre + post)[j] == post[j - pre.len()]);
                    assert(post[j - pre.len()] == w[i + 2 + (j - i)]);
                }
            }
        }
        assert(w.subrange(0, k + 2) =~= pre + pair + post) by {
            assert(w.subrange(0, k + 2) =~= pre + w.subrange(i, k + 2));
            assert(w.subrange(i, k + 2) =~= pair + post);
        }
        lemma_asum_concat(pre, post);
        lemma_asum_concat(pre + pair, post);
        lemma_asum_concat(pre, pair);
        lemma_asum_inverse_pair_zero(pair, w[i], w[i + 1]);
    }
}

/// At `k`, the two preimage maps (`≤` for prefix lengths, `<` for positions) agree as a-exponents:
/// they differ only at `k == i`, where the difference is the removed pair (a-exponent 0).
proof fn lemma_pa_pre_pos(w: Word, i: int, k: int)
    requires
        has_cancellation_at(w, i),
        0 <= k <= w.len() - 2,
    ensures
        asum(w.subrange(0, if k <= i { k } else { k + 2 })) == asum(w.subrange(0, pre_pos(i, k))),
{
    if k == i {
        // LHS = asum(w[0..i]); RHS = asum(w[0..i+2]) — differ by the pair, which has a-exponent 0.
        lemma_asum_subrange_split(w, i, i + 2);
        lemma_asum_inverse_pair_zero(w.subrange(i, i + 2), w[i], w[i + 1]);
    }
}

/// The a-exponent of the block between consecutive positions is preserved by removing the pair:
/// `asum(reduce_at(w,i).subrange(p+1, q)) == asum(w.subrange(p̂+1, q̂))`.  Holds for any positions
/// (the removed inverse pair contributes a-exponent 0).
proof fn lemma_asum_infix_eq(w: Word, i: int, p: int, q: int)
    requires
        has_cancellation_at(w, i),
        0 <= p < q <= reduce_at(w, i).len(),
    ensures
        asum(reduce_at(w, i).subrange(p + 1, q))
            == asum(w.subrange(pre_pos(i, p) + 1, pre_pos(i, q))),
{
    let red = reduce_at(w, i);
    let ph = pre_pos(i, p);
    let qh = pre_pos(i, q);
    assert(red.len() == w.len() - 2);
    // Split the reduct block via prefixes.
    lemma_asum_subrange_split(red, p + 1, q);
    lemma_pa_reduce(w, i, q);
    lemma_pa_reduce(w, i, p + 1);
    lemma_pa_pre_pos(w, i, q);
    // The (p+1)-prefix map agrees with ph+1 as a position (no boundary subtlety).
    assert((if p + 1 <= i { p + 1 } else { p + 1 + 2 }) == ph + 1);
    // ph < qh (pre_pos is strictly monotone), so the w-block range is well-formed.
    assert(0 <= ph + 1 <= qh <= w.len());
    lemma_asum_subrange_split(w, ph + 1, qh);
}

/// **Preservation.**  `bsep` survives removing any non-b inverse pair.
pub proof fn lemma_reduce_preserves_bsep(w: Word, i: int)
    requires
        bsep(w),
        has_cancellation_at(w, i),
        generator_index(w[i]) != 1,
    ensures
        bsep(reduce_at(w, i)),
{
    let red = reduce_at(w, i);
    assert forall|p: int, q: int| (#[trigger] consec_b(red, p, q)) && is_inverse_pair(red[p], red[q])
        implies asum(red.subrange(p + 1, q)) != 0 by {
        let ph = pre_pos(i, p);
        let qh = pre_pos(i, q);
        lemma_consec_b_preimage(w, i, p, q);
        // is_inverse_pair carries to the preimage endpoints.
        assert(is_inverse_pair(w[ph], w[qh]));
        // bsep(w) on the consecutive preimage pair.
        assert(consec_b(w, ph, qh));
        assert(asum(w.subrange(ph + 1, qh)) != 0);
        // a-exponent of the block is preserved.
        assert(0 <= p < q <= red.len());
        lemma_asum_infix_eq(w, i, p, q);
    }
}

} // verus!
