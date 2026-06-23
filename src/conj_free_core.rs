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
use crate::machine_group::{symbol_power, lemma_symbol_power_merge, lemma_symbol_power_one,
    lemma_inverse_word_one};
use crate::benign::{apply_embedding, apply_embedding_symbol};
use crate::presentation::{equiv_in_presentation, presentation_valid, lemma_equiv_symmetric,
    lemma_equiv_transitive};
use crate::presentation_lemmas::lemma_freely_equivalent_implies_equiv;
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::machine_group::lemma_emb_respects_source_equiv;
use crate::free_word_problem::lemma_free_group_equiv_freely_equivalent;
use crate::f_free::is_free_family;

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

// ----------------------------------------------------------------------------
// Block structure of φ-images: `apply_embedding_symbol(conj_family(k), s) = phi_block(s)`.
// ----------------------------------------------------------------------------

/// The central b-letter of `phi_block(s)`: `Gen(1)` for a generator, `Inv(1)` for an inverse.
pub open spec fn b_sym(s: Symbol) -> Symbol {
    match s { Symbol::Gen(_) => Symbol::Gen(1), Symbol::Inv(_) => Symbol::Inv(1) }
}

/// The image block of a single source symbol: `a⁻ᶜ b^{±} aᶜ` with `c = generator_index(s)`.
pub open spec fn phi_block(s: Symbol) -> Word {
    symbol_power(Symbol::Inv(0), generator_index(s)) + seq![b_sym(s)]
        + symbol_power(Symbol::Gen(0), generator_index(s))
}

/// `inverse_word(symbol_power(s, n)) == symbol_power(inverse_symbol(s), n)` (a constant power).
proof fn lemma_inverse_symbol_power(s: Symbol, n: nat)
    ensures
        inverse_word(symbol_power(s, n)) =~= symbol_power(inverse_symbol(s), n),
    decreases n,
{
    if n == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
        assert(symbol_power(inverse_symbol(s), 0) =~= empty_word());
    } else {
        lemma_symbol_power_merge(s, 1, (n - 1) as nat);
        lemma_inverse_concat(symbol_power(s, 1), symbol_power(s, (n - 1) as nat));
        lemma_inverse_symbol_power(s, (n - 1) as nat);
        lemma_symbol_power_one(s);
        lemma_inverse_word_one(s);
        lemma_symbol_power_merge(inverse_symbol(s), (n - 1) as nat, 1);
        lemma_symbol_power_one(inverse_symbol(s));
    }
}

/// `inverse_word(conj_word(i)) == phi_block(Inv(i)) = a⁻ⁱ b⁻¹ aⁱ`.
proof fn lemma_inverse_conj_word(i: nat)
    ensures
        inverse_word(conj_word(i)) =~= symbol_power(Symbol::Inv(0), i) + seq![Symbol::Inv(1)]
            + symbol_power(Symbol::Gen(0), i),
{
    let p = symbol_power(Symbol::Inv(0), i);
    let m = seq![Symbol::Gen(1)];
    let s = symbol_power(Symbol::Gen(0), i);
    assert(conj_word(i) == p + m + s);
    lemma_inverse_concat(p + m, s);
    lemma_inverse_concat(p, m);
    lemma_inverse_symbol_power(Symbol::Gen(0), i);
    lemma_inverse_symbol_power(Symbol::Inv(0), i);
    lemma_inverse_word_one(Symbol::Gen(1));
}

/// `apply_embedding_symbol(conj_family(k), s) == phi_block(s)`.
pub proof fn lemma_phi_block(k: nat, s: Symbol)
    requires
        symbol_valid(s, k),
    ensures
        crate::benign::apply_embedding_symbol(conj_family(k), s) == phi_block(s),
{
    let fam = conj_family(k);
    let c = generator_index(s);
    assert(c < k);
    match s {
        Symbol::Gen(i) => {
            assert(fam[i as int] == conj_word(i));
            assert(phi_block(s) =~= conj_word(i));
        },
        Symbol::Inv(i) => {
            assert(fam[i as int] == conj_word(i));
            lemma_inverse_conj_word(i);
        },
    }
}

/// The leading block of a φ-image peels off: `φ(w) = phi_block(w[0]) ++ φ(drop_first(w))`.
pub proof fn lemma_emb_first_block(k: nat, w: Word)
    requires
        word_valid(w, k),
        w.len() > 0,
    ensures
        crate::benign::apply_embedding(conj_family(k), w)
            =~= phi_block(w[0]) + crate::benign::apply_embedding(conj_family(k), w.drop_first()),
{
    assert(w.first() == w[0]);
    assert(symbol_valid(w[0], k));
    lemma_phi_block(k, w[0]);
}

/// The a-exponent of a one-symbol power: `asum(symbol_power(s, n)) == n · asym(s)`.
proof fn lemma_asum_symbol_power(s: Symbol, n: nat)
    ensures
        asum(symbol_power(s, n)) == (n as int) * asym(s),
    decreases n,
{
    if n == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
    } else {
        let sp = symbol_power(s, n);
        assert(sp.first() == s);
        assert(sp.drop_first() =~= symbol_power(s, (n - 1) as nat));
        lemma_asum_symbol_power(s, (n - 1) as nat);
        assert(asum(sp) == asym(s) + ((n - 1) as int) * asym(s));
        assert((n as int) * asym(s) == asym(s) + ((n - 1) as int) * asym(s)) by(nonlinear_arith);
    }
}

/// **Structure of `phi_block(s)`** (`c = generator_index(s)`): length `2c+1`; the leading `c` and
/// trailing `c` symbols are non-b `a`-letters; position `c` is the b-letter.
pub proof fn lemma_phi_block_struct(s: Symbol)
    ensures
        phi_block(s).len() == 2 * generator_index(s) + 1,
        is_b(phi_block(s)[generator_index(s) as int]),
        phi_block(s)[generator_index(s) as int] == b_sym(s),
        forall|m: int| 0 <= m < generator_index(s) ==> !is_b(#[trigger] phi_block(s)[m]),
        forall|m: int| generator_index(s) < m < phi_block(s).len() ==> !is_b(#[trigger] phi_block(s)[m]),
{
    let c = generator_index(s);
    let pre = symbol_power(Symbol::Inv(0), c);
    let mid = seq![b_sym(s)];
    let post = symbol_power(Symbol::Gen(0), c);
    assert(pre.len() == c && post.len() == c);
    assert(phi_block(s) == pre + mid + post);
    assert(b_sym(s) == Symbol::Gen(1) || b_sym(s) == Symbol::Inv(1)) by {
        match s { Symbol::Gen(_) => {}, Symbol::Inv(_) => {} }
    }
    // Position c is the b-letter.
    assert((pre + mid)[c as int] == b_sym(s));
    assert(phi_block(s)[c as int] == b_sym(s));
    assert(generator_index(b_sym(s)) == 1);
    // Leading positions: Inv(0), index 0.
    assert forall|m: int| 0 <= m < c implies !is_b(#[trigger] phi_block(s)[m]) by {
        assert(phi_block(s)[m] == pre[m]);
        assert(pre[m] == Symbol::Inv(0));
    }
    // Trailing positions: Gen(0), index 0.
    assert forall|m: int| c < m < phi_block(s).len() implies !is_b(#[trigger] phi_block(s)[m]) by {
        assert(phi_block(s)[m] == post[m - c - 1]);
        assert(post[m - c - 1] == Symbol::Gen(0));
    }
}

// ----------------------------------------------------------------------------
// Concat-subrange helpers for the base case.
// ----------------------------------------------------------------------------

/// A subrange entirely inside the right factor: `(h+v)[a..b] = v[a−|h|..b−|h|]`.
proof fn lemma_concat_subrange_right(h: Word, v: Word, a: int, b: int)
    requires
        h.len() <= a <= b <= h.len() + v.len(),
    ensures
        (h + v).subrange(a, b) =~= v.subrange(a - h.len(), b - h.len()),
{
    assert forall|j: int| #![trigger (h + v).subrange(a, b)[j]]
        0 <= j < (h + v).subrange(a, b).len()
        implies (h + v).subrange(a, b)[j] == v.subrange(a - h.len(), b - h.len())[j] by {
        assert((h + v).subrange(a, b)[j] == (h + v)[a + j]);
        assert((h + v)[a + j] == v[a + j - h.len()]);
        assert(v.subrange(a - h.len(), b - h.len())[j] == v[a - h.len() + j]);
    }
}

/// A subrange straddling the split: `(h+v)[a..b] = h[a..|h|] ++ v[0..b−|h|]`.
proof fn lemma_concat_subrange_mid(h: Word, v: Word, a: int, b: int)
    requires
        0 <= a <= h.len() <= b <= h.len() + v.len(),
    ensures
        (h + v).subrange(a, b) =~= h.subrange(a, h.len() as int) + v.subrange(0, b - h.len()),
{
    let l = h.len() as int;
    assert forall|j: int| #![trigger (h + v).subrange(a, b)[j]]
        0 <= j < (h + v).subrange(a, b).len()
        implies (h + v).subrange(a, b)[j] == (h.subrange(a, l) + v.subrange(0, b - l))[j] by {
        assert((h + v).subrange(a, b)[j] == (h + v)[a + j]);
        assert(h.subrange(a, l).len() == l - a);
        if a + j < l {
            assert((h + v)[a + j] == h[a + j]);
            assert((h.subrange(a, l) + v.subrange(0, b - l))[j] == h.subrange(a, l)[j]);
            assert(h.subrange(a, l)[j] == h[a + j]);
        } else {
            assert((h + v)[a + j] == v[a + j - l]);
            assert((h.subrange(a, l) + v.subrange(0, b - l))[j]
                == v.subrange(0, b - l)[j - (l - a)]);
            assert(v.subrange(0, b - l)[j - (l - a)] == v[j - (l - a)]);
        }
    }
}

/// **First b of a φ-image.**  For `V = φ(w)` (`w` nonempty), the first b-letter sits at position
/// `c = generator_index(w[0])`, equals `b_sym(w[0])`, the earlier positions are non-b, and the
/// length-`c` prefix is exactly `a⁻ᶜ` (a-exponent `−c`).
pub proof fn lemma_emb_first_b(k: nat, w: Word)
    requires
        word_valid(w, k),
        w.len() > 0,
    ensures
        ({
            let v = crate::benign::apply_embedding(conj_family(k), w);
            let c = generator_index(w[0]) as int;
            &&& c < v.len()
            &&& is_b(v[c])
            &&& v[c] == b_sym(w[0])
            &&& (forall|m: int| 0 <= m < c ==> !is_b(#[trigger] v[m]))
            &&& v.subrange(0, c) =~= symbol_power(Symbol::Inv(0), generator_index(w[0]))
        }),
{
    let v = crate::benign::apply_embedding(conj_family(k), w);
    let s = w[0];
    let c = generator_index(s) as int;
    let h = phi_block(s);
    lemma_emb_first_block(k, w);          // v =~= h + φ(rest)
    lemma_phi_block_struct(s);            // h structure, len 2c+1
    let rest_emb = crate::benign::apply_embedding(conj_family(k), w.drop_first());
    assert(v =~= h + rest_emb);
    assert(h.len() == 2 * c + 1);
    // For m ≤ c < h.len(), v[m] = h[m].
    assert forall|m: int| 0 <= m <= c implies v[m] == h[m] by {
        assert(v[m] == (h + rest_emb)[m]);
    }
    assert(v[c] == h[c]);
    // Prefix of length c is the leading a⁻ᶜ of the block.
    assert(v.subrange(0, c) =~= symbol_power(Symbol::Inv(0), generator_index(s))) by {
        let pre = symbol_power(Symbol::Inv(0), generator_index(s));
        assert forall|j: int| #![trigger v.subrange(0, c)[j]] 0 <= j < c
            implies v.subrange(0, c)[j] == pre[j] by {
            assert(v.subrange(0, c)[j] == v[j]);
            assert(v[j] == h[j]);
            assert(h[j] == pre[j]);   // h = pre + mid + post, j < c = pre.len()
        }
    }
}

// ----------------------------------------------------------------------------
// The base case: `bsep(φ(w'))` for a reduced source word `w'`.
// ----------------------------------------------------------------------------

/// If the central b's of two blocks are an inverse pair and the source symbols share a generator
/// index, the source symbols themselves are an inverse pair.
proof fn lemma_b_sym_inverse(s1: Symbol, s2: Symbol)
    requires
        generator_index(s1) == generator_index(s2),
        is_inverse_pair(b_sym(s1), b_sym(s2)),
    ensures
        is_inverse_pair(s1, s2),
{
    match s1 {
        Symbol::Gen(i) => { match s2 { Symbol::Gen(j) => {}, Symbol::Inv(j) => {} } },
        Symbol::Inv(i) => { match s2 { Symbol::Gen(j) => {}, Symbol::Inv(j) => {} } },
    }
}

/// **Boundary case** of the base induction: the head block's b paired with the first b of the rest.
/// The a-block between them has a-exponent `c − c'` (`c = index(w[0])`, `c' = index(w[1])`); the
/// source word being reduced forces `c ≠ c'`, so the exponent is nonzero.
proof fn lemma_bsep_emb_boundary(k: nat, w: Word, q: int)
    requires
        word_valid(w, k),
        is_reduced(w),
        w.len() > 0,
        consec_b(apply_embedding(conj_family(k), w), generator_index(w[0]) as int, q),
        is_inverse_pair(apply_embedding(conj_family(k), w)[generator_index(w[0]) as int],
            apply_embedding(conj_family(k), w)[q]),
    ensures
        asum(apply_embedding(conj_family(k), w).subrange(generator_index(w[0]) as int + 1, q)) != 0,
{
    let fam = conj_family(k);
    let big_w = apply_embedding(fam, w);
    let s = w[0];
    let c = generator_index(s) as int;
    let h = phi_block(s);
    let rest = w.drop_first();
    let v = apply_embedding(fam, rest);
    lemma_emb_first_block(k, w);
    lemma_phi_block_struct(s);
    let l = 2 * c + 1;
    assert(h.len() == l);
    assert(big_w =~= h + v);
    assert(c < q);
    // The rest is nonempty (else the only b is the head-b at c).
    assert(rest.len() > 0) by {
        if rest.len() == 0 {
            assert(v =~= empty_word());
            assert(big_w =~= h);
            assert(big_w[q] == h[q]);
            assert(is_b(big_w[q]));
            assert(q == c);
            assert(false);
        }
    }
    assert(word_valid(rest, k)) by {
        assert forall|j: int| 0 <= j < rest.len() implies symbol_valid(#[trigger] rest[j], k) by {
            assert(rest[j] == w[j + 1]);
        }
    }
    lemma_emb_first_b(k, rest);
    let cp = generator_index(rest[0]) as int;
    assert(is_b(big_w[q]));
    // q lands in the V-region.
    assert(q >= l) by {
        if q < l {
            assert(big_w[q] == h[q]);
            assert(q == c);
            assert(false);
        }
    }
    let qp = q - l;
    assert(big_w[q] == v[qp]) by { assert(big_w[q] == (h + v)[q]); }
    assert(qp < v.len());
    // qp is exactly the first b of V.
    assert(qp >= cp) by {
        if qp < cp {
            assert(!is_b(v[qp]));
            assert(false);
        }
    }
    assert(qp <= cp) by {
        if qp > cp {
            assert(cp < v.len());
            assert(is_b(v[cp]));
            assert(big_w[l + cp] == v[cp]) by { assert(big_w[l + cp] == (h + v)[l + cp]); }
            assert(c < l + cp < q);
            assert(!is_b(big_w[l + cp]));
            assert(false);
        }
    }
    assert(qp == cp);
    assert(q == l + cp);
    // Infix a-exponent = c (trailing aᶜ of the head) + (−c') (leading a⁻ᶜ' of the rest).
    lemma_concat_subrange_mid(h, v, c + 1, q);
    assert(big_w.subrange(c + 1, q) =~= h.subrange(c + 1, l) + v.subrange(0, cp));
    assert(h.subrange(c + 1, l) =~= symbol_power(Symbol::Gen(0), generator_index(s))) by {
        let post = symbol_power(Symbol::Gen(0), generator_index(s));
        let pre = symbol_power(Symbol::Inv(0), generator_index(s));
        let mid = seq![b_sym(s)];
        assert((pre + mid).len() == c + 1);
        assert forall|j: int| #![trigger h.subrange(c + 1, l)[j]] 0 <= j < c
            implies h.subrange(c + 1, l)[j] == post[j] by {
            assert(h.subrange(c + 1, l)[j] == h[c + 1 + j]);
            assert(h[c + 1 + j] == post[j]);
        }
    }
    lemma_asum_symbol_power(Symbol::Gen(0), generator_index(s));
    lemma_asum_symbol_power(Symbol::Inv(0), generator_index(rest[0]));
    lemma_asum_concat(h.subrange(c + 1, l), v.subrange(0, cp));
    // c ≠ c' from reducedness.
    assert(c != cp) by {
        if c == cp {
            assert(big_w[c] == h[c]) by { assert(big_w[c] == (h + v)[c]); }
            assert(h[c] == b_sym(s));
            assert(v[cp] == b_sym(rest[0]));
            assert(is_inverse_pair(b_sym(s), b_sym(rest[0])));
            lemma_b_sym_inverse(s, rest[0]);
            assert(rest[0] == w[1]);
            assert(is_inverse_pair(w[0], w[1]));
            assert(has_cancellation_at(w, 0));
            assert(has_cancellation(w));
            assert(false);
        }
    }
}

/// **Inner case** of the base induction: both b's lie inside the rest's image; conclude directly
/// from `bsep` of the rest's image (the head block lies entirely before them).
proof fn lemma_bsep_emb_inner(k: nat, w: Word, p: int, q: int)
    requires
        word_valid(w, k),
        w.len() > 0,
        bsep(apply_embedding(conj_family(k), w.drop_first())),
        2 * generator_index(w[0]) + 1 <= p,
        consec_b(apply_embedding(conj_family(k), w), p, q),
        is_inverse_pair(apply_embedding(conj_family(k), w)[p], apply_embedding(conj_family(k), w)[q]),
    ensures
        asum(apply_embedding(conj_family(k), w).subrange(p + 1, q)) != 0,
{
    let fam = conj_family(k);
    let big_w = apply_embedding(fam, w);
    let s = w[0];
    let c = generator_index(s) as int;
    let h = phi_block(s);
    let rest = w.drop_first();
    let v = apply_embedding(fam, rest);
    lemma_emb_first_block(k, w);
    lemma_phi_block_struct(s);
    let l = 2 * c + 1;
    assert(h.len() == l);
    assert(big_w =~= h + v);
    assert(p < q);
    let pp = p - l;
    let qp = q - l;
    assert(0 <= pp < qp);
    assert(qp < v.len());
    assert(big_w[p] == v[pp]) by { assert(big_w[p] == (h + v)[p]); }
    assert(big_w[q] == v[qp]) by { assert(big_w[q] == (h + v)[q]); }
    assert(consec_b(v, pp, qp)) by {
        assert forall|mm: int| pp < mm < qp implies !is_b(v[mm]) by {
            assert(big_w[l + mm] == v[mm]) by { assert(big_w[l + mm] == (h + v)[l + mm]); }
            assert(p < l + mm < q);
            assert(!is_b(big_w[l + mm]));
        }
    }
    assert(is_inverse_pair(v[pp], v[qp]));
    assert(asum(v.subrange(pp + 1, qp)) != 0);
    lemma_concat_subrange_right(h, v, p + 1, q);
    assert(big_w.subrange(p + 1, q) =~= v.subrange(pp + 1, qp));
}

/// **THE BASE CASE.**  For a reduced source word `w'`, the embedding `φ(w')` satisfies the
/// net-exponent invariant `bsep`: consecutive same-index source letters are forced to share a sign,
/// so no two consecutive image-b's at equal height ever form an inverse pair.
pub proof fn lemma_bsep_emb(k: nat, w: Word)
    requires
        word_valid(w, k),
        is_reduced(w),
    ensures
        bsep(apply_embedding(conj_family(k), w)),
    decreases w.len(),
{
    let fam = conj_family(k);
    let big_w = apply_embedding(fam, w);
    if w.len() == 0 {
        assert(big_w =~= empty_word());
    } else {
        let s = w[0];
        let c = generator_index(s) as int;
        let rest = w.drop_first();
        let v = apply_embedding(fam, rest);
        let h = phi_block(s);
        let l = 2 * c + 1;
        // rest valid + reduced.
        assert(word_valid(rest, k)) by {
            assert forall|j: int| 0 <= j < rest.len() implies symbol_valid(#[trigger] rest[j], k) by {
                assert(rest[j] == w[j + 1]);
            }
        }
        assert(is_reduced(rest)) by {
            assert forall|i: int| !has_cancellation_at(rest, i) by {
                if 0 <= i < rest.len() - 1 {
                    assert(rest[i] == w[i + 1] && rest[i + 1] == w[i + 2]);
                    if has_cancellation_at(rest, i) {
                        assert(has_cancellation_at(w, i + 1));
                        assert(has_cancellation(w));
                    }
                }
            }
        }
        lemma_bsep_emb(k, rest);            // bsep(v)
        lemma_emb_first_block(k, w);        // big_w =~= h + v
        lemma_phi_block_struct(s);
        assert(h.len() == l);
        assert(big_w =~= h + v);
        assert forall|p: int, q: int| (#[trigger] consec_b(big_w, p, q))
            && is_inverse_pair(big_w[p], big_w[q])
            implies asum(big_w.subrange(p + 1, q)) != 0 by {
            if p < l {
                // The only b in the head block is at position c.
                assert(big_w[p] == h[p]) by { assert(big_w[p] == (h + v)[p]); }
                assert(p == c);
                lemma_bsep_emb_boundary(k, w, q);
            } else {
                lemma_bsep_emb_inner(k, w, p, q);
            }
        }
    }
}

// ----------------------------------------------------------------------------
// `count1` is preserved through the entire reduction to normal form, under `bsep`.
// ----------------------------------------------------------------------------

/// **`count1` is a reduction invariant under `bsep`.**  Every step of the normal-form reduction
/// cancels a non-b pair (by `bsep`), preserving the b-count and re-establishing `bsep`.
pub proof fn lemma_count1_bsep_invariant(w: Word, fuel: nat)
    requires
        bsep(w),
    ensures
        count1(reduce_n_steps(w, fuel)) == count1(w),
        bsep(reduce_n_steps(w, fuel)),
    decreases fuel,
{
    if fuel == 0 {
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        if pos >= w.len() {
        } else {
            // The found cancellation is a non-b pair, so b-count and bsep both survive.
            lemma_bsep_no_b_cancel(w, pos as int);
            lemma_count1_reduce_non_b(w, pos as int);
            lemma_reduce_preserves_bsep(w, pos as int);
            lemma_count1_bsep_invariant(reduce_at(w, pos as int), (fuel - 1) as nat);
        }
    }
}

// ----------------------------------------------------------------------------
// Assembly: `conj_family(k)` is a FREE family in `F₂ = free_group(2)`.
// ----------------------------------------------------------------------------

/// Free reduction preserves word validity (every symbol of `reduce_n_steps(w, fuel)` came from `w`).
proof fn lemma_reduce_n_steps_word_valid(w: Word, fuel: nat, n: nat)
    requires
        word_valid(w, n),
    ensures
        word_valid(reduce_n_steps(w, fuel), n),
    decreases fuel,
{
    if fuel == 0 {
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        if pos >= w.len() {
        } else {
            assert(word_valid(reduce_at(w, pos as int), n)) by {
                crate::britton_infra::lemma_subrange_word_valid(w, 0, pos as int, n);
                crate::britton_infra::lemma_subrange_word_valid(w, pos as int + 2, w.len() as int, n);
                lemma_concat_word_valid(w.subrange(0, pos as int),
                    w.subrange(pos as int + 2, w.len() as int), n);
            }
            lemma_reduce_n_steps_word_valid(reduce_at(w, pos as int), (fuel - 1) as nat, n);
        }
    }
}

/// **The forward freeness obligation.**  If `φ(w)` is trivial in `F₂`, then `w` was already trivial
/// in the abstract free group on the family.  The chain: reduce `w` to `w' = normal_form(w)`; push
/// the source equivalence through φ; the bridge gives `normal_form(φ(w')) = ε`; but `bsep(φ(w'))`
/// (base case) keeps `count1` constant through reduction, so `count1(ε) = count1(φ(w')) = |w'|`,
/// forcing `w' = ε`.
proof fn lemma_conj_family_free_forward(k: nat, w: Word)
    requires
        word_valid(w, k),
        equiv_in_presentation(free_group(2), apply_embedding(conj_family(k), w), empty_word()),
    ensures
        equiv_in_presentation(free_group(k), w, empty_word()),
{
    let fam = conj_family(k);
    let wp = normal_form(w);
    lemma_reduces_to_normal_form(w);                    // reduces_to(w, wp)
    lemma_normal_form_is_reduced(w);                    // is_reduced(wp)
    lemma_reduce_n_steps_word_valid(w, w.len(), k);     // word_valid(wp, k)
    lemma_free_group_valid(k);
    lemma_free_group_valid(2);
    // w ≡ w' in free_group(k) (a pure free reduction).
    lemma_reduces_to_refl(wp);
    assert(freely_equivalent(w, wp));
    lemma_freely_equivalent_implies_equiv(free_group(k), w, wp);
    // Each family image is valid over 2.
    assert forall|i: int| 0 <= i < fam.len() implies word_valid(#[trigger] fam[i], 2) by {
        assert(fam[i] == conj_word(i as nat));
        lemma_conj_word_valid(i as nat);
    }
    // φ respects the (relator-free) source equivalence.
    lemma_emb_respects_source_equiv(free_group(k), free_group(2), fam, w, wp);
    let phw = apply_embedding(fam, w);
    let phwp = apply_embedding(fam, wp);
    crate::benign::lemma_apply_embedding_valid(fam, w, 2);   // word_valid(phw, 2)
    lemma_equiv_symmetric(free_group(2), phw, phwp);
    lemma_equiv_transitive(free_group(2), phwp, phw, empty_word());   // equiv(F₂, φ(w'), ε)
    // Bridge to free reduction; normal_form(φ(w')) = ε.
    lemma_free_group_equiv_freely_equivalent(2, phwp, empty_word());
    lemma_normal_form_equiv_forward(phwp, empty_word());
    lemma_empty_is_reduced();
    lemma_reduced_is_own_normal_form(empty_word());
    assert(normal_form(phwp) =~= empty_word());
    // count1 is constant through the reduction, by bsep — so |w'| = count1(ε) = 0.
    lemma_count1_emb(k, wp);                            // count1(φ(w')) == |w'|
    lemma_bsep_emb(k, wp);                              // bsep(φ(w'))
    lemma_count1_bsep_invariant(phwp, phwp.len());      // count1(normal_form(φ(w'))) == count1(φ(w'))
    assert(count1(empty_word()) == 0);
    assert(wp.len() == 0);
    assert(wp =~= empty_word());
    assert(equiv_in_presentation(free_group(k), w, empty_word()));
}

/// **THE FREE-FAMILY LEMMA (Miller §4.1).**  `conj_family(k) = {a⁻ⁱbaⁱ : 0 ≤ i < k}` is a FREE
/// family in `F₂ = free_group(2)`.  This is the representation-independent foundational lemma of the
/// Higman–Neumann–Neumann embedding (Layer 0.5): "the central b of each term survives free
/// reduction".  Built on the net-exponent invariant `bsep` + the already-banked `count1` counting
/// (`docs/higman-embedding-blueprint.md` §"Build order" step 2).
pub proof fn lemma_conj_family_free(k: nat)
    ensures
        is_free_family(free_group(2), conj_family(k)),
{
    let fam = conj_family(k);
    assert(free_group(2).num_generators == 2);
    // Clause 1: each image is a valid F₂-word.
    assert forall|i: int| 0 <= i < fam.len()
        implies word_valid(#[trigger] fam[i], free_group(2).num_generators) by {
        assert(fam[i] == conj_word(i as nat));
        lemma_conj_word_valid(i as nat);
    }
    // Clause 2: the forward freeness obligation.
    assert forall|w: Word| (#[trigger] word_valid(w, fam.len())
        && equiv_in_presentation(free_group(2), apply_embedding(fam, w), empty_word()))
        implies equiv_in_presentation(free_group(fam.len()), w, empty_word()) by {
        assert(fam.len() == k);
        lemma_conj_family_free_forward(k, w);
    }
}

} // verus!
