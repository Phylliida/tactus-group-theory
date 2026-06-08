use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;

verus! {

//  ============================================================
//  Symbol ordering
//  ============================================================

///  Total ordering on symbols: Gen(0) < Inv(0) < Gen(1) < Inv(1) < ...
///  Maps each symbol to a unique natural number for comparison.
pub open spec fn symbol_ord(s: Symbol) -> nat {
    match s {
        Symbol::Gen(i) => 2 * i,
        Symbol::Inv(i) => 2 * i + 1,
    }
}

///  symbol_ord is injective: distinct symbols have distinct ordinals.
pub proof fn lemma_symbol_ord_injective(s1: Symbol, s2: Symbol)
    requires
        symbol_ord(s1) == symbol_ord(s2),
    ensures
        s1 == s2,
{
}

///  Inverse symbol has adjacent ordinal.
pub proof fn lemma_symbol_ord_inverse(s: Symbol)
    ensures
        symbol_ord(inverse_symbol(s)) != symbol_ord(s),
{
}

//  ============================================================
//  Lexicographic ordering on words (same-length)
//  ============================================================

///  Lexicographic comparison at a given position.
///  Returns true if w1 < w2 at the first position >= `from` where they differ.
pub open spec fn lex_lt_from(w1: Word, w2: Word, from: nat) -> bool
    decreases w1.len() - from,
{
    if from >= w1.len() {
        false  //  identical words are not strictly less
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        true
    } else if symbol_ord(w1[from as int]) > symbol_ord(w2[from as int]) {
        false
    } else {
        lex_lt_from(w1, w2, from + 1)
    }
}

///  Lexicographic strict less-than on same-length words.
pub open spec fn lex_lt(w1: Word, w2: Word) -> bool
    recommends
        w1.len() == w2.len(),
{
    lex_lt_from(w1, w2, 0)
}

//  ============================================================
//  Shortlex ordering
//  ============================================================

///  Shortlex ordering: shorter words first, then lexicographic for same length.
///  This is a reduction ordering (well-founded + compatible with concatenation).
pub open spec fn shortlex_lt(w1: Word, w2: Word) -> bool {
    w1.len() < w2.len() || (w1.len() == w2.len() && lex_lt(w1, w2))
}

//  ============================================================
//  Lex ordering lemmas
//  ============================================================

///  lex_lt_from is irreflexive.
pub proof fn lemma_lex_lt_from_irreflexive(w: Word, from: nat)
    ensures
        !lex_lt_from(w, w, from),
    decreases w.len() - from,
{
    if from >= w.len() {
    } else {
        lemma_lex_lt_from_irreflexive(w, from + 1);
    }
}

///  lex_lt is irreflexive.
pub proof fn lemma_lex_lt_irreflexive(w: Word)
    ensures
        !lex_lt(w, w),
{
    lemma_lex_lt_from_irreflexive(w, 0);
}

///  lex_lt_from is asymmetric.
pub proof fn lemma_lex_lt_from_asymmetric(w1: Word, w2: Word, from: nat)
    requires
        w1.len() == w2.len(),
        lex_lt_from(w1, w2, from),
    ensures
        !lex_lt_from(w2, w1, from),
    decreases w1.len() - from,
{
    if from >= w1.len() {
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        //  w1 < w2 at this position, so w2[from] > w1[from], thus w2 !< w1
    } else if symbol_ord(w1[from as int]) > symbol_ord(w2[from as int]) {
        //  contradicts lex_lt_from(w1, w2, from)
    } else {
        lemma_lex_lt_from_asymmetric(w1, w2, from + 1);
    }
}

///  lex_lt_from is transitive.
pub proof fn lemma_lex_lt_from_transitive(w1: Word, w2: Word, w3: Word, from: nat)
    requires
        w1.len() == w2.len(),
        w2.len() == w3.len(),
        lex_lt_from(w1, w2, from),
        lex_lt_from(w2, w3, from),
    ensures
        lex_lt_from(w1, w3, from),
    decreases w1.len() - from,
{
    if from >= w1.len() {
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        //  w1[from] < w2[from] and w2[from] <= w3[from], so w1[from] < w3[from] or equal then recurse
        if symbol_ord(w2[from as int]) < symbol_ord(w3[from as int]) {
            //  w1[from] < w3[from]
        } else if symbol_ord(w2[from as int]) == symbol_ord(w3[from as int]) {
            //  w1[from] < w2[from] = w3[from]
        } else {
            //  w2[from] > w3[from], contradicts lex_lt_from(w2, w3, from) unless resolved earlier
            //  but w2[from] > w3[from] means lex_lt_from(w2, w3, from) = false, contradiction
        }
    } else if symbol_ord(w1[from as int]) == symbol_ord(w2[from as int]) {
        if symbol_ord(w2[from as int]) < symbol_ord(w3[from as int]) {
            //  w1[from] = w2[from] < w3[from]
        } else if symbol_ord(w2[from as int]) == symbol_ord(w3[from as int]) {
            //  all equal, recurse
            lemma_lex_lt_from_transitive(w1, w2, w3, from + 1);
        } else {
            //  w2[from] > w3[from], contradicts lex_lt_from(w2, w3, from)
        }
    } else {
        //  w1[from] > w2[from], contradicts lex_lt_from(w1, w2, from)
    }
}

///  lex_lt is transitive.
pub proof fn lemma_lex_lt_transitive(w1: Word, w2: Word, w3: Word)
    requires
        w1.len() == w2.len(),
        w2.len() == w3.len(),
        lex_lt(w1, w2),
        lex_lt(w2, w3),
    ensures
        lex_lt(w1, w3),
{
    lemma_lex_lt_from_transitive(w1, w2, w3, 0);
}

///  lex_lt_from is total on same-length distinct words (trichotomy).
pub proof fn lemma_lex_lt_from_total(w1: Word, w2: Word, from: nat)
    requires
        w1.len() == w2.len(),
        w1 !== w2,
        //  They differ at some position >= from
        exists|k: int| from as int <= k < w1.len() as int && w1[k] !== w2[k],
    ensures
        lex_lt_from(w1, w2, from) || lex_lt_from(w2, w1, from),
    decreases w1.len() - from,
{
    if from >= w1.len() {
        //  contradiction: no position exists
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
    } else if symbol_ord(w1[from as int]) > symbol_ord(w2[from as int]) {
    } else {
        //  same ordinal means same symbol
        lemma_symbol_ord_injective(w1[from as int], w2[from as int]);
        //  They still differ somewhere after `from`
        let k = choose|k: int| from as int <= k < w1.len() as int && w1[k] !== w2[k];
        assert(k > from as int);  //  since w1[from] == w2[from]
        assert(exists|k: int| (from + 1) as int <= k < w1.len() as int && w1[k] !== w2[k]);
        lemma_lex_lt_from_total(w1, w2, from + 1);
    }
}

///  Same-length words: if not equal, one is lex-less than the other.
pub proof fn lemma_lex_lt_total(w1: Word, w2: Word)
    requires
        w1.len() == w2.len(),
    ensures
        lex_lt(w1, w2) || lex_lt(w2, w1) || w1 =~= w2,
{
    if w1 =~= w2 {
    } else {
        //  They differ somewhere
        assert(exists|k: int| 0 <= k < w1.len() as int && w1[k] !== w2[k]) by {
            if forall|k: int| 0 <= k < w1.len() as int ==> w1[k] === w2[k] {
                assert(w1 =~= w2);
            }
        }
        lemma_lex_lt_from_total(w1, w2, 0);
    }
}

//  ============================================================
//  Shortlex ordering lemmas
//  ============================================================

///  Shortlex is irreflexive.
pub proof fn lemma_shortlex_irreflexive(w: Word)
    ensures
        !shortlex_lt(w, w),
{
    lemma_lex_lt_irreflexive(w);
}

///  Shortlex is transitive.
pub proof fn lemma_shortlex_transitive(w1: Word, w2: Word, w3: Word)
    requires
        shortlex_lt(w1, w2),
        shortlex_lt(w2, w3),
    ensures
        shortlex_lt(w1, w3),
{
    if w1.len() < w2.len() {
        if w2.len() < w3.len() {
            //  w1.len() < w3.len()
        } else {
            //  w2.len() == w3.len() && lex_lt(w2, w3), but w1.len() < w2.len() = w3.len()
        }
    } else {
        //  w1.len() == w2.len() && lex_lt(w1, w2)
        if w2.len() < w3.len() {
            //  w1.len() = w2.len() < w3.len()
        } else {
            //  w1.len() == w2.len() == w3.len()
            lemma_lex_lt_transitive(w1, w2, w3);
        }
    }
}

///  Shortlex is total: any two distinct words are comparable.
pub proof fn lemma_shortlex_total(w1: Word, w2: Word)
    ensures
        shortlex_lt(w1, w2) || shortlex_lt(w2, w1) || w1 =~= w2,
{
    if w1.len() < w2.len() {
    } else if w2.len() < w1.len() {
    } else {
        lemma_lex_lt_total(w1, w2);
    }
}

///  Shortlex is asymmetric.
pub proof fn lemma_shortlex_asymmetric(w1: Word, w2: Word)
    requires
        shortlex_lt(w1, w2),
    ensures
        !shortlex_lt(w2, w1),
{
    if w1.len() < w2.len() {
        //  w2.len() > w1.len(), so w2.len() < w1.len() is false and w2.len() == w1.len() is false
    } else {
        //  w1.len() == w2.len() && lex_lt(w1, w2)
        lemma_lex_lt_from_asymmetric(w1, w2, 0);
    }
}

///  The empty word is shortlex-minimal: nothing is smaller than it.
pub proof fn lemma_empty_shortlex_minimal(w: Word)
    ensures
        !shortlex_lt(w, empty_word()) || w =~= empty_word(),
{
}

//  ============================================================
//  Compatibility with concatenation
//  ============================================================

///  Key lemma: if two words have the same length and one is lex-smaller,
///  then prepending the same prefix preserves the lex ordering.
pub proof fn lemma_lex_lt_from_prepend(w1: Word, w2: Word, prefix: Word, from: nat)
    requires
        w1.len() == w2.len(),
        lex_lt_from(w1, w2, from),
    ensures
        lex_lt_from(prefix + w1, prefix + w2, prefix.len() + from),
    decreases w1.len() - from,
{
    let pw1 = prefix + w1;
    let pw2 = prefix + w2;
    if from >= w1.len() {
    } else {
        let idx = prefix.len() + from;
        assert(pw1[idx as int] == w1[from as int]);
        assert(pw2[idx as int] == w2[from as int]);
        if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
            //  pw1[idx] < pw2[idx], so lex_lt_from(pw1, pw2, idx) = true
        } else if symbol_ord(w1[from as int]) == symbol_ord(w2[from as int]) {
            lemma_lex_lt_from_prepend(w1, w2, prefix, from + 1);
        }
    }
}

///  Key lemma: if two words have the same length and one is lex-smaller,
///  then appending the same suffix preserves the lex ordering.
pub proof fn lemma_lex_lt_from_append(w1: Word, w2: Word, suffix: Word, from: nat)
    requires
        w1.len() == w2.len(),
        lex_lt_from(w1, w2, from),
    ensures
        lex_lt_from(w1 + suffix, w2 + suffix, from),
    decreases w1.len() - from,
{
    let ws1 = w1 + suffix;
    let ws2 = w2 + suffix;
    if from >= w1.len() {
    } else {
        assert(ws1[from as int] == w1[from as int]);
        assert(ws2[from as int] == w2[from as int]);
        if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        } else if symbol_ord(w1[from as int]) == symbol_ord(w2[from as int]) {
            lemma_lex_lt_from_append(w1, w2, suffix, from + 1);
        }
    }
}

///  Shortlex is compatible with concatenation on both sides.
///  If u < v in shortlex, then w·u·x < w·v·x for any w, x.
///  (This is the "reduction ordering" property.)
pub proof fn lemma_shortlex_compatible_concat(u: Word, v: Word, prefix: Word, suffix: Word)
    requires
        shortlex_lt(u, v),
    ensures
        shortlex_lt(prefix + u + suffix, prefix + v + suffix),
{
    let pu = prefix + u + suffix;
    let pv = prefix + v + suffix;

    if u.len() < v.len() {
        //  |prefix + u + suffix| < |prefix + v + suffix|
        assert(pu.len() < pv.len());
    } else {
        //  u.len() == v.len() && lex_lt(u, v)
        assert(pu.len() == pv.len());
        //  First: lex_lt_from(u + suffix, v + suffix, 0)
        lemma_lex_lt_from_append(u, v, suffix, 0);
        //  Then: lex_lt_from(prefix + (u+suffix), prefix + (v+suffix), prefix.len())
        lemma_lex_lt_from_prepend(u + suffix, v + suffix, prefix, 0);
        //  Reassociate
        assert((prefix + u + suffix) =~= (prefix + (u + suffix)));
        assert((prefix + v + suffix) =~= (prefix + (v + suffix)));
        //  The prefix is identical, so lower from prefix.len() to 0
        assert(forall|i: int| 0 <= i < prefix.len() as int ==> pu[i] == pv[i]) by {
            assert forall|i: int| 0 <= i < prefix.len() as int implies pu[i] == pv[i] by {
                assert(pu[i] == prefix[i]);
                assert(pv[i] == prefix[i]);
            }
        }
        lemma_lex_lt_from_lower(pu, pv, 0, prefix.len());
    }
}

///  If words agree on [from, to) and lex_lt_from holds at `to`, then it holds at `from`.
proof fn lemma_lex_lt_from_lower(w1: Word, w2: Word, from: nat, to: nat)
    requires
        w1.len() == w2.len(),
        from <= to,
        forall|i: int| from as int <= i < to as int ==> w1[i] == w2[i],
        lex_lt_from(w1, w2, to),
    ensures
        lex_lt_from(w1, w2, from),
    decreases to - from,
{
    if from == to {
    } else {
        //  w1[from] == w2[from], so symbol_ord equal
        assert(w1[from as int] == w2[from as int]);
        //  lex_lt_from(w1, w2, from) falls through to lex_lt_from(w1, w2, from + 1)
        lemma_lex_lt_from_lower(w1, w2, from + 1, to);
    }
}

//  ============================================================
//  Well-foundedness (via nat measure)
//  ============================================================

///  Shortlex rank: a nat that strictly decreases with shortlex_lt.
///  We use a simple encoding: (word_length, lex_rank) as a pair,
///  but for Verus decreases clauses, we just use the word length
///  as the primary measure since that's sufficient for KB
///  (all rules strictly decrease length, or same length with lex decrease).
///
///  For the general Newman's lemma, we use lexicographic decreases (len, lex_rank).

///  If shortlex_lt(w1, w2), then w1.len() <= w2.len().
pub proof fn lemma_shortlex_lt_len_bound(w1: Word, w2: Word)
    requires
        shortlex_lt(w1, w2),
    ensures
        w1.len() <= w2.len(),
{
}

///  Replacing a subword with a shortlex-smaller one gives a shortlex-smaller word.
///  This is the key lemma for showing that rewrite rules decrease words.
pub proof fn lemma_shortlex_subword_replace(
    w: Word,
    pos: int,
    old_len: nat,
    replacement: Word,
    old_word: Word,
)
    requires
        0 <= pos,
        pos + old_len <= w.len(),
        w.subrange(pos, pos + old_len as int) == old_word,
        shortlex_lt(replacement, old_word),
    ensures
        shortlex_lt(
            w.subrange(0, pos) + replacement + w.subrange(pos + old_len as int, w.len() as int),
            w,
        ),
{
    let prefix = w.subrange(0, pos);
    let suffix = w.subrange(pos + old_len as int, w.len() as int);
    let new_w = prefix + replacement + suffix;

    //  w =~= prefix + old_word + suffix
    assert(w =~= prefix + old_word + suffix) by {
        assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
        assert(w.subrange(pos, w.len() as int) =~=
            w.subrange(pos, pos + old_len as int) + w.subrange(pos + old_len as int, w.len() as int));
    }

    lemma_shortlex_compatible_concat(replacement, old_word, prefix, suffix);
}

} //  verus!
