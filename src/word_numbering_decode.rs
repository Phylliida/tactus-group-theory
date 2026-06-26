// GAP-1 item-3b, brick B1 — the word-numbering DECODE bridge (machine-free).
//
// `docs/final-gate-axiom-removal-plan.md` §3.4 / §14.4.  Co-designed with Danielle (port 8051,
// 2026-06-26): item-3b's relator-set match splits into THREE machine-INDEPENDENT bricks, with the
// only machine content (`mm_in_H0 ⟺ declared`, = GAP-2) carried as a `requires` hypothesis (a sound
// conditional theorem — no verifier escape hatches).  This is brick B1, the "vacuum-sealed"
// combinatorial core: it shows the word-numbering map `w_c(c_base,n,m,·)` is a SURJECTION onto words
// over the c-block alphabet `{c₁,…,cₙ}^±`, by exhibiting an explicit section `decode_word`.
//
// `w_c(c_base,n,m,α)` reads α's base-m digits (each ∈ 1..=2n) into a word over the 2n-letter alphabet
//   digit j ↦ alphabet_letter(c_base,n,j) =  Gen(c_base+j-1)   (1 ≤ j ≤ n,  the c_j)
//                                            Inv(c_base+(j-n)-1) (n < j ≤ 2n, the c_{j-n}⁻¹),
// appending the LOWEST digit LAST (`w_{αm+i}(c) = w_α(c)·c_i`).  So the inverse reads the word's
// letters back to digits (`letter_digit`) and folds them Horner-style (`decode_word`).  The headline
// `lemma_decode_section`:  for any `w` whose every letter lives in the c-block `[c_base, c_base+n)`,
//   numbers_word(n,m,decode_word(c_base,n,m,w))   ∧   w_c(c_base,n,m,decode_word(c_base,n,m,w)) =~= w.
//
// Used by B2 to define the GAP-2 encoding `enc(a,b) := decode_word(re_index(u_a·u_b⁻¹))`, which makes
// Cohen's word-numbering bridge `w_{enc(a,b)}(c) = re_index(u_a·u_b⁻¹)` hold BY CONSTRUCTION.
//
// Routing-neutral / machine-free: depends only on `word_numbering` (itself self-contained on
// `word`/`symbol`).  Additive; reversible.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::word_numbering::{numbers_word, w_c, alphabet_letter, lemma_div_mod_step};

verus! {

// ----------------------------------------------------------------------------
// The c-block alphabet
// ----------------------------------------------------------------------------

/// `sym` is a letter of the c-block alphabet based at `c_base`: a `Gen`/`Inv` whose generator index
/// lies in `[c_base, c_base+n)` — i.e. some `c_i^{±1}` (`1 ≤ i ≤ n`).
pub open spec fn in_c_block(c_base: nat, n: nat, sym: Symbol) -> bool {
    c_base <= generator_index(sym) < c_base + n
}

/// `w` is a word over the c-block alphabet: every letter is some `c_i^{±1}`.
pub open spec fn c_alphabet_word(c_base: nat, n: nat, w: Word) -> bool {
    forall|k: int| 0 <= k < w.len() ==> in_c_block(c_base, n, #[trigger] w[k])
}

// ----------------------------------------------------------------------------
// The per-letter and whole-word decode (inverse of `alphabet_letter` / `w_c`)
// ----------------------------------------------------------------------------

/// The digit `j ∈ 1..=2n` of a c-block letter — inverse of `alphabet_letter(c_base,n,·)`:
///   Gen(g)  ↦  g - c_base + 1        ∈ 1..=n      (c_{g-c_base+1})
///   Inv(g)  ↦  g - c_base + 1 + n    ∈ n+1..=2n   (c_{g-c_base+1}⁻¹)
pub open spec fn letter_digit(c_base: nat, n: nat, sym: Symbol) -> nat {
    match sym {
        Symbol::Gen(g) => (g - c_base + 1) as nat,
        Symbol::Inv(g) => (g - c_base + 1 + n) as nat,
    }
}

/// The word-number of a c-block word — inverse of `w_c(c_base,n,m,·)`.  Since `w_c` appends the
/// lowest base-m digit last, decode folds Horner-style with the LAST letter as the lowest digit:
///   decode([]) = 0,   decode(w) = decode(w.drop_last())·m + letter_digit(w.last()).
pub open spec fn decode_word(c_base: nat, n: nat, m: nat, w: Word) -> nat
    decreases w.len()
{
    if w.len() == 0 {
        0
    } else {
        decode_word(c_base, n, m, w.drop_last()) * m + letter_digit(c_base, n, w.last())
    }
}

// ----------------------------------------------------------------------------
// Per-letter section: alphabet_letter ∘ letter_digit = id on the c-block alphabet
// ----------------------------------------------------------------------------

/// `letter_digit` is a section of `alphabet_letter` on the c-block: the digit it returns lies in
/// `1..=2n` and re-encodes to the original letter.
pub proof fn lemma_alphabet_letter_section(c_base: nat, n: nat, sym: Symbol)
    requires
        in_c_block(c_base, n, sym),
    ensures
        1 <= letter_digit(c_base, n, sym) <= 2 * n,
        alphabet_letter(c_base, n, letter_digit(c_base, n, sym)) == sym,
{
    match sym {
        Symbol::Gen(g) => {
            // generator_index(Gen(g)) = g, so c_base ≤ g < c_base+n.
            assert(c_base <= g < c_base + n);
            let j = letter_digit(c_base, n, sym);          // = g - c_base + 1
            assert(j == (g - c_base + 1) as nat);
            assert(1 <= j <= n);                            // g - c_base ∈ [0, n)
            // j ≤ n ⟹ alphabet_letter = Gen((c_base+j-1) as nat) = Gen(g).
            assert((c_base + j - 1) as nat == g);
        },
        Symbol::Inv(g) => {
            assert(c_base <= g < c_base + n);
            let j = letter_digit(c_base, n, sym);          // = (g - c_base + 1) + n
            assert(j == (g - c_base + 1 + n) as nat);
            assert(n < j <= 2 * n);                         // g - c_base + 1 ∈ [1, n]
            // j > n ⟹ alphabet_letter = Inv((c_base+(j-n)-1) as nat); j-n = g-c_base+1.
            assert((j - n) as nat == (g - c_base + 1) as nat);
            assert((c_base + (j - n) - 1) as nat == g);
        },
    }
}

// ----------------------------------------------------------------------------
// The headline: decode_word is a section of w_c on c-block words
// ----------------------------------------------------------------------------

/// **B1 — the decode bridge.**  Every word over the c-block alphabet is `w_α(c)` for the explicit
/// word-number `α = decode_word(…,w)`, and that `α` numbers a word (`numbers_word`).  I.e.
/// `w_c(c_base,n,m,·)` is a surjection onto c-block words with `decode_word` as a section.
pub proof fn lemma_decode_section(c_base: nat, n: nat, m: nat, w: Word)
    requires
        c_alphabet_word(c_base, n, w),
        2 * n < m,
    ensures
        numbers_word(n, m, decode_word(c_base, n, m, w)),
        w_c(c_base, n, m, decode_word(c_base, n, m, w)) =~= w,
    decreases w.len()
{
    if w.len() == 0 {
        assert(w =~= empty_word());
        // decode = 0 ⟹ numbers_word(n,m,0) = true and w_c(…,0) = empty_word().
        assert(decode_word(c_base, n, m, w) == 0);
    } else {
        let pref = w.drop_last();
        let last = w.last();
        // `pref` is also a c-block word (it is a prefix of `w`).
        assert(c_alphabet_word(c_base, n, pref)) by {
            assert forall|k: int| 0 <= k < pref.len() implies in_c_block(c_base, n, #[trigger] pref[k]) by {
                assert(pref[k] == w[k]);
            }
        }
        // `last` is in the c-block.
        assert(last == w[w.len() - 1]);
        assert(in_c_block(c_base, n, last));

        lemma_decode_section(c_base, n, m, pref);             // IH
        lemma_alphabet_letter_section(c_base, n, last);       // 1 ≤ i ≤ 2n, alphabet_letter(…,i)=last

        let a_pref = decode_word(c_base, n, m, pref);
        let i = letter_digit(c_base, n, last);
        let alpha = decode_word(c_base, n, m, w);
        assert(alpha == a_pref * m + i);

        // i < m (i ≤ 2n < m) and m > 1 (from 1 ≤ i ≤ 2n < m ⟹ 2n ≥ 1 ⟹ m > 2).
        assert(1 <= i <= 2 * n);
        assert(i < m);
        assert(m > 1);
        lemma_div_mod_step(a_pref, m, i);                     // alpha % m == i, alpha / m == a_pref
        assert(alpha % m == i);
        assert(alpha / m == a_pref);
        assert(alpha >= 1);                                   // i ≥ 1 ⟹ alpha ≥ 1

        // numbers_word(n,m,alpha) unfolds (alpha ≠ 0, m > 1) to
        //   1 ≤ alpha%m ≤ 2n  ∧  numbers_word(n,m,alpha/m) = numbers_word(n,m,a_pref) [IH].

        // w_c(n,m,alpha) unfolds to w_c(n,m,a_pref) + [alphabet_letter(c_base,n,i)].
        let appended = Seq::new(1, |_k: int| alphabet_letter(c_base, n, alpha % m));
        let tail = Seq::new(1, |_k: int| last);
        assert(w_c(c_base, n, m, alpha) =~= w_c(c_base, n, m, a_pref) + appended);
        // IH: w_c(n,m,a_pref) =~= pref;  section: alphabet_letter(c_base,n,i) == last.
        assert(appended =~= tail);
        assert(w_c(c_base, n, m, alpha) =~= pref + tail);
        // pref + [last] = w.drop_last() + [w.last()] =~= w.
        let glued = pref + tail;
        assert(w =~= glued) by {
            assert forall|k: int| #![trigger glued[k]]
                0 <= k < glued.len()
                implies w[k] == glued[k] by {
                if k < pref.len() {
                    assert(pref[k] == w[k]);
                } else {
                    assert(k == w.len() - 1);
                }
            }
        }
    }
}

} // verus!
