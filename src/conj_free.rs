// Layer 0.5 crux (Miller §4.1, "previous discussion") — `{a⁻ⁱbaⁱ : i≥0}` is a FREE FAMILY in
// `F₂ = free_group(2)` (a = Gen(0), b = Gen(1)).  "The central b of each term survives free reduction."
//
// This is the foundational lemma of the Higman–Neumann–Neumann embedding of a countable group into a
// 2-generator group (`docs/higman-embedding-blueprint.md` §"Build order" step 2); the free bases
// `A = ⟨b, cᵢa⁻ⁱbaⁱ⟩` / `B = ⟨a, b⁻ⁱabⁱ⟩` of `L = C ⋆ F₂` generalize it.  It is representation-
// independent (pure `F₂`), so buildable before the infinitely-generated-`C` infra is decided.
//
// THE ARGUMENT (a fresh free-reduction / cancellation proof, the style `f_free.rs` avoids):
//   forward obligation: `equiv(F₂, φ(w), ε) ⟹ equiv(free_group(K), w, ε)`, via
//   (1) `w' = normal_form(w)`; reduce the goal to `w' = ε`;
//   (2) φ respects source equiv (`lemma_emb_respects_source_equiv`, vacuous for a free source) ⟹
//       `equiv(F₂, φ(w'), ε)`;
//   (3) the bridge (`free_word_problem.rs`) ⟹ `normal_form(φ(w')) = ε`;
//   (4) **the core "central b survives"**: `w'` reduced non-empty ⟹ `normal_form(φ(w')) ≠ ε`.
// THIS MODULE builds the counting infrastructure step (4) needs — `count1` (# of index-1 / b-symbols),
// with `count1(φ(w)) = |w|` (each `conj_word` carries exactly one b) — plus the family definitions and
// validity.  The core (4) (no reduction of a φ-image ever cancels a b ⟹ `count1(normal_form(φ(w')))
// = |w'| > 0`) is the remaining work; see the blueprint plan.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::symbol_power;

verus! {

// ----------------------------------------------------------------------------
// `count1` — the number of index-1 (b = Gen(1)/Inv(1)) symbols in a word.
// ----------------------------------------------------------------------------

/// The number of symbols with generator index 1 (the `b`-letters) in `w`.
pub open spec fn count1(w: Word) -> nat
    decreases w.len(),
{
    if w.len() == 0 {
        0
    } else {
        (if generator_index(w.first()) == 1 { 1nat } else { 0nat }) + count1(w.drop_first())
    }
}

/// `count1` of a single-symbol word.
pub proof fn lemma_count1_single(w: Word, s: Symbol)
    requires
        w.len() == 1,
        w[0] == s,
    ensures
        count1(w) == (if generator_index(s) == 1 { 1nat } else { 0nat }),
{
    assert(w.first() == s);
    assert(w.drop_first() =~= empty_word());
    assert(count1(w.drop_first()) == 0);
}

/// `count1` is additive over concatenation.
pub proof fn lemma_count1_concat(a: Word, b: Word)
    ensures
        count1(a + b) == count1(a) + count1(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        let first = a.first();
        assert((a + b).first() == first);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_count1_concat(a.drop_first(), b);
    }
}

/// `count1` is invariant under formal inverse (reversal + per-symbol Gen↔Inv preserves the index 1).
pub proof fn lemma_count1_inverse(w: Word)
    ensures
        count1(inverse_word(w)) == count1(w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        // inverse_word(w) = inverse_word(w.drop_first()) ++ [inverse_symbol(w.first())]  (by def).
        let first = w.first();
        let tail_inv = inverse_word(w.drop_first());
        let inv_first = Seq::new(1, |_i: int| inverse_symbol(first));
        assert(inverse_word(w) == tail_inv + inv_first);
        lemma_count1_concat(tail_inv, inv_first);
        lemma_count1_inverse(w.drop_first());
        // the appended symbol keeps its index: generator_index(inverse_symbol(s)) == generator_index(s).
        assert(generator_index(inverse_symbol(first)) == generator_index(first)) by {
            match first { Symbol::Gen(i) => {}, Symbol::Inv(i) => {} }
        }
        lemma_count1_single(inv_first, inverse_symbol(first));
        // and count1 of the original first symbol (a length-1 view).
        assert(count1(w) == (if generator_index(first) == 1 { 1nat } else { 0nat })
            + count1(w.drop_first()));
    }
}

/// A power of `a = Gen(0)` (or `a⁻¹ = Inv(0)`) contains no `b`-letters.
pub proof fn lemma_count1_a_power(s: Symbol, j: nat)
    requires
        generator_index(s) == 0,
    ensures
        count1(symbol_power(s, j)) == 0,
    decreases j,
{
    if j == 0 {
        assert(symbol_power(s, j) =~= empty_word());
    } else {
        let sp = symbol_power(s, j);
        assert(sp.first() == s);
        assert(sp.drop_first() =~= symbol_power(s, (j - 1) as nat));
        lemma_count1_a_power(s, (j - 1) as nat);
    }
}

// ----------------------------------------------------------------------------
// The conjugate family `{a⁻ⁱbaⁱ}` and its `count1`.
// ----------------------------------------------------------------------------

/// `conj_word(i) = a⁻ⁱ · b · aⁱ = symbol_power(Inv(0),i) ++ [Gen(1)] ++ symbol_power(Gen(0),i)`.
pub open spec fn conj_word(i: nat) -> Word {
    symbol_power(Symbol::Inv(0), i) + seq![Symbol::Gen(1)] + symbol_power(Symbol::Gen(0), i)
}

/// The family `{a⁻ⁱbaⁱ : 0 ≤ i < k}` as a `Seq<Word>` (the image list of the free-family embedding).
pub open spec fn conj_family(k: nat) -> Seq<Word> {
    Seq::new(k, |i: int| conj_word(i as nat))
}

/// Each `conj_word(i)` is a valid `F₂`-word (only `a = Gen(0)`, `b = Gen(1)`).
pub proof fn lemma_conj_word_valid(i: nat)
    ensures
        word_valid(conj_word(i), 2),
{
    let cw = conj_word(i);
    let pre = symbol_power(Symbol::Inv(0), i);
    let post = symbol_power(Symbol::Gen(0), i);
    assert(cw =~= pre + seq![Symbol::Gen(1)] + post);
    assert forall|j: int| 0 <= j < cw.len() implies symbol_valid(#[trigger] cw[j], 2) by {
        // every symbol is Inv(0), Gen(1), or Gen(0): index < 2.
        let s = cw[j];
        if j < pre.len() {
            assert(s == pre[j]);
            assert(pre[j] == Symbol::Inv(0));
        } else if j == pre.len() {
            assert(s == Symbol::Gen(1));
        } else {
            assert(s == post[j - pre.len() - 1]);
            assert(post[j - pre.len() - 1] == Symbol::Gen(0));
        }
    }
}

/// Each `conj_word(i)` has exactly one `b`-letter: `count1(conj_word(i)) == 1`.
pub proof fn lemma_count1_conj_word(i: nat)
    ensures
        count1(conj_word(i)) == 1,
{
    let pre = symbol_power(Symbol::Inv(0), i);
    let post = symbol_power(Symbol::Gen(0), i);
    lemma_count1_a_power(Symbol::Inv(0), i);              // count1(pre) == 0
    lemma_count1_a_power(Symbol::Gen(0), i);              // count1(post) == 0
    lemma_count1_concat(pre, seq![Symbol::Gen(1)]);       // count1(pre ++ [b]) == 0 + 1
    lemma_count1_concat(pre + seq![Symbol::Gen(1)], post);// + 0
    assert(conj_word(i) == pre + seq![Symbol::Gen(1)] + post);
    lemma_count1_single(seq![Symbol::Gen(1)], Symbol::Gen(1));   // count1([b]) == 1
}

/// **The counting lemma:** the embedding of a `K`-letter word under `conj_family` has exactly `|w|`
/// `b`-letters — `count1(apply_embedding(conj_family(k), w)) == w.len()`.  (Each source letter
/// contributes one `conj_word`, hence one `b`; `a`-powers and inverses carry no extra `b`.)  This is
/// what makes the core "central b survives" yield NON-EMPTINESS: the reduced image keeps all `|w|` b's.
pub proof fn lemma_count1_emb(k: nat, w: Word)
    requires
        word_valid(w, k),
    ensures
        count1(crate::benign::apply_embedding(conj_family(k), w)) == w.len(),
    decreases w.len(),
{
    let fam = conj_family(k);
    if w.len() == 0 {
        assert(crate::benign::apply_embedding(fam, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, k)) by { assert(w[0] == s); }
        assert(word_valid(rest, k)) by {
            assert forall|j: int| 0 <= j < rest.len() implies symbol_valid(#[trigger] rest[j], k) by {
                assert(rest[j] == w[j + 1]);
            }
        }
        let head = crate::benign::apply_embedding_symbol(fam, s);
        // head has exactly one b: it is conj_word(idx) or its inverse.
        let idx = generator_index(s);
        assert(idx < k);
        assert(fam[idx as int] == conj_word(idx));
        lemma_count1_conj_word(idx);
        assert(count1(head) == 1) by {
            match s {
                Symbol::Gen(i) => { assert(head == fam[i as int]); },
                Symbol::Inv(i) => {
                    assert(head == inverse_word(fam[i as int]));
                    lemma_count1_inverse(fam[i as int]);
                },
            }
        }
        // apply_embedding(fam, w) = concat(head, apply_embedding(fam, rest)).
        assert(crate::benign::apply_embedding(fam, w)
            =~= head + crate::benign::apply_embedding(fam, rest));
        lemma_count1_concat(head, crate::benign::apply_embedding(fam, rest));
        lemma_count1_emb(k, rest);
    }
}

} // verus!
