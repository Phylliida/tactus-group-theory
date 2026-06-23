// Layer 0.5 (Miller §4.1) — the SECOND free basis: `{b⁻ⁱabⁱ : 0 ≤ i < k}` is FREE in `F₂`.
//
// Miller's Higman–Neumann–Neumann embedding of a countable group into a 2-generator group uses TWO
// free bases of `L = C ⋆ F₂` (`docs/higman-embedding-blueprint.md` §"Build order" step 2):
//
//     A = ⟨b, cᵢ a⁻ⁱ b aⁱ⟩          B = ⟨a, b⁻ⁱ a bⁱ⟩
//
// The `F₂`-part of `A` is the already-banked `conj_free_core::lemma_conj_family_free`
// (`{a⁻ⁱbaⁱ}` free, 34/0).  THIS module supplies the `F₂`-part of `B`: `{b⁻ⁱabⁱ}` free.
//
// `b⁻ⁱabⁱ` is literally `a⁻ⁱbaⁱ` with the generators `a = Gen(0)` and `b = Gen(1)` SWAPPED.  The
// swap `a↔b` is an (involutive) automorphism of `F₂`, and applying a group automorphism to each
// member of a free family preserves freeness — so we get `{b⁻ⁱabⁱ}` free as the IMAGE of the done
// `{a⁻ⁱbaⁱ}` lemma, with NO re-derivation of the net-exponent / "central letter survives" argument.
//
// Both bases are representation-independent (pure `F₂`), so buildable before the
// infinitely-generated-`C` representation decision (the standing Layer 0.5 blocker).
//
// The swap is realized as an `apply_embedding` image list `swap_emb = [[b], [a]]` (`Gen(0)↦[b]`,
// `Gen(1)↦[a]`), reusing the `benign`/`free_basis` embedding machinery.  The transfer:
//   `apply_embedding(conj_family_b, w) ≡_{F₂} ε`
//     =  apply_embedding(swap_emb, apply_embedding(conj_family, w)) ≡ ε        (compose)
//     ⟹ apply_embedding(conj_family, w) ≡ ε                                    (swap is an iso)
//     ⟹ w ≡_{free(k)} ε                                                        (A-basis is free).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::machine_group::{symbol_power, lemma_emb_respects_source_equiv};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat,
    lemma_apply_embedding_valid};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::f_free::is_free_family;
use crate::h3_ii::{compose_embeddings, lemma_apply_embedding_compose};
use crate::conj_free::{conj_word, conj_family, lemma_conj_word_valid};
use crate::conj_free_core::lemma_conj_family_free;

verus! {

// ----------------------------------------------------------------------------
// The swap embedding `a ↔ b` and the explicit B-basis words.
// ----------------------------------------------------------------------------

/// The generator swap on `{0,1}`: `0 ↦ 1`, `1 ↦ 0` (and anything else fixed — only `0,1` matter).
pub open spec fn swap_idx(i: nat) -> nat {
    if i == 0 { 1 } else { 0 }
}

/// The per-symbol swap: `Gen(i) ↦ Gen(swap_idx i)`, `Inv(i) ↦ Inv(swap_idx i)`.
pub open spec fn swap_symbol(s: Symbol) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Gen(swap_idx(i)),
        Symbol::Inv(i) => Symbol::Inv(swap_idx(i)),
    }
}

/// The swap as an `apply_embedding` image list: `Gen(0) ↦ [b=Gen(1)]`, `Gen(1) ↦ [a=Gen(0)]`.
pub open spec fn swap_emb() -> Seq<Word> {
    seq![ seq![Symbol::Gen(1)], seq![Symbol::Gen(0)] ]
}

/// `conj_word_b(i) = b⁻ⁱ · a · bⁱ = Inv(1)ⁱ ++ [Gen(0)] ++ Gen(1)ⁱ`.
pub open spec fn conj_word_b(i: nat) -> Word {
    symbol_power(Symbol::Inv(1), i) + seq![Symbol::Gen(0)] + symbol_power(Symbol::Gen(1), i)
}

/// The B-basis family `{b⁻ⁱabⁱ : 0 ≤ i < k}` as a `Seq<Word>`.
pub open spec fn conj_family_b(k: nat) -> Seq<Word> {
    Seq::new(k, |i: int| conj_word_b(i as nat))
}

// ----------------------------------------------------------------------------
// Single-symbol helpers (unfold `inverse_word` / `apply_embedding` once).
// ----------------------------------------------------------------------------

/// `inverse_word([s]) = [inverse_symbol(s)]`.
proof fn lemma_inverse_single(s: Symbol)
    ensures inverse_word(seq![s]) =~= seq![inverse_symbol(s)],
{
    let w: Word = seq![s];
    assert(w.first() == s);
    assert(w.drop_first() =~= empty_word());
    assert(inverse_word(w.drop_first()) =~= empty_word());
    assert(inverse_word(w) =~= inverse_word(w.drop_first()) + Seq::new(1, |_i: int| inverse_symbol(s)));
}

/// `apply_embedding(images, [s]) = apply_embedding_symbol(images, s)`.
proof fn lemma_apply_embedding_single(images: Seq<Word>, s: Symbol)
    ensures apply_embedding(images, seq![s]) =~= apply_embedding_symbol(images, s),
{
    let w: Word = seq![s];
    assert(w.first() == s);
    assert(w.drop_first() =~= empty_word());
    assert(apply_embedding(images, w.drop_first()) =~= empty_word());
}

// ----------------------------------------------------------------------------
// `swap_emb` basics: length, validity, per-symbol action.
// ----------------------------------------------------------------------------

/// `swap_emb` has the two images `[Gen(1)]` and `[Gen(0)]`, both valid `F₂`-words.
pub proof fn lemma_swap_emb_images_valid()
    ensures
        swap_emb().len() == 2,
        forall|i: int| 0 <= i < 2 ==> word_valid(#[trigger] swap_emb()[i], 2),
{
    assert(swap_emb()[0] =~= seq![Symbol::Gen(1)]);
    assert(swap_emb()[1] =~= seq![Symbol::Gen(0)]);
    assert forall|i: int| 0 <= i < 2 implies word_valid(#[trigger] swap_emb()[i], 2) by {
        if i == 0 {
            assert(swap_emb()[0][0] == Symbol::Gen(1));
        } else {
            assert(swap_emb()[1][0] == Symbol::Gen(0));
        }
    }
}

/// `swap_idx` is its own inverse on `{0,1}`.
pub proof fn lemma_swap_idx_involution(i: nat)
    requires i < 2,
    ensures swap_idx(swap_idx(i)) == i,
{ }

/// `swap_symbol` is its own inverse on `F₂`-symbols.
pub proof fn lemma_swap_symbol_involution(s: Symbol)
    requires symbol_valid(s, 2),
    ensures swap_symbol(swap_symbol(s)) == s,
{
    match s {
        Symbol::Gen(i) => { assert(i < 2); lemma_swap_idx_involution(i); }
        Symbol::Inv(i) => { assert(i < 2); lemma_swap_idx_involution(i); }
    }
}

/// The single-symbol action: `apply_embedding_symbol(swap_emb, s) = [swap_symbol(s)]`.
pub proof fn lemma_swap_emb_symbol(s: Symbol)
    requires symbol_valid(s, 2),
    ensures apply_embedding_symbol(swap_emb(), s) =~= seq![swap_symbol(s)],
{
    match s {
        Symbol::Gen(i) => {
            assert(i < 2);
            if i == 0 {
                assert(apply_embedding_symbol(swap_emb(), s) == swap_emb()[0]);
                assert(swap_emb()[0] =~= seq![Symbol::Gen(1)]);
            } else {
                assert(i == 1);
                assert(apply_embedding_symbol(swap_emb(), s) == swap_emb()[1]);
                assert(swap_emb()[1] =~= seq![Symbol::Gen(0)]);
            }
        }
        Symbol::Inv(i) => {
            assert(i < 2);
            // apply_embedding_symbol(swap_emb, Inv(i)) = inverse_word(swap_emb[i]).
            let img = swap_emb()[i as int];
            assert(apply_embedding_symbol(swap_emb(), s) == inverse_word(img));
            if i == 0 {
                assert(img =~= seq![Symbol::Gen(1)]);
                lemma_inverse_single(Symbol::Gen(1));   // inverse_word([Gen(1)]) = [Inv(1)]
                assert(inverse_word(img) =~= seq![Symbol::Inv(1)]);
            } else {
                assert(i == 1);
                assert(img =~= seq![Symbol::Gen(0)]);
                lemma_inverse_single(Symbol::Gen(0));   // inverse_word([Gen(0)]) = [Inv(0)]
                assert(inverse_word(img) =~= seq![Symbol::Inv(0)]);
            }
        }
    }
}

/// Applying `swap_emb` to a length-`i` power `sⁱ` gives `(swap_symbol s)ⁱ`.
pub proof fn lemma_swap_symbol_power(s: Symbol, i: nat)
    requires symbol_valid(s, 2),
    ensures apply_embedding(swap_emb(), symbol_power(s, i)) =~= symbol_power(swap_symbol(s), i),
    decreases i,
{
    let t = swap_symbol(s);
    if i == 0 {
        assert(symbol_power(s, i) =~= empty_word());
        assert(apply_embedding(swap_emb(), empty_word()) =~= empty_word());
        assert(symbol_power(t, 0nat) =~= empty_word());
    } else {
        let sp = symbol_power(s, i);
        assert(sp.first() == s);
        assert(sp.drop_first() =~= symbol_power(s, (i - 1) as nat));
        // apply_embedding(swap_emb, sp) = [swap_symbol s] ++ apply_embedding(swap_emb, sp.drop_first()).
        lemma_swap_emb_symbol(s);
        lemma_swap_symbol_power(s, (i - 1) as nat);
        // [t] ++ symbol_power(t, i-1) = symbol_power(t, i).
        assert(seq![t] + symbol_power(t, (i - 1) as nat) =~= symbol_power(t, i));
    }
}

// ----------------------------------------------------------------------------
// `swap_emb(conj_word(i)) = conj_word_b(i)`, and the family-level compose form.
// ----------------------------------------------------------------------------

/// `apply_embedding(swap_emb, a⁻ⁱbaⁱ) = b⁻ⁱabⁱ`.
pub proof fn lemma_conj_word_b_eq(i: nat)
    ensures apply_embedding(swap_emb(), conj_word(i)) =~= conj_word_b(i),
{
    let pre = symbol_power(Symbol::Inv(0), i);   // a⁻ⁱ
    let mid = seq![Symbol::Gen(1)];              // b
    let post = symbol_power(Symbol::Gen(0), i);  // aⁱ
    assert(conj_word(i) =~= pre + mid + post);
    // Distribute apply_embedding over the two concatenations.
    lemma_apply_embedding_concat(swap_emb(), pre + mid, post);
    lemma_apply_embedding_concat(swap_emb(), pre, mid);
    // The three pieces map to b⁻ⁱ, a, bⁱ.
    assert(symbol_valid(Symbol::Inv(0), 2));
    assert(symbol_valid(Symbol::Gen(0), 2));
    lemma_swap_symbol_power(Symbol::Inv(0), i);  // a⁻ⁱ ↦ b⁻ⁱ = Inv(1)ⁱ
    lemma_swap_symbol_power(Symbol::Gen(0), i);  // aⁱ  ↦ bⁱ  = Gen(1)ⁱ
    assert(swap_symbol(Symbol::Inv(0)) == Symbol::Inv(1));
    assert(swap_symbol(Symbol::Gen(0)) == Symbol::Gen(1));
    // b ↦ a:  apply_embedding(swap_emb, [Gen(1)]) = [Gen(0)].
    assert(apply_embedding(swap_emb(), mid) =~= seq![Symbol::Gen(0)]) by {
        assert(mid =~= seq![Symbol::Gen(1)]);
        lemma_apply_embedding_single(swap_emb(), Symbol::Gen(1));
        lemma_swap_emb_symbol(Symbol::Gen(1));
        assert(swap_symbol(Symbol::Gen(1)) == Symbol::Gen(0));
    }
    assert(apply_embedding(swap_emb(), conj_word(i))
        =~= symbol_power(Symbol::Inv(1), i) + seq![Symbol::Gen(0)] + symbol_power(Symbol::Gen(1), i));
}

/// The B-basis family is the swap-image of the A-basis family (compose form).
pub proof fn lemma_conj_family_b_is_compose(k: nat)
    ensures conj_family_b(k) =~= compose_embeddings(swap_emb(), conj_family(k)),
{
    let lhs = conj_family_b(k);
    let rhs = compose_embeddings(swap_emb(), conj_family(k));
    assert(conj_family(k).len() == k);
    assert(rhs.len() == k);
    assert(lhs.len() == k);
    assert forall|i: int| 0 <= i < k implies lhs[i] =~= rhs[i] by {
        // rhs[i] = apply_embedding(swap_emb, conj_family(k)[i]) = apply_embedding(swap_emb, conj_word(i)).
        assert(conj_family(k)[i] == conj_word(i as nat));
        lemma_conj_word_b_eq(i as nat);
        assert(lhs[i] == conj_word_b(i as nat));
    }
    assert(lhs =~= rhs);
}

// ----------------------------------------------------------------------------
// `swap_emb` is an involutive automorphism of `F₂`.
// ----------------------------------------------------------------------------

/// `swap_emb` preserves `F₂`-triviality (it is a free-group endomorphism: relators are vacuous).
pub proof fn lemma_swap_preserves_triv(w: Word)
    requires
        word_valid(w, 2),
        equiv_in_presentation(free_group(2), w, empty_word()),
    ensures
        equiv_in_presentation(free_group(2), apply_embedding(swap_emb(), w), empty_word()),
{
    lemma_swap_emb_images_valid();
    lemma_free_group_valid(2);
    assert(word_valid(empty_word(), 2));
    assert(free_group(2).relators.len() == 0);
    lemma_emb_respects_source_equiv(free_group(2), free_group(2), swap_emb(), w, empty_word());
    // apply_embedding(swap_emb, ε) = ε, so the target RHS collapses.
    assert(apply_embedding(swap_emb(), empty_word()) =~= empty_word());
}

/// `swap_emb ∘ swap_emb = id` on valid `F₂`-words.
pub proof fn lemma_swap_involution(w: Word)
    requires word_valid(w, 2),
    ensures apply_embedding(swap_emb(), apply_embedding(swap_emb(), w)) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_embedding(swap_emb(), w) =~= empty_word());
        assert(apply_embedding(swap_emb(), empty_word()) =~= empty_word());
    } else {
        let first = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(first, 2)) by { assert(first == w[0]); }
        assert(word_valid(rest, 2)) by {
            assert forall|j: int| 0 <= j < rest.len() implies symbol_valid(#[trigger] rest[j], 2) by {
                assert(rest[j] == w[j + 1]);
            }
        }
        let xw = apply_embedding_symbol(swap_emb(), first);
        let yw = apply_embedding(swap_emb(), rest);
        // apply_embedding(swap_emb, w) = xw ++ yw.
        assert(apply_embedding(swap_emb(), w) =~= xw + yw);
        // Apply swap a second time, distributing over the concatenation.
        lemma_apply_embedding_concat(swap_emb(), xw, yw);
        // Inner (rest) by IH.
        lemma_swap_involution(rest);
        // Inner (the first symbol): swap(swap([first])) = [first].
        lemma_swap_emb_symbol(first);                                   // xw = [swap_symbol first]
        assert(symbol_valid(swap_symbol(first), 2));
        assert(apply_embedding(swap_emb(), xw) =~= seq![first]) by {
            lemma_swap_emb_symbol(first);
            assert(xw =~= seq![swap_symbol(first)]);
            lemma_apply_embedding_single(swap_emb(), swap_symbol(first)); // swap([swap first]) = swap_sym(swap first)
            assert(symbol_valid(swap_symbol(first), 2));
            lemma_swap_emb_symbol(swap_symbol(first));                    // = [swap swap first]
            lemma_swap_symbol_involution(first);                         // swap swap first = first
        }
        assert(apply_embedding(swap_emb(), apply_embedding(swap_emb(), w)) =~= seq![first] + rest);
        assert(seq![first] + rest =~= w);
    }
}

// ----------------------------------------------------------------------------
// THE B-BASIS FREE-FAMILY LEMMA.
// ----------------------------------------------------------------------------

/// **THE SECOND FREE-FAMILY LEMMA (Miller §4.1).**  `conj_family_b(k) = {b⁻ⁱabⁱ : 0 ≤ i < k}` is a
/// FREE family in `F₂ = free_group(2)`.  The `F₂`-part of Miller's `B = ⟨a, b⁻ⁱabⁱ⟩`; obtained as
/// the swap-automorphism image of the A-basis `conj_free_core::lemma_conj_family_free`.
pub proof fn lemma_conj_family_b_free(k: nat)
    ensures
        is_free_family(free_group(2), conj_family_b(k)),
{
    assert(free_group(2).num_generators == 2);
    assert(conj_family_b(k).len() == k);
    assert(conj_family(k).len() == k);

    // Clause 1: each B-basis word is a valid F₂-word.
    assert forall|i: int| 0 <= i < conj_family_b(k).len()
        implies word_valid(#[trigger] conj_family_b(k)[i], 2) by {
        let cw = conj_word_b(i as nat);
        assert(conj_family_b(k)[i] == cw);
        let n = i as nat;
        assert(cw =~= symbol_power(Symbol::Inv(1), n) + seq![Symbol::Gen(0)]
            + symbol_power(Symbol::Gen(1), n));
        assert forall|j: int| 0 <= j < cw.len() implies symbol_valid(#[trigger] cw[j], 2) by {
            // Inv(1) / Gen(0) / Gen(1) all have generator index < 2.
            if j < n {
                assert(cw[j] == Symbol::Inv(1));
            } else if j == n {
                assert(cw[j] == Symbol::Gen(0));
            } else {
                assert(cw[j] == Symbol::Gen(1));
            }
        }
    }

    // Clause 2: apply_embedding(conj_family_b, w) ≡ ε  ⟹  w ≡_{free(k)} ε.
    assert forall|w: Word| (#[trigger] word_valid(w, conj_family_b(k).len())
        && equiv_in_presentation(free_group(2), apply_embedding(conj_family_b(k), w), empty_word()))
        implies equiv_in_presentation(free_group(k), w, empty_word()) by {
        assert(word_valid(w, k));

        // (a) apply_embedding(conj_family_b, w) = swap_emb(apply_embedding(conj_family, w)).
        lemma_conj_family_b_is_compose(k);
        assert(apply_embedding(conj_family_b(k), w)
            =~= apply_embedding(compose_embeddings(swap_emb(), conj_family(k)), w));
        lemma_apply_embedding_compose(swap_emb(), conj_family(k), w);
        let c = apply_embedding(conj_family(k), w);
        assert(apply_embedding(swap_emb(), c) =~= apply_embedding(conj_family_b(k), w));
        assert(equiv_in_presentation(free_group(2), apply_embedding(swap_emb(), c), empty_word()));

        // c is a valid F₂-word (each A-basis image is).
        assert forall|i: int| 0 <= i < conj_family(k).len()
            implies word_valid(#[trigger] conj_family(k)[i], 2) by {
            assert(conj_family(k)[i] == conj_word(i as nat));
            lemma_conj_word_valid(i as nat);
        }
        lemma_apply_embedding_valid(conj_family(k), w, 2);
        assert(word_valid(c, 2));

        // (b) swap is an iso ⟹ c ≡ ε.
        lemma_swap_emb_images_valid();
        lemma_apply_embedding_valid(swap_emb(), c, 2);          // word_valid(swap(c), 2)
        lemma_swap_preserves_triv(apply_embedding(swap_emb(), c));
        lemma_swap_involution(c);
        assert(equiv_in_presentation(free_group(2), c, empty_word()));

        // (c) the A-basis is free ⟹ w ≡_{free(k)} ε.
        lemma_conj_family_free(k);
        assert(conj_family(k).len() == k);
        // is_free_family clause-2 instantiated at w.
        assert(equiv_in_presentation(free_group(k), w, empty_word()));
    }
}

} // verus!
