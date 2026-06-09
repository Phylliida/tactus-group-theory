///  Infrastructure lemmas for Britton's lemma proofs.
///  Extracted from the old britton_proof.rs to allow removal of the failed proof attempt.
///  These are self-contained utility lemmas used by britton_via_tower.rs.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;

verus! {

///  word_valid is monotone: valid for n implies valid for n+1.
pub proof fn lemma_word_valid_monotone(w: Word, n: nat)
    requires
        word_valid(w, n),
    ensures
        word_valid(w, n + 1),
{
    assert forall|i: int| 0 <= i < w.len()
        implies symbol_valid(#[trigger] w[i], n + 1)
    by {
        assert(symbol_valid(w[i], n));
        match w[i] {
            Symbol::Gen(idx) => {},
            Symbol::Inv(idx) => {},
        }
    }
}

///  Subrange of a word_valid word is word_valid.
pub proof fn lemma_subrange_word_valid(w: Word, lo: int, hi: int, n: nat)
    requires
        word_valid(w, n),
        0 <= lo <= hi <= w.len(),
    ensures
        word_valid(w.subrange(lo, hi), n),
{
    let sub = w.subrange(lo, hi);
    assert forall|i: int| 0 <= i < sub.len()
        implies symbol_valid(#[trigger] sub[i], n)
    by {
        assert(sub[i] == w[lo + i]);
    }
}

///  Inverse of a valid symbol is valid.
proof fn lemma_inverse_symbol_valid(s: Symbol, n: nat)
    requires
        symbol_valid(s, n),
    ensures
        symbol_valid(inverse_symbol(s), n),
{
    match s {
        Symbol::Gen(idx) => {},
        Symbol::Inv(idx) => {},
    }
}

///  A relator from a valid presentation is word_valid, lifted to n+1.
proof fn lemma_relator_valid_lifted(p: Presentation, i: int)
    requires
        presentation_valid(p),
        0 <= i < p.relators.len(),
    ensures
        word_valid(p.relators[i], p.num_generators + 1),
{
    reveal(presentation_valid);
    lemma_word_valid_monotone(p.relators[i], p.num_generators);
}

///  The HNN presentation is valid (all relators are word_valid).
pub proof fn lemma_hnn_presentation_valid(data: HNNData)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(hnn_presentation(data)),
{
    reveal(presentation_valid);
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    assert forall|i: int| #![trigger hp.relators[i]]
        0 <= i < hp.relators.len()
        implies word_valid(hp.relators[i], hp.num_generators)
    by {
        let base_len = data.base.relators.len() as int;
        if i < base_len {
            assert(hp.relators[i] == data.base.relators[i]);
            lemma_relator_valid_lifted(data.base, i);
        } else {
            let k = (i - base_len);
            let (a_k, b_k) = data.associations[k];
            let t = stable_letter(data);
            let t_inv = stable_letter_inv(data);
            let r = Seq::new(1, |_j: int| t_inv) + a_k
                + Seq::new(1, |_j: int| t) + inverse_word(b_k);
            assert(hp.relators[i] =~= r);

            assert(word_valid(a_k, n));
            crate::word::lemma_inverse_word_valid(b_k, n);

            assert forall|j: int| 0 <= j < r.len()
                implies symbol_valid(#[trigger] r[j], n + 1)
            by {
                if j == 0 {
                } else if (j as int) < 1 + a_k.len() {
                    let aj = (j - 1) as int;
                    assert(r[j] == a_k[aj]);
                    match a_k[aj] { Symbol::Gen(idx) => {} Symbol::Inv(idx) => {} }
                } else if j == 1 + a_k.len() {
                } else {
                    let bj = (j - 2 - a_k.len()) as int;
                    let inv_bk = inverse_word(b_k);
                    assert(r[j] == inv_bk[bj]);
                    match inv_bk[bj] { Symbol::Gen(idx) => {} Symbol::Inv(idx) => {} }
                }
            }
        }
    }
}

///  A single derivation step preserves word_valid.
pub proof fn lemma_step_preserves_word_valid(
    data: HNNData, w: Word, step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators + 1),
        apply_step(hnn_presentation(data), w, step).is_some(),
    ensures
        word_valid(
            apply_step(hnn_presentation(data), w, step).unwrap(),
            data.base.num_generators + 1,
        ),
{
    let hp = hnn_presentation(data);
    let n = data.base.num_generators + 1;
    let result = apply_step(hp, w, step).unwrap();

    match step {
        DerivationStep::FreeReduce { position } => {
            let pos = position;
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos + 2, w.len() as int, n);
            crate::word::lemma_concat_word_valid(
                w.subrange(0, pos),
                w.subrange(pos + 2, w.len() as int), n);
            assert(result =~= w.subrange(0, pos) + w.subrange(pos + 2, w.len() as int));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pos = position;
            let pair = Seq::new(1, |_i: int| symbol)
                + Seq::new(1, |_i: int| inverse_symbol(symbol));
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos, w.len() as int, n);
            lemma_inverse_symbol_valid(symbol, n);
            assert(word_valid(pair, n)) by {
                assert forall|i: int| 0 <= i < pair.len()
                    implies symbol_valid(#[trigger] pair[i], n)
                by { if i == 0 {} else { assert(pair[1] == inverse_symbol(symbol)); } }
            }
            crate::word::lemma_concat_word_valid(w.subrange(0, pos), pair, n);
            crate::word::lemma_concat_word_valid(
                w.subrange(0, pos) + pair,
                w.subrange(pos, w.len() as int), n);
            assert(result =~=
                w.subrange(0, pos) + pair + w.subrange(pos, w.len() as int));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let pos = position;
            let r = get_relator(hp, relator_index, inverted);
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos, w.len() as int, n);
            lemma_hnn_presentation_valid(data);
            reveal(presentation_valid);
            let rel = hp.relators[relator_index as int];
            if inverted { crate::word::lemma_inverse_word_valid(rel, n); }
            crate::word::lemma_concat_word_valid(w.subrange(0, pos), r, n);
            crate::word::lemma_concat_word_valid(
                w.subrange(0, pos) + r,
                w.subrange(pos, w.len() as int), n);
            assert(result =~=
                w.subrange(0, pos) + r + w.subrange(pos, w.len() as int));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(hp, relator_index, inverted);
            let rlen = r.len();
            let pos = position;
            lemma_subrange_word_valid(w, 0, pos, n);
            lemma_subrange_word_valid(w, pos + rlen as int, w.len() as int, n);
            crate::word::lemma_concat_word_valid(
                w.subrange(0, pos),
                w.subrange(pos + rlen as int, w.len() as int), n);
            assert(result =~=
                w.subrange(0, pos) + w.subrange(pos + rlen as int, w.len() as int));
        },
    }
}

} //  verus!
