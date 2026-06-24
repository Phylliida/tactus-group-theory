// Layer 2 — Cohen §1 assembly, brick CS-4a′: the von-Dyck "homomorphism extends" tool over a
// PREDICATE target. `docs/cohen-cs4-architecture.md` §4.
//
// CS-4a gives the per-relator triviality `emb(col, pa_relator) ≡_{h2_pred} ε`; to USE it (CS-4c/d)
// we need the standard von-Dyck extension: an embedding that kills every relator of a FINITE source
// presentation respects all of its equivalences in a (here PREDICATE) target. This is a port of
// `lemma_emb_respects_source_equiv` (`machine_group.rs:3441`) keeping the SOURCE finite (so
// `apply_step`/`derivation_produces` are unchanged) and only the TARGET predicate.
//
// The arc is the finite proof verbatim with the target-equiv algebra swapped for the predicate
// closure algebra (`pred_presentation_lemmas.rs`). This module first builds the 4 missing predicate
// atoms (delete/insert a trivial middle; an embedded inverse pair / inverse word is trivial), then
// the per-step / per-derivation / top-level induction. Additive/reversible; no regression.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::{Presentation, DerivationStep, Derivation, apply_step, get_relator,
    presentation_valid, derivation_produces, derivation_valid, equiv_in_presentation,
    lemma_step_preserves_word_valid_pres};
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::{lemma_pred_equiv_concat_left, lemma_pred_equiv_concat_right,
    lemma_pred_word_inverse_left, lemma_pred_word_inverse_right};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_symbol_inverse,
    lemma_apply_embedding_inverse, lemma_apply_embedding_concat, lemma_apply_embedding_valid};

verus! {

// ----------------------------------------------------------------------------
// The 4 predicate atoms (mirror the finite `*_equiv_empty` / `emb_inverse_*` helpers)
// ----------------------------------------------------------------------------

/// **Delete a trivial middle.** `r ≡_p ε ⟹ prefix·r·suffix ≡_p prefix·suffix`. Port of
/// `lemma_delete_equiv_empty`.
pub proof fn lemma_pred_delete_equiv_empty(p: PredPresentation, prefix: Word, r: Word, suffix: Word)
    requires
        equiv_in_pred_presentation(p, r, empty_word()),
    ensures
        equiv_in_pred_presentation(p, concat(prefix, concat(r, suffix)), concat(prefix, suffix)),
{
    // r ≡ ε ⟹ concat(r, suffix) ≡ concat(ε, suffix) =~= suffix
    lemma_pred_equiv_concat_left(p, r, empty_word(), suffix);
    assert(concat(empty_word(), suffix) =~= suffix);
    // ⟹ concat(prefix, concat(r, suffix)) ≡ concat(prefix, suffix)
    lemma_pred_equiv_concat_right(p, prefix, concat(r, suffix), suffix);
}

/// **Insert a trivial middle.** `r ≡_p ε ⟹ prefix·suffix ≡_p prefix·r·suffix`. The symmetric of
/// `lemma_pred_delete_equiv_empty` (no validity hyp needed — predicate symmetry is unconditional).
pub proof fn lemma_pred_insert_equiv_empty(p: PredPresentation, prefix: Word, r: Word, suffix: Word)
    requires
        equiv_in_pred_presentation(p, r, empty_word()),
        pred_presentation_valid(p),
        word_valid(prefix, p.num_generators),
        word_valid(r, p.num_generators),
        word_valid(suffix, p.num_generators),
    ensures
        equiv_in_pred_presentation(p, concat(prefix, suffix), concat(prefix, concat(r, suffix))),
{
    lemma_pred_delete_equiv_empty(p, prefix, r, suffix);
    crate::word::lemma_concat_word_valid(r, suffix, p.num_generators);
    crate::word::lemma_concat_word_valid(prefix, concat(r, suffix), p.num_generators);
    lemma_pred_equiv_symmetric(p, concat(prefix, concat(r, suffix)), concat(prefix, suffix));
}

/// **An embedded inverse pair is trivial.** `emb(images, [s, s⁻¹]) ≡_p ε`. Port of
/// `lemma_emb_inverse_pair_trivial` (`m_sym + inverse_word(m_sym) ≡ ε` via `lemma_pred_word_inverse_right`).
pub proof fn lemma_emb_inverse_pair_trivial_pred(p: PredPresentation, images: Seq<Word>, s: Symbol)
    ensures
        equiv_in_pred_presentation(p, apply_embedding(images, seq![s, inverse_symbol(s)]), empty_word()),
{
    reveal_with_fuel(apply_embedding, 3);
    let s2 = inverse_symbol(s);
    let m_sym = apply_embedding_symbol(images, s);
    lemma_apply_embedding_symbol_inverse(images, s);   // emb_sym(s2) =~= inverse_word(m_sym)
    assert(seq![s, s2].drop_first() =~= seq![s2]);
    assert(seq![s2].drop_first() =~= empty_word());
    assert(apply_embedding(images, seq![s, s2]) =~= concat(m_sym, inverse_word(m_sym)));
    lemma_pred_word_inverse_right(p, m_sym);            // concat(m, m⁻¹) ≡ ε
}

/// **An embedded inverse word is trivial.** `emb(images, r) ≡_p ε ⟹ emb(images, r⁻¹) ≡_p ε`.
/// `emb(r⁻¹) =~= inverse_word(emb(r)) =: u⁻¹`; with `u ≡ ε`, `u⁻¹ ≡ u⁻¹·u ≡ u⁻¹·ε = u⁻¹` and
/// `u⁻¹·u ≡ ε` (`lemma_pred_word_inverse_left`), so `u⁻¹ ≡ ε`. (Routes through the left-inverse +
/// concat-right rather than a predicate `equiv_inverse`, which is not yet available.)
pub proof fn lemma_emb_inverse_word_trivial_pred(p: PredPresentation, images: Seq<Word>, r: Word)
    requires
        equiv_in_pred_presentation(p, apply_embedding(images, r), empty_word()),
        pred_presentation_valid(p),
        word_valid(apply_embedding(images, r), p.num_generators),
    ensures
        equiv_in_pred_presentation(p, apply_embedding(images, inverse_word(r)), empty_word()),
{
    let u = apply_embedding(images, r);
    lemma_apply_embedding_inverse(images, r);          // emb(inverse_word(r)) =~= inverse_word(u)
    lemma_pred_word_inverse_left(p, u);                // concat(inverse_word(u), u) ≡ ε
    lemma_pred_equiv_concat_right(p, inverse_word(u), u, empty_word());  // concat(inv(u),u) ≡ concat(inv(u),ε)
    assert(concat(inverse_word(u), empty_word()) =~= inverse_word(u));
    // inverse_word(u) ≡ concat(inv(u),u) ≡ ε
    crate::word::lemma_inverse_word_valid(u, p.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(u), u, p.num_generators);
    lemma_pred_equiv_symmetric(p, concat(inverse_word(u), u), inverse_word(u));
    lemma_pred_equiv_transitive(p, inverse_word(u), concat(inverse_word(u), u), empty_word());
}

// ----------------------------------------------------------------------------
// The induction: a finite-source derivation respects the embedding in a pred target
// ----------------------------------------------------------------------------

/// **Single finite step ⟹ pred-target embedding-equivalence.** Port of `lemma_emb_step_respects`
/// (`machine_group.rs:3290`); `src` stays a finite `Presentation` (so `apply_step`/`get_relator` are
/// unchanged), only `tgt` is predicate. Each step type splits the embedded word at the edit position
/// and deletes/inserts a trivial middle (an inverse pair for free ops; a respected relator image for
/// relator ops), using the predicate atoms above.
pub proof fn lemma_emb_step_respects_pred(
    src: Presentation, tgt: PredPresentation, images: Seq<Word>, w: Word, w2: Word, step: DerivationStep,
)
    requires
        apply_step(src, w, step) == Some(w2),
        src.num_generators == images.len(),
        word_valid(w, src.num_generators),
        presentation_valid(src),
        pred_presentation_valid(tgt),
        forall|i: int| 0 <= i < images.len() ==> word_valid(#[trigger] images[i], tgt.num_generators),
        forall|j: int| 0 <= j < src.relators.len()
            ==> equiv_in_pred_presentation(tgt, apply_embedding(images, #[trigger] src.relators[j]),
                empty_word()),
    ensures
        equiv_in_pred_presentation(tgt, apply_embedding(images, w2), apply_embedding(images, w)),
{
    let k = images.len();
    let tng = tgt.num_generators;
    reveal(presentation_valid);
    match step {
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            let pre = w.subrange(0, position);
            let suf = w.subrange(position, w.len() as int);
            assert(w2 == pre + pair + suf);
            assert(w =~= pre + suf);
            assert(pair =~= seq![symbol, inverse_symbol(symbol)]);
            lemma_emb_inverse_pair_trivial_pred(tgt, images, symbol);
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, pair);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_concat(images, pre + pair, suf);
            lemma_apply_embedding_concat(images, pre, pair);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w2) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w) =~= concat(ep, es));
            lemma_pred_delete_equiv_empty(tgt, ep, ec, es);
        },
        DerivationStep::FreeReduce { position } => {
            let pre = w.subrange(0, position);
            let suf = w.subrange(position + 2, w.len() as int);
            let pair = w.subrange(position, position + 2);
            assert(crate::reduction::has_cancellation_at(w, position));
            assert(w[position + 1] == inverse_symbol(w[position]));
            assert(pair =~= seq![w[position], inverse_symbol(w[position])]);
            assert(w =~= pre + pair + suf);
            assert(w2 == pre + suf);
            assert(word_valid(pre, k)) by { assert forall|i: int| 0 <= i < pre.len()
                implies symbol_valid(pre[i], k) by { assert(pre[i] == w[i]); } }
            assert(word_valid(suf, k)) by { assert forall|i: int| 0 <= i < suf.len()
                implies symbol_valid(suf[i], k) by { assert(suf[i] == w[position + 2 + i]); } }
            assert(word_valid(pair, k));
            lemma_emb_inverse_pair_trivial_pred(tgt, images, w[position]);
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, pair);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_valid(images, pre, tng);
            lemma_apply_embedding_valid(images, suf, tng);
            lemma_apply_embedding_valid(images, pair, tng);
            assert(ec =~= apply_embedding(images, seq![w[position], inverse_symbol(w[position])]));
            lemma_apply_embedding_concat(images, pre + pair, suf);
            lemma_apply_embedding_concat(images, pre, pair);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w2) =~= concat(ep, es));
            lemma_pred_insert_equiv_empty(tgt, ep, ec, es);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(src, relator_index, inverted);
            let pre = w.subrange(0, position);
            let suf = w.subrange(position, w.len() as int);
            assert(w2 == pre + r + suf);
            assert(w =~= pre + suf);
            assert(word_valid(src.relators[relator_index as int], src.num_generators));
            if inverted {
                lemma_apply_embedding_valid(images, src.relators[relator_index as int], tng);
                lemma_emb_inverse_word_trivial_pred(tgt, images, src.relators[relator_index as int]);
            }
            assert(equiv_in_pred_presentation(tgt, apply_embedding(images, r), empty_word()));
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, r);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_concat(images, pre + r, suf);
            lemma_apply_embedding_concat(images, pre, r);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w2) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w) =~= concat(ep, es));
            lemma_pred_delete_equiv_empty(tgt, ep, ec, es);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(src, relator_index, inverted);
            let rlen = r.len() as int;
            let pre = w.subrange(0, position);
            let suf = w.subrange(position + rlen, w.len() as int);
            assert(w.subrange(position, position + rlen) == r);
            assert(w =~= pre + r + suf);
            assert(w2 == pre + suf);
            assert(word_valid(src.relators[relator_index as int], src.num_generators));
            if inverted {
                crate::word::lemma_inverse_word_valid(src.relators[relator_index as int],
                    src.num_generators);
                lemma_apply_embedding_valid(images, src.relators[relator_index as int], tng);
                lemma_emb_inverse_word_trivial_pred(tgt, images, src.relators[relator_index as int]);
            }
            assert(equiv_in_pred_presentation(tgt, apply_embedding(images, r), empty_word()));
            assert(word_valid(r, k));
            assert(word_valid(pre, k)) by { assert forall|i: int| 0 <= i < pre.len()
                implies symbol_valid(pre[i], k) by { assert(pre[i] == w[i]); } }
            assert(word_valid(suf, k)) by { assert forall|i: int| 0 <= i < suf.len()
                implies symbol_valid(suf[i], k) by { assert(suf[i] == w[position + rlen + i]); } }
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, r);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_valid(images, pre, tng);
            lemma_apply_embedding_valid(images, suf, tng);
            lemma_apply_embedding_valid(images, r, tng);
            lemma_apply_embedding_concat(images, pre + r, suf);
            lemma_apply_embedding_concat(images, pre, r);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w2) =~= concat(ep, es));
            lemma_pred_insert_equiv_empty(tgt, ep, ec, es);
        },
    }
}

/// **A whole finite-source derivation respects the embedding in a pred target.** Port of
/// `lemma_emb_derivation_respects` — induction on `steps`, threading word-validity via
/// `lemma_step_preserves_word_valid_pres` and chaining with `lemma_pred_equiv_transitive`.
pub proof fn lemma_emb_derivation_respects_pred(
    src: Presentation, tgt: PredPresentation, images: Seq<Word>,
    steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        derivation_produces(src, steps, start) == Some(end),
        src.num_generators == images.len(),
        word_valid(start, src.num_generators),
        presentation_valid(src),
        pred_presentation_valid(tgt),
        forall|i: int| 0 <= i < images.len() ==> word_valid(#[trigger] images[i], tgt.num_generators),
        forall|j: int| 0 <= j < src.relators.len()
            ==> equiv_in_pred_presentation(tgt, apply_embedding(images, #[trigger] src.relators[j]),
                empty_word()),
    ensures
        equiv_in_pred_presentation(tgt, apply_embedding(images, end), apply_embedding(images, start)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(start == end);
        lemma_pred_equiv_refl(tgt, apply_embedding(images, start));
    } else {
        let first = steps.first();
        match apply_step(src, start, first) {
            Some(next) => {
                lemma_emb_step_respects_pred(src, tgt, images, start, next, first);
                lemma_step_preserves_word_valid_pres(src, start, first, next);
                lemma_emb_derivation_respects_pred(src, tgt, images, steps.drop_first(), next, end);
                lemma_pred_equiv_transitive(tgt, apply_embedding(images, end),
                    apply_embedding(images, next), apply_embedding(images, start));
            },
            None => {
                assert(false);
            },
        }
    }
}

/// **von-Dyck "homomorphism extends" over a predicate target.** `w1 ≡_{src} w2` (finite `src`) and
/// `images` kills every `src` relator in `tgt` ⟹ `emb(images, w1) ≡_{tgt} emb(images, w2)`. The
/// finite-source / predicate-target analog of `lemma_emb_respects_source_equiv` — the tool CS-4c/d
/// use to push a `pa_data`-equivalence into `h2_pred` via the CS-4a relator-trivialities.
pub proof fn lemma_emb_respects_source_equiv_pred(
    src: Presentation, tgt: PredPresentation, images: Seq<Word>, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(src, w1, w2),
        src.num_generators == images.len(),
        word_valid(w1, src.num_generators),
        word_valid(w2, src.num_generators),
        presentation_valid(src),
        pred_presentation_valid(tgt),
        forall|i: int| 0 <= i < images.len() ==> word_valid(#[trigger] images[i], tgt.num_generators),
        forall|j: int| 0 <= j < src.relators.len()
            ==> equiv_in_pred_presentation(tgt, apply_embedding(images, #[trigger] src.relators[j]),
                empty_word()),
    ensures
        equiv_in_pred_presentation(tgt, apply_embedding(images, w1), apply_embedding(images, w2)),
{
    let d = choose|d: Derivation| derivation_valid(src, d, w1, w2);
    lemma_emb_derivation_respects_pred(src, tgt, images, d.steps, w1, w2);
    lemma_apply_embedding_valid(images, w2, tgt.num_generators);
    lemma_pred_equiv_symmetric(tgt, apply_embedding(images, w2), apply_embedding(images, w1));
}

} // verus!
