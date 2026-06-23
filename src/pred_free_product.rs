use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::*;
//  Word-level shift machinery is relator-agnostic ⟹ REUSED verbatim from the
//  finite free_product module (these take no Presentation; pure Word ops).
use crate::free_product::{
    shift_symbol, shift_word,
    lemma_shift_word_len, lemma_shift_preserves_cancellation, lemma_shift_reduce_at,
    lemma_shift_inverse_word,
};

verus! {

//  ============================================================
//  FORK-A brick 3 — predicate-base free products (2026-06-23).
//
//  Predicate-base analog of `free_product.rs`, over `PredPresentation`.  This
//  is the layer that introduces the predicate `shift` named in
//  `docs/cohen-faithfulness-primary-source.md` §4 step 2 / §4-probe step 1.
//
//  Key economy (primary-source §7c, confirmed in code): the WORD-LEVEL shift
//  machinery (`shift_word`, `shift_symbol`, and the six shift-preservation
//  lemmas) is relator-agnostic, so it is REUSED verbatim from the finite
//  `free_product` module — nothing to re-port there.  Only the relator SET
//  changes: the right factor's relator predicate, lifted into the product, is
//  the SHIFTED predicate `Q(w) := ∃ w0. P₂(w0) ∧ w == shift_word(w0, offset)`.
//
//  This brick ports the construction + the FORWARD embeddings (left/right embed
//  into the free product), the relator-set-agnostic directions.  Kept separate
//  from finite `free_product` (reversible, zero regression).
//  ============================================================

///  The shifted relator predicate: `w` is a shift (by `offset`) of some word
///  accepted by `pred`.  The predicate-base analog of `shift_relators`.
pub open spec fn shifted_pred(pred: spec_fn(Word) -> bool, offset: nat, w: Word) -> bool {
    exists|w0: Word| #![trigger shift_word(w0, offset)] pred(w0) && w == shift_word(w0, offset)
}

///  The free-product relator predicate: a left (p1) relator, or a shifted
///  right (p2) relator.
pub open spec fn free_product_pred_relators(p1: PredPresentation, p2: PredPresentation, w: Word) -> bool {
    (p1.relators)(w) || shifted_pred(p2.relators, p1.num_generators, w)
}

///  The free product of two predicate presentations.
///  Generators: p1's (0..n1-1) and p2's (n1..n1+n2-1).
///  Relators: p1's relators, or p2's relators shifted up by n1.
pub open spec fn free_product_pred(p1: PredPresentation, p2: PredPresentation) -> PredPresentation {
    PredPresentation {
        num_generators: (p1.num_generators + p2.num_generators) as nat,
        relators: |w: Word| free_product_pred_relators(p1, p2, w),
    }
}

///  symbol_valid is monotone in the bound.
pub proof fn lemma_symbol_valid_mono(s: Symbol, n: nat, m: nat)
    requires
        symbol_valid(s, n),
        n <= m,
    ensures
        symbol_valid(s, m),
{
}

//  ============================================================
//  Left embedding (relator-set-agnostic, like the finite version).
//  ============================================================

///  A derivation step valid in p1 is valid in free_product_pred(p1, p2).
proof fn lemma_step_valid_in_fp_pred_left(
    p1: PredPresentation, p2: PredPresentation,
    w: Word, step: PredDerivationStep, w_prime: Word,
)
    requires
        apply_step_pred(p1, w, step) == Some(w_prime),
    ensures
        apply_step_pred(free_product_pred(p1, p2), w, step) == Some(w_prime),
{
    let fp = free_product_pred(p1, p2);
    match step {
        PredDerivationStep::FreeReduce { position } => {},
        PredDerivationStep::FreeExpand { position, symbol } => {
            //  symbol_valid(symbol, p1.num_generators) held ⟹ valid for fp's larger bound
            assert(symbol_valid(symbol, p1.num_generators));
            lemma_symbol_valid_mono(symbol, p1.num_generators, fp.num_generators);
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            assert((p1.relators)(relator));
            assert(free_product_pred_relators(p1, p2, relator));
            assert((fp.relators)(relator));
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert((p1.relators)(relator));
            assert(free_product_pred_relators(p1, p2, relator));
            assert((fp.relators)(relator));
        },
    }
}

///  A derivation valid in p1 is valid in free_product_pred(p1, p2).
proof fn lemma_derivation_valid_in_fp_pred_left(
    p1: PredPresentation, p2: PredPresentation,
    steps: Seq<PredDerivationStep>, w1: Word, w2: Word,
)
    requires
        pred_derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        pred_derivation_produces(free_product_pred(p1, p2), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step_pred(p1, w1, step).unwrap();
        lemma_step_valid_in_fp_pred_left(p1, p2, w1, step, next);
        lemma_derivation_valid_in_fp_pred_left(p1, p2, steps.drop_first(), next, w2);
    }
}

///  Left embedding: equiv in p1 ⟹ equiv in free_product_pred(p1, p2).
pub proof fn lemma_left_embeds_pred(p1: PredPresentation, p2: PredPresentation, w1: Word, w2: Word)
    requires
        equiv_in_pred_presentation(p1, w1, w2),
    ensures
        equiv_in_pred_presentation(free_product_pred(p1, p2), w1, w2),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_in_fp_pred_left(p1, p2, d.steps, w1, w2);
    let d_fp = PredDerivation { steps: d.steps };
    assert(pred_derivation_valid(free_product_pred(p1, p2), d_fp, w1, w2));
}

//  ============================================================
//  Right embedding.
//  ============================================================

///  Shift a predicate derivation step: shift symbols / the carried relator
///  word by `offset`.  No relator-index shift needed — the word is carried.
pub open spec fn shift_derivation_step_pred(step: PredDerivationStep, offset: nat) -> PredDerivationStep {
    match step {
        PredDerivationStep::FreeReduce { position } =>
            PredDerivationStep::FreeReduce { position },
        PredDerivationStep::FreeExpand { position, symbol } =>
            PredDerivationStep::FreeExpand { position, symbol: shift_symbol(symbol, offset) },
        PredDerivationStep::RelatorInsert { position, relator, inverted } =>
            PredDerivationStep::RelatorInsert { position, relator: shift_word(relator, offset), inverted },
        PredDerivationStep::RelatorDelete { position, relator, inverted } =>
            PredDerivationStep::RelatorDelete { position, relator: shift_word(relator, offset), inverted },
    }
}

///  A shifted step on a shifted word produces a shifted result in the product.
proof fn lemma_shifted_step_valid_pred(
    p1: PredPresentation, p2: PredPresentation,
    w: Word, step: PredDerivationStep, w_prime: Word,
)
    requires
        apply_step_pred(p2, w, step) == Some(w_prime),
    ensures
        apply_step_pred(
            free_product_pred(p1, p2),
            shift_word(w, p1.num_generators),
            shift_derivation_step_pred(step, p1.num_generators),
        ) == Some(shift_word(w_prime, p1.num_generators)),
{
    let fp = free_product_pred(p1, p2);
    let offset = p1.num_generators;
    let sw = shift_word(w, offset);
    match step {
        PredDerivationStep::FreeReduce { position } => {
            assert(has_cancellation_at(w, position));
            lemma_shift_preserves_cancellation(w, offset, position);
            lemma_shift_reduce_at(w, offset, position);
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
            let ss = shift_symbol(symbol, offset);
            let pair_shifted = Seq::new(1, |_i: int| ss) + Seq::new(1, |_i: int| inverse_symbol(ss));
            assert(symbol_valid(symbol, p2.num_generators));
            assert(symbol_valid(ss, fp.num_generators));
            assert(shift_symbol(inverse_symbol(symbol), offset) == inverse_symbol(shift_symbol(symbol, offset)));
            lemma_shift_word_len(w, offset);
            assert(sw.subrange(0, position) =~= shift_word(w.subrange(0, position), offset));
            assert(sw.subrange(position, sw.len() as int) =~= shift_word(w.subrange(position, w.len() as int), offset));
            assert(sw.subrange(0, position) + pair_shifted + sw.subrange(position, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            //  guard in p2: (p2.relators)(relator) ⟹ shifted relator accepted in fp
            assert((p2.relators)(relator));
            let shifted_rel = shift_word(relator, offset);
            assert(shifted_pred(p2.relators, offset, shifted_rel)) by {
                assert((p2.relators)(relator) && shifted_rel == shift_word(relator, offset));
            }
            assert((fp.relators)(shifted_rel));

            let r = get_relator_pred(relator, inverted);
            let r_fp = get_relator_pred(shifted_rel, inverted);
            if inverted {
                lemma_shift_inverse_word(relator, offset);
            }
            assert(r_fp =~= shift_word(r, offset));

            lemma_shift_word_len(w, offset);
            assert(sw.subrange(0, position) =~= shift_word(w.subrange(0, position), offset));
            assert(sw.subrange(position, sw.len() as int) =~= shift_word(w.subrange(position, w.len() as int), offset));
            assert(sw.subrange(0, position) + r_fp + sw.subrange(position, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert((p2.relators)(relator));
            let shifted_rel = shift_word(relator, offset);
            assert(shifted_pred(p2.relators, offset, shifted_rel)) by {
                assert((p2.relators)(relator) && shifted_rel == shift_word(relator, offset));
            }
            assert((fp.relators)(shifted_rel));

            let r = get_relator_pred(relator, inverted);
            let rlen = r.len();
            let r_fp = get_relator_pred(shifted_rel, inverted);
            if inverted {
                lemma_shift_inverse_word(relator, offset);
            }
            assert(r_fp =~= shift_word(r, offset));

            lemma_shift_word_len(r, offset);
            lemma_shift_word_len(w, offset);
            assert(r_fp.len() == rlen);

            assert(sw.subrange(position, position + rlen as int) =~= shift_word(r, offset));
            assert(sw.subrange(position, position + r_fp.len() as int) == r_fp);
            assert(sw.subrange(0, position) + sw.subrange(position + r_fp.len() as int, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
    }
}

///  A shifted derivation valid in fp.
proof fn lemma_shifted_derivation_valid_pred(
    p1: PredPresentation, p2: PredPresentation,
    steps: Seq<PredDerivationStep>, w1: Word, w2: Word,
)
    requires
        pred_derivation_produces(p2, steps, w1) == Some(w2),
    ensures
        equiv_in_pred_presentation(
            free_product_pred(p1, p2),
            shift_word(w1, p1.num_generators),
            shift_word(w2, p1.num_generators),
        ),
    decreases steps.len(),
{
    let fp = free_product_pred(p1, p2);
    let offset = p1.num_generators;
    if steps.len() == 0 {
        assert(w1 == w2);
        lemma_pred_equiv_refl(fp, shift_word(w1, offset));
    } else {
        let step = steps.first();
        let next = apply_step_pred(p2, w1, step).unwrap();
        let rest = steps.drop_first();

        let shifted_step = shift_derivation_step_pred(step, offset);
        lemma_shifted_step_valid_pred(p1, p2, w1, step, next);

        let d = PredDerivation { steps: Seq::new(1, |_i: int| shifted_step) };
        assert(d.steps.first() == shifted_step);
        assert(d.steps.drop_first() =~= Seq::<PredDerivationStep>::empty());
        assert(pred_derivation_produces(fp, d.steps.drop_first(), shift_word(next, offset)) == Some(shift_word(next, offset)));
        assert(pred_derivation_valid(fp, d, shift_word(w1, offset), shift_word(next, offset)));

        lemma_shifted_derivation_valid_pred(p1, p2, rest, next, w2);

        lemma_pred_equiv_transitive(fp, shift_word(w1, offset), shift_word(next, offset), shift_word(w2, offset));
    }
}

///  Right embedding: equiv in p2 ⟹ equiv of shifted words in free_product_pred.
pub proof fn lemma_right_embeds_pred(p1: PredPresentation, p2: PredPresentation, w1: Word, w2: Word)
    requires
        equiv_in_pred_presentation(p2, w1, w2),
    ensures
        equiv_in_pred_presentation(
            free_product_pred(p1, p2),
            shift_word(w1, p1.num_generators),
            shift_word(w2, p1.num_generators),
        ),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p2, d, w1, w2);
    lemma_shifted_derivation_valid_pred(p1, p2, d.steps, w1, w2);
}

} //  verus!
