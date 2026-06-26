// GAP-3 (final gate) — generic SOUNDNESS transport: `PredPresentation` → `Presentation`.
//
// `docs/final-gate-axiom-removal-plan.md` §5.  The Layer-2 faithfulness direction
// (`h3_pres ⟹ c_pred`) is `lemma_C_faithful_printable_canonical` (PROVEN).  The final iff also
// needs the OTHER direction — SOUNDNESS — `equiv_in_pred_presentation(c_pred,w,ε) ⟹
// equiv_in_presentation(h3_pres,w,ε)`.  Since `c_pred`'s only relators are `S = {w_α(c):(α,0)∈H₀}`
// and each such word is trivial in `h3_pres` (Layer-2 soundness `lemma_III`), a `c_pred`-derivation
// lifts step-by-step to an `h3_pres`-equivalence.
//
// This module proves that lift GENERICALLY, with no dependence on the machine / Cohen specifics:
// for ANY `PredPresentation cp` and `Presentation fp` with `cp.num_generators ≤ fp.num_generators`
// and `presentation_valid(fp)`, if every `cp`-relator is `ε` in `fp` (and a valid `fp`-word), then
// `cp`-equivalence implies `fp`-equivalence.  The machine-specific application (instantiate at
// `cp = c_pred`, `fp = h3_pres`, discharge the relator hypothesis with `lemma_III`) is a separate
// brick.
//
// Method: each pred derivation step `w → w_next` is shown to be an `fp`-equivalence —
//   * `FreeReduce`/`FreeExpand` map to the identical finite step (free-reduction is presentation-
//     agnostic; expansion's only side condition `symbol_valid` is monotone in `num_generators`);
//   * `RelatorInsert`/`RelatorDelete` splice / unsplice a word `r` with `cp.relators(r)`, which is
//     `ε` in `fp` by hypothesis, so the splice preserves `fp`-equivalence.  Each step is produced in
//     the FORWARD orientation directly, so only the *relators* (valid c-words) ever need validity —
//     never the intermediate derivation words.
// Chaining over the derivation by transitivity gives the headline.  Additive; reversible; the only
// imports are the verified word/presentation algebra.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::pred_presentation::*;

verus! {

// ============================================================================
// Building block (validity-free): splice a trivial word forward
// ============================================================================

/// Splicing a trivial word preserves equivalence (forward): `u ≡_fp ε ⟹ (a·u)·b ≡_fp a·b`.
/// Validity-free — pure congruence over `lemma_equiv_concat`.
pub proof fn lemma_splice_trivial(fp: Presentation, a: Word, u: Word, b: Word)
    requires
        equiv_in_presentation(fp, u, empty_word()),
    ensures
        equiv_in_presentation(fp, concat(concat(a, u), b), concat(a, b)),
{
    lemma_equiv_refl(fp, b);
    // a·u ≡ a·ε =~= a
    lemma_equiv_refl(fp, a);
    lemma_equiv_concat(fp, a, a, u, empty_word());          // a·u ≡ a·ε
    assert(concat(a, empty_word()) =~= a);
    assert(equiv_in_presentation(fp, concat(a, u), a));
    // (a·u)·b ≡ a·b
    lemma_equiv_concat(fp, concat(a, u), a, b, b);
}

// ============================================================================
// Per-step lift
// ============================================================================

/// A single `cp` pred-derivation step is an `fp`-equivalence (forward), given gen-count inclusion,
/// `presentation_valid(fp)`, and that every `cp`-relator is `fp`-trivial AND a valid `fp`-word.
pub proof fn lemma_pred_step_lifts(
    cp: PredPresentation, fp: Presentation, w: Word, step: PredDerivationStep, w_next: Word,
)
    requires
        cp.num_generators <= fp.num_generators,
        presentation_valid(fp),
        forall|r: Word| #[trigger] (cp.relators)(r) ==>
            equiv_in_presentation(fp, r, empty_word()) && word_valid(r, fp.num_generators),
        apply_step_pred(cp, w, step) == Some(w_next),
    ensures
        equiv_in_presentation(fp, w, w_next),
{
    match step {
        PredDerivationStep::FreeReduce { position } => {
            // identical finite step
            assert(has_cancellation_at(w, position));
            assert(w_next == reduce_at(w, position));
            let fstep = DerivationStep::FreeReduce { position };
            assert(apply_step(fp, w, fstep) == Some(w_next));
            crate::base_swap::lemma_single_step_equiv(fp, w, fstep, w_next);
        }
        PredDerivationStep::FreeExpand { position, symbol } => {
            // pred success ⟹ symbol_valid in cp ⟹ symbol_valid in fp (monotone)
            assert(0 <= position <= w.len());
            assert(symbol_valid(symbol, cp.num_generators));
            assert(symbol_valid(symbol, fp.num_generators)) by {
                assert(generator_index(symbol) < cp.num_generators);
            }
            let fstep = DerivationStep::FreeExpand { position, symbol };
            assert(apply_step(fp, w, fstep) == Some(w_next));
            crate::base_swap::lemma_single_step_equiv(fp, w, fstep, w_next);
        }
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            assert((cp.relators)(relator));
            assert(equiv_in_presentation(fp, relator, empty_word()));
            assert(word_valid(relator, fp.num_generators));
            let rr = get_relator_pred(relator, inverted);
            // rr ≡_fp ε and word_valid(rr)
            if inverted {
                crate::base_swap::lemma_inv_equiv_empty(fp, relator);
                lemma_inverse_word_valid(relator, fp.num_generators);
            }
            assert(equiv_in_presentation(fp, rr, empty_word()));
            assert(word_valid(rr, fp.num_generators));
            // ε ≡ rr (symmetric; needs word_valid(rr) + presentation_valid(fp))
            lemma_equiv_symmetric(fp, rr, empty_word());
            assert(equiv_in_presentation(fp, empty_word(), rr));
            // build w ≡ w_next FORWARD
            let prefix = w.subrange(0, position);
            let suffix = w.subrange(position, w.len() as int);
            // prefix ≡ prefix·rr
            lemma_equiv_concat_right(fp, prefix, empty_word(), rr);  // prefix·ε ≡ prefix·rr
            assert(concat(prefix, empty_word()) =~= prefix);
            assert(equiv_in_presentation(fp, prefix, concat(prefix, rr)));
            // prefix·suffix ≡ (prefix·rr)·suffix
            lemma_equiv_concat_left(fp, prefix, concat(prefix, rr), suffix);
            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(concat(prefix, rr), suffix));
        }
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert((cp.relators)(relator));
            assert(equiv_in_presentation(fp, relator, empty_word()));
            let rr = get_relator_pred(relator, inverted);
            let rlen = rr.len();
            assert(0 <= position && position + rlen <= w.len());
            assert(w.subrange(position, position + rlen as int) == rr);
            // rr ≡_fp ε
            if inverted {
                crate::base_swap::lemma_inv_equiv_empty(fp, relator);
            }
            assert(equiv_in_presentation(fp, rr, empty_word()));
            let prefix = w.subrange(0, position);
            let tail = w.subrange(position + rlen as int, w.len() as int);
            // w =~= (prefix·rr)·tail
            assert(w =~= concat(concat(prefix, rr), tail)) by {
                assert(w =~= prefix + w.subrange(position, position + rlen as int) + tail);
            }
            assert(w_next =~= concat(prefix, tail));
            lemma_splice_trivial(fp, prefix, rr, tail);     // (prefix·rr)·tail ≡ prefix·tail
        }
    }
}

// ============================================================================
// Derivation lift + headline
// ============================================================================

/// A `cp` pred-derivation lifts to an `fp`-equivalence between its endpoints.
pub proof fn lemma_pred_deriv_lifts(
    cp: PredPresentation, fp: Presentation, steps: Seq<PredDerivationStep>, start: Word, end: Word,
)
    requires
        cp.num_generators <= fp.num_generators,
        presentation_valid(fp),
        forall|r: Word| #[trigger] (cp.relators)(r) ==>
            equiv_in_presentation(fp, r, empty_word()) && word_valid(r, fp.num_generators),
        pred_derivation_produces(cp, steps, start) == Some(end),
    ensures
        equiv_in_presentation(fp, start, end),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(end == start);
        lemma_equiv_refl(fp, start);
    } else {
        let first = steps.first();
        assert(apply_step_pred(cp, start, first) is Some);
        let w1 = apply_step_pred(cp, start, first).unwrap();
        assert(apply_step_pred(cp, start, first) == Some(w1));
        assert(pred_derivation_produces(cp, steps.drop_first(), w1) == Some(end));
        lemma_pred_step_lifts(cp, fp, start, first, w1);
        lemma_pred_deriv_lifts(cp, fp, steps.drop_first(), w1, end);
        lemma_equiv_transitive(fp, start, w1, end);
    }
}

/// **HEADLINE (GAP-3 generic soundness).**  If `fp` is valid, every `cp`-relator is a valid `fp`-word
/// trivial in `fp`, and `cp`'s generators inject into `fp`'s, then `cp`-equivalence implies
/// `fp`-equivalence.
pub proof fn lemma_pred_equiv_lifts_to_finite(
    cp: PredPresentation, fp: Presentation, w1: Word, w2: Word,
)
    requires
        cp.num_generators <= fp.num_generators,
        presentation_valid(fp),
        forall|r: Word| #[trigger] (cp.relators)(r) ==>
            equiv_in_presentation(fp, r, empty_word()) && word_valid(r, fp.num_generators),
        equiv_in_pred_presentation(cp, w1, w2),
    ensures
        equiv_in_presentation(fp, w1, w2),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(cp, d, w1, w2);
    lemma_pred_deriv_lifts(cp, fp, d.steps, w1, w2);
}

} // verus!
