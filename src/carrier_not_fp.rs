// carrier_not_fp — the NON-FINITE-PRESENTABILITY arc (docs/carrier-not-fp-plan.md).
//
// Target: the Miller CEER carrier `P_∞(fam) = ⟨a,t | ⋃_M D̄_M⟩` presents a group that is NOT
// finitely presentable.  This module builds the two generic bricks that need no Miller machinery:
//
//   * **NF-1** — `lemma_fin_equiv_lifts_to_pred`: the exact MIRROR of
//     `pred_to_finite::lemma_pred_equiv_lifts_to_finite` — a FINITE-presentation equivalence lifts
//     into a predicate presentation in which every finite relator is trivial (≡ ε).  This is the
//     "replay" half of B. H. Neumann's finite-subset lemma: a finite presentation whose relators
//     are all consequences of a relator set derives nothing beyond that set's consequences.
//
//   * **NF-A** — `lemma_carrier_not_fp_over_std_gens`: the core refutation.  If a finite
//     presentation `fp` on the same 2 generators has the same TRIVIAL WORDS as `P_∞(fam)`, then
//     (compactness: `lemma_extract_slice`) each of its finitely many relators is trivial in a
//     single finite slice `P_{≤m*}`, so (NF-1) every `fp`-trivial word is `P_{≤m*}`-trivial — and
//     the ESCAPE HYPOTHESIS (`limit_escapes_every_slice`: every slice misses some `P_∞`-trivial
//     word) yields a contradiction.
//
// The escape hypothesis is discharged separately (bricks NF-2/NF-3 of the plan: Miller
// faithfulness per slice + finite equivalence closures have bounded classes); it is exactly
// "the CEER is not finitely generated as an equivalence relation," seen at the carrier.
//
// Additive; reversible; the only substrate changes are `pub` on four `miller_collapse_limit`
// helpers (strip/extract/slice-monotone).  No assume/admit/external_body.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::*;
use crate::pred_britton_via_tower::lemma_pred_inverse_of_trivial;
use crate::miller_collapse_preserve::*;
use crate::miller_collapse_limit::*;
use crate::cohen_layer05::decls_family_valid;

verus! {

// ============================================================================
// Part 1 — NF-1: finite → pred lift over target-trivial relators
// (mirror of pred_to_finite.rs with the two presentation kinds swapped)
// ============================================================================

/// A single successful pred step witnesses equivalence (singleton derivation).
proof fn lemma_pred_single_step_equiv(
    q: PredPresentation, w: Word, step: PredDerivationStep, w_next: Word,
)
    requires
        apply_step_pred(q, w, step) == Some(w_next),
    ensures
        equiv_in_pred_presentation(q, w, w_next),
{
    let d = PredDerivation { steps: seq![step] };
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<PredDerivationStep>::empty());
    assert(pred_derivation_produces(q, d.steps.drop_first(), w_next) == Some(w_next));
    assert(pred_derivation_produces(q, d.steps, w) == Some(w_next));
    assert(pred_derivation_valid(q, d, w, w_next));
}

/// Splicing a trivial word preserves pred-equivalence (forward):
/// `u ≡_q ε ⟹ (a·u)·b ≡_q a·b`.  Mirror of `pred_to_finite::lemma_splice_trivial`.
proof fn lemma_pred_splice_trivial(q: PredPresentation, a: Word, u: Word, b: Word)
    requires
        equiv_in_pred_presentation(q, u, empty_word()),
    ensures
        equiv_in_pred_presentation(q, concat(concat(a, u), b), concat(a, b)),
{
    lemma_pred_equiv_refl(q, a);
    lemma_pred_equiv_concat(q, a, a, u, empty_word());          // a·u ≡ a·ε
    assert(concat(a, empty_word()) =~= a);
    assert(equiv_in_pred_presentation(q, concat(a, u), a));
    lemma_pred_equiv_concat_left(q, concat(a, u), a, b);        // (a·u)·b ≡ a·b
}

/// A single finite `fp`-derivation step is a `q`-equivalence, given gen-count inclusion,
/// `pred_presentation_valid(q)`, and that every `fp`-relator is `q`-trivial AND a valid `q`-word.
proof fn lemma_fin_step_lifts_to_pred(
    fp: Presentation, q: PredPresentation, w: Word, step: DerivationStep, w_next: Word,
)
    requires
        fp.num_generators <= q.num_generators,
        pred_presentation_valid(q),
        forall|k: int| 0 <= k < fp.relators.len() ==>
            equiv_in_pred_presentation(q, #[trigger] fp.relators[k], empty_word())
            && word_valid(fp.relators[k], q.num_generators),
        apply_step(fp, w, step) == Some(w_next),
    ensures
        equiv_in_pred_presentation(q, w, w_next),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            // identical pred step
            assert(has_cancellation_at(w, position));
            assert(w_next == reduce_at(w, position));
            let qstep = PredDerivationStep::FreeReduce { position };
            assert(apply_step_pred(q, w, qstep) == Some(w_next));
            lemma_pred_single_step_equiv(q, w, qstep, w_next);
        }
        DerivationStep::FreeExpand { position, symbol } => {
            // finite success ⟹ symbol_valid in fp ⟹ symbol_valid in q (monotone)
            assert(0 <= position <= w.len());
            assert(symbol_valid(symbol, fp.num_generators));
            assert(symbol_valid(symbol, q.num_generators)) by {
                assert(generator_index(symbol) < fp.num_generators);
            }
            let qstep = PredDerivationStep::FreeExpand { position, symbol };
            assert(apply_step_pred(q, w, qstep) == Some(w_next));
            lemma_pred_single_step_equiv(q, w, qstep, w_next);
        }
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= position <= w.len());
            assert(0 <= relator_index < fp.relators.len());
            let r = fp.relators[relator_index as int];
            assert(equiv_in_pred_presentation(q, r, empty_word()));
            assert(word_valid(r, q.num_generators));
            let rr = get_relator(fp, relator_index, inverted);
            // rr ≡_q ε and word_valid(rr)
            if inverted {
                assert(rr == inverse_word(r));
                lemma_pred_inverse_of_trivial(q, r);
                lemma_inverse_word_valid(r, q.num_generators);
            }
            assert(equiv_in_pred_presentation(q, rr, empty_word()));
            assert(word_valid(rr, q.num_generators));
            // ε ≡ rr (symmetric; needs word_valid(rr) + pred_presentation_valid(q))
            lemma_pred_equiv_symmetric(q, rr, empty_word());
            assert(equiv_in_pred_presentation(q, empty_word(), rr));
            // build w ≡ w_next FORWARD
            let prefix = w.subrange(0, position);
            let suffix = w.subrange(position, w.len() as int);
            // prefix ≡ prefix·rr
            lemma_pred_equiv_concat_right(q, prefix, empty_word(), rr);  // prefix·ε ≡ prefix·rr
            assert(concat(prefix, empty_word()) =~= prefix);
            assert(equiv_in_pred_presentation(q, prefix, concat(prefix, rr)));
            // prefix·suffix ≡ (prefix·rr)·suffix
            lemma_pred_equiv_concat_left(q, prefix, concat(prefix, rr), suffix);
            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(concat(prefix, rr), suffix));
        }
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < fp.relators.len());
            let r = fp.relators[relator_index as int];
            assert(equiv_in_pred_presentation(q, r, empty_word()));
            assert(word_valid(r, q.num_generators));
            let rr = get_relator(fp, relator_index, inverted);
            if inverted {
                assert(rr == inverse_word(r));
                lemma_pred_inverse_of_trivial(q, r);
            }
            assert(equiv_in_pred_presentation(q, rr, empty_word()));
            let rlen = rr.len();
            assert(0 <= position && position + rlen <= w.len());
            assert(w.subrange(position, position + rlen as int) == rr);
            let prefix = w.subrange(0, position);
            let tail = w.subrange(position + rlen as int, w.len() as int);
            // w =~= (prefix·rr)·tail
            assert(w =~= concat(concat(prefix, rr), tail)) by {
                assert(w =~= prefix + w.subrange(position, position + rlen as int) + tail);
            }
            assert(w_next =~= concat(prefix, tail));
            lemma_pred_splice_trivial(q, prefix, rr, tail);     // (prefix·rr)·tail ≡ prefix·tail
        }
    }
}

/// A finite `fp`-derivation lifts to a `q`-equivalence between its endpoints.
proof fn lemma_fin_deriv_lifts_to_pred(
    fp: Presentation, q: PredPresentation, steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        fp.num_generators <= q.num_generators,
        pred_presentation_valid(q),
        forall|k: int| 0 <= k < fp.relators.len() ==>
            equiv_in_pred_presentation(q, #[trigger] fp.relators[k], empty_word())
            && word_valid(fp.relators[k], q.num_generators),
        derivation_produces(fp, steps, start) == Some(end),
    ensures
        equiv_in_pred_presentation(q, start, end),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(end == start);
        lemma_pred_equiv_refl(q, start);
    } else {
        let first = steps.first();
        assert(apply_step(fp, start, first) is Some);
        let w1 = apply_step(fp, start, first).unwrap();
        assert(apply_step(fp, start, first) == Some(w1));
        assert(derivation_produces(fp, steps.drop_first(), w1) == Some(end));
        lemma_fin_step_lifts_to_pred(fp, q, start, first, w1);
        lemma_fin_deriv_lifts_to_pred(fp, q, steps.drop_first(), w1, end);
        lemma_pred_equiv_transitive(q, start, w1, end);
    }
}

/// **NF-1 HEADLINE.**  If every relator of the finite `fp` is trivial in (and a valid word of) the
/// predicate presentation `q`, and `fp`'s generators inject into `q`'s, then `fp`-equivalence
/// implies `q`-equivalence.  (Mirror of `lemma_pred_equiv_lifts_to_finite`.)
pub proof fn lemma_fin_equiv_lifts_to_pred(
    fp: Presentation, q: PredPresentation, w1: Word, w2: Word,
)
    requires
        fp.num_generators <= q.num_generators,
        pred_presentation_valid(q),
        forall|k: int| 0 <= k < fp.relators.len() ==>
            equiv_in_pred_presentation(q, #[trigger] fp.relators[k], empty_word())
            && word_valid(fp.relators[k], q.num_generators),
        equiv_in_presentation(fp, w1, w2),
    ensures
        equiv_in_pred_presentation(q, w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(fp, d, w1, w2);
    lemma_fin_deriv_lifts_to_pred(fp, q, d.steps, w1, w2);
}

// ============================================================================
// Part 2 — slice plumbing over the banked compactness toolkit
// ============================================================================

/// A `P_{≤m1}`-equivalence is a `P_{≤m2}`-equivalence (`m1 ≤ m2`): strip the empty-relator no-op
/// steps, then replay the (nonempty) derivation at the larger slice by monotonicity.
pub proof fn lemma_slice_equiv_monotone(
    fam: spec_fn(nat) -> Seq<Word>, m1: nat, m2: nat, w1: Word, w2: Word,
)
    requires
        dbar_family_monotone(fam),
        m1 <= m2,
        equiv_in_pred_presentation(p_le(fam, m1), w1, w2),
    ensures
        equiv_in_pred_presentation(p_le(fam, m2), w1, w2),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p_le(fam, m1), d, w1, w2);
    assert(pred_derivation_produces(p_le(fam, m1), d.steps, w1) == Some(w2));
    let stripped = strip_empty_steps(d.steps);
    lemma_strip_preserves_produces(p_le(fam, m1), d.steps, w1, w2);
    lemma_strip_yields_nonempty(d.steps);
    lemma_produces_slice_monotone(fam, m1, m2, stripped, w1, w2);
    let pd = PredDerivation { steps: stripped };
    assert(pred_derivation_valid(p_le(fam, m2), pd, w1, w2));
}

/// A `P_∞`-trivial word is trivial in SOME finite slice (strip + `lemma_extract_slice`).
pub proof fn lemma_trivial_in_some_slice(fam: spec_fn(nat) -> Seq<Word>, w: Word)
    requires
        dbar_family_monotone(fam),
        equiv_in_pred_presentation(p_infty(fam), w, empty_word()),
    ensures
        exists|m: nat| equiv_in_pred_presentation(#[trigger] p_le(fam, m), w, empty_word()),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p_infty(fam), d, w, empty_word());
    assert(pred_derivation_produces(p_infty(fam), d.steps, w) == Some(empty_word()));
    let stripped = strip_empty_steps(d.steps);
    lemma_strip_preserves_produces(p_infty(fam), d.steps, w, empty_word());
    lemma_strip_yields_nonempty(d.steps);
    lemma_extract_slice(fam, 0, stripped, w, empty_word());
    let m = choose|m: nat| #![trigger pred_derivation_produces(p_le(fam, m), stripped, w)]
        0 <= m && pred_derivation_produces(p_le(fam, m), stripped, w) == Some(empty_word());
    let pd = PredDerivation { steps: stripped };
    assert(pred_derivation_valid(p_le(fam, m), pd, w, empty_word()));
    assert(equiv_in_pred_presentation(p_le(fam, m), w, empty_word()));
}

/// The first `k` relators of `fp` are all trivial at slice `m`.
pub open spec fn relators_trivial_upto(
    fam: spec_fn(nat) -> Seq<Word>, fp: Presentation, m: nat, k: int,
) -> bool {
    forall|i: int| 0 <= i < k ==>
        equiv_in_pred_presentation(p_le(fam, m), #[trigger] fp.relators[i], empty_word())
}

/// Finitely many `P_∞`-trivial relators are all trivial in ONE common slice
/// (induction on `k`, taking the max of the two witness levels at each step).
proof fn lemma_relators_in_common_slice(
    fam: spec_fn(nat) -> Seq<Word>, fp: Presentation, k: int,
)
    requires
        dbar_family_monotone(fam),
        forall|i: int| 0 <= i < fp.relators.len() ==>
            equiv_in_pred_presentation(p_infty(fam), #[trigger] fp.relators[i], empty_word()),
        0 <= k <= fp.relators.len(),
    ensures
        exists|m: nat| #[trigger] relators_trivial_upto(fam, fp, m, k),
    decreases k,
{
    if k == 0 {
        assert(relators_trivial_upto(fam, fp, 0, 0));
    } else {
        lemma_relators_in_common_slice(fam, fp, k - 1);
        let m_prev = choose|m: nat| #[trigger] relators_trivial_upto(fam, fp, m, k - 1);
        let r = fp.relators[k - 1];
        assert(equiv_in_pred_presentation(p_infty(fam), r, empty_word()));
        lemma_trivial_in_some_slice(fam, r);
        let m_k = choose|m: nat| equiv_in_pred_presentation(#[trigger] p_le(fam, m), r, empty_word());
        let mf: nat = if m_prev >= m_k { m_prev } else { m_k };
        assert forall|i: int| 0 <= i < k implies
            equiv_in_pred_presentation(p_le(fam, mf), #[trigger] fp.relators[i], empty_word()) by {
            if i < k - 1 {
                assert(equiv_in_pred_presentation(p_le(fam, m_prev), fp.relators[i], empty_word()));
                lemma_slice_equiv_monotone(fam, m_prev, mf, fp.relators[i], empty_word());
            } else {
                assert(fp.relators[i] == r);
                lemma_slice_equiv_monotone(fam, m_k, mf, r, empty_word());
            }
        }
        assert(relators_trivial_upto(fam, fp, mf, k));
    }
}

// ============================================================================
// Part 3 — the escape hypothesis and the NF-A refutation
// ============================================================================

/// Slice `m` MISSES some `P_∞`-trivial word: there is a valid 2-generator word trivial in the
/// full carrier `P_∞` but not in `P_{≤m}`.
pub open spec fn slice_escaped(fam: spec_fn(nat) -> Seq<Word>, m: nat) -> bool {
    exists|w: Word|
        word_valid(w, 2)
        && #[trigger] equiv_in_pred_presentation(p_infty(fam), w, empty_word())
        && !equiv_in_pred_presentation(p_le(fam, m), w, empty_word())
}

/// EVERY finite slice is escaped.  This is "the CEER is not finitely generated as an equivalence
/// relation," seen at the carrier — discharged separately by the Miller-faithfulness bricks
/// (plan NF-2/NF-3); here it is the abstract hypothesis of the refutation.
pub open spec fn limit_escapes_every_slice(fam: spec_fn(nat) -> Seq<Word>) -> bool {
    forall|m: nat| #[trigger] slice_escaped(fam, m)
}

/// **NF-A HEADLINE — the core refutation.**  No finite presentation `fp` on the standard 2
/// generators has the same trivial words as the carrier `P_∞(fam)`: its finitely many relators
/// would all be `P_∞`-trivial (they are trivial in `fp` itself), hence — by compactness — trivial
/// in one finite slice `P_{≤m*}`; NF-1 then lifts EVERY `fp`-trivial word into `P_{≤m*}`,
/// contradicting the escape hypothesis at `m*`.
pub proof fn lemma_carrier_not_fp_over_std_gens(
    fam: spec_fn(nat) -> Seq<Word>, fp: Presentation,
)
    requires
        decls_family_valid(fam),
        dbar_family_monotone(fam),
        limit_escapes_every_slice(fam),
        fp.num_generators == 2,
        presentation_valid(fp),
        forall|w: Word| word_valid(w, 2) ==>
            (equiv_in_presentation(fp, w, empty_word())
                <==> #[trigger] equiv_in_pred_presentation(p_infty(fam), w, empty_word())),
    ensures
        false,
{
    reveal(presentation_valid);
    // 1. every fp-relator is P_∞-trivial (trivial in fp itself + the same-trivial-words iff)
    assert forall|i: int| 0 <= i < fp.relators.len() implies
        equiv_in_pred_presentation(p_infty(fam), #[trigger] fp.relators[i], empty_word()) by {
        lemma_relator_is_identity(fp, i);
        assert(word_valid(fp.relators[i], 2));
        assert(equiv_in_presentation(fp, fp.relators[i], empty_word()));
    }
    // 2. one common slice m* holds them all
    lemma_relators_in_common_slice(fam, fp, fp.relators.len() as int);
    let mf = choose|m: nat| #[trigger] relators_trivial_upto(fam, fp, m, fp.relators.len() as int);
    // 3. the escape word at m*
    assert(slice_escaped(fam, mf));
    let wt = choose|w: Word|
        word_valid(w, 2)
        && #[trigger] equiv_in_pred_presentation(p_infty(fam), w, empty_word())
        && !equiv_in_pred_presentation(p_le(fam, mf), w, empty_word());
    // 4. by the iff, the escape word is fp-trivial
    assert(equiv_in_presentation(fp, wt, empty_word()));
    // 5. the slice presentation is valid (its relators are the D̄ words, valid over 2 generators)
    assert forall|j: int| 0 <= j < fam(mf).len() implies word_valid(#[trigger] fam(mf)[j], mf) by {}
    lemma_dbar_valid(mf, fam(mf));
    assert(pred_presentation_valid(p_le(fam, mf))) by {
        reveal(pred_presentation_valid);
        assert forall|r: Word| #[trigger] (p_le(fam, mf).relators)(r) implies word_valid(r, 2) by {
            assert(dbar(mf, fam(mf)).contains(r));
            let idx = choose|idx: int| #![trigger dbar(mf, fam(mf))[idx]]
                0 <= idx < dbar(mf, fam(mf)).len() && dbar(mf, fam(mf))[idx] == r;
            assert(word_valid(dbar(mf, fam(mf))[idx], 2));
        }
    }
    // 6. NF-1: every fp-trivial word — in particular the escape word — is P_{≤m*}-trivial
    assert forall|k: int| 0 <= k < fp.relators.len() implies
        equiv_in_pred_presentation(p_le(fam, mf), #[trigger] fp.relators[k], empty_word())
        && word_valid(fp.relators[k], 2) by {
        assert(relators_trivial_upto(fam, fp, mf, fp.relators.len() as int));
        assert(equiv_in_pred_presentation(p_le(fam, mf), fp.relators[k], empty_word()));
    }
    lemma_fin_equiv_lifts_to_pred(fp, p_le(fam, mf), wt, empty_word());
    // contradiction with the escape word's non-triviality at m*
    assert(false);
}

} // verus!
