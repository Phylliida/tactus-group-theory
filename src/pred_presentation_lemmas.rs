use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::pred_presentation::*;

verus! {

//  ============================================================
//  FORK-A — predicate-base equivalence-congruence algebra (2026-06-23).
//
//  Predicate-base analog of `presentation_lemmas.rs`'s core congruence layer,
//  over `PredPresentation`.  Per `docs/cohen-faithfulness-primary-source.md`
//  §7c, the equivalence/derivation algebra is relator-set-agnostic and ports
//  VERBATIM; the only relator-aware lemmas (`relator_is_identity`,
//  `conjugate_relator_is_identity`) carry the relator WORD gated by
//  `(p.relators)(r)` instead of an index — §6a's "trivial" word-carrying port.
//
//  This is brick FA-2: the congruence algebra the predicate HNN conjugation
//  lemma and the eventual predicate Britton tower depend on.  Kept separate
//  from the verified finite `presentation_lemmas` (reversible, zero regression).
//
//  Builds on `pred_presentation::{lemma_pred_equiv_refl, lemma_pred_equiv_transitive}`.
//  ============================================================

//  ============================================================
//  Equivalence respects group operations
//  ============================================================

///  A single derivation step on the left part of a concatenation.
proof fn lemma_pred_single_step_concat_left(p: PredPresentation, w1: Word, w2: Word, step: PredDerivationStep, w1_prime: Word)
    requires
        apply_step_pred(p, w1, step) == Some(w1_prime),
    ensures
        apply_step_pred(p, concat(w1, w2), step) == Some(concat(w1_prime, w2)),
{
    let cw = concat(w1, w2);
    match step {
        PredDerivationStep::FreeReduce { position } => {
            assert(has_cancellation_at(w1, position));
            assert(cw[position] == w1[position]);
            assert(cw[position + 1] == w1[position + 1]);
            assert(has_cancellation_at(cw, position));
            assert(reduce_at(cw, position) =~= concat(reduce_at(w1, position), w2));
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(cw.subrange(0, position) =~= w1.subrange(0, position));
            assert(cw.subrange(position, cw.len() as int) =~= w1.subrange(position, w1.len() as int) + w2);
            assert(cw.subrange(0, position) + pair + cw.subrange(position, cw.len() as int) =~=
                concat(w1.subrange(0, position) + pair + w1.subrange(position, w1.len() as int), w2));
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            let r = get_relator_pred(relator, inverted);
            assert(cw.subrange(0, position) =~= w1.subrange(0, position));
            assert(cw.subrange(position, cw.len() as int) =~= w1.subrange(position, w1.len() as int) + w2);
            assert(cw.subrange(0, position) + r + cw.subrange(position, cw.len() as int) =~=
                concat(w1.subrange(0, position) + r + w1.subrange(position, w1.len() as int), w2));
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            let r = get_relator_pred(relator, inverted);
            let rlen = r.len();
            assert(w1.subrange(position, position + rlen as int) == r);
            assert(cw.subrange(position, position + rlen as int) =~= r);
            assert(cw.subrange(0, position) + cw.subrange(position + rlen as int, cw.len() as int) =~=
                concat(w1.subrange(0, position) + w1.subrange(position + rlen as int, w1.len() as int), w2));
        },
    }
}

///  If w1 ≡ w1' then w1·w2 ≡ w1'·w2.
pub proof fn lemma_pred_equiv_concat_left(p: PredPresentation, w1: Word, w1_prime: Word, w2: Word)
    requires
        equiv_in_pred_presentation(p, w1, w1_prime),
    ensures
        equiv_in_pred_presentation(p, concat(w1, w2), concat(w1_prime, w2)),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p, d, w1, w1_prime);
    lemma_pred_derivation_lift_left(p, d.steps, w1, w1_prime, w2);
}

///  Lift an entire derivation to the left of a concatenation.
proof fn lemma_pred_derivation_lift_left(
    p: PredPresentation, steps: Seq<PredDerivationStep>,
    w1: Word, w1_prime: Word, w2: Word,
)
    requires
        pred_derivation_produces(p, steps, w1) == Some(w1_prime),
    ensures
        equiv_in_pred_presentation(p, concat(w1, w2), concat(w1_prime, w2)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w1 == w1_prime);
        lemma_pred_equiv_refl(p, concat(w1, w2));
    } else {
        let step = steps.first();
        let next = apply_step_pred(p, w1, step).unwrap();
        let rest = steps.drop_first();

        lemma_pred_single_step_concat_left(p, w1, w2, step, next);
        let lifted_step = step;
        assert(apply_step_pred(p, concat(w1, w2), lifted_step) == Some(concat(next, w2)));
        let lifted_d = PredDerivation { steps: Seq::new(1, |_i: int| lifted_step) };
        assert(lifted_d.steps.first() == lifted_step);
        assert(lifted_d.steps.drop_first() =~= Seq::<PredDerivationStep>::empty());
        assert(pred_derivation_produces(p, lifted_d.steps.drop_first(), concat(next, w2)) == Some(concat(next, w2)));
        assert(pred_derivation_valid(p, lifted_d, concat(w1, w2), concat(next, w2)));

        lemma_pred_derivation_lift_left(p, rest, next, w1_prime, w2);

        lemma_pred_equiv_transitive(p, concat(w1, w2), concat(next, w2), concat(w1_prime, w2));
    }
}

///  Shift a derivation step's position by an offset (for right-concat lifting).
pub open spec fn shift_step_pred(step: PredDerivationStep, offset: int) -> PredDerivationStep {
    match step {
        PredDerivationStep::FreeReduce { position } =>
            PredDerivationStep::FreeReduce { position: position + offset },
        PredDerivationStep::FreeExpand { position, symbol } =>
            PredDerivationStep::FreeExpand { position: position + offset, symbol },
        PredDerivationStep::RelatorInsert { position, relator, inverted } =>
            PredDerivationStep::RelatorInsert { position: position + offset, relator, inverted },
        PredDerivationStep::RelatorDelete { position, relator, inverted } =>
            PredDerivationStep::RelatorDelete { position: position + offset, relator, inverted },
    }
}

///  A single derivation step on the right part of a concatenation.
proof fn lemma_pred_single_step_concat_right(p: PredPresentation, w1: Word, w2: Word, step: PredDerivationStep, w2_prime: Word)
    requires
        apply_step_pred(p, w2, step) == Some(w2_prime),
    ensures
        apply_step_pred(p, concat(w1, w2), shift_step_pred(step, w1.len() as int)) == Some(concat(w1, w2_prime)),
{
    let cw = concat(w1, w2);
    let offset = w1.len() as int;
    match step {
        PredDerivationStep::FreeReduce { position } => {
            assert(has_cancellation_at(w2, position));
            assert(cw[position + offset] == w2[position]);
            assert(cw[position + offset + 1] == w2[position + 1]);
            assert(has_cancellation_at(cw, position + offset));
            assert(reduce_at(cw, position + offset) =~= concat(w1, reduce_at(w2, position)));
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(cw.subrange(0, position + offset) =~= w1 + w2.subrange(0, position));
            assert(cw.subrange(position + offset, cw.len() as int) =~= w2.subrange(position, w2.len() as int));
            assert(cw.subrange(0, position + offset) + pair + cw.subrange(position + offset, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + pair + w2.subrange(position, w2.len() as int)));
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            let r = get_relator_pred(relator, inverted);
            assert(cw.subrange(0, position + offset) =~= w1 + w2.subrange(0, position));
            assert(cw.subrange(position + offset, cw.len() as int) =~= w2.subrange(position, w2.len() as int));
            assert(cw.subrange(0, position + offset) + r + cw.subrange(position + offset, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + r + w2.subrange(position, w2.len() as int)));
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            let r = get_relator_pred(relator, inverted);
            let rlen = r.len();
            assert(w2.subrange(position, position + rlen as int) == r);
            assert(cw.subrange(position + offset, position + offset + rlen as int) =~= r);
            assert(cw.subrange(0, position + offset) + cw.subrange(position + offset + rlen as int, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + w2.subrange(position + rlen as int, w2.len() as int)));
        },
    }
}

///  If w2 ≡ w2' then w1·w2 ≡ w1·w2'.
pub proof fn lemma_pred_equiv_concat_right(p: PredPresentation, w1: Word, w2: Word, w2_prime: Word)
    requires
        equiv_in_pred_presentation(p, w2, w2_prime),
    ensures
        equiv_in_pred_presentation(p, concat(w1, w2), concat(w1, w2_prime)),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p, d, w2, w2_prime);
    lemma_pred_derivation_lift_right(p, d.steps, w1, w2, w2_prime);
}

///  Lift an entire derivation to the right of a concatenation.
proof fn lemma_pred_derivation_lift_right(
    p: PredPresentation, steps: Seq<PredDerivationStep>,
    w1: Word, w2: Word, w2_prime: Word,
)
    requires
        pred_derivation_produces(p, steps, w2) == Some(w2_prime),
    ensures
        equiv_in_pred_presentation(p, concat(w1, w2), concat(w1, w2_prime)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w2 == w2_prime);
        lemma_pred_equiv_refl(p, concat(w1, w2));
    } else {
        let step = steps.first();
        let next = apply_step_pred(p, w2, step).unwrap();
        let rest = steps.drop_first();

        let shifted = shift_step_pred(step, w1.len() as int);
        lemma_pred_single_step_concat_right(p, w1, w2, step, next);
        assert(apply_step_pred(p, concat(w1, w2), shifted) == Some(concat(w1, next)));
        let lifted_d = PredDerivation { steps: Seq::new(1, |_i: int| shifted) };
        assert(lifted_d.steps.first() == shifted);
        assert(lifted_d.steps.drop_first() =~= Seq::<PredDerivationStep>::empty());
        assert(pred_derivation_produces(p, lifted_d.steps.drop_first(), concat(w1, next)) == Some(concat(w1, next)));
        assert(pred_derivation_valid(p, lifted_d, concat(w1, w2), concat(w1, next)));

        lemma_pred_derivation_lift_right(p, rest, w1, next, w2_prime);
        lemma_pred_equiv_transitive(p, concat(w1, w2), concat(w1, next), concat(w1, w2_prime));
    }
}

///  Equivalence respects concatenation on both sides.
pub proof fn lemma_pred_equiv_concat(
    p: PredPresentation, w1: Word, w1_prime: Word, w2: Word, w2_prime: Word,
)
    requires
        equiv_in_pred_presentation(p, w1, w1_prime),
        equiv_in_pred_presentation(p, w2, w2_prime),
    ensures
        equiv_in_pred_presentation(p, concat(w1, w2), concat(w1_prime, w2_prime)),
{
    lemma_pred_equiv_concat_left(p, w1, w1_prime, w2);
    lemma_pred_equiv_concat_right(p, w1_prime, w2, w2_prime);
    lemma_pred_equiv_transitive(p, concat(w1, w2), concat(w1_prime, w2), concat(w1_prime, w2_prime));
}

//  ============================================================
//  Identity and inverses
//  ============================================================

///  The empty word is the identity: w·ε ≡ w.
pub proof fn lemma_pred_concat_identity_right(p: PredPresentation, w: Word)
    ensures
        equiv_in_pred_presentation(p, concat(w, empty_word()), w),
{
    assert(concat(w, empty_word()) =~= w);
    lemma_pred_equiv_refl(p, w);
}

///  ε·w ≡ w.
pub proof fn lemma_pred_concat_identity_left(p: PredPresentation, w: Word)
    ensures
        equiv_in_pred_presentation(p, concat(empty_word(), w), w),
{
    assert(concat(empty_word(), w) =~= w);
    lemma_pred_equiv_refl(p, w);
}

///  A single FreeReduce step as a derivation.
proof fn lemma_pred_free_reduce_step(p: PredPresentation, w: Word, pos: int)
    requires
        has_cancellation_at(w, pos),
    ensures
        equiv_in_pred_presentation(p, w, reduce_at(w, pos)),
{
    let step = PredDerivationStep::FreeReduce { position: pos };
    let w2 = reduce_at(w, pos);
    let d = PredDerivation { steps: Seq::new(1, |_i: int| step) };
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<PredDerivationStep>::empty());
    assert(apply_step_pred(p, w, step) == Some(w2));
    assert(pred_derivation_produces(p, d.steps.drop_first(), w2) == Some(w2));
    assert(pred_derivation_valid(p, d, w, w2));
}

///  w · w⁻¹ ≡ ε (right inverse).
pub proof fn lemma_pred_word_inverse_right(p: PredPresentation, w: Word)
    ensures
        equiv_in_pred_presentation(p, concat(w, inverse_word(w)), empty_word()),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(w =~= empty_word());
        lemma_inverse_empty();
        assert(concat(w, inverse_word(w)) =~= empty_word());
        lemma_pred_equiv_refl(p, empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let s_seq = Seq::new(1, |_i: int| s);
        let s_inv = Seq::new(1, |_i: int| inverse_symbol(s));

        assert(w =~= s_seq + rest);
        assert(inverse_word(w) =~= inverse_word(rest) + s_inv);

        let rest_rest_inv = concat(rest, inverse_word(rest));
        let middle = concat(s_seq, concat(rest_rest_inv, s_inv));
        let s_sinv = concat(s_seq, s_inv);

        let ww_inv = concat(w, inverse_word(w));
        assert(ww_inv =~= middle);

        //  Step 1: rest · rest⁻¹ ≡ ε (IH)
        lemma_pred_word_inverse_right(p, rest);

        //  Step 2: lift through concat
        lemma_pred_equiv_concat_left(p, rest_rest_inv, empty_word(), s_inv);
        lemma_pred_equiv_concat_right(p, s_seq,
            concat(rest_rest_inv, s_inv),
            concat(empty_word(), s_inv),
        );
        assert(concat(s_seq, concat(empty_word(), s_inv)) =~= s_sinv);

        //  Step 3: s · s⁻¹ cancels at 0
        assert(has_cancellation_at(s_sinv, 0));
        assert(reduce_at(s_sinv, 0) =~= empty_word());
        lemma_pred_free_reduce_step(p, s_sinv, 0);

        //  Chain
        lemma_pred_equiv_transitive(p, middle, s_sinv, empty_word());
    }
}

///  w⁻¹ · w ≡ ε (left inverse).
pub proof fn lemma_pred_word_inverse_left(p: PredPresentation, w: Word)
    ensures
        equiv_in_pred_presentation(p, concat(inverse_word(w), w), empty_word()),
    decreases w.len(),
{
    crate::word::lemma_inverse_involution(w);
    lemma_inverse_word_len(w);
    lemma_pred_word_inverse_right(p, inverse_word(w));
    assert(concat(inverse_word(w), inverse_word(inverse_word(w))) =~= concat(inverse_word(w), w));
}

//  ============================================================
//  Relators
//  ============================================================

///  Each accepted relator is equivalent to the identity.  §6a's "trivial"
///  port: the relator is carried as the WORD `r` gated by `(p.relators)(r)`
///  instead of indexed.  The body is the defining closure axiom of a
///  presentation (one RelatorDelete step).
pub proof fn lemma_pred_relator_is_identity(p: PredPresentation, r: Word)
    requires
        (p.relators)(r),
    ensures
        equiv_in_pred_presentation(p, r, empty_word()),
{
    let step = PredDerivationStep::RelatorDelete {
        position: 0,
        relator: r,
        inverted: false,
    };
    let rel = get_relator_pred(r, false);
    assert(rel == r);
    let rlen = rel.len();

    assert(r.subrange(0, 0 + rlen as int) =~= r);
    let result = r.subrange(0, 0int) + r.subrange(0 + rlen as int, r.len() as int);
    assert(result =~= empty_word());

    assert(apply_step_pred(p, r, step) == Some(result));

    let d = PredDerivation { steps: Seq::new(1, |_j: int| step) };
    let steps = d.steps;
    assert(steps.len() == 1);
    assert(steps.first() == step);
    assert(steps.drop_first().len() == 0);
    assert(steps.drop_first() =~= Seq::<PredDerivationStep>::empty());
    assert(pred_derivation_produces(p, steps.drop_first(), result) == Some(result));
    assert(result == empty_word());
    assert(pred_derivation_valid(p, d, r, empty_word()));
}

///  Conjugation: if r is an accepted relator, then w·r·w⁻¹ ≡ ε.
pub proof fn lemma_pred_conjugate_relator_is_identity(p: PredPresentation, w: Word, r: Word)
    requires
        (p.relators)(r),
    ensures
        equiv_in_pred_presentation(
            p,
            concat(concat(w, r), inverse_word(w)),
            empty_word(),
        ),
{
    let w_inv = inverse_word(w);
    let wrw_inv = concat(concat(w, r), w_inv);

    //  Step 1: r ≡ ε
    lemma_pred_relator_is_identity(p, r);

    //  Step 2: concat(r, w_inv) ≡ concat(ε, w_inv)
    lemma_pred_equiv_concat_left(p, r, empty_word(), w_inv);

    //  Step 3: w · concat(r, w_inv) ≡ w · concat(ε, w_inv)
    lemma_pred_equiv_concat_right(p, w, concat(r, w_inv), concat(empty_word(), w_inv));

    assert(wrw_inv =~= concat(w, concat(r, w_inv)));
    assert(concat(w, concat(empty_word(), w_inv)) =~= concat(w, w_inv));

    //  Step 4: w · w⁻¹ ≡ ε
    lemma_pred_word_inverse_right(p, w);

    //  Chain
    lemma_pred_equiv_transitive(p, wrw_inv, concat(w, w_inv), empty_word());
}

//  ============================================================
//  Group axioms
//  ============================================================

///  Associativity is definitional (Seq concatenation is associative).
pub proof fn lemma_pred_group_associative(p: PredPresentation, w1: Word, w2: Word, w3: Word)
    ensures
        equiv_in_pred_presentation(
            p,
            concat(concat(w1, w2), w3),
            concat(w1, concat(w2, w3)),
        ),
{
    lemma_concat_assoc(w1, w2, w3);
    assert(concat(concat(w1, w2), w3) =~= concat(w1, concat(w2, w3)));
    lemma_pred_equiv_refl(p, concat(w1, concat(w2, w3)));
}

} //  verus!
