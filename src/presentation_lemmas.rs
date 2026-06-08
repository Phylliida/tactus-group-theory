use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;

verus! {

//  ============================================================
//  Equivalence respects group operations
//  ============================================================

///  A single derivation step on the left part of a concatenation.
///  If apply_step(p, w1, step) = Some(w1'), then applying the same step
///  to concat(w1, w2) gives concat(w1', w2).
proof fn lemma_single_step_concat_left(p: Presentation, w1: Word, w2: Word, step: DerivationStep, w1_prime: Word)
    requires
        apply_step(p, w1, step) == Some(w1_prime),
    ensures
        apply_step(p, concat(w1, w2), step) == Some(concat(w1_prime, w2)),
{
    let cw = concat(w1, w2);
    match step {
        DerivationStep::FreeReduce { position } => {
            //  position is within w1 (has_cancellation_at(w1, position) requires position < w1.len()-1)
            assert(has_cancellation_at(w1, position));
            //  cw[position] == w1[position], cw[position+1] == w1[position+1]
            assert(cw[position] == w1[position]);
            assert(cw[position + 1] == w1[position + 1]);
            assert(has_cancellation_at(cw, position));
            //  reduce_at(cw, position) == reduce_at(w1, position) ++ w2
            assert(reduce_at(cw, position) =~= concat(reduce_at(w1, position), w2));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  0 <= position <= w1.len(), so position <= cw.len()
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(cw.subrange(0, position) =~= w1.subrange(0, position));
            assert(cw.subrange(position, cw.len() as int) =~= w1.subrange(position, w1.len() as int) + w2);
            assert(cw.subrange(0, position) + pair + cw.subrange(position, cw.len() as int) =~=
                concat(w1.subrange(0, position) + pair + w1.subrange(position, w1.len() as int), w2));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert(cw.subrange(0, position) =~= w1.subrange(0, position));
            assert(cw.subrange(position, cw.len() as int) =~= w1.subrange(position, w1.len() as int) + w2);
            assert(cw.subrange(0, position) + r + cw.subrange(position, cw.len() as int) =~=
                concat(w1.subrange(0, position) + r + w1.subrange(position, w1.len() as int), w2));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            let rlen = r.len();
            //  The relator is entirely within w1
            assert(w1.subrange(position, position + rlen as int) == r);
            assert(cw.subrange(position, position + rlen as int) =~= r);
            assert(cw.subrange(0, position) + cw.subrange(position + rlen as int, cw.len() as int) =~=
                concat(w1.subrange(0, position) + w1.subrange(position + rlen as int, w1.len() as int), w2));
        },
    }
}

///  If w1 ≡ w1' then w1·w2 ≡ w1'·w2.
pub proof fn lemma_equiv_concat_left(p: Presentation, w1: Word, w1_prime: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w1_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2)),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w1_prime);
    lemma_derivation_lift_left(p, d.steps, w1, w1_prime, w2);
}

///  Lift an entire derivation to the left of a concatenation.
proof fn lemma_derivation_lift_left(
    p: Presentation, steps: Seq<DerivationStep>,
    w1: Word, w1_prime: Word, w2: Word,
)
    requires
        derivation_produces(p, steps, w1) == Some(w1_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w1 == w1_prime);
        lemma_equiv_refl(p, concat(w1, w2));
    } else {
        let step = steps.first();
        let next = apply_step(p, w1, step).unwrap();
        let rest = steps.drop_first();

        //  Lift this single step
        lemma_single_step_concat_left(p, w1, w2, step, next);
        let lifted_step = step;
        assert(apply_step(p, concat(w1, w2), lifted_step) == Some(concat(next, w2)));
        let lifted_d = Derivation { steps: Seq::new(1, |_i: int| lifted_step) };
        assert(lifted_d.steps.first() == lifted_step);
        assert(lifted_d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(p, lifted_d.steps.drop_first(), concat(next, w2)) == Some(concat(next, w2)));
        assert(derivation_valid(p, lifted_d, concat(w1, w2), concat(next, w2)));

        //  Recurse on rest
        lemma_derivation_lift_left(p, rest, next, w1_prime, w2);

        //  Chain: concat(w1, w2) ≡ concat(next, w2) ≡ concat(w1_prime, w2)
        lemma_equiv_transitive(p, concat(w1, w2), concat(next, w2), concat(w1_prime, w2));
    }
}

///  Shift a derivation step's position by an offset (for right-concat lifting).
pub open spec fn shift_step(step: DerivationStep, offset: int) -> DerivationStep {
    match step {
        DerivationStep::FreeReduce { position } =>
            DerivationStep::FreeReduce { position: position + offset },
        DerivationStep::FreeExpand { position, symbol } =>
            DerivationStep::FreeExpand { position: position + offset, symbol },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            DerivationStep::RelatorInsert { position: position + offset, relator_index, inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            DerivationStep::RelatorDelete { position: position + offset, relator_index, inverted },
    }
}

///  A single derivation step on the right part of a concatenation.
proof fn lemma_single_step_concat_right(p: Presentation, w1: Word, w2: Word, step: DerivationStep, w2_prime: Word)
    requires
        apply_step(p, w2, step) == Some(w2_prime),
    ensures
        apply_step(p, concat(w1, w2), shift_step(step, w1.len() as int)) == Some(concat(w1, w2_prime)),
{
    let cw = concat(w1, w2);
    let offset = w1.len() as int;
    match step {
        DerivationStep::FreeReduce { position } => {
            assert(has_cancellation_at(w2, position));
            assert(cw[position + offset] == w2[position]);
            assert(cw[position + offset + 1] == w2[position + 1]);
            assert(has_cancellation_at(cw, position + offset));
            assert(reduce_at(cw, position + offset) =~= concat(w1, reduce_at(w2, position)));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(cw.subrange(0, position + offset) =~= w1 + w2.subrange(0, position));
            assert(cw.subrange(position + offset, cw.len() as int) =~= w2.subrange(position, w2.len() as int));
            assert(cw.subrange(0, position + offset) + pair + cw.subrange(position + offset, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + pair + w2.subrange(position, w2.len() as int)));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert(cw.subrange(0, position + offset) =~= w1 + w2.subrange(0, position));
            assert(cw.subrange(position + offset, cw.len() as int) =~= w2.subrange(position, w2.len() as int));
            assert(cw.subrange(0, position + offset) + r + cw.subrange(position + offset, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + r + w2.subrange(position, w2.len() as int)));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            let rlen = r.len();
            assert(w2.subrange(position, position + rlen as int) == r);
            assert(cw.subrange(position + offset, position + offset + rlen as int) =~= r);
            assert(cw.subrange(0, position + offset) + cw.subrange(position + offset + rlen as int, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + w2.subrange(position + rlen as int, w2.len() as int)));
        },
    }
}

///  If w2 ≡ w2' then w1·w2 ≡ w1·w2'.
pub proof fn lemma_equiv_concat_right(p: Presentation, w1: Word, w2: Word, w2_prime: Word)
    requires
        equiv_in_presentation(p, w2, w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1, w2_prime)),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w2, w2_prime);
    lemma_derivation_lift_right(p, d.steps, w1, w2, w2_prime);
}

///  Lift an entire derivation to the right of a concatenation.
proof fn lemma_derivation_lift_right(
    p: Presentation, steps: Seq<DerivationStep>,
    w1: Word, w2: Word, w2_prime: Word,
)
    requires
        derivation_produces(p, steps, w2) == Some(w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1, w2_prime)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w2 == w2_prime);
        lemma_equiv_refl(p, concat(w1, w2));
    } else {
        let step = steps.first();
        let next = apply_step(p, w2, step).unwrap();
        let rest = steps.drop_first();

        let shifted = shift_step(step, w1.len() as int);
        lemma_single_step_concat_right(p, w1, w2, step, next);
        assert(apply_step(p, concat(w1, w2), shifted) == Some(concat(w1, next)));
        let lifted_d = Derivation { steps: Seq::new(1, |_i: int| shifted) };
        assert(lifted_d.steps.first() == shifted);
        assert(lifted_d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(p, lifted_d.steps.drop_first(), concat(w1, next)) == Some(concat(w1, next)));
        assert(derivation_valid(p, lifted_d, concat(w1, w2), concat(w1, next)));

        lemma_derivation_lift_right(p, rest, w1, next, w2_prime);
        lemma_equiv_transitive(p, concat(w1, w2), concat(w1, next), concat(w1, w2_prime));
    }
}

///  Equivalence respects concatenation on both sides.
pub proof fn lemma_equiv_concat(
    p: Presentation, w1: Word, w1_prime: Word, w2: Word, w2_prime: Word,
)
    requires
        equiv_in_presentation(p, w1, w1_prime),
        equiv_in_presentation(p, w2, w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2_prime)),
{
    lemma_equiv_concat_left(p, w1, w1_prime, w2);
    lemma_equiv_concat_right(p, w1_prime, w2, w2_prime);
    lemma_equiv_transitive(p, concat(w1, w2), concat(w1_prime, w2), concat(w1_prime, w2_prime));
}

//  ============================================================
//  Identity and inverses
//  ============================================================

///  The empty word is the identity: w·ε ≡ w.
pub proof fn lemma_concat_identity_right(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(w, empty_word()), w),
{
    assert(concat(w, empty_word()) =~= w);
    lemma_equiv_refl(p, w);
}

///  ε·w ≡ w.
pub proof fn lemma_concat_identity_left(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(empty_word(), w), w),
{
    assert(concat(empty_word(), w) =~= w);
    lemma_equiv_refl(p, w);
}

///  A single FreeReduce step as a derivation.
proof fn lemma_free_reduce_step(p: Presentation, w: Word, pos: int)
    requires
        has_cancellation_at(w, pos),
    ensures
        equiv_in_presentation(p, w, reduce_at(w, pos)),
{
    let step = DerivationStep::FreeReduce { position: pos };
    let w2 = reduce_at(w, pos);
    let d = Derivation { steps: Seq::new(1, |_i: int| step) };
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(apply_step(p, w, step) == Some(w2));
    assert(derivation_produces(p, d.steps.drop_first(), w2) == Some(w2));
    assert(derivation_valid(p, d, w, w2));
}

///  w · w⁻¹ ≡ ε (right inverse).
///
///  Base: ε · ε⁻¹ = ε ≡ ε
///  Step: w = s · rest, so w⁻¹ = rest⁻¹ · s⁻¹
///    w · w⁻¹ = s · rest · rest⁻¹ · s⁻¹
///    Step 1: rest · rest⁻¹ ≡ ε (IH)
///    Step 2: s · (rest · rest⁻¹) · s⁻¹ ≡ s · ε · s⁻¹ = s · s⁻¹ (by concat lifting)
///    Step 3: s · s⁻¹ ≡ ε (free reduction)
pub proof fn lemma_word_inverse_right(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(w, inverse_word(w)), empty_word()),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(w =~= empty_word());
        lemma_inverse_empty();
        assert(concat(w, inverse_word(w)) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let s_seq = Seq::new(1, |_i: int| s);
        let s_inv = Seq::new(1, |_i: int| inverse_symbol(s));

        //  Establish key equalities
        assert(w =~= s_seq + rest);
        assert(inverse_word(w) =~= inverse_word(rest) + s_inv);

        //  Name the intermediate words
        let rest_rest_inv = concat(rest, inverse_word(rest));  //  rest · rest⁻¹
        let middle = concat(s_seq, concat(rest_rest_inv, s_inv)); //  s · (rest·rest⁻¹) · s⁻¹
        let s_sinv = concat(s_seq, s_inv); //  s · s⁻¹

        //  ww_inv =~= middle (just reassociation)
        let ww_inv = concat(w, inverse_word(w));
        assert(ww_inv =~= middle);

        //  Step 1: rest · rest⁻¹ ≡ ε (IH)
        lemma_word_inverse_right(p, rest);

        //  Step 2: concat(rest_rest_inv, s_inv) ≡ concat(empty, s_inv)
        lemma_equiv_concat_left(p, rest_rest_inv, empty_word(), s_inv);
        //  → concat(s_seq, concat(rest_rest_inv, s_inv)) ≡ concat(s_seq, concat(empty, s_inv))
        lemma_equiv_concat_right(p, s_seq,
            concat(rest_rest_inv, s_inv),
            concat(empty_word(), s_inv),
        );
        //  middle ≡ concat(s_seq, concat(empty, s_inv))
        //  concat(s_seq, concat(empty, s_inv)) =~= s_sinv
        assert(concat(s_seq, concat(empty_word(), s_inv)) =~= s_sinv);

        //  Step 3: s · s⁻¹ has a cancellation at 0
        assert(has_cancellation_at(s_sinv, 0));
        assert(reduce_at(s_sinv, 0) =~= empty_word());
        lemma_free_reduce_step(p, s_sinv, 0);

        //  Chain: ww_inv ≡ middle ≡ s_sinv ≡ ε
        lemma_equiv_transitive(p, middle, s_sinv, empty_word());
    }
}

///  w⁻¹ · w ≡ ε (left inverse).
pub proof fn lemma_word_inverse_left(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(inverse_word(w), w), empty_word()),
    decreases w.len(),
{
    //  inverse_word(w) · w ≡ ε
    //  Use: inverse_word(inverse_word(w)) =~= w
    //  So this is: inverse_word(w) · inverse_word(inverse_word(w)) ≡ ε
    //  Which is the right inverse for inverse_word(w)
    crate::word::lemma_inverse_involution(w);
    lemma_inverse_word_len(w);
    lemma_word_inverse_right(p, inverse_word(w));
    //  inverse_word(w) · inverse_word(inverse_word(w)) ≡ ε
    //  but inverse_word(inverse_word(w)) =~= w
    assert(concat(inverse_word(w), inverse_word(inverse_word(w))) =~= concat(inverse_word(w), w));
}

//  ============================================================
//  Relators
//  ============================================================

///  Each relator is equivalent to the identity.
pub proof fn lemma_relator_is_identity(p: Presentation, i: int)
    requires
        0 <= i < p.relators.len(),
    ensures
        equiv_in_presentation(p, p.relators[i], empty_word()),
{
    let r = p.relators[i];
    let step = DerivationStep::RelatorDelete {
        position: 0,
        relator_index: i as nat,
        inverted: false,
    };
    let rel = get_relator(p, i as nat, false);
    assert(rel == r);
    let rlen = rel.len();

    //  The key check in apply_step: w.subrange(position, position + rlen) == rel
    //  Here w = r, position = 0, so r.subrange(0, rlen) == r
    assert(r.subrange(0, 0 + rlen as int) =~= r);
    //  Result: r.subrange(0, 0) + r.subrange(0 + rlen, r.len()) = empty
    let result = r.subrange(0, 0int) + r.subrange(0 + rlen as int, r.len() as int);
    assert(result =~= empty_word());

    assert(apply_step(p, r, step) == Some(result));

    let d = Derivation { steps: Seq::new(1, |_j: int| step) };
    let steps = d.steps;
    assert(steps.len() == 1);
    assert(steps.first() == step);
    assert(steps.drop_first().len() == 0);
    assert(steps.drop_first() =~= Seq::<DerivationStep>::empty());
    //  Unfold: derivation_produces(p, steps, r)
    //    = match apply_step(p, r, step) { Some(next) => derivation_produces(p, rest, next) }
    //    = match Some(result) { Some(result) => derivation_produces(p, empty, result) }
    //    = Some(result)
    assert(derivation_produces(p, steps.drop_first(), result) == Some(result));
    //  result =~= empty_word(), so result == empty_word() for Seq
    assert(result == empty_word());
    assert(derivation_valid(p, d, r, empty_word()));
}

///  Conjugation: if r is a relator, then w·r·w⁻¹ ≡ ε.
pub proof fn lemma_conjugate_relator_is_identity(p: Presentation, w: Word, i: int)
    requires
        0 <= i < p.relators.len(),
    ensures
        equiv_in_presentation(
            p,
            concat(concat(w, p.relators[i]), inverse_word(w)),
            empty_word(),
        ),
{
    let r = p.relators[i];
    let w_inv = inverse_word(w);
    let wrw_inv = concat(concat(w, r), w_inv);

    //  Step 1: r ≡ ε
    lemma_relator_is_identity(p, i);

    //  Step 2: concat(r, w_inv) ≡ concat(ε, w_inv)
    lemma_equiv_concat_left(p, r, empty_word(), w_inv);

    //  Step 3: w · concat(r, w_inv) ≡ w · concat(ε, w_inv)
    lemma_equiv_concat_right(p, w, concat(r, w_inv), concat(empty_word(), w_inv));

    //  Reassociate: wrw_inv = concat(concat(w, r), w_inv) =~= concat(w, concat(r, w_inv))
    assert(wrw_inv =~= concat(w, concat(r, w_inv)));
    //  and concat(w, concat(ε, w_inv)) =~= concat(w, w_inv)
    assert(concat(w, concat(empty_word(), w_inv)) =~= concat(w, w_inv));

    //  Step 4: w · w⁻¹ ≡ ε
    lemma_word_inverse_right(p, w);

    //  Chain: wrw_inv ≡ concat(w, w_inv) ≡ ε
    lemma_equiv_transitive(p, wrw_inv, concat(w, w_inv), empty_word());
}

//  ============================================================
//  The presented group is indeed a group
//  ============================================================

///  Summary: the quotient Free(S)/⟨⟨R⟩⟩ satisfies the group axioms:
///  - Associativity: (w1·w2)·w3 ≡ w1·(w2·w3)      (follows from Seq concat assoc)
///  - Identity: ε·w ≡ w ≡ w·ε                        (above)
///  - Inverses: w·w⁻¹ ≡ ε ≡ w⁻¹·w                   (above)
///  - Closure: concat and inverse_word are total      (by construction)
///  - Well-defined: equiv respects concat             (above)

///  Associativity is definitional (Seq concatenation is associative).
pub proof fn lemma_group_associative(p: Presentation, w1: Word, w2: Word, w3: Word)
    ensures
        equiv_in_presentation(
            p,
            concat(concat(w1, w2), w3),
            concat(w1, concat(w2, w3)),
        ),
{
    lemma_concat_assoc(w1, w2, w3);
    //  They're extensionally equal, so trivially equivalent
    assert(concat(concat(w1, w2), w3) =~= concat(w1, concat(w2, w3)));
    lemma_equiv_refl(p, concat(w1, concat(w2, w3)));
}

//  ============================================================
//  Quotient Presentations
//  ============================================================

///  A presentation p' extends p: same generators, relators are p's relators plus extras.
pub open spec fn extends_presentation(p: Presentation, p_prime: Presentation) -> bool {
    p_prime.num_generators == p.num_generators
    && p.relators.len() <= p_prime.relators.len()
    && p_prime.relators.subrange(0, p.relators.len() as int) == p.relators
}

///  A single derivation step valid in p is also valid in any extension p'.
pub proof fn lemma_step_valid_in_extension(
    p: Presentation, p_prime: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        extends_presentation(p, p_prime),
        apply_step(p, w, step) == Some(w_prime),
    ensures
        apply_step(p_prime, w, step) == Some(w_prime),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            //  FreeReduce doesn't depend on the presentation
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  FreeExpand doesn't depend on the presentation
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            //  relator_index < p.relators.len() <= p_prime.relators.len()
            //  p_prime.relators[relator_index] == p.relators[relator_index]
            assert(0 <= relator_index < p.relators.len());
            assert(p_prime.relators[relator_index as int] == p.relators[relator_index as int]);
            assert(get_relator(p_prime, relator_index, inverted) == get_relator(p, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p.relators.len());
            assert(p_prime.relators[relator_index as int] == p.relators[relator_index as int]);
            assert(get_relator(p_prime, relator_index, inverted) == get_relator(p, relator_index, inverted));
        },
    }
}

///  A derivation valid in p is also valid in any extension p'.
pub proof fn lemma_derivation_valid_in_extension(
    p: Presentation, p_prime: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        extends_presentation(p, p_prime),
        derivation_produces(p, steps, w1) == Some(w2),
    ensures
        derivation_produces(p_prime, steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step(p, w1, step).unwrap();
        lemma_step_valid_in_extension(p, p_prime, w1, step, next);
        lemma_derivation_valid_in_extension(p, p_prime, steps.drop_first(), next, w2);
    }
}

///  Adding relators preserves equivalence: if w1 ≡ w2 in p, then w1 ≡ w2 in any extension p'.
pub proof fn lemma_quotient_preserves_equiv(
    p: Presentation, p_prime: Presentation,
    w1: Word, w2: Word,
)
    requires
        extends_presentation(p, p_prime),
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(p_prime, w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_derivation_valid_in_extension(p, p_prime, d.steps, w1, w2);
    let d_prime = Derivation { steps: d.steps };
    assert(derivation_valid(p_prime, d_prime, w1, w2));
}

//  ============================================================
//  Relator inclusion (generalization of extends_presentation)
//  ============================================================

///  Every relator of p1 appears somewhere in p2's relators.
pub open spec fn relators_included(p1: Presentation, p2: Presentation) -> bool {
    p1.num_generators == p2.num_generators &&
    forall|i: int| 0 <= i < p1.relators.len() ==>
        exists|j: int| 0 <= j < p2.relators.len() &&
            p2.relators[j] == #[trigger] p1.relators[i]
}

///  Re-index a derivation step from p1 to p2 using relator inclusion.
pub open spec fn reindex_step(p1: Presentation, p2: Presentation, step: DerivationStep) -> DerivationStep {
    match step {
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            DerivationStep::RelatorInsert { position, relator_index: j as nat, inverted }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            DerivationStep::RelatorDelete { position, relator_index: j as nat, inverted }
        },
        _ => step,
    }
}

///  A single derivation step valid in p1 can be replayed in p2
///  when relators are included.
pub proof fn lemma_step_valid_with_inclusion(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        relators_included(p1, p2),
        apply_step(p1, w, step) == Some(w_prime),
    ensures
        apply_step(p2, w, reindex_step(p1, p2, step)) == Some(w_prime),
{
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {},
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            assert(get_relator(p2, j as nat, inverted)
                == get_relator(p1, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            assert(get_relator(p2, j as nat, inverted)
                == get_relator(p1, relator_index, inverted));
        },
    }
}

///  Re-index a sequence of derivation steps.
pub open spec fn reindex_steps(p1: Presentation, p2: Presentation, steps: Seq<DerivationStep>) -> Seq<DerivationStep> {
    Seq::new(steps.len(), |i: int| reindex_step(p1, p2, steps[i]))
}

///  A valid derivation in p1 can be replayed in p2 when relators are included.
pub proof fn lemma_derivation_valid_with_inclusion(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        relators_included(p1, p2),
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(p2, reindex_steps(p1, p2, steps), w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(reindex_steps(p1, p2, steps) =~= Seq::<DerivationStep>::empty());
    } else {
        let step = steps.first();
        let next = apply_step(p1, w1, step).unwrap();
        lemma_step_valid_with_inclusion(p1, p2, w1, step, next);

        let new_steps = reindex_steps(p1, p2, steps);
        assert(new_steps.first() == reindex_step(p1, p2, step));
        assert(apply_step(p2, w1, new_steps.first()) == Some(next));

        let tail = steps.drop_first();
        lemma_derivation_valid_with_inclusion(p1, p2, tail, next, w2);

        assert(new_steps.drop_first() =~= reindex_steps(p1, p2, tail));
    }
}

///  Equivalence transfers from p1 to p2 when relators are included.
pub proof fn lemma_relator_inclusion_preserves_equiv(
    p1: Presentation, p2: Presentation,
    w1: Word, w2: Word,
)
    requires
        relators_included(p1, p2),
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(p2, w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_with_inclusion(p1, p2, d.steps, w1, w2);
    let d2 = Derivation { steps: reindex_steps(p1, p2, d.steps) };
    assert(derivation_valid(p2, d2, w1, w2));
}

//  ============================================================
//  Bridge: free reduction → presentation equivalence
//  ============================================================

///  A single free reduction step implies presentation equivalence.
///  reduce_at(w, i) IS apply_step(p, w, FreeReduce{position: i}).
proof fn lemma_reduces_one_step_equiv(p: Presentation, w1: Word, w2: Word)
    requires
        reduces_one_step(w1, w2),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let i = choose|i: int| has_cancellation_at(w1, i) && w2 == reduce_at(w1, i);
    lemma_free_reduce_step(p, w1, i);
}

///  Multi-step free reduction implies presentation equivalence (induction on n).
proof fn lemma_reduces_in_steps_equiv(p: Presentation, w1: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w2, n),
    ensures
        equiv_in_presentation(p, w1, w2),
    decreases n,
{
    if n == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(p, w1);
    } else {
        if w1 == w2 {
            lemma_equiv_refl(p, w1);
        } else {
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
            lemma_reduces_one_step_equiv(p, w1, w_mid);
            lemma_reduces_in_steps_equiv(p, w_mid, w2, (n - 1) as nat);
            lemma_equiv_transitive(p, w1, w_mid, w2);
        }
    }
}

///  Free reduction implies presentation equivalence.
pub proof fn lemma_reduces_to_equiv(p: Presentation, w1: Word, w2: Word)
    requires
        reduces_to(w1, w2),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let n = choose|n: nat| reduces_in_steps(w1, w2, n);
    lemma_reduces_in_steps_equiv(p, w1, w2, n);
}

///  Free equivalence implies presentation equivalence.
///  freely_equivalent(w1, w2) means ∃ w. w1 →* w ←* w2.
///  Both directions give equiv_in_presentation, then symmetry + transitivity.
pub proof fn lemma_freely_equivalent_implies_equiv(p: Presentation, w1: Word, w2: Word)
    requires
        freely_equivalent(w1, w2),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let w = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    //  w1 →* w  ⟹  w1 ≡ w in presentation
    lemma_reduces_to_equiv(p, w1, w);
    //  w2 →* w  ⟹  w2 ≡ w in presentation
    lemma_reduces_to_equiv(p, w2, w);
    //  w ≡ w2 by symmetry (needs word_valid(w2) + presentation_valid)
    lemma_equiv_symmetric(p, w2, w);
    //  w1 ≡ w ≡ w2 by transitivity... wait, we have w1 ≡ w and w ≡ w2
    //  Hmm, we have equiv(w1, w) and equiv(w, w2) — but for symmetry we need word_valid(w2).
    //  Actually: we have equiv(w2, w). To get equiv(w, w2) we need symmetry on w2.
    //  lemma_equiv_symmetric requires word_valid(w2) which we have.
    lemma_equiv_transitive(p, w1, w, w2);
}

} //  verus!
