use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;

verus! {

//  ============================================================
//  Free Products of Presented Groups
//  ============================================================

///  Shift a symbol's generator index by an offset.
///  Gen(i) → Gen(i + offset), Inv(i) → Inv(i + offset).
pub open spec fn shift_symbol(s: Symbol, offset: nat) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Gen(i + offset),
        Symbol::Inv(i) => Symbol::Inv(i + offset),
    }
}

///  Shift every symbol in a word by an offset.
pub open spec fn shift_word(w: Word, offset: nat) -> Word {
    Seq::new(w.len(), |i: int| shift_symbol(w[i], offset))
}

///  Shift every word in a sequence of relators.
pub open spec fn shift_relators(relators: Seq<Word>, offset: nat) -> Seq<Word> {
    Seq::new(relators.len(), |i: int| shift_word(relators[i], offset))
}

///  The free product of two presentations.
///  Generators: p1's generators (0..n1-1) and p2's generators (n1..n1+n2-1).
///  Relators: p1's relators followed by p2's relators (shifted).
pub open spec fn free_product(p1: Presentation, p2: Presentation) -> Presentation {
    Presentation {
        num_generators: p1.num_generators + p2.num_generators,
        relators: p1.relators + shift_relators(p2.relators, p1.num_generators),
    }
}

///  A word uses only generators from p1 (indices < p1.num_generators).
pub open spec fn word_in_left(w: Word, p1: Presentation) -> bool {
    forall|i: int| 0 <= i < w.len() ==> generator_index(#[trigger] w[i]) < p1.num_generators
}

///  A word uses only generators from p2 (indices >= p1.num_generators).
pub open spec fn word_in_right(w: Word, p1: Presentation, p2: Presentation) -> bool {
    forall|i: int| 0 <= i < w.len() ==>
        p1.num_generators <= generator_index(#[trigger] w[i])
        && generator_index(w[i]) < p1.num_generators + p2.num_generators
}

//  ============================================================
//  Shift lemmas
//  ============================================================

///  Shifting preserves inverse pair relationships.
pub proof fn lemma_shift_preserves_inverse_pair(s1: Symbol, s2: Symbol, offset: nat)
    ensures
        is_inverse_pair(s1, s2) == is_inverse_pair(shift_symbol(s1, offset), shift_symbol(s2, offset)),
{
}

///  Shifting a word preserves its length.
pub proof fn lemma_shift_word_len(w: Word, offset: nat)
    ensures
        shift_word(w, offset).len() == w.len(),
{
}

///  Shifting preserves cancellations.
pub proof fn lemma_shift_preserves_cancellation(w: Word, offset: nat, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        has_cancellation_at(shift_word(w, offset), i),
{
    let sw = shift_word(w, offset);
    assert(sw[i] == shift_symbol(w[i], offset));
    assert(sw[i + 1] == shift_symbol(w[i + 1], offset));
    lemma_shift_preserves_inverse_pair(w[i], w[i + 1], offset);
}

///  reduce_at commutes with shifting.
pub proof fn lemma_shift_reduce_at(w: Word, offset: nat, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        shift_word(reduce_at(w, i), offset) =~= reduce_at(shift_word(w, offset), i),
{
    lemma_shift_preserves_cancellation(w, offset, i);
    lemma_reduce_at_len(w, i);
    lemma_reduce_at_elements(w, i);
    let sw = shift_word(w, offset);
    lemma_reduce_at_len(sw, i);
    lemma_reduce_at_elements(sw, i);
    let lhs = shift_word(reduce_at(w, i), offset);
    let rhs = reduce_at(sw, i);
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies #[trigger] lhs[k] == rhs[k] by {
        if k < i {
            assert(lhs[k] == shift_symbol(reduce_at(w, i)[k], offset));
            assert(reduce_at(w, i)[k] == w[k]);
            assert(rhs[k] == sw[k]);
            assert(sw[k] == shift_symbol(w[k], offset));
        } else {
            assert(lhs[k] == shift_symbol(reduce_at(w, i)[k], offset));
            assert(reduce_at(w, i)[k] == w[k + 2]);
            assert(rhs[k] == sw[k + 2]);
            assert(sw[k + 2] == shift_symbol(w[k + 2], offset));
        }
    };
}

///  Shifting distributes over concatenation.
pub proof fn lemma_shift_concat(w1: Word, w2: Word, offset: nat)
    ensures
        shift_word(concat(w1, w2), offset) =~= concat(shift_word(w1, offset), shift_word(w2, offset)),
{
    let lhs = shift_word(concat(w1, w2), offset);
    let rhs = concat(shift_word(w1, offset), shift_word(w2, offset));
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies #[trigger] lhs[k] == rhs[k] by {
        if k < w1.len() {
            assert(lhs[k] == shift_symbol(concat(w1, w2)[k], offset));
            assert(concat(w1, w2)[k] == w1[k]);
            assert(rhs[k] == shift_word(w1, offset)[k]);
        } else {
            assert(lhs[k] == shift_symbol(concat(w1, w2)[k], offset));
            assert(concat(w1, w2)[k] == w2[k - w1.len()]);
            assert(rhs[k] == shift_word(w2, offset)[k - w1.len()]);
        }
    };
}

///  Shifting distributes over word inversion.
pub proof fn lemma_shift_inverse_word(w: Word, offset: nat)
    ensures
        shift_word(inverse_word(w), offset) =~= inverse_word(shift_word(w, offset)),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(shift_word(inverse_word(w), offset) =~= Seq::<Symbol>::empty());
        assert(inverse_word(shift_word(w, offset)) =~= Seq::<Symbol>::empty());
    } else {
        let first = w.first();
        let rest = w.drop_first();
        lemma_shift_inverse_word(rest, offset);

        let sw = shift_word(w, offset);
        assert(sw.first() == shift_symbol(first, offset));
        assert(sw.drop_first() =~= shift_word(rest, offset));
        assert(shift_symbol(inverse_symbol(first), offset) == inverse_symbol(shift_symbol(first, offset)));

        lemma_shift_concat(
            inverse_word(rest),
            Seq::new(1, |_i: int| inverse_symbol(first)),
            offset,
        );

        lemma_inverse_word_len(rest);
        assert(shift_word(Seq::new(1, |_i: int| inverse_symbol(first)), offset) =~=
            Seq::new(1, |_i: int| inverse_symbol(shift_symbol(first, offset))));
        assert(shift_word(inverse_word(rest), offset) =~= inverse_word(shift_word(rest, offset)));
    }
}

//  ============================================================
//  Left Embedding
//  ============================================================

///  A derivation step valid in p1 is also valid in free_product(p1, p2).
///  apply_step doesn't check num_generators, only relator indices.
///  p1's relators are at the same indices in fp.
proof fn lemma_step_valid_in_free_product_left(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        apply_step(p1, w, step) == Some(w_prime),
    ensures
        apply_step(free_product(p1, p2), w, step) == Some(w_prime),
{
    let fp = free_product(p1, p2);
    match step {
        DerivationStep::FreeReduce { position } => {
            //  Doesn't use relators
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  Doesn't use relators
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
            assert(get_relator(fp, relator_index, inverted) == get_relator(p1, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
            assert(get_relator(fp, relator_index, inverted) == get_relator(p1, relator_index, inverted));
        },
    }
}

///  A derivation valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_derivation_valid_in_free_product_left(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(free_product(p1, p2), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step(p1, w1, step).unwrap();
        lemma_step_valid_in_free_product_left(p1, p2, w1, step, next);
        lemma_derivation_valid_in_free_product_left(p1, p2, steps.drop_first(), next, w2);
    }
}

///  Left embedding: equivalence in p1 implies equivalence in free_product(p1, p2).
pub proof fn lemma_left_embeds(p1: Presentation, p2: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(free_product(p1, p2), w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_in_free_product_left(p1, p2, d.steps, w1, w2);
    let d_fp = Derivation { steps: d.steps };
    assert(derivation_valid(free_product(p1, p2), d_fp, w1, w2));
}

//  ============================================================
//  Right Embedding
//  ============================================================

///  Shift a derivation step: shift symbols by offset, shift relator indices by relator_offset.
pub open spec fn shift_derivation_step(step: DerivationStep, offset: nat, relator_offset: nat) -> DerivationStep {
    match step {
        DerivationStep::FreeReduce { position } =>
            DerivationStep::FreeReduce { position },
        DerivationStep::FreeExpand { position, symbol } =>
            DerivationStep::FreeExpand { position, symbol: shift_symbol(symbol, offset) },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            DerivationStep::RelatorInsert { position, relator_index: relator_index + relator_offset, inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            DerivationStep::RelatorDelete { position, relator_index: relator_index + relator_offset, inverted },
    }
}

///  A shifted derivation step on a shifted word produces a shifted result in the free product.
proof fn lemma_shifted_step_valid(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        apply_step(p2, w, step) == Some(w_prime),
    ensures
        apply_step(
            free_product(p1, p2),
            shift_word(w, p1.num_generators),
            shift_derivation_step(step, p1.num_generators, p1.relators.len()),
        ) == Some(shift_word(w_prime, p1.num_generators)),
{
    let fp = free_product(p1, p2);
    let offset = p1.num_generators;
    let roff = p1.relators.len();
    let sw = shift_word(w, offset);
    match step {
        DerivationStep::FreeReduce { position } => {
            assert(has_cancellation_at(w, position));
            lemma_shift_preserves_cancellation(w, offset, position);
            lemma_shift_reduce_at(w, offset, position);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let ss = shift_symbol(symbol, offset);
            let pair_shifted = Seq::new(1, |_i: int| ss) + Seq::new(1, |_i: int| inverse_symbol(ss));
            assert(shift_symbol(inverse_symbol(symbol), offset) == inverse_symbol(shift_symbol(symbol, offset)));
            assert(sw.subrange(0, position) =~= shift_word(w.subrange(0, position), offset));
            assert(sw.subrange(position, sw.len() as int) =~= shift_word(w.subrange(position, w.len() as int), offset));
            assert(sw.subrange(0, position) + pair_shifted + sw.subrange(position, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p2, relator_index, inverted);
            let shifted_idx = relator_index + roff;
            //  fp.relators[shifted_idx] == shift_word(p2.relators[relator_index], offset)
            assert(fp.relators[shifted_idx as int] == shift_word(p2.relators[relator_index as int], offset));
            let r_fp = get_relator(fp, shifted_idx, inverted);
            if inverted {
                lemma_shift_inverse_word(p2.relators[relator_index as int], offset);
            }
            assert(r_fp =~= shift_word(r, offset));

            assert(sw.subrange(0, position) =~= shift_word(w.subrange(0, position), offset));
            assert(sw.subrange(position, sw.len() as int) =~= shift_word(w.subrange(position, w.len() as int), offset));
            assert(sw.subrange(0, position) + r_fp + sw.subrange(position, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p2, relator_index, inverted);
            let rlen = r.len();
            let shifted_idx = relator_index + roff;
            assert(fp.relators[shifted_idx as int] == shift_word(p2.relators[relator_index as int], offset));
            let r_fp = get_relator(fp, shifted_idx, inverted);
            if inverted {
                lemma_shift_inverse_word(p2.relators[relator_index as int], offset);
            }
            assert(r_fp =~= shift_word(r, offset));

            lemma_shift_word_len(r, offset);
            assert(r_fp.len() == rlen);

            assert(sw.subrange(position, position + rlen as int) =~= shift_word(r, offset));
            assert(sw.subrange(position, position + r_fp.len() as int) == r_fp);
            assert(sw.subrange(0, position) + sw.subrange(position + r_fp.len() as int, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
    }
}

///  A shifted derivation valid in fp.
proof fn lemma_shifted_derivation_valid(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p2, steps, w1) == Some(w2),
    ensures
        equiv_in_presentation(
            free_product(p1, p2),
            shift_word(w1, p1.num_generators),
            shift_word(w2, p1.num_generators),
        ),
    decreases steps.len(),
{
    let fp = free_product(p1, p2);
    let offset = p1.num_generators;
    if steps.len() == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(fp, shift_word(w1, offset));
    } else {
        let step = steps.first();
        let next = apply_step(p2, w1, step).unwrap();
        let rest = steps.drop_first();

        let shifted_step = shift_derivation_step(step, offset, p1.relators.len());
        lemma_shifted_step_valid(p1, p2, w1, step, next);

        //  Single-step derivation in fp
        let d = Derivation { steps: Seq::new(1, |_i: int| shifted_step) };
        assert(d.steps.first() == shifted_step);
        assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(fp, d.steps.drop_first(), shift_word(next, offset)) == Some(shift_word(next, offset)));
        assert(derivation_valid(fp, d, shift_word(w1, offset), shift_word(next, offset)));

        //  Recurse
        lemma_shifted_derivation_valid(p1, p2, rest, next, w2);

        //  Chain
        lemma_equiv_transitive(fp, shift_word(w1, offset), shift_word(next, offset), shift_word(w2, offset));
    }
}

///  Right embedding: equivalence in p2 implies equivalence of shifted words in free_product(p1, p2).
pub proof fn lemma_right_embeds(p1: Presentation, p2: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p2, w1, w2),
    ensures
        equiv_in_presentation(
            free_product(p1, p2),
            shift_word(w1, p1.num_generators),
            shift_word(w2, p1.num_generators),
        ),
{
    let d = choose|d: Derivation| derivation_valid(p2, d, w1, w2);
    lemma_shifted_derivation_valid(p1, p2, d.steps, w1, w2);
}

} //  verus!
