use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;

verus! {

///  A group presentation ⟨S | R⟩.
///
///  - `num_generators`: the generators are Gen(0), ..., Gen(num_generators - 1)
///  - `relators`: words that are set equal to the identity
///
///  The presented group is the quotient of the free group on S by the normal
///  closure of R.
pub struct Presentation {
    pub num_generators: nat,
    pub relators: Seq<Word>,
}

///  All symbols in a relator use valid generators.
#[verifier::opaque]
pub open spec fn presentation_valid(p: Presentation) -> bool {
    forall|i: int| #![trigger p.relators[i]]
        0 <= i < p.relators.len() ==> word_valid(p.relators[i], p.num_generators)
}

///  An elementary derivation step in a presented group.
pub enum DerivationStep {
    ///  Free reduction: remove an inverse pair at position i.
    FreeReduce { position: int },
    ///  Free expansion: insert an inverse pair at position i.
    FreeExpand { position: int, symbol: Symbol },
    ///  Relator insertion: insert relator r (or its inverse) at position i,
    ///  possibly conjugated by prefix of the word.
    RelatorInsert { position: int, relator_index: nat, inverted: bool },
    ///  Relator deletion: delete a copy of relator r at position i.
    RelatorDelete { position: int, relator_index: nat, inverted: bool },
}

///  Get the relator word, possibly inverted.
pub open spec fn get_relator(p: Presentation, idx: nat, inverted: bool) -> Word {
    if inverted {
        inverse_word(p.relators[idx as int])
    } else {
        p.relators[idx as int]
    }
}

///  Apply a derivation step to a word, producing the result.
///  Returns None if the step is invalid.
pub open spec fn apply_step(p: Presentation, w: Word, step: DerivationStep) -> Option<Word> {
    match step {
        DerivationStep::FreeReduce { position } => {
            if has_cancellation_at(w, position) {
                Some(reduce_at(w, position))
            } else {
                None
            }
        },
        DerivationStep::FreeExpand { position, symbol } => {
            if 0 <= position <= w.len() && symbol_valid(symbol, p.num_generators) {
                let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
                Some(w.subrange(0, position) + pair + w.subrange(position, w.len() as int))
            } else {
                None
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            if 0 <= position <= w.len() && 0 <= relator_index < p.relators.len() {
                let r = get_relator(p, relator_index, inverted);
                Some(w.subrange(0, position) + r + w.subrange(position, w.len() as int))
            } else {
                None
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            if 0 <= relator_index < p.relators.len() {
                let r = get_relator(p, relator_index, inverted);
                let rlen = r.len();
                if 0 <= position && position + rlen <= w.len()
                    && w.subrange(position, position + rlen as int) == r
                {
                    Some(w.subrange(0, position) + w.subrange(position + rlen as int, w.len() as int))
                } else {
                    None
                }
            } else {
                None
            }
        },
    }
}

///  A derivation is a sequence of steps transforming w1 into w2.
pub struct Derivation {
    pub steps: Seq<DerivationStep>,
}

///  Check that a derivation is valid: each step successfully produces the next word.
pub open spec fn derivation_valid(p: Presentation, d: Derivation, start: Word, end: Word) -> bool {
    derivation_produces(p, d.steps, start) == Some(end)
}

///  Apply a sequence of steps starting from a word.
pub open spec fn derivation_produces(p: Presentation, steps: Seq<DerivationStep>, start: Word) -> Option<Word>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Some(start)
    } else {
        match apply_step(p, start, steps.first()) {
            Some(next) => derivation_produces(p, steps.drop_first(), next),
            None => None,
        }
    }
}

///  Two words are equivalent in the presented group: there exists a valid derivation.
pub open spec fn equiv_in_presentation(p: Presentation, w1: Word, w2: Word) -> bool {
    exists|d: Derivation| derivation_valid(p, d, w1, w2)
}

///  The empty derivation witnesses reflexivity.
pub proof fn lemma_equiv_refl(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, w, w),
{
    let d = Derivation { steps: Seq::empty() };
    assert(derivation_produces(p, d.steps, w) == Some(w));
    assert(derivation_valid(p, d, w, w));
}

///  Concatenating derivations witnesses transitivity.
pub proof fn lemma_derivation_concat(
    p: Presentation,
    steps1: Seq<DerivationStep>,
    steps2: Seq<DerivationStep>,
    w1: Word,
    w2: Word,
    w3: Word,
)
    requires
        derivation_produces(p, steps1, w1) == Some(w2),
        derivation_produces(p, steps2, w2) == Some(w3),
    ensures
        derivation_produces(p, steps1 + steps2, w1) == Some(w3),
    decreases steps1.len(),
{
    if steps1.len() == 0 {
        assert(steps1 + steps2 =~= steps2);
    } else {
        let next = apply_step(p, w1, steps1.first()).unwrap();
        lemma_derivation_concat(p, steps1.drop_first(), steps2, next, w2, w3);
        assert((steps1 + steps2).first() == steps1.first());
        assert((steps1 + steps2).drop_first() =~= steps1.drop_first() + steps2);
    }
}

///  Transitivity of equivalence.
pub proof fn lemma_equiv_transitive(p: Presentation, w1: Word, w2: Word, w3: Word)
    requires
        equiv_in_presentation(p, w1, w2),
        equiv_in_presentation(p, w2, w3),
    ensures
        equiv_in_presentation(p, w1, w3),
{
    let d1 = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    let d2 = choose|d: Derivation| derivation_valid(p, d, w2, w3);
    lemma_derivation_concat(p, d1.steps, d2.steps, w1, w2, w3);
    let d3 = Derivation { steps: d1.steps + d2.steps };
    assert(derivation_valid(p, d3, w1, w3));
}

///  Invert a single derivation step given the source word.
///  FreeReduce needs the symbol from the source word to construct FreeExpand.
pub open spec fn invert_step_with_context(step: DerivationStep, w: Word) -> DerivationStep {
    match step {
        DerivationStep::FreeReduce { position } =>
            DerivationStep::FreeExpand { position, symbol: w[position] },
        DerivationStep::FreeExpand { position, symbol } =>
            DerivationStep::FreeReduce { position },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            DerivationStep::RelatorDelete { position, relator_index, inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            DerivationStep::RelatorInsert { position, relator_index, inverted },
    }
}

///  A single step can be reversed: if apply_step(p, w, step) = Some(w'),
///  then apply_step(p, w', invert_step_with_context(step, w)) = Some(w).
pub proof fn lemma_single_step_reversible(p: Presentation, w: Word, step: DerivationStep, w_prime: Word)
    requires
        apply_step(p, w, step) == Some(w_prime),
        word_valid(w, p.num_generators),
        presentation_valid(p),
    ensures
        apply_step(p, w_prime, invert_step_with_context(step, w)) == Some(w),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            //  w has inverse pair at position, w' = reduce_at(w, position)
            //  Inverse: FreeExpand at position with symbol w[position]
            //  w' expanded at position gives w back
            let s = w[position];
            let inv_s = w[position + 1];
            assert(is_inverse_pair(s, inv_s));
            assert(inv_s == inverse_symbol(s));
            //  s is valid because w is word_valid
            assert(symbol_valid(s, p.num_generators));
            let pair = Seq::new(1, |_i: int| s) + Seq::new(1, |_i: int| inverse_symbol(s));
            //  w' = w[0..position] ++ w[position+2..]
            //  Expanding at position: w'[0..position] ++ pair ++ w'[position..]
            //  = w[0..position] ++ [s, inv_s] ++ w[position+2..] = w
            assert(w_prime.subrange(0, position) =~= w.subrange(0, position));
            assert(w_prime.subrange(position, w_prime.len() as int) =~= w.subrange(position + 2, w.len() as int));
            assert(w_prime.subrange(0, position) + pair + w_prime.subrange(position, w_prime.len() as int) =~= w);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  w' = w[0..position] ++ [symbol, inv(symbol)] ++ w[position..]
            //  Inverse: FreeReduce at position
            //  w'[position] = symbol, w'[position+1] = inv(symbol) → inverse pair
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(w_prime =~= w.subrange(0, position) + pair + w.subrange(position, w.len() as int));
            assert(w_prime[position] == symbol);
            assert(w_prime[position + 1] == inverse_symbol(symbol));
            assert(has_cancellation_at(w_prime, position));
            assert(reduce_at(w_prime, position) =~= w);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            //  w' = w[0..position] ++ relator ++ w[position..]
            //  Inverse: RelatorDelete at position
            let r = get_relator(p, relator_index, inverted);
            assert(w_prime =~= w.subrange(0, position) + r + w.subrange(position, w.len() as int));
            assert(w_prime.subrange(position, position + r.len() as int) =~= r);
            assert(w_prime.subrange(0, position) + w_prime.subrange(position + r.len() as int, w_prime.len() as int) =~= w);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            //  w' = w[0..position] ++ w[position+|r|..]
            //  Inverse: RelatorInsert at position
            let r = get_relator(p, relator_index, inverted);
            assert(w.subrange(position, position + r.len() as int) == r);
            assert(w_prime =~= w.subrange(0, position) + w.subrange(position + r.len() as int, w.len() as int));
            assert(w_prime.subrange(0, position) =~= w.subrange(0, position));
            assert(w_prime.subrange(position, w_prime.len() as int) =~= w.subrange(position + r.len() as int, w.len() as int));
            assert(w_prime.subrange(0, position) + r + w_prime.subrange(position, w_prime.len() as int) =~= w);
        },
    }
}

///  Symmetry: if w1 ≡ w2 then w2 ≡ w1.
///  Proof by induction on derivation length, reversing each step.
///  Requires word_valid(w1) + presentation_valid(p) because reversing
///  a FreeReduce produces a FreeExpand that needs symbol_valid.
pub proof fn lemma_equiv_symmetric(p: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w2),
        word_valid(w1, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, w2, w1),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_derivation_reversible(p, d.steps, w1, w2);
}

///  A single derivation step preserves word_valid when presentation_valid.
///  Used in lemma_derivation_reversible to maintain word_valid through induction.
pub proof fn lemma_step_preserves_word_valid_pres(
    p: Presentation, w: Word, step: DerivationStep, w_next: Word,
)
    requires
        apply_step(p, w, step) == Some(w_next),
        presentation_valid(p),
        word_valid(w, p.num_generators),
    ensures
        word_valid(w_next, p.num_generators),
{
    reveal(presentation_valid);
    let n = p.num_generators;
    match step {
        DerivationStep::FreeReduce { position } => {
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else { assert(w_next[k] == w[k + 2]); }
            }
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  apply_step guard ensures symbol_valid(symbol, n)
            crate::symbol::lemma_inverse_preserves_valid(symbol, n);
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            let pfx = w.subrange(0, position);
            let sfx = w.subrange(position, w.len() as int);
            assert(w_next =~= pfx + pair + sfx);
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else if k == position as int { }
                else if k == position + 1 { assert(w_next[k] == inverse_symbol(symbol)); }
                else { assert(w_next[k] == w[k - 2]); }
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            if inverted { crate::word::lemma_inverse_word_valid(p.relators[relator_index as int], n); }
            assert(word_valid(r, n));
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else if k < position + r.len() { assert(w_next[k] == r[k - position]); }
                else { assert(w_next[k] == w[k - r.len() as int]); }
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else { assert(w_next[k] == w[k + r.len() as int]); }
            }
        },
    }
}

///  A valid derivation can be reversed.
proof fn lemma_derivation_reversible(p: Presentation, steps: Seq<DerivationStep>, start: Word, end: Word)
    requires
        derivation_produces(p, steps, start) == Some(end),
        word_valid(start, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, end, start),
    decreases steps.len(),
{
    if steps.len() == 0 {
        //  start == end
        lemma_equiv_refl(p, start);
    } else {
        let step = steps.first();
        let next = apply_step(p, start, step).unwrap();
        let rest = steps.drop_first();

        //  Maintain word_valid through the derivation
        lemma_step_preserves_word_valid_pres(p, start, step, next);

        //  rest takes next to end
        lemma_derivation_reversible(p, rest, next, end);
        //  We now know: end ≡ next

        //  We need: next → start (single reverse step)
        lemma_single_step_reversible(p, start, step, next);
        let rev_step = invert_step_with_context(step, start);
        assert(apply_step(p, next, rev_step) == Some(start));
        //  derivation_produces on a single-step sequence:
        //  first apply rev_step to next → Some(start)
        //  then derivation_produces on empty from start → Some(start)
        let rev_steps = Seq::new(1, |_i: int| rev_step);
        assert(rev_steps.first() == rev_step);
        assert(rev_steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(p, rev_steps.drop_first(), start) == Some(start));
        let rev_d = Derivation { steps: rev_steps };
        assert(derivation_valid(p, rev_d, next, start));
        //  next ≡ start
        //  end ≡ next ≡ start
        lemma_equiv_transitive(p, end, next, start);
    }
}

} //  verus!
