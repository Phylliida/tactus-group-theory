use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;

verus! {

//  ============================================================
//  FORK-A DE-RISK PROBE (2026-06-23) — non-committing prototype.
//
//  This module is a faithful predicate-base port of `presentation.rs`.  Its
//  ONLY purpose is to measure scoping question #2 from
//  `docs/cohen-faithfulness-primary-source.md` §4 / §7 and
//  `docs/brick5-fork-reevaluation.md` §3 Q2:
//
//     "Does the relator-set-agnostic derivation algebra port VERBATIM, and
//      does the genuinely-new word-carrying relator core still close under
//      the tactus Lean backend, with a predicate relator set
//      `relators: spec_fn(Word) -> bool` instead of a finite `Seq<Word>`?"
//
//  It is kept SEPARATE from the verified finite `Presentation` so the 21k-line
//  tower (`britton_via_tower.rs`, `normal_form_afp_textbook.rs`) is untouched —
//  this is reversible (delete the file + the `pub mod` line) and does NOT
//  commit to the full Fork-A build.  The full-build go/no-go remains Danielle's.
//
//  Census prediction being tested (primary-source §7c):
//    * derivation algebra (`derivation_produces` / `equiv` / refl / concat /
//      transitive) is relator-set-agnostic ⟹ ports verbatim;
//    * the genuinely-new core is `apply_step` + the reversibility lemmas, where
//      the relator is carried as the WORD gated by `P(word)` instead of by index.
//  ============================================================

///  A predicate group presentation ⟨S | R⟩, R given as a membership predicate.
///
///  - `num_generators`: generators are Gen(0), ..., Gen(num_generators - 1)
///  - `relators`: a predicate on words; `relators(w)` means "w is a relator".
///
///  This is the Fork-A analog of `presentation::Presentation`, the only
///  difference being `relators: spec_fn(Word) -> bool` vs `Seq<Word>`.
pub struct PredPresentation {
    pub num_generators: nat,
    pub relators: spec_fn(Word) -> bool,
}

///  All relator words use valid generators.
///  Predicate analog of `presentation_valid`: instead of indexing each relator,
///  quantify over every word the predicate accepts.
#[verifier::opaque]
pub open spec fn pred_presentation_valid(p: PredPresentation) -> bool {
    forall|w: Word| #![trigger (p.relators)(w)]
        (p.relators)(w) ==> word_valid(w, p.num_generators)
}

///  An elementary derivation step in a predicate-presented group.
///  Free* variants are identical to `DerivationStep`; the Relator* variants
///  carry the relator WORD directly (gated by `relators(word)` in `apply_step`)
///  rather than an index into a finite `Seq`.
pub enum PredDerivationStep {
    ///  Free reduction: remove an inverse pair at position i.
    FreeReduce { position: int },
    ///  Free expansion: insert an inverse pair at position i.
    FreeExpand { position: int, symbol: Symbol },
    ///  Relator insertion: insert `relator` (or its inverse) at position i.
    RelatorInsert { position: int, relator: Word, inverted: bool },
    ///  Relator deletion: delete a copy of `relator` at position i.
    RelatorDelete { position: int, relator: Word, inverted: bool },
}

///  The relator word, possibly inverted.  No presentation lookup needed —
///  the word is carried on the step.
pub open spec fn get_relator_pred(relator: Word, inverted: bool) -> Word {
    if inverted {
        inverse_word(relator)
    } else {
        relator
    }
}

///  Apply a derivation step to a word, producing the result.
///  Returns None if the step is invalid.  The ONLY change vs `apply_step` is
///  the relator guard: `(p.relators)(relator)` instead of
///  `0 <= relator_index < p.relators.len()`.
pub open spec fn apply_step_pred(p: PredPresentation, w: Word, step: PredDerivationStep) -> Option<Word> {
    match step {
        PredDerivationStep::FreeReduce { position } => {
            if has_cancellation_at(w, position) {
                Some(reduce_at(w, position))
            } else {
                None
            }
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
            if 0 <= position <= w.len() && symbol_valid(symbol, p.num_generators) {
                let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
                Some(w.subrange(0, position) + pair + w.subrange(position, w.len() as int))
            } else {
                None
            }
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            if 0 <= position <= w.len() && (p.relators)(relator) {
                let r = get_relator_pred(relator, inverted);
                Some(w.subrange(0, position) + r + w.subrange(position, w.len() as int))
            } else {
                None
            }
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            if (p.relators)(relator) {
                let r = get_relator_pred(relator, inverted);
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
pub struct PredDerivation {
    pub steps: Seq<PredDerivationStep>,
}

///  Check that a derivation is valid: each step successfully produces the next word.
pub open spec fn pred_derivation_valid(p: PredPresentation, d: PredDerivation, start: Word, end: Word) -> bool {
    pred_derivation_produces(p, d.steps, start) == Some(end)
}

///  Apply a sequence of steps starting from a word.
///  Relator-set-agnostic above `apply_step_pred` ⟹ verbatim port (§7c).
pub open spec fn pred_derivation_produces(p: PredPresentation, steps: Seq<PredDerivationStep>, start: Word) -> Option<Word>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Some(start)
    } else {
        match apply_step_pred(p, start, steps.first()) {
            Some(next) => pred_derivation_produces(p, steps.drop_first(), next),
            None => None,
        }
    }
}

///  Two words are equivalent in the predicate-presented group.
pub open spec fn equiv_in_pred_presentation(p: PredPresentation, w1: Word, w2: Word) -> bool {
    exists|d: PredDerivation| pred_derivation_valid(p, d, w1, w2)
}

//  ============================================================
//  Relator-set-agnostic closure algebra — PREDICTED to port verbatim (§7c).
//  These are byte-for-byte the same proofs as `presentation.rs`, only the
//  types are renamed.  If they still close, §7c's "verbatim" claim holds.
//  ============================================================

///  The empty derivation witnesses reflexivity.
pub proof fn lemma_pred_equiv_refl(p: PredPresentation, w: Word)
    ensures
        equiv_in_pred_presentation(p, w, w),
{
    let d = PredDerivation { steps: Seq::empty() };
    assert(pred_derivation_produces(p, d.steps, w) == Some(w));
    assert(pred_derivation_valid(p, d, w, w));
}

///  Concatenating derivations witnesses transitivity.
pub proof fn lemma_pred_derivation_concat(
    p: PredPresentation,
    steps1: Seq<PredDerivationStep>,
    steps2: Seq<PredDerivationStep>,
    w1: Word,
    w2: Word,
    w3: Word,
)
    requires
        pred_derivation_produces(p, steps1, w1) == Some(w2),
        pred_derivation_produces(p, steps2, w2) == Some(w3),
    ensures
        pred_derivation_produces(p, steps1 + steps2, w1) == Some(w3),
    decreases steps1.len(),
{
    if steps1.len() == 0 {
        assert(steps1 + steps2 =~= steps2);
    } else {
        let next = apply_step_pred(p, w1, steps1.first()).unwrap();
        lemma_pred_derivation_concat(p, steps1.drop_first(), steps2, next, w2, w3);
        assert((steps1 + steps2).first() == steps1.first());
        assert((steps1 + steps2).drop_first() =~= steps1.drop_first() + steps2);
    }
}

///  Transitivity of equivalence.
pub proof fn lemma_pred_equiv_transitive(p: PredPresentation, w1: Word, w2: Word, w3: Word)
    requires
        equiv_in_pred_presentation(p, w1, w2),
        equiv_in_pred_presentation(p, w2, w3),
    ensures
        equiv_in_pred_presentation(p, w1, w3),
{
    let d1 = choose|d: PredDerivation| pred_derivation_valid(p, d, w1, w2);
    let d2 = choose|d: PredDerivation| pred_derivation_valid(p, d, w2, w3);
    lemma_pred_derivation_concat(p, d1.steps, d2.steps, w1, w2, w3);
    let d3 = PredDerivation { steps: d1.steps + d2.steps };
    assert(pred_derivation_valid(p, d3, w1, w3));
}

//  ============================================================
//  The genuinely-new word-carrying relator core (§7c).
//  Here the relator is carried as a WORD gated by P(word); the predicate
//  analog of `presentation_valid` supplies validity.  §6a predicts the
//  base-relator case ports with no new math — this is the real test.
//  ============================================================

///  Invert a single derivation step given the source word.
pub open spec fn invert_step_with_context_pred(step: PredDerivationStep, w: Word) -> PredDerivationStep {
    match step {
        PredDerivationStep::FreeReduce { position } =>
            PredDerivationStep::FreeExpand { position, symbol: w[position] },
        PredDerivationStep::FreeExpand { position, symbol } =>
            PredDerivationStep::FreeReduce { position },
        PredDerivationStep::RelatorInsert { position, relator, inverted } =>
            PredDerivationStep::RelatorDelete { position, relator, inverted },
        PredDerivationStep::RelatorDelete { position, relator, inverted } =>
            PredDerivationStep::RelatorInsert { position, relator, inverted },
    }
}

///  A single step can be reversed.  Note: inverting a RelatorInsert{relator}
///  yields a RelatorDelete{relator} carrying the SAME word, so `P(relator)` is
///  preserved with no `choose` — exactly §7d's "no witness friction".
pub proof fn lemma_pred_single_step_reversible(p: PredPresentation, w: Word, step: PredDerivationStep, w_prime: Word)
    requires
        apply_step_pred(p, w, step) == Some(w_prime),
        word_valid(w, p.num_generators),
        pred_presentation_valid(p),
    ensures
        apply_step_pred(p, w_prime, invert_step_with_context_pred(step, w)) == Some(w),
{
    match step {
        PredDerivationStep::FreeReduce { position } => {
            let s = w[position];
            let inv_s = w[position + 1];
            assert(is_inverse_pair(s, inv_s));
            assert(inv_s == inverse_symbol(s));
            assert(symbol_valid(s, p.num_generators));
            let pair = Seq::new(1, |_i: int| s) + Seq::new(1, |_i: int| inverse_symbol(s));
            assert(w_prime.subrange(0, position) =~= w.subrange(0, position));
            assert(w_prime.subrange(position, w_prime.len() as int) =~= w.subrange(position + 2, w.len() as int));
            assert(w_prime.subrange(0, position) + pair + w_prime.subrange(position, w_prime.len() as int) =~= w);
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(w_prime =~= w.subrange(0, position) + pair + w.subrange(position, w.len() as int));
            assert(w_prime[position] == symbol);
            assert(w_prime[position + 1] == inverse_symbol(symbol));
            assert(has_cancellation_at(w_prime, position));
            assert(reduce_at(w_prime, position) =~= w);
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            //  apply_step_pred returned Some ⟹ the guard `(p.relators)(relator)` held,
            //  so the inverted RelatorDelete carries an accepted relator too.
            assert((p.relators)(relator));
            let r = get_relator_pred(relator, inverted);
            assert(w_prime =~= w.subrange(0, position) + r + w.subrange(position, w.len() as int));
            assert(w_prime.subrange(position, position + r.len() as int) =~= r);
            assert(w_prime.subrange(0, position) + w_prime.subrange(position + r.len() as int, w_prime.len() as int) =~= w);
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert((p.relators)(relator));
            let r = get_relator_pred(relator, inverted);
            assert(w.subrange(position, position + r.len() as int) == r);
            assert(w_prime =~= w.subrange(0, position) + w.subrange(position + r.len() as int, w.len() as int));
            assert(w_prime.subrange(0, position) =~= w.subrange(0, position));
            assert(w_prime.subrange(position, w_prime.len() as int) =~= w.subrange(position + r.len() as int, w.len() as int));
            assert(w_prime.subrange(0, position) + r + w_prime.subrange(position, w_prime.len() as int) =~= w);
        },
    }
}

///  A single derivation step preserves word_valid when pred_presentation_valid.
pub proof fn lemma_pred_step_preserves_word_valid(
    p: PredPresentation, w: Word, step: PredDerivationStep, w_next: Word,
)
    requires
        apply_step_pred(p, w, step) == Some(w_next),
        pred_presentation_valid(p),
        word_valid(w, p.num_generators),
    ensures
        word_valid(w_next, p.num_generators),
{
    reveal(pred_presentation_valid);
    let n = p.num_generators;
    match step {
        PredDerivationStep::FreeReduce { position } => {
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else { assert(w_next[k] == w[k + 2]); }
            }
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
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
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            //  The guard held ⟹ relator is accepted ⟹ word_valid via pred_presentation_valid.
            assert((p.relators)(relator));
            assert(word_valid(relator, n));
            let r = get_relator_pred(relator, inverted);
            if inverted { crate::word::lemma_inverse_word_valid(relator, n); }
            assert(word_valid(r, n));
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else if k < position + r.len() { assert(w_next[k] == r[k - position]); }
                else { assert(w_next[k] == w[k - r.len() as int]); }
            }
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert((p.relators)(relator));
            let r = get_relator_pred(relator, inverted);
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
proof fn lemma_pred_derivation_reversible(p: PredPresentation, steps: Seq<PredDerivationStep>, start: Word, end: Word)
    requires
        pred_derivation_produces(p, steps, start) == Some(end),
        word_valid(start, p.num_generators),
        pred_presentation_valid(p),
    ensures
        equiv_in_pred_presentation(p, end, start),
    decreases steps.len(),
{
    if steps.len() == 0 {
        lemma_pred_equiv_refl(p, start);
    } else {
        let step = steps.first();
        let next = apply_step_pred(p, start, step).unwrap();
        let rest = steps.drop_first();

        lemma_pred_step_preserves_word_valid(p, start, step, next);
        lemma_pred_derivation_reversible(p, rest, next, end);
        lemma_pred_single_step_reversible(p, start, step, next);

        let rev_step = invert_step_with_context_pred(step, start);
        assert(apply_step_pred(p, next, rev_step) == Some(start));
        let rev_steps = Seq::new(1, |_i: int| rev_step);
        assert(rev_steps.first() == rev_step);
        assert(rev_steps.drop_first() =~= Seq::<PredDerivationStep>::empty());
        assert(pred_derivation_produces(p, rev_steps.drop_first(), start) == Some(start));
        let rev_d = PredDerivation { steps: rev_steps };
        assert(pred_derivation_valid(p, rev_d, next, start));
        lemma_pred_equiv_transitive(p, end, next, start);
    }
}

///  Symmetry: if w1 ≡ w2 then w2 ≡ w1.
pub proof fn lemma_pred_equiv_symmetric(p: PredPresentation, w1: Word, w2: Word)
    requires
        equiv_in_pred_presentation(p, w1, w2),
        word_valid(w1, p.num_generators),
        pred_presentation_valid(p),
    ensures
        equiv_in_pred_presentation(p, w2, w1),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p, d, w1, w2);
    lemma_pred_derivation_reversible(p, d.steps, w1, w2);
}

} //  verus!
