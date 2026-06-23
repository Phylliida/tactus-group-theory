// The free-group word problem IS free reduction.
//
// `equiv_in_presentation(free_group(n), w1, w2) ⟹ freely_equivalent(w1, w2)` — the converse of
// `lemma_freely_equivalent_implies_equiv` (`presentation_lemmas.rs`), specialized to a relator-free
// presentation.  Since `free_group(n).relators` is empty, NO `RelatorInsert`/`RelatorDelete` step can
// succeed (their guards require `relator_index < relators.len() = 0`), so every step of a valid
// derivation is a `FreeReduce` or `FreeExpand` — i.e. exactly a free reduction or its inverse.  By
// induction over the derivation, the endpoints are `freely_equivalent`.
//
// WHY (Layer 0.5 foundation): the existing freeness machinery (`f_free.rs`) descends a free family's
// triviality via *structured retractions* (HNN/free-product base-faithfulness) and never computes a
// free NORMAL FORM.  The Higman–Neumann–Neumann crux `{a⁻ⁱbaⁱ}` free in `F₂` (Miller §4.1, "the central
// b survives free reduction") is a CANCELLATION argument that needs the actual reduced word — so it
// needs this bridge from `≡_{free_group}` to `freely_equivalent`/`normal_form`.  Self-contained,
// representation-independent, reusable; lives in its own module to avoid trigger pollution.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::{DerivationStep, apply_step, derivation_produces, derivation_valid,
    equiv_in_presentation, Derivation};
use crate::reduction::{has_cancellation_at, reduce_at, reduces_one_step, reduces_in_steps, reduces_to,
    freely_equivalent, lemma_reduces_to_refl, lemma_freely_equivalent_refl, lemma_freely_equivalent_sym,
    lemma_freely_equivalent_trans};
use crate::higman_operations::free_group;

verus! {

/// A single free-reduction step connects freely-equivalent words.
proof fn lemma_reduces_one_step_freely_equivalent(w1: Word, w2: Word)
    requires
        reduces_one_step(w1, w2),
    ensures
        freely_equivalent(w1, w2),
{
    // reduces_one_step ⟹ reduces_in_steps(_, _, 1) ⟹ reduces_to.
    assert(reduces_in_steps(w1, w2, 1)) by {
        let i = choose|i: int| has_cancellation_at(w1, i) && w2 == reduce_at(w1, i);
        assert(reduces_one_step(w1, w2));
        assert(reduces_in_steps(w2, w2, 0));
    }
    assert(reduces_to(w1, w2));                         // witness n = 1
    lemma_reduces_to_refl(w2);
    assert(freely_equivalent(w1, w2));                 // common reduct u = w2
}

/// **Each derivation step over `free_group(n)` connects freely-equivalent words.**  Relator steps are
/// impossible (empty relators); free-reduce and free-expand are exactly free reductions (one forwards,
/// one backwards).
proof fn lemma_free_step_freely_equivalent(n: nat, w: Word, step: DerivationStep, next: Word)
    requires
        apply_step(free_group(n), w, step) == Some(next),
    ensures
        freely_equivalent(w, next),
{
    let fg = free_group(n);
    assert(fg.relators.len() == 0);
    match step {
        DerivationStep::FreeReduce { position } => {
            // apply_step succeeds ⟹ has_cancellation_at(w, position) ∧ next == reduce_at(w, position).
            assert(has_cancellation_at(w, position));
            assert(next == reduce_at(w, position));
            assert(reduces_one_step(w, next));          // witness position
            lemma_reduces_one_step_freely_equivalent(w, next);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            // next = w[0..pos] ++ [symbol, inverse_symbol(symbol)] ++ w[pos..]; it reduces back to w.
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(0 <= position <= w.len() && symbol_valid(symbol, n));
            assert(next == w.subrange(0, position) + pair + w.subrange(position, w.len() as int));
            assert(pair.len() == 2 && pair[0] == symbol && pair[1] == inverse_symbol(symbol));
            // the inserted pair is a cancellation at `position` in `next`.
            assert(next.len() == w.len() + 2);
            assert(next[position] == symbol);
            assert(next[position + 1] == inverse_symbol(symbol));
            assert(has_cancellation_at(next, position)) by {
                assert(is_inverse_pair(next[position], next[position + 1]));
            }
            // reduce_at(next, position) == w.
            assert(reduce_at(next, position) =~= w) by {
                let red = reduce_at(next, position);
                assert(red == next.subrange(0, position) + next.subrange(position + 2, next.len() as int));
                assert(next.subrange(0, position) =~= w.subrange(0, position));
                assert(next.subrange(position + 2, next.len() as int) =~= w.subrange(position, w.len() as int));
                assert(w =~= w.subrange(0, position) + w.subrange(position, w.len() as int));
            }
            assert(reduces_one_step(next, w));          // witness position
            lemma_reduces_one_step_freely_equivalent(next, w);
            lemma_freely_equivalent_sym(next, w);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            // relators empty ⟹ guard `relator_index < 0` fails ⟹ apply_step is None: contradiction.
            assert(apply_step(fg, w, step) == None::<Word>);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(apply_step(fg, w, step) == None::<Word>);
        },
    }
}

/// **A whole derivation over `free_group(n)` connects freely-equivalent words** (induction on steps).
proof fn lemma_free_derivation_freely_equivalent(n: nat, steps: Seq<DerivationStep>, start: Word,
    end: Word)
    requires
        derivation_produces(free_group(n), steps, start) == Some(end),
    ensures
        freely_equivalent(start, end),
    decreases steps.len(),
{
    let fg = free_group(n);
    if steps.len() == 0 {
        assert(start == end);                           // derivation_produces == Some(start) == Some(end)
        lemma_freely_equivalent_refl(start);
    } else {
        let first = steps.first();
        match apply_step(fg, start, first) {
            Some(mid) => {
                assert(derivation_produces(fg, steps.drop_first(), mid) == Some(end));
                lemma_free_step_freely_equivalent(n, start, first, mid);          // start ~ mid
                lemma_free_derivation_freely_equivalent(n, steps.drop_first(), mid, end);  // mid ~ end
                lemma_freely_equivalent_trans(start, mid, end);
            },
            None => {
                assert(derivation_produces(fg, steps, start) == None::<Word>);    // contradiction
            },
        }
    }
}

/// **THE BRIDGE.** Equivalence in the free group on `n` generators is exactly free equivalence:
/// `equiv_in_presentation(free_group(n), w1, w2) ⟹ freely_equivalent(w1, w2)`.  (The converse is
/// `lemma_freely_equivalent_implies_equiv`.)  This is the missing link that lets a free-reduction /
/// normal-form cancellation argument conclude triviality in the abstract free group — the foundation
/// for the Higman–Neumann–Neumann `{a⁻ⁱbaⁱ}`-free lemma (Layer 0.5).
pub proof fn lemma_free_group_equiv_freely_equivalent(n: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(free_group(n), w1, w2),
    ensures
        freely_equivalent(w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(free_group(n), d, w1, w2);
    lemma_free_derivation_freely_equivalent(n, d.steps, w1, w2);
}

} // verus!
