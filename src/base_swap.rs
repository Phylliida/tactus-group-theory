// base_swap — the *reflecting* direction of "adding derivable relators doesn't change
// the group". Foundation stone for the Brick-5 completeness reroute (C3.0,
// `docs/brick5-completeness-plan.md` §2.2ter): augmenting a base with a finite list of
// relators that are already CONSEQUENCES of the base (each `rs[i] ≡_p ε`) preserves the
// group, so we may run the Britton engine over the augmented base `h3_II` (where the
// a-level associations become literal isomorphisms) and transport the conclusion back to
// `h3_pres`.
//
// The FORWARD direction (`equiv_in(p,·,·) ⟹ equiv_in(add_relators(p,rs),·,·)`) already
// exists (`quotient.rs::lemma_add_relators_preserves_equiv` — adding relators can only add
// equivalences). This module supplies the REFLECTING direction
// (`equiv_in(add_relators(p,rs),·,·) ∧ ∀i.rs[i]≡_p ε ⟹ equiv_in(p,·,·)`); together they
// give the group-preservation iff `lemma_add_derivable_relators_iff`.
//
// Pure presentation theory — no Higman specifics. The argument replays a derivation over
// `add_relators(p,rs)` step-by-step into a `≡_p` chain: original relators / free moves are
// valid `p`-steps; an added-relator insert/delete only inserts or deletes a `≡_p ε` word,
// which is a `≡_p`-equivalence by congruence. (`presentation_valid` + `word_valid(rs[i])`
// are needed only because reversing an equivalence — `lemma_equiv_symmetric` — requires
// them; both hold for the Higman base `h3_upto(2n)` and its family-(II) relators.)

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::quotient::*;

verus! {

// ----------------------------------------------------------------------------
// Small reusable atoms
// ----------------------------------------------------------------------------

/// A single valid step is a one-step equivalence.
pub proof fn lemma_single_step_equiv(p: Presentation, w: Word, step: DerivationStep, w2: Word)
    requires
        apply_step(p, w, step) == Some(w2),
    ensures
        equiv_in_presentation(p, w, w2),
{
    let d = Derivation { steps: seq![step] };
    assert(d.steps.len() == 1);
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(p, d.steps.drop_first(), w2) == Some(w2));
    assert(derivation_produces(p, d.steps, w) == Some(w2));
    assert(derivation_valid(p, d, w, w2));
}

/// `inverse_word(r) ≡_p ε` from `r ≡_p ε` (special case of equiv-respects-inverse).
pub proof fn lemma_inv_equiv_empty(p: Presentation, r: Word)
    requires
        presentation_valid(p),
        word_valid(r, p.num_generators),
        equiv_in_presentation(p, r, empty_word()),
    ensures
        equiv_in_presentation(p, inverse_word(r), empty_word()),
{
    let ri = inverse_word(r);
    lemma_inverse_word_valid(r, p.num_generators);          // word_valid(ri)
    lemma_concat_word_valid(ri, r, p.num_generators);       // word_valid(ri·r)
    lemma_word_inverse_left(p, r);                          // ri·r ≡ ε      (A)
    lemma_equiv_concat_right(p, ri, r, empty_word());       // ri·r ≡ ri·ε
    assert(concat(ri, r) == ri + r);
    assert(concat(ri, empty_word()) =~= ri);               // ri·r ≡ ri      (B)
    // ri ≡ ri·r ≡ ε
    lemma_equiv_symmetric(p, ri + r, ri);                  // ri ≡ ri·r  (flip B)
    lemma_equiv_transitive(p, ri, ri + r, empty_word());   // ri ≡ ε
}

/// Inserting a `≡_p ε` word is a `≡_p`-equivalence (forward):  `A·r·B ≡_p A·B`.
pub proof fn lemma_insert_eps(p: Presentation, a: Word, r: Word, b: Word)
    requires
        equiv_in_presentation(p, r, empty_word()),
    ensures
        equiv_in_presentation(p, a + r + b, a + b),
{
    lemma_equiv_concat_left(p, r, empty_word(), b);         // r·b ≡ ε·b
    assert(concat(r, b) == r + b);
    assert(concat(empty_word(), b) =~= b);                  // r·b ≡ b
    lemma_equiv_concat_right(p, a, r + b, b);               // a·(r·b) ≡ a·b
    assert(concat(a, r + b) =~= a + r + b);                 // assoc
    assert(concat(a, b) == a + b);
}

/// Inserting a `≡_p ε` word is a `≡_p`-equivalence (reverse):  `A·B ≡_p A·r·B`. Caller
/// supplies the already-flipped hypothesis `ε ≡_p r` (so this stays symmetric-free).
pub proof fn lemma_insert_eps_rev(p: Presentation, a: Word, r: Word, b: Word)
    requires
        equiv_in_presentation(p, empty_word(), r),
    ensures
        equiv_in_presentation(p, a + b, a + r + b),
{
    lemma_equiv_concat_left(p, empty_word(), r, b);         // ε·b ≡ r·b
    assert(concat(empty_word(), b) =~= b);
    assert(concat(r, b) == r + b);                          // b ≡ r·b
    lemma_equiv_concat_right(p, a, b, r + b);               // a·b ≡ a·(r·b)
    assert(concat(a, b) == a + b);
    assert(concat(a, r + b) =~= a + r + b);                 // assoc
}

// ----------------------------------------------------------------------------
// Structure of `add_relators`
// ----------------------------------------------------------------------------

/// `add_relators(p, rs)` keeps `p`'s generators and appends `rs` to its relators.
pub proof fn lemma_add_relators_relators(p: Presentation, rs: Seq<Word>)
    ensures
        add_relators(p, rs).num_generators == p.num_generators,
        add_relators(p, rs).relators == p.relators + rs,
    decreases rs.len(),
{
    if rs.len() == 0 {
        assert(p.relators + rs =~= p.relators);
    } else {
        let p1 = add_relator(p, rs.first());
        lemma_add_relators_relators(p1, rs.drop_first());
        assert(p1.relators =~= p.relators + seq![rs.first()]);
        assert(p1.relators + rs.drop_first() =~= p.relators + rs) by {
            assert(seq![rs.first()] + rs.drop_first() =~= rs);
            assert((p.relators + seq![rs.first()]) + rs.drop_first()
                =~= p.relators + (seq![rs.first()] + rs.drop_first()));
        }
    }
}

// ----------------------------------------------------------------------------
// The reflecting lemma — per-step, then by induction over a derivation
// ----------------------------------------------------------------------------

/// A single step over `add_relators(p, rs)` reflects to a `≡_p`-equivalence, provided every
/// added relator is `≡_p ε`. Original-relator and free moves are valid `p`-steps; an
/// added-relator insert/delete only inserts/deletes a `≡_p ε` word.
pub proof fn lemma_step_reflects_to_base(
    p: Presentation, rs: Seq<Word>, w: Word, step: DerivationStep, w2: Word,
)
    requires
        presentation_valid(p),
        forall|i: int| 0 <= i < rs.len() ==>
            word_valid(#[trigger] rs[i], p.num_generators)
            && equiv_in_presentation(p, rs[i], empty_word()),
        apply_step(add_relators(p, rs), w, step) == Some(w2),
    ensures
        equiv_in_presentation(p, w, w2),
{
    let q = add_relators(p, rs);
    lemma_add_relators_relators(p, rs);
    assert(q.num_generators == p.num_generators);
    assert(q.relators == p.relators + rs);
    let np = p.relators.len() as int;

    match step {
        DerivationStep::FreeReduce { position } => {
            assert(apply_step(p, w, step) == Some(w2));     // presentation-independent
            lemma_single_step_equiv(p, w, step, w2);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            assert(apply_step(p, w, step) == Some(w2));     // num_generators agrees
            lemma_single_step_equiv(p, w, step, w2);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= position <= w.len());
            assert(0 <= relator_index < q.relators.len());
            let r = get_relator(q, relator_index, inverted);
            assert(w2 == w.subrange(0, position) + r + w.subrange(position, w.len() as int));
            if (relator_index as int) < np {
                assert(q.relators[relator_index as int] == p.relators[relator_index as int]);
                assert(get_relator(p, relator_index, inverted) == r);
                assert(apply_step(p, w, step) == Some(w2));
                lemma_single_step_equiv(p, w, step, w2);
            } else {
                let k = relator_index as int - np;
                assert(0 <= k < rs.len());
                assert(q.relators[relator_index as int] == rs[k]);
                // r ≡_p ε, then flip to ε ≡_p r (validity for the flip)
                if inverted {
                    assert(r == inverse_word(rs[k]));
                    lemma_inv_equiv_empty(p, rs[k]);
                    lemma_inverse_word_valid(rs[k], p.num_generators);
                } else {
                    assert(r == rs[k]);
                }
                assert(word_valid(r, p.num_generators));
                assert(equiv_in_presentation(p, r, empty_word()));
                lemma_equiv_symmetric(p, r, empty_word());  // ε ≡ r
                // insert: w = A·B,  w2 = A·r·B
                assert(w =~= w.subrange(0, position) + w.subrange(position, w.len() as int));
                lemma_insert_eps_rev(p, w.subrange(0, position), r, w.subrange(position, w.len() as int));
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < q.relators.len());
            let r = get_relator(q, relator_index, inverted);
            let rlen = r.len() as int;
            assert(0 <= position && position + rlen <= w.len());
            assert(w.subrange(position, position + rlen) == r);
            assert(w2 == w.subrange(0, position) + w.subrange(position + rlen, w.len() as int));
            if (relator_index as int) < np {
                assert(q.relators[relator_index as int] == p.relators[relator_index as int]);
                assert(get_relator(p, relator_index, inverted) == r);
                assert(apply_step(p, w, step) == Some(w2));
                lemma_single_step_equiv(p, w, step, w2);
            } else {
                let k = relator_index as int - np;
                assert(0 <= k < rs.len());
                assert(q.relators[relator_index as int] == rs[k]);
                if inverted {
                    assert(r == inverse_word(rs[k]));
                    lemma_inv_equiv_empty(p, rs[k]);
                } else {
                    assert(r == rs[k]);
                }
                assert(equiv_in_presentation(p, r, empty_word()));
                // delete: w = A·r·B',  w2 = A·B'  (forward insert_eps)
                assert(w =~= w.subrange(0, position) + r + w.subrange(position + rlen, w.len() as int)) by {
                    assert(w =~= w.subrange(0, position) + w.subrange(position, position + rlen)
                        + w.subrange(position + rlen, w.len() as int));
                    assert(w.subrange(position, position + rlen) == r);
                }
                lemma_insert_eps(p, w.subrange(0, position), r, w.subrange(position + rlen, w.len() as int));
            }
        },
    }
}

/// A derivation over `add_relators(p, rs)` reflects to a `≡_p`-equivalence.
pub proof fn lemma_derivation_reflects_to_base(
    p: Presentation, rs: Seq<Word>, steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        presentation_valid(p),
        forall|i: int| 0 <= i < rs.len() ==>
            word_valid(#[trigger] rs[i], p.num_generators)
            && equiv_in_presentation(p, rs[i], empty_word()),
        derivation_produces(add_relators(p, rs), steps, w1) == Some(w2),
    ensures
        equiv_in_presentation(p, w1, w2),
    decreases steps.len(),
{
    let q = add_relators(p, rs);
    if steps.len() == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(p, w1);
    } else {
        let step = steps.first();
        let next = apply_step(q, w1, step).unwrap();
        assert(apply_step(q, w1, step) == Some(next));
        lemma_step_reflects_to_base(p, rs, w1, step, next);    // w1 ≡_p next
        lemma_derivation_reflects_to_base(p, rs, steps.drop_first(), next, w2);  // next ≡_p w2
        lemma_equiv_transitive(p, w1, next, w2);
    }
}

/// **The reflecting base-swap (C3.0).** If every added relator is already a consequence of
/// `p`, then any equivalence over `add_relators(p, rs)` holds in `p` itself.
pub proof fn lemma_add_relators_reflects_equiv(
    p: Presentation, rs: Seq<Word>, w1: Word, w2: Word,
)
    requires
        presentation_valid(p),
        forall|i: int| 0 <= i < rs.len() ==>
            word_valid(#[trigger] rs[i], p.num_generators)
            && equiv_in_presentation(p, rs[i], empty_word()),
        equiv_in_presentation(add_relators(p, rs), w1, w2),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let q = add_relators(p, rs);
    let d = choose|d: Derivation| derivation_valid(q, d, w1, w2);
    assert(derivation_produces(q, d.steps, w1) == Some(w2));
    lemma_derivation_reflects_to_base(p, rs, d.steps, w1, w2);
}

/// **Group-preservation iff.** Adding consequence-relators does not change the group:
/// `equiv_in(p,·,·) ⟺ equiv_in(add_relators(p,rs),·,·)`.
pub proof fn lemma_add_derivable_relators_iff(
    p: Presentation, rs: Seq<Word>, w1: Word, w2: Word,
)
    requires
        presentation_valid(p),
        forall|i: int| 0 <= i < rs.len() ==>
            word_valid(#[trigger] rs[i], p.num_generators)
            && equiv_in_presentation(p, rs[i], empty_word()),
    ensures
        equiv_in_presentation(p, w1, w2)
            <==> equiv_in_presentation(add_relators(p, rs), w1, w2),
{
    if equiv_in_presentation(p, w1, w2) {
        lemma_add_relators_preserves_equiv(p, rs, w1, w2);
    }
    if equiv_in_presentation(add_relators(p, rs), w1, w2) {
        lemma_add_relators_reflects_equiv(p, rs, w1, w2);
    }
}

} // verus!
