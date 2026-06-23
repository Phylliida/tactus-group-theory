use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::*;
use crate::pred_free_product::*;
use crate::free_product::{shift_symbol, shift_word};

verus! {

//  ============================================================
//  FORK-A brick 4 — predicate-base amalgamated free products (2026-06-23).
//
//  Predicate-base analog of `amalgamated_free_product.rs`, over
//  `PredPresentation`.  This is the last piece of the relator-agnostic
//  CONSTRUCTION layer (the forward directions) — the AFP *injectivity* (the
//  normal form) is the reserved multi-week arc and lives elsewhere.
//
//  Includes a small predicate `add_relators` layer (analog of `quotient.rs`'s
//  add_relators machinery), defined DIRECTLY as an OR rather than recursively:
//  adding a FINITE set of relators to a predicate presentation just OR's the
//  membership into the predicate (same pattern as `pred_hnn`'s
//  `hnn_all_relator_pred`).
//
//  Kept separate from finite `amalgamated_free_product` (reversible, zero
//  regression).
//  ============================================================

//  ============================================================
//  Predicate add_relators layer.
//  ============================================================

///  Predicate after adding the finite relator set `rs`: an original relator, or
///  one of the `rs[i]`.
pub open spec fn added_relators_pred(p: PredPresentation, rs: Seq<Word>, w: Word) -> bool {
    (p.relators)(w) || (exists|i: int| 0 <= i < rs.len() && w == rs[i])
}

///  Add a finite set of relators to a predicate presentation (generators
///  unchanged).
pub open spec fn add_relators_pred(p: PredPresentation, rs: Seq<Word>) -> PredPresentation {
    PredPresentation {
        num_generators: p.num_generators,
        relators: |w: Word| added_relators_pred(p, rs, w),
    }
}

///  A step valid in p is valid in add_relators_pred(p, rs) (the predicate is
///  monotone; num_generators is unchanged).
proof fn lemma_step_valid_in_add_relators_pred(
    p: PredPresentation, rs: Seq<Word>, w: Word, step: PredDerivationStep, w_prime: Word,
)
    requires
        apply_step_pred(p, w, step) == Some(w_prime),
    ensures
        apply_step_pred(add_relators_pred(p, rs), w, step) == Some(w_prime),
{
    let ap = add_relators_pred(p, rs);
    match step {
        PredDerivationStep::FreeReduce { position } => {},
        PredDerivationStep::FreeExpand { position, symbol } => {
            //  num_generators unchanged ⟹ identical guard
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            assert((p.relators)(relator));
            assert(added_relators_pred(p, rs, relator));
            assert((ap.relators)(relator));
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert((p.relators)(relator));
            assert(added_relators_pred(p, rs, relator));
            assert((ap.relators)(relator));
        },
    }
}

proof fn lemma_derivation_valid_in_add_relators_pred(
    p: PredPresentation, rs: Seq<Word>, steps: Seq<PredDerivationStep>, w1: Word, w2: Word,
)
    requires
        pred_derivation_produces(p, steps, w1) == Some(w2),
    ensures
        pred_derivation_produces(add_relators_pred(p, rs), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step_pred(p, w1, step).unwrap();
        lemma_step_valid_in_add_relators_pred(p, rs, w1, step, next);
        lemma_derivation_valid_in_add_relators_pred(p, rs, steps.drop_first(), next, w2);
    }
}

///  Adding relators preserves existing equivalences.
pub proof fn lemma_add_relators_pred_preserves_equiv(
    p: PredPresentation, rs: Seq<Word>, w1: Word, w2: Word,
)
    requires
        equiv_in_pred_presentation(p, w1, w2),
    ensures
        equiv_in_pred_presentation(add_relators_pred(p, rs), w1, w2),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p, d, w1, w2);
    lemma_derivation_valid_in_add_relators_pred(p, rs, d.steps, w1, w2);
    let d2 = PredDerivation { steps: d.steps };
    assert(pred_derivation_valid(add_relators_pred(p, rs), d2, w1, w2));
}

///  Each added relator is the identity in the extended presentation.
pub proof fn lemma_each_added_relator_pred_is_identity(
    p: PredPresentation, rs: Seq<Word>, i: int,
)
    requires
        0 <= i < rs.len(),
    ensures
        equiv_in_pred_presentation(add_relators_pred(p, rs), rs[i], empty_word()),
{
    let ap = add_relators_pred(p, rs);
    assert(added_relators_pred(p, rs, rs[i])) by {
        assert(0 <= i < rs.len() && rs[i] == rs[i]);
    }
    assert((ap.relators)(rs[i]));
    lemma_pred_relator_is_identity(ap, rs[i]);
}

///  Adding relators preserves validity when all added words are word_valid.
pub proof fn lemma_add_relators_pred_valid(p: PredPresentation, rs: Seq<Word>)
    requires
        pred_presentation_valid(p),
        forall|i: int| 0 <= i < rs.len() ==> word_valid(rs[i], p.num_generators),
    ensures
        pred_presentation_valid(add_relators_pred(p, rs)),
{
    reveal(pred_presentation_valid);
    let ap = add_relators_pred(p, rs);
    assert forall|w: Word| #![trigger (ap.relators)(w)] (ap.relators)(w) implies word_valid(w, ap.num_generators) by {
        assert((ap.relators)(w) == added_relators_pred(p, rs, w));
        if (p.relators)(w) {
            assert(word_valid(w, p.num_generators));
        } else {
            let i = choose|i: int| 0 <= i < rs.len() && w == rs[i];
            assert(word_valid(rs[i], p.num_generators));
        }
    }
}

//  ============================================================
//  Predicate amalgamated free product.
//  ============================================================

///  Data for a predicate amalgamated free product.
pub struct PredAmalgamatedData {
    pub p1: PredPresentation,
    pub p2: PredPresentation,
    pub identifications: Seq<(Word, Word)>,
}

///  Validity of the amalgamation data.
pub open spec fn amalgamated_data_pred_valid(data: PredAmalgamatedData) -> bool {
    pred_presentation_valid(data.p1)
    && pred_presentation_valid(data.p2)
    && forall|i: int| #![trigger data.identifications[i]] 0 <= i < data.identifications.len() ==>
        word_valid(data.identifications[i].0, data.p1.num_generators)
        && word_valid(data.identifications[i].1, data.p2.num_generators)
}

///  Build the i-th identification relator: u_i · shift(v_i)⁻¹.
pub open spec fn amalgamation_relator_pred(data: PredAmalgamatedData, i: int) -> Word
    recommends
        0 <= i < data.identifications.len(),
{
    let (u_i, v_i) = data.identifications[i];
    let shifted_v = shift_word(v_i, data.p1.num_generators);
    concat(u_i, inverse_word(shifted_v))
}

///  All identification relators.
pub open spec fn amalgamation_relators_pred(data: PredAmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| amalgamation_relator_pred(data, i))
}

///  The amalgamated free product: free_product_pred(p1, p2) + identification relators.
pub open spec fn amalgamated_free_product_pred(data: PredAmalgamatedData) -> PredPresentation {
    add_relators_pred(free_product_pred(data.p1, data.p2), amalgamation_relators_pred(data))
}

///  Shifted word validity helper (relator-agnostic; word-level).
proof fn lemma_shift_word_valid_into(w: Word, offset: nat, m: nat)
    requires
        word_valid(w, m),
    ensures
        word_valid(shift_word(w, offset), (offset + m) as nat),
{
    let sw = shift_word(w, offset);
    let n = (offset + m) as nat;
    assert forall|k: int| 0 <= k < sw.len() implies symbol_valid(#[trigger] sw[k], n) by {
        assert(sw[k] == shift_symbol(w[k], offset));
        assert(symbol_valid(w[k], m));
    }
}

///  The amalgamated free product is valid.
pub proof fn lemma_amalgamated_pred_valid(data: PredAmalgamatedData)
    requires
        amalgamated_data_pred_valid(data),
    ensures
        pred_presentation_valid(amalgamated_free_product_pred(data)),
{
    let fp = free_product_pred(data.p1, data.p2);
    let rels = amalgamation_relators_pred(data);
    let n = (data.p1.num_generators + data.p2.num_generators) as nat;

    //  fp is valid: a left relator (word_valid for p1.ng ≤ n) or a shifted
    //  right relator (word_valid for n by lemma_shift_word_valid_into).
    assert(pred_presentation_valid(fp)) by {
        reveal(pred_presentation_valid);
        assert forall|w: Word| #![trigger (fp.relators)(w)] (fp.relators)(w) implies word_valid(w, fp.num_generators) by {
            assert((fp.relators)(w) == free_product_pred_relators(data.p1, data.p2, w));
            if (data.p1.relators)(w) {
                assert(word_valid(w, data.p1.num_generators));
                assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], fp.num_generators) by {
                    assert(symbol_valid(w[k], data.p1.num_generators));
                }
            } else {
                assert(shifted_pred(data.p2.relators, data.p1.num_generators, w));
                let w0 = choose|w0: Word| (data.p2.relators)(w0) && w == shift_word(w0, data.p1.num_generators);
                assert(word_valid(w0, data.p2.num_generators));
                lemma_shift_word_valid_into(w0, data.p1.num_generators, data.p2.num_generators);
                assert(fp.num_generators == n);
            }
        }
    }

    //  each amalgamation relator is word_valid for fp
    assert forall|i: int| 0 <= i < rels.len() implies word_valid(rels[i], fp.num_generators) by {
        assert(rels[i] == amalgamation_relator_pred(data, i));
        let (u_i, v_i) = data.identifications[i];
        let shifted_v = shift_word(v_i, data.p1.num_generators);
        assert(word_valid(u_i, data.p1.num_generators));
        assert(word_valid(u_i, fp.num_generators)) by {
            assert forall|k: int| 0 <= k < u_i.len() implies symbol_valid(#[trigger] u_i[k], fp.num_generators) by {
                assert(symbol_valid(u_i[k], data.p1.num_generators));
            }
        }
        assert(word_valid(v_i, data.p2.num_generators));
        lemma_shift_word_valid_into(v_i, data.p1.num_generators, data.p2.num_generators);
        assert(word_valid(shifted_v, fp.num_generators));
        crate::word::lemma_inverse_word_valid(shifted_v, fp.num_generators);
        crate::word::lemma_concat_word_valid(u_i, inverse_word(shifted_v), fp.num_generators);
    }

    lemma_add_relators_pred_valid(fp, rels);
}

///  Left embedding: equiv in p1 ⟹ equiv in the amalgamated product.
pub proof fn lemma_left_embeds_in_amalgamation_pred(
    data: PredAmalgamatedData, w1: Word, w2: Word,
)
    requires
        equiv_in_pred_presentation(data.p1, w1, w2),
    ensures
        equiv_in_pred_presentation(amalgamated_free_product_pred(data), w1, w2),
{
    lemma_left_embeds_pred(data.p1, data.p2, w1, w2);
    lemma_add_relators_pred_preserves_equiv(
        free_product_pred(data.p1, data.p2),
        amalgamation_relators_pred(data),
        w1, w2,
    );
}

///  Right embedding: equiv in p2 ⟹ equiv of shifted words in the amalgamated product.
pub proof fn lemma_right_embeds_in_amalgamation_pred(
    data: PredAmalgamatedData, w1: Word, w2: Word,
)
    requires
        equiv_in_pred_presentation(data.p2, w1, w2),
    ensures
        equiv_in_pred_presentation(
            amalgamated_free_product_pred(data),
            shift_word(w1, data.p1.num_generators),
            shift_word(w2, data.p1.num_generators),
        ),
{
    lemma_right_embeds_pred(data.p1, data.p2, w1, w2);
    lemma_add_relators_pred_preserves_equiv(
        free_product_pred(data.p1, data.p2),
        amalgamation_relators_pred(data),
        shift_word(w1, data.p1.num_generators),
        shift_word(w2, data.p1.num_generators),
    );
}

///  Free product embeds in amalgamation.
pub proof fn lemma_free_product_embeds_in_amalgamation_pred(
    data: PredAmalgamatedData, w1: Word, w2: Word,
)
    requires
        equiv_in_pred_presentation(free_product_pred(data.p1, data.p2), w1, w2),
    ensures
        equiv_in_pred_presentation(amalgamated_free_product_pred(data), w1, w2),
{
    lemma_add_relators_pred_preserves_equiv(
        free_product_pred(data.p1, data.p2),
        amalgamation_relators_pred(data),
        w1, w2,
    );
}

///  The identified words are equivalent: u_i ≡ shift(v_i) in the amalgamation.
pub proof fn lemma_amalgamation_identifies_pred(data: PredAmalgamatedData, i: int)
    requires
        amalgamated_data_pred_valid(data),
        0 <= i < data.identifications.len(),
    ensures
        equiv_in_pred_presentation(
            amalgamated_free_product_pred(data),
            data.identifications[i].0,
            shift_word(data.identifications[i].1, data.p1.num_generators),
        ),
{
    let afp = amalgamated_free_product_pred(data);
    let (u_i, v_i) = data.identifications[i];
    let shifted_v = shift_word(v_i, data.p1.num_generators);
    let rel = amalgamation_relator_pred(data, i);
    let rels = amalgamation_relators_pred(data);
    let fp = free_product_pred(data.p1, data.p2);

    assert(rel == concat(u_i, inverse_word(shifted_v)));
    assert(rels[i] == rel);

    //  rel ≡ ε
    lemma_each_added_relator_pred_is_identity(fp, rels, i);

    //  concat(rel, shifted_v) ≡ shifted_v
    lemma_pred_equiv_concat_left(afp, rel, empty_word(), shifted_v);
    assert(concat(empty_word(), shifted_v) =~= shifted_v);
    lemma_pred_equiv_refl(afp, shifted_v);
    lemma_pred_equiv_transitive(afp, concat(rel, shifted_v), concat(empty_word(), shifted_v), shifted_v);

    assert(concat(rel, shifted_v) =~= concat(u_i, concat(inverse_word(shifted_v), shifted_v)));

    //  inv(shifted_v) · shifted_v ≡ ε
    lemma_pred_word_inverse_left(afp, shifted_v);

    //  u_i · (inv(sv) · sv) ≡ u_i · ε ≡ u_i
    lemma_pred_equiv_concat_right(afp, u_i, concat(inverse_word(shifted_v), shifted_v), empty_word());
    assert(concat(u_i, empty_word()) =~= u_i);
    lemma_pred_equiv_refl(afp, u_i);
    lemma_pred_equiv_transitive(
        afp,
        concat(u_i, concat(inverse_word(shifted_v), shifted_v)),
        concat(u_i, empty_word()),
        u_i,
    );

    //  validity + word_valid for the symmetric step
    lemma_amalgamated_pred_valid(data);
    let n = afp.num_generators;
    assert(n == fp.num_generators);

    assert(word_valid(u_i, n)) by {
        assert(word_valid(u_i, data.p1.num_generators));
        assert forall|k: int| 0 <= k < u_i.len() implies symbol_valid(#[trigger] u_i[k], n) by {
            assert(symbol_valid(u_i[k], data.p1.num_generators));
        }
    }
    assert(word_valid(v_i, data.p2.num_generators));
    lemma_shift_word_valid_into(v_i, data.p1.num_generators, data.p2.num_generators);
    assert(word_valid(shifted_v, n));
    crate::word::lemma_inverse_word_valid(shifted_v, n);
    crate::word::lemma_concat_word_valid(inverse_word(shifted_v), shifted_v, n);
    crate::word::lemma_concat_word_valid(u_i, concat(inverse_word(shifted_v), shifted_v), n);

    //  u_i ≡ concat(u_i, concat(inv(sv), sv)) (symmetric)
    lemma_pred_equiv_symmetric(afp, concat(u_i, concat(inverse_word(shifted_v), shifted_v)), u_i);

    //  Chain: u_i ≡ concat(u_i, concat(inv(sv), sv)) = concat(rel, sv) ≡ shifted_v
    lemma_pred_equiv_transitive(
        afp,
        u_i,
        concat(u_i, concat(inverse_word(shifted_v), shifted_v)),
        shifted_v,
    );
}

} //  verus!
