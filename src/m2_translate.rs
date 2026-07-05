// m2_translate.rs — M-ladder rung M2 (read/translate): positivity of ⟨q,a,b,q′ | qa = bq′⟩.
//
// docs/semantic-finite-basis.md §4.2. The group is F(q,a,b) (Tietze: q′ = b⁻¹qa).
//   positivity(m2_rules, 4): for positive u,v over {a,b,q,q′}:
//     u = v in the group  ⟺  u ↔*_{qa=bq′} v.
//
// ⟸ (Thue ⟹ group): immediate from thue.rs.
// ⟹ (group ⟹ Thue): sub: G → F(q,a,b) (q′↦b⁻¹qa) is a hom (no retraction needed — unlike M0).
//   Orient bq′→qa (nf = no `bq′` substring, #q′ strictly decreases → complete). NO-CANCELLATION
//   READBACK: sub(w) for a no-bq′ word has no cancellations (b⁻¹ heads only sub(q′), cancels only a
//   literal preceding b = the excluded `bq′`), so sub(nf) is reduced-as-written and parses back
//   letterwise (first symbol ∈ {Gen0,Gen1,Gen2,Inv1}, all distinct). sub injective on nf.
//
// Alphabet:  a = Gen(0)  b = Gen(1)  q = Gen(2)  q′ = Gen(3).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::thue::*;

verus! {

pub open spec fn m2_rules() -> Seq<ThueRule> {
    seq![ ThueRule {
        lhs: seq![Symbol::Gen(2), Symbol::Gen(0)],   // q a
        rhs: seq![Symbol::Gen(1), Symbol::Gen(3)],   // b q′
    } ]
}

pub proof fn lemma_m2_rules_valid()
    ensures
        forall|r: int| 0 <= r < m2_rules().len() ==>
            word_valid(#[trigger] m2_rules()[r].lhs, 4) && word_valid(m2_rules()[r].rhs, 4),
{
    assert forall|r: int| 0 <= r < m2_rules().len() implies
        word_valid(#[trigger] m2_rules()[r].lhs, 4) && word_valid(m2_rules()[r].rhs, 4) by {
        assert(word_valid(m2_rules()[0].lhs, 4));
        assert(word_valid(m2_rules()[0].rhs, 4));
    }
}

pub proof fn lemma_m2_pres_valid()
    ensures presentation_valid(rules_pres(m2_rules(), 4))
{
    reveal(presentation_valid);
    let p = rules_pres(m2_rules(), 4);
    lemma_m2_rules_valid();
    assert forall|i: int| 0 <= i < p.relators.len() implies word_valid(#[trigger] p.relators[i], 4) by {
        assert(p.relators[0] =~= thue_relator(m2_rules()[0]));
        let l = m2_rules()[0].lhs;
        let rr = m2_rules()[0].rhs;
        lemma_inverse_word_valid(rr, 4);
        assert forall|k: int| 0 <= k < concat(l, inverse_word(rr)).len()
            implies symbol_valid(#[trigger] concat(l, inverse_word(rr))[k], 4) by {
            if k < l.len() { assert(concat(l, inverse_word(rr))[k] == l[k]); }
            else { assert(concat(l, inverse_word(rr))[k] == inverse_word(rr)[k - l.len()]); }
        }
        assert(word_valid(concat(l, inverse_word(rr)), 4));
        assert(thue_relator(m2_rules()[0]) =~= concat(l, inverse_word(rr)));
    }
}

// ── ⟸  Thue ⟹ group (from thue.rs) ──
pub proof fn lemma_m2_backward(u: Word, v: Word)
    requires word_valid(u, 4), thue_equiv(m2_rules(), u, v),
    ensures equiv_in_presentation(rules_pres(m2_rules(), 4), u, v)
{
    lemma_m2_pres_valid();
    lemma_m2_rules_valid();
    lemma_thue_implies_group(m2_rules(), 4, u, v);
}

// ═══ sub: G → F(q,a,b), q′ ↦ b⁻¹qa (the Tietze hom).  a=0,b=1,q=2 in target. ═══
pub open spec fn sub_hom() -> crate::homomorphism::HomomorphismData {
    crate::homomorphism::HomomorphismData {
        source: rules_pres(m2_rules(), 4),
        target: crate::higman_operations::free_group(3),
        generator_images: seq![
            seq![Symbol::Gen(0)],                              // a ↦ a
            seq![Symbol::Gen(1)],                              // b ↦ b
            seq![Symbol::Gen(2)],                              // q ↦ q
            seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)]  // q′ ↦ b⁻¹qa
        ],
    }
}

// reduces_to(w0, ε) via 3 explicit cancellations (for the relator image).
proof fn m2_reduces3(w0: Word, i0: int, w1: Word, i1: int, w2: Word, i2: int)
    requires
        crate::reduction::has_cancellation_at(w0, i0), w1 == crate::reduction::reduce_at(w0, i0),
        crate::reduction::has_cancellation_at(w1, i1), w2 == crate::reduction::reduce_at(w1, i1),
        crate::reduction::has_cancellation_at(w2, i2), crate::reduction::reduce_at(w2, i2) == empty_word(),
    ensures crate::reduction::reduces_to(w0, empty_word())
{
    use crate::reduction::*;
    assert(reduces_one_step(w2, empty_word())) by { assert(has_cancellation_at(w2, i2) && empty_word() == reduce_at(w2, i2)); }
    assert(reduces_in_steps(w2, empty_word(), 1)) by { assert(reduces_one_step(w2, empty_word()) && reduces_in_steps(empty_word(), empty_word(), 0)); }
    assert(reduces_one_step(w1, w2)) by { assert(has_cancellation_at(w1, i1) && w2 == reduce_at(w1, i1)); }
    assert(reduces_in_steps(w1, empty_word(), 2)) by { assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, empty_word(), 1)); }
    assert(reduces_one_step(w0, w1)) by { assert(has_cancellation_at(w0, i0) && w1 == reduce_at(w0, i0)); }
    assert(reduces_in_steps(w0, empty_word(), 3)) by { assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, empty_word(), 2)); }
    assert(reduces_to(w0, empty_word())) by { assert(reduces_in_steps(w0, empty_word(), 3)); }
}

pub proof fn lemma_sub_valid()
    ensures crate::homomorphism::is_valid_homomorphism(sub_hom()),
{
    use crate::homomorphism::*;
    use crate::higman_operations::{free_group, lemma_free_group_valid};
    let h = sub_hom();
    lemma_m2_pres_valid();
    lemma_free_group_valid(3);
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], 3) by {
        assert(word_valid(h.generator_images[i], 3));
    }
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(h.target, apply_hom(h, #[trigger] h.source.relators[i]), empty_word()) by {
        // relator[0] = qaq′⁻¹b⁻¹ = [Gen2,Gen0,Inv3,Inv1] ; sub-image = [Gen2,Gen0,Inv0,Inv2,Gen1,Inv1]
        assert(thue_relator(m2_rules()[0]) =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]) by (compute);
        assert(h.source.relators[0] =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]);
        let img = seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(0), Symbol::Inv(2), Symbol::Gen(1), Symbol::Inv(1)];
        // compute on sub_hom() DIRECTLY — `by (compute)` does not see through the let-bound `h`
        assert(apply_hom(sub_hom(), seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]) =~= img) by (compute);
        // img reduces to ε: @1(Gen0,Inv0)→[Gen2,Inv2,Gen1,Inv1] @0(Gen2,Inv2)→[Gen1,Inv1] @0→ε
        let w1: Word = seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Inv(1)];
        let w2: Word = seq![Symbol::Gen(1), Symbol::Inv(1)];
        assert(crate::reduction::has_cancellation_at(img, 1));
        assert(w1 == crate::reduction::reduce_at(img, 1)) by { assert(w1 =~= crate::reduction::reduce_at(img, 1)); }
        assert(crate::reduction::has_cancellation_at(w1, 0));
        assert(w2 == crate::reduction::reduce_at(w1, 0)) by { assert(w2 =~= crate::reduction::reduce_at(w1, 0)); }
        assert(crate::reduction::has_cancellation_at(w2, 0));
        assert(crate::reduction::reduce_at(w2, 0) == empty_word()) by { assert(crate::reduction::reduce_at(w2, 0) =~= empty_word()); }
        m2_reduces3(img, 1, w1, 0, w2, 0);
        crate::presentation_lemmas::lemma_reduces_to_equiv(free_group(3), img, empty_word());
    }
}

// ── group-equal ⟹ sub-images freely equivalent (the ⟹ engine's first step) ──
pub proof fn lemma_group_implies_sub_equal(u: Word, v: Word)
    requires equiv_in_presentation(rules_pres(m2_rules(), 4), u, v),
    ensures crate::reduction::freely_equivalent(
        crate::homomorphism::apply_hom(sub_hom(), u), crate::homomorphism::apply_hom(sub_hom(), v))
{
    use crate::homomorphism::*;
    use crate::higman_operations::free_group;
    lemma_sub_valid();
    lemma_hom_preserves_equiv(sub_hom(), u, v);
    crate::free_word_problem::lemma_free_group_equiv_freely_equivalent(3,
        apply_hom(sub_hom(), u), apply_hom(sub_hom(), v));
}

} // verus!