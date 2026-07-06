// m4_defect_flow.rs — M-ladder rung M4 (mixed transduction): positivity of ⟨q,a,b,q′ | qa=bq′, q′b=aq⟩.
//
// docs/semantic-finite-basis.md §4.4 + docs/m4-defect-flow-brief.md. Tietze elimination (q′=b⁻¹qa,
// SAME substitution as M3) turns the second relator into q(ab)q⁻¹=ba, so
//   G ≅ ⟨a,b,q | q(ab)q⁻¹=ba⟩ — an HNN extension of F(a,b), stable letter q, associated subgroups
// ⟨ab⟩→⟨ba⟩ (the cycle word is now MIXED, ab vs ba). The M3 head-cap fails locally (syllable heads
// unbounded, local masquerade (ab)⁻¹·a = b⁻¹); the ⟹ readback is the DEFECT-FLOW argument.
//
// ORACLE (verified): G ≅ ℤ*ℤ². Set c=ab, p=aq; the relator becomes a⁻¹[p,c]a, so
//   G = ⟨a,c,p | [p,c]⟩ = ⟨a⟩ * (⟨c⟩×⟨p⟩). Translation a↦a, b↦a⁻¹c, q↦a⁻¹p, q′↦c⁻¹pa. Used only as
// a hand-check oracle here (e.g. the masquerade q′q=c⁻¹p² vs qq′=a⁻¹c⁻¹p²a never closes globally).
//
// ⟸ (Thue ⟹ group): immediate from thue.rs (lemma_m4_backward).
// ⟹ (group ⟹ Thue): the defect-flow readback (R2 series, forthcoming).
//
// Alphabet:  a = Gen(0)  b = Gen(1)  q = Gen(2)  q′ = Gen(3).   HNN target: a=Gen0,b=Gen1,q=Gen2.
//
// D1 (association orientation, confirmed from hnn.rs): hnn_relator(data,i) = t⁻¹·a_i·t·b_i⁻¹ for
// association (a_i,b_i), i.e. q⁻¹·a_i·q = b_i ⟺ q·b_i·q⁻¹ = a_i. For q(ab)q⁻¹=ba the tuple is
// (a_0,b_0) = (ba, ab).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::thue::*;

verus! {

pub open spec fn m4_rules() -> Seq<ThueRule> {
    seq![
        ThueRule { lhs: seq![Symbol::Gen(2), Symbol::Gen(0)], rhs: seq![Symbol::Gen(1), Symbol::Gen(3)] },  // qa = bq′
        ThueRule { lhs: seq![Symbol::Gen(3), Symbol::Gen(1)], rhs: seq![Symbol::Gen(0), Symbol::Gen(2)] },  // q′b = aq
    ]
}

pub proof fn lemma_m4_rules_valid()
    ensures
        forall|r: int| 0 <= r < m4_rules().len() ==>
            word_valid(#[trigger] m4_rules()[r].lhs, 4) && word_valid(m4_rules()[r].rhs, 4),
{
    assert forall|r: int| 0 <= r < m4_rules().len() implies
        word_valid(#[trigger] m4_rules()[r].lhs, 4) && word_valid(m4_rules()[r].rhs, 4) by {
        assert(word_valid(m4_rules()[0].lhs, 4)); assert(word_valid(m4_rules()[0].rhs, 4));
        assert(word_valid(m4_rules()[1].lhs, 4)); assert(word_valid(m4_rules()[1].rhs, 4));
    }
}

pub proof fn lemma_m4_pres_valid()
    ensures presentation_valid(rules_pres(m4_rules(), 4))
{
    reveal(presentation_valid);
    let p = rules_pres(m4_rules(), 4);
    lemma_m4_rules_valid();
    assert forall|i: int| 0 <= i < p.relators.len() implies word_valid(#[trigger] p.relators[i], 4) by {
        assert(p.relators[i] =~= thue_relator(m4_rules()[i]));
        let l = m4_rules()[i].lhs;
        let rr = m4_rules()[i].rhs;
        lemma_inverse_word_valid(rr, 4);
        assert forall|k: int| 0 <= k < concat(l, inverse_word(rr)).len()
            implies symbol_valid(#[trigger] concat(l, inverse_word(rr))[k], 4) by {
            if k < l.len() { assert(concat(l, inverse_word(rr))[k] == l[k]); }
            else { assert(concat(l, inverse_word(rr))[k] == inverse_word(rr)[k - l.len()]); }
        }
        assert(word_valid(concat(l, inverse_word(rr)), 4));
        assert(thue_relator(m4_rules()[i]) =~= concat(l, inverse_word(rr)));
    }
}

// ── ⟸  Thue ⟹ group (from thue.rs) ──
pub proof fn lemma_m4_backward(u: Word, v: Word)
    requires word_valid(u, 4), thue_equiv(m4_rules(), u, v),
    ensures equiv_in_presentation(rules_pres(m4_rules(), 4), u, v)
{
    lemma_m4_pres_valid();
    lemma_m4_rules_valid();
    lemma_thue_implies_group(m4_rules(), 4, u, v);
}

// ═══ The HNN instantiation: G ≅ ⟨a,b,q | q(ab)q⁻¹=ba⟩ ═══
// base = F(a,b); association (A,B)=(ba,ab) encodes q⁻¹(ba)q=ab ⟺ q(ab)q⁻¹=ba. stable letter q=Gen(2).
pub open spec fn m4_data() -> crate::hnn::HNNData {
    crate::hnn::HNNData {
        base: crate::higman_operations::free_group(2),
        associations: seq![ (seq![Symbol::Gen(1), Symbol::Gen(0)], seq![Symbol::Gen(0), Symbol::Gen(1)]) ],
    }
}

pub proof fn lemma_m4_data_valid()
    ensures crate::hnn::hnn_data_valid(m4_data())
{
    crate::higman_operations::lemma_free_group_valid(2);
    assert forall|i: int| 0 <= i < m4_data().associations.len() implies
        word_valid(#[trigger] m4_data().associations[i].0, 2)
        && word_valid(m4_data().associations[i].1, 2) by {
        assert(word_valid(m4_data().associations[0].0, 2));
        assert(word_valid(m4_data().associations[0].1, 2));
    }
}

// reduces_to an arbitrary target via 2 cancellations (copy of m3_blinker::m3_reduces2).
proof fn m4_reduces2(w0: Word, i0: int, w1: Word, i1: int, w2: Word)
    requires
        crate::reduction::has_cancellation_at(w0, i0), w1 == crate::reduction::reduce_at(w0, i0),
        crate::reduction::has_cancellation_at(w1, i1), w2 == crate::reduction::reduce_at(w1, i1),
    ensures crate::reduction::reduces_to(w0, w2)
{
    use crate::reduction::*;
    assert(reduces_in_steps(w2, w2, 0));
    assert(reduces_one_step(w1, w2)) by { assert(has_cancellation_at(w1, i1) && w2 == reduce_at(w1, i1)); }
    assert(reduces_in_steps(w1, w2, 1)) by { assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, w2, 0)); }
    assert(reduces_one_step(w0, w1)) by { assert(has_cancellation_at(w0, i0) && w1 == reduce_at(w0, i0)); }
    assert(reduces_in_steps(w0, w2, 2)) by { assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, w2, 1)); }
    assert(reduces_to(w0, w2)) by { assert(reduces_in_steps(w0, w2, 2)); }
}

// THE HNN RELATION: q(ab)q⁻¹ ≡ ba  in hnn_presentation(m4_data()).  (M4 analog of lemma_qa2_equiv_b2.)
pub proof fn lemma_qab_equiv_ba()
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)],  // q(ab)q⁻¹
        seq![Symbol::Gen(1), Symbol::Gen(0)])                                  // ba
{
    use crate::hnn::*;
    use crate::presentation_lemmas::*;
    let hp = hnn_presentation(m4_data());
    let ab = seq![Symbol::Gen(0), Symbol::Gen(1)];
    let ba = seq![Symbol::Gen(1), Symbol::Gen(0)];
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    // relator[0] = hnn_relator = q⁻¹·ba·q·(ab)⁻¹ = q⁻¹ ba q b⁻¹a⁻¹ ≡ ε
    let r = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0)];
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    assert(hnn_relator(m4_data(), 0) =~= r) by (compute);
    assert(hp.relators =~= hnn_relators(m4_data()));
    assert(hp.relators[0] =~= r);
    lemma_relator_is_identity(hp, 0);       // r ≡ ε
    // eq1: q⁻¹·ba·q ≡ ab   (right-multiply r by ab, cancel a⁻¹a then b⁻¹b)
    let qi_ba_q = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2)];
    lemma_equiv_concat_left(hp, r, empty_word(), ab);   // r·ab ≡ ε·ab
    assert(concat(empty_word(), ab) =~= ab);
    let r_ab = concat(r, ab);
    assert(r_ab =~= seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(1)]);
    // r_ab: idx5=Inv0,idx6=Gen0 cancel → then idx4=Inv1,idx5=Gen1 cancel → qi_ba_q
    let r_ab_1 = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(1), Symbol::Gen(1)];
    assert(crate::reduction::has_cancellation_at(r_ab, 5));
    assert(r_ab_1 == crate::reduction::reduce_at(r_ab, 5)) by { assert(r_ab_1 =~= crate::reduction::reduce_at(r_ab, 5)); }
    assert(crate::reduction::has_cancellation_at(r_ab_1, 4));
    assert(qi_ba_q == crate::reduction::reduce_at(r_ab_1, 4)) by { assert(qi_ba_q =~= crate::reduction::reduce_at(r_ab_1, 4)); }
    m4_reduces2(r_ab, 5, r_ab_1, 4, qi_ba_q);
    lemma_reduces_to_equiv(hp, r_ab, qi_ba_q);
    assert(word_valid(r_ab, 3));
    crate::presentation::lemma_equiv_symmetric(hp, r_ab, qi_ba_q);
    crate::presentation::lemma_equiv_transitive(hp, qi_ba_q, r_ab, ab);   // eq1: qi_ba_q ≡ ab
    // conjugate eq1 by q: q·(q⁻¹ba q)·q⁻¹ ≡ q·ab·q⁻¹, LHS reduces to ba
    lemma_equiv_concat_right(hp, q, qi_ba_q, ab);      // q·qi_ba_q ≡ q·ab
    let q_qi_ba_q = concat(q, qi_ba_q);
    let q_ab = concat(q, ab);
    lemma_equiv_concat_left(hp, q_qi_ba_q, q_ab, qi);  // (q·qi_ba_q)·q⁻¹ ≡ (q·ab)·q⁻¹
    let lhs = concat(q_qi_ba_q, qi);
    let rhs = concat(q_ab, qi);
    assert(lhs =~= seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(2)]);
    assert(rhs =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)]);
    // lhs: idx0(Gen2,Inv2)→[Gen1,Gen0,Gen2,Inv2] idx2(Gen2,Inv2)→[Gen1,Gen0]=ba
    let lhs1 = seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(2)];
    assert(crate::reduction::has_cancellation_at(lhs, 0));
    assert(lhs1 == crate::reduction::reduce_at(lhs, 0)) by { assert(lhs1 =~= crate::reduction::reduce_at(lhs, 0)); }
    assert(crate::reduction::has_cancellation_at(lhs1, 2));
    assert(ba == crate::reduction::reduce_at(lhs1, 2)) by { assert(ba =~= crate::reduction::reduce_at(lhs1, 2)); }
    m4_reduces2(lhs, 0, lhs1, 2, ba);
    lemma_reduces_to_equiv(hp, lhs, ba);
    assert(word_valid(lhs, 3));
    crate::presentation::lemma_equiv_symmetric(hp, lhs, rhs);        // rhs ≡ lhs
    crate::presentation::lemma_equiv_transitive(hp, rhs, lhs, ba);   // rhs ≡ ba = goal
}

// sub: G → hnn_presentation(m4_data()) (3 gens: a=Gen0,b=Gen1,q=Gen2), q′↦b⁻¹qa (byte-identical to M3).
pub open spec fn sub_hom() -> crate::homomorphism::HomomorphismData {
    crate::homomorphism::HomomorphismData {
        source: rules_pres(m4_rules(), 4),
        target: crate::hnn::hnn_presentation(m4_data()),
        generator_images: seq![
            seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(2)],
            seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)]
        ],
    }
}

// reduces_to ε via 3 cancellations (copy of m3_blinker::m3_reduces3).
proof fn m4_reduces3(w0: Word, i0: int, w1: Word, i1: int, w2: Word, i2: int)
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
    use crate::presentation_lemmas::{lemma_reduces_to_equiv, lemma_equiv_concat_left, lemma_equiv_concat_right};
    use crate::presentation::lemma_equiv_transitive;
    let h = sub_hom();
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_pres_valid();
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], 3) by { assert(word_valid(h.generator_images[i], 3)); }
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(hp, apply_hom(h, #[trigger] h.source.relators[i]), empty_word()) by {
        if i == 0 {
            // relator[0] = thue_relator(qa=bq′) = [Gen2,Gen0,Inv3,Inv1] — SAME as M3, reduces to ε
            assert(thue_relator(m4_rules()[0]) =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]) by (compute);
            assert(h.source.relators[0] =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]);
            let img = seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(0), Symbol::Inv(2), Symbol::Gen(1), Symbol::Inv(1)];
            assert(apply_hom(sub_hom(), seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]) =~= img) by (compute);
            let w1 = seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Inv(1)];
            let w2 = seq![Symbol::Gen(1), Symbol::Inv(1)];
            assert(crate::reduction::has_cancellation_at(img, 1));
            assert(w1 == crate::reduction::reduce_at(img, 1)) by { assert(w1 =~= crate::reduction::reduce_at(img, 1)); }
            assert(crate::reduction::has_cancellation_at(w1, 0));
            assert(w2 == crate::reduction::reduce_at(w1, 0)) by { assert(w2 =~= crate::reduction::reduce_at(w1, 0)); }
            assert(crate::reduction::has_cancellation_at(w2, 0));
            assert(crate::reduction::reduce_at(w2, 0) == empty_word()) by { assert(crate::reduction::reduce_at(w2, 0) =~= empty_word()); }
            m4_reduces3(img, 1, w1, 0, w2, 0);
            lemma_reduces_to_equiv(hp, img, empty_word());
        } else {
            // relator[1] = thue_relator(q′b=aq) = [Gen3,Gen1,Inv2,Inv0]; img2 = b⁻¹·(qabq⁻¹)·a⁻¹ ≡ b⁻¹·ba·a⁻¹ ≡ ε
            assert(thue_relator(m4_rules()[1]) =~= seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Inv(2), Symbol::Inv(0)]) by (compute);
            assert(h.source.relators[1] =~= seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Inv(2), Symbol::Inv(0)]);
            let img2 = seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2), Symbol::Inv(0)];
            assert(apply_hom(sub_hom(), seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Inv(2), Symbol::Inv(0)]) =~= img2) by (compute);
            let qabq = seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)];
            let ba = seq![Symbol::Gen(1), Symbol::Gen(0)];
            let bi = seq![Symbol::Inv(1)];
            let ai = seq![Symbol::Inv(0)];
            lemma_qab_equiv_ba();                                  // qabq ≡ ba
            lemma_equiv_concat_right(hp, bi, qabq, ba);            // bi·qabq ≡ bi·ba
            lemma_equiv_concat_left(hp, concat(bi, qabq), concat(bi, ba), ai);   // (bi·qabq)·ai ≡ (bi·ba)·ai
            assert(concat(concat(bi, qabq), ai) =~= img2);
            let bb = concat(concat(bi, ba), ai);
            assert(bb =~= seq![Symbol::Inv(1), Symbol::Gen(1), Symbol::Gen(0), Symbol::Inv(0)]);
            let bb1 = seq![Symbol::Gen(0), Symbol::Inv(0)];
            assert(crate::reduction::has_cancellation_at(bb, 0));
            assert(bb1 == crate::reduction::reduce_at(bb, 0)) by { assert(bb1 =~= crate::reduction::reduce_at(bb, 0)); }
            assert(crate::reduction::has_cancellation_at(bb1, 0));
            assert(crate::reduction::reduce_at(bb1, 0) == empty_word()) by { assert(crate::reduction::reduce_at(bb1, 0) =~= empty_word()); }
            m4_reduces2(bb, 0, bb1, 0, empty_word());
            lemma_reduces_to_equiv(hp, bb, empty_word());
            lemma_equiv_transitive(hp, img2, bb, empty_word());
        }
    }
}

// ── group-equal ⟹ sub-images equal in the HNN group ──
pub proof fn lemma_group_to_hnn(u: Word, v: Word)
    requires equiv_in_presentation(rules_pres(m4_rules(), 4), u, v),
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        crate::homomorphism::apply_hom(sub_hom(), u), crate::homomorphism::apply_hom(sub_hom(), v)),
{
    lemma_sub_valid();
    crate::homomorphism::lemma_hom_preserves_equiv(sub_hom(), u, v);
}

// ═══ R1 — discharge hnn_associations_isomorphic(m4_data()) via the a↔b swap automorphism ═══
// swap: F(a,b)→F(a,b), a↦b, b↦a (involution). swap(ba)=ab, so swap maps A-emb(w) to B-emb(w).
pub open spec fn swap_hom() -> crate::homomorphism::HomomorphismData {
    crate::homomorphism::HomomorphismData {
        source: crate::higman_operations::free_group(2),
        target: crate::higman_operations::free_group(2),
        generator_images: seq![ seq![Symbol::Gen(1)], seq![Symbol::Gen(0)] ],
    }
}

pub proof fn lemma_swap_valid()
    ensures crate::homomorphism::is_valid_homomorphism(swap_hom())
{
    use crate::homomorphism::*;
    crate::higman_operations::lemma_free_group_valid(2);
    let h = swap_hom();
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], 2) by { assert(word_valid(h.generator_images[i], 2)); }
    assert(h.source.relators.len() == 0);
}

// apply_hom distributes over concat (local helper).
pub proof fn lemma_apply_hom_concat(h: crate::homomorphism::HomomorphismData, a: Word, b: Word)
    ensures crate::homomorphism::apply_hom(h, a + b) =~=
        crate::homomorphism::apply_hom(h, a) + crate::homomorphism::apply_hom(h, b)
    decreases a.len()
{
    use crate::homomorphism::*;
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).first() == a.first());
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_apply_hom_concat(h, a.drop_first(), b);
    }
}

// swap∘(embed by src) = embed by tgt, given the per-generator swap facts.
pub proof fn lemma_swap_emb(src: Word, tgt: Word, w: Word)
    requires
        word_valid(w, 1),
        crate::homomorphism::apply_hom(swap_hom(), src) =~= tgt,
        crate::homomorphism::apply_hom(swap_hom(), inverse_word(src)) =~= inverse_word(tgt),
    ensures crate::homomorphism::apply_hom(swap_hom(), crate::benign::apply_embedding(seq![src], w))
        =~= crate::benign::apply_embedding(seq![tgt], w)
    decreases w.len()
{
    use crate::homomorphism::*;
    use crate::benign::*;
    if w.len() > 0 {
        let s = w[0];
        let rest = w.drop_first();
        assert(symbol_valid(s, 1));
        assert(word_valid(rest, 1)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 1) by { assert(rest[i] == w[i + 1]); }
        }
        assert(apply_embedding(seq![src], w) =~= apply_embedding_symbol(seq![src], s) + apply_embedding(seq![src], rest)) by {
            assert(w.first() == s);
        }
        lemma_apply_hom_concat(swap_hom(), apply_embedding_symbol(seq![src], s), apply_embedding(seq![src], rest));
        lemma_swap_emb(src, tgt, rest);
        if s == Symbol::Gen(0) {
            assert(apply_embedding_symbol(seq![src], s) == src);
            assert(apply_embedding_symbol(seq![tgt], s) == tgt);
        } else {
            assert(s == Symbol::Inv(0));
            assert(apply_embedding_symbol(seq![src], s) == inverse_word(src));
            assert(apply_embedding_symbol(seq![tgt], s) == inverse_word(tgt));
        }
        assert(apply_embedding(seq![tgt], w) =~= apply_embedding_symbol(seq![tgt], s) + apply_embedding(seq![tgt], rest)) by {
            assert(w.first() == s);
        }
    }
}

pub proof fn lemma_m4_iso()
    ensures crate::hnn::hnn_associations_isomorphic(m4_data())
{
    use crate::homomorphism::*;
    use crate::benign::*;
    let fg = crate::higman_operations::free_group(2);
    let col0 = seq![Symbol::Gen(1), Symbol::Gen(0)];   // ba = associations[0].0  (a_words entry)
    let col1 = seq![Symbol::Gen(0), Symbol::Gen(1)];   // ab = associations[0].1  (b_words entry)
    let a_words = Seq::new(1, |i: int| m4_data().associations[i].0);
    let b_words = Seq::new(1, |i: int| m4_data().associations[i].1);
    assert(a_words =~= seq![col0]);
    assert(b_words =~= seq![col1]);
    crate::higman_operations::lemma_free_group_valid(2);
    lemma_swap_valid();
    // per-generator swap facts — compute on LITERALS only
    assert(apply_hom(swap_hom(), seq![Symbol::Gen(1), Symbol::Gen(0)]) =~= seq![Symbol::Gen(0), Symbol::Gen(1)]) by (compute);
    assert(apply_hom(swap_hom(), seq![Symbol::Gen(0), Symbol::Gen(1)]) =~= seq![Symbol::Gen(1), Symbol::Gen(0)]) by (compute);
    assert(inverse_word(seq![Symbol::Gen(1), Symbol::Gen(0)]) =~= seq![Symbol::Inv(0), Symbol::Inv(1)]) by (compute);
    assert(inverse_word(seq![Symbol::Gen(0), Symbol::Gen(1)]) =~= seq![Symbol::Inv(1), Symbol::Inv(0)]) by (compute);
    assert(apply_hom(swap_hom(), seq![Symbol::Inv(0), Symbol::Inv(1)]) =~= seq![Symbol::Inv(1), Symbol::Inv(0)]) by (compute);
    assert(apply_hom(swap_hom(), seq![Symbol::Inv(1), Symbol::Inv(0)]) =~= seq![Symbol::Inv(0), Symbol::Inv(1)]) by (compute);
    // connect to the let-bound forms
    assert(apply_hom(swap_hom(), col0) =~= col1);
    assert(apply_hom(swap_hom(), col1) =~= col0);
    assert(apply_hom(swap_hom(), inverse_word(col0)) =~= inverse_word(col1));
    assert(apply_hom(swap_hom(), inverse_word(col1)) =~= inverse_word(col0));
    assert forall|w: Word| word_valid(w, 1) implies
        (equiv_in_presentation(fg, apply_embedding(a_words, w), empty_word())
         <==> equiv_in_presentation(fg, apply_embedding(b_words, w), empty_word())) by {
        assert(apply_embedding(a_words, w) =~= apply_embedding(seq![col0], w));
        assert(apply_embedding(b_words, w) =~= apply_embedding(seq![col1], w));
        if equiv_in_presentation(fg, apply_embedding(seq![col0], w), empty_word()) {
            lemma_hom_preserves_equiv(swap_hom(), apply_embedding(seq![col0], w), empty_word());
            lemma_swap_emb(col0, col1, w);
            assert(apply_hom(swap_hom(), empty_word()) =~= empty_word());
        }
        if equiv_in_presentation(fg, apply_embedding(seq![col1], w), empty_word()) {
            lemma_hom_preserves_equiv(swap_hom(), apply_embedding(seq![col1], w), empty_word());
            lemma_swap_emb(col1, col0, w);
            assert(apply_hom(swap_hom(), empty_word()) =~= empty_word());
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════
// B6 — the pw (power-word) library: (ab)^t and (ba)^t for t ∈ ℤ, over the HNN base F(a,b).
// Foundation for the defect-flow readback. Every compensation reduces to comparing these
// against shape words via free reduction. (K-identities forthcoming.)
// ═══════════════════════════════════════════════════════════════════════════════════════

// (ab)^t : t>0 ↦ (ab)^t = [a b a b …]; t<0 ↦ (b⁻¹a⁻¹)^|t|; t=0 ↦ ε.
pub open spec fn abpow(t: int) -> Word
    decreases (if t >= 0 { t } else { -t })
{
    if t == 0 { empty_word() }
    else if t > 0 { seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(t - 1) }
    else { seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(t + 1) }
}

// (ba)^t : t>0 ↦ (ba)^t = [b a b a …]; t<0 ↦ (a⁻¹b⁻¹)^|t|; t=0 ↦ ε.
pub open spec fn bapow(t: int) -> Word
    decreases (if t >= 0 { t } else { -t })
{
    if t == 0 { empty_word() }
    else if t > 0 { seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(t - 1) }
    else { seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(t + 1) }
}

pub proof fn lemma_abpow_valid(t: int)
    ensures word_valid(abpow(t), 2)
    decreases (if t >= 0 { t } else { -t })
{
    if t == 0 {
    } else if t > 0 {
        lemma_abpow_valid(t - 1);
        assert(word_valid(seq![Symbol::Gen(0), Symbol::Gen(1)], 2));
        crate::word::lemma_concat_word_valid(seq![Symbol::Gen(0), Symbol::Gen(1)], abpow(t - 1), 2);
        assert(concat(seq![Symbol::Gen(0), Symbol::Gen(1)], abpow(t - 1)) =~= abpow(t));
    } else {
        lemma_abpow_valid(t + 1);
        assert(word_valid(seq![Symbol::Inv(1), Symbol::Inv(0)], 2));
        crate::word::lemma_concat_word_valid(seq![Symbol::Inv(1), Symbol::Inv(0)], abpow(t + 1), 2);
        assert(concat(seq![Symbol::Inv(1), Symbol::Inv(0)], abpow(t + 1)) =~= abpow(t));
    }
}

pub proof fn lemma_bapow_valid(t: int)
    ensures word_valid(bapow(t), 2)
    decreases (if t >= 0 { t } else { -t })
{
    if t == 0 {
    } else if t > 0 {
        lemma_bapow_valid(t - 1);
        assert(word_valid(seq![Symbol::Gen(1), Symbol::Gen(0)], 2));
        crate::word::lemma_concat_word_valid(seq![Symbol::Gen(1), Symbol::Gen(0)], bapow(t - 1), 2);
        assert(concat(seq![Symbol::Gen(1), Symbol::Gen(0)], bapow(t - 1)) =~= bapow(t));
    } else {
        lemma_bapow_valid(t + 1);
        assert(word_valid(seq![Symbol::Inv(0), Symbol::Inv(1)], 2));
        crate::word::lemma_concat_word_valid(seq![Symbol::Inv(0), Symbol::Inv(1)], bapow(t + 1), 2);
        assert(concat(seq![Symbol::Inv(0), Symbol::Inv(1)], bapow(t + 1)) =~= bapow(t));
    }
}

// ── freely_equivalent congruence helpers (lift reduces_to congruence) ──
pub proof fn lemma_fe_from_reduces(x: Word, y: Word)
    requires crate::reduction::reduces_to(x, y),
    ensures crate::reduction::freely_equivalent(x, y),
{
    crate::reduction::lemma_reduces_to_refl(y);
    assert(crate::reduction::reduces_to(x, y) && crate::reduction::reduces_to(y, y));
}

pub proof fn lemma_fe_concat_left(p: Word, x: Word, y: Word)
    requires crate::reduction::freely_equivalent(x, y),
    ensures crate::reduction::freely_equivalent(p + x, p + y),
{
    use crate::reduction::*;
    let w = choose|w: Word| reduces_to(x, w) && reduces_to(y, w);
    lemma_reduces_to_concat_right(p, x, w);   // reduces_to(p+x, p+w)
    lemma_reduces_to_concat_right(p, y, w);   // reduces_to(p+y, p+w)
    assert(concat(p, x) =~= p + x);
    assert(concat(p, y) =~= p + y);
    assert(concat(p, w) =~= p + w);
    assert(reduces_to(p + x, p + w) && reduces_to(p + y, p + w));
}

pub proof fn lemma_fe_concat_right(x: Word, y: Word, s: Word)
    requires crate::reduction::freely_equivalent(x, y),
    ensures crate::reduction::freely_equivalent(x + s, y + s),
{
    use crate::reduction::*;
    let w = choose|w: Word| reduces_to(x, w) && reduces_to(y, w);
    lemma_reduces_to_concat_left(x, w, s);    // reduces_to(x+s, w+s)
    lemma_reduces_to_concat_left(y, w, s);    // reduces_to(y+s, w+s)
    assert(concat(x, s) =~= x + s);
    assert(concat(y, s) =~= y + s);
    assert(concat(w, s) =~= w + s);
    assert(reduces_to(x + s, w + s) && reduces_to(y + s, w + s));
}

// ── prepend atoms: prepending one ab / (ab)⁻¹ block to abpow(t) shifts the exponent ──
pub proof fn lemma_abpow_prepend_ab(t: int)
    ensures crate::reduction::reduces_to(seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(t), abpow(t + 1)),
{
    use crate::reduction::*;
    if t >= 0 {
        assert(abpow(t + 1) =~= seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(t));
        lemma_reduces_to_refl(seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(t));
    } else {
        let tail = abpow(t + 1);
        assert(abpow(t) =~= seq![Symbol::Inv(1), Symbol::Inv(0)] + tail);
        let block = seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(1), Symbol::Inv(0)];
        assert(seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(t) =~= block + tail);
        let block1 = seq![Symbol::Gen(0), Symbol::Inv(0)];
        assert(has_cancellation_at(block, 1));
        assert(block1 == reduce_at(block, 1)) by { assert(block1 =~= reduce_at(block, 1)); }
        assert(has_cancellation_at(block1, 0));
        assert(reduce_at(block1, 0) == empty_word()) by { assert(reduce_at(block1, 0) =~= empty_word()); }
        m4_reduces2(block, 1, block1, 0, empty_word());        // reduces_to(block, ε)
        lemma_reduces_to_concat_left(block, empty_word(), tail);  // reduces_to(block+tail, ε+tail)
        assert(concat(block, tail) =~= block + tail);
        assert(concat(empty_word(), tail) =~= tail);
    }
}

pub proof fn lemma_abpow_prepend_abinv(t: int)
    ensures crate::reduction::reduces_to(seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(t), abpow(t - 1)),
{
    use crate::reduction::*;
    if t <= 0 {
        assert(abpow(t - 1) =~= seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(t));
        lemma_reduces_to_refl(seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(t));
    } else {
        let tail = abpow(t - 1);
        assert(abpow(t) =~= seq![Symbol::Gen(0), Symbol::Gen(1)] + tail);
        let block = seq![Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(1)];
        assert(seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(t) =~= block + tail);
        let block1 = seq![Symbol::Inv(1), Symbol::Gen(1)];
        assert(has_cancellation_at(block, 1));
        assert(block1 == reduce_at(block, 1)) by { assert(block1 =~= reduce_at(block, 1)); }
        assert(has_cancellation_at(block1, 0));
        assert(reduce_at(block1, 0) == empty_word()) by { assert(reduce_at(block1, 0) =~= empty_word()); }
        m4_reduces2(block, 1, block1, 0, empty_word());
        lemma_reduces_to_concat_left(block, empty_word(), tail);
        assert(concat(block, tail) =~= block + tail);
        assert(concat(empty_word(), tail) =~= tail);
    }
}

pub proof fn lemma_bapow_prepend_ba(t: int)
    ensures crate::reduction::reduces_to(seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(t), bapow(t + 1)),
{
    use crate::reduction::*;
    if t >= 0 {
        assert(bapow(t + 1) =~= seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(t));
        lemma_reduces_to_refl(seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(t));
    } else {
        let tail = bapow(t + 1);
        assert(bapow(t) =~= seq![Symbol::Inv(0), Symbol::Inv(1)] + tail);
        let block = seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Inv(0), Symbol::Inv(1)];
        assert(seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(t) =~= block + tail);
        let block1 = seq![Symbol::Gen(1), Symbol::Inv(1)];
        assert(has_cancellation_at(block, 1));
        assert(block1 == reduce_at(block, 1)) by { assert(block1 =~= reduce_at(block, 1)); }
        assert(has_cancellation_at(block1, 0));
        assert(reduce_at(block1, 0) == empty_word()) by { assert(reduce_at(block1, 0) =~= empty_word()); }
        m4_reduces2(block, 1, block1, 0, empty_word());
        lemma_reduces_to_concat_left(block, empty_word(), tail);
        assert(concat(block, tail) =~= block + tail);
        assert(concat(empty_word(), tail) =~= tail);
    }
}

pub proof fn lemma_bapow_prepend_bainv(t: int)
    ensures crate::reduction::reduces_to(seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(t), bapow(t - 1)),
{
    use crate::reduction::*;
    if t <= 0 {
        assert(bapow(t - 1) =~= seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(t));
        lemma_reduces_to_refl(seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(t));
    } else {
        let tail = bapow(t - 1);
        assert(bapow(t) =~= seq![Symbol::Gen(1), Symbol::Gen(0)] + tail);
        let block = seq![Symbol::Inv(0), Symbol::Inv(1), Symbol::Gen(1), Symbol::Gen(0)];
        assert(seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(t) =~= block + tail);
        let block1 = seq![Symbol::Inv(0), Symbol::Gen(0)];
        assert(has_cancellation_at(block, 1));
        assert(block1 == reduce_at(block, 1)) by { assert(block1 =~= reduce_at(block, 1)); }
        assert(has_cancellation_at(block1, 0));
        assert(reduce_at(block1, 0) == empty_word()) by { assert(reduce_at(block1, 0) =~= empty_word()); }
        m4_reduces2(block, 1, block1, 0, empty_word());
        lemma_reduces_to_concat_left(block, empty_word(), tail);
        assert(concat(block, tail) =~= block + tail);
        assert(concat(empty_word(), tail) =~= tail);
    }
}

// ── K3: the additive law (ab)^s·(ab)^t reduces to (ab)^(s+t), and same for ba ──
pub proof fn lemma_abpow_add(s: int, t: int)
    ensures crate::reduction::reduces_to(abpow(s) + abpow(t), abpow(s + t)),
    decreases (if s >= 0 { s } else { -s }),
{
    use crate::reduction::*;
    if s == 0 {
        assert(abpow(s) + abpow(t) =~= abpow(t));
        assert(abpow(s + t) == abpow(t));
        lemma_reduces_to_refl(abpow(t));
    } else if s > 0 {
        assert(abpow(s) =~= seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(s - 1));
        let mid1 = seq![Symbol::Gen(0), Symbol::Gen(1)] + (abpow(s - 1) + abpow(t));
        let mid2 = seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(s - 1 + t);
        assert(abpow(s) + abpow(t) =~= mid1);
        lemma_abpow_add(s - 1, t);                                                   // abpow(s-1)+abpow(t) →* abpow(s-1+t)
        lemma_reduces_to_concat_right(seq![Symbol::Gen(0), Symbol::Gen(1)], abpow(s - 1) + abpow(t), abpow(s - 1 + t));
        assert(concat(seq![Symbol::Gen(0), Symbol::Gen(1)], abpow(s - 1) + abpow(t)) =~= mid1);
        assert(concat(seq![Symbol::Gen(0), Symbol::Gen(1)], abpow(s - 1 + t)) =~= mid2);
        lemma_abpow_prepend_ab(s - 1 + t);                                           // mid2 →* abpow(s-1+t+1)
        assert(abpow(s - 1 + t + 1) == abpow(s + t));
        lemma_reduces_to_transitive(mid1, mid2, abpow(s + t));
    } else {
        assert(abpow(s) =~= seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(s + 1));
        let mid1 = seq![Symbol::Inv(1), Symbol::Inv(0)] + (abpow(s + 1) + abpow(t));
        let mid2 = seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(s + 1 + t);
        assert(abpow(s) + abpow(t) =~= mid1);
        lemma_abpow_add(s + 1, t);
        lemma_reduces_to_concat_right(seq![Symbol::Inv(1), Symbol::Inv(0)], abpow(s + 1) + abpow(t), abpow(s + 1 + t));
        assert(concat(seq![Symbol::Inv(1), Symbol::Inv(0)], abpow(s + 1) + abpow(t)) =~= mid1);
        assert(concat(seq![Symbol::Inv(1), Symbol::Inv(0)], abpow(s + 1 + t)) =~= mid2);
        lemma_abpow_prepend_abinv(s + 1 + t);
        assert(abpow(s + 1 + t - 1) == abpow(s + t));
        lemma_reduces_to_transitive(mid1, mid2, abpow(s + t));
    }
}

pub proof fn lemma_bapow_add(s: int, t: int)
    ensures crate::reduction::reduces_to(bapow(s) + bapow(t), bapow(s + t)),
    decreases (if s >= 0 { s } else { -s }),
{
    use crate::reduction::*;
    if s == 0 {
        assert(bapow(s) + bapow(t) =~= bapow(t));
        assert(bapow(s + t) == bapow(t));
        lemma_reduces_to_refl(bapow(t));
    } else if s > 0 {
        assert(bapow(s) =~= seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(s - 1));
        let mid1 = seq![Symbol::Gen(1), Symbol::Gen(0)] + (bapow(s - 1) + bapow(t));
        let mid2 = seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(s - 1 + t);
        assert(bapow(s) + bapow(t) =~= mid1);
        lemma_bapow_add(s - 1, t);
        lemma_reduces_to_concat_right(seq![Symbol::Gen(1), Symbol::Gen(0)], bapow(s - 1) + bapow(t), bapow(s - 1 + t));
        assert(concat(seq![Symbol::Gen(1), Symbol::Gen(0)], bapow(s - 1) + bapow(t)) =~= mid1);
        assert(concat(seq![Symbol::Gen(1), Symbol::Gen(0)], bapow(s - 1 + t)) =~= mid2);
        lemma_bapow_prepend_ba(s - 1 + t);
        assert(bapow(s - 1 + t + 1) == bapow(s + t));
        lemma_reduces_to_transitive(mid1, mid2, bapow(s + t));
    } else {
        assert(bapow(s) =~= seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(s + 1));
        let mid1 = seq![Symbol::Inv(0), Symbol::Inv(1)] + (bapow(s + 1) + bapow(t));
        let mid2 = seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(s + 1 + t);
        assert(bapow(s) + bapow(t) =~= mid1);
        lemma_bapow_add(s + 1, t);
        lemma_reduces_to_concat_right(seq![Symbol::Inv(0), Symbol::Inv(1)], bapow(s + 1) + bapow(t), bapow(s + 1 + t));
        assert(concat(seq![Symbol::Inv(0), Symbol::Inv(1)], bapow(s + 1) + bapow(t)) =~= mid1);
        assert(concat(seq![Symbol::Inv(0), Symbol::Inv(1)], bapow(s + 1 + t)) =~= mid2);
        lemma_bapow_prepend_bainv(s + 1 + t);
        assert(bapow(s + 1 + t - 1) == bapow(s + t));
        lemma_reduces_to_transitive(mid1, mid2, bapow(s + t));
    }
}

// reduces_to via a single cancellation.
proof fn m4_reduces1(w0: Word, i0: int, w1: Word)
    requires crate::reduction::has_cancellation_at(w0, i0), w1 == crate::reduction::reduce_at(w0, i0),
    ensures crate::reduction::reduces_to(w0, w1)
{
    use crate::reduction::*;
    assert(reduces_one_step(w0, w1)) by { assert(has_cancellation_at(w0, i0) && w1 == reduce_at(w0, i0)); }
    assert(reduces_in_steps(w1, w1, 0));
    assert(reduces_in_steps(w0, w1, 1)) by { assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, w1, 0)); }
}

// a·a⁻¹ (concrete cancelling pair) reduces to ε.
proof fn lemma_pair_cancels(x: Symbol, xi: Symbol)
    requires is_inverse_pair(x, xi),
    ensures crate::reduction::reduces_to(seq![x, xi], empty_word()),
{
    use crate::reduction::*;
    let p = seq![x, xi];
    assert(has_cancellation_at(p, 0));
    assert(reduce_at(p, 0) == empty_word()) by { assert(reduce_at(p, 0) =~= empty_word()); }
    m4_reduces1(p, 0, empty_word());
}

// ── K1 (conj_a): a·(ba)^t =_F (ab)^t·a  (pull `a` left through the mixed cycle) ──
pub proof fn lemma_conj_a(t: int)
    ensures crate::reduction::freely_equivalent(seq![Symbol::Gen(0)] + bapow(t), abpow(t) + seq![Symbol::Gen(0)]),
    decreases (if t >= 0 { t } else { -t }),
{
    use crate::reduction::*;
    let a = seq![Symbol::Gen(0)];
    if t == 0 {
        assert(a + bapow(0) =~= a);
        assert(abpow(0) + a =~= a);
        lemma_freely_equivalent_refl(a);
    } else if t > 0 {
        // both sides = [ab] + (inductive body), congruence step
        assert(a + bapow(t) =~= seq![Symbol::Gen(0), Symbol::Gen(1)] + (a + bapow(t - 1)));
        assert(abpow(t) + a =~= seq![Symbol::Gen(0), Symbol::Gen(1)] + (abpow(t - 1) + a));
        lemma_conj_a(t - 1);
        lemma_fe_concat_left(seq![Symbol::Gen(0), Symbol::Gen(1)], a + bapow(t - 1), abpow(t - 1) + a);
    } else {
        // t < 0.  Both sides freely reduce to M = b⁻¹·(ba)^(t+1).
        let m = seq![Symbol::Inv(1)] + bapow(t + 1);
        // LHS = a·(ba)^t = [a a⁻¹]·(b⁻¹·(ba)^(t+1)) →* M
        assert(a + bapow(t) =~= seq![Symbol::Gen(0), Symbol::Inv(0)] + m);
        lemma_pair_cancels(Symbol::Gen(0), Symbol::Inv(0));
        lemma_reduces_to_concat_left(seq![Symbol::Gen(0), Symbol::Inv(0)], empty_word(), m);
        assert(concat(seq![Symbol::Gen(0), Symbol::Inv(0)], m) =~= a + bapow(t));
        assert(concat(empty_word(), m) =~= m);
        lemma_fe_from_reduces(a + bapow(t), m);                       // fe(LHS, M)
        // RHS = (ab)^t·a = [b⁻¹a⁻¹]·((ab)^(t+1)·a);  IH: (ab)^(t+1)·a =_F a·(ba)^(t+1)
        lemma_conj_a(t + 1);
        lemma_freely_equivalent_sym(a + bapow(t + 1), abpow(t + 1) + a);
        lemma_fe_concat_left(seq![Symbol::Inv(1), Symbol::Inv(0)], abpow(t + 1) + a, a + bapow(t + 1));
        let w = seq![Symbol::Inv(1), Symbol::Inv(0)] + (a + bapow(t + 1));
        assert(abpow(t) + a =~= seq![Symbol::Inv(1), Symbol::Inv(0)] + (abpow(t + 1) + a));
        // fe(RHS, W) where W = [b⁻¹a⁻¹]·(a·(ba)^(t+1));  W →* M via a⁻¹a cancel under b⁻¹
        assert(w =~= seq![Symbol::Inv(1)] + (seq![Symbol::Inv(0), Symbol::Gen(0)] + bapow(t + 1)));
        lemma_pair_cancels(Symbol::Inv(0), Symbol::Gen(0));
        lemma_reduces_to_concat_left(seq![Symbol::Inv(0), Symbol::Gen(0)], empty_word(), bapow(t + 1));
        assert(concat(seq![Symbol::Inv(0), Symbol::Gen(0)], bapow(t + 1)) =~= seq![Symbol::Inv(0), Symbol::Gen(0)] + bapow(t + 1));
        assert(concat(empty_word(), bapow(t + 1)) =~= bapow(t + 1));
        lemma_reduces_to_concat_right(seq![Symbol::Inv(1)], seq![Symbol::Inv(0), Symbol::Gen(0)] + bapow(t + 1), bapow(t + 1));
        assert(concat(seq![Symbol::Inv(1)], seq![Symbol::Inv(0), Symbol::Gen(0)] + bapow(t + 1)) =~= w);
        assert(concat(seq![Symbol::Inv(1)], bapow(t + 1)) =~= m);
        lemma_fe_from_reduces(w, m);                                  // fe(W, M)
        // chain: fe(RHS, W), fe(W, M) ⟹ fe(RHS, M); fe(LHS, M) ⟹ fe(LHS, RHS)
        lemma_freely_equivalent_trans(abpow(t) + a, w, m);           // fe(RHS, M)
        lemma_freely_equivalent_sym(abpow(t) + a, m);                // fe(M, RHS)
        lemma_freely_equivalent_trans(a + bapow(t), m, abpow(t) + a);
    }
}

// helper: b⁻¹·(ba)^t =_F a·(ba)^(t-1)  (a single cancellation either direction)
pub proof fn lemma_binv_bapow(t: int)
    ensures crate::reduction::freely_equivalent(seq![Symbol::Inv(1)] + bapow(t), seq![Symbol::Gen(0)] + bapow(t - 1)),
{
    use crate::reduction::*;
    if t > 0 {
        // [b⁻¹]·(ba)^t = [b⁻¹ b]·(a)·(ba)^(t-1)... reduce (b⁻¹,b) → a·(ba)^(t-1)
        assert(seq![Symbol::Inv(1)] + bapow(t) =~= seq![Symbol::Inv(1), Symbol::Gen(1)] + (seq![Symbol::Gen(0)] + bapow(t - 1)));
        lemma_pair_cancels(Symbol::Inv(1), Symbol::Gen(1));
        lemma_reduces_to_concat_left(seq![Symbol::Inv(1), Symbol::Gen(1)], empty_word(), seq![Symbol::Gen(0)] + bapow(t - 1));
        assert(concat(seq![Symbol::Inv(1), Symbol::Gen(1)], seq![Symbol::Gen(0)] + bapow(t - 1)) =~= seq![Symbol::Inv(1)] + bapow(t));
        assert(concat(empty_word(), seq![Symbol::Gen(0)] + bapow(t - 1)) =~= seq![Symbol::Gen(0)] + bapow(t - 1));
        lemma_fe_from_reduces(seq![Symbol::Inv(1)] + bapow(t), seq![Symbol::Gen(0)] + bapow(t - 1));
    } else {
        // t ≤ 0: [a]·(ba)^(t-1) = [a a⁻¹]·(b⁻¹)·(ba)^t → reduce → [b⁻¹]·(ba)^t
        assert(seq![Symbol::Gen(0)] + bapow(t - 1) =~= seq![Symbol::Gen(0), Symbol::Inv(0)] + (seq![Symbol::Inv(1)] + bapow(t)));
        lemma_pair_cancels(Symbol::Gen(0), Symbol::Inv(0));
        lemma_reduces_to_concat_left(seq![Symbol::Gen(0), Symbol::Inv(0)], empty_word(), seq![Symbol::Inv(1)] + bapow(t));
        assert(concat(seq![Symbol::Gen(0), Symbol::Inv(0)], seq![Symbol::Inv(1)] + bapow(t)) =~= seq![Symbol::Gen(0)] + bapow(t - 1));
        assert(concat(empty_word(), seq![Symbol::Inv(1)] + bapow(t)) =~= seq![Symbol::Inv(1)] + bapow(t));
        lemma_fe_from_reduces(seq![Symbol::Gen(0)] + bapow(t - 1), seq![Symbol::Inv(1)] + bapow(t));
        lemma_freely_equivalent_sym(seq![Symbol::Gen(0)] + bapow(t - 1), seq![Symbol::Inv(1)] + bapow(t));
    }
}

// ── K2 (conj_binv): b⁻¹·(ba)^t =_F (ab)^(t-1)·a ──
pub proof fn lemma_conj_binv(t: int)
    ensures crate::reduction::freely_equivalent(seq![Symbol::Inv(1)] + bapow(t), abpow(t - 1) + seq![Symbol::Gen(0)]),
{
    use crate::reduction::*;
    lemma_binv_bapow(t);                                             // b⁻¹(ba)^t =_F a(ba)^(t-1)
    lemma_conj_a(t - 1);                                             // a(ba)^(t-1) =_F (ab)^(t-1)a
    lemma_freely_equivalent_trans(seq![Symbol::Inv(1)] + bapow(t), seq![Symbol::Gen(0)] + bapow(t - 1), abpow(t - 1) + seq![Symbol::Gen(0)]);
}

} // verus!
