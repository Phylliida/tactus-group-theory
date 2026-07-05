// m3_blinker.rs — M-ladder rung M3 (THE BLINKER): positivity of ⟨q,a,b,q′ | qa=bq′, q′a=bq⟩.
//
// docs/semantic-finite-basis.md §4.3. THE CRITICAL TEST: Tietze elimination (q′=b⁻¹qa) turns the
// second relator into qa²q⁻¹=b², so  G ≅ ⟨a,b,q | qa²q⁻¹=b²⟩ — an HNN extension of F(a,b), stable
// letter q, associated subgroups ⟨a²⟩→⟨b²⟩. NOT free: neither M1's two-projection nor M2's
// free-reduction readback applies. The ⟹ uses BRITTON'S LEMMA (britton_via_tower::britton_lemma_full)
// + the parity head-cap argument.
//
// ⟸ (Thue ⟹ group): immediate from thue.rs.
// ⟹ (group ⟹ Thue): sub: G → ⟨a,b,q|qa²q⁻¹=b²⟩ (q′↦b⁻¹qa, same images as M2, HNN target).
//   sub(u),sub(v) are Britton-reduced (all q positive ⟹ no pinch). sub(u)=sub(v) ⟹ [Britton]
//   same q-count k + syllable compensations dᵢ=a^{2mᵢ}∈⟨a²⟩; the head-cap (irreducible ⟹ each
//   syllable's a-head ∈{0,1}) + parity (even shift −2mᵢ exits {0,1}) forces all mᵢ=0 ⟹ readback.
//
// Alphabet:  a = Gen(0)  b = Gen(1)  q = Gen(2)  q′ = Gen(3).   HNN target: a=Gen0,b=Gen1,q=Gen2.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::thue::*;

verus! {

pub open spec fn m3_rules() -> Seq<ThueRule> {
    seq![
        ThueRule { lhs: seq![Symbol::Gen(2), Symbol::Gen(0)], rhs: seq![Symbol::Gen(1), Symbol::Gen(3)] },  // qa = bq′
        ThueRule { lhs: seq![Symbol::Gen(3), Symbol::Gen(0)], rhs: seq![Symbol::Gen(1), Symbol::Gen(2)] },  // q′a = bq
    ]
}

pub proof fn lemma_m3_rules_valid()
    ensures
        forall|r: int| 0 <= r < m3_rules().len() ==>
            word_valid(#[trigger] m3_rules()[r].lhs, 4) && word_valid(m3_rules()[r].rhs, 4),
{
    assert forall|r: int| 0 <= r < m3_rules().len() implies
        word_valid(#[trigger] m3_rules()[r].lhs, 4) && word_valid(m3_rules()[r].rhs, 4) by {
        assert(word_valid(m3_rules()[0].lhs, 4)); assert(word_valid(m3_rules()[0].rhs, 4));
        assert(word_valid(m3_rules()[1].lhs, 4)); assert(word_valid(m3_rules()[1].rhs, 4));
    }
}

pub proof fn lemma_m3_pres_valid()
    ensures presentation_valid(rules_pres(m3_rules(), 4))
{
    reveal(presentation_valid);
    let p = rules_pres(m3_rules(), 4);
    lemma_m3_rules_valid();
    assert forall|i: int| 0 <= i < p.relators.len() implies word_valid(#[trigger] p.relators[i], 4) by {
        assert(p.relators[i] =~= thue_relator(m3_rules()[i]));
        let l = m3_rules()[i].lhs;
        let rr = m3_rules()[i].rhs;
        lemma_inverse_word_valid(rr, 4);
        assert forall|k: int| 0 <= k < concat(l, inverse_word(rr)).len()
            implies symbol_valid(#[trigger] concat(l, inverse_word(rr))[k], 4) by {
            if k < l.len() { assert(concat(l, inverse_word(rr))[k] == l[k]); }
            else { assert(concat(l, inverse_word(rr))[k] == inverse_word(rr)[k - l.len()]); }
        }
        assert(word_valid(concat(l, inverse_word(rr)), 4));
        assert(thue_relator(m3_rules()[i]) =~= concat(l, inverse_word(rr)));
    }
}

// ── ⟸  Thue ⟹ group (from thue.rs) ──
pub proof fn lemma_m3_backward(u: Word, v: Word)
    requires word_valid(u, 4), thue_equiv(m3_rules(), u, v),
    ensures equiv_in_presentation(rules_pres(m3_rules(), 4), u, v)
{
    lemma_m3_pres_valid();
    lemma_m3_rules_valid();
    lemma_thue_implies_group(m3_rules(), 4, u, v);
}

// ═══ The HNN instantiation: G ≅ ⟨a,b,q | qa²q⁻¹=b²⟩ ═══
// base = F(a,b); association (A,B)=(b²,a²) encodes q⁻¹b²q=a² ⟺ qa²q⁻¹=b². stable letter q=Gen(2).
pub open spec fn m3_data() -> crate::hnn::HNNData {
    crate::hnn::HNNData {
        base: crate::higman_operations::free_group(2),
        associations: seq![ (seq![Symbol::Gen(1), Symbol::Gen(1)], seq![Symbol::Gen(0), Symbol::Gen(0)]) ],
    }
}

pub proof fn lemma_m3_data_valid()
    ensures crate::hnn::hnn_data_valid(m3_data())
{
    crate::higman_operations::lemma_free_group_valid(2);
    assert forall|i: int| 0 <= i < m3_data().associations.len() implies
        word_valid(#[trigger] m3_data().associations[i].0, 2)
        && word_valid(m3_data().associations[i].1, 2) by {
        assert(word_valid(m3_data().associations[0].0, 2));
        assert(word_valid(m3_data().associations[0].1, 2));
    }
}

// sub: G → hnn_presentation(m3_data()) (3 gens: a=Gen0,b=Gen1,q=Gen2), q′↦b⁻¹qa (same images as M2).
pub open spec fn sub_hom() -> crate::homomorphism::HomomorphismData {
    crate::homomorphism::HomomorphismData {
        source: rules_pres(m3_rules(), 4),
        target: crate::hnn::hnn_presentation(m3_data()),
        generator_images: seq![
            seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(2)],
            seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)]
        ],
    }
}

// reduces_to helpers to an arbitrary target (2 / 3 cancellations)
proof fn m3_reduces2(w0: Word, i0: int, w1: Word, i1: int, w2: Word)
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

// THE HNN RELATION: qa²q⁻¹ ≡ b²  in hnn_presentation(m3_data()).
pub proof fn lemma_qa2_equiv_b2()
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m3_data()),
        seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(0), Symbol::Inv(2)],
        seq![Symbol::Gen(1), Symbol::Gen(1)])
{
    use crate::hnn::*;
    use crate::presentation_lemmas::*;
    let hp = hnn_presentation(m3_data());
    let a2 = seq![Symbol::Gen(0), Symbol::Gen(0)];
    let b2 = seq![Symbol::Gen(1), Symbol::Gen(1)];
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    // relator[0] = hnn_relator = q⁻¹b²qa⁻² ≡ ε
    let r = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(0), Symbol::Inv(0)];
    lemma_m3_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m3_data());
    assert(hnn_relator(m3_data(), 0) =~= r) by (compute);
    assert(hp.relators =~= hnn_relators(m3_data()));
    assert(hp.relators[0] =~= r);
    lemma_relator_is_identity(hp, 0);       // r ≡ ε
    // eq1: q⁻¹b²q ≡ a²   (right-multiply r by a², cancel a⁻²a²)
    let qi_b2_q = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(1), Symbol::Gen(2)];
    lemma_equiv_concat_left(hp, r, empty_word(), a2);   // r·a² ≡ ε·a²
    assert(concat(empty_word(), a2) =~= a2);
    let ra2 = concat(r, a2);
    assert(ra2 =~= seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(0), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(0)]);
    // ra2 reduces: @5(Inv0,Gen0)→ len8→7? reduce removes 2. @4 then @? Let me: idx4=Inv0,idx5=Inv0,idx6=Gen0,idx7=Gen0. cancellation at 5 (Inv0,Gen0). → [..Gen2,Inv0,Gen0] then at 4 (Inv0,Gen0) → qi_b2_q
    let ra2_1 = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(0), Symbol::Gen(0)];
    assert(crate::reduction::has_cancellation_at(ra2, 5));
    assert(ra2_1 == crate::reduction::reduce_at(ra2, 5)) by { assert(ra2_1 =~= crate::reduction::reduce_at(ra2, 5)); }
    assert(crate::reduction::has_cancellation_at(ra2_1, 4));
    assert(qi_b2_q == crate::reduction::reduce_at(ra2_1, 4)) by { assert(qi_b2_q =~= crate::reduction::reduce_at(ra2_1, 4)); }
    m3_reduces2(ra2, 5, ra2_1, 4, qi_b2_q);
    lemma_reduces_to_equiv(hp, ra2, qi_b2_q);
    // ra2 ≡ a2 (concat_left) and ra2 ≡ qi_b2_q (reduces) ⟹ qi_b2_q ≡ a2
    assert(word_valid(ra2, 3));
    crate::presentation::lemma_equiv_symmetric(hp, ra2, qi_b2_q);
    crate::presentation::lemma_equiv_transitive(hp, qi_b2_q, ra2, a2);   // eq1: qi_b2_q ≡ a2
    // conjugate eq1 by q: q·(q⁻¹b²q)·q⁻¹ ≡ q·a²·q⁻¹, LHS reduces to b²
    lemma_equiv_concat_right(hp, q, qi_b2_q, a2);      // q·qi_b2_q ≡ q·a²
    let q_qibq = concat(q, qi_b2_q);
    let q_a2 = concat(q, a2);
    lemma_equiv_concat_left(hp, q_qibq, q_a2, qi);     // (q·qi_b2_q)·q⁻¹ ≡ (q·a²)·q⁻¹
    let lhs = concat(q_qibq, qi);
    let rhs = concat(q_a2, qi);
    assert(lhs =~= seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(2)]);
    assert(rhs =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(0), Symbol::Inv(2)]);
    // lhs reduces: @0(Gen2,Inv2)→[Gen1,Gen1,Gen2,Inv2] @2(Gen2,Inv2)→[Gen1,Gen1]=b2
    let lhs1 = seq![Symbol::Gen(1), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(2)];
    assert(crate::reduction::has_cancellation_at(lhs, 0));
    assert(lhs1 == crate::reduction::reduce_at(lhs, 0)) by { assert(lhs1 =~= crate::reduction::reduce_at(lhs, 0)); }
    assert(crate::reduction::has_cancellation_at(lhs1, 2));
    assert(b2 == crate::reduction::reduce_at(lhs1, 2)) by { assert(b2 =~= crate::reduction::reduce_at(lhs1, 2)); }
    m3_reduces2(lhs, 0, lhs1, 2, b2);
    lemma_reduces_to_equiv(hp, lhs, b2);
    // lhs ≡ b2 (reduces) and lhs ≡ rhs (concat) ⟹ rhs ≡ b2 = goal
    assert(word_valid(lhs, 3));
    crate::presentation::lemma_equiv_symmetric(hp, lhs, rhs);        // rhs ≡ lhs
    crate::presentation::lemma_equiv_transitive(hp, rhs, lhs, b2);   // rhs ≡ b2 = goal
}

// reduces_to ε via 3 cancellations
proof fn m3_reduces3(w0: Word, i0: int, w1: Word, i1: int, w2: Word, i2: int)
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
    let hp = crate::hnn::hnn_presentation(m3_data());
    lemma_m3_pres_valid();
    lemma_m3_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m3_data());
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], 3) by { assert(word_valid(h.generator_images[i], 3)); }
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(hp, apply_hom(h, #[trigger] h.source.relators[i]), empty_word()) by {
        if i == 0 {
            assert(thue_relator(m3_rules()[0]) =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]) by (compute);
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
            m3_reduces3(img, 1, w1, 0, w2, 0);
            lemma_reduces_to_equiv(hp, img, empty_word());
        } else {
            assert(thue_relator(m3_rules()[1]) =~= seq![Symbol::Gen(3), Symbol::Gen(0), Symbol::Inv(2), Symbol::Inv(1)]) by (compute);
            assert(h.source.relators[1] =~= seq![Symbol::Gen(3), Symbol::Gen(0), Symbol::Inv(2), Symbol::Inv(1)]);
            let img2 = seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(0), Symbol::Inv(2), Symbol::Inv(1)];
            assert(apply_hom(sub_hom(), seq![Symbol::Gen(3), Symbol::Gen(0), Symbol::Inv(2), Symbol::Inv(1)]) =~= img2) by (compute);
            let qa2q = seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(0), Symbol::Inv(2)];
            let b2 = seq![Symbol::Gen(1), Symbol::Gen(1)];
            let bi = seq![Symbol::Inv(1)];
            lemma_qa2_equiv_b2();                                  // qa2q ≡ b2
            lemma_equiv_concat_right(hp, bi, qa2q, b2);            // bi·qa2q ≡ bi·b2
            lemma_equiv_concat_left(hp, concat(bi, qa2q), concat(bi, b2), bi);   // (bi·qa2q)·bi ≡ (bi·b2)·bi
            assert(concat(concat(bi, qa2q), bi) =~= img2);
            let bb = concat(concat(bi, b2), bi);
            assert(bb =~= seq![Symbol::Inv(1), Symbol::Gen(1), Symbol::Gen(1), Symbol::Inv(1)]);
            let bb1 = seq![Symbol::Gen(1), Symbol::Inv(1)];
            assert(crate::reduction::has_cancellation_at(bb, 0));
            assert(bb1 == crate::reduction::reduce_at(bb, 0)) by { assert(bb1 =~= crate::reduction::reduce_at(bb, 0)); }
            assert(crate::reduction::has_cancellation_at(bb1, 0));
            assert(crate::reduction::reduce_at(bb1, 0) == empty_word()) by { assert(crate::reduction::reduce_at(bb1, 0) =~= empty_word()); }
            m3_reduces2(bb, 0, bb1, 0, empty_word());
            lemma_reduces_to_equiv(hp, bb, empty_word());
            lemma_equiv_transitive(hp, img2, bb, empty_word());
        }
    }
}

// ── group-equal ⟹ sub-images equal in the HNN group ──
pub proof fn lemma_group_to_hnn(u: Word, v: Word)
    requires equiv_in_presentation(rules_pres(m3_rules(), 4), u, v),
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m3_data()),
        crate::homomorphism::apply_hom(sub_hom(), u), crate::homomorphism::apply_hom(sub_hom(), v)),
{
    lemma_sub_valid();
    crate::homomorphism::lemma_hom_preserves_equiv(sub_hom(), u, v);
}

// ═══ R1 — discharge hnn_associations_isomorphic(m3_data()) via the a↔b swap automorphism ═══
// swap: F(a,b) → F(a,b), a↦b, b↦a (an involution). swap(b²)=a², so swap(A-emb(w))=B-emb(w).
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
    // free_group(2) has no relators ⟹ relator condition vacuous
    assert(h.source.relators.len() == 0);
}

// apply_hom distributes over concat (local helper)
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
        assert(symbol_valid(s, 1));   // s ∈ {Gen0, Inv0}
        assert(word_valid(rest, 1)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 1) by { assert(rest[i] == w[i + 1]); }
        }
        // apply_embedding(seq![src], w) = apply_embedding_symbol(seq![src], s) + apply_embedding(seq![src], rest)
        assert(apply_embedding(seq![src], w) =~= apply_embedding_symbol(seq![src], s) + apply_embedding(seq![src], rest)) by {
            assert(w.first() == s);
        }
        lemma_apply_hom_concat(swap_hom(), apply_embedding_symbol(seq![src], s), apply_embedding(seq![src], rest));
        lemma_swap_emb(src, tgt, rest);
        // per-symbol: apply_hom(swap, apply_embedding_symbol(seq![src],s)) = apply_embedding_symbol(seq![tgt],s)
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

pub proof fn lemma_m3_iso()
    ensures crate::hnn::hnn_associations_isomorphic(m3_data())
{
    use crate::homomorphism::*;
    use crate::benign::*;
    let fg = crate::higman_operations::free_group(2);
    let b2 = seq![Symbol::Gen(1), Symbol::Gen(1)];
    let a2 = seq![Symbol::Gen(0), Symbol::Gen(0)];
    let a_words = Seq::new(1, |i: int| m3_data().associations[i].0);
    let b_words = Seq::new(1, |i: int| m3_data().associations[i].1);
    assert(a_words =~= seq![b2]);
    assert(b_words =~= seq![a2]);
    crate::higman_operations::lemma_free_group_valid(2);
    lemma_swap_valid();
    // per-generator swap facts — compute on LITERALS only (compute HANGS on let-bound b2/a2)
    assert(apply_hom(swap_hom(), seq![Symbol::Gen(1), Symbol::Gen(1)]) =~= seq![Symbol::Gen(0), Symbol::Gen(0)]) by (compute);
    assert(apply_hom(swap_hom(), seq![Symbol::Gen(0), Symbol::Gen(0)]) =~= seq![Symbol::Gen(1), Symbol::Gen(1)]) by (compute);
    assert(inverse_word(seq![Symbol::Gen(1), Symbol::Gen(1)]) =~= seq![Symbol::Inv(1), Symbol::Inv(1)]) by (compute);
    assert(inverse_word(seq![Symbol::Gen(0), Symbol::Gen(0)]) =~= seq![Symbol::Inv(0), Symbol::Inv(0)]) by (compute);
    assert(apply_hom(swap_hom(), seq![Symbol::Inv(1), Symbol::Inv(1)]) =~= seq![Symbol::Inv(0), Symbol::Inv(0)]) by (compute);
    assert(apply_hom(swap_hom(), seq![Symbol::Inv(0), Symbol::Inv(0)]) =~= seq![Symbol::Inv(1), Symbol::Inv(1)]) by (compute);
    // connect to the let-bound forms (b2 == seq![Gen1,Gen1], a2 == seq![Gen0,Gen0])
    assert(apply_hom(swap_hom(), b2) =~= a2);
    assert(apply_hom(swap_hom(), a2) =~= b2);
    assert(apply_hom(swap_hom(), inverse_word(b2)) =~= inverse_word(a2));
    assert(apply_hom(swap_hom(), inverse_word(a2)) =~= inverse_word(b2));
    assert forall|w: Word| word_valid(w, 1) implies
        (equiv_in_presentation(fg, apply_embedding(a_words, w), empty_word())
         <==> equiv_in_presentation(fg, apply_embedding(b_words, w), empty_word())) by {
        assert(apply_embedding(a_words, w) =~= apply_embedding(seq![b2], w));
        assert(apply_embedding(b_words, w) =~= apply_embedding(seq![a2], w));
        if equiv_in_presentation(fg, apply_embedding(seq![b2], w), empty_word()) {
            lemma_hom_preserves_equiv(swap_hom(), apply_embedding(seq![b2], w), empty_word());
            lemma_swap_emb(b2, a2, w);
            assert(apply_hom(swap_hom(), empty_word()) =~= empty_word());
        }
        if equiv_in_presentation(fg, apply_embedding(seq![a2], w), empty_word()) {
            lemma_hom_preserves_equiv(swap_hom(), apply_embedding(seq![a2], w), empty_word());
            lemma_swap_emb(a2, b2, w);
            assert(apply_hom(swap_hom(), empty_word()) =~= empty_word());
        }
    }
}

// ═══ R2 base case — u,v with NO state letters (over {a,b}) ═══
// sub is the identity on base words {a,b}
pub proof fn lemma_sub_on_base(u: Word)
    requires word_valid(u, 2),
    ensures crate::homomorphism::apply_hom(sub_hom(), u) =~= u,
    decreases u.len()
{
    use crate::homomorphism::*;
    if u.len() > 0 {
        let s = u[0];
        let rest = u.drop_first();
        assert(symbol_valid(s, 2));
        assert(word_valid(rest, 2)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 2) by { assert(rest[i] == u[i + 1]); }
        }
        lemma_sub_on_base(rest);
        assert(apply_hom(sub_hom(), u) =~= apply_hom_symbol(sub_hom(), s) + apply_hom(sub_hom(), rest)) by { assert(u.first() == s); }
        assert(apply_hom_symbol(sub_hom(), s) =~= seq![s]) by {
            if s == Symbol::Gen(0) {
                assert(sub_hom().generator_images[0] =~= seq![Symbol::Gen(0)]);
            } else if s == Symbol::Gen(1) {
                assert(sub_hom().generator_images[1] =~= seq![Symbol::Gen(1)]);
            } else if s == Symbol::Inv(0) {
                assert(sub_hom().generator_images[0] =~= seq![Symbol::Gen(0)]);
                assert(inverse_word(seq![Symbol::Gen(0)]) =~= seq![Symbol::Inv(0)]) by (compute);
            } else {
                assert(s == Symbol::Inv(1));
                assert(sub_hom().generator_images[1] =~= seq![Symbol::Gen(1)]);
                assert(inverse_word(seq![Symbol::Gen(1)]) =~= seq![Symbol::Inv(1)]) by (compute);
            }
        }
        assert(seq![s] + rest =~= u);
    }
}

// BASE CASE: state-letter-free positive words equal in HNN ⟹ literally equal
pub proof fn lemma_m3_base(u: Word, v: Word)
    requires
        positive_word(u), positive_word(v), word_valid(u, 2), word_valid(v, 2),
        equiv_in_presentation(crate::hnn::hnn_presentation(m3_data()),
            crate::homomorphism::apply_hom(sub_hom(), u), crate::homomorphism::apply_hom(sub_hom(), v)),
    ensures u == v
{
    use crate::hnn::*;
    use crate::presentation_lemmas::*;
    use crate::presentation::{lemma_equiv_transitive, lemma_equiv_symmetric};
    let hp = hnn_presentation(m3_data());
    let fg = crate::higman_operations::free_group(2);
    lemma_m3_data_valid(); lemma_m3_iso();
    crate::britton_infra::lemma_hnn_presentation_valid(m3_data());
    crate::higman_operations::lemma_free_group_valid(2);
    lemma_sub_on_base(u); lemma_sub_on_base(v);
    // sub(u)=~=u, sub(v)=~=v ⟹ equiv(hp, u, v)
    assert(equiv_in_presentation(hp, u, v));
    // u·v⁻¹ ≡ ε in hp
    lemma_inverse_word_valid(v, 2);
    let uvi = concat(u, inverse_word(v));
    lemma_equiv_concat_left(hp, u, v, inverse_word(v));       // u·v⁻¹ ≡ v·v⁻¹
    lemma_word_inverse_right(hp, v);                          // v·v⁻¹ ≡ ε
    lemma_equiv_transitive(hp, uvi, concat(v, inverse_word(v)), empty_word());
    // word_valid(u·v⁻¹, 2)
    assert(word_valid(uvi, 2)) by {
        assert forall|i: int| 0 <= i < uvi.len() implies symbol_valid(#[trigger] uvi[i], 2) by {
            if i < u.len() { assert(uvi[i] == u[i]); } else { assert(uvi[i] == inverse_word(v)[i - u.len()]); }
        }
    }
    // Britton base embedding ⟹ equiv(free_group(2), u·v⁻¹, ε)
    crate::britton_via_tower::britton_lemma_unconditional(m3_data(), uvi);
    // (u·v⁻¹)·v ≡ ε·v = v  AND  (u·v⁻¹)·v =~= u·(v⁻¹·v) ≡ u·ε ≡ u  ⟹  u ≡ v
    lemma_equiv_concat_left(fg, uvi, empty_word(), v);        // (u·v⁻¹)·v ≡ ε·v
    assert(concat(empty_word(), v) =~= v);
    lemma_word_inverse_left(fg, v);                          // v⁻¹·v ≡ ε
    lemma_equiv_concat_right(fg, u, concat(inverse_word(v), v), empty_word());  // u·(v⁻¹·v) ≡ u·ε
    assert(concat(u, empty_word()) =~= u);
    assert(concat(uvi, v) =~= concat(u, concat(inverse_word(v), v)));            // assoc
    // chain: u ≡ u·(v⁻¹·v) = (u·v⁻¹)·v ≡ v
    lemma_equiv_symmetric(fg, concat(u, concat(inverse_word(v), v)), u);         // u ≡ u·(v⁻¹·v)
    lemma_equiv_transitive(fg, u, concat(uvi, v), v);
    // freely_equivalent ⟹ u==v (positive ⟹ reduced)
    crate::free_word_problem::lemma_free_group_equiv_freely_equivalent(2, u, v);
    crate::m1_guard::lemma_positive_reduced(u); crate::m1_guard::lemma_positive_reduced(v);
    let w = choose|w: Word| crate::reduction::reduces_to(u, w) && crate::reduction::reduces_to(v, w);
    crate::reduction::lemma_reduced_reduces_to_self(u, w);
    crate::reduction::lemma_reduced_reduces_to_self(v, w);
}

// ═══ R2 case 2 — "mixed" (one has state letters, the other doesn't) is IMPOSSIBLE ═══
// recursive symbol predicates (Lean-friendly)
pub open spec fn no_sym(w: Word, t: Symbol) -> bool
    decreases w.len()
{ w.len() == 0 || (w[0] != t && no_sym(w.drop_first(), t)) }

pub open spec fn has_gen2(w: Word) -> bool
    decreases w.len()
{ w.len() > 0 && (w[0] == Symbol::Gen(2) || has_gen2(w.drop_first())) }

pub proof fn lemma_no_sym_cons(t0: Symbol, rest: Word, t: Symbol)
    ensures no_sym(seq![t0] + rest, t) == (t0 != t && no_sym(rest, t))
{ assert((seq![t0] + rest)[0] == t0); assert((seq![t0] + rest).drop_first() =~= rest); }

pub proof fn lemma_has_gen2_cons(t0: Symbol, rest: Word)
    ensures has_gen2(seq![t0] + rest) == (t0 == Symbol::Gen(2) || has_gen2(rest))
{ assert((seq![t0] + rest)[0] == t0); assert((seq![t0] + rest).drop_first() =~= rest); }

// no_sym holds for any image of a valid generator w.r.t. Inv(2)
pub proof fn lemma_img_no_inv2(img: Word)
    requires img =~= seq![Symbol::Gen(0)] || img =~= seq![Symbol::Gen(1)] || img =~= seq![Symbol::Gen(2)]
        || img =~= seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)],
    ensures no_sym(img, Symbol::Inv(2))
{
    assert(no_sym(empty_word(), Symbol::Inv(2)));
    lemma_no_sym_cons(Symbol::Gen(0), empty_word(), Symbol::Inv(2));
    lemma_no_sym_cons(Symbol::Gen(1), empty_word(), Symbol::Inv(2));
    lemma_no_sym_cons(Symbol::Gen(2), empty_word(), Symbol::Inv(2));
    lemma_no_sym_cons(Symbol::Gen(0), empty_word(), Symbol::Inv(2));
    lemma_no_sym_cons(Symbol::Gen(2), seq![Symbol::Gen(0)], Symbol::Inv(2));
    lemma_no_sym_cons(Symbol::Inv(1), seq![Symbol::Gen(2), Symbol::Gen(0)], Symbol::Inv(2));
    assert(seq![Symbol::Gen(0)] =~= seq![Symbol::Gen(0)] + empty_word());
    assert(seq![Symbol::Gen(1)] =~= seq![Symbol::Gen(1)] + empty_word());
    assert(seq![Symbol::Gen(2)] =~= seq![Symbol::Gen(2)] + empty_word());
    assert(seq![Symbol::Gen(2), Symbol::Gen(0)] =~= seq![Symbol::Gen(2)] + seq![Symbol::Gen(0)]);
    assert(seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)] =~= seq![Symbol::Inv(1)] + seq![Symbol::Gen(2), Symbol::Gen(0)]);
}

pub proof fn lemma_no_sym_concat(a: Word, b: Word, t: Symbol)
    ensures no_sym(a + b, t) == (no_sym(a, t) && no_sym(b, t))
    decreases a.len()
{
    if a.len() == 0 { assert(a + b =~= b); }
    else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_no_sym_concat(a.drop_first(), b, t);
    }
}

pub proof fn lemma_has_gen2_concat_right(a: Word, b: Word)
    requires has_gen2(b),
    ensures has_gen2(a + b)
    decreases a.len()
{
    if a.len() == 0 { assert(a + b =~= b); }
    else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_has_gen2_concat_right(a.drop_first(), b);
    }
}

// word_valid over 2 ⟹ no Gen2 and no Inv2
pub proof fn lemma_wv2_no_stable(w: Word)
    requires word_valid(w, 2),
    ensures no_sym(w, Symbol::Gen(2)), no_sym(w, Symbol::Inv(2))
    decreases w.len()
{
    if w.len() > 0 {
        assert(symbol_valid(w[0], 2));
        assert(word_valid(w.drop_first(), 2)) by {
            assert forall|i: int| 0 <= i < w.drop_first().len() implies symbol_valid(#[trigger] w.drop_first()[i], 2) by { assert(w.drop_first()[i] == w[i + 1]); }
        }
        lemma_wv2_no_stable(w.drop_first());
    }
}

// sub of a positive valid word has no Inv2
pub proof fn lemma_sub_no_inv2(u: Word)
    requires positive_word(u), word_valid(u, 4),
    ensures no_sym(crate::homomorphism::apply_hom(sub_hom(), u), Symbol::Inv(2))
    decreases u.len()
{
    use crate::homomorphism::*;
    if u.len() > 0 {
        let s = u[0];
        let rest = u.drop_first();
        lemma_positive_gen(u, 0);
        assert(symbol_valid(s, 4));
        let j = choose|j: nat| s == Symbol::Gen(j);
        assert(positive_word(rest)); assert(word_valid(rest, 4)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 4) by { assert(rest[i] == u[i + 1]); }
        }
        lemma_sub_no_inv2(rest);
        assert(apply_hom(sub_hom(), u) =~= apply_hom_symbol(sub_hom(), s) + apply_hom(sub_hom(), rest)) by { assert(u.first() == s); }
        // apply_hom_symbol(sub, Gen(j)) = images[j], none contain Inv2  (j<4)
        assert(apply_hom_symbol(sub_hom(), s) == sub_hom().generator_images[j as int]);
        assert(sub_hom().generator_images[0] =~= seq![Symbol::Gen(0)]);
        assert(sub_hom().generator_images[1] =~= seq![Symbol::Gen(1)]);
        assert(sub_hom().generator_images[2] =~= seq![Symbol::Gen(2)]);
        assert(sub_hom().generator_images[3] =~= seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)]);
        lemma_img_no_inv2(apply_hom_symbol(sub_hom(), s));
        lemma_no_sym_concat(apply_hom_symbol(sub_hom(), s), apply_hom(sub_hom(), rest), Symbol::Inv(2));
    }
}

// sub of a word containing a state letter (Gen2/Gen3) has a Gen2
pub proof fn lemma_sub_has_gen2(u: Word)
    requires positive_word(u), word_valid(u, 4), !word_valid(u, 2),
    ensures has_gen2(crate::homomorphism::apply_hom(sub_hom(), u))
    decreases u.len()
{
    use crate::homomorphism::*;
    // u nonempty; find a state letter
    assert(u.len() > 0);
    let s = u[0];
    let rest = u.drop_first();
    lemma_positive_gen(u, 0);
    let j = choose|j: nat| s == Symbol::Gen(j);
    assert(apply_hom(sub_hom(), u) =~= apply_hom_symbol(sub_hom(), s) + apply_hom(sub_hom(), rest)) by { assert(u.first() == s); }
    if j == 2 {
        assert(apply_hom_symbol(sub_hom(), s) =~= seq![Symbol::Gen(2)]);
        assert(seq![Symbol::Gen(2)] =~= seq![Symbol::Gen(2)] + empty_word());
        lemma_has_gen2_cons(Symbol::Gen(2), empty_word());
        lemma_has_gen2_concat_right_flip(apply_hom_symbol(sub_hom(), s), apply_hom(sub_hom(), rest));
    } else if j == 3 {
        assert(apply_hom_symbol(sub_hom(), s) =~= seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)]);
        assert(seq![Symbol::Gen(2), Symbol::Gen(0)] =~= seq![Symbol::Gen(2)] + seq![Symbol::Gen(0)]);
        lemma_has_gen2_cons(Symbol::Gen(2), seq![Symbol::Gen(0)]);
        assert(seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)] =~= seq![Symbol::Inv(1)] + seq![Symbol::Gen(2), Symbol::Gen(0)]);
        lemma_has_gen2_cons(Symbol::Inv(1), seq![Symbol::Gen(2), Symbol::Gen(0)]);
        lemma_has_gen2_concat_right_flip(apply_hom_symbol(sub_hom(), s), apply_hom(sub_hom(), rest));
    } else {
        // s is a wall (Gen0/Gen1); the state letter is in rest
        assert(symbol_valid(s, 2));
        assert(positive_word(rest)); assert(word_valid(rest, 4)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 4) by { assert(rest[i] == u[i + 1]); }
        }
        assert(!word_valid(rest, 2)) by {
            assert(exists|p: int| 0 <= p < u.len() && !symbol_valid(#[trigger] u[p], 2));
            let p = choose|p: int| 0 <= p < u.len() && !symbol_valid(u[p], 2);
            assert(symbol_valid(s, 2));   // s is a wall (j != 2,3 and j < 4)
            assert(p != 0);
            assert(rest[p - 1] == u[p]);
            assert(!symbol_valid(rest[p - 1], 2));
        }
        lemma_sub_has_gen2(rest);
        lemma_has_gen2_concat_right(apply_hom_symbol(sub_hom(), s), apply_hom(sub_hom(), rest));
    }
}

// prefix version of has_gen2 (Gen2 in the LEFT part)
pub proof fn lemma_has_gen2_concat_right_flip(a: Word, b: Word)
    requires has_gen2(a),
    ensures has_gen2(a + b)
    decreases a.len()
{
    if a.len() > 0 {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        if a[0] != Symbol::Gen(2) { lemma_has_gen2_concat_right_flip(a.drop_first(), b); }
    }
}

// no Inv2 ⟹ no pinch (all stable letters are Gen2, no adjacent-opposite pair)
pub proof fn lemma_no_inv2_no_pinch(w: Word)
    requires no_sym(w, Symbol::Inv(2)),
    ensures !crate::britton_via_tower::has_pinch(m3_data(), w)
{
    use crate::britton_via_tower::*;
    lemma_no_sym_index(w, Symbol::Inv(2));
    assert forall|i: int, j: int| !has_pinch_at(m3_data(), w, i, j) by {
        if has_adjacent_opposite_at(m3_data(), w, i, j) {
            // w[i], w[j] both stable, w[i] != w[j] ; no Inv2 ⟹ both Gen2 ⟹ contradiction
            assert(is_stable(m3_data(), w[i]) && is_stable(m3_data(), w[j]));
            assert(w[i] != Symbol::Inv(2) && w[j] != Symbol::Inv(2));
        }
    }
}

// no_sym gives pointwise inequality
pub proof fn lemma_no_sym_index(w: Word, t: Symbol)
    requires no_sym(w, t),
    ensures forall|i: int| 0 <= i < w.len() ==> #[trigger] w[i] != t
    decreases w.len()
{
    if w.len() > 0 {
        lemma_no_sym_index(w.drop_first(), t);
        assert forall|i: int| 0 <= i < w.len() implies #[trigger] w[i] != t by {
            if i > 0 { assert(w[i] == w.drop_first()[i - 1]); }
        }
    }
}

pub proof fn lemma_has_gen2_stable(w: Word)
    requires has_gen2(w),
    ensures crate::britton_via_tower::has_stable_letter(m3_data(), w)
    decreases w.len()
{
    use crate::britton_via_tower::*;
    if w[0] == Symbol::Gen(2) {
        assert(is_stable(m3_data(), w[0]));
    } else {
        lemma_has_gen2_stable(w.drop_first());
        let i0 = choose|i: int| 0 <= i < w.drop_first().len() && is_stable(m3_data(), w.drop_first()[i]);
        assert(w[i0 + 1] == w.drop_first()[i0]);
    }
}

// THE MIXED CASE IS IMPOSSIBLE
pub proof fn lemma_m3_no_mixed(u: Word, v: Word)
    requires
        positive_word(u), positive_word(v), word_valid(u, 4), word_valid(v, 4),
        !word_valid(u, 2), word_valid(v, 2),
        equiv_in_presentation(crate::hnn::hnn_presentation(m3_data()),
            crate::homomorphism::apply_hom(sub_hom(), u), crate::homomorphism::apply_hom(sub_hom(), v)),
    ensures false
{
    use crate::hnn::*;
    use crate::homomorphism::*;
    use crate::presentation_lemmas::*;
    use crate::presentation::lemma_equiv_transitive;
    let hp = hnn_presentation(m3_data());
    let su = apply_hom(sub_hom(), u);
    let sv = apply_hom(sub_hom(), v);
    let w = concat(su, inverse_word(sv));
    lemma_m3_data_valid(); lemma_m3_iso();
    crate::britton_infra::lemma_hnn_presentation_valid(m3_data());
    lemma_sub_valid();
    // w ≡ ε
    lemma_apply_hom_word_valid(sub_hom(), u); lemma_apply_hom_word_valid(sub_hom(), v);
    lemma_inverse_word_valid(sv, 3);
    lemma_equiv_concat_left(hp, su, sv, inverse_word(sv));   // su·sv⁻¹ ≡ sv·sv⁻¹
    lemma_word_inverse_right(hp, sv);
    lemma_equiv_transitive(hp, w, concat(sv, inverse_word(sv)), empty_word());
    // word_valid(w, 3)
    assert(word_valid(w, 3)) by {
        assert forall|i: int| 0 <= i < w.len() implies symbol_valid(#[trigger] w[i], 3) by {
            if i < su.len() { assert(w[i] == su[i]); } else { assert(w[i] == inverse_word(sv)[i - su.len()]); }
        }
    }
    // has_stable_letter(w): su has Gen2
    lemma_sub_has_gen2(u);
    lemma_has_gen2_concat_right_flip(su, inverse_word(sv));   // has_gen2(w)
    lemma_has_gen2_stable(w);
    // no Inv2 in w: su has none, sv⁻¹ has none (sv=v base ⟹ inverse over {Inv0,Inv1})
    lemma_sub_no_inv2(u);
    lemma_sub_on_base(v);                                     // sv =~= v
    lemma_wv2_no_stable(v);
    lemma_inverse_word_valid(v, 2);
    lemma_wv2_no_stable(inverse_word(v));                    // inverse_word(v) no Inv2
    assert(inverse_word(sv) =~= inverse_word(v));
    lemma_no_sym_concat(su, inverse_word(sv), Symbol::Inv(2));   // no_sym(w, Inv2)
    lemma_no_inv2_no_pinch(w);
    // britton_full ⟹ has_pinch ⟹ contradiction
    crate::britton_via_tower::britton_lemma_full(m3_data(), w);
}

// ═══ R2 case 3 via ACT_SYLS (the shortcut) — act_syls is a group invariant ═══
// generalize lemma_derivation_preserves_syls to an arbitrary target (only the base case differs)
pub proof fn lemma_deriv_syls(data: crate::hnn::HNNData, steps: Seq<crate::presentation::DerivationStep>, w: Word, w2: Word)
    requires
        crate::hnn::hnn_data_valid(data),
        crate::hnn::hnn_associations_isomorphic(data),
        word_valid(w, crate::hnn::hnn_presentation(data).num_generators),
        derivation_produces(crate::hnn::hnn_presentation(data), steps, w) == Some(w2),
    ensures crate::machine_group::act_syls(data, w) =~= crate::machine_group::act_syls(data, w2),
    decreases steps.len()
{
    let hp = crate::hnn::hnn_presentation(data);
    if steps.len() == 0 {
        assert(derivation_produces(hp, steps, w) == Some(w));   // ⟹ w2 == w
    } else {
        let step = steps.first();
        assert(apply_step(hp, w, step).is_some());              // else produces == None ≠ Some(w2)
        let w_next = apply_step(hp, w, step).unwrap();
        assert(derivation_produces(hp, steps.drop_first(), w_next) == Some(w2));
        crate::britton_infra::lemma_step_preserves_word_valid(data, w, step);
        lemma_deriv_syls(data, steps.drop_first(), w_next, w2);
        crate::britton_via_tower::lemma_single_step_preserves_syls(data, w, step);
    }
}

// act_syls is preserved by group equivalence (the two-word Britton normal-form invariance)
pub proof fn lemma_syls_preserved(data: crate::hnn::HNNData, w1: Word, w2: Word)
    requires
        crate::hnn::hnn_data_valid(data),
        crate::hnn::hnn_associations_isomorphic(data),
        word_valid(w1, crate::hnn::hnn_presentation(data).num_generators),
        equiv_in_presentation(crate::hnn::hnn_presentation(data), w1, w2),
    ensures crate::machine_group::act_syls(data, w1) =~= crate::machine_group::act_syls(data, w2),
{
    let hp = crate::hnn::hnn_presentation(data);
    let d = choose|d: crate::presentation::Derivation| derivation_valid(hp, d, w1, w2);
    assert(derivation_produces(hp, d.steps, w1) == Some(w2));
    lemma_deriv_syls(data, d.steps, w1, w2);
}

// ═══ Readback brick 1: sub(u)·q is p-reduced ⟹ the action never COLLAPSES ═══
// (all stable letters are Gen2 ⟹ no pinch ⟹ no collapse; syllables read off cleanly)
pub proof fn lemma_sub_no_collapse(u: Word)
    requires positive_word(u), word_valid(u, 4),
    ensures crate::britton_via_tower::textbook_no_collapse(
        m3_data(),
        concat(crate::homomorphism::apply_hom(sub_hom(), u), seq![Symbol::Gen(2)]),
        empty_word(), Seq::<crate::normal_form_afp_textbook::Syllable>::empty()),
{
    use crate::homomorphism::*;
    let su = apply_hom(sub_hom(), u);
    let w = concat(su, seq![Symbol::Gen(2)]);
    lemma_m3_data_valid();
    lemma_sub_valid();
    // no Inv2 in w ⟹ no pinch
    lemma_sub_no_inv2(u);
    assert(no_sym(seq![Symbol::Gen(2)], Symbol::Inv(2))) by {
        assert(seq![Symbol::Gen(2)] =~= seq![Symbol::Gen(2)] + empty_word());
        lemma_no_sym_cons(Symbol::Gen(2), empty_word(), Symbol::Inv(2));
    }
    lemma_no_sym_concat(su, seq![Symbol::Gen(2)], Symbol::Inv(2));
    lemma_no_inv2_no_pinch(w);
    // word_valid(w, 3)
    lemma_apply_hom_word_valid(sub_hom(), u);
    assert(word_valid(w, 3)) by {
        assert forall|i: int| 0 <= i < w.len() implies symbol_valid(#[trigger] w[i], 3) by {
            if i < su.len() { assert(w[i] == su[i]); } else { assert(w[i] == Symbol::Gen(2)); }
        }
    }
    crate::britton_via_tower::lemma_p_reduced_initial_no_collapse(m3_data(), w);
}

// ═══ Readback brick 2: syllable count = stable_count (no collapse) ═══
pub proof fn lemma_sub_syls_count(u: Word)
    requires positive_word(u), word_valid(u, 4),
    ensures crate::machine_group::act_syls(m3_data(),
        concat(crate::homomorphism::apply_hom(sub_hom(), u), seq![Symbol::Gen(2)])).len()
        == crate::britton_via_tower::stable_count(m3_data(),
            concat(crate::homomorphism::apply_hom(sub_hom(), u), seq![Symbol::Gen(2)])),
{
    let w = concat(crate::homomorphism::apply_hom(sub_hom(), u), seq![Symbol::Gen(2)]);
    lemma_m3_data_valid();
    lemma_sub_no_collapse(u);
    crate::britton_via_tower::lemma_no_collapse_gives_m(m3_data(), w, empty_word(),
        Seq::<crate::normal_form_afp_textbook::Syllable>::empty());
}

// ═══ Readback brick B4: the PARITY head-cap (pure free-group) ═══
// reduced-form uniqueness: equiv in free group + both reduced ⟹ literally equal
pub proof fn lemma_reduced_unique(g1: Word, g2: Word)
    requires
        word_valid(g1, 2), word_valid(g2, 2),
        crate::reduction::is_reduced(g1), crate::reduction::is_reduced(g2),
        equiv_in_presentation(crate::higman_operations::free_group(2), g1, g2),
    ensures g1 =~= g2
{
    use crate::reduction::*;
    crate::higman_operations::lemma_free_group_valid(2);
    crate::free_word_problem::lemma_free_group_equiv_freely_equivalent(2, g1, g2);
    let w = choose|w: Word| reduces_to(g1, w) && reduces_to(g2, w);
    lemma_reduced_reduces_to_self(g1, w);
    lemma_reduced_reduces_to_self(g2, w);
}

// word_valid of a Gen(0) power
pub proof fn lemma_gen0_pow_valid(n: nat)
    ensures word_valid(crate::machine_group::symbol_power(Symbol::Gen(0), n), 2)
{
    let ap = crate::machine_group::symbol_power(Symbol::Gen(0), n);
    assert forall|i: int| 0 <= i < ap.len() implies symbol_valid(#[trigger] ap[i], 2) by { assert(ap[i] == Symbol::Gen(0)); }
}

// prepending a^n (n≥2) to a reduced word (whose head ≠ a⁻¹) stays reduced with a-head ≥ 2
pub proof fn lemma_prepend_gen0(g: Word, n: nat)
    requires n >= 2, crate::reduction::is_reduced(g), (g.len() > 0 ==> g[0] != Symbol::Inv(0)),
    ensures
        crate::reduction::is_reduced(concat(crate::machine_group::symbol_power(Symbol::Gen(0), n), g)),
        crate::m1_guard::lead(concat(crate::machine_group::symbol_power(Symbol::Gen(0), n), g), 0) >= 2,
{
    use crate::reduction::*;
    let ap = crate::machine_group::symbol_power(Symbol::Gen(0), n);
    let w = concat(ap, g);
    assert(forall|i: int| 0 <= i < ap.len() ==> ap[i] == Symbol::Gen(0));
    // ap reduced (all Gen0, no inverse pair)
    assert(is_reduced(ap)) by {
        assert forall|i: int| !has_cancellation_at(ap, i) by {
            if 0 <= i < ap.len() - 1 { assert(ap[i] == Symbol::Gen(0) && ap[i + 1] == Symbol::Gen(0)); }
        }
    }
    // junction ok: ap.last() = Gen0, g[0] != Inv0
    assert((ap.len() > 0 && g.len() > 0) ==> !is_inverse_pair(ap[ap.len() - 1], g[0])) by {
        if ap.len() > 0 && g.len() > 0 { assert(ap[ap.len() - 1] == Symbol::Gen(0)); }
    }
    crate::machine_group::lemma_concat_reduced(ap, g);
    // lead ≥ 2:  w[0]=w[1]=Gen0
    assert(w[0] == Symbol::Gen(0)) by { assert(w[0] == ap[0]); }
    assert(w.drop_first()[0] == Symbol::Gen(0)) by { assert(w.drop_first()[0] == w[1]); assert(w[1] == ap[1]); }
    assert(crate::m1_guard::lead(w.drop_first(), 0) >= 1);
    assert(crate::m1_guard::lead(w, 0) == 1 + crate::m1_guard::lead(w.drop_first(), 0));
}

// THE PARITY HEAD-CAP: two nf gaps in the same ⟨a²⟩-coset (g1 ≡ a^{2k}·g2), both a-head ≤ 1
// and no a⁻¹, are EQUAL.  (k≠0 blows the a-head past 1 on one side.)
pub proof fn lemma_parity_head_cap(g1: Word, g2: Word, k: int)
    requires
        word_valid(g1, 2), word_valid(g2, 2),
        crate::reduction::is_reduced(g1), crate::reduction::is_reduced(g2),
        no_sym(g1, Symbol::Inv(0)), no_sym(g2, Symbol::Inv(0)),
        crate::m1_guard::lead(g1, 0) <= 1, crate::m1_guard::lead(g2, 0) <= 1,
        equiv_in_presentation(crate::higman_operations::free_group(2), g1,
            concat(crate::machine_group::signed_power(0, 2 * k), g2)),
    ensures g1 =~= g2
{
    use crate::machine_group::*;
    use crate::presentation_lemmas::*;
    use crate::presentation::{lemma_equiv_transitive, lemma_equiv_symmetric};
    let fg = crate::higman_operations::free_group(2);
    crate::higman_operations::lemma_free_group_valid(2);
    let sp = signed_power(0, 2 * k);
    let w = concat(sp, g2);
    if k == 0 {
        assert(sp =~= empty_word());
        assert(w =~= g2);
        lemma_reduced_unique(g1, g2);
    } else if k > 0 {
        let n: nat = (2 * k) as nat;
        assert(sp =~= symbol_power(Symbol::Gen(0), n));
        lemma_no_sym_index(g2, Symbol::Inv(0));
        lemma_prepend_gen0(g2, n);
        lemma_gen0_pow_valid(n);
        assert(word_valid(w, 2)) by {
            assert forall|i: int| 0 <= i < w.len() implies symbol_valid(#[trigger] w[i], 2) by {
                if i < sp.len() { assert(w[i] == sp[i]); } else { assert(w[i] == g2[i - sp.len()]); }
            }
        }
        lemma_reduced_unique(g1, w);   // g1 =~= w ⟹ lead(g1,0)=lead(w,0) ≥ 2, contra ≤ 1
        assert(false);
    } else {
        // k < 0: rearrange equiv(g1, a^{2k}·g2) → equiv(g2, a^{-2k}·g1), then symmetric to k>0
        let neg: int = -2 * k;   // ≥ 2
        let spn = signed_power(0, neg);
        lemma_no_sym_index(g1, Symbol::Inv(0));
        // left-multiply by spn:  equiv(spn·g1, spn·(sp·g2))
        lemma_equiv_concat_right(fg, spn, g1, w);
        assert(concat(spn, w) =~= concat(concat(spn, sp), g2));
        // spn·sp ≡ a^{neg+2k}=a^0=ε
        lemma_signed_power_add(fg, 0, neg, 2 * k);
        assert(signed_power(0, neg + 2 * k) =~= empty_word());
        lemma_equiv_concat_left(fg, concat(spn, sp), empty_word(), g2);   // (spn·sp)·g2 ≡ ε·g2
        assert(concat(empty_word(), g2) =~= g2);
        lemma_equiv_transitive(fg, concat(spn, g1), concat(concat(spn, sp), g2), g2);
        lemma_equiv_symmetric(fg, concat(spn, g1), g2);   // equiv(g2, spn·g1)
        // spn = a^{neg}, neg ≥ 2
        assert(spn =~= symbol_power(Symbol::Gen(0), neg as nat));
        lemma_prepend_gen0(g1, neg as nat);
        lemma_gen0_pow_valid(neg as nat);
        assert(word_valid(concat(spn, g1), 2)) by {
            assert forall|i: int| 0 <= i < concat(spn, g1).len() implies symbol_valid(#[trigger] concat(spn, g1)[i], 2) by {
                if i < spn.len() { assert(concat(spn, g1)[i] == spn[i]); } else { assert(concat(spn, g1)[i] == g1[i - spn.len()]); }
            }
        }
        lemma_reduced_unique(g2, concat(spn, g1));   // g2 =~= a^{neg}·g1 ⟹ lead(g2,0) ≥ 2, contra
        assert(false);
    }
}

// ═══ B3 foundation: b_rcoset_rep(nf gap) = gap — Stage A (coset/reduction helpers) ═══
pub open spec fn m3_afp() -> crate::amalgamated_free_product::AmalgamatedData {
    crate::tower::tower_afp_data(m3_data(), 0)
}
pub open spec fn abs_int(m: int) -> int { if m >= 0 { m } else { -m } }
pub open spec fn head_decomp_ok(w: Word, m: int, s: Word) -> bool {
    &&& w == crate::machine_group::signed_power(0, m) + s
    &&& word_valid(s, 2)
    &&& crate::reduction::is_reduced(s)
    &&& (s.len() > 0 ==> s[0] != Symbol::Gen(0) && s[0] != Symbol::Inv(0))
    &&& w.len() == abs_int(m) + s.len()
}

proof fn lemma_m3_afp_valid()
    ensures
        crate::amalgamated_free_product::amalgamated_data_valid(m3_afp()),
        crate::presentation::presentation_valid(m3_afp().p2),
        m3_afp().p2 == crate::higman_operations::free_group(2),
        m3_afp().p2.num_generators == 2,
        crate::normal_form_afp_textbook::b_words(m3_afp()) =~= seq![seq![Symbol::Gen(0), Symbol::Gen(0)]],
{
    reveal(crate::presentation::presentation_valid);
    lemma_m3_data_valid();
    crate::tower::lemma_tower_afp_data_valid(m3_data(), 0);
    crate::higman_operations::lemma_free_group_valid(2);
    assert(m3_afp().p2 == m3_data().base);
    assert(m3_afp().identifications[0].1 =~= seq![Symbol::Gen(0), Symbol::Gen(0)]);
}

// H1: monotone extraction from no_shorter
proof fn lemma_no_shorter_below(data: crate::amalgamated_free_product::AmalgamatedData, g: Word, l: nat, l2: nat)
    requires
        crate::normal_form_afp_textbook::no_shorter_b_rcoset_word(data, g, l),
        l2 < l,
    ensures !crate::normal_form_afp_textbook::has_b_rcoset_word_of_len(data, g, l2),
    decreases l,
{
    if l2 < (l - 1) as nat { lemma_no_shorter_below(data, g, (l - 1) as nat, l2); }
}

// suffix of reduced is reduced
proof fn lemma_suffix_reduced(w: Word)
    requires crate::reduction::is_reduced(w), w.len() > 0,
    ensures crate::reduction::is_reduced(w.drop_first()),
{
    use crate::reduction::*;
    let d = w.drop_first();
    assert(d.len() == w.len() - 1);
    assert(!has_cancellation(d)) by {
        assert forall|i: int| !has_cancellation_at(d, i) by {
            if 0 <= i < d.len() - 1 {
                assert(d[i] == w[i + 1]);
                assert(d[i + 1] == w[i + 2]);
                assert(!has_cancellation_at(w, i + 1));
            }
        }
    }
}

// H12: one-step lex-rank unfold for a headed word
proof fn lemma_rank_head(w: Word, s: Word, sym: Symbol)
    requires w =~= seq![sym] + s,
    ensures crate::normal_form_afp_textbook::word_lex_rank_base(w, 5)
        == crate::todd_coxeter::symbol_to_column(sym)
         + 5 * crate::normal_form_afp_textbook::word_lex_rank_base(s, 5),
{
    assert(w.len() == 1 + s.len());
    assert(w.first() == sym);
    assert(w.drop_first() =~= s);
}

// H11: a^j · s reduced when s reduced and doesn't start with a±
proof fn lemma_signed_power_concat_reduced(j: int, s: Word)
    requires
        crate::reduction::is_reduced(s),
        s.len() > 0 ==> s[0] != Symbol::Gen(0) && s[0] != Symbol::Inv(0),
    ensures crate::reduction::is_reduced(crate::machine_group::signed_power(0, j) + s),
{
    use crate::reduction::*;
    let sp = crate::machine_group::signed_power(0, j);
    assert(forall|i: int| 0 <= i < sp.len() ==> (sp[i] == Symbol::Gen(0) || sp[i] == Symbol::Inv(0)));
    assert(is_reduced(sp)) by {
        assert forall|i: int| !has_cancellation_at(sp, i) by {
            if 0 <= i < sp.len() - 1 { assert(sp[i] == sp[i + 1]); }
        }
    }
    if sp.len() > 0 && s.len() > 0 {
        assert(sp[sp.len() - 1] == Symbol::Gen(0) || sp[sp.len() - 1] == Symbol::Inv(0));
        assert(!is_inverse_pair(sp[sp.len() - 1], s[0]));
    }
    crate::machine_group::lemma_concat_reduced(sp, s);
}

// H5: same_b_rcoset reflexive
proof fn lemma_same_b_rcoset_refl(data: crate::amalgamated_free_product::AmalgamatedData, g: Word)
    requires
        crate::amalgamated_free_product::amalgamated_data_valid(data),
        crate::presentation::presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
    ensures crate::normal_form_afp_textbook::same_b_rcoset(data, g, g),
{
    crate::word::lemma_inverse_word_valid(g, data.p2.num_generators);
    crate::presentation_lemmas::lemma_word_inverse_right(data.p2, g);
    crate::benign::lemma_identity_in_generated_subgroup(data.p2, crate::normal_form_afp_textbook::b_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p2, concat(g, inverse_word(g)), empty_word());
    crate::normal_form_afp_textbook::lemma_in_subgroup_equiv(data.p2,
        crate::normal_form_afp_textbook::b_words(data), empty_word(), concat(g, inverse_word(g)));
}

// H6: same_b_rcoset respects equiv on the 2nd arg
proof fn lemma_same_b_rcoset_respects_equiv(data: crate::amalgamated_free_product::AmalgamatedData, g: Word, w1: Word, w2: Word)
    requires
        crate::amalgamated_free_product::amalgamated_data_valid(data),
        crate::presentation::presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(w1, data.p2.num_generators),
        word_valid(w2, data.p2.num_generators),
        crate::normal_form_afp_textbook::same_b_rcoset(data, g, w1),
        equiv_in_presentation(data.p2, w1, w2),
    ensures crate::normal_form_afp_textbook::same_b_rcoset(data, g, w2),
{
    crate::normal_form_afp_textbook::lemma_equiv_inverse(data.p2, w1, w2);
    crate::word::lemma_inverse_word_valid(w1, data.p2.num_generators);
    crate::word::lemma_inverse_word_valid(w2, data.p2.num_generators);
    crate::presentation_lemmas::lemma_equiv_concat_right(data.p2, g, inverse_word(w1), inverse_word(w2));
    crate::normal_form_afp_textbook::lemma_in_subgroup_equiv(data.p2,
        crate::normal_form_afp_textbook::b_words(data),
        concat(g, inverse_word(w1)), concat(g, inverse_word(w2)));
}

// H7: a min-length coset word is freely reduced
proof fn lemma_min_coset_word_reduced(data: crate::amalgamated_free_product::AmalgamatedData, g: Word, rep: Word)
    requires
        crate::amalgamated_free_product::amalgamated_data_valid(data),
        crate::presentation::presentation_valid(data.p2),
        data.p2.num_generators == 2,
        word_valid(g, 2), word_valid(rep, 2),
        crate::normal_form_afp_textbook::same_b_rcoset(data, g, rep),
        rep.len() == crate::normal_form_afp_textbook::b_rcoset_min_len(data, g),
        crate::normal_form_afp_textbook::is_min_b_rcoset_len(data, g,
            crate::normal_form_afp_textbook::b_rcoset_min_len(data, g)),
    ensures crate::reduction::is_reduced(rep),
{
    use crate::reduction::*;
    if !is_reduced(rep) {
        assert(has_cancellation(rep));
        let i = choose|i: int| has_cancellation_at(rep, i);
        let rep2 = reduce_at(rep, i);
        lemma_reduce_at_len(rep, i);
        lemma_reduce_at_elements(rep, i);
        assert(reduces_one_step(rep, rep2));
        assert(reduces_in_steps(rep2, rep2, 0));
        assert(reduces_in_steps(rep, rep2, 1));
        assert(reduces_to(rep, rep2));
        assert(word_valid(rep2, 2)) by {
            assert forall|k: int| 0 <= k < rep2.len() implies symbol_valid(#[trigger] rep2[k], 2) by {
                if k < i { assert(rep2[k] == rep[k]); } else { assert(rep2[k] == rep[k + 2]); }
            }
        }
        crate::presentation_lemmas::lemma_reduces_to_equiv(data.p2, rep, rep2);
        lemma_same_b_rcoset_respects_equiv(data, g, rep, rep2);
        assert(crate::normal_form_afp_textbook::has_b_rcoset_word_of_len(data, g, rep2.len()));
        lemma_no_shorter_below(data, g, crate::normal_form_afp_textbook::b_rcoset_min_len(data, g), rep2.len());
        assert(false);
    }
}

// ═══ B3 foundation — Stage B (head decomposition, factor powers, carrier shift, MAIN) ═══
proof fn lemma_symbol_power_cons(x: Symbol, n: nat)
    ensures crate::machine_group::symbol_power(x, (n + 1) as nat)
        =~= seq![x] + crate::machine_group::symbol_power(x, n),
{
    let a = crate::machine_group::symbol_power(x, (n + 1) as nat);
    let b = seq![x] + crate::machine_group::symbol_power(x, n);
    assert(a.len() == b.len());
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        assert(a[i] == x);
        if i >= 1 { assert(b[i] == crate::machine_group::symbol_power(x, n)[i - 1]); }
    }
}

// H8: signed head decomposition of a reduced word
proof fn lemma_signed_head_decompose(w: Word)
    requires word_valid(w, 2), crate::reduction::is_reduced(w),
    ensures exists|m: int, s: Word| head_decomp_ok(w, m, s),
    decreases w.len(),
{
    use crate::machine_group::*;
    if w.len() == 0 {
        assert(signed_power(0, 0) =~= empty_word());
        assert(w =~= signed_power(0, 0) + empty_word());
        assert(head_decomp_ok(w, 0, empty_word()));
    } else if w[0] == Symbol::Gen(0) || w[0] == Symbol::Inv(0) {
        let rest = w.drop_first();
        lemma_suffix_reduced(w);
        assert(word_valid(rest, 2)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 2) by { assert(rest[i] == w[i + 1]); }
        }
        lemma_signed_head_decompose(rest);
        let (m1, s1) = choose|m1: int, s1: Word| head_decomp_ok(rest, m1, s1);
        assert(rest == signed_power(0, m1) + s1);
        if w[0] == Symbol::Gen(0) {
            if m1 < 0 {
                assert(signed_power(0, m1) == symbol_power(Symbol::Inv(0), (-m1) as nat));
                assert(signed_power(0, m1)[0] == Symbol::Inv(0));
                assert(rest[0] == Symbol::Inv(0));
                assert(w[1] == Symbol::Inv(0));
                assert(crate::reduction::has_cancellation_at(w, 0));
                assert(false);
            }
            lemma_symbol_power_cons(Symbol::Gen(0), m1 as nat);
            assert(signed_power(0, m1 + 1) =~= seq![Symbol::Gen(0)] + signed_power(0, m1));
            assert(w =~= seq![Symbol::Gen(0)] + rest);
            assert(w =~= signed_power(0, m1 + 1) + s1);
            assert(head_decomp_ok(w, m1 + 1, s1));
        } else {
            if m1 > 0 {
                assert(signed_power(0, m1) == symbol_power(Symbol::Gen(0), m1 as nat));
                assert(signed_power(0, m1)[0] == Symbol::Gen(0));
                assert(rest[0] == Symbol::Gen(0));
                assert(w[1] == Symbol::Gen(0));
                assert(crate::reduction::has_cancellation_at(w, 0));
                assert(false);
            }
            lemma_symbol_power_cons(Symbol::Inv(0), (-m1) as nat);
            assert(signed_power(0, m1 - 1) =~= seq![Symbol::Inv(0)] + signed_power(0, m1));
            assert(w =~= seq![Symbol::Inv(0)] + rest);
            assert(w =~= signed_power(0, m1 - 1) + s1);
            assert(head_decomp_ok(w, m1 - 1, s1));
        }
    } else {
        assert(signed_power(0, 0) =~= empty_word());
        assert(w =~= signed_power(0, 0) + w);
        assert(head_decomp_ok(w, 0, w));
    }
}

// H9: a product of a²/a⁻² factors ≡ a^{2k}
proof fn lemma_a2_factors_signed_power(factors: Seq<Word>)
    requires crate::benign::factors_from_generators(seq![seq![Symbol::Gen(0), Symbol::Gen(0)]], factors),
    ensures
        word_valid(crate::benign::concat_all(factors), 2),
        exists|k: int| equiv_in_presentation(crate::higman_operations::free_group(2),
            crate::benign::concat_all(factors), #[trigger] crate::machine_group::signed_power(0, 2 * k)),
    decreases factors.len(),
{
    use crate::machine_group::*;
    use crate::benign::*;
    let fg = crate::higman_operations::free_group(2);
    crate::higman_operations::lemma_free_group_valid(2);
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
        assert(word_valid(concat_all(factors), 2));
        assert(signed_power(0, 2 * 0int) =~= empty_word());
        crate::presentation::lemma_equiv_refl(fg, empty_word());
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(seq![seq![Symbol::Gen(0), Symbol::Gen(0)]], rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies is_generator_or_inverse(seq![seq![Symbol::Gen(0), Symbol::Gen(0)]], #[trigger] rest[j]) by { assert(rest[j] == factors[j + 1]); }
        }
        lemma_a2_factors_signed_power(rest);
        let k1 = choose|k1: int| equiv_in_presentation(fg, concat_all(rest), #[trigger] signed_power(0, 2 * k1));
        assert(is_generator_or_inverse(seq![seq![Symbol::Gen(0), Symbol::Gen(0)]], factors[0]));
        assert(concat_all(factors) == concat(factors.first(), concat_all(rest)));
        assert(factors.first() == factors[0]);
        // factors[0] is a² or a⁻²
        assert(inverse_word(seq![Symbol::Gen(0), Symbol::Gen(0)]) =~= seq![Symbol::Inv(0), Symbol::Inv(0)]) by (compute);
        let ex: int = if factors[0] == seq![Symbol::Gen(0), Symbol::Gen(0)] { 2 } else { -2 };
        assert(factors[0] =~= signed_power(0, ex));
        assert(word_valid(factors[0], 2));
        assert(word_valid(concat_all(factors), 2)) by {
            assert forall|i: int| 0 <= i < concat_all(factors).len() implies symbol_valid(#[trigger] concat_all(factors)[i], 2) by {
                if i < factors[0].len() { assert(concat_all(factors)[i] == factors[0][i]); }
                else { assert(concat_all(factors)[i] == concat_all(rest)[i - factors[0].len()]); }
            }
        }
        // congruence + signed_power_add:  a^ex · a^{2k1} ≡ a^{ex+2k1}
        crate::presentation_lemmas::lemma_equiv_concat_right(fg, factors[0], concat_all(rest), signed_power(0, 2 * k1));
        lemma_signed_power_add(fg, 0, ex, 2 * k1);
        assert(concat(factors[0], signed_power(0, 2 * k1)) =~= signed_power(0, ex) + signed_power(0, 2 * k1));
        crate::presentation::lemma_equiv_transitive(fg, concat_all(factors),
            concat(factors[0], signed_power(0, 2 * k1)), signed_power(0, ex + 2 * k1));
        assert(ex + 2 * k1 == 2 * (if factors[0] == seq![Symbol::Gen(0), Symbol::Gen(0)] { 1 + k1 } else { -1 + k1 }));
    }
}

// H10: a^{2k} ≡ g·rep⁻¹  ⟹  g ≡ a^{2k}·rep
proof fn lemma_shift_carrier(g: Word, rep: Word, k: int)
    requires
        word_valid(g, 2), word_valid(rep, 2),
        equiv_in_presentation(crate::higman_operations::free_group(2),
            crate::machine_group::signed_power(0, 2 * k), concat(g, inverse_word(rep))),
    ensures equiv_in_presentation(crate::higman_operations::free_group(2),
        g, concat(crate::machine_group::signed_power(0, 2 * k), rep)),
{
    use crate::machine_group::*;
    use crate::presentation::*;
    use crate::presentation_lemmas::*;
    let fg = crate::higman_operations::free_group(2);
    crate::higman_operations::lemma_free_group_valid(2);
    crate::word::lemma_inverse_word_valid(rep, 2);
    let sp = signed_power(0, 2 * k);
    // a^{2k}·rep ≡ (g·rep⁻¹)·rep
    lemma_equiv_concat_left(fg, sp, concat(g, inverse_word(rep)), rep);
    // rep⁻¹·rep ≡ ε ⟹ g·(rep⁻¹·rep) ≡ g·ε
    lemma_word_inverse_left(fg, rep);
    lemma_equiv_concat_right(fg, g, concat(inverse_word(rep), rep), empty_word());
    assert(concat(concat(g, inverse_word(rep)), rep) =~= concat(g, concat(inverse_word(rep), rep)));
    assert(concat(g, empty_word()) =~= g);
    // g ≡ g·(rep⁻¹rep)
    lemma_equiv_symmetric(fg, concat(g, concat(inverse_word(rep), rep)), concat(g, empty_word()));
    // (g·rep⁻¹)·rep ≡ a^{2k}·rep
    lemma_equiv_symmetric(fg, concat(sp, rep), concat(concat(g, inverse_word(rep)), rep));
    // g ≡ g·(rep⁻¹rep) = (g·rep⁻¹)·rep ≡ a^{2k}·rep
    lemma_equiv_transitive(fg, g, concat(g, concat(inverse_word(rep), rep)), concat(sp, rep));
}

// ═══════════════════ THE LEMMA ═══════════════════
pub proof fn lemma_b_rcoset_rep_eq_gap(g: Word)
    requires
        word_valid(g, 2),
        crate::reduction::is_reduced(g),
        no_sym(g, Symbol::Inv(0)),
        crate::m1_guard::lead(g, 0) <= 1,
    ensures crate::normal_form_afp_textbook::b_rcoset_rep(m3_afp(), g) =~= g,
{
    use crate::machine_group::*;
    use crate::normal_form_afp_textbook::*;
    let fg = crate::higman_operations::free_group(2);
    lemma_m3_afp_valid();
    let data = m3_afp();
    // rep + min facts
    let rep = b_rcoset_rep(data, g);
    lemma_b_rcoset_rep_props(data, g);
    lemma_b_rcoset_rep_satisfiable(data, g);
    let ml = b_rcoset_min_len(data, g);
    lemma_same_b_rcoset_refl(data, g);
    // ml ≤ |g|
    if g.len() < ml {
        lemma_no_shorter_below(data, g, ml, g.len());
        assert(has_b_rcoset_word_of_len(data, g, g.len()));
        assert(false);
    }
    // rep reduced, decompose rep = a^m·s
    lemma_min_coset_word_reduced(data, g, rep);
    lemma_signed_head_decompose(rep);
    let (m, s) = choose|m: int, s: Word| head_decomp_ok(rep, m, s);
    // extract k with g ≡ a^{2k}·rep
    assert(same_b_rcoset(data, g, rep));
    crate::word::lemma_inverse_word_valid(rep, 2);
    assert(crate::normal_form_amalgamated::in_right_subgroup(data, concat(g, inverse_word(rep))));
    let factors = choose|f: Seq<Word>|
        crate::benign::factors_from_generators(b_words(data), f)
        && equiv_in_presentation(data.p2, crate::benign::concat_all(f), concat(g, inverse_word(rep)));
    assert(b_words(data) =~= seq![seq![Symbol::Gen(0), Symbol::Gen(0)]]);
    lemma_a2_factors_signed_power(factors);
    let k = choose|k: int| equiv_in_presentation(fg, crate::benign::concat_all(factors), #[trigger] signed_power(0, 2 * k));
    // a^{2k} ≡ concat_all(factors) ≡ g·rep⁻¹
    crate::presentation::lemma_equiv_symmetric(fg, crate::benign::concat_all(factors), signed_power(0, 2 * k));
    crate::presentation::lemma_equiv_transitive(fg, signed_power(0, 2 * k), crate::benign::concat_all(factors), concat(g, inverse_word(rep)));
    lemma_shift_carrier(g, rep, k);   // g ≡ a^{2k}·rep
    // g ≡ a^{2k}·(a^m·s) = a^{2k+m}·s
    let j = 2 * k + m;
    assert(concat(signed_power(0, 2 * k), rep) =~= concat(signed_power(0, 2 * k), signed_power(0, m)) + s);
    lemma_signed_power_add(fg, 0, 2 * k, m);
    crate::presentation_lemmas::lemma_equiv_concat_left(fg, concat(signed_power(0, 2 * k), signed_power(0, m)), signed_power(0, j), s);
    assert(concat(signed_power(0, j), s) == signed_power(0, j) + s);
    crate::presentation::lemma_equiv_transitive(fg, g, concat(signed_power(0, 2 * k), rep), signed_power(0, j) + s);
    // g == a^j·s literally
    lemma_signed_power_concat_reduced(j, s);
    lemma_reduced_unique(g, signed_power(0, j) + s);
    assert(g =~= signed_power(0, j) + s);
    assert(g.len() == abs_int(j) + s.len());
    // 0 ≤ j ≤ 1
    if j < 0 {
        assert(signed_power(0, j) == symbol_power(Symbol::Inv(0), (-j) as nat));
        assert(g[0] == Symbol::Inv(0));
        lemma_no_sym_index(g, Symbol::Inv(0));
        assert(false);
    }
    if j >= 2 {
        assert(s.len() > 0 ==> s[0] != Symbol::Inv(0));
        lemma_prepend_gen0(s, j as nat);
        assert(signed_power(0, j) =~= symbol_power(Symbol::Gen(0), j as nat));
        assert(crate::m1_guard::lead(g, 0) >= 2);
        assert(false);
    }
    // |m| ≤ j   (rep len = |m|+|s| = ml ≤ |g| = j+|s|)
    assert(abs_int(m) <= j);
    // kill m == -1 via min-lex
    if m == -1 {
        assert(j == 1);
        assert(g.len() == ml);
        let rr = word_lex_rank_base(rep, 5);
        let rg = word_lex_rank_base(g, 5);
        assert(has_b_rcoset_word_of_len_rank(data, g, ml, rr));
        assert(is_min_b_rcoset_lex(data, g, ml, b_rcoset_min_lex(data, g)));
        assert(rr == b_rcoset_min_lex(data, g));
        assert(signed_power(0, 1) =~= seq![Symbol::Gen(0)]);
        assert(signed_power(0, -1) =~= seq![Symbol::Inv(0)]);
        assert(g =~= seq![Symbol::Gen(0)] + s);
        assert(rep =~= seq![Symbol::Inv(0)] + s);
        lemma_rank_head(g, s, Symbol::Gen(0));
        lemma_rank_head(rep, s, Symbol::Inv(0));
        assert(crate::todd_coxeter::symbol_to_column(Symbol::Gen(0)) == 0);
        assert(crate::todd_coxeter::symbol_to_column(Symbol::Inv(0)) == 1);
        assert(rg < rr);
        assert(has_b_rcoset_word_of_len_rank(data, g, ml, rg));
        lemma_no_smaller_lex_below(data, g, ml, b_rcoset_min_lex(data, g), rg);
        assert(false);
    }
    // parity: j - m = 2k even, m ∈ {0,1}, j ∈ {0,1}  ⟹  m == j  ⟹  rep = a^m·s = a^j·s = g
    assert(m == j);
    assert(rep =~= g);
}

// H4-mirror for lex (the one min-existence helper the main lemma still needs)
proof fn lemma_no_smaller_lex_below(data: crate::amalgamated_free_product::AmalgamatedData, g: Word, l: nat, r: nat, r2: nat)
    requires
        crate::normal_form_afp_textbook::no_smaller_b_rcoset_lex(data, g, l, r),
        r2 < r,
    ensures !crate::normal_form_afp_textbook::has_b_rcoset_word_of_len_rank(data, g, l, r2),
    decreases r,
{
    if r2 < (r - 1) as nat { lemma_no_smaller_lex_below(data, g, l, (r - 1) as nat, r2); }
}

// ═══ B3 step: processing one q on a nf-gap accumulator prepends {false,gap}, carry vanishes ═══
pub proof fn lemma_psi_p_nf_gap(h: Word, syls: Seq<crate::normal_form_afp_textbook::Syllable>)
    requires
        word_valid(h, 2),
        crate::reduction::is_reduced(h),
        no_sym(h, Symbol::Inv(0)),
        crate::m1_guard::lead(h, 0) <= 1,
        syls.len() == 0 || !syls.first().is_left,
    ensures
        crate::britton_via_tower::textbook_psi_p(m3_data(), h, syls)
            == (empty_word(),
                Seq::new(1, |_i: int| crate::normal_form_afp_textbook::Syllable { is_left: false, rep: h }) + syls),
{
    use crate::normal_form_afp_textbook::*;
    let afp = crate::tower::tower_afp_data(m3_data(), 0);
    lemma_m3_afp_valid();
    assert(afp == m3_afp());
    lemma_b_rcoset_rep_eq_gap(h);                        // b_rcoset_rep(afp, h) =~= h
    let rep = b_rcoset_rep(afp, h);
    assert(rep == h);
    lemma_b_rcoset_h_eps_when_rep_eq(afp, h);            // b_rcoset_h(afp, h) =~= ε
    let h_id = b_rcoset_h(afp, h);
    assert(h_id == empty_word());
    let phi_inv_h = crate::benign::apply_embedding(a_words(afp), h_id);
    assert(phi_inv_h =~= empty_word());
    // no collapse: either rep=h≠ε, or h=ε and !syls.first().is_left
    assert(!(rep =~= empty_word() && syls.len() > 0 && syls.first().is_left));
    // PREPEND branch
    assert(Seq::new(1, |_i: int| Syllable { is_left: false, rep: rep })
        =~= Seq::new(1, |_i: int| Syllable { is_left: false, rep: h }));
}

// ═══ B3 crux: act_syls(gap_word(gs)) = gap_syls(gs) for nf gaps ═══
pub open spec fn nf_gap(g: Word) -> bool {
    word_valid(g, 2) && crate::reduction::is_reduced(g)
        && no_sym(g, Symbol::Inv(0)) && crate::m1_guard::lead(g, 0) <= 1
}
pub open spec fn gap_word(gs: Seq<Word>) -> Word
    decreases gs.len()
{
    if gs.len() == 0 { empty_word() }
    else { concat(seq![Symbol::Gen(2)], concat(gs.first(), gap_word(gs.drop_first()))) }
}
pub open spec fn gap_syls(gs: Seq<Word>) -> Seq<crate::normal_form_afp_textbook::Syllable> {
    Seq::new(gs.len(), |i: int| crate::normal_form_afp_textbook::Syllable { is_left: false, rep: gs[i] })
}

pub proof fn lemma_act_gap_word(gs: Seq<Word>)
    requires forall|i: int| 0 <= i < gs.len() ==> nf_gap(#[trigger] gs[i]),
    ensures crate::britton_via_tower::textbook_act_hnn(m3_data(), gap_word(gs), empty_word(),
        Seq::<crate::normal_form_afp_textbook::Syllable>::empty()) == (empty_word(), gap_syls(gs)),
    decreases gs.len(),
{
    use crate::britton_via_tower::*;
    use crate::normal_form_afp_textbook::Syllable;
    let md = m3_data();
    let e = empty_word();
    let esyl = Seq::<Syllable>::empty();
    if gs.len() == 0 {
        assert(gap_word(gs) =~= e);
        assert(gap_syls(gs) =~= esyl);
    } else {
        let g0 = gs.first();
        let rest = gs.drop_first();
        assert(nf_gap(g0));
        assert(forall|i: int| 0 <= i < rest.len() ==> nf_gap(#[trigger] rest[i])) by {
            assert forall|i: int| 0 <= i < rest.len() implies nf_gap(#[trigger] rest[i]) by { assert(rest[i] == gs[i + 1]); }
        }
        lemma_act_gap_word(rest);                          // act(gap_word(rest),ε,[]) == (ε, gap_syls(rest))
        // gap_word(gs) = ([q]·g0) · gap_word(rest)
        assert(gap_word(gs) =~= concat(concat(seq![Symbol::Gen(2)], g0), gap_word(rest)));
        lemma_act_compose(md, concat(seq![Symbol::Gen(2)], g0), gap_word(rest), e, esyl);
        // inner processes gap_word(rest) → (ε, gap_syls(rest)); then process [q]·g0 on that
        lemma_act_compose(md, seq![Symbol::Gen(2)], g0, e, gap_syls(rest));
        // act(g0, ε, gap_syls(rest)) = (g0, gap_syls(rest))   [g0 is a base word]
        assert(md.base.num_generators == 2) by { crate::higman_operations::lemma_free_group_valid(2); }
        assert(forall|i: int| 0 <= i < g0.len() ==> !is_stable(md, #[trigger] g0[i])) by {
            assert forall|i: int| 0 <= i < g0.len() implies !is_stable(md, #[trigger] g0[i]) by { assert(symbol_valid(g0[i], 2)); }
        }
        lemma_act_base(md, g0, e, gap_syls(rest));
        assert(concat(g0, e) =~= g0);
        // act([q], g0, gap_syls(rest)) = psi_p(g0, gap_syls(rest))
        let q1 = seq![Symbol::Gen(2)];
        assert(q1.last() == Symbol::Gen(md.base.num_generators));
        let (hn, sn) = textbook_psi_p(md, g0, gap_syls(rest));
        assert(q1.drop_last() =~= e);
        assert(textbook_act_hnn(md, q1.drop_last(), hn, sn) == (hn, sn));
        assert(textbook_act_hnn(md, q1, g0, gap_syls(rest))
            == textbook_psi_p(md, g0, gap_syls(rest)));
        assert(gap_syls(rest).len() == 0 || !gap_syls(rest).first().is_left) by {
            if gap_syls(rest).len() > 0 { assert(gap_syls(rest).first() == gap_syls(rest)[0]); }
        }
        lemma_psi_p_nf_gap(g0, gap_syls(rest));            // = (ε, {false,g0}::gap_syls(rest))
        assert(Seq::new(1, |_i: int| Syllable { is_left: false, rep: g0 }) + gap_syls(rest) =~= gap_syls(gs));
    }
}

// ═══ B3 fix: firing bq'→qa is a Thue move (= the b·b⁻¹ free-reduction in sub) ═══
// m3_rules()[0]: qa (lhs) = bq' (rhs). So replacing bq'→qa is rule 0 backward.
pub proof fn lemma_bq_qa_thue(x: Word, y: Word)
    ensures thue_equiv(m3_rules(),
        concat(x, concat(seq![Symbol::Gen(1), Symbol::Gen(3)], y)),
        concat(x, concat(seq![Symbol::Gen(2), Symbol::Gen(0)], y))),
{
    let bq = seq![Symbol::Gen(1), Symbol::Gen(3)];   // bq' = rules[0].rhs
    let qa = seq![Symbol::Gen(2), Symbol::Gen(0)];   // qa  = rules[0].lhs
    let u = concat(x, concat(bq, y));
    let v = concat(x, concat(qa, y));
    let pos = x.len() as int;
    assert(u =~= x + bq + y);
    assert(v =~= x + qa + y);
    assert(m3_rules()[0].rhs =~= bq);
    assert(m3_rules()[0].lhs =~= qa);
    assert(u.subrange(0, pos) =~= x);
    assert(u.subrange(pos, pos + 2) =~= bq);
    assert(u.subrange(pos + 2, u.len() as int) =~= y);
    assert(thue_step_at(m3_rules()[0], u, v, pos, false)) by {
        assert(u.subrange(pos, pos + m3_rules()[0].rhs.len() as int) =~= m3_rules()[0].rhs);
        assert(v =~= u.subrange(0, pos) + m3_rules()[0].lhs
            + u.subrange(pos + m3_rules()[0].rhs.len() as int, u.len() as int));
    }
    assert(thue_step(m3_rules(), u, v)) by { assert(thue_step_at(m3_rules()[0], u, v, pos, false)); }
    lemma_thue_single(m3_rules(), u, v);
}

} // verus!