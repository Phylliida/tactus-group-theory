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

} // verus!