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

} // verus!
