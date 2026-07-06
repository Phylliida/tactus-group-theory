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

} // verus!
