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

} // verus!
