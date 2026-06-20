//  ============================================================
//  E2.B — property (v) assembly:  prop_v_holds.
//  ============================================================
//  Own module (imports both config_reduce and tower_peel; keeps config_reduce a generic library).
//  See docs/property-v-tfree-architecture.md.  Consumes the Part-A crux (config_reduce) and the
//  quad wiring (ii_subset, tower_peel) to discharge prop_v_holds — the last hole of lemma_vi.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::hnn::*;
use crate::ii_subset::{lemma_ii_subset, lemma_signed_power_inverse};
use crate::benign::{apply_embedding, apply_embedding_symbol, in_generated_subgroup,
    lemma_apply_embedding_concat};
use crate::tower_peel::{quad_data, lemma_in_TM_gexp_zero};
use crate::config_reduce::*;

verus! {

//  hnn_a_gens(quad_data(mm,qi)) is the explicit residue-generator triple [t(a,b), xᵐ, yᵐ].
pub proof fn lemma_quad_a_gens_form(mm: ModMachine, qi: nat)
    requires
        qi < mm.quads.len(),
    ensures
        hnn_a_gens(quad_data(mm, qi)) =~= seq![
            config_word(mm.quads[qi as int].a, mm.quads[qi as int].b),
            signed_power(1, mm.m as int),
            signed_power(2, mm.m as int)
        ],
{
    let q = mm.quads[qi as int];
    let ag = hnn_a_gens(quad_data(mm, qi));
    let assoc = quad_associations(q, mm.m);
    assert(ag.len() == 3);
    assert(ag[0] == assoc[0].0);
    assert(ag[1] == assoc[1].0);
    assert(ag[2] == assoc[2].0);
    //  Both R and L share the .0 column: [t(a,b), xᵐ, yᵐ].
    assert(assoc[0].0 == config_word(q.a, q.b));
    assert(assoc[1].0 == symbol_power(Symbol::Gen(1), mm.m));
    assert(assoc[2].0 == symbol_power(Symbol::Gen(2), mm.m));
    assert(signed_power(1, mm.m as int) =~= symbol_power(Symbol::Gen(1), mm.m));
    assert(signed_power(2, mm.m as int) =~= symbol_power(Symbol::Gen(2), mm.m));
}

//  From in_TM of an a-side embedding, derive membership in the residue class ⟨t(r,s):r≡a,s≡b⟩.
pub proof fn lemma_emb_a_in_residue_class(mm: ModMachine, qi: nat, uw: Word)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
        word_valid(uw, 3),
        in_TM(mm, apply_embedding(hnn_a_gens(quad_data(mm, qi)), uw)),
    ensures
        in_residue_class(mm.quads[qi as int].a as int, mm.quads[qi as int].b as int, mm.m as int,
            apply_embedding(hnn_a_gens(quad_data(mm, qi)), uw)),
{
    let q = mm.quads[qi as int];
    let ag = hnn_a_gens(quad_data(mm, qi));
    let g = apply_embedding(ag, uw);
    lemma_base_A_valid();
    //  emb ∈ ⟨a_gens⟩
    assert(ag.len() == 3);
    assert(word_valid(uw, ag.len() as nat));
    lemma_apply_embedding_in_subgroup(base_A(), ag, uw);
    //  a_gens = the explicit triple
    lemma_quad_a_gens_form(mm, qi);
    let iigens = seq![config_word(q.a, q.b), signed_power(1, mm.m as int), signed_power(2, mm.m as int)];
    assert(ag =~= iigens);
    assert(in_generated_subgroup(base_A(), iigens, g));
    //  gexp(1,g) = gexp(2,g) = 0
    lemma_in_TM_gexp_zero(mm, g, 1);
    lemma_in_TM_gexp_zero(mm, g, 2);
    //  ii_subset ⟹ in_residue_class
    assert(mm.m > 1);
    lemma_ii_subset(q.a, q.b, mm.m, g);
}

//  From in_TM of an a-side embedding, get its H₀∩residue reduced form (consumes the Part-A crux).
pub proof fn lemma_emb_a_reduced(mm: ModMachine, qi: nat, uw: Word)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
        word_valid(uw, 3),
        in_TM(mm, apply_embedding(hnn_a_gens(quad_data(mm, qi)), uw)),
    ensures
        exists|red: Seq<CanonLetter>| {
            &&& canw_reduced(red)
            &&& equiv_in_presentation(base_A(), canw_eval(red),
                    apply_embedding(hnn_a_gens(quad_data(mm, qi)), uw))
            &&& (forall|i: int| 0 <= i < red.len() ==> {
                    &&& (#[trigger] red[i]).r >= 0
                    &&& red[i].s >= 0
                    &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
                    &&& (red[i].r - mm.quads[qi as int].a as int) % (mm.m as int) == 0
                    &&& (red[i].s - mm.quads[qi as int].b as int) % (mm.m as int) == 0
                })
        },
{
    let g = apply_embedding(hnn_a_gens(quad_data(mm, qi)), uw);
    lemma_emb_a_in_residue_class(mm, qi, uw);
    lemma_in_TM_residue_reduced(mm, mm.quads[qi as int].a as int, mm.quads[qi as int].b as int,
        mm.m as int, g);
}

//  ============================================================
//  B4 — per-letter embedding lemmas (the algebraic core).
//  ============================================================

//  Signed config-power conjugation by x:  x⁻ᵖᵖ · gsconfig(r,s,e) · xᵖᵖ ≡ gsconfig(r+pp, s, e).
//  Identical to lemma_sconfig_conj_x but with the t-letter replaced by t^e (middle-independent:
//  the prefix/suffix conj lemmas only move the outer x-power past the y⁻ˢ/yˢ).
#[verifier::rlimit(100)]
pub proof fn lemma_conj_gsconfig_by_x(r: int, s: int, e: int, pp: int)
    ensures
        equiv_in_presentation(base_A(),
            signed_power(1, -pp) + gsconfig(r, s, e) + signed_power(1, pp),
            gsconfig(r + pp, s, e)),
{
    let a = base_A();
    lemma_base_A_valid();
    let xmP = signed_power(1, -pp);
    let xP = signed_power(1, pp);
    let mid = signed_power(0, e);
    let preL = signed_power(1, -pp) + signed_power(2, -s) + signed_power(1, -r);
    let preL2 = signed_power(2, -s) + signed_power(1, -(r + pp));
    let sufR = signed_power(1, r) + signed_power(2, s) + signed_power(1, pp);
    let sufR2 = signed_power(1, (r + pp)) + signed_power(2, s);
    lemma_sconfig_prefix_conj(r, s, pp);                     //  preL ≡ preL2
    lemma_sconfig_suffix_conj(r, s, pp);                     //  sufR ≡ sufR2
    let lhs = xmP + gsconfig(r, s, e) + xP;
    let rhs = gsconfig(r + pp, s, e);
    assert(lhs =~= preL + (mid + sufR));
    assert(rhs =~= preL2 + (mid + sufR2));
    let m1 = preL2 + (mid + sufR);
    assert(equiv_in_presentation(a, lhs, m1)) by {
        lemma_equiv_concat_left(a, preL, preL2, mid + sufR);
        assert(lhs =~= preL + (mid + sufR));
        assert(m1 =~= preL2 + (mid + sufR));
    }
    assert(equiv_in_presentation(a, m1, rhs)) by {
        lemma_equiv_concat_right(a, preL2 + mid, sufR, sufR2);
        assert(m1 =~= (preL2 + mid) + sufR);
        assert(rhs =~= (preL2 + mid) + sufR2);
    }
    lemma_equiv_transitive(a, lhs, m1, rhs);
}

//  Signed config-power conjugation by y:  y⁻ᵠ · gsconfig(r,s,e) · yᵠ ≡ gsconfig(r, s+qq, e).
#[verifier::rlimit(100)]
pub proof fn lemma_conj_gsconfig_by_y(r: int, s: int, e: int, qq: int)
    ensures
        equiv_in_presentation(base_A(),
            signed_power(2, -qq) + gsconfig(r, s, e) + signed_power(2, qq),
            gsconfig(r, s + qq, e)),
{
    let a = base_A();
    lemma_base_A_valid();
    let ymQ = signed_power(2, -qq);
    let yQ = signed_power(2, qq);
    let middle = signed_power(1, -r) + signed_power(0, e) + signed_power(1, r);
    let preL = signed_power(2, -qq) + signed_power(2, -s);
    let preL2 = signed_power(2, -(s + qq));
    let sufR = signed_power(2, s) + signed_power(2, qq);
    let sufR2 = signed_power(2, (s + qq));
    lemma_signed_power_add(a, 2, -qq, -s);                   //  ymQ·y⁻ˢ ≡ y^(-qq-s)
    assert(signed_power(2, -qq + -s) == preL2) by { assert(-qq + -s == -(s + qq)); }
    lemma_signed_power_add(a, 2, s, qq);                     //  yˢ·yQ ≡ y^(s+qq)
    let lhs = ymQ + gsconfig(r, s, e) + yQ;
    let rhs = gsconfig(r, (s + qq), e);
    assert(lhs =~= preL + (middle + sufR));
    assert(rhs =~= preL2 + (middle + sufR2));
    let m1 = preL2 + (middle + sufR);
    assert(equiv_in_presentation(a, lhs, m1)) by {
        lemma_equiv_concat_left(a, preL, preL2, middle + sufR);
        assert(lhs =~= preL + (middle + sufR));
        assert(m1 =~= preL2 + (middle + sufR));
    }
    assert(equiv_in_presentation(a, m1, rhs)) by {
        lemma_equiv_concat_right(a, preL2 + middle, sufR, sufR2);
        assert(m1 =~= (preL2 + middle) + sufR);
        assert(rhs =~= (preL2 + middle) + sufR2);
    }
    lemma_equiv_transitive(a, lhs, m1, rhs);
}

} //  verus!
