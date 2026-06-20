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
use crate::machine_group::*;
use crate::ii_subset::lemma_ii_subset;
use crate::benign::{apply_embedding, in_generated_subgroup};
use crate::tower_peel::{quad_data, lemma_in_TM_gexp_zero};
use crate::config_reduce::{lemma_in_TM_residue_reduced};

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

} //  verus!
