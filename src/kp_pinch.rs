//  ============================================================
//  E2.C / L1 — ⟨K,p⟩ pinch elimination (the central engine of property II).
//  ============================================================
//  Kept in its own module (separate from ii_subset's conjugation engine) to avoid trigger
//  pollution and concurrent-edit churn.  See docs/e2c-property-ii-design.md.
//
//  K is abstracted as `in_k: spec_fn(Word)->bool` with four hypotheses (all instantiated for
//  K=T(M) later via the in_subgroup_pred closure lemmas + property (v)):
//    H_resp : in_k respects base-equivalence
//    H_mul  : in_k closed under product
//    H_ab   : φ-compatibility A→B   (in_k(emb(a_gens,uw)) ⟹ in_k(emb(b_gens,uw)))
//    H_ba   : φ-compatibility B→A
//
//  L1 (this file): a KP-word with a KP-pinch at index i ⟹ a KP-word with 2 fewer p's, ≡ value,
//  still a KP-word.  Recursion is on the pinch index i — the base case (i==0) does the
//  conjugation surgery, the recursive case peels the head and recurses into the tail.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::machine_group::{hnn_a_gens, hnn_b_gens, lemma_stable_conj_factorization,
    lemma_stable_conj_factorization_rev, lemma_in_gen_implies_emb};
use crate::benign::{in_generated_subgroup, apply_embedding};
use crate::ii_subset::{KPWord, kp_value, kp_pcount, is_kp_word, lemma_kp_value_cons};

verus! {

//  Forward φ-helper:  mid ∈ K∩A₊  ⟹  ∃ phi ∈ K with  p⁻¹·mid·p ≡ phi.
pub proof fn lemma_kp_phi_fwd(data: HNNData, in_k: spec_fn(Word) -> bool, mid: Word) -> (phi: Word)
    requires
        hnn_data_valid(data),
        forall|a: Word, b: Word| in_k(a) && #[trigger] equiv_in_presentation(data.base, a, b) ==> in_k(b),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_a_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_b_gens(data), uw)),
        in_k(mid),
        in_generated_subgroup(data.base, hnn_a_gens(data), mid),
    ensures
        in_k(phi),
        equiv_in_presentation(hnn_presentation(data),
            seq![stable_letter_inv(data)] + mid + seq![stable_letter(data)], phi),
{
    let pres = hnn_presentation(data);
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    let ag = hnn_a_gens(data);
    let bg = hnn_b_gens(data);
    let k = data.associations.len();
    lemma_in_gen_implies_emb(data.base, ag, mid);
    let uw = choose|uw: Word| word_valid(uw, ag.len() as nat)
        && equiv_in_presentation(data.base, apply_embedding(ag, uw), mid);
    assert(word_valid(uw, k as nat)
        && equiv_in_presentation(data.base, apply_embedding(ag, uw), mid));
    let g = apply_embedding(ag, uw);
    let phi = apply_embedding(bg, uw);
    //  conjugation:  [si] + g + [st] ≡ phi
    lemma_stable_conj_factorization(data, uw);
    //  bridge  mid ≡_pres g
    lemma_base_embeds_in_hnn(data, g, mid);
    lemma_equiv_symmetric(pres, g, mid);
    //  congruence:  [si] + mid + [st] ≡ [si] + g + [st]
    lemma_equiv_concat_right(pres, seq![si], mid, g);
    lemma_equiv_concat_left(pres, seq![si] + mid, seq![si] + g, seq![st]);
    lemma_equiv_transitive(pres, seq![si] + mid + seq![st], seq![si] + g + seq![st], phi);
    //  in_k(phi):  H_resp (mid → g), then H_ab (uw)
    lemma_equiv_symmetric(data.base, g, mid);
    assert(in_k(g));
    assert(in_k(phi));
    phi
}

//  Reverse φ-helper:  mid ∈ K∩A₋  ⟹  ∃ phi ∈ K with  p·mid·p⁻¹ ≡ phi.
pub proof fn lemma_kp_phi_rev(data: HNNData, in_k: spec_fn(Word) -> bool, mid: Word) -> (phi: Word)
    requires
        hnn_data_valid(data),
        forall|a: Word, b: Word| in_k(a) && #[trigger] equiv_in_presentation(data.base, a, b) ==> in_k(b),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_b_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_a_gens(data), uw)),
        in_k(mid),
        in_generated_subgroup(data.base, hnn_b_gens(data), mid),
    ensures
        in_k(phi),
        equiv_in_presentation(hnn_presentation(data),
            seq![stable_letter(data)] + mid + seq![stable_letter_inv(data)], phi),
{
    let pres = hnn_presentation(data);
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    let ag = hnn_a_gens(data);
    let bg = hnn_b_gens(data);
    let k = data.associations.len();
    lemma_in_gen_implies_emb(data.base, bg, mid);
    let uw = choose|uw: Word| word_valid(uw, bg.len() as nat)
        && equiv_in_presentation(data.base, apply_embedding(bg, uw), mid);
    assert(word_valid(uw, k as nat)
        && equiv_in_presentation(data.base, apply_embedding(bg, uw), mid));
    let g = apply_embedding(bg, uw);
    let phi = apply_embedding(ag, uw);
    //  reverse conjugation:  [st] + g + [si] ≡ phi
    lemma_stable_conj_factorization_rev(data, uw);
    //  bridge  mid ≡_pres g
    lemma_base_embeds_in_hnn(data, g, mid);
    lemma_equiv_symmetric(pres, g, mid);
    //  congruence:  [st] + mid + [si] ≡ [st] + g + [si]
    lemma_equiv_concat_right(pres, seq![st], mid, g);
    lemma_equiv_concat_left(pres, seq![st] + mid, seq![st] + g, seq![si]);
    lemma_equiv_transitive(pres, seq![st] + mid + seq![si], seq![st] + g + seq![si], phi);
    //  in_k(phi):  H_resp (mid → g), then H_ba (uw)
    lemma_equiv_symmetric(data.base, g, mid);
    assert(in_k(g));
    assert(in_k(phi));
    phi
}

//  A KP-pinch at index i: opposite-sign consecutive p's at tail[i], tail[i+1], with the
//  syllable between them (tail[i].1) lying in the appropriate associated subgroup.
//    tail[i].0 == false  (p⁻¹·mid·p)  ⟹  mid ∈ A₊ = ⟨a_gens⟩
//    tail[i].0 == true   (p·mid·p⁻¹)  ⟹  mid ∈ A₋ = ⟨b_gens⟩
pub open spec fn kp_has_pinch_at(data: HNNData, kp: KPWord, i: int) -> bool {
    &&& 0 <= i
    &&& i + 1 < kp.tail.len()
    &&& kp.tail[i].0 != kp.tail[i + 1].0
    &&& (kp.tail[i].0 == false ==> in_generated_subgroup(data.base, hnn_a_gens(data), kp.tail[i].1))
    &&& (kp.tail[i].0 == true ==> in_generated_subgroup(data.base, hnn_b_gens(data), kp.tail[i].1))
}

//  kp_value of a KP-word splits off its head:  value{head,tail} = head + value{ε,tail}.
pub proof fn lemma_kp_value_head_split(stable: Symbol, head: Word, tail: Seq<(bool, Word)>)
    ensures
        kp_value(stable, KPWord { head, tail })
            =~= head + kp_value(stable, KPWord { head: empty_word(), tail }),
{
    if tail.len() == 0 {
        assert(kp_value(stable, KPWord { head, tail }) =~= head);
        assert(kp_value(stable, KPWord { head: empty_word(), tail }) =~= empty_word());
        assert(head + empty_word() =~= head);
    } else {
        lemma_kp_value_cons(stable, KPWord { head, tail });
        lemma_kp_value_cons(stable, KPWord { head: empty_word(), tail });
    }
}

} //  verus!
