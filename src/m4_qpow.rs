// m4_qpow.rs — M4 B8 enabler (2): q·(ab)^e·q⁻¹ ≡ (ba)^e  (used later by the peeling producer).
//
// QUARANTINED out of m4_defect_flow.rs: lemma_qpow_conj is a verification CLIFF under the Lean
// backend (recursive equiv_in_presentation derivation-building — the module verified in minutes at
// 43 fns and stopped finishing the moment this trio was added). Isolating it keeps m4_defect_flow
// fast + green while this is reworked. Rework idea: prove the e≥0 case by a single-branch
// induction, then derive e<0 non-recursively via lemma_equiv_inverse (mirroring qab→qabinv),
// and drop the intermediate `assert(equiv_in_presentation(...))` re-assertions.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::m4_defect_flow::*;

verus! {

// conjugation splits over concat: (q·x·q⁻¹)·(q·y·q⁻¹) ≡ q·(x·y)·q⁻¹  (middle q⁻¹q cancels).
proof fn lemma_conj_split(x: Word, y: Word)
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        (seq![Symbol::Gen(2)] + x + seq![Symbol::Inv(2)]) + (seq![Symbol::Gen(2)] + y + seq![Symbol::Inv(2)]),
        seq![Symbol::Gen(2)] + (x + y) + seq![Symbol::Inv(2)]),
{
    use crate::presentation_lemmas::*;
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let ax = seq![Symbol::Gen(2)] + x;                       // q·x
    let by = y + seq![Symbol::Inv(2)];                       // y·q⁻¹
    let mid = seq![Symbol::Inv(2), Symbol::Gen(2)];          // q⁻¹·q
    assert(inverse_word(seq![Symbol::Gen(2)]) =~= seq![Symbol::Inv(2)]) by (compute);
    lemma_word_inverse_left(hp, seq![Symbol::Gen(2)]);        // q⁻¹·q ≡ ε
    assert(concat(inverse_word(seq![Symbol::Gen(2)]), seq![Symbol::Gen(2)]) =~= mid);
    lemma_equiv_concat_right(hp, ax, mid, empty_word());     // ax·mid ≡ ax·ε
    assert(concat(ax, empty_word()) =~= ax);
    lemma_equiv_concat_left(hp, concat(ax, mid), ax, by);    // (ax·mid)·by ≡ ax·by
    assert((ax + mid) + by =~= (seq![Symbol::Gen(2)] + x + seq![Symbol::Inv(2)]) + (seq![Symbol::Gen(2)] + y + seq![Symbol::Inv(2)]));
    assert(ax + by =~= seq![Symbol::Gen(2)] + (x + y) + seq![Symbol::Inv(2)]);
}

// q·(ab)⁻¹·q⁻¹ ≡ (ba)⁻¹  — the inverse of lemma_qab_equiv_ba.
pub proof fn lemma_qabinv_equiv_bainv()
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)],   // q·b⁻¹a⁻¹·q⁻¹
        seq![Symbol::Inv(0), Symbol::Inv(1)]),                                  // (ba)⁻¹
{
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    lemma_qab_equiv_ba();
    assert(hp.num_generators == 3);
    assert(word_valid(seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)], 3));
    assert(word_valid(seq![Symbol::Gen(1), Symbol::Gen(0)], 3));
    crate::normal_form_afp_textbook::lemma_equiv_inverse(hp,
        seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)],
        seq![Symbol::Gen(1), Symbol::Gen(0)]);
    assert(inverse_word(seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)]) =~= seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)]) by (compute);
    assert(inverse_word(seq![Symbol::Gen(1), Symbol::Gen(0)]) =~= seq![Symbol::Inv(0), Symbol::Inv(1)]) by (compute);
}

pub proof fn lemma_qpow_conj(e: int)
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2)] + abpow(e) + seq![Symbol::Inv(2)], bapow(e)),
    decreases (if e >= 0 { e } else { -e }),
{
    use crate::presentation_lemmas::*;
    use crate::presentation::{lemma_equiv_symmetric, lemma_equiv_transitive};
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    let goal_l = q + abpow(e) + qi;
    if e == 0 {
        assert(abpow(0) =~= empty_word() && bapow(0) =~= empty_word());
        assert(inverse_word(q) =~= qi) by (compute);
        lemma_word_inverse_right(hp, q);                     // q·q⁻¹ ≡ ε
        assert(concat(q, inverse_word(q)) =~= q + qi);
        assert(goal_l =~= q + qi);
        assert(empty_word() =~= bapow(0));
    } else if e > 0 {
        let blk = seq![Symbol::Gen(0), Symbol::Gen(1)];       // ab
        let t = abpow(e - 1);
        let a = (q + blk + qi) + (q + t + qi);               // split
        let ba = seq![Symbol::Gen(1), Symbol::Gen(0)];
        lemma_conj_split(blk, t);                            // equiv(a, q·(blk·t)·q⁻¹)
        assert(blk + t =~= abpow(e));
        assert(q + (blk + t) + qi =~= goal_l);
        assert(equiv_in_presentation(hp, a, goal_l));        // rewrite 2nd arg via ==
        // first factor ≡ ba
        assert(q + blk + qi =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)]);
        lemma_qab_equiv_ba();
        assert(equiv_in_presentation(hp, q + blk + qi, ba));
        // second factor ≡ bapow(e-1)
        lemma_qpow_conj(e - 1);                              // equiv(q+t+qi, bapow(e-1))
        lemma_equiv_concat_left(hp, q + blk + qi, ba, q + t + qi);       // equiv(a, ba·(q+t+qi))
        lemma_equiv_concat_right(hp, ba, q + t + qi, bapow(e - 1));      // equiv(ba·(q+t+qi), ba·bapow(e-1))
        lemma_equiv_transitive(hp, a, ba + (q + t + qi), ba + bapow(e - 1));
        assert(ba + bapow(e - 1) =~= bapow(e));
        assert(equiv_in_presentation(hp, a, bapow(e)));
        lemma_equiv_symmetric(hp, a, goal_l);               // equiv(goal_l, a)
        lemma_equiv_transitive(hp, goal_l, a, bapow(e));
    } else {
        let blk = seq![Symbol::Inv(1), Symbol::Inv(0)];       // (ab)⁻¹
        let t = abpow(e + 1);
        let a = (q + blk + qi) + (q + t + qi);
        let bai = seq![Symbol::Inv(0), Symbol::Inv(1)];       // (ba)⁻¹
        lemma_conj_split(blk, t);
        assert(blk + t =~= abpow(e));
        assert(q + (blk + t) + qi =~= goal_l);
        assert(equiv_in_presentation(hp, a, goal_l));
        assert(q + blk + qi =~= seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)]);
        lemma_qabinv_equiv_bainv();
        assert(equiv_in_presentation(hp, q + blk + qi, bai));
        lemma_qpow_conj(e + 1);
        lemma_equiv_concat_left(hp, q + blk + qi, bai, q + t + qi);
        lemma_equiv_concat_right(hp, bai, q + t + qi, bapow(e + 1));
        lemma_equiv_transitive(hp, a, bai + (q + t + qi), bai + bapow(e + 1));
        assert(bai + bapow(e + 1) =~= bapow(e));
        assert(equiv_in_presentation(hp, a, bapow(e)));
        lemma_equiv_symmetric(hp, a, goal_l);
        lemma_equiv_transitive(hp, goal_l, a, bapow(e));
    }
}

} // verus!
