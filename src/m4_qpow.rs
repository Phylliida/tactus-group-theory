// m4_qpow.rs — M4 B8 enabler (2): q·(ab)^e·q⁻¹ ≡ (ba)^e  (future "peeling producer" infrastructure).
//
// STATUS: the reusable NON-RECURSIVE machinery below VERIFIES (~40s). The recursive tie-together
// `lemma_qpow_conj` is BLOCKED by a tactus Lean-backend cliff and is commented out at the bottom.
// Full diagnosis + minimal repro + what to try: docs/m4-qpow-cliff-handoff.md.
// One-line summary: a recursive proof fn whose equiv motive RELATES TWO DIFFERENT symbolic-recursive
// words (abpow(e) LHS vs bapow(e) RHS) hangs under --lean-backend. Same-word recursion, using a
// recursive result, and having both fns present are all FAST; only relating the two loops. No source
// dodge works (decreases form / opaque motive / opaque Word params all hang) because the theorem's
// induction hypothesis IS that different-words equiv. qpow_step_pos proves it fine non-recursively.
use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::m4_defect_flow::*;

verus! {

// ── unfold EQUATIONS ( == ): keep abpow/bapow out of every equiv goal ──
pub proof fn lemma_pow_zero()
    ensures abpow(0) == empty_word(), bapow(0) == empty_word(),
{
    assert(abpow(0) =~= empty_word());
    assert(bapow(0) =~= empty_word());
}

pub proof fn lemma_pow_unfold_pos(e: int)
    requires e > 0,
    ensures
        abpow(e) == seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(e - 1),
        bapow(e) == seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(e - 1),
{
    assert(abpow(e) =~= seq![Symbol::Gen(0), Symbol::Gen(1)] + abpow(e - 1));
    assert(bapow(e) =~= seq![Symbol::Gen(1), Symbol::Gen(0)] + bapow(e - 1));
}

pub proof fn lemma_pow_unfold_neg(e: int)
    requires e < 0,
    ensures
        abpow(e) == seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(e + 1),
        bapow(e) == seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(e + 1),
{
    assert(abpow(e) =~= seq![Symbol::Inv(1), Symbol::Inv(0)] + abpow(e + 1));
    assert(bapow(e) =~= seq![Symbol::Inv(0), Symbol::Inv(1)] + bapow(e + 1));
}

// ── (q·x·q⁻¹)·(q·y·q⁻¹) ≡ q·(x·y)·q⁻¹ ──
proof fn lemma_conj_split(x: Word, y: Word)
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        (seq![Symbol::Gen(2)] + x + seq![Symbol::Inv(2)]) + (seq![Symbol::Gen(2)] + y + seq![Symbol::Inv(2)]),
        seq![Symbol::Gen(2)] + (x + y) + seq![Symbol::Inv(2)]),
{
    use crate::presentation_lemmas::*;
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let ax = seq![Symbol::Gen(2)] + x;
    let by = y + seq![Symbol::Inv(2)];
    let mid = seq![Symbol::Inv(2), Symbol::Gen(2)];
    assert(inverse_word(seq![Symbol::Gen(2)]) =~= seq![Symbol::Inv(2)]) by (compute);
    lemma_word_inverse_left(hp, seq![Symbol::Gen(2)]);
    assert(concat(inverse_word(seq![Symbol::Gen(2)]), seq![Symbol::Gen(2)]) =~= mid);
    lemma_equiv_concat_right(hp, ax, mid, empty_word());
    assert(concat(ax, empty_word()) =~= ax);
    lemma_equiv_concat_left(hp, concat(ax, mid), ax, by);
    assert((ax + mid) + by =~= (seq![Symbol::Gen(2)] + x + seq![Symbol::Inv(2)]) + (seq![Symbol::Gen(2)] + y + seq![Symbol::Inv(2)]));
    assert(ax + by =~= seq![Symbol::Gen(2)] + (x + y) + seq![Symbol::Inv(2)]);
}

// ── q·(ab)⁻¹·q⁻¹ ≡ (ba)⁻¹ ──
pub proof fn lemma_qabinv_equiv_bainv()
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)],
        seq![Symbol::Inv(0), Symbol::Inv(1)]),
{
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    lemma_qab_equiv_ba();
    assert(word_valid(seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)], 3));
    assert(word_valid(seq![Symbol::Gen(1), Symbol::Gen(0)], 3));
    crate::normal_form_afp_textbook::lemma_equiv_inverse(hp,
        seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)],
        seq![Symbol::Gen(1), Symbol::Gen(0)]);
    assert(inverse_word(seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)]) =~= seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)]) by (compute);
    assert(inverse_word(seq![Symbol::Gen(1), Symbol::Gen(0)]) =~= seq![Symbol::Inv(0), Symbol::Inv(1)]) by (compute);
}

// ── GENERIC HNN-conjugation step over OPAQUE words (NO abpow/bapow) — shaped like the fast qab_equiv_ba ──
proof fn qconj_step_generic(blk: Word, cblk: Word, u: Word, v: Word)
    requires
        word_valid(blk, 3),
        word_valid(u, 3),
        equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
            seq![Symbol::Gen(2)] + blk + seq![Symbol::Inv(2)], cblk),
        equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
            seq![Symbol::Gen(2)] + u + seq![Symbol::Inv(2)], v),
    ensures
        equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
            seq![Symbol::Gen(2)] + (blk + u) + seq![Symbol::Inv(2)], cblk + v),
{
    use crate::presentation_lemmas::*;
    use crate::presentation::{lemma_equiv_symmetric, lemma_equiv_transitive};
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    let a = (q + blk + qi) + (q + u + qi);
    let goal_l = q + (blk + u) + qi;
    lemma_conj_split(blk, u);
    assert(equiv_in_presentation(hp, a, goal_l));
    lemma_equiv_concat_left(hp, q + blk + qi, cblk, q + u + qi);
    lemma_equiv_concat_right(hp, cblk, q + u + qi, v);
    lemma_equiv_transitive(hp, a, cblk + (q + u + qi), cblk + v);
    // word_valid(a, 3) for lemma_equiv_symmetric (a = (q·blk·q⁻¹)·(q·u·q⁻¹)):
    assert(word_valid(q, 3) && word_valid(qi, 3));
    lemma_concat_word_valid(q, blk, 3);
    lemma_concat_word_valid(q + blk, qi, 3);
    lemma_concat_word_valid(q, u, 3);
    lemma_concat_word_valid(q + u, qi, 3);
    lemma_concat_word_valid(q + blk + qi, q + u + qi, 3);
    lemma_equiv_symmetric(hp, a, goal_l);
    lemma_equiv_transitive(hp, goal_l, a, cblk + v);
}

// ── step lemmas: instantiate the generic step + substitute by == equations (no power inside any equiv goal) ──
proof fn qpow_step_pos(e: int)
    requires
        e > 0,
        equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
            seq![Symbol::Gen(2)] + abpow(e - 1) + seq![Symbol::Inv(2)], bapow(e - 1)),
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2)] + abpow(e) + seq![Symbol::Inv(2)], bapow(e)),
{
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    let blk = seq![Symbol::Gen(0), Symbol::Gen(1)];
    let ba = seq![Symbol::Gen(1), Symbol::Gen(0)];
    lemma_qab_equiv_ba();
    assert(q + blk + qi =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)]);
    lemma_abpow_valid(e - 1);
    crate::britton_infra::lemma_word_valid_monotone(abpow(e - 1), 2);   // word_valid(abpow(e-1), 3)
    qconj_step_generic(blk, ba, abpow(e - 1), bapow(e - 1));
    lemma_pow_unfold_pos(e);
    assert(q + abpow(e) + qi == q + (blk + abpow(e - 1)) + qi);
    assert(bapow(e) == ba + bapow(e - 1));
}

proof fn qpow_step_neg(e: int)
    requires
        e < 0,
        equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
            seq![Symbol::Gen(2)] + abpow(e + 1) + seq![Symbol::Inv(2)], bapow(e + 1)),
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2)] + abpow(e) + seq![Symbol::Inv(2)], bapow(e)),
{
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    let blk = seq![Symbol::Inv(1), Symbol::Inv(0)];
    let bai = seq![Symbol::Inv(0), Symbol::Inv(1)];
    lemma_qabinv_equiv_bainv();
    assert(q + blk + qi =~= seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)]);
    lemma_abpow_valid(e + 1);
    crate::britton_infra::lemma_word_valid_monotone(abpow(e + 1), 2);   // word_valid(abpow(e+1), 3)
    qconj_step_generic(blk, bai, abpow(e + 1), bapow(e + 1));
    lemma_pow_unfold_neg(e);
    assert(q + abpow(e) + qi == q + (blk + abpow(e + 1)) + qi);
    assert(bapow(e) == bai + bapow(e + 1));
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// BLOCKED: the recursive tie-together. Every version below HANGS >240s under --lean-backend (the
// recursive proof fn's ensures is an equiv-over-abpow goal). Tried: if-abs decreases; split simple
// decreases e / -e; opaque motive (#[verifier::opaque] + reveal). All hang. The step lemmas above
// prove exactly the induction step and VERIFY — only the recursive glue is blocked. See
// docs/m4-qpow-cliff-handoff.md for the generated-Lean / backend-fix plan.
//
// pub proof fn lemma_qpow_conj(e: int)
//     ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
//         seq![Symbol::Gen(2)] + abpow(e) + seq![Symbol::Inv(2)], bapow(e)),
//     decreases (if e >= 0 { e } else { -e }),
// {
//     ... if e==0 { base via lemma_pow_zero + lemma_word_inverse_right }
//     else if e>0 { lemma_qpow_conj(e-1); qpow_step_pos(e); }
//     else        { lemma_qpow_conj(e+1); qpow_step_neg(e); }
// }
// ═══════════════════════════════════════════════════════════════════════════════════════════════

} // verus!
