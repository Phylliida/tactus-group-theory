use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_equiv_concat_right,
    lemma_word_inverse_left, lemma_word_inverse_right};
use crate::machine_group::{symbol_power, word_power, lemma_symbol_power_one,
    lemma_symbol_power_merge};
use crate::miller_collapse::{b_sub, binv_sub};

verus! {

// ===========================================================================
// GAP-1, §9.2-item-(2), BRICK 1 — the conjugation telescoping engine.
//
// `docs/final-gate-axiom-removal-plan.md` §9.2/§11.  Danielle signed off (2026-06-26) on the
// fresh-`{a,t}`-Presentation packaging and the D̄_M shape; this module builds the *engine* underneath
// the well-definedness brick (`apply_embedding(emb_M, hnn_relator(i)) ≡ ε`): the fact that a power of
// the collapsed `b = tat⁻¹` telescopes,
//        (t aᵏ t⁻¹)  ←  word_power(b_sub, k)   ≡   t · aᵏ · t⁻¹.
// This is what makes Miller's `uⱼ` discharge the HNN associations as *free tautologies* after the
// `cⱼ↦uⱼ`, `b↦tat⁻¹` substitution, so the associations contribute ZERO relators to D̄_M.
//
// All lemmas are presentation-generic (`∀ p`): the cancellations are pure free reductions, so they
// hold in `free_group(2)`, in `K_M = ⟨a,t|D̄_M⟩`, anywhere.  No codomain commitment lives here.
// ===========================================================================

/// Conjugation of `w` by the generator `t = Gen(t_idx)`:  `t · w · t⁻¹`.
pub open spec fn conj_t(t_idx: nat, w: Word) -> Word {
    seq![Symbol::Gen(t_idx)] + w + seq![Symbol::Inv(t_idx)]
}

/// `inverse_word([Gen(t)]) =~= [Inv(t)]` — singleton-inverse, bridged through `lemma_inverse_singleton`.
proof fn lemma_inv_gen_singleton(t_idx: nat)
    ensures
        inverse_word(seq![Symbol::Gen(t_idx)]) =~= seq![Symbol::Inv(t_idx)],
{
    lemma_inverse_singleton(Symbol::Gen(t_idx));
    assert(seq![Symbol::Gen(t_idx)] =~= Seq::new(1, |_i: int| Symbol::Gen(t_idx)));
    assert(Seq::new(1, |_i: int| inverse_symbol(Symbol::Gen(t_idx))) =~= seq![Symbol::Inv(t_idx)]);
}

/// `t · ε · t⁻¹ ≡ ε` — the empty conjugate collapses (the `tt⁻¹` free cancellation).
pub proof fn lemma_conj_empty(p: Presentation, t_idx: nat)
    ensures
        equiv_in_presentation(p, conj_t(t_idx, empty_word()), empty_word()),
{
    let gt = seq![Symbol::Gen(t_idx)];
    // conj_t(t, ε) = gt + ε + [Inv(t)] = gt + inverse_word(gt)
    lemma_inv_gen_singleton(t_idx);
    assert(conj_t(t_idx, empty_word()) =~= concat(gt, inverse_word(gt)));
    lemma_word_inverse_right(p, gt);   // gt · gt⁻¹ ≡ ε
}

/// `(t·x·t⁻¹)·(t·y·t⁻¹) ≡ t·(x·y)·t⁻¹` — the inner `t⁻¹t` cancels.
pub proof fn lemma_conj_mul(p: Presentation, t_idx: nat, x: Word, y: Word)
    ensures
        equiv_in_presentation(p, conj_t(t_idx, x) + conj_t(t_idx, y), conj_t(t_idx, x + y)),
{
    let gt = seq![Symbol::Gen(t_idx)];
    let it = seq![Symbol::Inv(t_idx)];
    let big_l = gt + x;          // t · x
    let mid = it + gt;           // t⁻¹ · t
    let big_r = y + it;          // y · t⁻¹

    // mid = inverse_word(gt) + gt ≡ ε
    lemma_inv_gen_singleton(t_idx);
    assert(inverse_word(gt) =~= it);
    lemma_word_inverse_left(p, gt);   // concat(inverse_word(gt), gt) ≡ ε, i.e. mid ≡ ε

    // mid + big_r ≡ ε + big_r
    lemma_equiv_concat_left(p, mid, empty_word(), big_r);
    // big_l + (mid + big_r) ≡ big_l + (ε + big_r)
    lemma_equiv_concat_right(p, big_l, mid + big_r, empty_word() + big_r);

    // Seq associativity bridges to the two stated words.
    assert(conj_t(t_idx, x) + conj_t(t_idx, y) =~= big_l + (mid + big_r));
    assert(big_l + (empty_word() + big_r) =~= conj_t(t_idx, x + y));
}

/// **Telescoping.**  `word_power(t·s·t⁻¹, i) ≡ t · sⁱ · t⁻¹` for a single symbol `s`.
pub proof fn lemma_conj_power(p: Presentation, t_idx: nat, s: Symbol, i: nat)
    requires
        presentation_valid(p),
        t_idx < p.num_generators,
    ensures
        equiv_in_presentation(p, word_power(conj_t(t_idx, seq![s]), i),
            conj_t(t_idx, symbol_power(s, i))),
    decreases i,
{
    let cs = conj_t(t_idx, seq![s]);
    if i == 0 {
        assert(word_power(cs, 0) =~= empty_word());
        assert(symbol_power(s, 0) =~= empty_word());
        lemma_conj_empty(p, t_idx);   // conj_t(t, ε) ≡ ε
        // flip needs validity: conj_t(t, ε) = [Gen(t), Inv(t)] is valid since t_idx < num_generators
        assert(word_valid(conj_t(t_idx, empty_word()), p.num_generators)) by {
            assert forall|k: int| 0 <= k < conj_t(t_idx, empty_word()).len()
                implies symbol_valid(#[trigger] conj_t(t_idx, empty_word())[k], p.num_generators) by { }
        }
        lemma_equiv_symmetric(p, conj_t(t_idx, empty_word()), empty_word());
    } else {
        let k = (i - 1) as nat;
        // word_power(cs, i) = cs + word_power(cs, k)
        assert(word_power(cs, i) =~= cs + word_power(cs, k));

        // IH: word_power(cs, k) ≡ conj_t(t, sᵏ)
        lemma_conj_power(p, t_idx, s, k);
        // cs + word_power(cs, k) ≡ cs + conj_t(t, sᵏ)
        lemma_equiv_concat_right(p, cs, word_power(cs, k), conj_t(t_idx, symbol_power(s, k)));

        // cs = conj_t(t, s¹) ; merge:  conj_t(t,s¹) + conj_t(t,sᵏ) ≡ conj_t(t, s¹·sᵏ) = conj_t(t, sⁱ)
        lemma_symbol_power_one(s);                                   // symbol_power(s,1) =~= seq![s]
        assert(cs =~= conj_t(t_idx, symbol_power(s, 1)));
        lemma_conj_mul(p, t_idx, symbol_power(s, 1), symbol_power(s, k));
        lemma_symbol_power_merge(s, 1, k);                          // s¹·sᵏ =~= sⁱ
        assert(symbol_power(s, 1) + symbol_power(s, k) =~= symbol_power(s, i));

        // chain:  word_power(cs,i) ≡ cs+conj(sᵏ) ≡ conj(s¹·sᵏ) = conj(sⁱ)
        lemma_equiv_transitive(p, word_power(cs, i),
            cs + conj_t(t_idx, symbol_power(s, k)),
            conj_t(t_idx, symbol_power(s, i)));
    }
}

// ---------------------------------------------------------------------------
// Specializations to the collapsed b/b⁻¹ (`b_sub = tat⁻¹`, `binv_sub = ta⁻¹t⁻¹`).
// ---------------------------------------------------------------------------

/// `word_power(b_sub, i) ≡ t · aⁱ · t⁻¹`  (the collapsed `bⁱ`).
pub proof fn lemma_b_sub_power(p: Presentation, a_idx: nat, t_idx: nat, i: nat)
    requires
        presentation_valid(p),
        t_idx < p.num_generators,
    ensures
        equiv_in_presentation(p, word_power(b_sub(a_idx, t_idx), i),
            conj_t(t_idx, symbol_power(Symbol::Gen(a_idx), i))),
{
    assert(b_sub(a_idx, t_idx) =~= conj_t(t_idx, seq![Symbol::Gen(a_idx)]));
    lemma_conj_power(p, t_idx, Symbol::Gen(a_idx), i);
}

/// `word_power(binv_sub, i) ≡ t · a⁻ⁱ · t⁻¹`  (the collapsed `b⁻ⁱ`).
pub proof fn lemma_binv_sub_power(p: Presentation, a_idx: nat, t_idx: nat, i: nat)
    requires
        presentation_valid(p),
        t_idx < p.num_generators,
    ensures
        equiv_in_presentation(p, word_power(binv_sub(a_idx, t_idx), i),
            conj_t(t_idx, symbol_power(Symbol::Inv(a_idx), i))),
{
    assert(binv_sub(a_idx, t_idx) =~= conj_t(t_idx, seq![Symbol::Inv(a_idx)]));
    lemma_conj_power(p, t_idx, Symbol::Inv(a_idx), i);
}

// ---------------------------------------------------------------------------
// Generic free-cancellation helpers for the association brick.
// ---------------------------------------------------------------------------

/// `inverse_word(sⁿ) = (s⁻¹)ⁿ`  (a constant symbol-power).  (Public copy of the `conj_free_core`
/// private analog — kept local to avoid invalidating that module's cache.)
pub proof fn lemma_inverse_symbol_power(s: Symbol, n: nat)
    ensures
        inverse_word(symbol_power(s, n)) =~= symbol_power(inverse_symbol(s), n),
    decreases n,
{
    if n == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
        assert(symbol_power(inverse_symbol(s), 0) =~= empty_word());
    } else {
        let k = (n - 1) as nat;
        lemma_symbol_power_merge(s, k, 1);
        lemma_symbol_power_one(s);
        assert(symbol_power(s, n) =~= symbol_power(s, k) + seq![s]);
        lemma_inverse_concat(symbol_power(s, k), seq![s]);
        lemma_inverse_symbol_power(s, k);                 // IH
        lemma_inverse_singleton(s);
        assert(seq![s] =~= Seq::new(1, |_i: int| s));
        assert(inverse_word(seq![s]) =~= seq![inverse_symbol(s)]);
        lemma_symbol_power_one(inverse_symbol(s));
        lemma_symbol_power_merge(inverse_symbol(s), 1, k);
        assert(seq![inverse_symbol(s)] + symbol_power(inverse_symbol(s), k)
            =~= symbol_power(inverse_symbol(s), n));
    }
}

/// `sⁿ · (s⁻¹)ⁿ ≡ ε`  (a symbol-power cancels its inverse-symbol-power).
pub proof fn lemma_symbol_power_inverse_cancel(p: Presentation, s: Symbol, n: nat)
    ensures
        equiv_in_presentation(p, symbol_power(s, n) + symbol_power(inverse_symbol(s), n), empty_word()),
{
    lemma_inverse_symbol_power(s, n);   // inverse_word(sⁿ) =~= (s⁻¹)ⁿ
    lemma_word_inverse_right(p, symbol_power(s, n));   // sⁿ · inverse_word(sⁿ) ≡ ε
    assert(symbol_power(s, n) + symbol_power(inverse_symbol(s), n)
        =~= concat(symbol_power(s, n), inverse_word(symbol_power(s, n))));
}

/// **Deconjugation.**  `t⁻¹ · (t·w·t⁻¹) · t ≡ w`  (the inverse of `conj_t`).
pub proof fn lemma_deconj(p: Presentation, t_idx: nat, w: Word)
    ensures
        equiv_in_presentation(p,
            seq![Symbol::Inv(t_idx)] + conj_t(t_idx, w) + seq![Symbol::Gen(t_idx)], w),
{
    let it = seq![Symbol::Inv(t_idx)];
    let gt = seq![Symbol::Gen(t_idx)];
    let c = it + gt;   // t⁻¹ · t

    // c ≡ ε
    lemma_inv_gen_singleton(t_idx);     // inverse_word(gt) =~= it
    lemma_word_inverse_left(p, gt);     // concat(inverse_word(gt), gt) ≡ ε, i.e. c ≡ ε

    // it + conj_t(t,w) + gt =~= (c + w) + c
    assert(it + conj_t(t_idx, w) + gt =~= (c + w) + c);

    // c + w ≡ ε + w =~= w
    lemma_equiv_concat_left(p, c, empty_word(), w);
    assert(empty_word() + w =~= w);
    // (c + w) + c ≡ w + c
    lemma_equiv_concat_left(p, c + w, w, c);
    // w + c ≡ w + ε =~= w
    lemma_equiv_concat_right(p, w, c, empty_word());
    assert(w + empty_word() =~= w);
    // chain (c+w)+c ≡ w+c ≡ w
    lemma_equiv_transitive(p, (c + w) + c, w + c, w);
}

} // verus!
