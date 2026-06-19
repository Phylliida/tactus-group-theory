use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::machine_group::*;

verus! {

//  ============================================================
//  Property (ii)⊆ — structural decomposition (separate module)
//  ============================================================
//
//  This work lives in its own module so its predicate-heavy `in_residue_class`
//  goals (exists/forall triggers) don't pollute machine_group's triggers — that
//  pollution was tipping a fragile config-basis lemma (lemma_psi_A_stable_count_scales)
//  over the Lean heartbeat edge.  Builds on machine_group's signed config words,
//  index-shifts, and the residue-class predicate.

//  Shifting an index by ±m preserves its residue mod m.
pub proof fn lemma_residue_shift_x(i: int, m: int, r: int)
    requires
        m > 0,
        (r - i) % m == 0,
    ensures
        (r - m - i) % m == 0,
        (r + m - i) % m == 0,
{
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(r - i, m);  // (m + (r-i)) % m == (r-i) % m
    vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(r - i, m);  // (-m + (r-i)) % m == (r-i) % m
    assert(r + m - i == m + (r - i));
    assert(r - m - i == -m + (r - i));
}

//  Single-gen closure: conjugating a residue gen by xᵐ stays in the residue class.
//  xᵐ · t(r,s) · x⁻ᵐ ≡ t(r-m, s), and t(r-m,s) is still a residue gen (r-m ≡ i mod m).
pub proof fn lemma_conj_residue_gen_x(i: int, j: int, m: int, r: int, s: int)
    requires
        m > 0,
        (r - i) % m == 0,
        (s - j) % m == 0,
    ensures
        equiv_in_presentation(base_A(),
            signed_power(1, m) + config_word_signed(r, s) + signed_power(1, -m),
            config_word_signed(r - m, s)),
        in_residue_class(i, j, m, config_word_signed((r - m), s)),
{
    lemma_conj_config_signed_by_x(r, s, -m);   // x^m · t(r,s) · x^-m ≡ t(r-m, s)
    lemma_residue_shift_x(i, m, r);
    lemma_residue_gen_in_class(i, j, m, r - m, s);
}

//  Single-gen closure for y:  yᵐ · t(r,s) · y⁻ᵐ ≡ t(r, s-m), still a residue gen.
pub proof fn lemma_conj_residue_gen_y(i: int, j: int, m: int, r: int, s: int)
    requires
        m > 0,
        (r - i) % m == 0,
        (s - j) % m == 0,
    ensures
        equiv_in_presentation(base_A(),
            signed_power(2, m) + config_word_signed(r, s) + signed_power(2, -m),
            config_word_signed(r, s - m)),
        in_residue_class(i, j, m, config_word_signed(r, (s - m))),
{
    lemma_conj_config_signed_by_y(r, s, -m);
    lemma_residue_shift_x(j, m, s);
    lemma_residue_gen_in_class(i, j, m, r, s - m);
}

} //  verus!
