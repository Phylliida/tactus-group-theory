use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;

verus! {

//  ============================================================
//  Move lemmas: slide a config word past an x/y power (index-shift, rearranged).
//  ============================================================

//  t(r,s) · xᵏ ≡ xᵏ · t(r+k, s).
pub proof fn lemma_config_move_x(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            config_word_signed(r, s) + signed_power(1, k),
            signed_power(1, k) + config_word_signed(r + k, s)),
{
    let p = base_A();
    lemma_base_A_valid();
    let xk = signed_power(1, k);
    let xnk = signed_power(1, -k);
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r + k, s);
    lemma_conj_config_signed_by_x(r, s, k);                 // x⁻ᵏ·cw·xᵏ ≡ cwk
    lemma_equiv_symmetric(p, xnk + cw + xk, cwk);            // cwk ≡ x⁻ᵏ·cw·xᵏ
    lemma_equiv_concat_right(p, xk, cwk, xnk + cw + xk);     // xᵏ·cwk ≡ xᵏ·(x⁻ᵏ·cw·xᵏ)
    lemma_signed_power_add(p, 1, k, -k);                     // xᵏ·x⁻ᵏ ≡ x⁰
    assert(signed_power(1, 0) =~= empty_word());
    assert(equiv_in_presentation(p, xk + xnk, empty_word()));
    crate::britton_via_tower::lemma_delete_equiv_empty(p, empty_word(), xk + xnk, cw + xk);
    assert(xk + cwk =~= xk + cwk);
    assert(xk + (xnk + cw + xk) =~= (xk + xnk) + (cw + xk));
    assert(empty_word() + (xk + xnk) + (cw + xk) =~= (xk + xnk) + (cw + xk));
    assert(empty_word() + (cw + xk) =~= cw + xk);
    lemma_equiv_transitive(p, xk + cwk, (xk + xnk) + (cw + xk), cw + xk);
    lemma_equiv_symmetric(p, xk + cwk, cw + xk);
}

//  t(r,s) · yᵏ ≡ yᵏ · t(r, s+k).
pub proof fn lemma_config_move_y(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            config_word_signed(r, s) + signed_power(2, k),
            signed_power(2, k) + config_word_signed(r, s + k)),
{
    let p = base_A();
    lemma_base_A_valid();
    let yk = signed_power(2, k);
    let ynk = signed_power(2, -k);
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r, s + k);
    lemma_conj_config_signed_by_y(r, s, k);
    lemma_equiv_symmetric(p, ynk + cw + yk, cwk);
    lemma_equiv_concat_right(p, yk, cwk, ynk + cw + yk);
    lemma_signed_power_add(p, 2, k, -k);
    assert(signed_power(2, 0) =~= empty_word());
    assert(equiv_in_presentation(p, yk + ynk, empty_word()));
    crate::britton_via_tower::lemma_delete_equiv_empty(p, empty_word(), yk + ynk, cw + yk);
    assert(yk + (ynk + cw + yk) =~= (yk + ynk) + (cw + yk));
    assert(empty_word() + (yk + ynk) + (cw + yk) =~= (yk + ynk) + (cw + yk));
    assert(empty_word() + (cw + yk) =~= cw + yk);
    lemma_equiv_transitive(p, yk + cwk, (yk + ynk) + (cw + yk), cw + yk);
    lemma_equiv_symmetric(p, yk + cwk, cw + yk);
}

//  t(r,s) · xᵃ · yᵇ ≡ xᵃ · yᵇ · t(r+a, s+b).
pub proof fn lemma_config_move_xy(r: int, s: int, aa: int, bb: int)
    ensures
        equiv_in_presentation(base_A(),
            config_word_signed(r, s) + signed_power(1, aa) + signed_power(2, bb),
            signed_power(1, aa) + signed_power(2, bb) + config_word_signed(r + aa, s + bb)),
{
    let p = base_A();
    lemma_base_A_valid();
    let xa = signed_power(1, aa);
    let yb = signed_power(2, bb);
    let cw = config_word_signed(r, s);
    let cwa = config_word_signed(r + aa, s);
    let cwab = config_word_signed(r + aa, s + bb);
    lemma_config_move_x(r, s, aa);                          // cw·xa ≡ xa·cwa
    lemma_equiv_concat_left(p, cw + xa, xa + cwa, yb);      // (cw·xa)·yb ≡ (xa·cwa)·yb
    lemma_config_move_y(r + aa, s, bb);                     // cwa·yb ≡ yb·cwab
    lemma_equiv_concat_right(p, xa, cwa + yb, yb + cwab);   // xa·(cwa·yb) ≡ xa·(yb·cwab)
    assert((cw + xa) + yb =~= cw + xa + yb);
    assert((xa + cwa) + yb =~= xa + (cwa + yb));
    assert(xa + (yb + cwab) =~= xa + yb + cwab);
    lemma_equiv_transitive(p, cw + xa + yb, xa + (cwa + yb), xa + (yb + cwab));
}

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
