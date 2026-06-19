use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::benign::{in_generated_subgroup, factors_from_generators, is_generator_or_inverse, concat_all};

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

//  inverse_word(xᵏ) = x⁻ᵏ.
pub proof fn lemma_signed_power_inverse(i: nat, k: int)
    ensures
        inverse_word(signed_power(i, k)) =~= signed_power(i, -k),
{
    if k >= 0 {
        lemma_inverse_word_sympower(Symbol::Gen(i), k as nat);
        assert(inverse_symbol(Symbol::Gen(i)) == Symbol::Inv(i));
    } else {
        lemma_inverse_word_sympower(Symbol::Inv(i), (-k) as nat);
        assert(inverse_symbol(Symbol::Inv(i)) == Symbol::Gen(i));
    }
}

//  config_word_signed(r,s) is a valid word over A's 3 generators.
pub proof fn lemma_config_signed_valid(r: int, s: int)
    ensures
        word_valid(config_word_signed(r, s), 3),
{
    lemma_signed_power_valid(2, -s, 3);
    lemma_signed_power_valid(1, -r, 3);
    lemma_signed_power_valid(1, r, 3);
    lemma_signed_power_valid(2, s, 3);
    let t0: Word = seq![Symbol::Gen(0)];
    assert(word_valid(t0, 3)) by {
        assert forall|k: int| 0 <= k < t0.len() implies symbol_valid(#[trigger] t0[k], 3) by { }
    }
    lemma_concat_word_valid(signed_power(2, -s), signed_power(1, -r), 3);
    lemma_concat_word_valid(signed_power(2, -s) + signed_power(1, -r), t0, 3);
    lemma_concat_word_valid(signed_power(2, -s) + signed_power(1, -r) + t0, signed_power(1, r), 3);
    lemma_concat_word_valid(signed_power(2, -s) + signed_power(1, -r) + t0 + signed_power(1, r),
        signed_power(2, s), 3);
}

//  inverse_word(t(r,s)) · xᵏ ≡ xᵏ · inverse_word(t(r+k, s)).  (from config_move_x at (r+k,s,-k))
pub proof fn lemma_config_inv_move_x(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            inverse_word(config_word_signed(r, s)) + signed_power(1, k),
            signed_power(1, k) + inverse_word(config_word_signed(r + k, s))),
{
    let p = base_A();
    lemma_base_A_valid();
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r + k, s);
    let xnk = signed_power(1, -k);
    //  t(r+k,s)·x⁻ᵏ ≡ x⁻ᵏ·t(r,s)
    lemma_config_move_x(r + k, s, -k);
    //  validity for inversion
    lemma_config_signed_valid(r, s);
    lemma_config_signed_valid(r + k, s);
    lemma_signed_power_valid(1, -k, 3);
    lemma_concat_word_valid(cwk, xnk, 3);
    lemma_concat_word_valid(xnk, cw, 3);
    crate::normal_form_afp_textbook::lemma_equiv_inverse(p, cwk + xnk, xnk + cw);
    //  compute the two inverses
    lemma_inverse_word_concat(cwk, xnk);
    lemma_inverse_word_concat(xnk, cw);
    lemma_signed_power_inverse(1, -k);                      // inverse_word(x⁻ᵏ) =~= xᵏ
    assert(inverse_word(cwk + xnk) =~= signed_power(1, k) + inverse_word(cwk));
    assert(inverse_word(xnk + cw) =~= inverse_word(cw) + signed_power(1, k));
    lemma_inverse_word_valid(cwk, 3);
    lemma_signed_power_valid(1, k, 3);
    lemma_concat_word_valid(signed_power(1, k), inverse_word(cwk), 3);
    lemma_equiv_symmetric(p, signed_power(1, k) + inverse_word(cwk), inverse_word(cw) + signed_power(1, k));
}

//  inverse_word(t(r,s)) · yᵏ ≡ yᵏ · inverse_word(t(r, s+k)).
pub proof fn lemma_config_inv_move_y(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            inverse_word(config_word_signed(r, s)) + signed_power(2, k),
            signed_power(2, k) + inverse_word(config_word_signed(r, s + k))),
{
    let p = base_A();
    lemma_base_A_valid();
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r, s + k);
    let ynk = signed_power(2, -k);
    lemma_config_move_y(r, s + k, -k);
    lemma_config_signed_valid(r, s);
    lemma_config_signed_valid(r, s + k);
    lemma_signed_power_valid(2, -k, 3);
    lemma_concat_word_valid(cwk, ynk, 3);
    lemma_concat_word_valid(ynk, cw, 3);
    crate::normal_form_afp_textbook::lemma_equiv_inverse(p, cwk + ynk, ynk + cw);
    lemma_inverse_word_concat(cwk, ynk);
    lemma_inverse_word_concat(ynk, cw);
    lemma_signed_power_inverse(2, -k);
    assert(inverse_word(cwk + ynk) =~= signed_power(2, k) + inverse_word(cwk));
    assert(inverse_word(ynk + cw) =~= inverse_word(cw) + signed_power(2, k));
    lemma_inverse_word_valid(cwk, 3);
    lemma_signed_power_valid(2, k, 3);
    lemma_concat_word_valid(signed_power(2, k), inverse_word(cwk), 3);
    lemma_equiv_symmetric(p, signed_power(2, k) + inverse_word(cwk), inverse_word(cw) + signed_power(2, k));
}

//  inverse_word(t(r,s)) · xᵃ · yᵇ ≡ xᵃ · yᵇ · inverse_word(t(r+a, s+b)).
pub proof fn lemma_config_inv_move_xy(r: int, s: int, aa: int, bb: int)
    ensures
        equiv_in_presentation(base_A(),
            inverse_word(config_word_signed(r, s)) + signed_power(1, aa) + signed_power(2, bb),
            signed_power(1, aa) + signed_power(2, bb) + inverse_word(config_word_signed(r + aa, s + bb))),
{
    let p = base_A();
    lemma_base_A_valid();
    let xa = signed_power(1, aa);
    let yb = signed_power(2, bb);
    let icw = inverse_word(config_word_signed(r, s));
    let icwa = inverse_word(config_word_signed(r + aa, s));
    let icwab = inverse_word(config_word_signed(r + aa, s + bb));
    lemma_config_inv_move_x(r, s, aa);                      // icw·xa ≡ xa·icwa
    lemma_equiv_concat_left(p, icw + xa, xa + icwa, yb);
    lemma_config_inv_move_y(r + aa, s, bb);                 // icwa·yb ≡ yb·icwab
    lemma_equiv_concat_right(p, xa, icwa + yb, yb + icwab);
    assert((icw + xa) + yb =~= icw + xa + yb);
    assert((xa + icwa) + yb =~= xa + (icwa + yb));
    assert(xa + (yb + icwab) =~= xa + yb + icwab);
    lemma_equiv_transitive(p, icw + xa + yb, xa + (icwa + yb), xa + (yb + icwab));
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

//  ============================================================
//  Decomposition induction — per-factor step helpers.
//  ============================================================
//
//  Each takes the IH normal form  rest ≡ x^{aa·m}·y^{bb·m}·u  (u in the residue class)
//  and produces the normal form for  factor·rest.

//  The normal form is parameterized by the actual x,y EXPONENTS (ax, by), each a multiple of m.
//  Each step helper RETURNS the new (u, ax, by) tuple (ghost return — no existential triggers).

//  Prepend x^{de·m} (de = ±1 for the xᵐ / x⁻ᵐ factor): merges into the x-exponent.
pub proof fn lemma_step_x(i: nat, j: nat, m: nat, de: int, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), signed_power(1, de * m) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let xdm = signed_power(1, de * m);
    let xam = signed_power(1, ax);
    let ybm = signed_power(2, by);
    let nf = xam + ybm + u;
    lemma_equiv_concat_right(p, xdm, rest, nf);                  // xdm·rest ≡ xdm·nf
    lemma_signed_power_add(p, 1, de * m, ax);                    // xdm·xam ≡ x^{de·m+ax}
    let xsum = signed_power(1, de * m + ax);
    lemma_equiv_concat_left(p, xdm + xam, xsum, ybm + u);
    assert(xdm + nf =~= (xdm + xam) + (ybm + u));
    assert(xsum + (ybm + u) =~= xsum + ybm + u);
    lemma_equiv_transitive(p, xdm + rest, (xdm + xam) + (ybm + u), xsum + ybm + u);
    //  (de·m + ax) % m == 0
    assert(de * m + ax == (m as int) * de + ax) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(de, ax, m as int);  // (m·de+ax)%m == ax%m
    (u, de * m + ax, by)
}

//  Prepend y^{de·m} (de = ±1): commute past the x-exponent, then merge into the y-exponent.
pub proof fn lemma_step_y(i: nat, j: nat, m: nat, de: int, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), signed_power(2, de * m) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let ydm = signed_power(2, de * m);
    let xax = signed_power(1, ax);
    let yby = signed_power(2, by);
    let ysum = signed_power(2, de * m + by);
    let nf = xax + yby + u;
    lemma_equiv_concat_right(p, ydm, rest, nf);                  // ydm·rest ≡ ydm·nf
    //  commute ydm past xax
    lemma_signed_xy_commute(ax, de * m);                          // xax·ydm ≡ ydm·xax
    lemma_signed_power_valid(1, ax, 3);
    lemma_signed_power_valid(2, de * m, 3);
    lemma_concat_word_valid(xax, ydm, 3);
    lemma_equiv_symmetric(p, xax + ydm, ydm + xax);              // ydm·xax ≡ xax·ydm
    lemma_equiv_concat_left(p, ydm + xax, xax + ydm, yby + u);
    //  merge ydm·yby → ysum
    lemma_signed_power_add(p, 2, de * m, by);                    // ydm·yby ≡ ysum
    lemma_equiv_concat_left(p, ydm + yby, ysum, u);
    lemma_equiv_concat_right(p, xax, (ydm + yby) + u, ysum + u);
    assert(ydm + nf =~= (ydm + xax) + (yby + u));
    assert((xax + ydm) + (yby + u) =~= xax + ((ydm + yby) + u));
    assert(xax + (ysum + u) =~= xax + ysum + u);
    lemma_equiv_transitive(p, ydm + rest, (ydm + xax) + (yby + u), xax + ((ydm + yby) + u));
    lemma_equiv_transitive(p, ydm + rest, xax + ((ydm + yby) + u), xax + ysum + u);
    assert(de * m + by == (m as int) * de + by) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(de, by, m as int);
    (u, ax, de * m + by)
}

//  Prepend the config gen t(i,j): slide it right past x^{ax}·y^{by} (shifting to t(i+ax,j+by),
//  still a residue gen since ax,by ≡ 0 mod m) and absorb into u.
pub proof fn lemma_step_config(i: nat, j: nat, m: nat, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), config_word(i, j) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let cw = config_word(i, j);
    let cws = config_word_signed(i as int, j as int);
    let xax = signed_power(1, ax);
    let yby = signed_power(2, by);
    let cwshift = config_word_signed(i as int + ax, j as int + by);
    let u2 = cwshift + u;
    let nf = xax + yby + u;
    lemma_config_signed_matches_nat(i, j);                       // cws =~= cw
    lemma_equiv_concat_right(p, cw, rest, nf);                   // cw·rest ≡ cw·nf
    lemma_config_move_xy(i as int, j as int, ax, by);           // cws·xax·yby ≡ xax·yby·cwshift
    lemma_equiv_concat_left(p, cws + xax + yby, xax + yby + cwshift, u);
    assert(cw == cws);
    assert(cw + nf =~= (cws + xax + yby) + u);
    assert((xax + yby + cwshift) + u =~= xax + yby + u2);
    lemma_equiv_transitive(p, cw + rest, (cws + xax + yby) + u, (xax + yby + cwshift) + u);
    //  residue class:  cwshift is a residue gen, product with u
    lemma_residue_gen_in_class(i as int, j as int, m as int, i as int + ax, j as int + by);
    lemma_product_in_subgroup_pred(p, residue_pred(i as int, j as int, m as int), cwshift, u);
    (u2, ax, by)
}

//  Prepend the inverse config gen t(i,j)⁻¹: same as config, with the inverse move and inverse residue gen.
pub proof fn lemma_step_inv_config(i: nat, j: nat, m: nat, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), inverse_word(config_word(i, j)) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let icw = inverse_word(config_word(i, j));
    let icws = inverse_word(config_word_signed(i as int, j as int));
    let xax = signed_power(1, ax);
    let yby = signed_power(2, by);
    let icwshift = inverse_word(config_word_signed(i as int + ax, j as int + by));
    let u2 = icwshift + u;
    let nf = xax + yby + u;
    lemma_config_signed_matches_nat(i, j);
    lemma_equiv_concat_right(p, icw, rest, nf);
    lemma_config_inv_move_xy(i as int, j as int, ax, by);       // icws·xax·yby ≡ xax·yby·icwshift
    lemma_equiv_concat_left(p, icws + xax + yby, xax + yby + icwshift, u);
    assert(icw == icws);
    assert(icw + nf =~= (icws + xax + yby) + u);
    assert((xax + yby + icwshift) + u =~= xax + yby + u2);
    lemma_equiv_transitive(p, icw + rest, (icws + xax + yby) + u, (xax + yby + icwshift) + u);
    //  icwshift is an (inverse) residue gen
    assert(is_residue_gen(i as int, j as int, m as int, icwshift)) by {
        assert((i as int + ax - i as int) % (m as int) == 0);
        assert((j as int + by - j as int) % (m as int) == 0);
        assert(icwshift == inverse_word(config_word_signed(i as int + ax, j as int + by)));
    }
    assert(residue_pred(i as int, j as int, m as int)(icwshift) == is_residue_gen(i as int, j as int, m as int, icwshift));
    lemma_gen_in_subgroup_pred(p, residue_pred(i as int, j as int, m as int), icwshift);
    lemma_product_in_subgroup_pred(p, residue_pred(i as int, j as int, m as int), icwshift, u);
    (u2, ax, by)
}

//  ============================================================
//  THE STRUCTURAL DECOMPOSITION (the main induction).
//  ============================================================
//
//  Any product of t(i,j), xᵐ, yᵐ (and inverses) equals  x^{ax}·y^{by}·u  with ax,by ≡ 0 (mod m)
//  and u ∈ ⟨t(r,s) : r≡i, s≡j (mod m)⟩.  Induction on the factor sequence; prepend each factor.
pub proof fn lemma_decompose_factors(i: nat, j: nat, m: nat, factors: Seq<Word>) -> (res: (Word, int, int))
    requires
        m > 0,
        factors_from_generators(
            seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)], factors),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), concat_all(factors),
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
    decreases factors.len(),
{
    let p = base_A();
    lemma_base_A_valid();
    let gens = seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)];
    let pred = residue_pred(i as int, j as int, m as int);
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
        assert(in_subgroup_pred(p, pred, empty_word())) by {
            assert(factors_from_pred(pred, Seq::<Word>::empty()));
            assert(concat_all(Seq::<Word>::empty()) =~= empty_word());
            lemma_equiv_refl(p, empty_word());
        }
        assert(signed_power(1, 0) =~= empty_word());
        assert(signed_power(2, 0) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
        assert(concat_all(factors) =~= signed_power(1, 0) + signed_power(2, 0) + empty_word());
        (empty_word(), 0, 0)
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies is_generator_or_inverse(gens, #[trigger] rest[k]) by {
                assert(rest[k] == factors[k + 1]);
            }
        }
        assert(is_generator_or_inverse(gens, first)) by { assert(first == factors[0]); }
        let ih = lemma_decompose_factors(i, j, m, rest);
        let u2 = ih.0; let ax2 = ih.1; let by2 = ih.2;
        let cr = concat_all(rest);
        assert(concat_all(factors) =~= concat(first, cr));
        let jj = choose|jj: int| 0 <= jj < gens.len() && (first == gens[jj] || first == inverse_word(gens[jj]));
        assert(0 <= jj < 3 && (first == gens[jj] || first == inverse_word(gens[jj])));
        if jj == 0 {
            if first == gens[0] {
                assert(first == config_word(i, j));
                let r = lemma_step_config(i, j, m, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= config_word(i, j) + cr);
                r
            } else {
                lemma_step_inv_config(i, j, m, ax2, by2, u2, cr)
            }
        } else if jj == 1 {
            if first == gens[1] {
                assert(first == signed_power(1, 1 * (m as int)));
                let r = lemma_step_x(i, j, m, 1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(1, 1 * (m as int)) + cr);
                r
            } else {
                lemma_signed_power_inverse(1, m as int);       // inverse_word(xᵐ) =~= x⁻ᵐ
                assert(first == signed_power(1, -1 * (m as int)));
                let r = lemma_step_x(i, j, m, -1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(1, -1 * (m as int)) + cr);
                r
            }
        } else {
            if first == gens[2] {
                assert(first == signed_power(2, 1 * (m as int)));
                let r = lemma_step_y(i, j, m, 1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(2, 1 * (m as int)) + cr);
                r
            } else {
                lemma_signed_power_inverse(2, m as int);
                assert(first == signed_power(2, -1 * (m as int)));
                let r = lemma_step_y(i, j, m, -1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(2, -1 * (m as int)) + cr);
                r
            }
        }
    }
}

} //  verus!
