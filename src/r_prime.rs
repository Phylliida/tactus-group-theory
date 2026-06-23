// Layer 2 — Brick 5, C3.2c / map_b forward — the (R') canw index-tracking core.
//
// (R')  emb(φ_F, u) ∈ ⟨config_emb(bet)⟩_{free(n+3)}  ⟹  emb(φ_F, u) ∈ ⟨config_emb(σ(bet))⟩,
//        σ(β) = m·β + l,  under σ-backward-saturation  ∀β. (mβ+l)∈bet ⟹ β∈bet.
//
// This is the irreducible "Image(φ_F) ∩ ⟨t,x⟩ = config-products with conjugating indices ≡ l (mod m)"
// fact.  Route = canw coordinate-tracking (this file), reusing config_reduce's coordinate-survival
// crux `lemma_tfree_coord_restrict` + `lemma_canw_eval_nontrivial`.  See docs/brick5-c3.2c-plan.md §7.
//
// CENTERPIECE (this chunk): the coordinate-tracking invariant.  `phi_prime = π∘φ_F = [config(l,0),
// xᵐ, ε, …, ε]` (the d,b-killed φ_F image family); reading its embedding symbol-by-symbol gives a
// canw `phi_canon_acc(u, E)` (running x-exponent E) every letter of which sits at a coordinate
// `l − m·E ≡ l (mod m)`:
//
//   signed_power(1, m·E) + emb(φ', u)  ≡_p  canw_eval(phi_canon_acc(u, E)) + signed_power(1, m·(E + xexp(u)))
//
// (xexp(u) = gexp(1, u)).  At E=0 this reads emb(φ', u) as a config-product-over-σ(ℤ) up to a trailing
// x-power that the membership later forces to vanish.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::{Presentation, presentation_valid, equiv_in_presentation, lemma_equiv_refl,
    lemma_equiv_symmetric, lemma_equiv_transitive};
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_equiv_concat_right};
use crate::machine_group::{config_word, symbol_power, signed_power, gsconfig, CanonLetter,
    canl_eval, canw_eval, gexp, sym_exp, lemma_signed_power_add, lemma_signed_power_valid,
    lemma_inverse_word_concat, lemma_gexp_concat, lemma_gexp_signed_power};
use crate::ii_subset::lemma_signed_power_inverse;
use crate::benign::{apply_embedding, apply_embedding_symbol};
use crate::config_reduce::lemma_canw_eval_concat;
use crate::phi_l_mapb::sigma_betas;

verus! {

// ----------------------------------------------------------------------------
// φ' = π∘φ_F — the d,b-killed image family `[config(l,0), xᵐ, ε, …, ε]` (length n+3).
// ----------------------------------------------------------------------------

pub open spec fn phi_prime(n: nat, m: nat, l: nat) -> Seq<Word> {
    Seq::new((n + 3) as nat, |g: int| {
        if g == 0 {
            config_word(l, 0)
        } else if g == 1 {
            symbol_power(Symbol::Gen(1), m)
        } else {
            empty_word()
        }
    })
}

// ----------------------------------------------------------------------------
// phi_canon_acc — the canw reading of `emb(φ', u)`, threading the running x-exponent `xe`.
//   t (Gen0)  ↦ prepend the config letter {l − m·xe, 0, +1}
//   Inv0      ↦ prepend {l − m·xe, 0, −1}
//   x (Gen1)  ↦ recurse with xe+1     Inv1 ↦ recurse with xe−1
//   d,b (≥2)  ↦ recurse with xe       (φ' kills these to ε)
// ----------------------------------------------------------------------------

pub open spec fn phi_canon_acc(l: nat, m: nat, u: Word, xe: int) -> Seq<CanonLetter>
    decreases u.len(),
{
    if u.len() == 0 {
        Seq::<CanonLetter>::empty()
    } else {
        let head = u[0];
        let rest = u.drop_first();
        let coord = (l as int) - (m as int) * xe;
        match head {
            Symbol::Gen(i) =>
                if i == 0 {
                    seq![CanonLetter { r: coord, s: 0, e: 1 }] + phi_canon_acc(l, m, rest, xe)
                } else if i == 1 {
                    phi_canon_acc(l, m, rest, xe + 1)
                } else {
                    phi_canon_acc(l, m, rest, xe)
                },
            Symbol::Inv(i) =>
                if i == 0 {
                    seq![CanonLetter { r: coord, s: 0, e: -1 }] + phi_canon_acc(l, m, rest, xe)
                } else if i == 1 {
                    phi_canon_acc(l, m, rest, xe - 1)
                } else {
                    phi_canon_acc(l, m, rest, xe)
                },
        }
    }
}

// ----------------------------------------------------------------------------
// Word-form helpers — strip the s=0 empties from config_word / gsconfig.
// ----------------------------------------------------------------------------

/// `config_word(l,0) = x⁻ˡ · t · xˡ` in signed-power form (the y-powers vanish at s=0).
pub proof fn lemma_config_word_zero_form(l: nat)
    ensures
        config_word(l, 0)
            =~= signed_power(1, -(l as int)) + seq![Symbol::Gen(0)] + signed_power(1, l as int),
{
    // config_word(l,0) = symbol_power(Inv2,0) + symbol_power(Inv1,l) + [Gen0]
    //                    + symbol_power(Gen1,l) + symbol_power(Gen2,0).
    assert(symbol_power(Symbol::Inv(2), 0) =~= empty_word());
    assert(symbol_power(Symbol::Gen(2), 0) =~= empty_word());
    assert(symbol_power(Symbol::Inv(1), l) =~= signed_power(1, -(l as int)));
    assert(symbol_power(Symbol::Gen(1), l) =~= signed_power(1, l as int));
}

/// `gsconfig(r,0,e) = x⁻ʳ · t^e · xʳ` in signed-power form (the y-powers vanish at s=0).
pub proof fn lemma_gsconfig_zero_form(r: int, e: int)
    ensures
        gsconfig(r, 0, e) =~= signed_power(1, -r) + signed_power(0, e) + signed_power(1, r),
{
    // gsconfig(r,0,e) = signed_power(2,0) + signed_power(1,-r) + signed_power(0,e)
    //                   + signed_power(1,r) + signed_power(2,0).
    assert(signed_power(2, 0) =~= empty_word());
}

/// `inverse_word(config_word(l,0)) = x⁻ˡ · t⁻¹ · xˡ` in signed-power form.
pub proof fn lemma_config_word_inv_form(l: nat)
    ensures
        inverse_word(config_word(l, 0))
            =~= signed_power(1, -(l as int)) + seq![Symbol::Inv(0)] + signed_power(1, l as int),
{
    let li = l as int;
    let g0: Word = seq![Symbol::Gen(0)];
    let ab: Word = signed_power(1, -li) + g0;
    lemma_config_word_zero_form(l);     // config_word(l,0) =~= (sp(-l) + [Gen0]) + sp(l) = ab + sp(l)
    assert(config_word(l, 0) =~= ab + signed_power(1, li));
    // inverse_word(ab + sp(l)) =~= inverse_word(sp(l)) + inverse_word(ab)
    lemma_inverse_word_concat(ab, signed_power(1, li));
    lemma_signed_power_inverse(1, li);      // inv(sp(l))  = sp(-l)
    // inverse_word(ab) = inverse_word(sp(-l) + [Gen0]) =~= inverse_word([Gen0]) + inverse_word(sp(-l))
    lemma_inverse_word_concat(signed_power(1, -li), g0);
    lemma_signed_power_inverse(1, -li);     // inv(sp(-l)) = sp(l)
    assert(inverse_word(g0) =~= seq![Symbol::Inv(0)]) by { reveal_with_fuel(inverse_word, 2); }
    assert(inverse_word(ab) =~= seq![Symbol::Inv(0)] + signed_power(1, li));
    assert(inverse_word(config_word(l, 0))
        =~= signed_power(1, -li) + (seq![Symbol::Inv(0)] + signed_power(1, li)));
}

// ----------------------------------------------------------------------------
// The per-step "absorb" atoms — push a running x-power through one config / x / ε image.
// ----------------------------------------------------------------------------

/// **x-conjugation absorb (generic over the middle symbol)**:
///   `xᵏ · (x⁻ˡ · mid · xˡ)  ≡  (x^{k−l} · mid · x^{l−k}) · xᵏ`.
/// Both sides reduce to `x^{k−l} · mid · xˡ`; the `≡` is two `lemma_signed_power_add`'s + one
/// `lemma_equiv_symmetric` (whence the `presentation_valid` / `symbol_valid` hypotheses).
pub proof fn lemma_xconj_absorb(p: Presentation, mid: Symbol, li: int, k: int)
    requires
        presentation_valid(p),
        p.num_generators >= 2,
        symbol_valid(mid, p.num_generators),
    ensures
        equiv_in_presentation(p,
            signed_power(1, k) + (signed_power(1, -li) + seq![mid] + signed_power(1, li)),
            (signed_power(1, k - li) + seq![mid] + signed_power(1, li - k)) + signed_power(1, k)),
{
    let ms: Word = seq![mid];
    let mw: Word = signed_power(1, k - li) + ms + signed_power(1, li);
    let lhs = signed_power(1, k) + (signed_power(1, -li) + ms + signed_power(1, li));
    let rhs = (signed_power(1, k - li) + ms + signed_power(1, li - k)) + signed_power(1, k);

    // --- LHS ≡ mw ---
    assert(lhs =~= (signed_power(1, k) + signed_power(1, -li)) + ms + signed_power(1, li));
    lemma_signed_power_add(p, 1, k, -li);      // sp(k)+sp(-l) ≡ sp(k-l)
    lemma_equiv_concat_left(p, signed_power(1, k) + signed_power(1, -li), signed_power(1, k - li),
        ms + signed_power(1, li));
    assert((signed_power(1, k) + signed_power(1, -li)) + (ms + signed_power(1, li))
        =~= lhs);
    assert(signed_power(1, k - li) + (ms + signed_power(1, li)) =~= mw);
    assert(equiv_in_presentation(p, lhs, mw));

    // --- RHS ≡ mw ---
    assert(rhs =~= (signed_power(1, k - li) + ms) + (signed_power(1, li - k) + signed_power(1, k)));
    lemma_signed_power_add(p, 1, li - k, k);   // sp(l-k)+sp(k) ≡ sp(l)
    lemma_equiv_concat_right(p, signed_power(1, k - li) + ms,
        signed_power(1, li - k) + signed_power(1, k), signed_power(1, li));
    assert((signed_power(1, k - li) + ms) + signed_power(1, li) =~= mw);
    assert(equiv_in_presentation(p, rhs, mw));

    // --- LHS ≡ RHS via symmetric(rhs, mw) + transitive ---
    assert(word_valid(rhs, p.num_generators)) by {
        lemma_signed_power_valid(1, k - li, p.num_generators);
        lemma_signed_power_valid(1, li - k, p.num_generators);
        lemma_signed_power_valid(1, k, p.num_generators);
        assert(word_valid(ms, p.num_generators)) by { assert(ms[0] == mid); }
        lemma_concat_word_valid(signed_power(1, k - li), ms, p.num_generators);
        lemma_concat_word_valid(signed_power(1, k - li) + ms, signed_power(1, li - k),
            p.num_generators);
        lemma_concat_word_valid(signed_power(1, k - li) + ms + signed_power(1, li - k),
            signed_power(1, k), p.num_generators);
    }
    lemma_equiv_symmetric(p, rhs, mw);
    lemma_equiv_transitive(p, lhs, mw, rhs);
}

/// **t-absorb**: `xᵏ · config(l,0)  ≡  gsconfig(l−k, 0, 1) · xᵏ`.
pub proof fn lemma_t_absorb(p: Presentation, l: nat, k: int)
    requires
        presentation_valid(p),
        p.num_generators >= 3,
    ensures
        equiv_in_presentation(p,
            signed_power(1, k) + config_word(l, 0),
            gsconfig((l as int) - k, 0, 1) + signed_power(1, k)),
{
    let li = l as int;
    let g0: Word = seq![Symbol::Gen(0)];
    lemma_config_word_zero_form(l);
    lemma_gsconfig_zero_form(li - k, 1);
    assert(signed_power(0, 1) =~= g0);
    assert(symbol_valid(Symbol::Gen(0), p.num_generators));
    lemma_xconj_absorb(p, Symbol::Gen(0), li, k);
    // rewrite the absorb endpoints into config_word / gsconfig form.
    assert(signed_power(1, k) + config_word(l, 0)
        =~= signed_power(1, k) + (signed_power(1, -li) + g0 + signed_power(1, li)));
    assert(gsconfig(li - k, 0, 1) + signed_power(1, k)
        =~= (signed_power(1, k - li) + g0 + signed_power(1, li - k)) + signed_power(1, k));
}

/// **t⁻¹-absorb**: `xᵏ · config(l,0)⁻¹  ≡  gsconfig(l−k, 0, −1) · xᵏ`.
pub proof fn lemma_tinv_absorb(p: Presentation, l: nat, k: int)
    requires
        presentation_valid(p),
        p.num_generators >= 3,
    ensures
        equiv_in_presentation(p,
            signed_power(1, k) + inverse_word(config_word(l, 0)),
            gsconfig((l as int) - k, 0, -1) + signed_power(1, k)),
{
    let li = l as int;
    let i0: Word = seq![Symbol::Inv(0)];
    lemma_config_word_inv_form(l);
    lemma_gsconfig_zero_form(li - k, -1);
    assert(signed_power(0, -1) =~= i0);
    assert(symbol_valid(Symbol::Inv(0), p.num_generators));
    lemma_xconj_absorb(p, Symbol::Inv(0), li, k);
    assert(signed_power(1, k) + inverse_word(config_word(l, 0))
        =~= signed_power(1, k) + (signed_power(1, -li) + i0 + signed_power(1, li)));
    assert(gsconfig(li - k, 0, -1) + signed_power(1, k)
        =~= (signed_power(1, k - li) + i0 + signed_power(1, li - k)) + signed_power(1, k));
}

// ----------------------------------------------------------------------------
// phi_head — the canw prefix `phi_canon_acc` prepends for one symbol.
// ----------------------------------------------------------------------------

pub open spec fn phi_head(l: nat, m: nat, s: Symbol, xe: int) -> Seq<CanonLetter> {
    let coord = (l as int) - (m as int) * xe;
    if s == Symbol::Gen(0) {
        seq![CanonLetter { r: coord, s: 0, e: 1 }]
    } else if s == Symbol::Inv(0) {
        seq![CanonLetter { r: coord, s: 0, e: -1 }]
    } else {
        Seq::<CanonLetter>::empty()
    }
}

/// `phi_canon_acc(u, xe)` unfolds one symbol: prepend `phi_head(u[0], xe)`, recurse with the
/// x-exponent shifted by `sym_exp(1, u[0])` (the x-image of `u[0]`).
pub proof fn lemma_phi_canon_acc_unfold(l: nat, m: nat, u: Word, xe: int)
    requires
        u.len() >= 1,
    ensures
        phi_canon_acc(l, m, u, xe)
            =~= phi_head(l, m, u[0], xe)
                + phi_canon_acc(l, m, u.drop_first(), xe + sym_exp(1, u[0])),
{
    let s = u[0];
    let rest = u.drop_first();
    match s {
        Symbol::Gen(i) => {
            if i == 0 {
                assert(sym_exp(1, s) == 0);
            } else if i == 1 {
                assert(phi_head(l, m, s, xe) =~= Seq::<CanonLetter>::empty());
                assert(sym_exp(1, s) == 1);
            } else {
                assert(phi_head(l, m, s, xe) =~= Seq::<CanonLetter>::empty());
                assert(sym_exp(1, s) == 0);
            }
        },
        Symbol::Inv(i) => {
            if i == 0 {
                assert(sym_exp(1, s) == 0);
            } else if i == 1 {
                assert(phi_head(l, m, s, xe) =~= Seq::<CanonLetter>::empty());
                assert(sym_exp(1, s) == -1);
            } else {
                assert(phi_head(l, m, s, xe) =~= Seq::<CanonLetter>::empty());
                assert(sym_exp(1, s) == 0);
            }
        },
    }
}

/// canw_eval of a single letter.
proof fn lemma_canw_eval_single(c: CanonLetter)
    ensures
        canw_eval(seq![c]) =~= canl_eval(c),
{
    let w: Seq<CanonLetter> = seq![c];
    assert(w.len() == 1 && w[0] == c);
    assert(w.drop_first() =~= Seq::<CanonLetter>::empty());
    assert(canw_eval(w) =~= canl_eval(c) + canw_eval(w.drop_first()));
    assert(canw_eval(w.drop_first()) =~= empty_word());
    lemma_concat_empty_right(canl_eval(c));
}

// ----------------------------------------------------------------------------
// The per-step lemma — push `xᵐ·ˣᵉ` through one φ' image, producing the canw head.
// ----------------------------------------------------------------------------

/// **Per-step**: `x^{m·xe} · φ'(s) ≡ canw_eval(phi_head(s, xe)) · x^{m·(xe + sym_exp(1,s))}`.
/// Six cases: t/t⁻¹ (the absorb atoms), x/x⁻¹ (signed-power merge), d,b (image ε).
pub proof fn lemma_phi_step(p: Presentation, n: nat, m: nat, l: nat, s: Symbol, xe: int)
    requires
        presentation_valid(p),
        p.num_generators >= 3,
        symbol_valid(s, (n + 3) as nat),
    ensures
        equiv_in_presentation(p,
            signed_power(1, (m as int) * xe) + apply_embedding_symbol(phi_prime(n, m, l), s),
            canw_eval(phi_head(l, m, s, xe))
                + signed_power(1, (m as int) * (xe + sym_exp(1, s)))),
{
    let M = m as int;
    let k = M * xe;
    let pp = phi_prime(n, m, l);
    let img = apply_embedding_symbol(pp, s);
    let head_v = canw_eval(phi_head(l, m, s, xe));
    let trail = signed_power(1, M * (xe + sym_exp(1, s)));
    let coord = (l as int) - k;

    match s {
        Symbol::Gen(i) => {
            if i == 0 {
                // img = config(l,0); head_v = gsconfig(coord,0,1); de=0 ⟹ trail = x^k.
                assert(img == pp[0] && pp[0] == config_word(l, 0));
                lemma_canw_eval_single(CanonLetter { r: coord, s: 0, e: 1 });
                assert(head_v =~= gsconfig(coord, 0, 1));
                assert(sym_exp(1, s) == 0 && trail == signed_power(1, k));
                lemma_t_absorb(p, l, k);
            } else if i == 1 {
                // img = xᵐ; head_v = ε; de=1 ⟹ trail = x^{m(xe+1)}.
                assert(img == pp[1] && pp[1] == symbol_power(Symbol::Gen(1), m));
                assert(img =~= signed_power(1, M));
                assert(head_v =~= empty_word());
                assert(sym_exp(1, s) == 1);
                lemma_signed_power_add(p, 1, k, M);   // x^k·xᵐ ≡ x^{k+m}
                assert(M * xe + M == M * (xe + 1)) by(nonlinear_arith);
                assert(k + M == M * (xe + 1));        // k == M*xe (definitional)
                lemma_concat_empty_left(trail);
                assert(signed_power(1, k) + img =~= signed_power(1, k) + signed_power(1, M));
                assert(head_v + trail =~= trail);
            } else {
                // img = ε; head_v = ε; de=0 ⟹ both sides ≡ x^k.
                assert(img == pp[i as int] && pp[i as int] == empty_word());
                assert(head_v =~= empty_word());
                assert(sym_exp(1, s) == 0 && trail == signed_power(1, k));
                lemma_concat_empty_right(signed_power(1, k));
                lemma_concat_empty_left(signed_power(1, k));
                lemma_equiv_refl(p, signed_power(1, k));
                assert(signed_power(1, k) + img =~= signed_power(1, k));
                assert(head_v + trail =~= signed_power(1, k));
            }
        },
        Symbol::Inv(i) => {
            if i == 0 {
                assert(img =~= inverse_word(pp[0]) && pp[0] == config_word(l, 0));
                lemma_canw_eval_single(CanonLetter { r: coord, s: 0, e: -1 });
                assert(head_v =~= gsconfig(coord, 0, -1));
                assert(sym_exp(1, s) == 0 && trail == signed_power(1, k));
                lemma_tinv_absorb(p, l, k);
            } else if i == 1 {
                assert(img =~= inverse_word(pp[1]) && pp[1] == symbol_power(Symbol::Gen(1), m));
                assert(pp[1] =~= signed_power(1, M));
                lemma_signed_power_inverse(1, M);   // inv(xᵐ) = x⁻ᵐ
                assert(img =~= signed_power(1, -M));
                assert(head_v =~= empty_word());
                assert(sym_exp(1, s) == -1);
                lemma_signed_power_add(p, 1, k, -M);   // x^k·x⁻ᵐ ≡ x^{k−m}
                assert(M * xe + (-M) == M * (xe - 1)) by(nonlinear_arith);
                assert(k + (-M) == M * (xe - 1));      // k == M*xe (definitional)
                lemma_concat_empty_left(trail);
                assert(signed_power(1, k) + img =~= signed_power(1, k) + signed_power(1, -M));
                assert(head_v + trail =~= trail);
            } else {
                assert(img =~= inverse_word(pp[i as int]) && pp[i as int] == empty_word());
                lemma_inverse_empty();
                assert(img =~= empty_word());
                assert(head_v =~= empty_word());
                assert(sym_exp(1, s) == 0 && trail == signed_power(1, k));
                lemma_concat_empty_right(signed_power(1, k));
                lemma_concat_empty_left(signed_power(1, k));
                lemma_equiv_refl(p, signed_power(1, k));
                assert(signed_power(1, k) + img =~= signed_power(1, k));
                assert(head_v + trail =~= signed_power(1, k));
            }
        },
    }
}

// ----------------------------------------------------------------------------
// Net x-exponent of a canw word is 0 (each config x⁻ʳ·tᵉ·xʳ has zero gen-1 exponent).
// ----------------------------------------------------------------------------

/// `gexp(1, canl_eval(c)) == 0` — `gsconfig(r,s,e)`'s `x⁻ʳ … xʳ` cancel in the gen-1 exponent.
pub proof fn lemma_gexp1_canl_zero(c: CanonLetter)
    ensures
        gexp(1, canl_eval(c)) == 0,
{
    let r = c.r;
    let s = c.s;
    let e = c.e;
    // canl_eval(c) = gsconfig(r,s,e) = sp(2,-s)+sp(1,-r)+sp(0,e)+sp(1,r)+sp(2,s).
    lemma_gexp_concat(1, signed_power(2, -s) + signed_power(1, -r) + signed_power(0, e)
        + signed_power(1, r), signed_power(2, s));
    lemma_gexp_concat(1, signed_power(2, -s) + signed_power(1, -r) + signed_power(0, e),
        signed_power(1, r));
    lemma_gexp_concat(1, signed_power(2, -s) + signed_power(1, -r), signed_power(0, e));
    lemma_gexp_concat(1, signed_power(2, -s), signed_power(1, -r));
    lemma_gexp_signed_power(2, 1, -s);   // 0
    lemma_gexp_signed_power(1, 1, -r);   // -r
    lemma_gexp_signed_power(0, 1, e);    // 0
    lemma_gexp_signed_power(1, 1, r);    // r
    lemma_gexp_signed_power(2, 1, s);    // 0
}

/// `gexp(1, canw_eval(w)) == 0` — a config product lives in the normal closure of `t`.
pub proof fn lemma_gexp1_canw_zero(w: Seq<CanonLetter>)
    ensures
        gexp(1, canw_eval(w)) == 0,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(canw_eval(w) =~= empty_word());
    } else {
        lemma_gexp_concat(1, canl_eval(w[0]), canw_eval(w.drop_first()));
        lemma_gexp1_canl_zero(w[0]);
        lemma_gexp1_canw_zero(w.drop_first());
    }
}

// ----------------------------------------------------------------------------
// THE CENTERPIECE — the coordinate-tracking invariant.
// ----------------------------------------------------------------------------

/// **Coordinate-tracking invariant**: reading `emb(φ', u)` symbol-by-symbol with running x-exponent
/// `xe`, every `t` lands at a config coordinate `≡ l (mod m)`:
///   `x^{m·xe} · emb(φ', u)  ≡_p  canw_eval(phi_canon_acc(u, xe)) · x^{m·(xe + xexp(u))}`,
/// `xexp(u) = gexp(1, u)`.  Induction on `u` via the per-step lemma + the unfold of `phi_canon_acc`.
pub proof fn lemma_phi_canon_invariant(p: Presentation, n: nat, m: nat, l: nat, u: Word, xe: int)
    requires
        presentation_valid(p),
        p.num_generators >= 3,
        word_valid(u, (n + 3) as nat),
    ensures
        equiv_in_presentation(p,
            signed_power(1, (m as int) * xe) + apply_embedding(phi_prime(n, m, l), u),
            canw_eval(phi_canon_acc(l, m, u, xe))
                + signed_power(1, (m as int) * (xe + gexp(1, u)))),
    decreases u.len(),
{
    let M = m as int;
    let pp = phi_prime(n, m, l);
    let lhs = signed_power(1, M * xe) + apply_embedding(pp, u);
    let rhs = canw_eval(phi_canon_acc(l, m, u, xe)) + signed_power(1, M * (xe + gexp(1, u)));

    if u.len() == 0 {
        assert(apply_embedding(pp, u) =~= empty_word());
        assert(phi_canon_acc(l, m, u, xe) =~= Seq::<CanonLetter>::empty());
        assert(canw_eval(phi_canon_acc(l, m, u, xe)) =~= empty_word());
        assert(gexp(1, u) == 0);
        assert(M * (xe + 0) == M * xe);
        lemma_concat_empty_right(signed_power(1, M * xe));
        lemma_concat_empty_left(signed_power(1, M * xe));
        assert(lhs =~= signed_power(1, M * xe));
        assert(rhs =~= signed_power(1, M * xe));
        lemma_equiv_refl(p, signed_power(1, M * xe));
    } else {
        let s = u[0];
        let rest = u.drop_first();
        let de = sym_exp(1, s);
        let img = apply_embedding_symbol(pp, s);
        assert(symbol_valid(s, (n + 3) as nat)) by { assert(u[0] == s); }
        assert(word_valid(rest, (n + 3) as nat)) by {
            assert forall|j: int| 0 <= j < rest.len()
                implies symbol_valid(#[trigger] rest[j], (n + 3) as nat) by {
                assert(rest[j] == u[j + 1]);
            }
        }
        assert(apply_embedding(pp, u) =~= img + apply_embedding(pp, rest));
        // gexp(1, u) = sym_exp(1, s) + gexp(1, rest) = de + gexp(1, rest).
        assert(gexp(1, u) == de + gexp(1, rest)) by { assert(u[0] == s); }

        let head_v = canw_eval(phi_head(l, m, s, xe));
        let embr = apply_embedding(pp, rest);
        let tail_de = signed_power(1, M * (xe + de));
        let inner_tail = signed_power(1, M * (xe + de + gexp(1, rest)));
        let pc_rest = canw_eval(phi_canon_acc(l, m, rest, xe + de));

        // --- per-step + IH ---
        lemma_phi_step(p, n, m, l, s, xe);
        // equiv(p, sp(M*xe)+img, head_v + tail_de)
        lemma_phi_canon_invariant(p, n, m, l, rest, xe + de);
        // equiv(p, sp(M*(xe+de))+embr, pc_rest + inner_tail)

        // --- chain ---
        // X = (sp(M*xe)+img)+embr ;  Y = head_v + (tail_de + embr)
        let x1 = (signed_power(1, M * xe) + img) + embr;
        let y = head_v + (tail_de + embr);
        assert(lhs =~= x1);                                      // assoc
        lemma_equiv_concat_left(p, signed_power(1, M * xe) + img, head_v + tail_de, embr);
        assert((head_v + tail_de) + embr =~= y);                // assoc
        assert(equiv_in_presentation(p, lhs, y)) by {
            assert(lhs =~= x1);
            assert((signed_power(1, M * xe) + img) + embr == x1);
        }
        // Z = head_v + (pc_rest + inner_tail) ;  RHS shape
        let z = head_v + (pc_rest + inner_tail);
        lemma_equiv_concat_right(p, head_v, tail_de + embr, pc_rest + inner_tail);
        assert(equiv_in_presentation(p, y, z));
        // z =~= (head_v + pc_rest) + inner_tail =~= canw_eval(phi_canon_acc(u,xe)) + rhs_tail
        lemma_phi_canon_acc_unfold(l, m, u, xe);
        lemma_canw_eval_concat(phi_head(l, m, s, xe), phi_canon_acc(l, m, rest, xe + de));
        assert(canw_eval(phi_canon_acc(l, m, u, xe)) =~= head_v + pc_rest);
        assert(M * (xe + de + gexp(1, rest)) == M * (xe + gexp(1, u))) by {
            assert(gexp(1, u) == de + gexp(1, rest));
        }
        assert(z =~= rhs);
        lemma_equiv_transitive(p, lhs, y, z);
        assert(equiv_in_presentation(p, lhs, rhs)) by { assert(z =~= rhs); }
    }
}

// ----------------------------------------------------------------------------
// Coordinate congruence — every canw letter sits at `r ≡ l (mod m)`.
// ----------------------------------------------------------------------------

/// `r ≡ l (mod m)`: there is an integer `b` with `r = m·b + l`.  (`b = −E` for the running
/// x-exponent `E`; the σ-shift `σ(β) = m·β + l` is exactly `cong_l` with `b = β`.)
pub open spec fn cong_l(r: int, m: nat, l: nat) -> bool {
    exists|b: int| r == #[trigger] ((m as int) * b) + (l as int)
}

/// Introduce `cong_l` from a concrete witness `b`.
pub proof fn lemma_cong_l_intro(r: int, m: nat, l: nat, b: int)
    requires
        r == (m as int) * b + (l as int),
    ensures
        cong_l(r, m, l),
{
}

// ----------------------------------------------------------------------------
// σ-backward-saturation — the side condition that makes (R') true.
// ----------------------------------------------------------------------------

/// **σ-backward-saturation**: every `bet`-element of the form `m·b + l` has its preimage `b` in `bet`.
/// (Without it, (R') is false — see docs/brick5-c3.2c-plan.md §6 counterexample.)
pub open spec fn sigma_backsat(bet: Seq<nat>, m: nat, l: nat) -> bool {
    forall|b: nat| bet.contains(#[trigger] ((m * b + l) as nat)) ==> bet.contains(b)
}

/// **Saturation bridge**: a `bet`-coordinate `r ≡ l (mod m)` is actually a `σ(bet)`-coordinate.
/// From `cong_l` get `r = m·b + l`; `r ≥ 0` (a nat coordinate) and `l < m` force `b ≥ 0`; saturation
/// pulls `b` into `bet`, so `r = σ(b) = sigma_betas(bet)[k]` for that `k`.
pub proof fn lemma_sat_bridge(bet: Seq<nat>, m: nat, l: nat, r: int)
    requires
        m >= 1,
        l < m,
        cong_l(r, m, l),
        exists|j: int| 0 <= j < bet.len() && bet[j] as int == r,
        sigma_backsat(bet, m, l),
    ensures
        exists|k: int| 0 <= k < bet.len() && sigma_betas(bet, m, l)[k] as int == r,
{
    let j = choose|j: int| 0 <= j < bet.len() && bet[j] as int == r;
    assert(0 <= j < bet.len() && bet[j] as int == r);
    assert(r >= 0);   // r == bet[j] : nat
    let b = choose|b: int| r == #[trigger] ((m as int) * b) + (l as int);   // from cong_l
    assert(r == (m as int) * b + (l as int));
    // b ≥ 0: if b ≤ −1 then m·b ≤ −m, so r = m·b + l ≤ l − m < 0, contradicting r ≥ 0.
    assert(b >= 0) by(nonlinear_arith)
        requires r == (m as int) * b + (l as int), r >= 0, (l as int) < (m as int), m >= 1;
    let bn = b as nat;
    assert(bn == b && (m * bn + l) as int == r) by {
        assert(bn as int == b);
        assert((m as int) * b + (l as int) == r);
    }
    // bet contains m·bn + l  (= r = bet[j]).
    assert(bet.contains((m * bn + l) as nat)) by {
        assert((m * bn + l) as nat == bet[j]);
        assert(bet[j] == bet[j]);
    }
    // saturation ⟹ bet contains bn.
    assert(bet.contains(bn));
    let k = choose|k: int| 0 <= k < bet.len() && bet[k] == bn;
    assert(0 <= k < bet.len() && bet[k] == bn);
    // sigma_betas(bet)[k] = m·bet[k] + l = m·bn + l = r.
    assert(sigma_betas(bet, m, l)[k] == (m * bet[k] + l) as nat);
    assert(sigma_betas(bet, m, l)[k] as int == r) by {
        assert(bet[k] == bn);
        assert((m * bn + l) as int == r);
    }
}

/// **Coordinate congruence**: every letter of `phi_canon_acc(u, xe)` has `s = 0` and a coordinate
/// `≡ l (mod m)` — each `t` of `u` lands at `l − m·E` for the running x-exponent `E`.
pub proof fn lemma_phi_canon_acc_coords(l: nat, m: nat, u: Word, xe: int)
    ensures
        forall|j: int| 0 <= j < phi_canon_acc(l, m, u, xe).len() ==> {
            &&& (#[trigger] phi_canon_acc(l, m, u, xe)[j]).s == 0
            &&& cong_l(phi_canon_acc(l, m, u, xe)[j].r, m, l)
        },
    decreases u.len(),
{
    let pc = phi_canon_acc(l, m, u, xe);
    if u.len() == 0 {
        assert(pc =~= Seq::<CanonLetter>::empty());
    } else {
        let s = u[0];
        let rest = u.drop_first();
        let de = sym_exp(1, s);
        let hd = phi_head(l, m, s, xe);
        let tl = phi_canon_acc(l, m, rest, xe + de);
        lemma_phi_canon_acc_unfold(l, m, u, xe);            // pc =~= hd + tl
        lemma_phi_canon_acc_coords(l, m, rest, xe + de);    // IH on tl
        let coord = (l as int) - (m as int) * xe;
        // coord == M·(−xe) + l  (coord == l − M·xe definitionally; the product flip is nonlinear).
        assert((m as int) * (-xe) + (l as int) == (l as int) - (m as int) * xe) by(nonlinear_arith);
        lemma_cong_l_intro(coord, m, l, -xe);   // witness b = −xe
        assert forall|j: int| 0 <= j < pc.len() implies {
            &&& (#[trigger] pc[j]).s == 0
            &&& cong_l(pc[j].r, m, l)
        } by {
            assert(pc == hd + tl);
            if j < hd.len() {
                assert(pc[j] == hd[j]);
                // hd is [{coord,0,±1}] (Gen0/Inv0) — its single letter has s=0, r=coord.
                assert(hd[j].s == 0 && hd[j].r == coord);
            } else {
                assert(pc[j] == tl[j - hd.len()]);
                assert(0 <= j - hd.len() < tl.len());
                assert(tl[j - hd.len()].s == 0 && cong_l(tl[j - hd.len()].r, m, l));
            }
        }
    }
}

} // verus!
