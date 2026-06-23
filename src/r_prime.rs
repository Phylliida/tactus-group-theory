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
    canl_eval, canw_eval, gexp, lemma_signed_power_add, lemma_signed_power_valid,
    lemma_inverse_word_concat};
use crate::ii_subset::lemma_signed_power_inverse;

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

} // verus!
