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
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::hnn::*;
use crate::ii_subset::{lemma_ii_subset, lemma_signed_power_inverse, lemma_exact_div};
use crate::benign::{apply_embedding, apply_embedding_symbol, in_generated_subgroup,
    lemma_apply_embedding_concat, lemma_apply_embedding_valid};
use crate::tower_peel::{quad_data, lemma_in_TM_gexp_zero};
use crate::config_reduce::*;

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

//  ============================================================
//  B4 — per-letter embedding lemmas (the algebraic core).
//  ============================================================

//  Signed config-power conjugation by x:  x⁻ᵖᵖ · gsconfig(r,s,e) · xᵖᵖ ≡ gsconfig(r+pp, s, e).
//  Identical to lemma_sconfig_conj_x but with the t-letter replaced by t^e (middle-independent:
//  the prefix/suffix conj lemmas only move the outer x-power past the y⁻ˢ/yˢ).
#[verifier::rlimit(100)]
pub proof fn lemma_conj_gsconfig_by_x(r: int, s: int, e: int, pp: int)
    ensures
        equiv_in_presentation(base_A(),
            signed_power(1, -pp) + gsconfig(r, s, e) + signed_power(1, pp),
            gsconfig(r + pp, s, e)),
{
    let a = base_A();
    lemma_base_A_valid();
    let xmP = signed_power(1, -pp);
    let xP = signed_power(1, pp);
    let mid = signed_power(0, e);
    let preL = signed_power(1, -pp) + signed_power(2, -s) + signed_power(1, -r);
    let preL2 = signed_power(2, -s) + signed_power(1, -(r + pp));
    let sufR = signed_power(1, r) + signed_power(2, s) + signed_power(1, pp);
    let sufR2 = signed_power(1, (r + pp)) + signed_power(2, s);
    lemma_sconfig_prefix_conj(r, s, pp);                     //  preL ≡ preL2
    lemma_sconfig_suffix_conj(r, s, pp);                     //  sufR ≡ sufR2
    let lhs = xmP + gsconfig(r, s, e) + xP;
    let rhs = gsconfig(r + pp, s, e);
    assert(lhs =~= preL + (mid + sufR));
    assert(rhs =~= preL2 + (mid + sufR2));
    let m1 = preL2 + (mid + sufR);
    assert(equiv_in_presentation(a, lhs, m1)) by {
        lemma_equiv_concat_left(a, preL, preL2, mid + sufR);
        assert(lhs =~= preL + (mid + sufR));
        assert(m1 =~= preL2 + (mid + sufR));
    }
    assert(equiv_in_presentation(a, m1, rhs)) by {
        lemma_equiv_concat_right(a, preL2 + mid, sufR, sufR2);
        assert(m1 =~= (preL2 + mid) + sufR);
        assert(rhs =~= (preL2 + mid) + sufR2);
    }
    lemma_equiv_transitive(a, lhs, m1, rhs);
}

//  Signed config-power conjugation by y:  y⁻ᵠ · gsconfig(r,s,e) · yᵠ ≡ gsconfig(r, s+qq, e).
#[verifier::rlimit(100)]
pub proof fn lemma_conj_gsconfig_by_y(r: int, s: int, e: int, qq: int)
    ensures
        equiv_in_presentation(base_A(),
            signed_power(2, -qq) + gsconfig(r, s, e) + signed_power(2, qq),
            gsconfig(r, s + qq, e)),
{
    let a = base_A();
    lemma_base_A_valid();
    let ymQ = signed_power(2, -qq);
    let yQ = signed_power(2, qq);
    let middle = signed_power(1, -r) + signed_power(0, e) + signed_power(1, r);
    let preL = signed_power(2, -qq) + signed_power(2, -s);
    let preL2 = signed_power(2, -(s + qq));
    let sufR = signed_power(2, s) + signed_power(2, qq);
    let sufR2 = signed_power(2, (s + qq));
    lemma_signed_power_add(a, 2, -qq, -s);                   //  ymQ·y⁻ˢ ≡ y^(-qq-s)
    assert(signed_power(2, -qq + -s) == preL2) by { assert(-qq + -s == -(s + qq)); }
    lemma_signed_power_add(a, 2, s, qq);                     //  yˢ·yQ ≡ y^(s+qq)
    let lhs = ymQ + gsconfig(r, s, e) + yQ;
    let rhs = gsconfig(r, (s + qq), e);
    assert(lhs =~= preL + (middle + sufR));
    assert(rhs =~= preL2 + (middle + sufR2));
    let m1 = preL2 + (middle + sufR);
    assert(equiv_in_presentation(a, lhs, m1)) by {
        lemma_equiv_concat_left(a, preL, preL2, middle + sufR);
        assert(lhs =~= preL + (middle + sufR));
        assert(m1 =~= preL2 + (middle + sufR));
    }
    assert(equiv_in_presentation(a, m1, rhs)) by {
        lemma_equiv_concat_right(a, preL2 + middle, sufR, sufR2);
        assert(m1 =~= (preL2 + middle) + sufR);
        assert(rhs =~= (preL2 + middle) + sufR2);
    }
    lemma_equiv_transitive(a, lhs, m1, rhs);
}

//  ── apply_embedding of a generator power scales the exponent (literal equality). ──
//  gens[i] = xᵖᵖ (well, the gen-i image is the symbol-power);  apply_embedding sends Gen(i)ⁿ ↦ Gen(i)^{pp·n}.
pub proof fn lemma_emb_gen_pow(gens: Seq<Word>, i: nat, pp: nat, n: nat)
    requires
        (i as int) < gens.len(),
        gens[i as int] =~= symbol_power(Symbol::Gen(i), pp),
    ensures
        apply_embedding(gens, symbol_power(Symbol::Gen(i), n)) =~= symbol_power(Symbol::Gen(i), pp * n),
    decreases n,
{
    reveal_with_fuel(apply_embedding, 2);
    if n == 0 {
        assert(symbol_power(Symbol::Gen(i), n) =~= Seq::<Symbol>::empty());
        assert(apply_embedding(gens, symbol_power(Symbol::Gen(i), n)) =~= Seq::<Symbol>::empty());
        assert(pp * n == 0);
        assert(symbol_power(Symbol::Gen(i), pp * n) =~= Seq::<Symbol>::empty());
    } else {
        let n1: nat = (n - 1) as nat;
        let tail = symbol_power(Symbol::Gen(i), n1);
        assert(n == n1 + 1);
        assert(symbol_power(Symbol::Gen(i), n) =~= seq![Symbol::Gen(i)] + tail) by {
            lemma_symbol_power_merge(Symbol::Gen(i), 1, n1);
            lemma_symbol_power_one(Symbol::Gen(i));
        }
        lemma_apply_embedding_concat(gens, seq![Symbol::Gen(i)], tail);
        assert(apply_embedding(gens, seq![Symbol::Gen(i)]) =~= symbol_power(Symbol::Gen(i), pp));
        lemma_emb_gen_pow(gens, i, pp, n1);
        lemma_symbol_power_merge(Symbol::Gen(i), pp, pp * n1);
        assert(pp + pp * n1 == pp * n) by (nonlinear_arith) requires n == n1 + 1;
    }
}

pub proof fn lemma_emb_inv_pow(gens: Seq<Word>, i: nat, pp: nat, n: nat)
    requires
        (i as int) < gens.len(),
        gens[i as int] =~= symbol_power(Symbol::Gen(i), pp),
    ensures
        apply_embedding(gens, symbol_power(Symbol::Inv(i), n)) =~= symbol_power(Symbol::Inv(i), pp * n),
    decreases n,
{
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    if n == 0 {
        assert(symbol_power(Symbol::Inv(i), n) =~= Seq::<Symbol>::empty());
        assert(apply_embedding(gens, symbol_power(Symbol::Inv(i), n)) =~= Seq::<Symbol>::empty());
        assert(pp * n == 0);
        assert(symbol_power(Symbol::Inv(i), pp * n) =~= Seq::<Symbol>::empty());
    } else {
        let n1: nat = (n - 1) as nat;
        let tail = symbol_power(Symbol::Inv(i), n1);
        assert(n == n1 + 1);
        assert(symbol_power(Symbol::Inv(i), n) =~= seq![Symbol::Inv(i)] + tail) by {
            lemma_symbol_power_merge(Symbol::Inv(i), 1, n1);
            lemma_symbol_power_one(Symbol::Inv(i));
        }
        lemma_apply_embedding_concat(gens, seq![Symbol::Inv(i)], tail);
        //  apply_embedding(gens, [Inv(i)]) = inverse_word(gens[i]) = inverse_word(xᵖᵖ) = x⁻ᵖᵖ-as-Inv-power
        lemma_inverse_word_sympower(Symbol::Gen(i), pp);
        assert(apply_embedding(gens, seq![Symbol::Inv(i)]) =~= symbol_power(Symbol::Inv(i), pp));
        lemma_emb_inv_pow(gens, i, pp, n1);
        lemma_symbol_power_merge(Symbol::Inv(i), pp, pp * n1);
        assert(pp + pp * n1 == pp * n) by (nonlinear_arith) requires n == n1 + 1;
    }
}

//  Signed wrapper:  apply_embedding(gens, signed_power(i,k)) =~= signed_power(i, pp·k).
pub proof fn lemma_emb_signed_scaled(gens: Seq<Word>, i: nat, pp: nat, k: int)
    requires
        (i as int) < gens.len(),
        gens[i as int] =~= signed_power(i, pp as int),
    ensures
        apply_embedding(gens, signed_power(i, k)) =~= signed_power(i, (pp as int) * k),
{
    assert(gens[i as int] =~= symbol_power(Symbol::Gen(i), pp));
    if k >= 0 {
        assert(signed_power(i, k) =~= symbol_power(Symbol::Gen(i), k as nat));
        lemma_emb_gen_pow(gens, i, pp, k as nat);
        assert((pp as int) * k >= 0) by (nonlinear_arith) requires pp >= 0, k >= 0;
        assert(pp * (k as nat) == ((pp as int) * k) as nat) by (nonlinear_arith) requires k >= 0;
        assert(signed_power(i, (pp as int) * k) =~= symbol_power(Symbol::Gen(i), pp * (k as nat)));
    } else {
        assert(signed_power(i, k) =~= symbol_power(Symbol::Inv(i), (-k) as nat));
        lemma_emb_inv_pow(gens, i, pp, (-k) as nat);
        assert((pp as int) * k <= 0) by (nonlinear_arith) requires pp >= 0, k < 0;
        assert(pp * ((-k) as nat) == (-((pp as int) * k)) as nat) by (nonlinear_arith) requires k < 0;
        assert(signed_power(i, (pp as int) * k) =~= symbol_power(Symbol::Inv(i), pp * ((-k) as nat)));
    }
}

//  apply_embedding(gens, signed_power(0,e)) ≡_A gsconfig(a,b,e)  when gens[0] = config_word(a,b).
//  (The t-generator image is a config; its e-th power is the conjugated power gsconfig(·,·,e).)
pub proof fn lemma_emb_tpow(gens: Seq<Word>, a: nat, b: nat, e: int)
    requires
        0 < gens.len(),
        gens[0] =~= config_word(a, b),
    ensures
        equiv_in_presentation(base_A(), apply_embedding(gens, signed_power(0, e)),
            gsconfig(a as int, b as int, e)),
    decreases (if e >= 0 { e } else { -e }),
{
    let p = base_A();
    lemma_base_A_valid();
    let ai = a as int;
    let bi = b as int;
    //  config_word(a,b) =~= gsconfig(a,b,1):  config_word =~= sconfig =~= gsconfig(·,·,1).
    lemma_sconfig_nat(ai, bi);
    lemma_sconfig_is_gsconfig1(ai, bi);
    assert(config_word(a, b) =~= gsconfig(ai, bi, 1));
    if e == 0 {
        assert(signed_power(0, 0) =~= Seq::<Symbol>::empty());
        assert(apply_embedding(gens, signed_power(0, 0)) =~= empty_word()) by {
            reveal_with_fuel(apply_embedding, 2);
        }
        lemma_gsconfig_zero(ai, bi);                          //  gsconfig(a,b,0) ≡ empty
        lemma_equiv_symmetric(p, gsconfig(ai, bi, 0), empty_word());
        lemma_equiv_refl(p, empty_word());
        lemma_equiv_transitive(p, apply_embedding(gens, signed_power(0, 0)), empty_word(),
            gsconfig(ai, bi, 0));
    } else if e > 0 {
        let e1 = e - 1;
        let tail = signed_power(0, e1);
        assert(signed_power(0, e) =~= seq![Symbol::Gen(0)] + tail) by {
            lemma_symbol_power_merge(Symbol::Gen(0), 1, e1 as nat);
            lemma_symbol_power_one(Symbol::Gen(0));
        }
        lemma_apply_embedding_concat(gens, seq![Symbol::Gen(0)], tail);
        assert(apply_embedding(gens, seq![Symbol::Gen(0)]) =~= gens[0]) by {
            reveal_with_fuel(apply_embedding, 2);
        }
        //  AE(signed_power(0,e)) =~= config_word(a,b) + AE(tail) == gsconfig(a,b,1) + AE(tail)
        let ae_tail = apply_embedding(gens, tail);
        assert(apply_embedding(gens, signed_power(0, e)) =~= gsconfig(ai, bi, 1) + ae_tail);
        lemma_emb_tpow(gens, a, b, e1);                        //  AE(tail) ≡ gsconfig(a,b,e-1)
        lemma_equiv_concat_right(p, gsconfig(ai, bi, 1), ae_tail, gsconfig(ai, bi, e1));
        lemma_gsconfig_merge(ai, bi, 1, e1);                   //  g(·,1)·g(·,e-1) ≡ g(·,e)
        assert(1 + e1 == e);
        lemma_equiv_transitive(p, apply_embedding(gens, signed_power(0, e)),
            gsconfig(ai, bi, 1) + gsconfig(ai, bi, e1), gsconfig(ai, bi, e));
    } else {
        let e1 = e + 1;
        let tail = signed_power(0, e1);
        assert(signed_power(0, e) =~= seq![Symbol::Inv(0)] + tail) by {
            lemma_symbol_power_merge(Symbol::Inv(0), 1, (-e1) as nat);
            lemma_symbol_power_one(Symbol::Inv(0));
        }
        lemma_apply_embedding_concat(gens, seq![Symbol::Inv(0)], tail);
        //  AE([Inv(0)]) = inverse_word(gens[0]) =~= inverse_word(config_word(a,b)) =~= gsconfig(a,b,-1)
        assert(apply_embedding(gens, seq![Symbol::Inv(0)]) =~= inverse_word(gens[0])) by {
            reveal_with_fuel(apply_embedding, 2);
            reveal_with_fuel(inverse_word, 2);
        }
        lemma_gsconfig_neg_one(ai, bi);                        //  gsconfig(a,b,-1) =~= inverse_word(sconfig(a,b))
        assert(inverse_word(gens[0]) =~= gsconfig(ai, bi, -1));
        let ae_tail = apply_embedding(gens, tail);
        assert(apply_embedding(gens, signed_power(0, e)) =~= gsconfig(ai, bi, -1) + ae_tail);
        lemma_emb_tpow(gens, a, b, e1);                        //  AE(tail) ≡ gsconfig(a,b,e+1)
        lemma_equiv_concat_right(p, gsconfig(ai, bi, -1), ae_tail, gsconfig(ai, bi, e1));
        lemma_gsconfig_merge(ai, bi, -1, e1);                  //  g(·,-1)·g(·,e+1) ≡ g(·,e)
        assert(-1 + e1 == e);
        lemma_equiv_transitive(p, apply_embedding(gens, signed_power(0, e)),
            gsconfig(ai, bi, -1) + gsconfig(ai, bi, e1), gsconfig(ai, bi, e));
    }
}

//  ── The generic per-letter embedding lemma (combines distribution + scaling + conjugation). ──
//  For gens = [config_word(a,b), xᵖˣ, yᵖʸ],  apply_embedding(gens, gsconfig(k,l,e)) ≡_A
//  gsconfig(a + px·k, b + py·l, e).  Serves all three quad sides (a-side px=py=m; R b-side px=m²,py=1;
//  L b-side px=1,py=m²).  The b-side image lands at the quad_step-relabelled coordinate.
#[verifier::rlimit(300)]
pub proof fn lemma_emb_gsconfig(gens: Seq<Word>, a: nat, b: nat, px: nat, py: nat, k: int, l: int, e: int)
    requires
        gens.len() == 3,
        gens[0] =~= config_word(a, b),
        gens[1] =~= signed_power(1, px as int),
        gens[2] =~= signed_power(2, py as int),
    ensures
        equiv_in_presentation(base_A(), apply_embedding(gens, gsconfig(k, l, e)),
            gsconfig(a as int + (px as int) * k, b as int + (py as int) * l, e)),
{
    let p = base_A();
    lemma_base_A_valid();
    let ai = a as int;
    let bi = b as int;
    let pxk = (px as int) * k;
    let pyl = (py as int) * l;
    let s1 = signed_power(2, -l);
    let s2 = signed_power(1, -k);
    let s3 = signed_power(0, e);
    let s4 = signed_power(1, k);
    let s5 = signed_power(2, l);
    assert(gsconfig(k, l, e) == s1 + s2 + s3 + s4 + s5);
    let ae1 = apply_embedding(gens, s1);
    let ae2 = apply_embedding(gens, s2);
    let ae3 = apply_embedding(gens, s3);
    let ae4 = apply_embedding(gens, s4);
    let ae5 = apply_embedding(gens, s5);
    //  --- distribution: AE(gsconfig) =~= ae1+ae2+ae3+ae4+ae5 ---
    let w12 = s1 + s2;
    let w123 = s1 + s2 + s3;
    let w1234 = s1 + s2 + s3 + s4;
    lemma_apply_embedding_concat(gens, w1234, s5);
    lemma_apply_embedding_concat(gens, w123, s4);
    lemma_apply_embedding_concat(gens, w12, s3);
    lemma_apply_embedding_concat(gens, s1, s2);
    assert(apply_embedding(gens, gsconfig(k, l, e)) =~= ae1 + ae2 + ae3 + ae4 + ae5);
    //  --- scaling: ae1,ae2,ae4,ae5 are signed powers ---
    lemma_emb_signed_scaled(gens, 2, py, -l);
    lemma_emb_signed_scaled(gens, 1, px, -k);
    lemma_emb_signed_scaled(gens, 1, px, k);
    lemma_emb_signed_scaled(gens, 2, py, l);
    assert((py as int) * (-l) == -((py as int) * l)) by (nonlinear_arith);
    assert((px as int) * (-k) == -((px as int) * k)) by (nonlinear_arith);
    assert((py as int) * (-l) == -pyl);
    assert((px as int) * (-k) == -pxk);
    assert(ae1 =~= signed_power(2, -pyl));
    assert(ae2 =~= signed_power(1, -pxk));
    assert(ae4 =~= signed_power(1, pxk));
    assert(ae5 =~= signed_power(2, pyl));
    //  ae3 ≡_A gsconfig(a,b,e)
    lemma_emb_tpow(gens, a, b, e);
    let g0 = gsconfig(ai, bi, e);
    //  --- replace ae3 by g0 in the middle (congruence) ---
    //  D := ae1+ae2+ae3+ae4+ae5 =~= sp(2,-pyl)+sp(1,-pxk)+ae3+sp(1,pxk)+sp(2,pyl)
    let xL = signed_power(1, -pxk);
    let xR = signed_power(1, pxk);
    let yL = signed_power(2, -pyl);
    let yR = signed_power(2, pyl);
    assert(ae1 + ae2 + ae3 + ae4 + ae5 =~= yL + xL + ae3 + xR + yR);
    //  middle x-conjugation on ae3 ≡ g0:  xL+ae3+xR ≡ xL+g0+xR
    let mxA = xL + ae3 + xR;
    let mxB = xL + g0 + xR;
    assert(equiv_in_presentation(p, mxA, mxB)) by {
        lemma_equiv_concat_left(p, ae3, g0, xR);              //  ae3+xR ≡ g0+xR
        lemma_equiv_concat_right(p, xL, ae3 + xR, g0 + xR);   //  xL+(ae3+xR) ≡ xL+(g0+xR)
        assert(mxA =~= xL + (ae3 + xR));
        assert(mxB =~= xL + (g0 + xR));
    }
    //  conj-by-x:  xL + g0 + xR ≡ gsconfig(a+pxk, b, e)
    lemma_conj_gsconfig_by_x(ai, bi, e, pxk);
    let g1 = gsconfig(ai + pxk, bi, e);
    lemma_equiv_transitive(p, mxA, mxB, g1);
    //  now wrap with y:  yL + mxA + yR ≡ yL + g1 + yR ≡ gsconfig(a+pxk, b+pyl, e)
    let fullA = yL + mxA + yR;
    let fullB = yL + g1 + yR;
    assert(equiv_in_presentation(p, fullA, fullB)) by {
        lemma_equiv_concat_left(p, mxA, g1, yR);              //  mxA+yR ≡ g1+yR
        lemma_equiv_concat_right(p, yL, mxA + yR, g1 + yR);   //  yL+(mxA+yR) ≡ yL+(g1+yR)
        assert(fullA =~= yL + (mxA + yR));
        assert(fullB =~= yL + (g1 + yR));
    }
    lemma_conj_gsconfig_by_y(ai + pxk, bi, e, pyl);
    let g2 = gsconfig(ai + pxk, bi + pyl, e);
    lemma_equiv_transitive(p, fullA, fullB, g2);
    //  assemble:  AE(gsconfig) =~= yL+xL+ae3+xR+yR =~= fullA ≡ g2
    assert(yL + xL + ae3 + xR + yR =~= fullA);
    lemma_equiv_refl(p, apply_embedding(gens, gsconfig(k, l, e)));
    assert(equiv_in_presentation(p, apply_embedding(gens, gsconfig(k, l, e)), fullA));
    lemma_equiv_transitive(p, apply_embedding(gens, gsconfig(k, l, e)), fullA, g2);
}

//  ============================================================
//  B4/B5 — fold the reduced config word into one embedding word U, then run it through both sides.
//  ============================================================

//  nat division/mod agree with int division/mod on nonnegatives.
proof fn lemma_nat_div_int(x: int, m: int)
    requires
        x >= 0,
        m > 0,
    ensures
        (x as nat) / (m as nat) == x / m,
        (x as nat) % (m as nat) == x % m,
{
}

//  Residue reconstruction:  for r ≡ a (mod m), 0≤a<m,  a + m·(r/m) == r  and  r%m == a.
proof fn lemma_residue_recon(r: int, a: int, m: int)
    requires
        r >= 0,
        0 <= a < m,
        (r - a) % m == 0,
    ensures
        a + m * (r / m) == r,
        r % m == a,
{
    lemma_exact_div(r - a, m);                                       //  r-a == ((r-a)/m)·m
    let q = (r - a) / m;
    assert(q * m == m * q) by (nonlinear_arith);
    assert(r == q * m + a);                                          //  from r-a == q·m
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(r, m, q, a);  //  q == r/m, a == r%m
    assert(m * (r / m) == m * q);                                    //  congruence from q == r/m
    //  a + m·(r/m) == a + m·q == a + q·m == a + (r - a) == r
}

//  Per-letter embedding word over the 3 quad generators:  gsconfig(r/m, s/m, e) (the residue quotients).
pub open spec fn letter_to_U(c: CanonLetter, m: int) -> Word {
    gsconfig(c.r / m, c.s / m, c.e)
}

//  Fold a reduced config word into a single embedding word.
pub open spec fn red_to_U(red: Seq<CanonLetter>, m: int) -> Word
    decreases red.len(),
{
    if red.len() == 0 {
        empty_word()
    } else {
        letter_to_U(red[0], m) + red_to_U(red.drop_first(), m)
    }
}

//  a-side:  apply_embedding(a_gens, red_to_U(red,m)) ≡_A canw_eval(red),  where a_gens = [t(a,b), xᵐ, yᵐ]
//  and every coordinate of red lies in the residue class (a,b mod m).
pub proof fn lemma_emb_aside_eq(gens: Seq<Word>, red: Seq<CanonLetter>, a: nat, b: nat, m: nat)
    requires
        m > 0,
        a < m,
        b < m,
        gens.len() == 3,
        gens[0] =~= config_word(a, b),
        gens[1] =~= signed_power(1, m as int),
        gens[2] =~= signed_power(2, m as int),
        forall|i: int| 0 <= i < red.len() ==> {
            &&& (#[trigger] red[i]).r >= 0
            &&& red[i].s >= 0
            &&& (red[i].r - a as int) % (m as int) == 0
            &&& (red[i].s - b as int) % (m as int) == 0
        },
    ensures
        equiv_in_presentation(base_A(), apply_embedding(gens, red_to_U(red, m as int)), canw_eval(red)),
    decreases red.len(),
{
    let p = base_A();
    lemma_base_A_valid();
    let mi = m as int;
    if red.len() == 0 {
        assert(red_to_U(red, mi) =~= empty_word());
        assert(apply_embedding(gens, red_to_U(red, mi)) =~= empty_word()) by {
            reveal_with_fuel(apply_embedding, 2);
        }
        assert(canw_eval(red) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
    } else {
        let c = red[0];
        let rest = red.drop_first();
        assert(red_to_U(red, mi) == letter_to_U(c, mi) + red_to_U(rest, mi));
        lemma_apply_embedding_concat(gens, letter_to_U(c, mi), red_to_U(rest, mi));
        let ae_head = apply_embedding(gens, letter_to_U(c, mi));
        let ae_rest = apply_embedding(gens, red_to_U(rest, mi));
        assert(apply_embedding(gens, red_to_U(red, mi)) =~= ae_head + ae_rest);
        //  head: per-letter lemma with px=py=m, k=c.r/mi, l=c.s/mi
        lemma_emb_gsconfig(gens, a, b, m, m, c.r / mi, c.s / mi, c.e);
        //  reconstruct: a + m·(c.r/m) == c.r,  b + m·(c.s/m) == c.s
        assert((red[0]).r >= 0 && red[0].s >= 0
            && (red[0].r - a as int) % mi == 0 && (red[0].s - b as int) % mi == 0);
        lemma_residue_recon(c.r, a as int, mi);
        lemma_residue_recon(c.s, b as int, mi);
        assert(a as int + mi * (c.r / mi) == c.r);
        assert(b as int + mi * (c.s / mi) == c.s);
        assert(gsconfig(a as int + mi * (c.r / mi), b as int + mi * (c.s / mi), c.e)
            == gsconfig(c.r, c.s, c.e));
        assert(ae_head == apply_embedding(gens, gsconfig(c.r / mi, c.s / mi, c.e)));
        assert(equiv_in_presentation(p, ae_head, canl_eval(c)));     //  canl_eval(c) = gsconfig(c.r,c.s,c.e)
        //  rest: IH
        assert(forall|i: int| 0 <= i < rest.len() ==> {
            &&& (#[trigger] rest[i]).r >= 0
            &&& rest[i].s >= 0
            &&& (rest[i].r - a as int) % mi == 0
            &&& (rest[i].s - b as int) % mi == 0
        }) by {
            assert forall|i: int| 0 <= i < rest.len() implies {
                &&& (#[trigger] rest[i]).r >= 0
                &&& rest[i].s >= 0
                &&& (rest[i].r - a as int) % mi == 0
                &&& (rest[i].s - b as int) % mi == 0
            } by {
                assert(rest[i] == red[i + 1]);
            }
        }
        lemma_emb_aside_eq(gens, rest, a, b, m);
        assert(equiv_in_presentation(p, ae_rest, canw_eval(rest)));
        //  congruence:  ae_head + ae_rest ≡ canl_eval(c) + canw_eval(rest) = canw_eval(red)
        lemma_equiv_concat_left(p, ae_head, canl_eval(c), ae_rest);
        lemma_equiv_concat_right(p, canl_eval(c), ae_rest, canw_eval(rest));
        lemma_equiv_transitive(p, ae_head + ae_rest, canl_eval(c) + ae_rest,
            canl_eval(c) + canw_eval(rest));
        assert(canw_eval(red) == canl_eval(c) + canw_eval(rest));
        assert(apply_embedding(gens, red_to_U(red, mi)) =~= ae_head + ae_rest);
        lemma_equiv_refl(p, apply_embedding(gens, red_to_U(red, mi)));
        lemma_equiv_transitive(p, apply_embedding(gens, red_to_U(red, mi)), ae_head + ae_rest,
            canw_eval(red));
    }
}

//  ── b-side per letter:  apply_embedding(b_gens, letter_to_U(c,m)) ∈ T(M). ──
//  Each residue-(a,b) config letter maps to a config at the quad_step-relabelled coordinate, which is
//  in H₀ (step_preserves_h0), hence in T(M).
#[verifier::rlimit(300)]
pub proof fn lemma_bside_letter_in_TM(mm: ModMachine, qi: nat, c: CanonLetter)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
        c.r >= 0,
        c.s >= 0,
        mm_in_H0(mm, c.r as nat, c.s as nat),
        (c.r - mm.quads[qi as int].a as int) % (mm.m as int) == 0,
        (c.s - mm.quads[qi as int].b as int) % (mm.m as int) == 0,
    ensures
        in_TM(mm, apply_embedding(hnn_b_gens(quad_data(mm, qi)), letter_to_U(c, mm.m as int))),
{
    let p = base_A();
    lemma_base_A_valid();
    let q = mm.quads[qi as int];
    let m = mm.m;
    let mi = m as int;
    let bg = hnn_b_gens(quad_data(mm, qi));
    let assoc = quad_associations(q, m);
    assert(bg.len() == 3);
    assert(bg[0] == assoc[0].1 && bg[1] == assoc[1].1 && bg[2] == assoc[2].1);
    //  residue / quad_matches facts
    assert(q.a < m && q.b < m) by { assert(quad_wf(q, m)); }
    lemma_residue_recon(c.r, q.a as int, mi);                  //  c.r % mi == q.a
    lemma_residue_recon(c.s, q.b as int, mi);                  //  c.s % mi == q.b
    lemma_nat_div_int(c.r, mi);                                //  (c.r as nat)/m == c.r/mi (& mod)
    lemma_nat_div_int(c.s, mi);
    let R0 = c.r as nat;
    let S0 = c.s as nat;
    let kr = c.r / mi;
    let ks = c.s / mi;
    assert(kr >= 0 && ks >= 0);
    assert(R0 % m == q.a && S0 % m == q.b);                    //  via nat/int mod bridge + recon
    assert(R0 / m == kr && S0 / m == ks);                      //  via nat/int div bridge
    let g0 = letter_to_U(c, mi);
    assert(g0 == gsconfig(kr, ks, c.e));
    //  validity of apply_embedding(bg, g0) over the 3 base generators
    lemma_quad_associations_valid(q, m, 3);
    lemma_gsconfig_valid(kr, ks, c.e);
    assert(forall|i: int| 0 <= i < bg.len() ==> word_valid(#[trigger] bg[i], 3)) by {
        assert forall|i: int| 0 <= i < bg.len() implies word_valid(#[trigger] bg[i], 3) by {
            assert(bg[i] == assoc[i].1);
        }
    }
    lemma_apply_embedding_valid(bg, g0, 3);
    match q.dir {
        Dir::R => {
            assert(bg[0] =~= config_word(q.c, 0));
            assert(bg[1] =~= signed_power(1, (m * m) as int)) by {
                assert(bg[1] == symbol_power(Symbol::Gen(1), m * m));
            }
            assert(bg[2] =~= signed_power(2, 1)) by {
                assert(bg[2] == symbol_power(Symbol::Gen(2), 1));
            }
            lemma_emb_gsconfig(bg, q.c, 0, m * m, 1, kr, ks, c.e);
            //  per-letter coords:  P = q.c + (m·m)·kr,  Q = ks
            let pp = q.c as int + (m * m) as int * kr;
            let qq = 0 + 1 * ks;
            assert(equiv_in_presentation(p, apply_embedding(bg, g0), gsconfig(pp, qq, c.e)));
            //  quad_step(R) = ((R0/m)·m² + q.c, S0/m) = (kr·m² + q.c, ks)
            let target = quad_step(q, m, R0, S0);
            assert(target.0 == (R0 / m) * (m * m) + q.c && target.1 == S0 / m);
            assert((m * m) as int * kr == kr * (m * m) as int) by (nonlinear_arith);
            assert(target.0 as int == pp) by {
                assert(target.0 == kr * (m * m) + q.c);
                assert((kr * (m * m)) as int == kr * (m * m) as int);
            }
            assert(target.1 as int == qq);
            assert(pp >= 0 && qq >= 0);
            //  mm_yields(R0,S0 → target); step_preserves_h0 ⟹ target ∈ H₀
            assert(mm_yields(mm, R0, S0, target.0, target.1)) by {
                assert(quad_matches(q, m, R0, S0));
                assert(quad_step(mm.quads[qi as int], m, R0, S0) == target);
            }
            lemma_step_preserves_h0(mm, R0, S0, target.0, target.1);
            assert(mm_in_H0(mm, target.0, target.1));
            lemma_gsconfig_in_TM(mm, target.0, target.1, c.e);
            assert(gsconfig(target.0 as int, target.1 as int, c.e) == gsconfig(pp, qq, c.e));
            lemma_equiv_symmetric(p, apply_embedding(bg, g0), gsconfig(pp, qq, c.e));
            lemma_in_subgroup_pred_respects_equiv(p, tm_pred(mm), gsconfig(pp, qq, c.e),
                apply_embedding(bg, g0));
            return;
        }
        Dir::L => {
            assert(bg[0] =~= config_word(0, q.c));
            assert(bg[1] =~= signed_power(1, 1)) by {
                assert(bg[1] == symbol_power(Symbol::Gen(1), 1));
            }
            assert(bg[2] =~= signed_power(2, (m * m) as int)) by {
                assert(bg[2] == symbol_power(Symbol::Gen(2), m * m));
            }
            lemma_emb_gsconfig(bg, 0, q.c, 1, m * m, kr, ks, c.e);
            //  per-letter coords:  P = kr,  Q = q.c + (m·m)·ks
            let pp = 0 + 1 * kr;
            let qq = q.c as int + (m * m) as int * ks;
            assert(equiv_in_presentation(p, apply_embedding(bg, g0), gsconfig(pp, qq, c.e)));
            let target = quad_step(q, m, R0, S0);
            assert(target.0 == R0 / m && target.1 == (S0 / m) * (m * m) + q.c);
            assert((m * m) as int * ks == ks * (m * m) as int) by (nonlinear_arith);
            assert(target.0 as int == pp);
            assert(target.1 as int == qq) by {
                assert(target.1 == ks * (m * m) + q.c);
                assert((ks * (m * m)) as int == ks * (m * m) as int);
            }
            assert(pp >= 0 && qq >= 0);
            assert(mm_yields(mm, R0, S0, target.0, target.1)) by {
                assert(quad_matches(q, m, R0, S0));
                assert(quad_step(mm.quads[qi as int], m, R0, S0) == target);
            }
            lemma_step_preserves_h0(mm, R0, S0, target.0, target.1);
            assert(mm_in_H0(mm, target.0, target.1));
            lemma_gsconfig_in_TM(mm, target.0, target.1, c.e);
            assert(gsconfig(target.0 as int, target.1 as int, c.e) == gsconfig(pp, qq, c.e));
            lemma_equiv_symmetric(p, apply_embedding(bg, g0), gsconfig(pp, qq, c.e));
            lemma_in_subgroup_pred_respects_equiv(p, tm_pred(mm), gsconfig(pp, qq, c.e),
                apply_embedding(bg, g0));
            return;
        }
    }
}

//  ── b-side fold:  apply_embedding(b_gens, red_to_U(red,m)) ∈ T(M). ──
pub proof fn lemma_emb_bside_in_TM(mm: ModMachine, qi: nat, red: Seq<CanonLetter>)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
        forall|i: int| 0 <= i < red.len() ==> {
            &&& (#[trigger] red[i]).r >= 0
            &&& red[i].s >= 0
            &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
            &&& (red[i].r - mm.quads[qi as int].a as int) % (mm.m as int) == 0
            &&& (red[i].s - mm.quads[qi as int].b as int) % (mm.m as int) == 0
        },
    ensures
        in_TM(mm, apply_embedding(hnn_b_gens(quad_data(mm, qi)), red_to_U(red, mm.m as int))),
    decreases red.len(),
{
    let p = base_A();
    lemma_base_A_valid();
    let bg = hnn_b_gens(quad_data(mm, qi));
    let mi = mm.m as int;
    if red.len() == 0 {
        assert(red_to_U(red, mi) =~= empty_word());
        assert(apply_embedding(bg, red_to_U(red, mi)) =~= empty_word()) by {
            reveal_with_fuel(apply_embedding, 2);
        }
        lemma_empty_in_TM(mm);
    } else {
        let c = red[0];
        let rest = red.drop_first();
        assert(red_to_U(red, mi) == letter_to_U(c, mi) + red_to_U(rest, mi));
        lemma_apply_embedding_concat(bg, letter_to_U(c, mi), red_to_U(rest, mi));
        let h = apply_embedding(bg, letter_to_U(c, mi));
        let t = apply_embedding(bg, red_to_U(rest, mi));
        assert(apply_embedding(bg, red_to_U(red, mi)) =~= h + t);
        //  head ∈ T(M)
        assert((red[0]).r >= 0 && red[0].s >= 0
            && mm_in_H0(mm, red[0].r as nat, red[0].s as nat)
            && (red[0].r - mm.quads[qi as int].a as int) % mi == 0
            && (red[0].s - mm.quads[qi as int].b as int) % mi == 0);
        lemma_bside_letter_in_TM(mm, qi, c);
        //  rest ∈ T(M) by IH
        assert(forall|i: int| 0 <= i < rest.len() ==> {
            &&& (#[trigger] rest[i]).r >= 0
            &&& rest[i].s >= 0
            &&& mm_in_H0(mm, rest[i].r as nat, rest[i].s as nat)
            &&& (rest[i].r - mm.quads[qi as int].a as int) % mi == 0
            &&& (rest[i].s - mm.quads[qi as int].b as int) % mi == 0
        }) by {
            assert forall|i: int| 0 <= i < rest.len() implies {
                &&& (#[trigger] rest[i]).r >= 0
                &&& rest[i].s >= 0
                &&& mm_in_H0(mm, rest[i].r as nat, rest[i].s as nat)
                &&& (rest[i].r - mm.quads[qi as int].a as int) % mi == 0
                &&& (rest[i].s - mm.quads[qi as int].b as int) % mi == 0
            } by {
                assert(rest[i] == red[i + 1]);
            }
        }
        lemma_emb_bside_in_TM(mm, qi, rest);
        lemma_product_in_subgroup_pred(p, tm_pred(mm), h, t);
    }
}

} //  verus!
