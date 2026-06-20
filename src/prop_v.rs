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

//  ============================================================
//  B4b — the quad HNN: validity, associated-subgroup isomorphism, base-faithfulness.
//  ============================================================

pub proof fn lemma_quad_data_valid(mm: ModMachine, qi: nat)
    requires
        qi < mm.quads.len(),
    ensures
        hnn_data_valid(quad_data(mm, qi)),
{
    let data = quad_data(mm, qi);
    lemma_base_A_valid();
    assert(data.base == base_A());
    assert(data.base.num_generators == 3);
    lemma_quad_associations_valid(mm.quads[qi as int], mm.m, 3);
}

//  The quad's associated subgroups are isomorphic (property iii), over the base A directly.
pub proof fn lemma_quad_data_iso(mm: ModMachine, qi: nat)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
    ensures
        hnn_associations_isomorphic(quad_data(mm, qi)),
{
    let data = quad_data(mm, qi);
    let q = mm.quads[qi as int];
    let m = mm.m;
    let k = data.associations.len();
    assert(k == 3);
    assert(m >= 1);
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    assert(a_words =~= seq![config_word(q.a, q.b), symbol_power(Symbol::Gen(1), m),
        symbol_power(Symbol::Gen(2), m)]);
    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word())
    ) by {
        assert(word_valid(w, 3));
        assert(m * m >= 1) by (nonlinear_arith) requires m >= 1;
        assert(apply_embedding(seq![config_word(q.a, q.b), symbol_power(Symbol::Gen(1), m),
            symbol_power(Symbol::Gen(2), m)], w) =~= apply_embedding(a_words, w));
        lemma_conj_scaling_trivial_iff(q.a, q.b, m, m, w);
        match q.dir {
            Dir::R => {
                assert(b_words =~= seq![config_word(q.c, 0), symbol_power(Symbol::Gen(1), m * m),
                    symbol_power(Symbol::Gen(2), 1)]);
                lemma_conj_scaling_trivial_iff(q.c, 0, m * m, 1, w);
            }
            Dir::L => {
                assert(b_words =~= seq![config_word(0, q.c), symbol_power(Symbol::Gen(1), 1),
                    symbol_power(Symbol::Gen(2), m * m)]);
                lemma_conj_scaling_trivial_iff(0, q.c, 1, m * m, w);
            }
        }
    }
}

//  Generic base cancellation:  w1·w2⁻¹ ≡ ε  ⟹  w1 ≡ w2  (in any valid presentation).
//  Pure word algebra; split out of lemma_quad_base_faithful to keep the HNN derivation reasoning
//  (lemma_single_hnn_base_faithful) in its own function context (rlimit).
pub proof fn lemma_equiv_from_concat_inv_trivial(p: Presentation, w1: Word, w2: Word)
    requires
        presentation_valid(p),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
        equiv_in_presentation(p, w1 + inverse_word(w2), empty_word()),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let iw2 = inverse_word(w2);
    let n = p.num_generators;
    lemma_inverse_word_valid(w2, n);
    lemma_concat_word_valid(iw2, w2, n);                  //  word_valid(iw2·w2)
    lemma_concat_word_valid(w1, iw2 + w2, n);             //  word_valid(w1·(iw2·w2))
    let x = w1 + iw2;
    //  x·w2 ≡ w2:  from x ≡ ε,  x·w2 ≡ ε·w2 =~= w2
    lemma_equiv_concat_left(p, x, empty_word(), w2);      //  x·w2 ≡ ε·w2
    lemma_concat_empty_left(w2);                          //  ε·w2 =~= w2
    //  w1 ≡ x·w2:  w1·(w2⁻¹·w2) ≡ w1·ε =~= w1, and x·w2 =~= w1·(w2⁻¹·w2)
    lemma_concat_assoc(w1, iw2, w2);                      //  (w1·w2⁻¹)·w2 =~= w1·(w2⁻¹·w2)
    lemma_word_inverse_left(p, w2);                       //  w2⁻¹·w2 ≡ ε
    lemma_equiv_concat_right(p, w1, iw2 + w2, empty_word());  //  w1·(w2⁻¹·w2) ≡ w1·ε
    lemma_concat_empty_right(w1);                         //  w1·ε =~= w1
    assert(x + w2 =~= w1 + (iw2 + w2));
    //  w1·(w2⁻¹·w2) ≡ w1, symmetric ⟹ w1 ≡ w1·(w2⁻¹·w2) =~= x·w2
    lemma_equiv_symmetric(p, w1 + (iw2 + w2), w1);        //  w1 ≡ x·w2
    //  combine:  w1 ≡ x·w2 ≡ w2
    lemma_equiv_transitive(p, w1, x + w2, w2);
}

//  Two-word base-faithfulness:  w1 ≡ w2 in the quad HNN ⟹ w1 ≡ w2 in base A (both base words).
pub proof fn lemma_quad_base_faithful(mm: ModMachine, qi: nat, w1: Word, w2: Word)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
        word_valid(w1, 3),
        word_valid(w2, 3),
        equiv_in_presentation(hnn_presentation(quad_data(mm, qi)), w1, w2),
    ensures
        equiv_in_presentation(base_A(), w1, w2),
{
    let data = quad_data(mm, qi);
    let hp = hnn_presentation(data);
    let p = base_A();
    lemma_base_A_valid();
    lemma_quad_data_valid(mm, qi);
    lemma_quad_data_iso(mm, qi);
    assert(data.base == p && data.base.num_generators == 3);
    let iw2 = inverse_word(w2);
    lemma_inverse_word_valid(w2, 3);
    lemma_concat_word_valid(w1, iw2, 3);
    //  (a)  w1 ≡_hp w2  ⟹  w1·w2⁻¹ ≡_hp ε
    lemma_equiv_concat_left(hp, w1, w2, iw2);             //  w1·w2⁻¹ ≡ w2·w2⁻¹
    lemma_word_inverse_right(hp, w2);                     //  w2·w2⁻¹ ≡ ε
    lemma_equiv_transitive(hp, w1 + iw2, w2 + iw2, empty_word());
    //  base-faithful (single):  w1·w2⁻¹ ≡_A ε
    lemma_single_hnn_base_faithful(data, w1 + iw2);
    //  (b)  w1·w2⁻¹ ≡_A ε  ⟹  w1 ≡_A w2  (generic helper)
    lemma_equiv_from_concat_inv_trivial(p, w1, w2);
}

//  ============================================================
//  B6 — the forward direction (A→B) and prop_v assembly.
//  ============================================================

//  red_to_U is a valid word over the 3 base generators.
pub proof fn lemma_red_to_U_valid(red: Seq<CanonLetter>, m: int)
    ensures
        word_valid(red_to_U(red, m), 3),
    decreases red.len(),
{
    if red.len() == 0 {
        assert(red_to_U(red, m) =~= empty_word());
        assert(word_valid(empty_word(), 3));
    } else {
        let c = red[0];
        lemma_gsconfig_valid(c.r / m, c.s / m, c.e);
        assert(letter_to_U(c, m) == gsconfig(c.r / m, c.s / m, c.e));
        lemma_red_to_U_valid(red.drop_first(), m);
        lemma_concat_word_valid(letter_to_U(c, m), red_to_U(red.drop_first(), m), 3);
        assert(red_to_U(red, m) == letter_to_U(c, m) + red_to_U(red.drop_first(), m));
    }
}

//  Forward direction of property (v):  in_TM(emb(a_gens,uw)) ⟹ in_TM(emb(b_gens,uw)).
#[verifier::rlimit(400)]
pub proof fn lemma_prop_v_AtoB(mm: ModMachine, qi: nat, uw: Word)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
        word_valid(uw, 3),
        in_TM(mm, apply_embedding(hnn_a_gens(quad_data(mm, qi)), uw)),
    ensures
        in_TM(mm, apply_embedding(hnn_b_gens(quad_data(mm, qi)), uw)),
{
    let p = base_A();
    lemma_base_A_valid();
    let data = quad_data(mm, qi);
    let hp = hnn_presentation(data);
    let q = mm.quads[qi as int];
    let m = mm.m;
    let mi = m as int;
    let ag = hnn_a_gens(data);
    let bg = hnn_b_gens(data);
    let g_a = apply_embedding(ag, uw);
    let g_b = apply_embedding(bg, uw);
    lemma_quad_data_valid(mm, qi);
    lemma_hnn_presentation_valid(data);              //  presentation_valid(hp)
    lemma_quad_a_gens_form(mm, qi);                  //  ag =~= [config(q.a,q.b), x^m, y^m] (signed)
    assert(q.a < m && q.b < m) by { assert(quad_wf(q, m)); }
    assert(ag.len() == 3 && bg.len() == 3);
    lemma_quad_associations_valid(q, m, 3);
    assert(forall|i: int| 0 <= i < ag.len() ==> word_valid(#[trigger] ag[i], 3)) by {
        assert forall|i: int| 0 <= i < ag.len() implies word_valid(#[trigger] ag[i], 3) by {
            assert(ag[i] == quad_associations(q, m)[i].0);
        }
    }
    assert(forall|i: int| 0 <= i < bg.len() ==> word_valid(#[trigger] bg[i], 3)) by {
        assert forall|i: int| 0 <= i < bg.len() implies word_valid(#[trigger] bg[i], 3) by {
            assert(bg[i] == quad_associations(q, m)[i].1);
        }
    }
    lemma_apply_embedding_valid(ag, uw, 3);          //  word_valid(g_a, 3)
    lemma_apply_embedding_valid(bg, uw, 3);          //  word_valid(g_b, 3)

    //  Step 1: reduced config form red (coords in H₀ ∩ residue).
    lemma_emb_a_reduced(mm, qi, uw);
    let red = choose|red: Seq<CanonLetter>| {
        &&& canw_reduced(red)
        &&& equiv_in_presentation(p, canw_eval(red), g_a)
        &&& (forall|i: int| 0 <= i < red.len() ==> {
                &&& (#[trigger] red[i]).r >= 0
                &&& red[i].s >= 0
                &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
                &&& (red[i].r - q.a as int) % mi == 0
                &&& (red[i].s - q.b as int) % mi == 0
            })
    };
    assert(canw_reduced(red) && equiv_in_presentation(p, canw_eval(red), g_a)
        && (forall|i: int| 0 <= i < red.len() ==> {
                &&& (#[trigger] red[i]).r >= 0
                &&& red[i].s >= 0
                &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
                &&& (red[i].r - q.a as int) % mi == 0
                &&& (red[i].s - q.b as int) % mi == 0
            }));

    let big_u = red_to_U(red, mi);
    lemma_red_to_U_valid(red, mi);                   //  word_valid(big_u, 3)
    //  a-side equality: apply_embedding(ag, big_u) ≡_A canw_eval(red)
    assert(ag[0] =~= config_word(q.a, q.b));
    assert(ag[1] =~= signed_power(1, mi));
    assert(ag[2] =~= signed_power(2, mi));
    lemma_emb_aside_eq(ag, red, q.a, q.b, m);
    let a_u = apply_embedding(ag, big_u);
    lemma_apply_embedding_valid(ag, big_u, 3);       //  word_valid(a_u, 3)
    //  g_a ≡_A a_u   (a_u ≡ canw_eval(red) ≡ g_a, then symm)
    lemma_equiv_transitive(p, a_u, canw_eval(red), g_a);
    lemma_equiv_symmetric(p, a_u, g_a);
    //  base embeds: g_a ≡_hp a_u
    lemma_base_embeds_in_hnn(data, g_a, a_u);

    //  Conjugation in the HNN presentation.
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    let png = hp.num_generators;
    assert(png == 4);
    assert(st == Symbol::Gen(3) && si == Symbol::Inv(3));
    lemma_stable_conj_factorization(data, uw);       //  [si]+g_a+[st] ≡_hp g_b
    lemma_stable_conj_factorization(data, big_u);    //  [si]+a_u+[st] ≡_hp b_u
    let b_u = apply_embedding(bg, big_u);
    let lhs_uw = seq![si] + g_a + seq![st];
    let lhs_u = seq![si] + a_u + seq![st];
    //  validity of lhs_uw over the HNN generators (for symmetry)
    lemma_word_valid_mono(g_a, 3, png);
    assert(word_valid(seq![si], png)) by {
        assert forall|t: int| 0 <= t < 1 implies symbol_valid(#[trigger] seq![si][t], png) by { }
    }
    assert(word_valid(seq![st], png)) by {
        assert forall|t: int| 0 <= t < 1 implies symbol_valid(#[trigger] seq![st][t], png) by { }
    }
    lemma_concat_word_valid(seq![si], g_a, png);
    lemma_concat_word_valid(seq![si] + g_a, seq![st], png);
    assert(lhs_uw =~= (seq![si] + g_a) + seq![st]);
    assert(word_valid(lhs_uw, png));
    //  congruence:  lhs_uw ≡_hp lhs_u   (from g_a ≡_hp a_u)
    lemma_equiv_concat_right(hp, seq![si], g_a, a_u);
    lemma_equiv_concat_left(hp, seq![si] + g_a, seq![si] + a_u, seq![st]);
    assert(lhs_uw =~= (seq![si] + g_a) + seq![st]);
    assert(lhs_u =~= (seq![si] + a_u) + seq![st]);
    //  chain:  g_b ≡ lhs_uw ≡ lhs_u ≡ b_u
    lemma_equiv_transitive(hp, lhs_uw, lhs_u, b_u);  //  lhs_uw ≡ b_u
    lemma_equiv_symmetric(hp, lhs_uw, g_b);          //  g_b ≡ lhs_uw
    lemma_equiv_transitive(hp, g_b, lhs_uw, b_u);    //  g_b ≡ b_u
    //  base-faithful: g_b ≡_A b_u
    lemma_apply_embedding_valid(bg, big_u, 3);       //  word_valid(b_u, 3)
    lemma_quad_base_faithful(mm, qi, g_b, b_u);
    //  b_u ∈ T(M); respects_equiv ⟹ g_b ∈ T(M)
    lemma_emb_bside_in_TM(mm, qi, red);
    lemma_equiv_symmetric(p, g_b, b_u);              //  b_u ≡_A g_b
    lemma_in_subgroup_pred_respects_equiv(p, tm_pred(mm), b_u, g_b);
}

//  ============================================================
//  B6-REV — the reverse direction (B→A).
//  ============================================================
//  The b-side is acc_gens(c,0,m²,1) [R] / acc_gens(0,c,1,m²) [L], with ASYMMETRIC moduli, so the
//  single-modulus ii_subset reduction (lemma_emb_a_reduced) does not apply.  Instead we get the
//  residue factorization directly from lemma_accumulator_inv and feed it into a generic reduction
//  core.  Mirror of A→B with the conjugation reversed and step_preserves_h0 used backwards (it is an
//  iff).  See docs/property-v-tfree-architecture.md, B6 "B→A".

//  Generic reduction core:  in_TM(g) ∧ canw_eval(qa) ≡_A g  ⟹  red = cw_reduce(qa) is reduced,
//  ≡_A g, and every coordinate is BOTH H₀ AND a coordinate of qa.  (Factors lemma_in_TM_residue_reduced
//  so the residue form qa can come from the accumulator with arbitrary moduli — the residue property
//  of red's coords then follows from coord_in(qa,·) at the call site.)
pub proof fn lemma_in_TM_canon_reduced(mm: ModMachine, g: Word, qa: Seq<CanonLetter>)
    requires
        in_TM(mm, g),
        equiv_in_presentation(base_A(), canw_eval(qa), g),
    ensures
        canw_reduced(cw_reduce(qa)),
        equiv_in_presentation(base_A(), canw_eval(cw_reduce(qa)), g),
        forall|i: int| 0 <= i < cw_reduce(qa).len() ==> {
            &&& (#[trigger] cw_reduce(qa)[i]).r >= 0
            &&& cw_reduce(qa)[i].s >= 0
            &&& mm_in_H0(mm, cw_reduce(qa)[i].r as nat, cw_reduce(qa)[i].s as nat)
            &&& coord_in(qa, cw_reduce(qa)[i].r, cw_reduce(qa)[i].s)
        },
{
    let a = base_A();
    lemma_base_A_valid();
    let p_canon = lemma_in_TM_to_canon(mm, g);           //  canw_eval(p_canon) ≡ g, coords ∈ H₀
    lemma_canw_eval_valid(p_canon);
    lemma_equiv_symmetric(a, canw_eval(p_canon), g);
    lemma_equiv_transitive(a, canw_eval(qa), g, canw_eval(p_canon));   //  canw(qa) ≡ canw(p_canon)
    let red = cw_reduce(qa);
    lemma_cw_reduce_reduced(qa);                          //  canw_reduced(red)
    lemma_cw_reduce_eval(qa);                             //  canw_eval(red) ≡ canw_eval(qa) ≡ g
    lemma_equiv_transitive(a, canw_eval(red), canw_eval(qa), g);
    lemma_cw_reduce_coords(qa);                           //  coord_in(red) ⟹ coord_in(qa)
    assert forall|i: int| 0 <= i < red.len() implies {
        &&& (#[trigger] red[i]).r >= 0
        &&& red[i].s >= 0
        &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
        &&& coord_in(qa, red[i].r, red[i].s)
    } by {
        let r = red[i].r;
        let s = red[i].s;
        assert(coord_in(red, r, s)) by { assert(red[i].r == r && red[i].s == s); }
        assert(coord_in(qa, r, s));                       //  from lemma_cw_reduce_coords
        lemma_tfree_coord_restrict(qa, p_canon, r, s);    //  ⟹ coord_in(p_canon, r, s)
        let jp = choose|j: int| 0 <= j < p_canon.len() && p_canon[j].r == r && p_canon[j].s == s;
        assert(0 <= jp < p_canon.len() && p_canon[jp].r == r && p_canon[jp].s == s);
        assert(p_canon[jp].r >= 0 && p_canon[jp].s >= 0
            && mm_in_H0(mm, p_canon[jp].r as nat, p_canon[jp].s as nat));
    }
}

//  ── 2-modulus U-fold (for the asymmetric b-side: divide r by mr, s by ms). ──
pub open spec fn letter_to_U2(c: CanonLetter, mr: int, ms: int) -> Word {
    gsconfig(c.r / mr, c.s / ms, c.e)
}

pub open spec fn red_to_U2(red: Seq<CanonLetter>, mr: int, ms: int) -> Word
    decreases red.len(),
{
    if red.len() == 0 {
        empty_word()
    } else {
        letter_to_U2(red[0], mr, ms) + red_to_U2(red.drop_first(), mr, ms)
    }
}

//  ── b-side residue parameters:  acc_gens(b_aa,b_bb,b_mr,b_ms) == hnn_b_gens(quad_data). ──
//  R: (c,0) with moduli (m²,1);  L: (0,c) with moduli (1,m²).
pub open spec fn b_aa(q: Quad) -> nat { match q.dir { Dir::R => q.c, Dir::L => 0 } }
pub open spec fn b_bb(q: Quad) -> nat { match q.dir { Dir::R => 0, Dir::L => q.c } }
pub open spec fn b_mr(q: Quad, m: nat) -> nat { match q.dir { Dir::R => m * m, Dir::L => 1 } }
pub open spec fn b_ms(q: Quad, m: nat) -> nat { match q.dir { Dir::R => 1, Dir::L => m * m } }

pub proof fn lemma_quad_b_gens_form(mm: ModMachine, qi: nat)
    requires
        qi < mm.quads.len(),
    ensures
        hnn_b_gens(quad_data(mm, qi)) =~= acc_gens(b_aa(mm.quads[qi as int]),
            b_bb(mm.quads[qi as int]), b_mr(mm.quads[qi as int], mm.m), b_ms(mm.quads[qi as int], mm.m)),
{
    let q = mm.quads[qi as int];
    let m = mm.m;
    let bg = hnn_b_gens(quad_data(mm, qi));
    let assoc = quad_associations(q, m);
    let ag2 = acc_gens(b_aa(q), b_bb(q), b_mr(q, m), b_ms(q, m));
    assert(bg.len() == 3 && ag2.len() == 3);
    assert(bg[0] == assoc[0].1 && bg[1] == assoc[1].1 && bg[2] == assoc[2].1);
    match q.dir {
        Dir::R => {
            assert(b_aa(q) == q.c && b_bb(q) == 0 && b_mr(q, m) == m * m && b_ms(q, m) == 1);
            assert(bg[0] == config_word(q.c, 0));
            assert(bg[1] == symbol_power(Symbol::Gen(1), m * m));
            assert(bg[2] == symbol_power(Symbol::Gen(2), 1));
        }
        Dir::L => {
            assert(b_aa(q) == 0 && b_bb(q) == q.c && b_mr(q, m) == 1 && b_ms(q, m) == m * m);
            assert(bg[0] == config_word(0, q.c));
            assert(bg[1] == symbol_power(Symbol::Gen(1), 1));
            assert(bg[2] == symbol_power(Symbol::Gen(2), m * m));
        }
    }
}

//  ── a-side per b-residue letter:  apply_embedding(a_gens, letter_to_U2(c, m²,1)) ∈ T(M). ──
//  Mirror of lemma_bside_letter_in_TM: each b-residue config letter c=(R,S)∈H₀ maps under the a-gens
//  to a config at the quad_step PRE-image, which is in H₀ by the reverse of step_preserves_h0 (an iff).
#[verifier::rlimit(300)]
pub proof fn lemma_aside_letter_in_TM(mm: ModMachine, qi: nat, c: CanonLetter)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
        c.r >= 0,
        c.s >= 0,
        mm_in_H0(mm, c.r as nat, c.s as nat),
        (c.r - b_aa(mm.quads[qi as int]) as int) % (b_mr(mm.quads[qi as int], mm.m) as int) == 0,
        (c.s - b_bb(mm.quads[qi as int]) as int) % (b_ms(mm.quads[qi as int], mm.m) as int) == 0,
    ensures
        in_TM(mm, apply_embedding(hnn_a_gens(quad_data(mm, qi)),
            letter_to_U2(c, b_mr(mm.quads[qi as int], mm.m) as int, b_ms(mm.quads[qi as int], mm.m) as int))),
{
    let p = base_A();
    lemma_base_A_valid();
    let q = mm.quads[qi as int];
    let m = mm.m;
    let ag = hnn_a_gens(quad_data(mm, qi));
    assert(q.a < m && q.b < m && q.c < m * m) by { assert(quad_wf(q, m)); }
    lemma_quad_a_gens_form(mm, qi);                     //  ag =~= [config(a,b), x^m, y^m]
    let mri = b_mr(q, m) as int;
    let msi = b_ms(q, m) as int;
    let kr = c.r / mri;
    let ks = c.s / msi;
    let g0 = letter_to_U2(c, mri, msi);
    assert(g0 == gsconfig(kr, ks, c.e));
    lemma_quad_associations_valid(q, m, 3);
    lemma_gsconfig_valid(kr, ks, c.e);
    assert(forall|i: int| 0 <= i < ag.len() ==> word_valid(#[trigger] ag[i], 3)) by {
        assert forall|i: int| 0 <= i < ag.len() implies word_valid(#[trigger] ag[i], 3) by {
            assert(ag[i] == quad_associations(q, m)[i].0);
        }
    }
    lemma_apply_embedding_valid(ag, g0, 3);
    //  a-side image:  emb(ag, gsconfig(kr,ks,e)) ≡ gsconfig(a + m·kr, b + m·ks, e)
    lemma_emb_gsconfig(ag, q.a, q.b, m, m, kr, ks, c.e);
    let pp = q.a as int + (m as int) * kr;
    let qq = q.b as int + (m as int) * ks;
    assert(equiv_in_presentation(p, apply_embedding(ag, g0), gsconfig(pp, qq, c.e)));
    assert(kr >= 0 && ks >= 0);
    assert(pp >= 0 && qq >= 0);
    let ppn = pp as nat;
    let qqn = qq as nat;
    //  nat coords of the preimage; their residues are (a,b), quotients (kr,ks)
    assert((m as int) * kr == kr * (m as int)) by (nonlinear_arith);
    assert((m as int) * ks == ks * (m as int)) by (nonlinear_arith);
    assert(pp == kr * (m as int) + q.a as int);
    assert(qq == ks * (m as int) + q.b as int);
    assert((q.a as int) >= 0 && (q.a as int) < (m as int) && (q.b as int) >= 0 && (q.b as int) < (m as int));
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(pp, m as int, kr, q.a as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(qq, m as int, ks, q.b as int);
    lemma_nat_div_int(pp, m as int);                 //  nat % / int % bridge for pp
    lemma_nat_div_int(qq, m as int);                 //  nat % / int % bridge for qq
    assert(ppn % m == q.a && qqn % m == q.b);
    assert(ppn / m == kr && qqn / m == ks);
    //  quad_step(pp,qq) == (c.r, c.s)
    let target = quad_step(q, m, ppn, qqn);
    match q.dir {
        Dir::R => {
            assert(mri == (m * m) as int && msi == 1);
            //  residue recon on r:  c + m²·kr == c.r ;  s free (ms=1 ⟹ ks = c.s)
            lemma_residue_recon(c.r, q.c as int, mri);   //  q.c + m²·(c.r/m²) == c.r
            assert(q.c as int + mri * kr == c.r);
            assert(ks == c.s) by { assert(c.s / 1 == c.s); }
            assert(target.0 == (ppn / m) * (m * m) + q.c && target.1 == qqn / m);
            assert(target.0 == kr * (m * m) + q.c);
            assert((kr * (m * m)) as int == kr * (m * m) as int);
            assert(mri * kr == kr * (m * m) as int) by (nonlinear_arith) requires mri == (m * m) as int;
            assert(target.0 as int == c.r);
            assert(target.1 as int == c.s);
        }
        Dir::L => {
            assert(mri == 1 && msi == (m * m) as int);
            lemma_residue_recon(c.s, q.c as int, msi);   //  q.c + m²·(c.s/m²) == c.s
            assert(q.c as int + msi * ks == c.s);
            assert(kr == c.r) by { assert(c.r / 1 == c.r); }
            assert(target.0 == ppn / m && target.1 == (qqn / m) * (m * m) + q.c);
            assert(target.1 == ks * (m * m) + q.c);
            assert((ks * (m * m)) as int == ks * (m * m) as int);
            assert(msi * ks == ks * (m * m) as int) by (nonlinear_arith) requires msi == (m * m) as int;
            assert(target.0 as int == c.r);
            assert(target.1 as int == c.s);
        }
    }
    assert(target == (c.r as nat, c.s as nat));
    //  mm_yields(pp,qq → c.r,c.s) ; (c.r,c.s)∈H₀ ; step_preserves_h0 (⟸) ⟹ (pp,qq)∈H₀
    assert(mm_yields(mm, ppn, qqn, c.r as nat, c.s as nat)) by {
        assert(quad_matches(q, m, ppn, qqn));
        assert(quad_step(mm.quads[qi as int], m, ppn, qqn) == (c.r as nat, c.s as nat));
    }
    lemma_step_preserves_h0(mm, ppn, qqn, c.r as nat, c.s as nat);
    assert(mm_in_H0(mm, ppn, qqn));
    lemma_gsconfig_in_TM(mm, ppn, qqn, c.e);
    assert(gsconfig(ppn as int, qqn as int, c.e) == gsconfig(pp, qq, c.e));
    lemma_equiv_symmetric(p, apply_embedding(ag, g0), gsconfig(pp, qq, c.e));
    lemma_in_subgroup_pred_respects_equiv(p, tm_pred(mm), gsconfig(pp, qq, c.e),
        apply_embedding(ag, g0));
}

pub proof fn lemma_red_to_U2_valid(red: Seq<CanonLetter>, mr: int, ms: int)
    ensures
        word_valid(red_to_U2(red, mr, ms), 3),
    decreases red.len(),
{
    if red.len() == 0 {
        assert(red_to_U2(red, mr, ms) =~= empty_word());
    } else {
        let c = red[0];
        lemma_gsconfig_valid(c.r / mr, c.s / ms, c.e);
        lemma_red_to_U2_valid(red.drop_first(), mr, ms);
        lemma_concat_word_valid(letter_to_U2(c, mr, ms), red_to_U2(red.drop_first(), mr, ms), 3);
    }
}

//  2-modulus reconstruction:  apply_embedding(acc_gens(aa,bb,mr,ms), red_to_U2(red,mr,ms)) ≡_A
//  canw_eval(red),  when every coordinate of red lies in the residue class (aa mod mr, bb mod ms).
//  Generalizes lemma_emb_aside_eq (mr=ms=m) to the asymmetric b-side.
pub proof fn lemma_emb_accgens_eq(gens: Seq<Word>, red: Seq<CanonLetter>, aa: nat, bb: nat, mr: nat, ms: nat)
    requires
        mr > 0,
        ms > 0,
        aa < mr,
        bb < ms,
        gens.len() == 3,
        gens[0] =~= config_word(aa, bb),
        gens[1] =~= signed_power(1, mr as int),
        gens[2] =~= signed_power(2, ms as int),
        forall|i: int| 0 <= i < red.len() ==> {
            &&& (#[trigger] red[i]).r >= 0
            &&& red[i].s >= 0
            &&& (red[i].r - aa as int) % (mr as int) == 0
            &&& (red[i].s - bb as int) % (ms as int) == 0
        },
    ensures
        equiv_in_presentation(base_A(), apply_embedding(gens, red_to_U2(red, mr as int, ms as int)),
            canw_eval(red)),
    decreases red.len(),
{
    let p = base_A();
    lemma_base_A_valid();
    let mri = mr as int;
    let msi = ms as int;
    if red.len() == 0 {
        assert(red_to_U2(red, mri, msi) =~= empty_word());
        assert(apply_embedding(gens, red_to_U2(red, mri, msi)) =~= empty_word()) by {
            reveal_with_fuel(apply_embedding, 2);
        }
        assert(canw_eval(red) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
    } else {
        let c = red[0];
        let rest = red.drop_first();
        assert(red_to_U2(red, mri, msi) == letter_to_U2(c, mri, msi) + red_to_U2(rest, mri, msi));
        lemma_apply_embedding_concat(gens, letter_to_U2(c, mri, msi), red_to_U2(rest, mri, msi));
        let ae_head = apply_embedding(gens, letter_to_U2(c, mri, msi));
        let ae_rest = apply_embedding(gens, red_to_U2(rest, mri, msi));
        assert(apply_embedding(gens, red_to_U2(red, mri, msi)) =~= ae_head + ae_rest);
        //  head: per-letter lemma with px=mr, py=ms, k=c.r/mri, l=c.s/msi
        lemma_emb_gsconfig(gens, aa, bb, mr, ms, c.r / mri, c.s / msi, c.e);
        assert((red[0]).r >= 0 && red[0].s >= 0
            && (red[0].r - aa as int) % mri == 0 && (red[0].s - bb as int) % msi == 0);
        lemma_residue_recon(c.r, aa as int, mri);
        lemma_residue_recon(c.s, bb as int, msi);
        assert(aa as int + mri * (c.r / mri) == c.r);
        assert(bb as int + msi * (c.s / msi) == c.s);
        assert(gsconfig(aa as int + mri * (c.r / mri), bb as int + msi * (c.s / msi), c.e)
            == gsconfig(c.r, c.s, c.e));
        assert(ae_head == apply_embedding(gens, gsconfig(c.r / mri, c.s / msi, c.e)));
        assert(equiv_in_presentation(p, ae_head, canl_eval(c)));
        //  rest: IH
        assert(forall|i: int| 0 <= i < rest.len() ==> {
            &&& (#[trigger] rest[i]).r >= 0
            &&& rest[i].s >= 0
            &&& (rest[i].r - aa as int) % mri == 0
            &&& (rest[i].s - bb as int) % msi == 0
        }) by {
            assert forall|i: int| 0 <= i < rest.len() implies {
                &&& (#[trigger] rest[i]).r >= 0
                &&& rest[i].s >= 0
                &&& (rest[i].r - aa as int) % mri == 0
                &&& (rest[i].s - bb as int) % msi == 0
            } by {
                assert(rest[i] == red[i + 1]);
            }
        }
        lemma_emb_accgens_eq(gens, rest, aa, bb, mr, ms);
        assert(equiv_in_presentation(p, ae_rest, canw_eval(rest)));
        //  congruence:  ae_head + ae_rest ≡ canl_eval(c) + canw_eval(rest) = canw_eval(red)
        lemma_equiv_concat_left(p, ae_head, canl_eval(c), ae_rest);
        lemma_equiv_concat_right(p, canl_eval(c), ae_rest, canw_eval(rest));
        lemma_equiv_transitive(p, ae_head + ae_rest, canl_eval(c) + ae_rest,
            canl_eval(c) + canw_eval(rest));
        assert(canw_eval(red) == canl_eval(c) + canw_eval(rest));
        lemma_equiv_refl(p, apply_embedding(gens, red_to_U2(red, mri, msi)));
        lemma_equiv_transitive(p, apply_embedding(gens, red_to_U2(red, mri, msi)), ae_head + ae_rest,
            canw_eval(red));
    }
}

} //  verus!
