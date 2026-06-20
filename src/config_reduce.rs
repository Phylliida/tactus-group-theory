//  ============================================================
//  E2.B — config reduction core (property (v) T-free uniqueness).
//  ============================================================
//  Own module (trigger isolation).  See docs/property-v-tfree-architecture.md.
//
//  The config basis {t(r,s)} is free in A.  `lemma_canw_eval_nontrivial` (machine_group.rs) already
//  proves a canw_reduced nonempty word is ≢_A ε — the deep 90%.  This module adds the reduction
//  function + its ≡_A / coordinate lemmas + uniqueness, which promote that single-word fact to the
//  free-group subset-intersection needed by property (v).
//
//  Part A0 (here first): the run-merge and zero-drop atoms the reduction rests on.

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::britton_via_tower::lemma_delete_equiv_empty;

verus! {

//  The inner xy-block of a config conjugate cancels:  xʳ · yˢ · y⁻ˢ · x⁻ʳ ≡ ε.
//  (This is what makes two same-coordinate configs merge.)
pub proof fn lemma_xy_block_cancel(r: int, s: int)
    ensures
        equiv_in_presentation(base_A(),
            signed_power(1, r) + signed_power(2, s) + signed_power(2, -s) + signed_power(1, -r),
            empty_word()),
{
    let a = base_A();
    lemma_base_A_valid();
    let xr = signed_power(1, r);
    let ys = signed_power(2, s);
    let yms = signed_power(2, -s);
    let xmr = signed_power(1, -r);
    //  ys · yms ≡ ε
    lemma_signed_power_add(a, 2, s, -s);
    assert(signed_power(2, s + -s) =~= empty_word());
    assert(equiv_in_presentation(a, ys + yms, empty_word()));
    //  xr · (ys·yms) · xmr ≡ xr · xmr   (delete the ε block)
    lemma_delete_equiv_empty(a, xr, ys + yms, xmr);
    assert(xr + ((ys + yms) + xmr) =~= signed_power(1, r) + signed_power(2, s)
        + signed_power(2, -s) + signed_power(1, -r));
    assert(xr + xmr =~= signed_power(1, r) + signed_power(1, -r));
    //  xr · xmr ≡ ε
    lemma_signed_power_add(a, 1, r, -r);
    assert(signed_power(1, r + -r) =~= empty_word());
    lemma_equiv_transitive(a,
        signed_power(1, r) + signed_power(2, s) + signed_power(2, -s) + signed_power(1, -r),
        xr + xmr,
        empty_word());
}

//  Run-merge atom:  two same-coordinate config powers merge by adding exponents.
//      gsconfig(r,s,e₁) · gsconfig(r,s,e₂)  ≡_A  gsconfig(r,s,e₁+e₂).
pub proof fn lemma_gsconfig_merge(r: int, s: int, e1: int, e2: int)
    ensures
        equiv_in_presentation(base_A(),
            gsconfig(r, s, e1) + gsconfig(r, s, e2),
            gsconfig(r, s, e1 + e2)),
{
    let a = base_A();
    lemma_base_A_valid();
    let yms = signed_power(2, -s);
    let xmr = signed_power(1, -r);
    let xr = signed_power(1, r);
    let ys = signed_power(2, s);
    let t1 = signed_power(0, e1);
    let t2 = signed_power(0, e2);
    let t12 = signed_power(0, e1 + e2);
    //  gsconfig(r,s,e) == yms + xmr + tᵉ + xr + ys  (definitional).
    assert(gsconfig(r, s, e1) =~= yms + xmr + t1 + xr + ys);
    assert(gsconfig(r, s, e2) =~= yms + xmr + t2 + xr + ys);
    //  --- Step 1: delete the inner block  (xr·ys·yms·xmr ≡ ε)  ---
    let blk = xr + ys + yms + xmr;
    lemma_xy_block_cancel(r, s);
    assert(equiv_in_presentation(a, blk, empty_word()));
    let prefix = yms + xmr + t1;
    let suffix = t2 + xr + ys;
    lemma_delete_equiv_empty(a, prefix, blk, suffix);
    //  LHS =~= prefix · blk · suffix
    assert(gsconfig(r, s, e1) + gsconfig(r, s, e2) =~= prefix + (blk + suffix));
    //  prefix · suffix == yms + xmr + t1 + t2 + xr + ys
    assert(prefix + suffix =~= (yms + xmr) + (t1 + t2) + (xr + ys));
    //  --- Step 2: merge t1·t2 ≡ t12 in the middle ---
    lemma_signed_power_add(a, 0, e1, e2);
    assert(equiv_in_presentation(a, t1 + t2, t12));
    lemma_equiv_concat_right(a, yms + xmr, t1 + t2, t12);
    lemma_equiv_concat_left(a, (yms + xmr) + (t1 + t2), (yms + xmr) + t12, xr + ys);
    assert(((yms + xmr) + (t1 + t2)) + (xr + ys) =~= (yms + xmr) + (t1 + t2) + (xr + ys));
    assert(((yms + xmr) + t12) + (xr + ys) =~= gsconfig(r, s, e1 + e2));
    //  --- chain:  LHS =~= prefix·blk·suffix ≡ prefix·suffix ≡ gsconfig(r,s,e1+e2) ---
    lemma_equiv_transitive(a,
        gsconfig(r, s, e1) + gsconfig(r, s, e2),
        prefix + suffix,
        gsconfig(r, s, e1 + e2));
}

//  Zero-drop atom:  a zero-exponent config power is trivial.
//      gsconfig(r,s,0)  ≡_A  ε.
pub proof fn lemma_gsconfig_zero(r: int, s: int)
    ensures
        equiv_in_presentation(base_A(), gsconfig(r, s, 0), empty_word()),
{
    let a = base_A();
    lemma_base_A_valid();
    let yms = signed_power(2, -s);
    let xmr = signed_power(1, -r);
    let xr = signed_power(1, r);
    let ys = signed_power(2, s);
    //  t⁰ = ε, so gsconfig(r,s,0) =~= yms + xmr + xr + ys.
    assert(signed_power(0, 0) =~= empty_word());
    assert(gsconfig(r, s, 0) =~= yms + ((xmr + xr) + ys));
    //  xmr · xr ≡ ε
    lemma_signed_power_add(a, 1, -r, r);
    assert(signed_power(1, -r + r) =~= empty_word());
    assert(equiv_in_presentation(a, xmr + xr, empty_word()));
    //  delete:  yms · (xmr·xr) · ys ≡ yms · ys
    lemma_delete_equiv_empty(a, yms, xmr + xr, ys);
    assert(yms + ((xmr + xr) + ys) =~= yms + ((xmr + xr) + ys));
    //  yms · ys ≡ ε
    lemma_signed_power_add(a, 2, -s, s);
    assert(signed_power(2, -s + s) =~= empty_word());
    assert(equiv_in_presentation(a, yms + ys, empty_word()));
    lemma_equiv_transitive(a, gsconfig(r, s, 0), yms + ys, empty_word());
}

} //  verus!
