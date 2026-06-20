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

//  ============================================================
//  A1 — the reduction function (stack fold, back-to-front).
//  ============================================================
//  Process the word right-to-left, consing each letter onto the front of an already-reduced
//  accumulator.  Front-consing matches canw_eval's front fold, so the ≡_A step needs no snoc lemma.
//  cw_cons drops zero-exponent letters and merges a letter into an equal-coordinate front letter
//  (cancelling if the exponents sum to zero).

pub open spec fn cw_cons(c: CanonLetter, acc: Seq<CanonLetter>) -> Seq<CanonLetter> {
    if c.e == 0 {
        acc
    } else if acc.len() > 0 && acc[0].r == c.r && acc[0].s == c.s {
        let me = c.e + acc[0].e;
        if me == 0 {
            acc.drop_first()
        } else {
            seq![CanonLetter { r: c.r, s: c.s, e: me }] + acc.drop_first()
        }
    } else {
        seq![c] + acc
    }
}

pub open spec fn cw_reduce_from(w: Seq<CanonLetter>, acc: Seq<CanonLetter>) -> Seq<CanonLetter>
    decreases w.len(),
{
    if w.len() == 0 {
        acc
    } else {
        cw_cons(w[0], cw_reduce_from(w.drop_first(), acc))
    }
}

pub open spec fn cw_reduce(w: Seq<CanonLetter>) -> Seq<CanonLetter> {
    cw_reduce_from(w, Seq::<CanonLetter>::empty())
}

//  ============================================================
//  A2 — reduction preserves the evaluated element (≡_A).
//  ============================================================

//  Per-step:  canw_eval(cw_cons(c, acc))  ≡_A  canl_eval(c) · canw_eval(acc).
pub proof fn lemma_cw_cons_eval(c: CanonLetter, acc: Seq<CanonLetter>)
    ensures
        equiv_in_presentation(base_A(), canw_eval(cw_cons(c, acc)),
            canl_eval(c) + canw_eval(acc)),
{
    let a = base_A();
    lemma_base_A_valid();
    lemma_canl_eval_valid(c);
    lemma_canw_eval_valid(acc);
    lemma_concat_word_valid(canl_eval(c), canw_eval(acc), 3);   //  word_valid(lhs, 3)
    let res = cw_cons(c, acc);
    if c.e == 0 {
        //  drop:  canl_eval(c) = gsconfig(r,s,0) ≡ ε, so canl(c)·canw(acc) ≡ canw(acc) = canw(res).
        lemma_gsconfig_zero(c.r, c.s);
        assert(canl_eval(c) =~= gsconfig(c.r, c.s, 0));
        lemma_equiv_refl(a, canw_eval(acc));
        lemma_equiv_concat_left(a, canl_eval(c), empty_word(), canw_eval(acc));
        assert(empty_word() + canw_eval(acc) =~= canw_eval(acc));
        lemma_equiv_symmetric(a, canl_eval(c) + canw_eval(acc), canw_eval(acc));
    } else if acc.len() > 0 && acc[0].r == c.r && acc[0].s == c.s {
        let me = c.e + acc[0].e;
        //  canw_eval(acc) = canl_eval(acc[0]) · canw_eval(acc.drop_first())   (front unfold)
        assert(canw_eval(acc) =~= canl_eval(acc[0]) + canw_eval(acc.drop_first()));
        //  canl_eval(c) · canl_eval(acc[0]) = gsconfig(r,s,c.e)·gsconfig(r,s,acc0.e) ≡ gsconfig(r,s,me)
        lemma_gsconfig_merge(c.r, c.s, c.e, acc[0].e);
        assert(canl_eval(c) =~= gsconfig(c.r, c.s, c.e));
        assert(canl_eval(acc[0]) =~= gsconfig(c.r, c.s, acc[0].e));
        let rest = canw_eval(acc.drop_first());
        if me == 0 {
            //  cancel:  res = acc.drop_first();  canl(c)·canw(acc) ≡ gsconfig(r,s,0)·rest ≡ ε·rest = rest.
            lemma_gsconfig_zero(c.r, c.s);
            //  canl(c)·canl(acc0) ≡ gsconfig(r,s,me)=gsconfig(r,s,0) ≡ ε
            lemma_equiv_transitive(a, canl_eval(c) + canl_eval(acc[0]),
                gsconfig(c.r, c.s, me), empty_word());
            assert(canl_eval(c) + canw_eval(acc) =~= (canl_eval(c) + canl_eval(acc[0])) + rest);
            lemma_equiv_concat_left(a, canl_eval(c) + canl_eval(acc[0]), empty_word(), rest);
            assert(empty_word() + rest =~= rest);
            assert(res =~= acc.drop_first());
            lemma_equiv_symmetric(a, canl_eval(c) + canw_eval(acc), rest);
        } else {
            //  merge:  res = [merged] · acc.drop_first();  canw(res) = canl(merged)·rest = gsconfig(r,s,me)·rest.
            let merged = CanonLetter { r: c.r, s: c.s, e: me };
            assert(res =~= seq![merged] + acc.drop_first());
            assert(res.len() > 0);
            assert(res[0] == merged);
            assert(res.drop_first() =~= acc.drop_first());
            assert(canw_eval(res) =~= canl_eval(res[0]) + canw_eval(res.drop_first()));
            assert(canw_eval(res) =~= canl_eval(merged) + rest);
            assert(canl_eval(merged) =~= gsconfig(c.r, c.s, me));
            //  canl(c)·canw(acc) ≡ (gsconfig(r,s,me))·rest = canw(res)
            assert(canl_eval(c) + canw_eval(acc) =~= (canl_eval(c) + canl_eval(acc[0])) + rest);
            lemma_equiv_concat_left(a, canl_eval(c) + canl_eval(acc[0]), gsconfig(c.r, c.s, me), rest);
            lemma_equiv_symmetric(a, canl_eval(c) + canw_eval(acc), canw_eval(res));
        }
    } else {
        //  prepend:  res = [c] · acc;  canw(res) = canl(c)·canw(acc) literally.
        assert(res =~= seq![c] + acc);
        assert(res.len() > 0);
        assert(res[0] == c);
        assert(res.drop_first() =~= acc);
        assert(canw_eval(res) =~= canl_eval(res[0]) + canw_eval(res.drop_first()));
        assert(canw_eval(res) =~= canl_eval(c) + canw_eval(acc));
        lemma_equiv_refl(a, canw_eval(res));
    }
}

//  Fold:  canw_eval(cw_reduce_from(w, acc))  ≡_A  canw_eval(w) · canw_eval(acc).
pub proof fn lemma_cw_reduce_from_eval(w: Seq<CanonLetter>, acc: Seq<CanonLetter>)
    ensures
        equiv_in_presentation(base_A(), canw_eval(cw_reduce_from(w, acc)),
            canw_eval(w) + canw_eval(acc)),
    decreases w.len(),
{
    let a = base_A();
    lemma_base_A_valid();
    if w.len() == 0 {
        assert(canw_eval(w) =~= empty_word());
        assert(cw_reduce_from(w, acc) =~= acc);
        assert(canw_eval(w) + canw_eval(acc) =~= canw_eval(acc));
        lemma_equiv_refl(a, canw_eval(acc));
    } else {
        let inner = cw_reduce_from(w.drop_first(), acc);
        //  per-step:  canw(cw_cons(w[0], inner)) ≡ canl(w[0])·canw(inner)
        lemma_cw_cons_eval(w[0], inner);
        //  IH:  canw(inner) ≡ canw(w.drop_first())·canw(acc)
        lemma_cw_reduce_from_eval(w.drop_first(), acc);
        //  canl(w[0])·canw(inner) ≡ canl(w[0])·(canw(w.drop_first())·canw(acc))
        lemma_equiv_concat_right(a, canl_eval(w[0]), canw_eval(inner),
            canw_eval(w.drop_first()) + canw_eval(acc));
        //  reassoc to canw(w)·canw(acc)
        assert(canl_eval(w[0]) + (canw_eval(w.drop_first()) + canw_eval(acc))
            =~= (canl_eval(w[0]) + canw_eval(w.drop_first())) + canw_eval(acc));
        assert((canl_eval(w[0]) + canw_eval(w.drop_first())) =~= canw_eval(w));
        lemma_equiv_transitive(a, canw_eval(cw_reduce_from(w, acc)),
            canl_eval(w[0]) + canw_eval(inner),
            canl_eval(w[0]) + (canw_eval(w.drop_first()) + canw_eval(acc)));
        assert(canw_eval(cw_reduce_from(w, acc)) =~= canw_eval(cw_cons(w[0], inner)));
    }
}

//  A2 headline:  the reduced word evaluates to the same element.
pub proof fn lemma_cw_reduce_eval(w: Seq<CanonLetter>)
    ensures
        equiv_in_presentation(base_A(), canw_eval(cw_reduce(w)), canw_eval(w)),
{
    let a = base_A();
    lemma_base_A_valid();
    lemma_canw_eval_valid(cw_reduce(w));
    lemma_cw_reduce_from_eval(w, Seq::<CanonLetter>::empty());
    assert(canw_eval(Seq::<CanonLetter>::empty()) =~= empty_word());
    assert(canw_eval(w) + empty_word() =~= canw_eval(w));
    lemma_equiv_symmetric(a, canw_eval(cw_reduce(w)), canw_eval(w));
}

} //  verus!
