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
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::britton_via_tower::lemma_delete_equiv_empty;
use crate::ii_subset::lemma_signed_power_inverse;
use crate::benign::{concat_all, lemma_concat_all_empty};

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

//  ============================================================
//  A3 — the reduced word is canw_reduced.
//  ============================================================

//  Generic:  prepending a nonzero letter whose coordinate differs from the front of a reduced
//  tail yields a reduced word.
pub proof fn lemma_canw_reduced_cons(head: CanonLetter, tail: Seq<CanonLetter>)
    requires
        head.e != 0,
        canw_reduced(tail),
        tail.len() > 0 ==> (tail[0].r != head.r || tail[0].s != head.s),
    ensures
        canw_reduced(seq![head] + tail),
{
    let res = seq![head] + tail;
    assert(res.len() == 1 + tail.len());
    assert(res[0] == head);
    assert forall|i: int| 1 <= i < res.len() implies res[i] == tail[i - 1] by { }
    //  Clause 1: all exponents nonzero.
    assert forall|i: int| 0 <= i < res.len() implies (#[trigger] res[i]).e != 0 by {
        if i == 0 { } else { assert(res[i] == tail[i - 1]); }
    }
    //  Clause 2: adjacent coordinates distinct.
    assert forall|i: int| 0 <= i < res.len() - 1
        implies !((#[trigger] res[i]).r == res[i + 1].r && res[i].s == res[i + 1].s) by {
        if i == 0 {
            assert(res[0] == head);
            assert(res[1] == tail[0]);
            assert(tail.len() > 0);
        } else {
            assert(res[i] == tail[i - 1]);
            assert(res[i + 1] == tail[i]);
        }
    }
}

//  A reduced word's tail is reduced.
pub proof fn lemma_canw_reduced_drop_first(w: Seq<CanonLetter>)
    requires
        canw_reduced(w),
        w.len() > 0,
    ensures
        canw_reduced(w.drop_first()),
{
    let t = w.drop_first();
    assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i]).e != 0 by {
        assert(t[i] == w[i + 1]);
    }
    assert forall|i: int| 0 <= i < t.len() - 1
        implies !((#[trigger] t[i]).r == t[i + 1].r && t[i].s == t[i + 1].s) by {
        assert(t[i] == w[i + 1]);
        assert(t[i + 1] == w[i + 2]);
    }
}

//  cw_cons preserves canw_reduced.
pub proof fn lemma_cw_cons_reduced(c: CanonLetter, acc: Seq<CanonLetter>)
    requires
        canw_reduced(acc),
    ensures
        canw_reduced(cw_cons(c, acc)),
{
    let res = cw_cons(c, acc);
    if c.e == 0 {
        assert(res =~= acc);
    } else if acc.len() > 0 && acc[0].r == c.r && acc[0].s == c.s {
        let me = c.e + acc[0].e;
        lemma_canw_reduced_drop_first(acc);
        if me == 0 {
            assert(res =~= acc.drop_first());
        } else {
            let merged = CanonLetter { r: c.r, s: c.s, e: me };
            let tail = acc.drop_first();
            //  tail[0] = acc[1], whose coord differs from acc[0] = merged's coord.
            assert(tail.len() > 0 ==> (tail[0].r != merged.r || tail[0].s != merged.s)) by {
                if tail.len() > 0 {
                    assert(tail[0] == acc[1]);
                    assert(!(acc[0].r == acc[1].r && acc[0].s == acc[1].s));
                }
            }
            lemma_canw_reduced_cons(merged, tail);
            assert(res =~= seq![merged] + tail);
        }
    } else {
        //  prepend
        assert(c.e != 0);
        assert(acc.len() > 0 ==> (acc[0].r != c.r || acc[0].s != c.s));
        lemma_canw_reduced_cons(c, acc);
        assert(res =~= seq![c] + acc);
    }
}

//  Fold: cw_reduce_from preserves canw_reduced.
pub proof fn lemma_cw_reduce_from_reduced(w: Seq<CanonLetter>, acc: Seq<CanonLetter>)
    requires
        canw_reduced(acc),
    ensures
        canw_reduced(cw_reduce_from(w, acc)),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(cw_reduce_from(w, acc) =~= acc);
    } else {
        lemma_cw_reduce_from_reduced(w.drop_first(), acc);
        lemma_cw_cons_reduced(w[0], cw_reduce_from(w.drop_first(), acc));
    }
}

//  A3 headline: the reduced word is canw_reduced.
pub proof fn lemma_cw_reduce_reduced(w: Seq<CanonLetter>)
    ensures
        canw_reduced(cw_reduce(w)),
{
    let e = Seq::<CanonLetter>::empty();
    assert(canw_reduced(e));
    lemma_cw_reduce_from_reduced(w, e);
}

//  ============================================================
//  A4 — reduction shrinks the coordinate set.
//  ============================================================
//  Every coordinate in the reduced word appears (as some letter's coordinate) in the input.
//  Stated relative to an accumulator: coords come from `acc` or `w`.

//  "coordinate (r,s) appears in v":
pub open spec fn coord_in(v: Seq<CanonLetter>, r: int, s: int) -> bool {
    exists|j: int| 0 <= j < v.len() && (#[trigger] v[j]).r == r && v[j].s == s
}

//  cw_cons introduces no coordinate outside {c} ∪ acc.
pub proof fn lemma_cw_cons_coords(c: CanonLetter, acc: Seq<CanonLetter>)
    ensures
        forall|i: int| 0 <= i < cw_cons(c, acc).len() ==> {
            ||| ((#[trigger] cw_cons(c, acc)[i]).r == c.r && cw_cons(c, acc)[i].s == c.s)
            ||| coord_in(acc, cw_cons(c, acc)[i].r, cw_cons(c, acc)[i].s)
        },
{
    let res = cw_cons(c, acc);
    assert forall|i: int| 0 <= i < res.len() implies {
        ||| ((#[trigger] res[i]).r == c.r && res[i].s == c.s)
        ||| coord_in(acc, res[i].r, res[i].s)
    } by {
        if c.e == 0 {
            assert(res =~= acc);
            assert(coord_in(acc, res[i].r, res[i].s)) by { assert(res[i] == acc[i]); }
        } else if acc.len() > 0 && acc[0].r == c.r && acc[0].s == c.s {
            let me = c.e + acc[0].e;
            if me == 0 {
                assert(res =~= acc.drop_first());
                assert(res[i] == acc[i + 1]);
                assert(coord_in(acc, res[i].r, res[i].s)) by { assert(acc[i + 1] == res[i]); }
            } else {
                let merged = CanonLetter { r: c.r, s: c.s, e: me };
                assert(res =~= seq![merged] + acc.drop_first());
                if i == 0 {
                    assert(res[0] == merged);
                } else {
                    assert(res[i] == acc.drop_first()[i - 1]);
                    assert(acc.drop_first()[i - 1] == acc[i]);
                    assert(coord_in(acc, res[i].r, res[i].s)) by { assert(acc[i] == res[i]); }
                }
            }
        } else {
            assert(res =~= seq![c] + acc);
            if i == 0 {
                assert(res[0] == c);
            } else {
                assert(res[i] == acc[i - 1]);
                assert(coord_in(acc, res[i].r, res[i].s)) by { assert(acc[i - 1] == res[i]); }
            }
        }
    }
}

//  Fold: every coordinate in cw_reduce_from(w, acc) appears in acc or w.
pub proof fn lemma_cw_reduce_from_coords(w: Seq<CanonLetter>, acc: Seq<CanonLetter>)
    ensures
        forall|i: int| 0 <= i < cw_reduce_from(w, acc).len() ==> {
            ||| coord_in(w, (#[trigger] cw_reduce_from(w, acc)[i]).r, cw_reduce_from(w, acc)[i].s)
            ||| coord_in(acc, cw_reduce_from(w, acc)[i].r, cw_reduce_from(w, acc)[i].s)
        },
    decreases w.len(),
{
    let res = cw_reduce_from(w, acc);
    if w.len() == 0 {
        assert(res =~= acc);
    } else {
        let inner = cw_reduce_from(w.drop_first(), acc);
        lemma_cw_reduce_from_coords(w.drop_first(), acc);
        lemma_cw_cons_coords(w[0], inner);
        assert(res =~= cw_cons(w[0], inner));
        assert forall|i: int| 0 <= i < res.len() implies {
            ||| coord_in(w, (#[trigger] res[i]).r, res[i].s)
            ||| coord_in(acc, res[i].r, res[i].s)
        } by {
            //  res[i] coord is c=w[0] (⊆ coord_in(w)), or in inner (⊆ w.drop_first()∪acc ⊆ w∪acc).
            if res[i].r == w[0].r && res[i].s == w[0].s {
                assert(coord_in(w, res[i].r, res[i].s)) by { assert(w[0] == w[0]); }
            } else {
                assert(coord_in(inner, res[i].r, res[i].s));
                let j = choose|j: int| 0 <= j < inner.len()
                    && inner[j].r == res[i].r && inner[j].s == res[i].s;
                assert(0 <= j < inner.len() && inner[j].r == res[i].r && inner[j].s == res[i].s);
                if coord_in(w.drop_first(), inner[j].r, inner[j].s) {
                    let k = choose|k: int| 0 <= k < w.drop_first().len()
                        && w.drop_first()[k].r == inner[j].r && w.drop_first()[k].s == inner[j].s;
                    assert(0 <= k < w.drop_first().len()
                        && w.drop_first()[k].r == inner[j].r && w.drop_first()[k].s == inner[j].s);
                    assert(w.drop_first()[k] == w[k + 1]);
                    assert(coord_in(w, res[i].r, res[i].s)) by { assert(w[k + 1].r == res[i].r); }
                }
            }
        }
    }
}

//  A4 headline: every coordinate in cw_reduce(w) appears in w.
pub proof fn lemma_cw_reduce_coords(w: Seq<CanonLetter>)
    ensures
        forall|i: int| 0 <= i < cw_reduce(w).len()
            ==> coord_in(w, (#[trigger] cw_reduce(w)[i]).r, cw_reduce(w)[i].s),
{
    let e = Seq::<CanonLetter>::empty();
    lemma_cw_reduce_from_coords(w, e);
    assert forall|i: int| 0 <= i < cw_reduce(w).len()
        implies coord_in(w, (#[trigger] cw_reduce(w)[i]).r, cw_reduce(w)[i].s) by {
        assert(!coord_in(e, cw_reduce(w)[i].r, cw_reduce(w)[i].s));
    }
}

//  ============================================================
//  A5 — trivial config words have empty reduced form.
//  ============================================================
//  Bridge to the proven nontriviality lemma (lemma_canw_eval_nontrivial): a canw_reduced nonempty
//  word is ≢_A ε; so if canw_eval(w) ≡_A ε, the reduced form must be empty.
pub proof fn lemma_cw_reduce_trivial_empty(w: Seq<CanonLetter>)
    requires
        equiv_in_presentation(base_A(), canw_eval(w), empty_word()),
    ensures
        cw_reduce(w).len() == 0,
{
    let a = base_A();
    lemma_base_A_valid();
    let r = cw_reduce(w);
    lemma_cw_reduce_reduced(w);   //  canw_reduced(r)
    lemma_cw_reduce_eval(w);      //  canw_eval(r) ≡ canw_eval(w)
    if r.len() >= 1 {
        //  Extract the nontriviality lemma's hypotheses from canw_reduced(r).
        assert(canw_reduced(r));
        assert forall|j: int| 0 <= j < r.len() implies (#[trigger] r[j]).e != 0 by { }
        assert forall|j: int| 0 <= j < r.len() - 1
            implies (#[trigger] r[j]).r != r[j + 1].r || r[j].s != r[j + 1].s by {
            assert(!(r[j].r == r[j + 1].r && r[j].s == r[j + 1].s));
        }
        lemma_canw_eval_nontrivial(r);   //  canw_eval(r) ≢_A ε
        //  but canw_eval(r) ≡ canw_eval(w) ≡ ε — contradiction.
        lemma_equiv_transitive(a, canw_eval(r), canw_eval(w), empty_word());
        assert(false);
    }
}

//  ============================================================
//  A6 — coordinate restriction (the crux, via coordinate survival).
//  ============================================================
//  Rather than full normal-form uniqueness, we track coordinate SETS: if revinv(V)·U reduces to ε,
//  every coordinate of cw_reduce(U) must appear in V (a foreign coordinate would survive the fold).

//  canw_eval distributes over concatenation.
pub proof fn lemma_canw_eval_concat(x: Seq<CanonLetter>, y: Seq<CanonLetter>)
    ensures
        canw_eval(x + y) =~= canw_eval(x) + canw_eval(y),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(x + y =~= y);
        assert(canw_eval(x) =~= empty_word());
    } else {
        assert((x + y)[0] == x[0]);
        assert((x + y).drop_first() =~= x.drop_first() + y);
        lemma_canw_eval_concat(x.drop_first(), y);
        assert(canw_eval(x + y) =~= canl_eval(x[0]) + canw_eval(x.drop_first() + y));
        assert(canw_eval(x) =~= canl_eval(x[0]) + canw_eval(x.drop_first()));
    }
}

//  cw_reduce_from distributes over concatenation (no barrier — fold A onto the fold of B).
pub proof fn lemma_cw_reduce_from_concat(x: Seq<CanonLetter>, y: Seq<CanonLetter>, acc: Seq<CanonLetter>)
    ensures
        cw_reduce_from(x + y, acc) == cw_reduce_from(x, cw_reduce_from(y, acc)),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(x + y =~= y);
    } else {
        assert((x + y)[0] == x[0]);
        assert((x + y).drop_first() =~= x.drop_first() + y);
        lemma_cw_reduce_from_concat(x.drop_first(), y, acc);
        assert(cw_reduce_from(x + y, acc)
            == cw_cons((x + y)[0], cw_reduce_from((x + y).drop_first(), acc)));
        assert(cw_reduce_from(x, cw_reduce_from(y, acc))
            == cw_cons(x[0], cw_reduce_from(x.drop_first(), cw_reduce_from(y, acc))));
    }
}

//  inverse_word of a config power is the negated config power.
pub proof fn lemma_gsconfig_inverse(r: int, s: int, e: int)
    ensures
        inverse_word(gsconfig(r, s, e)) =~= gsconfig(r, s, -e),
{
    let av = signed_power(2, -s);
    let bv = signed_power(1, -r);
    let cv = signed_power(0, e);
    let dv = signed_power(1, r);
    let fv = signed_power(2, s);
    assert(gsconfig(r, s, e) =~= av + bv + cv + dv + fv);
    //  peel the inverse off the 5-fold concat
    lemma_inverse_word_concat(av + bv + cv + dv, fv);
    lemma_inverse_word_concat(av + bv + cv, dv);
    lemma_inverse_word_concat(av + bv, cv);
    lemma_inverse_word_concat(av, bv);
    //  per-factor inverses
    lemma_signed_power_inverse(2, -s);   //  inv(av) = signed_power(2, s) = fv
    lemma_signed_power_inverse(1, -r);   //  inv(bv) = signed_power(1, r) = dv
    lemma_signed_power_inverse(0, e);    //  inv(cv) = signed_power(0, -e)
    lemma_signed_power_inverse(1, r);    //  inv(dv) = signed_power(1, -r) = bv
    lemma_signed_power_inverse(2, s);    //  inv(fv) = signed_power(2, -s) = av
    assert(inverse_word(gsconfig(r, s, e))
        =~= av + (bv + (signed_power(0, -e) + (dv + fv))));
    assert(gsconfig(r, s, -e) =~= av + (bv + (signed_power(0, -e) + (dv + fv))));
}

//  Reverse-and-invert a config word (the inverse in the config basis).
pub open spec fn canl_inv(c: CanonLetter) -> CanonLetter {
    CanonLetter { r: c.r, s: c.s, e: -c.e }
}

pub open spec fn revinv(v: Seq<CanonLetter>) -> Seq<CanonLetter>
    decreases v.len(),
{
    if v.len() == 0 {
        Seq::<CanonLetter>::empty()
    } else {
        revinv(v.drop_first()) + seq![canl_inv(v[0])]
    }
}

//  canw_eval(revinv(v)) ≡_A inverse_word(canw_eval(v)).
pub proof fn lemma_revinv_eval(v: Seq<CanonLetter>)
    ensures
        equiv_in_presentation(base_A(), canw_eval(revinv(v)), inverse_word(canw_eval(v))),
    decreases v.len(),
{
    let a = base_A();
    lemma_base_A_valid();
    if v.len() == 0 {
        assert(revinv(v) =~= Seq::<CanonLetter>::empty());
        assert(canw_eval(v) =~= empty_word());
        assert(inverse_word(canw_eval(v)) =~= empty_word()) by { lemma_inverse_empty(); }
        assert(canw_eval(revinv(v)) =~= empty_word());
        lemma_equiv_refl(a, canw_eval(revinv(v)));
    } else {
        let v0 = v[0];
        let tail = v.drop_first();
        //  canw_eval(revinv(v)) =~= canw_eval(revinv(tail)) + gsconfig(v0.r,v0.s,-v0.e)
        lemma_canw_eval_concat(revinv(tail), seq![canl_inv(v0)]);
        assert(seq![canl_inv(v0)][0] == canl_inv(v0));
        assert(seq![canl_inv(v0)].drop_first() =~= Seq::<CanonLetter>::empty());
        assert(canw_eval(Seq::<CanonLetter>::empty()) =~= empty_word());
        assert(canw_eval(seq![canl_inv(v0)])
            =~= canl_eval(canl_inv(v0)) + canw_eval(seq![canl_inv(v0)].drop_first()));
        assert(canw_eval(seq![canl_inv(v0)]) =~= canl_eval(canl_inv(v0)));
        assert(canl_eval(canl_inv(v0)) =~= gsconfig(v0.r, v0.s, -v0.e));
        let g_inv = gsconfig(v0.r, v0.s, -v0.e);
        assert(canw_eval(revinv(v)) =~= canw_eval(revinv(tail)) + g_inv);
        //  IH: canw_eval(revinv(tail)) ≡ inverse_word(canw_eval(tail))
        lemma_revinv_eval(tail);
        lemma_equiv_concat_left(a, canw_eval(revinv(tail)), inverse_word(canw_eval(tail)), g_inv);
        //  inverse_word(canw_eval(v)) =~= inverse_word(canw_eval(tail)) + g_inv
        assert(canw_eval(v) =~= canl_eval(v0) + canw_eval(tail));
        lemma_inverse_word_concat(canl_eval(v0), canw_eval(tail));
        lemma_gsconfig_inverse(v0.r, v0.s, v0.e);
        assert(canl_eval(v0) =~= gsconfig(v0.r, v0.s, v0.e));
        assert(inverse_word(canl_eval(v0)) =~= g_inv);
        assert(inverse_word(canw_eval(v)) =~= inverse_word(canw_eval(tail)) + g_inv);
        //  chain:  canw_eval(revinv(v)) =~= LHS ≡ RHS =~= inverse_word(canw_eval(v))
        assert(equiv_in_presentation(a, canw_eval(revinv(v)), inverse_word(canw_eval(v))));
    }
}

//  revinv only uses coordinates already in v.
pub proof fn lemma_revinv_coord(v: Seq<CanonLetter>, r: int, s: int)
    requires
        coord_in(revinv(v), r, s),
    ensures
        coord_in(v, r, s),
    decreases v.len(),
{
    let rv = revinv(v);
    let j = choose|j: int| 0 <= j < rv.len() && rv[j].r == r && rv[j].s == s;
    assert(0 <= j < rv.len() && rv[j].r == r && rv[j].s == s);
    let tail = v.drop_first();
    let rt = revinv(tail);
    assert(rv =~= rt + seq![canl_inv(v[0])]);
    if j < rt.len() {
        assert(rv[j] == rt[j]);
        assert(coord_in(rt, r, s)) by { assert(rt[j].r == r && rt[j].s == s); }
        lemma_revinv_coord(tail, r, s);
        assert(coord_in(v, r, s)) by {
            let k = choose|k: int| 0 <= k < tail.len() && tail[k].r == r && tail[k].s == s;
            assert(0 <= k < tail.len() && tail[k].r == r && tail[k].s == s);
            assert(tail[k] == v[k + 1]);
        }
    } else {
        assert(rv[j] == canl_inv(v[0]));
        assert(coord_in(v, r, s)) by { assert(v[0].r == r && v[0].s == s); }
    }
}

//  cw_cons keeps a foreign coordinate (one not equal to the consed letter's) that lives in acc.
pub proof fn lemma_cw_cons_preserves_foreign(c: CanonLetter, acc: Seq<CanonLetter>, r: int, s: int)
    requires
        coord_in(acc, r, s),
        !(c.r == r && c.s == s),
    ensures
        coord_in(cw_cons(c, acc), r, s),
{
    let res = cw_cons(c, acc);
    let j0 = choose|j: int| 0 <= j < acc.len() && acc[j].r == r && acc[j].s == s;
    assert(0 <= j0 < acc.len() && acc[j0].r == r && acc[j0].s == s);
    if c.e == 0 {
        assert(res =~= acc);
        assert(res[j0] == acc[j0]);
    } else if acc.len() > 0 && acc[0].r == c.r && acc[0].s == c.s {
        //  acc[0] has c's coordinate ≠ (r,s), so the (r,s) witness is at index ≥ 1.
        assert(j0 >= 1) by { if j0 == 0 { assert(acc[0].r == c.r && acc[0].s == c.s); } }
        let me = c.e + acc[0].e;
        if me == 0 {
            assert(res =~= acc.drop_first());
            assert(res[j0 - 1] == acc.drop_first()[j0 - 1]);
            assert(acc.drop_first()[j0 - 1] == acc[j0]);
            assert(coord_in(res, r, s)) by { assert(res[j0 - 1].r == r && res[j0 - 1].s == s); }
        } else {
            let merged = CanonLetter { r: c.r, s: c.s, e: me };
            assert(res =~= seq![merged] + acc.drop_first());
            assert(res[j0] == acc.drop_first()[j0 - 1]);
            assert(acc.drop_first()[j0 - 1] == acc[j0]);
            assert(coord_in(res, r, s)) by { assert(res[j0].r == r && res[j0].s == s); }
        }
    } else {
        assert(res =~= seq![c] + acc);
        assert(res[j0 + 1] == acc[j0]);
        assert(coord_in(res, r, s)) by { assert(res[j0 + 1].r == r && res[j0 + 1].s == s); }
    }
}

//  Fold-survival:  a coordinate in acc that is FOREIGN to x survives the fold cw_reduce_from(x, acc).
pub proof fn lemma_fold_preserves_foreign_coords(
    x: Seq<CanonLetter>, acc: Seq<CanonLetter>, r: int, s: int,
)
    requires
        coord_in(acc, r, s),
        !coord_in(x, r, s),
    ensures
        coord_in(cw_reduce_from(x, acc), r, s),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(cw_reduce_from(x, acc) =~= acc);
    } else {
        let inner = cw_reduce_from(x.drop_first(), acc);
        //  foreign to x ⟹ foreign to x.drop_first() and ≠ x[0]'s coordinate
        assert(!coord_in(x.drop_first(), r, s)) by {
            if coord_in(x.drop_first(), r, s) {
                let k = choose|k: int| 0 <= k < x.drop_first().len()
                    && x.drop_first()[k].r == r && x.drop_first()[k].s == s;
                assert(0 <= k < x.drop_first().len()
                    && x.drop_first()[k].r == r && x.drop_first()[k].s == s);
                assert(x.drop_first()[k] == x[k + 1]);
                assert(coord_in(x, r, s)) by { assert(x[k + 1].r == r && x[k + 1].s == s); }
            }
        }
        assert(!(x[0].r == r && x[0].s == s)) by {
            if x[0].r == r && x[0].s == s { assert(coord_in(x, r, s)) by { assert(x[0].r == r); } }
        }
        lemma_fold_preserves_foreign_coords(x.drop_first(), acc, r, s);   //  coord_in(inner, r, s)
        lemma_cw_cons_preserves_foreign(x[0], inner, r, s);
        assert(cw_reduce_from(x, acc) == cw_cons(x[0], inner));
    }
}

//  ============================================================
//  THE CRUX (A6 headline):  coordinate restriction.
//  ============================================================
//  If canw_eval(u) ≡_A canw_eval(v), then every coordinate of the reduced form of u appears in v.
//  (Instantiated in B3 with v = the H₀ factorization: forces cw_reduce(u)'s coords ⊆ H₀.)
pub proof fn lemma_tfree_coord_restrict(u: Seq<CanonLetter>, v: Seq<CanonLetter>, r: int, s: int)
    requires
        equiv_in_presentation(base_A(), canw_eval(u), canw_eval(v)),
        coord_in(cw_reduce(u), r, s),
    ensures
        coord_in(v, r, s),
{
    let a = base_A();
    lemma_base_A_valid();
    let d = revinv(v) + u;
    //  --- canw_eval(d) ≡ ε ---
    lemma_canw_eval_concat(revinv(v), u);                       //  canw(d) =~= canw(revinv v) + canw(u)
    lemma_revinv_eval(v);                                       //  canw(revinv v) ≡ inverse_word(canw v)
    lemma_equiv_concat_left(a, canw_eval(revinv(v)), inverse_word(canw_eval(v)), canw_eval(u));
    //  inverse_word(canw v) + canw(u) ≡ inverse_word(canw v) + canw(v)   (canw u ≡ canw v)
    lemma_equiv_concat_right(a, inverse_word(canw_eval(v)), canw_eval(u), canw_eval(v));
    lemma_word_inverse_left(a, canw_eval(v));                   //  inverse_word(canw v) + canw(v) ≡ ε
    lemma_equiv_transitive(a, inverse_word(canw_eval(v)) + canw_eval(u),
        inverse_word(canw_eval(v)) + canw_eval(v), empty_word());
    lemma_equiv_transitive(a, canw_eval(d),
        inverse_word(canw_eval(v)) + canw_eval(u), empty_word());
    //  --- cw_reduce(d) == [] ---
    lemma_cw_reduce_trivial_empty(d);
    assert(cw_reduce(d).len() == 0);
    //  cw_reduce(d) = cw_reduce_from(revinv(v), cw_reduce(u))
    lemma_cw_reduce_from_concat(revinv(v), u, Seq::<CanonLetter>::empty());
    assert(cw_reduce(d) == cw_reduce_from(revinv(v), cw_reduce(u)));
    //  --- contradiction if (r,s) ∉ v ---
    if !coord_in(v, r, s) {
        assert(!coord_in(revinv(v), r, s)) by {
            if coord_in(revinv(v), r, s) { lemma_revinv_coord(v, r, s); }
        }
        lemma_fold_preserves_foreign_coords(revinv(v), cw_reduce(u), r, s);
        assert(coord_in(cw_reduce_from(revinv(v), cw_reduce(u)), r, s));
        assert(cw_reduce_from(revinv(v), cw_reduce(u)).len() == 0);
        assert(false);
    }
}

//  ============================================================
//  Part B — bridging the accumulator / in_TM factor lists into CanonLetter form.
//  ============================================================
//  A factor word f is the evaluation of a signed CanonLetter c (e = ±1).
pub open spec fn is_canl_word(f: Word, c: CanonLetter) -> bool {
    (c.e == 1 && f == sconfig(c.r, c.s)) || (c.e == -1 && f == inverse_word(sconfig(c.r, c.s)))
}

//  sconfig is the e=1 config power.
pub proof fn lemma_sconfig_is_gsconfig1(r: int, s: int)
    ensures
        sconfig(r, s) =~= gsconfig(r, s, 1),
{
    assert(signed_power(0, 1) =~= seq![Symbol::Gen(0)]);
}

//  is_canl_word ⟹ the letter's evaluation matches the factor word.
pub proof fn lemma_is_canl_word_eval(f: Word, c: CanonLetter)
    requires
        is_canl_word(f, c),
    ensures
        canl_eval(c) =~= f,
{
    lemma_sconfig_is_gsconfig1(c.r, c.s);
    if c.e == 1 {
        assert(canl_eval(c) =~= gsconfig(c.r, c.s, 1));
    } else {
        //  canl_eval(c) = gsconfig(r,s,-1) =~= inverse_word(gsconfig(r,s,1)) =~= inverse_word(sconfig(r,s)) = f
        lemma_gsconfig_inverse(c.r, c.s, 1);
        assert(canl_eval(c) =~= gsconfig(c.r, c.s, -1));
        assert(inverse_word(gsconfig(c.r, c.s, 1)) =~= gsconfig(c.r, c.s, -1));
    }
}

//  A CanonLetter list represents a factor list: same length, pointwise is_canl_word.
pub open spec fn canon_represents(factors: Seq<Word>, canon: Seq<CanonLetter>) -> bool {
    &&& factors.len() == canon.len()
    &&& (forall|i: int| 0 <= i < factors.len() ==> is_canl_word(#[trigger] factors[i], canon[i]))
}

//  A representing CanonLetter list evaluates to the same word as concat_all of the factors.
pub proof fn lemma_canon_represents_eval(factors: Seq<Word>, canon: Seq<CanonLetter>)
    requires
        canon_represents(factors, canon),
    ensures
        concat_all(factors) =~= canw_eval(canon),
    decreases factors.len(),
{
    if factors.len() == 0 {
        lemma_concat_all_empty();
        assert(canw_eval(canon) =~= empty_word());
    } else {
        reveal_with_fuel(concat_all, 1);
        assert(concat_all(factors) =~= factors.first() + concat_all(factors.drop_first()));
        //  head: canl_eval(canon[0]) =~= factors[0]
        lemma_is_canl_word_eval(factors[0], canon[0]);
        assert(canw_eval(canon) =~= canl_eval(canon[0]) + canw_eval(canon.drop_first()));
        //  tail represents
        assert(canon_represents(factors.drop_first(), canon.drop_first())) by {
            assert forall|i: int| 0 <= i < factors.drop_first().len()
                implies is_canl_word(#[trigger] factors.drop_first()[i], canon.drop_first()[i]) by {
                assert(factors.drop_first()[i] == factors[i + 1]);
                assert(canon.drop_first()[i] == canon[i + 1]);
            }
        }
        lemma_canon_represents_eval(factors.drop_first(), canon.drop_first());
        assert(factors.first() == factors[0]);
    }
}

//  ============================================================
//  B2 — in_TM(g) ⟹ a CanonLetter list with H₀ coordinates evaluating to g.
//  ============================================================

//  Convert a T(M)-generator word to its CanonLetter (coordinate from the H₀ witness).
pub open spec fn tm_factor_to_canl(mm: ModMachine, f: Word) -> CanonLetter {
    let w = choose|p: nat, q: nat| #![trigger config_word(p, q)]
        mm_in_H0(mm, p, q) && (f == config_word(p, q) || f == inverse_word(config_word(p, q)));
    if f == config_word(w.0, w.1) {
        CanonLetter { r: w.0 as int, s: w.1 as int, e: 1 }
    } else {
        CanonLetter { r: w.0 as int, s: w.1 as int, e: -1 }
    }
}

pub proof fn lemma_tm_factor_to_canl(mm: ModMachine, f: Word)
    requires
        is_tm_gen(mm, f),
    ensures
        is_canl_word(f, tm_factor_to_canl(mm, f)),
        tm_factor_to_canl(mm, f).r >= 0,
        tm_factor_to_canl(mm, f).s >= 0,
        mm_in_H0(mm, tm_factor_to_canl(mm, f).r as nat, tm_factor_to_canl(mm, f).s as nat),
{
    let w = choose|p: nat, q: nat| #![trigger config_word(p, q)]
        mm_in_H0(mm, p, q) && (f == config_word(p, q) || f == inverse_word(config_word(p, q)));
    //  is_tm_gen gives a witness, so the choose's predicate is satisfied.
    assert(mm_in_H0(mm, w.0, w.1) && (f == config_word(w.0, w.1) || f == inverse_word(config_word(w.0, w.1))));
    let c = tm_factor_to_canl(mm, f);
    lemma_sconfig_nat(w.0 as int, w.1 as int);     //  config_word(w.0,w.1) =~= sconfig(w.0,w.1)
    assert(config_word(w.0, w.1) =~= sconfig(w.0 as int, w.1 as int));
    if f == config_word(w.0, w.1) {
        assert(c == CanonLetter { r: w.0 as int, s: w.1 as int, e: 1 });
        assert(f =~= sconfig(c.r, c.s));
    } else {
        assert(c == CanonLetter { r: w.0 as int, s: w.1 as int, e: -1 });
        assert(f =~= inverse_word(sconfig(c.r, c.s)));
    }
}

//  The builder: in_TM(g) ⟹ a CanonLetter list, H₀ coordinates, evaluating to g.
pub proof fn lemma_in_TM_to_canon(mm: ModMachine, g: Word) -> (canon: Seq<CanonLetter>)
    requires
        in_TM(mm, g),
    ensures
        equiv_in_presentation(base_A(), canw_eval(canon), g),
        forall|i: int| 0 <= i < canon.len() ==> {
            &&& (#[trigger] canon[i]).r >= 0
            &&& canon[i].s >= 0
            &&& mm_in_H0(mm, canon[i].r as nat, canon[i].s as nat)
        },
{
    let a = base_A();
    lemma_base_A_valid();
    let factors = choose|factors: Seq<Word>| #[trigger] factors_from_pred(tm_pred(mm), factors)
        && equiv_in_presentation(a, concat_all(factors), g);
    assert(factors_from_pred(tm_pred(mm), factors) && equiv_in_presentation(a, concat_all(factors), g));
    let canon = Seq::new(factors.len(), |i: int| tm_factor_to_canl(mm, factors[i]));
    assert(canon.len() == factors.len());
    assert forall|i: int| 0 <= i < canon.len() implies {
        &&& (#[trigger] canon[i]).r >= 0
        &&& canon[i].s >= 0
        &&& mm_in_H0(mm, canon[i].r as nat, canon[i].s as nat)
    } by {
        assert(canon[i] == tm_factor_to_canl(mm, factors[i]));
        assert(tm_pred(mm)(factors[i]));
        assert(is_tm_gen(mm, factors[i]));
        lemma_tm_factor_to_canl(mm, factors[i]);
    }
    //  canon_represents(factors, canon)
    assert(canon_represents(factors, canon)) by {
        assert forall|i: int| 0 <= i < factors.len()
            implies is_canl_word(#[trigger] factors[i], canon[i]) by {
            assert(canon[i] == tm_factor_to_canl(mm, factors[i]));
            assert(is_tm_gen(mm, factors[i]));
            lemma_tm_factor_to_canl(mm, factors[i]);
        }
    }
    lemma_canon_represents_eval(factors, canon);   //  concat_all(factors) =~= canw_eval(canon)
    assert(canw_eval(canon) =~= concat_all(factors));
    canon
}

//  ============================================================
//  B1 — in_residue_class(aa,bb,m,g) ⟹ a CanonLetter list with residue coordinates.
//  ============================================================

//  Convert a residue-class generator word to its CanonLetter (coordinate from the residue witness).
pub open spec fn res_factor_to_canl(aa: int, bb: int, m: int, f: Word) -> CanonLetter {
    let rs = choose|r: int, s: int| #![trigger config_word_signed(r, s)]
        (r - aa) % m == 0 && (s - bb) % m == 0
        && (f == config_word_signed(r, s) || f == inverse_word(config_word_signed(r, s)));
    if f == config_word_signed(rs.0, rs.1) {
        CanonLetter { r: rs.0, s: rs.1, e: 1 }
    } else {
        CanonLetter { r: rs.0, s: rs.1, e: -1 }
    }
}

pub proof fn lemma_res_factor_to_canl(aa: int, bb: int, m: int, f: Word)
    requires
        is_residue_gen(aa, bb, m, f),
    ensures
        is_canl_word(f, res_factor_to_canl(aa, bb, m, f)),
        (res_factor_to_canl(aa, bb, m, f).r - aa) % m == 0,
        (res_factor_to_canl(aa, bb, m, f).s - bb) % m == 0,
{
    let rs = choose|r: int, s: int| #![trigger config_word_signed(r, s)]
        (r - aa) % m == 0 && (s - bb) % m == 0
        && (f == config_word_signed(r, s) || f == inverse_word(config_word_signed(r, s)));
    assert((rs.0 - aa) % m == 0 && (rs.1 - bb) % m == 0
        && (f == config_word_signed(rs.0, rs.1) || f == inverse_word(config_word_signed(rs.0, rs.1))));
    let c = res_factor_to_canl(aa, bb, m, f);
    //  config_word_signed == sconfig (same definition).
    assert(config_word_signed(rs.0, rs.1) =~= sconfig(rs.0, rs.1));
    if f == config_word_signed(rs.0, rs.1) {
        assert(c == CanonLetter { r: rs.0, s: rs.1, e: 1 });
        assert(f =~= sconfig(c.r, c.s));
    } else {
        assert(c == CanonLetter { r: rs.0, s: rs.1, e: -1 });
        assert(f =~= inverse_word(sconfig(c.r, c.s)));
    }
}

//  The builder: in_residue_class(aa,bb,m,g) ⟹ a CanonLetter list, residue coordinates, eval = g.
pub proof fn lemma_residue_to_canon(aa: int, bb: int, m: int, g: Word) -> (canon: Seq<CanonLetter>)
    requires
        in_residue_class(aa, bb, m, g),
    ensures
        equiv_in_presentation(base_A(), canw_eval(canon), g),
        forall|i: int| 0 <= i < canon.len() ==> {
            &&& ((#[trigger] canon[i]).r - aa) % m == 0
            &&& (canon[i].s - bb) % m == 0
        },
{
    let a = base_A();
    lemma_base_A_valid();
    let factors = choose|factors: Seq<Word>| #[trigger] factors_from_pred(residue_pred(aa, bb, m), factors)
        && equiv_in_presentation(a, concat_all(factors), g);
    assert(factors_from_pred(residue_pred(aa, bb, m), factors)
        && equiv_in_presentation(a, concat_all(factors), g));
    let canon = Seq::new(factors.len(), |i: int| res_factor_to_canl(aa, bb, m, factors[i]));
    assert(canon.len() == factors.len());
    assert forall|i: int| 0 <= i < canon.len() implies {
        &&& ((#[trigger] canon[i]).r - aa) % m == 0
        &&& (canon[i].s - bb) % m == 0
    } by {
        assert(canon[i] == res_factor_to_canl(aa, bb, m, factors[i]));
        assert(residue_pred(aa, bb, m)(factors[i]));
        assert(is_residue_gen(aa, bb, m, factors[i]));
        lemma_res_factor_to_canl(aa, bb, m, factors[i]);
    }
    assert(canon_represents(factors, canon)) by {
        assert forall|i: int| 0 <= i < factors.len()
            implies is_canl_word(#[trigger] factors[i], canon[i]) by {
            assert(canon[i] == res_factor_to_canl(aa, bb, m, factors[i]));
            assert(is_residue_gen(aa, bb, m, factors[i]));
            lemma_res_factor_to_canl(aa, bb, m, factors[i]);
        }
    }
    lemma_canon_represents_eval(factors, canon);
    assert(canw_eval(canon) =~= concat_all(factors));
    canon
}

//  ============================================================
//  B3 — the intermediate:  in_TM ∩ residue-class ⟹ a reduced form with H₀∩residue coordinates.
//  ============================================================
//  Consumes the Part-A crux:  g ∈ T(M) and g ∈ ⟨residue⟩ ⟹ g ≡_A a canw_reduced word whose every
//  coordinate is BOTH an H₀ configuration AND in the residue class (aa,bb mod m).
pub proof fn lemma_in_TM_residue_reduced(mm: ModMachine, aa: int, bb: int, m: int, g: Word)
    requires
        in_TM(mm, g),
        in_residue_class(aa, bb, m, g),
    ensures
        exists|red: Seq<CanonLetter>| {
            &&& canw_reduced(red)
            &&& equiv_in_presentation(base_A(), canw_eval(red), g)
            &&& (forall|i: int| 0 <= i < red.len() ==> {
                    &&& (#[trigger] red[i]).r >= 0
                    &&& red[i].s >= 0
                    &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
                    &&& (red[i].r - aa) % m == 0
                    &&& (red[i].s - bb) % m == 0
                })
        },
{
    let a = base_A();
    lemma_base_A_valid();
    let p_canon = lemma_in_TM_to_canon(mm, g);            //  canw_eval(p) ≡ g, coords ∈ H₀
    let qa = lemma_residue_to_canon(aa, bb, m, g);        //  canw_eval(qa) ≡ g, coords residue
    //  canw_eval(qa) ≡ canw_eval(p_canon)  (both ≡ g)
    lemma_canw_eval_valid(p_canon);
    lemma_equiv_symmetric(a, canw_eval(p_canon), g);
    lemma_equiv_transitive(a, canw_eval(qa), g, canw_eval(p_canon));
    let red = cw_reduce(qa);
    lemma_cw_reduce_reduced(qa);                          //  canw_reduced(red)
    lemma_cw_reduce_eval(qa);                             //  canw_eval(red) ≡ canw_eval(qa) ≡ g
    lemma_equiv_transitive(a, canw_eval(red), canw_eval(qa), g);
    //  coordinate facts for red
    lemma_cw_reduce_coords(qa);                           //  coord_in(red) ⟹ coord_in(qa)
    assert forall|i: int| 0 <= i < red.len() implies {
        &&& (#[trigger] red[i]).r >= 0
        &&& red[i].s >= 0
        &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
        &&& (red[i].r - aa) % m == 0
        &&& (red[i].s - bb) % m == 0
    } by {
        let r = red[i].r;
        let s = red[i].s;
        assert(coord_in(red, r, s)) by { assert(red[i].r == r && red[i].s == s); }
        //  residue:  coord_in(red) ⟹ coord_in(qa) ⟹ residue
        let jq = choose|j: int| 0 <= j < qa.len() && qa[j].r == r && qa[j].s == s;
        assert(0 <= jq < qa.len() && qa[jq].r == r && qa[jq].s == s);
        assert((qa[jq].r - aa) % m == 0 && (qa[jq].s - bb) % m == 0);
        //  H₀:  crux ⟹ coord_in(p_canon) ⟹ H₀
        lemma_tfree_coord_restrict(qa, p_canon, r, s);
        let jp = choose|j: int| 0 <= j < p_canon.len() && p_canon[j].r == r && p_canon[j].s == s;
        assert(0 <= jp < p_canon.len() && p_canon[jp].r == r && p_canon[jp].s == s);
        assert(p_canon[jp].r >= 0 && p_canon[jp].s >= 0
            && mm_in_H0(mm, p_canon[jp].r as nat, p_canon[jp].s as nat));
    }
    assert(canw_reduced(red) && equiv_in_presentation(a, canw_eval(red), g)
        && (forall|i: int| 0 <= i < red.len() ==> {
            &&& (#[trigger] red[i]).r >= 0
            &&& red[i].s >= 0
            &&& mm_in_H0(mm, red[i].r as nat, red[i].s as nat)
            &&& (red[i].r - aa) % m == 0
            &&& (red[i].s - bb) % m == 0
        }));
}

//  ============================================================
//  B5 core — a config power at an H₀ coordinate is in T(M).
//  ============================================================

//  in_TM(ε) — the empty product.
pub proof fn lemma_empty_in_TM(mm: ModMachine)
    ensures
        in_TM(mm, empty_word()),
{
    let f = Seq::<Word>::empty();
    lemma_base_A_valid();
    lemma_concat_all_empty();
    lemma_equiv_refl(base_A(), empty_word());
    assert(factors_from_pred(tm_pred(mm), f));
    assert(in_TM(mm, empty_word())) by {
        assert(factors_from_pred(tm_pred(mm), f)
            && equiv_in_presentation(base_A(), concat_all(f), empty_word()));
    }
}

//  gsconfig(p,q,e) (a config raised to integer power e, at an H₀ coordinate) is in T(M).
pub proof fn lemma_gsconfig_in_TM(mm: ModMachine, p: nat, q: nat, e: int)
    requires
        mm_in_H0(mm, p, q),
    ensures
        in_TM(mm, gsconfig(p as int, q as int, e)),
    decreases (if e >= 0 { e } else { -e }),
{
    let a = base_A();
    lemma_base_A_valid();
    let pi = p as int;
    let qi = q as int;
    if e == 0 {
        lemma_gsconfig_zero(pi, qi);                       //  gsconfig(p,q,0) ≡ ε
        lemma_empty_in_TM(mm);
        lemma_canl_eval_valid(CanonLetter { r: pi, s: qi, e: 0 });   //  word_valid(gsconfig(p,q,0),3)
        lemma_equiv_symmetric(a, gsconfig(pi, qi, 0), empty_word());
        lemma_in_subgroup_pred_respects_equiv(a, tm_pred(mm), empty_word(), gsconfig(pi, qi, 0));
    } else if e == 1 {
        lemma_sconfig_is_gsconfig1(pi, qi);                //  gsconfig(p,q,1) =~= sconfig(p,q)
        lemma_sconfig_nat(pi, qi);                         //  sconfig(p,q) =~= config_word(p,q)
        lemma_config_in_TM(mm, p, q);                      //  in_TM(config_word(p,q))
        assert(gsconfig(pi, qi, 1) =~= config_word(p, q));
    } else if e == -1 {
        //  gsconfig(p,q,-1) =~= inverse_word(config_word(p,q)) — a T(M)-gen.
        lemma_sconfig_is_gsconfig1(pi, qi);
        lemma_sconfig_nat(pi, qi);
        lemma_gsconfig_inverse(pi, qi, 1);
        assert(gsconfig(pi, qi, -1) =~= inverse_word(config_word(p, q)));
        assert(is_tm_gen(mm, gsconfig(pi, qi, -1))) by {
            assert(mm_in_H0(mm, p, q) && gsconfig(pi, qi, -1) =~= inverse_word(config_word(p, q)));
        }
        assert(tm_pred(mm)(gsconfig(pi, qi, -1)) == is_tm_gen(mm, gsconfig(pi, qi, -1)));
        lemma_gen_in_subgroup_pred(a, tm_pred(mm), gsconfig(pi, qi, -1));
    } else if e > 1 {
        //  gsconfig(p,q,e) ≡ gsconfig(p,q,1) · gsconfig(p,q,e-1)
        lemma_gsconfig_merge(pi, qi, 1, e - 1);
        lemma_gsconfig_in_TM(mm, p, q, 1);
        lemma_gsconfig_in_TM(mm, p, q, e - 1);
        lemma_product_in_subgroup_pred(a, tm_pred(mm), gsconfig(pi, qi, 1), gsconfig(pi, qi, e - 1));
        assert(1 + (e - 1) == e);
        lemma_in_subgroup_pred_respects_equiv(a, tm_pred(mm),
            gsconfig(pi, qi, 1) + gsconfig(pi, qi, e - 1), gsconfig(pi, qi, e));
    } else {
        //  e < -1:  gsconfig(p,q,e) ≡ gsconfig(p,q,-1) · gsconfig(p,q,e+1)
        lemma_gsconfig_merge(pi, qi, -1, e + 1);
        lemma_gsconfig_in_TM(mm, p, q, -1);
        lemma_gsconfig_in_TM(mm, p, q, e + 1);
        lemma_product_in_subgroup_pred(a, tm_pred(mm), gsconfig(pi, qi, -1), gsconfig(pi, qi, e + 1));
        assert(-1 + (e + 1) == e);
        lemma_in_subgroup_pred_respects_equiv(a, tm_pred(mm),
            gsconfig(pi, qi, -1) + gsconfig(pi, qi, e + 1), gsconfig(pi, qi, e));
    }
}

//  ============================================================
//  E2.E — property (i):  in_TM(config(α,β)) ⟹ (α,β) ∈ H₀.
//  ============================================================
//  T-freeness "last mile".  Falls straight out of coordinate survival (lemma_tfree_coord_restrict —
//  the config-basis injectivity already proven for property (v)): the reduced singleton config word
//  [{α,β,1}] survives into any ≡_A H₀ factorization, so (α,β) must be one of the H₀ coordinates.
pub proof fn lemma_in_TM_config_implies_H0(mm: ModMachine, alpha: nat, beta: nat)
    requires
        in_TM(mm, config_word(alpha, beta)),
    ensures
        mm_in_H0(mm, alpha, beta),
{
    let a = base_A();
    lemma_base_A_valid();
    let g = config_word(alpha, beta);
    let ai = alpha as int;
    let bi = beta as int;
    //  u = reduced singleton config word [{α,β,1}], canw_eval(u) =~= config(α,β)
    let u = seq![CanonLetter { r: ai, s: bi, e: 1 }];
    lemma_sconfig_nat(ai, bi);                         //  sconfig(α,β) =~= config_word(α,β)
    lemma_sconfig_is_gsconfig1(ai, bi);               //  sconfig =~= gsconfig(·,1)
    assert(u.drop_first() =~= Seq::<CanonLetter>::empty());
    assert(canw_eval(u) =~= canl_eval(u[0]) + canw_eval(u.drop_first()));
    assert(canw_eval(u.drop_first()) =~= empty_word());
    assert(canl_eval(u[0]) =~= gsconfig(ai, bi, 1));
    assert(canw_eval(u) =~= g);
    //  u is already reduced ⟹ cw_reduce(u) =~= u ⟹ coord (α,β) is in cw_reduce(u)
    assert(cw_reduce(u) =~= u) by {
        reveal_with_fuel(cw_reduce_from, 2);
        assert(u.drop_first() =~= Seq::<CanonLetter>::empty());
        assert(cw_reduce_from(u.drop_first(), Seq::<CanonLetter>::empty()) =~= Seq::<CanonLetter>::empty());
        assert(cw_reduce(u) == cw_cons(u[0], Seq::<CanonLetter>::empty()));
        assert(u[0].e == 1);
        assert(cw_cons(u[0], Seq::<CanonLetter>::empty()) =~= seq![u[0]]);
    }
    assert(coord_in(cw_reduce(u), ai, bi)) by {
        assert(cw_reduce(u).len() == 1 && cw_reduce(u)[0].r == ai && cw_reduce(u)[0].s == bi);
    }
    //  H₀ canon form of g
    let p_canon = lemma_in_TM_to_canon(mm, g);        //  canw_eval(p_canon) ≡_A g, coords ∈ H₀
    lemma_canw_eval_valid(p_canon);
    lemma_equiv_symmetric(a, canw_eval(p_canon), g);  //  g ≡ canw_eval(p_canon)
    assert(equiv_in_presentation(a, canw_eval(u), canw_eval(p_canon)));   //  canw_eval(u) =~= g
    //  coordinate survival ⟹ coord_in(p_canon, α, β); that coordinate is H₀
    lemma_tfree_coord_restrict(u, p_canon, ai, bi);
    let j = choose|j: int| 0 <= j < p_canon.len() && p_canon[j].r == ai && p_canon[j].s == bi;
    assert(0 <= j < p_canon.len() && p_canon[j].r == ai && p_canon[j].s == bi);
    assert(mm_in_H0(mm, p_canon[j].r as nat, p_canon[j].s as nat));
    assert(p_canon[j].r as nat == alpha && p_canon[j].s as nat == beta);
}

} //  verus!
