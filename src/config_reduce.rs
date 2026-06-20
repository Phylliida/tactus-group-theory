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
use crate::ii_subset::lemma_signed_power_inverse;

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

} //  verus!
