// m2_translate.rs — M-ladder rung M2 (read/translate): positivity of ⟨q,a,b,q′ | qa = bq′⟩.
//
// docs/semantic-finite-basis.md §4.2. The group is F(q,a,b) (Tietze: q′ = b⁻¹qa).
//   positivity(m2_rules, 4): for positive u,v over {a,b,q,q′}:
//     u = v in the group  ⟺  u ↔*_{qa=bq′} v.
//
// ⟸ (Thue ⟹ group): immediate from thue.rs.
// ⟹ (group ⟹ Thue): sub: G → F(q,a,b) (q′↦b⁻¹qa) is a hom (no retraction needed — unlike M0).
//   Orient bq′→qa (nf = no `bq′` substring, #q′ strictly decreases → complete). NO-CANCELLATION
//   READBACK: sub(w) for a no-bq′ word has no cancellations (b⁻¹ heads only sub(q′), cancels only a
//   literal preceding b = the excluded `bq′`), so sub(nf) is reduced-as-written and parses back
//   letterwise (first symbol ∈ {Gen0,Gen1,Gen2,Inv1}, all distinct). sub injective on nf.
//
// Alphabet:  a = Gen(0)  b = Gen(1)  q = Gen(2)  q′ = Gen(3).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::thue::*;

verus! {

pub open spec fn m2_rules() -> Seq<ThueRule> {
    seq![ ThueRule {
        lhs: seq![Symbol::Gen(2), Symbol::Gen(0)],   // q a
        rhs: seq![Symbol::Gen(1), Symbol::Gen(3)],   // b q′
    } ]
}

pub proof fn lemma_m2_rules_valid()
    ensures
        forall|r: int| 0 <= r < m2_rules().len() ==>
            word_valid(#[trigger] m2_rules()[r].lhs, 4) && word_valid(m2_rules()[r].rhs, 4),
{
    assert forall|r: int| 0 <= r < m2_rules().len() implies
        word_valid(#[trigger] m2_rules()[r].lhs, 4) && word_valid(m2_rules()[r].rhs, 4) by {
        assert(word_valid(m2_rules()[0].lhs, 4));
        assert(word_valid(m2_rules()[0].rhs, 4));
    }
}

pub proof fn lemma_m2_pres_valid()
    ensures presentation_valid(rules_pres(m2_rules(), 4))
{
    reveal(presentation_valid);
    let p = rules_pres(m2_rules(), 4);
    lemma_m2_rules_valid();
    assert forall|i: int| 0 <= i < p.relators.len() implies word_valid(#[trigger] p.relators[i], 4) by {
        assert(p.relators[0] =~= thue_relator(m2_rules()[0]));
        let l = m2_rules()[0].lhs;
        let rr = m2_rules()[0].rhs;
        lemma_inverse_word_valid(rr, 4);
        assert forall|k: int| 0 <= k < concat(l, inverse_word(rr)).len()
            implies symbol_valid(#[trigger] concat(l, inverse_word(rr))[k], 4) by {
            if k < l.len() { assert(concat(l, inverse_word(rr))[k] == l[k]); }
            else { assert(concat(l, inverse_word(rr))[k] == inverse_word(rr)[k - l.len()]); }
        }
        assert(word_valid(concat(l, inverse_word(rr)), 4));
        assert(thue_relator(m2_rules()[0]) =~= concat(l, inverse_word(rr)));
    }
}

// ── ⟸  Thue ⟹ group (from thue.rs) ──
pub proof fn lemma_m2_backward(u: Word, v: Word)
    requires word_valid(u, 4), thue_equiv(m2_rules(), u, v),
    ensures equiv_in_presentation(rules_pres(m2_rules(), 4), u, v)
{
    lemma_m2_pres_valid();
    lemma_m2_rules_valid();
    lemma_thue_implies_group(m2_rules(), 4, u, v);
}

// ═══ sub: G → F(q,a,b), q′ ↦ b⁻¹qa (the Tietze hom).  a=0,b=1,q=2 in target. ═══
pub open spec fn sub_hom() -> crate::homomorphism::HomomorphismData {
    crate::homomorphism::HomomorphismData {
        source: rules_pres(m2_rules(), 4),
        target: crate::higman_operations::free_group(3),
        generator_images: seq![
            seq![Symbol::Gen(0)],                              // a ↦ a
            seq![Symbol::Gen(1)],                              // b ↦ b
            seq![Symbol::Gen(2)],                              // q ↦ q
            seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)]  // q′ ↦ b⁻¹qa
        ],
    }
}

// reduces_to(w0, ε) via 3 explicit cancellations (for the relator image).
proof fn m2_reduces3(w0: Word, i0: int, w1: Word, i1: int, w2: Word, i2: int)
    requires
        crate::reduction::has_cancellation_at(w0, i0), w1 == crate::reduction::reduce_at(w0, i0),
        crate::reduction::has_cancellation_at(w1, i1), w2 == crate::reduction::reduce_at(w1, i1),
        crate::reduction::has_cancellation_at(w2, i2), crate::reduction::reduce_at(w2, i2) == empty_word(),
    ensures crate::reduction::reduces_to(w0, empty_word())
{
    use crate::reduction::*;
    assert(reduces_one_step(w2, empty_word())) by { assert(has_cancellation_at(w2, i2) && empty_word() == reduce_at(w2, i2)); }
    assert(reduces_in_steps(w2, empty_word(), 1)) by { assert(reduces_one_step(w2, empty_word()) && reduces_in_steps(empty_word(), empty_word(), 0)); }
    assert(reduces_one_step(w1, w2)) by { assert(has_cancellation_at(w1, i1) && w2 == reduce_at(w1, i1)); }
    assert(reduces_in_steps(w1, empty_word(), 2)) by { assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, empty_word(), 1)); }
    assert(reduces_one_step(w0, w1)) by { assert(has_cancellation_at(w0, i0) && w1 == reduce_at(w0, i0)); }
    assert(reduces_in_steps(w0, empty_word(), 3)) by { assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, empty_word(), 2)); }
    assert(reduces_to(w0, empty_word())) by { assert(reduces_in_steps(w0, empty_word(), 3)); }
}

pub proof fn lemma_sub_valid()
    ensures crate::homomorphism::is_valid_homomorphism(sub_hom()),
{
    use crate::homomorphism::*;
    use crate::higman_operations::{free_group, lemma_free_group_valid};
    let h = sub_hom();
    lemma_m2_pres_valid();
    lemma_free_group_valid(3);
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], 3) by {
        assert(word_valid(h.generator_images[i], 3));
    }
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(h.target, apply_hom(h, #[trigger] h.source.relators[i]), empty_word()) by {
        // relator[0] = qaq′⁻¹b⁻¹ = [Gen2,Gen0,Inv3,Inv1] ; sub-image = [Gen2,Gen0,Inv0,Inv2,Gen1,Inv1]
        assert(thue_relator(m2_rules()[0]) =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]) by (compute);
        assert(h.source.relators[0] =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]);
        let img = seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(0), Symbol::Inv(2), Symbol::Gen(1), Symbol::Inv(1)];
        // compute on sub_hom() DIRECTLY — `by (compute)` does not see through the let-bound `h`
        assert(apply_hom(sub_hom(), seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Inv(3), Symbol::Inv(1)]) =~= img) by (compute);
        // img reduces to ε: @1(Gen0,Inv0)→[Gen2,Inv2,Gen1,Inv1] @0(Gen2,Inv2)→[Gen1,Inv1] @0→ε
        let w1: Word = seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Inv(1)];
        let w2: Word = seq![Symbol::Gen(1), Symbol::Inv(1)];
        assert(crate::reduction::has_cancellation_at(img, 1));
        assert(w1 == crate::reduction::reduce_at(img, 1)) by { assert(w1 =~= crate::reduction::reduce_at(img, 1)); }
        assert(crate::reduction::has_cancellation_at(w1, 0));
        assert(w2 == crate::reduction::reduce_at(w1, 0)) by { assert(w2 =~= crate::reduction::reduce_at(w1, 0)); }
        assert(crate::reduction::has_cancellation_at(w2, 0));
        assert(crate::reduction::reduce_at(w2, 0) == empty_word()) by { assert(crate::reduction::reduce_at(w2, 0) =~= empty_word()); }
        m2_reduces3(img, 1, w1, 0, w2, 0);
        crate::presentation_lemmas::lemma_reduces_to_equiv(free_group(3), img, empty_word());
    }
}

// ── group-equal ⟹ sub-images freely equivalent (the ⟹ engine's first step) ──
pub proof fn lemma_group_implies_sub_equal(u: Word, v: Word)
    requires equiv_in_presentation(rules_pres(m2_rules(), 4), u, v),
    ensures crate::reduction::freely_equivalent(
        crate::homomorphism::apply_hom(sub_hom(), u), crate::homomorphism::apply_hom(sub_hom(), v))
{
    use crate::homomorphism::*;
    use crate::higman_operations::free_group;
    lemma_sub_valid();
    lemma_hom_preserves_equiv(sub_hom(), u, v);
    crate::free_word_problem::lemma_free_group_equiv_freely_equivalent(3,
        apply_hom(sub_hom(), u), apply_hom(sub_hom(), v));
}

// ═══ PART B — normal form: every positive word is thue-equiv to a no-bq′ word ═══
// no_bq(w): w has no `bq′` substring  (b=Gen1, q′=Gen3).
pub open spec fn no_bq(w: Word) -> bool
    decreases w.len()
{
    w.len() <= 1 || (!(w[0] == Symbol::Gen(1) && w[1] == Symbol::Gen(3)) && no_bq(w.drop_first()))
}

pub open spec fn count_gen(w: Word, x: nat) -> nat
    decreases w.len()
{
    if w.len() == 0 { 0 }
    else { (if w[0] == Symbol::Gen(x) { 1nat } else { 0nat }) + count_gen(w.drop_first(), x) }
}

pub proof fn lemma_count_concat(a: Word, b: Word, x: nat)
    ensures count_gen(a + b, x) == count_gen(a, x) + count_gen(b, x)
    decreases a.len()
{
    if a.len() == 0 { assert(a + b =~= b); }
    else {
        lemma_count_concat(a.drop_first(), b, x);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert((a + b)[0] == a[0]);
    }
}

pub proof fn lemma_count_cons(t: Symbol, rest: Word, x: nat)
    ensures count_gen(seq![t] + rest, x) == (if t == Symbol::Gen(x) { 1nat } else { 0nat }) + count_gen(rest, x)
{
    assert((seq![t] + rest)[0] == t);
    assert((seq![t] + rest).drop_first() =~= rest);
}

// find a bq′ occurrence in a non-normal word
pub proof fn lemma_find_bq(w: Word)
    requires !no_bq(w),
    ensures exists|p: int| 0 <= p < w.len() - 1
        && #[trigger] w[p] == Symbol::Gen(1) && w[p + 1] == Symbol::Gen(3)
    decreases w.len()
{
    if !(w[0] == Symbol::Gen(1) && w[1] == Symbol::Gen(3)) {
        let df = w.drop_first();
        lemma_find_bq(df);
        let p0 = choose|p: int| 0 <= p < df.len() - 1
            && #[trigger] df[p] == Symbol::Gen(1) && df[p + 1] == Symbol::Gen(3);
        assert(w[p0 + 1] == df[p0]);
        assert(w[p0 + 2] == df[p0 + 1]);
    }
}

pub proof fn lemma_pos_sub2(w: Word, a: int, b: int)  // positive subrange (local, recursive)
    requires positive_word(w), 0 <= a <= b <= w.len(),
    ensures positive_word(w.subrange(a, b))
    decreases b - a
{
    let sub = w.subrange(a, b);
    if sub.len() > 0 {
        lemma_positive_gen(w, a);
        assert(sub[0] == w[a]);
        lemma_pos_sub2(w, a + 1, b);
        assert(sub.drop_first() =~= w.subrange(a + 1, b));
    }
}

pub proof fn lemma_pos_cat2(a: Word, b: Word)  // positive concat (local, recursive)
    requires positive_word(a), positive_word(b),
    ensures positive_word(a + b)
    decreases a.len()
{
    if a.len() == 0 { assert(a + b =~= b); }
    else {
        lemma_positive_gen(a, 0);
        assert((a + b)[0] == a[0]);
        lemma_pos_cat2(a.drop_first(), b);
        assert((a + b).drop_first() =~= a.drop_first() + b);
    }
}

// word_valid subrange/concat (used by nf construction)
pub proof fn lemma_wv_sub(w: Word, a: int, b: int, n: nat)
    requires word_valid(w, n), 0 <= a <= b <= w.len(),
    ensures word_valid(w.subrange(a, b), n),
{
    assert forall|i: int| 0 <= i < w.subrange(a, b).len() implies symbol_valid(#[trigger] w.subrange(a, b)[i], n) by { assert(w.subrange(a, b)[i] == w[a + i]); }
}
pub proof fn lemma_wv_cat(a: Word, b: Word, n: nat)
    requires word_valid(a, n), word_valid(b, n),
    ensures word_valid(a + b, n),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies symbol_valid(#[trigger] (a + b)[i], n) by {
        if i < a.len() { assert((a + b)[i] == a[i]); } else { assert((a + b)[i] == b[i - a.len()]); }
    }
}

// positive_word of a 2-literal + singleton helper
pub proof fn lemma_positive_singleton(t: Symbol)
    requires symbol_is_gen(t),
    ensures positive_word(seq![t]),
{
    assert(seq![t][0] == t);
    assert(seq![t].drop_first() =~= empty_word());
    assert(positive_word(empty_word()));
}

pub open spec fn m2_step_word(u: Word, p: int) -> Word {
    u.subrange(0, p) + seq![Symbol::Gen(2), Symbol::Gen(0)] + u.subrange(p + 2, u.len() as int)
}

// the heavy rewrite construction, extracted so nf_exists stays under the heartbeat budget
pub proof fn lemma_m2_step(u: Word, p: int)
    requires
        positive_word(u), word_valid(u, 4),
        0 <= p < u.len() - 1, u[p] == Symbol::Gen(1), u[p + 1] == Symbol::Gen(3),
    ensures
        positive_word(m2_step_word(u, p)), word_valid(m2_step_word(u, p), 4),
        thue_step(m2_rules(), u, m2_step_word(u, p)),
        count_gen(m2_step_word(u, p), 3) < count_gen(u, 3),
{
    let pre = u.subrange(0, p);
    let post = u.subrange(p + 2, u.len() as int);
    let mid2 = seq![Symbol::Gen(2), Symbol::Gen(0)];
    let up = m2_step_word(u, p);
    // thue step (bwd: l=rhs=bq′, rr=lhs=qa)
    assert(thue_step(m2_rules(), u, up)) by {
        assert(thue_step_at(m2_rules()[0], u, up, p, false)) by {
            assert(u.subrange(p, p + 2) =~= seq![Symbol::Gen(1), Symbol::Gen(3)]);
            assert(up =~= u.subrange(0, p) + mid2 + u.subrange(p + 2, u.len() as int));
        }
    }
    // positivity + validity of up
    lemma_pos_sub2(u, 0, p); lemma_pos_sub2(u, p + 2, u.len() as int);
    lemma_wv_sub(u, 0, p, 4); lemma_wv_sub(u, p + 2, u.len() as int, 4);
    lemma_positive_singleton(Symbol::Gen(2)); lemma_positive_singleton(Symbol::Gen(0));
    assert(mid2 =~= seq![Symbol::Gen(2)] + seq![Symbol::Gen(0)]);
    lemma_pos_cat2(seq![Symbol::Gen(2)], seq![Symbol::Gen(0)]);
    lemma_pos_cat2(pre, mid2); lemma_pos_cat2(pre + mid2, post);
    assert(word_valid(mid2, 4));
    lemma_wv_cat(pre, mid2, 4); lemma_wv_cat(pre + mid2, post, 4);
    // count decreases by 1
    assert(u =~= pre + seq![Symbol::Gen(1), Symbol::Gen(3)] + post);
    assert(count_gen(mid2, 3) == 0) by {
        assert(mid2 =~= seq![Symbol::Gen(2)] + seq![Symbol::Gen(0)]);
        lemma_count_cons(Symbol::Gen(2), seq![Symbol::Gen(0)], 3);
        assert(seq![Symbol::Gen(0)] =~= seq![Symbol::Gen(0)] + empty_word());
        lemma_count_cons(Symbol::Gen(0), empty_word(), 3);
    }
    assert(count_gen(seq![Symbol::Gen(1), Symbol::Gen(3)], 3) == 1) by {
        assert(seq![Symbol::Gen(1), Symbol::Gen(3)] =~= seq![Symbol::Gen(1)] + seq![Symbol::Gen(3)]);
        lemma_count_cons(Symbol::Gen(1), seq![Symbol::Gen(3)], 3);
        assert(seq![Symbol::Gen(3)] =~= seq![Symbol::Gen(3)] + empty_word());
        lemma_count_cons(Symbol::Gen(3), empty_word(), 3);
    }
    lemma_count_concat(pre + mid2, post, 3);
    lemma_count_concat(pre, mid2, 3);
    lemma_count_concat(pre + seq![Symbol::Gen(1), Symbol::Gen(3)], post, 3);
    lemma_count_concat(pre, seq![Symbol::Gen(1), Symbol::Gen(3)], 3);
}

// nf existence: positive valid u ⟹ ∃ no-bq′ positive valid w′ with thue_equiv(u, w′)
pub proof fn lemma_nf_exists(u: Word)
    requires positive_word(u), word_valid(u, 4),
    ensures exists|w2: Word| positive_word(w2) && word_valid(w2, 4) && no_bq(w2) && thue_equiv(m2_rules(), u, w2)
    decreases count_gen(u, 3)
{
    if no_bq(u) {
        lemma_thue_refl(m2_rules(), u);
        assert(positive_word(u) && word_valid(u, 4) && no_bq(u) && thue_equiv(m2_rules(), u, u));
    } else {
        lemma_find_bq(u);
        let p = choose|p: int| 0 <= p < u.len() - 1 && #[trigger] u[p] == Symbol::Gen(1) && u[p + 1] == Symbol::Gen(3);
        let up = m2_step_word(u, p);
        lemma_m2_step(u, p);
        lemma_thue_single(m2_rules(), u, up);
        lemma_nf_exists(up);
        let w2 = choose|w2: Word| positive_word(w2) && word_valid(w2, 4) && no_bq(w2) && thue_equiv(m2_rules(), up, w2);
        lemma_thue_trans(m2_rules(), u, up, w2);
    }
}

// ═══ PART C — no-cancellation readback: sub injective on no-bq′ words ═══
use crate::reduction::{is_reduced, has_cancellation_at, reduces_to, freely_equivalent,
    lemma_reduced_reduces_to_self};
use crate::homomorphism::{apply_hom, apply_hom_symbol};

pub open spec fn sub_img(j: nat) -> Word {
    if j == 0 { seq![Symbol::Gen(0)] }
    else if j == 1 { seq![Symbol::Gen(1)] }
    else if j == 2 { seq![Symbol::Gen(2)] }
    else { seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)] }
}

pub proof fn lemma_sub_sym(j: nat)
    requires j < 4,
    ensures apply_hom_symbol(sub_hom(), Symbol::Gen(j)) == sub_img(j),
{
    assert(sub_hom().generator_images[0] =~= seq![Symbol::Gen(0)]);
    assert(sub_hom().generator_images[1] =~= seq![Symbol::Gen(1)]);
    assert(sub_hom().generator_images[2] =~= seq![Symbol::Gen(2)]);
    assert(sub_hom().generator_images[3] =~= seq![Symbol::Inv(1), Symbol::Gen(2), Symbol::Gen(0)]);
    assert(apply_hom_symbol(sub_hom(), Symbol::Gen(j)) == sub_hom().generator_images[j as int]);
}

pub proof fn lemma_sub_cons(w: Word)
    requires w.len() > 0,
    ensures apply_hom(sub_hom(), w) =~=
        apply_hom_symbol(sub_hom(), w[0]) + apply_hom(sub_hom(), w.drop_first()),
{ assert(w.first() == w[0]); }

pub proof fn lemma_no_bq_tail(w: Word)
    requires no_bq(w), w.len() > 0,
    ensures no_bq(w.drop_first()),
{ }

pub proof fn lemma_reduced_concat(a: Word, b: Word)
    requires is_reduced(a), is_reduced(b),
        a.len() == 0 || b.len() == 0 || !is_inverse_pair(a[a.len() - 1], b[0]),
    ensures is_reduced(a + b),
{
    assert forall|i: int| 0 <= i < (a + b).len() - 1 implies !has_cancellation_at(a + b, i) by {
        if i + 1 < a.len() {
            assert((a + b)[i] == a[i] && (a + b)[i + 1] == a[i + 1]);
            assert(!has_cancellation_at(a, i));
        } else if i >= a.len() {
            assert((a + b)[i] == b[i - a.len()] && (a + b)[i + 1] == b[i + 1 - a.len()]);
            assert(!has_cancellation_at(b, i - a.len()));
        } else {
            assert((a + b)[i] == a[a.len() - 1] && (a + b)[i + 1] == b[0]);
        }
    }
}

pub proof fn lemma_sub_img_reduced(j: nat)
    requires j < 4,
    ensures is_reduced(sub_img(j)),
{ assert forall|i: int| 0 <= i < sub_img(j).len() - 1 implies !has_cancellation_at(sub_img(j), i) by { } }

// the seam: last(sub_img(j)) & first(sub_img(k)) are NOT an inverse pair unless (j,k)=(1,3)=`bq′`
pub proof fn lemma_sub_seam(j: nat, k: nat)
    requires j < 4, k < 4, !(j == 1 && k == 3),
    ensures !is_inverse_pair(sub_img(j)[sub_img(j).len() - 1], sub_img(k)[0]),
{
    // last(sub_img(j)) ∈ {Gen0(j=0),Gen1(j=1),Gen2(j=2),Gen0(j=3)} ; first(sub_img(k)) ∈ {Gen0,Gen1,Gen2,Inv1}
    let lj = sub_img(j)[sub_img(j).len() - 1];
    let fk = sub_img(k)[0];
    if k < 3 {
        assert(fk == Symbol::Gen(k));   // a Gen — never the inverse of a Gen
    } else {
        // k == 3, so j != 1 ; fk = Inv1, inverse pair needs lj == Gen1 ⟺ j == 1
        assert(fk == Symbol::Inv(1));
        assert(lj != Symbol::Gen(1));
    }
}

// sub(w) reduced for a no-bq′ positive valid word
pub proof fn lemma_sub_reduced(w: Word)
    requires positive_word(w), word_valid(w, 4), no_bq(w),
    ensures is_reduced(apply_hom(sub_hom(), w))
    decreases w.len()
{
    if w.len() == 0 {
        assert(apply_hom(sub_hom(), w) =~= empty_word());
    } else {
        lemma_positive_gen(w, 0);
        let j = choose|j: nat| w[0] == Symbol::Gen(j);
        assert(symbol_valid(w[0], 4));
        let rest = w.drop_first();
        lemma_sub_cons(w);
        lemma_sub_sym(j);
        lemma_sub_img_reduced(j);
        lemma_pos_sub2(w, 1, w.len() as int); assert(rest =~= w.subrange(1, w.len() as int));
        lemma_wv_sub(w, 1, w.len() as int, 4);
        lemma_no_bq_tail(w);
        lemma_sub_reduced(rest);
        if rest.len() > 0 {
            lemma_positive_gen(rest, 0);
            let k = choose|k: nat| rest[0] == Symbol::Gen(k);
            assert(symbol_valid(rest[0], 4));
            lemma_sub_cons(rest); lemma_sub_sym(k);
            assert(apply_hom(sub_hom(), rest)[0] == sub_img(k)[0]);
            // no_bq(w): w[0]=Gen1 && w[1]=Gen3 excluded ; w[1]==rest[0]
            assert(w[1] == rest[0]);
            assert(!(j == 1 && k == 3));
            lemma_sub_seam(j, k);
        }
        lemma_reduced_concat(apply_hom_symbol(sub_hom(), w[0]), apply_hom(sub_hom(), rest));
    }
}

// nonempty valid word ⟹ nonempty sub-image
pub proof fn lemma_sub_nonempty(w: Word)
    requires w.len() > 0, word_valid(w, 4), positive_word(w),
    ensures apply_hom(sub_hom(), w).len() > 0,
{
    lemma_positive_gen(w, 0);
    let j = choose|j: nat| w[0] == Symbol::Gen(j);
    assert(symbol_valid(w[0], 4));
    lemma_sub_cons(w); lemma_sub_sym(j);
    assert(sub_img(j).len() > 0);
}

// first symbols of the four letters are distinct ⟹ sub-image head determines the letter
pub proof fn lemma_sub_first_inj(jx: nat, jy: nat)
    requires jx < 4, jy < 4, sub_img(jx)[0] == sub_img(jy)[0],
    ensures jx == jy,
{ }

// THE READBACK: sub injective on no-bq′ positive valid words
pub proof fn lemma_sub_injective(x: Word, y: Word)
    requires
        positive_word(x), positive_word(y), word_valid(x, 4), word_valid(y, 4),
        no_bq(x), no_bq(y),
        apply_hom(sub_hom(), x) == apply_hom(sub_hom(), y),
    ensures x == y
    decreases x.len() + y.len()
{
    if x.len() == 0 {
        if y.len() > 0 { lemma_sub_nonempty(y); assert(apply_hom(sub_hom(), x) =~= empty_word()); }
        assert(x =~= y);
    } else if y.len() == 0 {
        lemma_sub_nonempty(x); assert(apply_hom(sub_hom(), y) =~= empty_word());
        assert(x =~= y);
    } else {
        lemma_positive_gen(x, 0); lemma_positive_gen(y, 0);
        let jx = choose|j: nat| x[0] == Symbol::Gen(j);
        let jy = choose|j: nat| y[0] == Symbol::Gen(j);
        assert(symbol_valid(x[0], 4)); assert(symbol_valid(y[0], 4));
        lemma_sub_cons(x); lemma_sub_cons(y);
        lemma_sub_sym(jx); lemma_sub_sym(jy);
        // heads: S(x)[0]==sub_img(jx)[0], S(y)[0]==sub_img(jy)[0]
        assert(apply_hom(sub_hom(), x)[0] == sub_img(jx)[0]);
        assert(apply_hom(sub_hom(), y)[0] == sub_img(jy)[0]);
        lemma_sub_first_inj(jx, jy);   // ⟹ jx == jy ⟹ x[0]==y[0]
        assert(x[0] == y[0]);
        // drop the common prefix sub_img(jx): S(x.drop_first())==S(y.drop_first())
        let xr = x.drop_first(); let yr = y.drop_first();
        assert(apply_hom(sub_hom(), x) =~= sub_img(jx) + apply_hom(sub_hom(), xr));
        assert(apply_hom(sub_hom(), y) =~= sub_img(jx) + apply_hom(sub_hom(), yr));
        assert(apply_hom(sub_hom(), xr) =~= apply_hom(sub_hom(), x).subrange(sub_img(jx).len() as int, apply_hom(sub_hom(), x).len() as int));
        assert(apply_hom(sub_hom(), yr) =~= apply_hom(sub_hom(), y).subrange(sub_img(jx).len() as int, apply_hom(sub_hom(), y).len() as int));
        assert(apply_hom(sub_hom(), xr) == apply_hom(sub_hom(), yr));
        lemma_pos_sub2(x, 1, x.len() as int); assert(xr =~= x.subrange(1, x.len() as int));
        lemma_pos_sub2(y, 1, y.len() as int); assert(yr =~= y.subrange(1, y.len() as int));
        lemma_wv_sub(x, 1, x.len() as int, 4); lemma_wv_sub(y, 1, y.len() as int, 4);
        lemma_no_bq_tail(x); lemma_no_bq_tail(y);
        lemma_sub_injective(xr, yr);
        assert(seq![x[0]] + xr =~= x); assert(seq![y[0]] + yr =~= y);
    }
}

// ═══ ASSEMBLE M2 POSITIVITY ═══
pub proof fn lemma_m2_forward(u: Word, v: Word)
    requires
        positive_word(u), positive_word(v), word_valid(u, 4), word_valid(v, 4),
        equiv_in_presentation(rules_pres(m2_rules(), 4), u, v),
    ensures thue_equiv(m2_rules(), u, v)
{
    use crate::higman_operations::{free_group, lemma_free_group_valid};
    use crate::homomorphism::lemma_apply_hom_word_valid;
    use crate::presentation_lemmas::lemma_freely_equivalent_implies_equiv;
    use crate::presentation::{lemma_equiv_symmetric, lemma_equiv_transitive};
    use crate::free_word_problem::lemma_free_group_equiv_freely_equivalent;
    let su = apply_hom(sub_hom(), u); let sv = apply_hom(sub_hom(), v);
    lemma_sub_valid(); lemma_free_group_valid(3);
    lemma_nf_exists(u); lemma_nf_exists(v);
    let nu = choose|w: Word| positive_word(w) && word_valid(w, 4) && no_bq(w) && thue_equiv(m2_rules(), u, w);
    let nv = choose|w: Word| positive_word(w) && word_valid(w, 4) && no_bq(w) && thue_equiv(m2_rules(), v, w);
    let snu = apply_hom(sub_hom(), nu); let snv = apply_hom(sub_hom(), nv);
    lemma_m2_backward(u, nu); lemma_m2_backward(v, nv);
    lemma_group_implies_sub_equal(u, nu);   // freely_eq(su, snu)
    lemma_group_implies_sub_equal(u, v);    // freely_eq(su, sv)
    lemma_group_implies_sub_equal(v, nv);   // freely_eq(sv, snv)
    lemma_apply_hom_word_valid(sub_hom(), u); lemma_apply_hom_word_valid(sub_hom(), v);
    lemma_apply_hom_word_valid(sub_hom(), nu); lemma_apply_hom_word_valid(sub_hom(), nv);
    lemma_freely_equivalent_implies_equiv(free_group(3), su, snu);
    lemma_freely_equivalent_implies_equiv(free_group(3), su, sv);
    lemma_freely_equivalent_implies_equiv(free_group(3), sv, snv);
    lemma_equiv_symmetric(free_group(3), su, snu);            // equiv(snu, su)
    lemma_equiv_transitive(free_group(3), snu, su, sv);       // equiv(snu, sv)
    lemma_equiv_transitive(free_group(3), snu, sv, snv);      // equiv(snu, snv)
    lemma_free_group_equiv_freely_equivalent(3, snu, snv);   // freely_eq(snu, snv)
    lemma_sub_reduced(nu); lemma_sub_reduced(nv);
    let w = choose|w: Word| reduces_to(snu, w) && reduces_to(snv, w);
    lemma_reduced_reduces_to_self(snu, w); lemma_reduced_reduces_to_self(snv, w);  // snu == snv
    lemma_sub_injective(nu, nv);                             // nu == nv
    assert(thue_equiv(m2_rules(), u, nv));                   // thue(u,nu) + nu==nv
    lemma_thue_symmetric(m2_rules(), v, nv);                // thue(nv, v)
    lemma_thue_trans(m2_rules(), u, nv, v);                 // thue(u, v)
}

pub proof fn lemma_m2_positivity()
    ensures positivity(m2_rules(), 4)
{
    assert forall|u: Word, v: Word|
        positive_word(u) && positive_word(v) && word_valid(u, 4) && word_valid(v, 4)
        implies (#[trigger] equiv_in_presentation(rules_pres(m2_rules(), 4), u, v)
            <==> thue_equiv(m2_rules(), u, v)) by {
        if equiv_in_presentation(rules_pres(m2_rules(), 4), u, v) { lemma_m2_forward(u, v); }
        if thue_equiv(m2_rules(), u, v) { lemma_m2_backward(u, v); }
    }
}

} // verus!