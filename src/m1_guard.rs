// m1_guard.rs — M-ladder rung M1 (guard motion): positivity of  ⟨a,b,g,n | gn = ng⟩.
//
// docs/semantic-finite-basis.md §4.1. The group is F(a,b) ∗ ℤ².  positivity(m1_rules, 4):
//   for positive u,v over {a,b,g,n}:  u = v in the group  ⟺  u ↔*_{gn=ng} v.
//
// ⟸ (Thue ⟹ group): immediate from thue.rs (`lemma_thue_implies_group`).
// ⟹ (group ⟹ Thue): the TWO-PROJECTION route (not free-product NF): kill_n: G→F(a,b,g)
//   and kill_g: G→F(a,b,n) are valid homs; group-equal ⟹ same delete_n AND same delete_g
//   (each via the free-group word problem); and (delete_n, delete_g) is a COMPLETE Thue-invariant
//   (they pin everything but g-vs-n order within a gap, which is exactly gn=ng). [checkpoint 2/3]
//
// Alphabet:  a = Gen(0)  b = Gen(1)  g = Gen(2)  n = Gen(3).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::thue::*;

verus! {

pub open spec fn m1_rules() -> Seq<ThueRule> {
    seq![ ThueRule {
        lhs: seq![Symbol::Gen(2), Symbol::Gen(3)],   // g n
        rhs: seq![Symbol::Gen(3), Symbol::Gen(2)],   // n g
    } ]
}

pub proof fn lemma_m1_rules_valid()
    ensures
        forall|r: int| 0 <= r < m1_rules().len() ==>
            word_valid(#[trigger] m1_rules()[r].lhs, 4) && word_valid(m1_rules()[r].rhs, 4),
{
    assert forall|r: int| 0 <= r < m1_rules().len() implies
        word_valid(#[trigger] m1_rules()[r].lhs, 4) && word_valid(m1_rules()[r].rhs, 4) by {
        assert(word_valid(m1_rules()[0].lhs, 4));
        assert(word_valid(m1_rules()[0].rhs, 4));
    }
}

pub proof fn lemma_m1_pres_valid()
    ensures presentation_valid(rules_pres(m1_rules(), 4))
{
    reveal(presentation_valid);
    let p = rules_pres(m1_rules(), 4);
    lemma_m1_rules_valid();
    assert forall|i: int| 0 <= i < p.relators.len() implies word_valid(#[trigger] p.relators[i], 4) by {
        assert(p.relators[0] =~= thue_relator(m1_rules()[0]));
        let l = m1_rules()[0].lhs;
        let rr = m1_rules()[0].rhs;
        lemma_inverse_word_valid(rr, 4);   // inverse_word(rr) valid in 4
        assert forall|k: int| 0 <= k < concat(l, inverse_word(rr)).len()
            implies symbol_valid(#[trigger] concat(l, inverse_word(rr))[k], 4) by {
            if k < l.len() { assert(concat(l, inverse_word(rr))[k] == l[k]); }
            else { assert(concat(l, inverse_word(rr))[k] == inverse_word(rr)[k - l.len()]); }
        }
        assert(word_valid(concat(l, inverse_word(rr)), 4));
        assert(thue_relator(m1_rules()[0]) =~= concat(l, inverse_word(rr)));
    }
}

// ── ⟸  Thue ⟹ group (the easy half of positivity, from thue.rs) ──
pub proof fn lemma_m1_backward(u: Word, v: Word)
    requires
        word_valid(u, 4),
        thue_equiv(m1_rules(), u, v),
    ensures equiv_in_presentation(rules_pres(m1_rules(), 4), u, v)
{
    lemma_m1_pres_valid();
    lemma_m1_rules_valid();
    lemma_thue_implies_group(m1_rules(), 4, u, v);
}

// ── delete_x: remove all Gen(x) letters — the projection at the word level ──
pub open spec fn delete_x(w: Word, x: nat) -> Word
    decreases w.len()
{
    if w.len() == 0 {
        empty_word()
    } else if w[0] == Symbol::Gen(x) {
        delete_x(w.drop_first(), x)
    } else {
        seq![w[0]] + delete_x(w.drop_first(), x)
    }
}

pub proof fn lemma_delete_concat(a: Word, b: Word, x: nat)
    ensures delete_x(concat(a, b), x) =~= concat(delete_x(a, x), delete_x(b, x))
    decreases a.len()
{
    if a.len() == 0 {
        assert(concat(a, b) =~= b);
        assert(delete_x(a, x) =~= empty_word());
    } else {
        lemma_delete_concat(a.drop_first(), b, x);
        assert(concat(a, b).drop_first() =~= concat(a.drop_first(), b));
        assert(concat(a, b)[0] == a[0]);
    }
}

// delete_x is idempotent-flavored: it never contains Gen(x)
pub proof fn lemma_delete_removes(w: Word, x: nat)
    ensures forall|i: int| 0 <= i < delete_x(w, x).len() ==> #[trigger] delete_x(w, x)[i] != Symbol::Gen(x)
    decreases w.len()
{
    if w.len() > 0 {
        lemma_delete_removes(w.drop_first(), x);
        if w[0] != Symbol::Gen(x) {
            assert(delete_x(w, x) =~= seq![w[0]] + delete_x(w.drop_first(), x));
        }
    }
}

// positive words are freely reduced (only Gen letters, no adjacent inverse pairs)
pub proof fn lemma_positive_reduced(w: Word)
    requires positive_word(w)
    ensures crate::reduction::is_reduced(w)
{
    assert forall|i: int| 0 <= i < w.len() - 1 implies
        !crate::reduction::has_cancellation_at(w, i) by {
        let j0 = choose|j: nat| w[i] == Symbol::Gen(j);
        let j1 = choose|j: nat| w[i + 1] == Symbol::Gen(j);
        // both Gen ⟹ not an inverse pair
    }
}

} // verus!