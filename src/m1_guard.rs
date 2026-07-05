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

// ═══ PART A — group-equal ⟹ same delete_n AND same delete_g (two projections) ═══
// kill_hom(x): rules_pres → free_group(4), Gen(x) ↦ ε, others fixed.  x∈{2,3} (g,n).

pub open spec fn kill_hom(x: nat) -> crate::homomorphism::HomomorphismData {
    crate::homomorphism::HomomorphismData {
        source: rules_pres(m1_rules(), 4),
        target: crate::higman_operations::free_group(4),
        generator_images: Seq::new(4, |i: int|
            if i == x { empty_word() } else { seq![Symbol::Gen(i as nat)] }),
    }
}

pub proof fn lemma_kill_valid(x: nat)
    requires x == 2 || x == 3,
    ensures crate::homomorphism::is_valid_homomorphism(kill_hom(x)),
{
    use crate::homomorphism::*;
    use crate::higman_operations::{free_group, lemma_free_group_valid};
    let h = kill_hom(x);
    lemma_m1_pres_valid();
    lemma_free_group_valid(4);
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], 4) by {
        assert(word_valid(h.generator_images[i], 4));
    }
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(h.target, apply_hom(h, #[trigger] h.source.relators[i]), empty_word()) by {
        // relators[0] = thue_relator(gn=ng) = [Gen2,Gen3,Inv2,Inv3]
        assert(thue_relator(m1_rules()[0]) =~= seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Inv(2), Symbol::Inv(3)]) by (compute);
        assert(h.source.relators[0] =~= seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Inv(2), Symbol::Inv(3)]);
        if x == 3 {
            assert(apply_hom(kill_hom(3), seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Inv(2), Symbol::Inv(3)])
                =~= seq![Symbol::Gen(2), Symbol::Inv(2)]) by (compute);
            crate::presentation_lemmas::lemma_word_inverse_right(free_group(4), seq![Symbol::Gen(2)]);
            assert(inverse_word(seq![Symbol::Gen(2)]) =~= seq![Symbol::Inv(2)]) by (compute);
            assert(concat(seq![Symbol::Gen(2)], inverse_word(seq![Symbol::Gen(2)])) =~= seq![Symbol::Gen(2), Symbol::Inv(2)]);
        } else {
            assert(apply_hom(kill_hom(2), seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Inv(2), Symbol::Inv(3)])
                =~= seq![Symbol::Gen(3), Symbol::Inv(3)]) by (compute);
            crate::presentation_lemmas::lemma_word_inverse_right(free_group(4), seq![Symbol::Gen(3)]);
            assert(inverse_word(seq![Symbol::Gen(3)]) =~= seq![Symbol::Inv(3)]) by (compute);
            assert(concat(seq![Symbol::Gen(3)], inverse_word(seq![Symbol::Gen(3)])) =~= seq![Symbol::Gen(3), Symbol::Inv(3)]);
        }
    }
}

// apply_hom(kill_hom(x), u) = delete_x(u, x) on positive words.
pub proof fn lemma_applyhom_kill_eq_delete(x: nat, u: Word)
    requires positive_word(u), word_valid(u, 4),
    ensures crate::homomorphism::apply_hom(kill_hom(x), u) =~= delete_x(u, x),
    decreases u.len(),
{
    use crate::homomorphism::*;
    if u.len() > 0 {
        let s = u.first();
        let rest = u.drop_first();
        assert(positive_word(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies exists|j: nat| #[trigger] rest[i] == Symbol::Gen(j) by {
                assert(rest[i] == u[i + 1]);
            }
        }
        assert(word_valid(rest, 4)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 4) by {
                assert(rest[i] == u[i + 1]);
            }
        }
        lemma_applyhom_kill_eq_delete(x, rest);
        let j = choose|j: nat| u[0] == Symbol::Gen(j);
        assert(u[0] == Symbol::Gen(j));
        assert(apply_hom_symbol(kill_hom(x), Symbol::Gen(j)) =~= kill_hom(x).generator_images[j as int]);
    }
}

pub proof fn lemma_delete_positive(u: Word, x: nat)
    ensures positive_word(u) ==> positive_word(delete_x(u, x))
        && (word_valid(u, 4) ==> word_valid(delete_x(u, x), 4)),
    decreases u.len(),
{
    if u.len() > 0 {
        lemma_delete_positive(u.drop_first(), x);
        if u[0] != Symbol::Gen(x) {
            assert(delete_x(u, x) =~= seq![u[0]] + delete_x(u.drop_first(), x));
        }
    }
}

// group-equal ⟹ same delete_n (x=3) and same delete_g (x=2).  Per-x helper:
pub proof fn lemma_kill_gives_same_delete(x: nat, u: Word, v: Word)
    requires
        x == 2 || x == 3,
        positive_word(u), positive_word(v), word_valid(u, 4), word_valid(v, 4),
        equiv_in_presentation(rules_pres(m1_rules(), 4), u, v),
    ensures delete_x(u, x) == delete_x(v, x),
{
    use crate::homomorphism::*;
    use crate::higman_operations::free_group;
    lemma_kill_valid(x);
    lemma_hom_preserves_equiv(kill_hom(x), u, v);
    lemma_applyhom_kill_eq_delete(x, u);
    lemma_applyhom_kill_eq_delete(x, v);
    // equiv(free4, delete_x(u,x), delete_x(v,x))
    crate::free_word_problem::lemma_free_group_equiv_freely_equivalent(4, delete_x(u, x), delete_x(v, x));
    let du = delete_x(u, x);
    let dv = delete_x(v, x);
    lemma_delete_positive(u, x);
    lemma_delete_positive(v, x);
    lemma_positive_reduced(du);
    lemma_positive_reduced(dv);
    // freely_equivalent(du,dv) + both reduced ⟹ du == dv
    let w = choose|w: Word| crate::reduction::reduces_to(du, w) && crate::reduction::reduces_to(dv, w);
    crate::reduction::lemma_reduced_reduces_to_self(du, w);
    crate::reduction::lemma_reduced_reduces_to_self(dv, w);
}

pub proof fn lemma_group_implies_same_deletes(u: Word, v: Word)
    requires
        positive_word(u), positive_word(v), word_valid(u, 4), word_valid(v, 4),
        equiv_in_presentation(rules_pres(m1_rules(), 4), u, v),
    ensures delete_x(u, 3) == delete_x(v, 3), delete_x(u, 2) == delete_x(v, 2),
{
    lemma_kill_gives_same_delete(3, u, v);
    lemma_kill_gives_same_delete(2, u, v);
}

// ═══ PART B — combinatorial completeness: same deletes ⟹ thue_equiv ═══
// leading-run splitter + the two bubble lemmas (move a letter to the front of a run).

pub open spec fn lead(w: Word, x: nat) -> nat
    decreases w.len()
{
    if w.len() > 0 && w[0] == Symbol::Gen(x) { (1 + lead(w.drop_first(), x)) as nat } else { 0 }
}

pub proof fn lemma_lead_run(w: Word, x: nat)
    ensures
        lead(w, x) <= w.len(),
        forall|i: int| 0 <= i < lead(w, x) ==> #[trigger] w[i] == Symbol::Gen(x),
        lead(w, x) < w.len() ==> w[lead(w, x) as int] != Symbol::Gen(x),
    decreases w.len()
{
    if w.len() > 0 && w[0] == Symbol::Gen(x) {
        lemma_lead_run(w.drop_first(), x);
        assert forall|i: int| 0 <= i < lead(w, x) implies #[trigger] w[i] == Symbol::Gen(x) by {
            if i > 0 { assert(w[i] == w.drop_first()[i - 1]); }
        }
        if lead(w, x) < w.len() {
            assert(w[lead(w, x) as int] == w.drop_first()[lead(w, x) as int - 1]);
        }
    }
}

// bubble a g to the front of a run of n's:  n^k · g · rest  ~  g · n^k · rest
pub proof fn lemma_bubble_g(run: Word, rest: Word)
    requires forall|i: int| 0 <= i < run.len() ==> #[trigger] run[i] == Symbol::Gen(3),
    ensures thue_equiv(m1_rules(),
        run + seq![Symbol::Gen(2)] + rest, seq![Symbol::Gen(2)] + run + rest),
    decreases run.len()
{
    let g = seq![Symbol::Gen(2)];
    if run.len() == 0 {
        assert(run + g + rest =~= g + rest);
        assert(g + run + rest =~= g + rest);
        lemma_thue_refl(m1_rules(), g + rest);
    } else {
        let run2 = run.drop_first();
        assert(run[0] == Symbol::Gen(3));
        assert forall|i: int| 0 <= i < run2.len() implies #[trigger] run2[i] == Symbol::Gen(3) by {
            assert(run2[i] == run[i + 1]);
        }
        lemma_bubble_g(run2, rest);                       // run2·g·rest ~ g·run2·rest
        lemma_thue_prepend(m1_rules(), Symbol::Gen(3), run2 + g + rest, g + run2 + rest);
        // [Gen3]·(run2·g·rest) = run·g·rest ; [Gen3]·(g·run2·rest) = [Gen3,Gen2]·run2·rest
        assert(seq![Symbol::Gen(3)] + (run2 + g + rest) =~= run + g + rest);
        let x = run2 + rest;
        assert(seq![Symbol::Gen(3)] + (g + run2 + rest)
            =~= seq![Symbol::Gen(3), Symbol::Gen(2)] + x);
        // swap [Gen3,Gen2]·x ~ [Gen2,Gen3]·x  (ng → gn, bwd step at pos 0)
        assert(thue_step(m1_rules(), seq![Symbol::Gen(3), Symbol::Gen(2)] + x,
                                      seq![Symbol::Gen(2), Symbol::Gen(3)] + x)) by {
            assert(thue_step_at(m1_rules()[0], seq![Symbol::Gen(3), Symbol::Gen(2)] + x,
                                                seq![Symbol::Gen(2), Symbol::Gen(3)] + x, 0, false)) by {
                assert((seq![Symbol::Gen(3), Symbol::Gen(2)] + x).subrange(0, 2) =~= seq![Symbol::Gen(3), Symbol::Gen(2)]);
                assert(seq![Symbol::Gen(2), Symbol::Gen(3)] + x
                    =~= (seq![Symbol::Gen(3), Symbol::Gen(2)] + x).subrange(0, 0)
                        + seq![Symbol::Gen(2), Symbol::Gen(3)]
                        + (seq![Symbol::Gen(3), Symbol::Gen(2)] + x).subrange(2, (2 + x.len()) as int));
            }
        }
        lemma_thue_single(m1_rules(), seq![Symbol::Gen(3), Symbol::Gen(2)] + x,
                                       seq![Symbol::Gen(2), Symbol::Gen(3)] + x);
        assert(seq![Symbol::Gen(2), Symbol::Gen(3)] + x =~= g + run + rest);
        // chain: run·g·rest ~ [Gen3,Gen2]·x ~ [Gen2,Gen3]·x = g·run·rest
        lemma_thue_trans(m1_rules(), run + g + rest,
            seq![Symbol::Gen(3), Symbol::Gen(2)] + x, seq![Symbol::Gen(2), Symbol::Gen(3)] + x);
    }
}

// mirror: bubble an n to the front of a run of g's:  g^k · n · rest  ~  n · g^k · rest
pub proof fn lemma_bubble_n(run: Word, rest: Word)
    requires forall|i: int| 0 <= i < run.len() ==> #[trigger] run[i] == Symbol::Gen(2),
    ensures thue_equiv(m1_rules(),
        run + seq![Symbol::Gen(3)] + rest, seq![Symbol::Gen(3)] + run + rest),
    decreases run.len()
{
    let n = seq![Symbol::Gen(3)];
    if run.len() == 0 {
        assert(run + n + rest =~= n + rest);
        assert(n + run + rest =~= n + rest);
        lemma_thue_refl(m1_rules(), n + rest);
    } else {
        let run2 = run.drop_first();
        assert(run[0] == Symbol::Gen(2));
        assert forall|i: int| 0 <= i < run2.len() implies #[trigger] run2[i] == Symbol::Gen(2) by {
            assert(run2[i] == run[i + 1]);
        }
        lemma_bubble_n(run2, rest);
        lemma_thue_prepend(m1_rules(), Symbol::Gen(2), run2 + n + rest, n + run2 + rest);
        assert(seq![Symbol::Gen(2)] + (run2 + n + rest) =~= run + n + rest);
        let x = run2 + rest;
        assert(seq![Symbol::Gen(2)] + (n + run2 + rest)
            =~= seq![Symbol::Gen(2), Symbol::Gen(3)] + x);
        // swap [Gen2,Gen3]·x ~ [Gen3,Gen2]·x  (gn → ng, FWD step at pos 0)
        assert(thue_step(m1_rules(), seq![Symbol::Gen(2), Symbol::Gen(3)] + x,
                                      seq![Symbol::Gen(3), Symbol::Gen(2)] + x)) by {
            assert(thue_step_at(m1_rules()[0], seq![Symbol::Gen(2), Symbol::Gen(3)] + x,
                                                seq![Symbol::Gen(3), Symbol::Gen(2)] + x, 0, true)) by {
                assert((seq![Symbol::Gen(2), Symbol::Gen(3)] + x).subrange(0, 2) =~= seq![Symbol::Gen(2), Symbol::Gen(3)]);
                assert(seq![Symbol::Gen(3), Symbol::Gen(2)] + x
                    =~= (seq![Symbol::Gen(2), Symbol::Gen(3)] + x).subrange(0, 0)
                        + seq![Symbol::Gen(3), Symbol::Gen(2)]
                        + (seq![Symbol::Gen(2), Symbol::Gen(3)] + x).subrange(2, (2 + x.len()) as int));
            }
        }
        lemma_thue_single(m1_rules(), seq![Symbol::Gen(2), Symbol::Gen(3)] + x,
                                       seq![Symbol::Gen(3), Symbol::Gen(2)] + x);
        assert(seq![Symbol::Gen(3), Symbol::Gen(2)] + x =~= n + run + rest);
        lemma_thue_trans(m1_rules(), run + n + rest,
            seq![Symbol::Gen(2), Symbol::Gen(3)] + x, seq![Symbol::Gen(3), Symbol::Gen(2)] + x);
    }
}

} // verus!