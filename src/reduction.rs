use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;

verus! {

///  A word has a cancellation at position i: symbols at i and i+1 are inverse pairs.
pub open spec fn has_cancellation_at(w: Word, i: int) -> bool {
    0 <= i < w.len() - 1 && is_inverse_pair(w[i], w[i + 1])
}

///  A word has at least one cancellation somewhere.
pub open spec fn has_cancellation(w: Word) -> bool {
    exists|i: int| has_cancellation_at(w, i)
}

///  A word is freely reduced: no adjacent inverse pairs.
pub open spec fn is_reduced(w: Word) -> bool {
    !has_cancellation(w)
}

///  Remove the inverse pair at position i, producing a shorter word.
///  w[0..i] ++ w[i+2..]
pub open spec fn reduce_at(w: Word, i: int) -> Word
    recommends
        has_cancellation_at(w, i),
{
    w.subrange(0, i) + w.subrange(i + 2, w.len() as int)
}

///  reduce_at decreases length by 2.
pub proof fn lemma_reduce_at_len(w: Word, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        reduce_at(w, i).len() == w.len() - 2,
{
}

///  reduce_at preserves elements outside the cancelled pair.
pub proof fn lemma_reduce_at_elements(w: Word, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        forall|k: int| 0 <= k < i ==> #[trigger] reduce_at(w, i)[k] == w[k],
        forall|k: int| i <= k < reduce_at(w, i).len() ==> #[trigger] reduce_at(w, i)[k] == w[k + 2],
{
}

///  Single-step free reduction: w1 reduces to w2 by removing one inverse pair.
pub open spec fn reduces_one_step(w1: Word, w2: Word) -> bool {
    exists|i: int| has_cancellation_at(w1, i) && w2 == reduce_at(w1, i)
}

///  Multi-step free reduction: transitive-reflexive closure.
///  w1 reduces to w2 in at most `n` steps.
pub open spec fn reduces_in_steps(w1: Word, w2: Word, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        w1 == w2
    } else {
        w1 == w2 || exists|w_mid: Word|
            reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat)
    }
}

///  w1 freely reduces to w2 (in some number of steps).
pub open spec fn reduces_to(w1: Word, w2: Word) -> bool {
    exists|n: nat| reduces_in_steps(w1, w2, n)
}

///  Two words are freely equivalent (connected by reductions and expansions).
pub open spec fn freely_equivalent(w1: Word, w2: Word) -> bool {
    exists|w: Word| reduces_to(w1, w) && reduces_to(w2, w)
}

//  --- Basic reduction lemmas ---

///  Every word reduces to itself (0 steps).
pub proof fn lemma_reduces_to_refl(w: Word)
    ensures
        reduces_to(w, w),
{
    assert(reduces_in_steps(w, w, 0));
}

///  If w1 reduces to w2 in n steps, it also reduces in n+1 steps.
pub proof fn lemma_reduces_in_steps_monotone(w1: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w2, n),
    ensures
        reduces_in_steps(w1, w2, (n + 1) as nat),
    decreases n,
{
    if n == 0 {
    } else {
        if w1 == w2 {
        } else {
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
            lemma_reduces_in_steps_monotone(w_mid, w2, (n - 1) as nat);
            assert(reduces_in_steps(w_mid, w2, n as nat));
        }
    }
}

///  Transitivity: if w1 →* w2 and w2 →* w3, then w1 →* w3.
pub proof fn lemma_reduces_to_transitive(w1: Word, w2: Word, w3: Word)
    requires
        reduces_to(w1, w2),
        reduces_to(w2, w3),
    ensures
        reduces_to(w1, w3),
{
    let n1 = choose|n: nat| reduces_in_steps(w1, w2, n);
    let n2 = choose|n: nat| reduces_in_steps(w2, w3, n);
    lemma_reduces_chain(w1, w2, w3, n1, n2);
}

///  Helper: chaining reductions with explicit step counts.
proof fn lemma_reduces_chain(w1: Word, w2: Word, w3: Word, n1: nat, n2: nat)
    requires
        reduces_in_steps(w1, w2, n1),
        reduces_in_steps(w2, w3, n2),
    ensures
        reduces_to(w1, w3),
    decreases n1,
{
    if n1 == 0 {
        assert(reduces_in_steps(w1, w3, n2));
    } else {
        if w1 == w2 {
            assert(reduces_in_steps(w1, w3, n2));
        } else {
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n1 - 1) as nat);
            lemma_reduces_chain(w_mid, w2, w3, (n1 - 1) as nat, n2);
            let n3 = choose|n: nat| reduces_in_steps(w_mid, w3, n);
            assert(reduces_in_steps(w1, w3, (n3 + 1) as nat));
        }
    }
}

///  A reduced word has no cancellations, so it doesn't reduce further.
pub proof fn lemma_reduced_no_step(w: Word)
    requires
        is_reduced(w),
    ensures
        !exists|w2: Word| reduces_one_step(w, w2),
{
}

///  The empty word is reduced.
pub proof fn lemma_empty_is_reduced()
    ensures
        is_reduced(empty_word()),
{
    assert forall|i: int| !has_cancellation_at(empty_word(), i) by {
    }
}

///  A single symbol is reduced.
pub proof fn lemma_singleton_is_reduced(s: Symbol)
    ensures
        is_reduced(Seq::new(1, |_i: int| s)),
{
    let w = Seq::new(1, |_i: int| s);
    assert forall|i: int| !has_cancellation_at(w, i) by {
    }
}

///  Free equivalence is reflexive.
pub proof fn lemma_freely_equivalent_refl(w: Word)
    ensures
        freely_equivalent(w, w),
{
    lemma_reduces_to_refl(w);
}

///  Free equivalence is symmetric.
pub proof fn lemma_freely_equivalent_sym(w1: Word, w2: Word)
    requires
        freely_equivalent(w1, w2),
    ensures
        freely_equivalent(w2, w1),
{
    let w = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    assert(reduces_to(w2, w) && reduces_to(w1, w));
}

///  Free equivalence is transitive.
pub proof fn lemma_freely_equivalent_trans(w1: Word, w2: Word, w3: Word)
    requires
        freely_equivalent(w1, w2),
        freely_equivalent(w2, w3),
    ensures
        freely_equivalent(w1, w3),
{
    //  w1 →* u ←* w2 →* v ←* w3
    let u = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    let v = choose|w: Word| reduces_to(w2, w) && reduces_to(w3, w);
    //  By confluence on w2 →* u and w2 →* v: ∃ t. u →* t ∧ v →* t
    lemma_confluence(w2, u, v);
    let t = choose|t: Word| reduces_to(u, t) && reduces_to(v, t);
    //  w1 →* u →* t and w3 →* v →* t
    lemma_reduces_to_transitive(w1, u, t);
    lemma_reduces_to_transitive(w3, v, t);
}

//  ============================================================
//  Church-Rosser (Confluence) via Newman's Lemma
//  ============================================================

///  One step of reduction decreases word length by exactly 2.
pub proof fn lemma_one_step_decreases_len(w1: Word, w2: Word)
    requires
        reduces_one_step(w1, w2),
    ensures
        w2.len() == w1.len() - 2,
{
    let i = choose|i: int| has_cancellation_at(w1, i) && w2 == reduce_at(w1, i);
    lemma_reduce_at_len(w1, i);
}

///  Multi-step reduction never increases word length.
pub proof fn lemma_reduces_to_len(w1: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w2, n),
    ensures
        w2.len() <= w1.len(),
    decreases n,
{
    if n == 0 {
    } else if w1 == w2 {
    } else {
        let w_mid = choose|w_mid: Word|
            reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
        lemma_one_step_decreases_len(w1, w_mid);
        lemma_reduces_to_len(w_mid, w2, (n - 1) as nat);
    }
}

///  Confluence: if w →* w1 and w →* w2, then ∃ w3. w1 →* w3 ∧ w2 →* w3.
///
///  Proof by induction on |w| (word length). Uses:
///  - Termination: each reduction step decreases length by 2
///  - Local confluence: if w →¹ w1 and w →¹ w2, then ∃ w3. w1 →* w3 ∧ w2 →* w3
///  - Newman's lemma: termination + local confluence → confluence
pub proof fn lemma_confluence(w: Word, w1: Word, w2: Word)
    requires
        reduces_to(w, w1),
        reduces_to(w, w2),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
    decreases w.len(),
{
    let n1 = choose|n: nat| reduces_in_steps(w, w1, n);
    let n2 = choose|n: nat| reduces_in_steps(w, w2, n);

    if n1 == 0 || w == w1 {
        //  w == w1
        lemma_reduces_to_refl(w2);
        assert(reduces_in_steps(w, w2, n2));
    } else if n2 == 0 || w == w2 {
        //  w == w2
        lemma_reduces_to_refl(w1);
        assert(reduces_in_steps(w, w1, n1));
    } else {
        //  w →¹ wa →* w1 and w →¹ wb →* w2
        let wa = choose|wa: Word|
            reduces_one_step(w, wa) && reduces_in_steps(wa, w1, (n1 - 1) as nat);
        let wb = choose|wb: Word|
            reduces_one_step(w, wb) && reduces_in_steps(wb, w2, (n2 - 1) as nat);

        //  wa, wb have length w.len() - 2
        lemma_one_step_decreases_len(w, wa);
        lemma_one_step_decreases_len(w, wb);

        //  By local confluence: ∃ wc. wa →* wc ∧ wb →* wc
        lemma_local_confluence(w, wa, wb);
        let wc = choose|wc: Word| reduces_to(wa, wc) && reduces_to(wb, wc);

        //  wc.len() <= wa.len() = w.len() - 2 < w.len()
        let nc_a = choose|n: nat| reduces_in_steps(wa, wc, n);
        lemma_reduces_to_len(wa, wc, nc_a);

        //  IH on wa: confluence of (wa →* w1, wa →* wc)
        lemma_confluence(wa, w1, wc);
        let d = choose|d: Word| reduces_to(w1, d) && reduces_to(wc, d);

        //  IH on wb: confluence of (wb →* w2, wb →* wc)
        lemma_confluence(wb, w2, wc);
        let e = choose|e: Word| reduces_to(w2, e) && reduces_to(wc, e);

        //  IH on wc: confluence of (wc →* d, wc →* e)
        lemma_confluence(wc, d, e);
        let w3 = choose|w3: Word| reduces_to(d, w3) && reduces_to(e, w3);

        //  Chain: w1 →* d →* w3 and w2 →* e →* w3
        lemma_reduces_to_transitive(w1, d, w3);
        lemma_reduces_to_transitive(w2, e, w3);
    }
}

//  ============================================================
//  Church-Rosser / Confluence
//  ============================================================

///  Find the first cancellation position, searching from index `start`.
///  Returns the first i >= start with a cancellation, or w.len() if none.
pub open spec fn find_cancellation_from(w: Word, start: nat) -> nat
    decreases w.len() - start,
{
    if start >= w.len() - 1 {
        w.len()
    } else if is_inverse_pair(w[start as int], w[start as int + 1]) {
        start
    } else {
        find_cancellation_from(w, start + 1)
    }
}

///  find_cancellation_from returns a valid cancellation or w.len().
pub proof fn lemma_find_cancellation_from_valid(w: Word, start: nat)
    ensures
        find_cancellation_from(w, start) < w.len() ==>
            has_cancellation_at(w, find_cancellation_from(w, start) as int),
    decreases w.len() - start,
{
    if start >= w.len() - 1 {
    } else if is_inverse_pair(w[start as int], w[start as int + 1]) {
    } else {
        lemma_find_cancellation_from_valid(w, start + 1);
    }
}

///  If find_cancellation_from returns w.len(), there is no cancellation at any position >= start.
pub proof fn lemma_find_cancellation_from_none(w: Word, start: nat, j: int)
    requires
        find_cancellation_from(w, start) >= w.len(),
        start as int <= j,
        j < w.len() - 1,
    ensures
        !is_inverse_pair(w[j], w[j + 1]),
    decreases w.len() - start,
{
    if start >= w.len() - 1 {
        //  j < w.len() - 1 and start >= w.len() - 1 and start <= j — contradiction
    } else if is_inverse_pair(w[start as int], w[start as int + 1]) {
        //  find_cancellation_from returns start < w.len() — contradicts requires
    } else {
        if j == start as int {
            //  !is_inverse_pair(w[start], w[start+1]) is the branch condition
        } else {
            lemma_find_cancellation_from_none(w, start + 1, j);
        }
    }
}

///  Iterated reduction with explicit fuel (half the word length suffices).
///  Each step removes 2 symbols, so w.len()/2 steps is enough.
pub open spec fn reduce_n_steps(w: Word, fuel: nat) -> Word
    decreases fuel,
{
    if fuel == 0 {
        w
    } else {
        let pos = find_cancellation_from(w, 0);
        if pos >= w.len() {
            w
        } else {
            reduce_n_steps(reduce_at(w, pos as int), (fuel - 1) as nat)
        }
    }
}

///  Normal form: reduce with enough fuel.
pub open spec fn normal_form(w: Word) -> Word {
    reduce_n_steps(w, w.len())
}

///  Helper: if find_cancellation_from finds a position, it's a valid cancellation.
proof fn lemma_find_gives_cancellation(w: Word)
    requires
        find_cancellation_from(w, 0) < w.len(),
    ensures
        has_cancellation_at(w, find_cancellation_from(w, 0) as int),
{
    lemma_find_cancellation_from_valid(w, 0);
}

///  reduce_n_steps with 0 fuel returns the input.
pub proof fn lemma_reduce_n_steps_zero(w: Word)
    ensures
        reduce_n_steps(w, 0) == w,
{
}

///  If w has no cancellation, reduce_n_steps returns w regardless of fuel.
pub proof fn lemma_reduce_n_steps_reduced(w: Word, fuel: nat)
    requires
        is_reduced(w),
    ensures
        reduce_n_steps(w, fuel) == w,
    decreases fuel,
{
    if fuel == 0 {
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        assert(pos >= w.len()) by {
            if pos < w.len() {
                assert(has_cancellation(w));
            }
        };
    }
}

///  The normal form is reduced.
pub proof fn lemma_normal_form_is_reduced(w: Word)
    ensures
        is_reduced(normal_form(w)),
{
    lemma_reduce_n_steps_is_reduced(w, w.len());
}

///  reduce_n_steps always produces a reduced word when given enough fuel.
///  fuel >= w.len() is always sufficient since each step removes 2 chars.
proof fn lemma_reduce_n_steps_is_reduced(w: Word, fuel: nat)
    requires
        fuel >= w.len(),
    ensures
        is_reduced(reduce_n_steps(w, fuel)),
    decreases fuel,
{
    if fuel == 0 {
        //  fuel >= w.len() and fuel == 0 means w.len() == 0, so w is empty
        assert(w =~= empty_word());
        lemma_empty_is_reduced();
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        if pos >= w.len() {
            assert forall|i: int| !has_cancellation_at(w, i) by {
                if 0 <= i < (w.len() - 1) as int {
                    lemma_find_cancellation_from_none(w, 0, i);
                }
            }
        } else {
            lemma_reduce_at_len(w, pos as int);
            //  reduce_at(w, pos).len() == w.len() - 2, and fuel - 1 >= w.len() - 1 >= w.len() - 2
            lemma_reduce_n_steps_is_reduced(reduce_at(w, pos as int), (fuel - 1) as nat);
        }
    }
}

///  The original word reduces to its normal form.
pub proof fn lemma_reduces_to_normal_form(w: Word)
    ensures
        reduces_to(w, normal_form(w)),
{
    lemma_reduce_n_steps_reduces(w, w.len());
}

///  reduce_n_steps produces a word reachable by reduction.
proof fn lemma_reduce_n_steps_reduces(w: Word, fuel: nat)
    ensures
        reduces_to(w, reduce_n_steps(w, fuel)),
    decreases fuel,
{
    if fuel == 0 {
        lemma_reduces_to_refl(w);
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        if pos >= w.len() {
            lemma_reduces_to_refl(w);
        } else {
            let w2 = reduce_at(w, pos as int);
            lemma_reduce_n_steps_reduces(w2, (fuel - 1) as nat);
            //  w →¹ w2 →* reduce_n_steps(w2, fuel-1)
            assert(reduces_one_step(w, w2));
            let n = choose|n: nat| reduces_in_steps(w2, reduce_n_steps(w, fuel), n);
            assert(reduces_in_steps(w, reduce_n_steps(w, fuel), (n + 1) as nat));
        }
    }
}

//  --- Local Confluence ---

///  Local confluence: if w →¹ w1 and w →¹ w2, then ∃ w3. w1 →* w3 ∧ w2 →* w3.
///
///  Cases:
///  - Same position: w1 == w2 (trivial)
///  - Disjoint positions (|i-j| >= 2): both reductions commute, w3 = reduce both
///  - Overlapping (|i-j| == 1): e.g. i=k, j=k+1 means w[k]w[k+1]w[k+2] where
///    w[k]w[k+1] cancel AND w[k+1]w[k+2] cancel. This means w[k] = inv(w[k+1])
///    and w[k+1] = inv(w[k+2]), so w[k] = inv(inv(w[k+2])) = w[k+2].
///    After either reduction, the remaining pair also cancels → same result.
pub proof fn lemma_local_confluence(w: Word, w1: Word, w2: Word)
    requires
        reduces_one_step(w, w1),
        reduces_one_step(w, w2),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
{
    let i = choose|i: int| has_cancellation_at(w, i) && w1 == reduce_at(w, i);
    let j = choose|j: int| has_cancellation_at(w, j) && w2 == reduce_at(w, j);

    if i == j {
        //  Case 1: Same position → same result
        assert(w1 == w2);
        lemma_reduces_to_refl(w1);
    } else if i < j {
        if j == i + 1 {
            //  Case 2: Overlapping — positions i and i+1
            //  w[i]=A, w[i+1]=B, w[i+2]=C
            //  AB cancel: A = inv(B), BC cancel: B = inv(C)
            //  So A = inv(B) = inv(inv(C)) = C
            lemma_overlapping_confluence(w, w1, w2, i);
        } else {
            //  Case 3: Disjoint — |i-j| >= 2
            lemma_disjoint_confluence(w, w1, w2, i, j);
        }
    } else {
        //  j < i, symmetric
        if i == j + 1 {
            lemma_overlapping_confluence(w, w2, w1, j);
            let w3 = choose|w3: Word| reduces_to(w2, w3) && reduces_to(w1, w3);
            assert(reduces_to(w1, w3) && reduces_to(w2, w3));
        } else {
            lemma_disjoint_confluence(w, w2, w1, j, i);
            let w3 = choose|w3: Word| reduces_to(w2, w3) && reduces_to(w1, w3);
            assert(reduces_to(w1, w3) && reduces_to(w2, w3));
        }
    }
}

///  Overlapping case: cancellations at adjacent positions i and i+1.
///  w[i]=A, w[i+1]=B, w[i+2]=C with AB and BC both inverse pairs.
///  Then A=C, so both reductions give the same result.
proof fn lemma_overlapping_confluence(w: Word, w1: Word, w2: Word, i: int)
    requires
        has_cancellation_at(w, i),
        has_cancellation_at(w, i + 1),
        w1 == reduce_at(w, i),
        w2 == reduce_at(w, i + 1),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
{
    //  A = w[i], B = w[i+1], C = w[i+2]
    //  is_inverse_pair(A, B) and is_inverse_pair(B, C)
    //  means B = inverse_symbol(A) and C = inverse_symbol(B) = inverse_symbol(inverse_symbol(A)) = A
    let a = w[i];
    let b = w[i + 1];
    let c = w[i + 2];
    assert(is_inverse_pair(a, b));
    assert(is_inverse_pair(b, c));
    //  b == inverse_symbol(a), c == inverse_symbol(b)
    assert(b == inverse_symbol(a));
    assert(c == inverse_symbol(b));
    crate::symbol::lemma_inverse_involution(a);
    assert(c == a);

    //  w1 = w[0..i] ++ w[i+2..] — removed positions i,i+1 (A,B)
    //  w2 = w[0..i+1] ++ w[i+3..] — removed positions i+1,i+2 (B,C)
    //  w1 = w[0..i] ++ [C] ++ w[i+3..]
    //  w2 = w[0..i] ++ [A] ++ w[i+3..]
    //  Since A == C, w1 =~= w2
    assert(w1 =~= w2) by {
        lemma_reduce_at_len(w, i);
        lemma_reduce_at_len(w, i + 1);
        assert(w1.len() == w2.len());
        assert forall|k: int| 0 <= k < w1.len() implies #[trigger] w1[k] == w2[k] by {
            lemma_reduce_at_elements(w, i);
            lemma_reduce_at_elements(w, i + 1);
            if k < i {
                assert(w1[k] == w[k]);
                assert(w2[k] == w[k]);
            } else if k == i {
                assert(w1[k] == w[k + 2]); //  C
                assert(w2[k] == w[k]); //  A
                assert(w[k] == a);
                assert(w[k + 2] == c);
            } else {
                //  k > i: w1[k] == w[k+2], w2[k] == w[k+2]
                assert(w1[k] == w[k + 2]);
                assert(w2[k] == w[k + 2]);
            }
        };
    };
    lemma_reduces_to_refl(w1);
}

///  Disjoint case: cancellations at positions i and j with i + 2 <= j.
///  Both reductions commute to a common reduct.
proof fn lemma_disjoint_confluence(w: Word, w1: Word, w2: Word, i: int, j: int)
    requires
        has_cancellation_at(w, i),
        has_cancellation_at(w, j),
        i + 2 <= j,
        w1 == reduce_at(w, i),
        w2 == reduce_at(w, j),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
{
    //  w1 still has cancellation at j-2, w2 still has cancellation at i
    //  Use reduce_at(w1, j-2) as the common reduct
    lemma_reduce_at_len(w, i);
    lemma_reduce_at_elements(w, i);
    assert(has_cancellation_at(w1, j - 2)) by {
        assert(w1[j - 2] == w[j]);
        assert(w1[j - 2 + 1] == w[j + 1]);
    };
    let w3 = reduce_at(w1, j - 2);

    //  w1 →¹ w3: witness the existentials explicitly
    assert(has_cancellation_at(w1, j - 2) && w3 == reduce_at(w1, j - 2));
    //  reduces_in_steps(w1, w3, 1) needs witness w_mid = w3
    assert(reduces_in_steps(w3, w3, 0));
    assert(reduces_one_step(w1, w3) && reduces_in_steps(w3, w3, 0));

    //  Show w2 has cancellation at i and reduce_at(w2, i) == w3
    lemma_reduce_at_len(w, j);
    lemma_reduce_at_elements(w, j);
    assert(has_cancellation_at(w2, i)) by {
        assert(w2[i] == w[i]);
        assert(w2[i + 1] == w[i + 1]);
    };
    let w2_reduced = reduce_at(w2, i);
    assert(w2_reduced =~= w3) by {
        lemma_reduce_at_len(w1, j - 2);
        lemma_reduce_at_elements(w1, j - 2);
        lemma_reduce_at_len(w2, i);
        lemma_reduce_at_elements(w2, i);
        assert(w3.len() == w2_reduced.len());
        assert forall|k: int| 0 <= k < w3.len() implies #[trigger] w3[k] == w2_reduced[k] by {
            if k < i {
                //  w3[k] = w1[k] = w[k], w2_reduced[k] = w2[k] = w[k]
                assert(w3[k] == w1[k]);
                assert(w1[k] == w[k]);
                assert(w2_reduced[k] == w2[k]);
                assert(w2[k] == w[k]);
            } else if k < j - 2 {
                //  w3[k] = w1[k] = w[k+2], w2_reduced[k] = w2[k+2] = w[k+2]
                assert(w3[k] == w1[k]);
                assert(w1[k] == w[k + 2]);
                assert(w2_reduced[k] == w2[k + 2]);
                assert(w2[k + 2] == w[k + 2]);
            } else {
                //  w3[k] = w1[k+2] = w[k+4], w2_reduced[k] = w2[k+2] = w[k+4]
                assert(w3[k] == w1[k + 2]);
                assert(w1[k + 2] == w[k + 4]);
                assert(w2_reduced[k] == w2[k + 2]);
                assert(w2[k + 2] == w[k + 4]);
            }
        };
    };
    //  w2 →¹ w2_reduced =~= w3, so w2 →¹ w3
    assert(has_cancellation_at(w2, i) && w3 == reduce_at(w2, i)) by {
        assert(w2_reduced == w3); //  from =~= for Seq
    };
    assert(reduces_in_steps(w3, w3, 0));
    assert(reduces_one_step(w2, w3) && reduces_in_steps(w3, w3, 0));

    //  Witness reduces_to
    assert(reduces_in_steps(w1, w3, 1nat));
    assert(reduces_in_steps(w2, w3, 1nat));
    assert(reduces_to(w1, w3));
    assert(reduces_to(w2, w3));
}

//  ============================================================
//  Reduction Respects Concatenation
//  ============================================================

///  If w1 reduces in one step to wa, then concat(w1, w2) reduces in one step to concat(wa, w2).
///  Proof: cancellation at position i in w1 is also at position i in concat(w1, w2),
///  and reduce_at(concat(w1, w2), i) =~= concat(reduce_at(w1, i), w2).
pub proof fn lemma_one_step_concat_left(w1: Word, wa: Word, w2: Word)
    requires
        reduces_one_step(w1, wa),
    ensures
        reduces_one_step(concat(w1, w2), concat(wa, w2)),
{
    let i = choose|i: int| has_cancellation_at(w1, i) && wa == reduce_at(w1, i);
    let cw = concat(w1, w2);
    //  cancellation at i in w1 means i < w1.len() - 1, so i < cw.len() - 1
    assert(cw[i] == w1[i]);
    assert(cw[i + 1] == w1[i + 1]);
    assert(has_cancellation_at(cw, i));
    //  Show reduce_at(cw, i) =~= concat(wa, w2)
    assert(reduce_at(cw, i) =~= concat(reduce_at(w1, i), w2)) by {
        lemma_reduce_at_len(cw, i);
        lemma_reduce_at_len(w1, i);
        lemma_reduce_at_elements(cw, i);
        lemma_reduce_at_elements(w1, i);
        let result = reduce_at(cw, i);
        let expected = concat(reduce_at(w1, i), w2);
        assert(result.len() == expected.len());
        assert forall|k: int| 0 <= k < result.len() implies #[trigger] result[k] == expected[k] by {
            if k < i {
                assert(result[k] == cw[k]);
                assert(cw[k] == w1[k]);
                assert(expected[k] == reduce_at(w1, i)[k]);
                assert(reduce_at(w1, i)[k] == w1[k]);
            } else if k < (w1.len() - 2) as int {
                assert(result[k] == cw[k + 2]);
                assert(cw[k + 2] == w1[k + 2]);
                assert(expected[k] == reduce_at(w1, i)[k]);
                assert(reduce_at(w1, i)[k] == w1[k + 2]);
            } else {
                //  k >= w1.len() - 2, in the w2 part
                assert(result[k] == cw[k + 2]);
                let w2_idx = k - (w1.len() - 2) as int;
                assert(cw[k + 2] == w2[w2_idx]);
                assert(expected[k] == w2[w2_idx]);
            }
        };
    };
    assert(has_cancellation_at(cw, i) && concat(wa, w2) == reduce_at(cw, i));
}

///  If w1 reduces to w1' (multi-step), then concat(w1, w2) reduces to concat(w1', w2).
pub proof fn lemma_reduces_to_concat_left(w1: Word, w1_prime: Word, w2: Word)
    requires
        reduces_to(w1, w1_prime),
    ensures
        reduces_to(concat(w1, w2), concat(w1_prime, w2)),
{
    let n = choose|n: nat| reduces_in_steps(w1, w1_prime, n);
    lemma_reduces_to_concat_left_aux(w1, w1_prime, w2, n);
}

proof fn lemma_reduces_to_concat_left_aux(w1: Word, w1_prime: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w1_prime, n),
    ensures
        reduces_to(concat(w1, w2), concat(w1_prime, w2)),
    decreases n,
{
    if n == 0 {
        lemma_reduces_to_refl(concat(w1, w2));
    } else if w1 == w1_prime {
        lemma_reduces_to_refl(concat(w1, w2));
    } else {
        let w_mid = choose|w_mid: Word|
            reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w1_prime, (n - 1) as nat);
        lemma_one_step_concat_left(w1, w_mid, w2);
        //  concat(w1, w2) →¹ concat(w_mid, w2)
        let cw1 = concat(w1, w2);
        let cwm = concat(w_mid, w2);
        assert(reduces_in_steps(cw1, cwm, 1nat)) by {
            assert(reduces_in_steps(cwm, cwm, 0));
            assert(reduces_one_step(cw1, cwm) && reduces_in_steps(cwm, cwm, 0));
        };
        //  IH: concat(w_mid, w2) →* concat(w1_prime, w2)
        lemma_reduces_to_concat_left_aux(w_mid, w1_prime, w2, (n - 1) as nat);
        //  chain
        lemma_reduces_to_transitive(cw1, cwm, concat(w1_prime, w2));
    }
}

///  If w2 reduces in one step to wb, then concat(w1, w2) reduces in one step to concat(w1, wb).
///  Cancellation at position j in w2 maps to position j + w1.len() in concat(w1, w2).
pub proof fn lemma_one_step_concat_right(w1: Word, w2: Word, wb: Word)
    requires
        reduces_one_step(w2, wb),
    ensures
        reduces_one_step(concat(w1, w2), concat(w1, wb)),
{
    let j = choose|j: int| has_cancellation_at(w2, j) && wb == reduce_at(w2, j);
    let cw = concat(w1, w2);
    let offset = w1.len() as int;
    //  cancellation at j+offset in concat
    assert(cw[j + offset] == w2[j]);
    assert(cw[j + offset + 1] == w2[j + 1]);
    assert(has_cancellation_at(cw, j + offset));
    //  Show reduce_at(cw, j+offset) =~= concat(w1, wb)
    assert(reduce_at(cw, j + offset) =~= concat(w1, reduce_at(w2, j))) by {
        lemma_reduce_at_len(cw, j + offset);
        lemma_reduce_at_len(w2, j);
        lemma_reduce_at_elements(cw, j + offset);
        lemma_reduce_at_elements(w2, j);
        let result = reduce_at(cw, j + offset);
        let expected = concat(w1, reduce_at(w2, j));
        assert(result.len() == expected.len());
        assert forall|k: int| 0 <= k < result.len() implies #[trigger] result[k] == expected[k] by {
            if k < offset {
                assert(result[k] == cw[k]);
                assert(cw[k] == w1[k]);
                assert(expected[k] == w1[k]);
            } else if k < j + offset {
                assert(result[k] == cw[k]);
                assert(cw[k] == w2[k - offset]);
                assert(expected[k] == reduce_at(w2, j)[k - offset]);
                assert(reduce_at(w2, j)[k - offset] == w2[k - offset]);
            } else {
                //  k >= j + offset
                assert(result[k] == cw[k + 2]);
                assert(cw[k + 2] == w2[k + 2 - offset]);
                assert(expected[k] == reduce_at(w2, j)[k - offset]);
                assert(reduce_at(w2, j)[k - offset] == w2[k - offset + 2]);
            }
        };
    };
    assert(has_cancellation_at(cw, j + offset) && concat(w1, wb) == reduce_at(cw, j + offset));
}

///  If w2 reduces to w2' (multi-step), then concat(w1, w2) reduces to concat(w1, w2').
pub proof fn lemma_reduces_to_concat_right(w1: Word, w2: Word, w2_prime: Word)
    requires
        reduces_to(w2, w2_prime),
    ensures
        reduces_to(concat(w1, w2), concat(w1, w2_prime)),
{
    let n = choose|n: nat| reduces_in_steps(w2, w2_prime, n);
    lemma_reduces_to_concat_right_aux(w1, w2, w2_prime, n);
}

proof fn lemma_reduces_to_concat_right_aux(w1: Word, w2: Word, w2_prime: Word, n: nat)
    requires
        reduces_in_steps(w2, w2_prime, n),
    ensures
        reduces_to(concat(w1, w2), concat(w1, w2_prime)),
    decreases n,
{
    if n == 0 {
        lemma_reduces_to_refl(concat(w1, w2));
    } else if w2 == w2_prime {
        lemma_reduces_to_refl(concat(w1, w2));
    } else {
        let w_mid = choose|w_mid: Word|
            reduces_one_step(w2, w_mid) && reduces_in_steps(w_mid, w2_prime, (n - 1) as nat);
        lemma_one_step_concat_right(w1, w2, w_mid);
        let cw2 = concat(w1, w2);
        let cwm = concat(w1, w_mid);
        assert(reduces_in_steps(cw2, cwm, 1nat)) by {
            assert(reduces_in_steps(cwm, cwm, 0));
            assert(reduces_one_step(cw2, cwm) && reduces_in_steps(cwm, cwm, 0));
        };
        lemma_reduces_to_concat_right_aux(w1, w_mid, w2_prime, (n - 1) as nat);
        lemma_reduces_to_transitive(cw2, cwm, concat(w1, w2_prime));
    }
}

///  Reduction respects concatenation: if w1 →* w1' and w2 →* w2',
///  then concat(w1, w2) →* concat(w1', w2').
pub proof fn lemma_reduces_to_concat(w1: Word, w1_prime: Word, w2: Word, w2_prime: Word)
    requires
        reduces_to(w1, w1_prime),
        reduces_to(w2, w2_prime),
    ensures
        reduces_to(concat(w1, w2), concat(w1_prime, w2_prime)),
{
    lemma_reduces_to_concat_left(w1, w1_prime, w2);
    lemma_reduces_to_concat_right(w1_prime, w2, w2_prime);
    lemma_reduces_to_transitive(concat(w1, w2), concat(w1_prime, w2), concat(w1_prime, w2_prime));
}

//  ============================================================
//  Normal Form Uniqueness
//  ============================================================

///  A reduced word is its own normal form.
pub proof fn lemma_reduced_is_own_normal_form(w: Word)
    requires
        is_reduced(w),
    ensures
        normal_form(w) == w,
{
    lemma_reduce_n_steps_reduced(w, w.len());
}

///  If w reduces to r and r is reduced, then r is the normal form of w.
pub proof fn lemma_reduces_to_reduced_unique(w: Word, r: Word)
    requires
        reduces_to(w, r),
        is_reduced(r),
    ensures
        r == normal_form(w),
{
    //  w →* r and w →* nf(w). By confluence, ∃ s with r →* s ←* nf(w).
    lemma_reduces_to_normal_form(w);
    lemma_confluence(w, r, normal_form(w));
    let s = choose|s: Word| reduces_to(r, s) && reduces_to(normal_form(w), s);
    //  r is reduced, so r →* s means r == s
    lemma_reduced_no_step(r);
    lemma_reduced_reduces_to_self(r, s);
    //  nf(w) is reduced, so nf(w) →* s means nf(w) == s
    lemma_normal_form_is_reduced(w);
    lemma_reduced_no_step(normal_form(w));
    lemma_reduced_reduces_to_self(normal_form(w), s);
    //  r == s == nf(w)
}

///  A reduced word can only reduce to itself.
proof fn lemma_reduced_reduces_to_self(w: Word, w2: Word)
    requires
        is_reduced(w),
        reduces_to(w, w2),
    ensures
        w == w2,
{
    let n = choose|n: nat| reduces_in_steps(w, w2, n);
    lemma_reduced_reduces_to_self_aux(w, w2, n);
}

proof fn lemma_reduced_reduces_to_self_aux(w: Word, w2: Word, n: nat)
    requires
        is_reduced(w),
        reduces_in_steps(w, w2, n),
    ensures
        w == w2,
    decreases n,
{
    if n == 0 {
    } else {
        if w == w2 {
        } else {
            //  w →¹ w_mid → contradiction since w is reduced
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
            lemma_reduced_no_step(w);
            //  contradiction: reduces_one_step(w, w_mid) is impossible
            assert(false);
        }
    }
}

///  Forward direction: freely_equivalent(w1, w2) → normal_form(w1) == normal_form(w2).
pub proof fn lemma_normal_form_equiv_forward(w1: Word, w2: Word)
    requires
        freely_equivalent(w1, w2),
    ensures
        normal_form(w1) == normal_form(w2),
{
    //  ∃ w with w1 →* w ←* w2
    let w = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    //  w1 →* nf(w1) and w1 →* w. By confluence, ∃ t1 with nf(w1) →* t1 ←* w.
    lemma_reduces_to_normal_form(w1);
    lemma_confluence(w1, normal_form(w1), w);
    let t1 = choose|t1: Word| reduces_to(normal_form(w1), t1) && reduces_to(w, t1);
    //  nf(w1) is reduced, so nf(w1) == t1
    lemma_normal_form_is_reduced(w1);
    lemma_reduced_reduces_to_self(normal_form(w1), t1);
    //  So w →* nf(w1)

    //  w2 →* w →* nf(w1). By transitivity: w2 →* nf(w1).
    lemma_reduces_to_transitive(w2, w, normal_form(w1));
    //  nf(w1) is reduced, so it's the normal form of w2
    lemma_reduces_to_reduced_unique(w2, normal_form(w1));
}

///  Backward direction: normal_form(w1) == normal_form(w2) → freely_equivalent(w1, w2).
pub proof fn lemma_normal_form_equiv_backward(w1: Word, w2: Word)
    requires
        normal_form(w1) == normal_form(w2),
    ensures
        freely_equivalent(w1, w2),
{
    //  Both w1 and w2 reduce to normal_form(w1) == normal_form(w2)
    lemma_reduces_to_normal_form(w1);
    lemma_reduces_to_normal_form(w2);
    let nf = normal_form(w1);
    assert(reduces_to(w1, nf) && reduces_to(w2, nf));
}

} //  verus!
