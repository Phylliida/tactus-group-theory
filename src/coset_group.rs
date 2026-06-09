use vstd::prelude::*;

verus! {

use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;
use crate::completeness::*;

//  ─── Coset reachability ──────────────────────────────────────────────────────

///  A coset is reachable if some word traces from 0 to it.
pub open spec fn coset_reachable(t: CosetTable, c: nat) -> bool {
    exists|w: Word| trace_word(t, 0 as nat, w) == Some(c)
        && (forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens)
}

///  Choose a representative word for coset c (traces 0 → c).
pub open spec fn coset_rep(t: CosetTable, c: nat) -> Word {
    choose|w: Word| trace_word(t, 0 as nat, w) == Some(c)
        && (forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens)
}

//  ─── Group operations on cosets ──────────────────────────────────────────────

///  Group multiplication: trace any representative of b from coset a.
pub open spec fn coset_mul(t: CosetTable, a: nat, b: nat) -> nat
    recommends a < t.num_cosets, b < t.num_cosets,
        coset_reachable(t, b),
{
    trace_word(t, a, coset_rep(t, b)).unwrap()
}

///  Group inverse: trace inverse_word of representative of a from 0.
pub open spec fn coset_inv(t: CosetTable, a: nat) -> nat
    recommends a < t.num_cosets,
        coset_reachable(t, a),
{
    trace_word(t, 0 as nat, inverse_word(coset_rep(t, a))).unwrap()
}

//  ─── Schreier representative system ─────────────────────────────────────────

///  A coset representative system: rep(0) = ε, each rep traces 0 → c,
///  and all reps are word_valid with valid columns.
pub open spec fn is_coset_rep_system(t: CosetTable, reps: spec_fn(nat) -> Word) -> bool {
    &&& reps(0nat) =~= empty_word()
    &&& forall|c: nat| c < t.num_cosets ==> (
        #[trigger] trace_word(t, 0 as nat, reps(c)) == Some(c)
        && word_valid(reps(c), t.num_gens)
        && (forall|k: int| 0 <= k < reps(c).len() ==> #[trigger] symbol_to_column(reps(c)[k]) < 2 * t.num_gens)
    )
}

///  The Schreier generator for coset c and symbol s is trivial.
pub open spec fn schreier_gen_equiv(
    t: CosetTable, p: Presentation, reps: spec_fn(nat) -> Word,
    c: nat, s: Symbol,
) -> bool {
    let col = symbol_to_column(s);
    let d = t.table[c as int][col as int].unwrap();
    equiv_in_presentation(p,
        concat(concat(reps(c), Seq::new(1, |_j: int| s)), inverse_word(reps(d))),
        empty_word())
}

///  All Schreier generators are trivial: for each coset c and valid symbol s,
///  reps(c) · [s] · reps(d)⁻¹ ≡ ε where d = table[c][s].
pub open spec fn schreier_trivial(t: CosetTable, p: Presentation, reps: spec_fn(nat) -> Word) -> bool {
    forall|c: nat, s: Symbol|
        c < t.num_cosets && symbol_valid(s, t.num_gens)
        ==> #[trigger] schreier_gen_equiv(t, p, reps, c, s)
}

///  A coset table has a Schreier system: there exist representatives
///  such that all Schreier generators are trivial.
pub open spec fn has_schreier_system(t: CosetTable, p: Presentation) -> bool {
    exists|reps: spec_fn(nat) -> Word|
        is_coset_rep_system(t, reps) && schreier_trivial(t, p, reps)
}

//  ─── Faithfulness ───────────────────────────────────────────────────────────

///  A coset table is faithful: words tracing 0 → 0 are trivial in the group.
///  This is the kernel condition: ker(φ) ⊆ ⟨⟨R⟩⟩ where φ(w) = trace(0, w).
pub open spec fn coset_table_faithful(t: CosetTable, p: Presentation) -> bool {
    forall|w: Word|
        word_valid(w, p.num_generators)
        && trace_word(t, 0 as nat, w) == Some(0 as nat)
        ==> equiv_in_presentation(p, w, empty_word())
}

///  If concat(u, inv(v)) ≡ ε, then u ≡ v.
pub proof fn lemma_cancel_inverse_right(p: Presentation, u: Word, v: Word)
    requires
        equiv_in_presentation(p, concat(u, inverse_word(v)), empty_word()),
        word_valid(u, p.num_generators),
        word_valid(v, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, u, v),
{
    let inv_v = inverse_word(v);
    let n = p.num_generators;
    //  concat(concat(u, inv_v), v) ≡ concat(ε, v) ≡ v
    lemma_equiv_concat_left(p, concat(u, inv_v), empty_word(), v);
    lemma_concat_identity_left(p, v);
    lemma_equiv_transitive(p, concat(concat(u, inv_v), v), concat(empty_word(), v), v);
    //  By assoc: concat(u, concat(inv_v, v)) =~= concat(concat(u, inv_v), v) ≡ v
    lemma_concat_assoc(u, inv_v, v);
    //  concat(inv_v, v) ≡ ε
    lemma_word_inverse_left(p, v);
    //  concat(u, concat(inv_v, v)) ≡ concat(u, ε)
    lemma_equiv_concat_right(p, u, concat(inv_v, v), empty_word());
    //  concat(u, ε) ≡ u
    lemma_concat_identity_right(p, u);
    //  Chain: concat(u, concat(inv_v, v)) ≡ u
    lemma_equiv_transitive(p, concat(u, concat(inv_v, v)), concat(u, empty_word()), u);
    //  Symmetric: u ≡ concat(u, concat(inv_v, v))
    crate::word::lemma_inverse_word_valid(v, n);
    lemma_concat_word_valid(inv_v, v, n);
    lemma_concat_word_valid(u, concat(inv_v, v), n);
    lemma_equiv_symmetric(p, concat(u, concat(inv_v, v)), u);
    //  Transitive: u ≡ v
    lemma_equiv_transitive(p, u, concat(u, concat(inv_v, v)), v);
}

///  Step case helper: given IH result concat(reps(d), w_tail) ≡ reps(c),
///  prove concat(reps(a), w) ≡ reps(c) using Schreier triviality.
proof fn lemma_trace_to_rep_step(
    t: CosetTable, p: Presentation,
    reps: spec_fn(nat) -> Word,
    a: nat, w: Word, s: Symbol, d: nat, c: nat,
)
    requires
        t.num_gens == p.num_generators,
        presentation_valid(p),
        is_coset_rep_system(t, reps),
        schreier_trivial(t, p, reps),
        a < t.num_cosets,
        d < t.num_cosets,
        symbol_valid(s, t.num_gens),
        symbol_to_column(s) < 2 * t.num_gens,
        t.table[a as int][symbol_to_column(s) as int] == Some(d),
        w.len() > 0,
        w.first() == s,
        word_valid(w.drop_first(), t.num_gens),
        equiv_in_presentation(p, concat(reps(d), w.drop_first()), reps(c)),
    ensures
        equiv_in_presentation(p, concat(reps(a), w), reps(c)),
{
    let w_tail = w.drop_first();
    let n = t.num_gens;
    let s_word: Word = Seq::new(1, |_j: int| s);
    let rep_a_s = concat(reps(a), s_word);

    //  Trigger rep system forall instantiation for a and d
    assert(trace_word(t, 0 as nat, reps(a)) == Some(a));
    assert(trace_word(t, 0 as nat, reps(d)) == Some(d));

    //  Trigger Schreier instantiation
    assert(schreier_gen_equiv(t, p, reps, a, s));

    //  word_valid for cancel_inverse_right
    assert(word_valid(s_word, n)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(s_word[k], n) by { assert(s_word[k] == s); }
    }
    lemma_concat_word_valid(reps(a), s_word, n);
    //  cancel: rep_a_s ≡ reps(d)
    lemma_cancel_inverse_right(p, rep_a_s, reps(d));
    //  concat(rep_a_s, w_tail) ≡ concat(reps(d), w_tail) ≡ reps(c)
    lemma_equiv_concat_left(p, rep_a_s, reps(d), w_tail);
    lemma_equiv_transitive(p, concat(rep_a_s, w_tail), concat(reps(d), w_tail), reps(c));
    //  concat(reps(a), w) =~= concat(rep_a_s, w_tail) by assoc + decomposition
    assert(w =~= concat(s_word, w_tail));
    lemma_concat_assoc(reps(a), s_word, w_tail);
}

///  Inductive core: if trace(a, w) = c, then concat(reps(a), w) ≡ reps(c).
proof fn lemma_trace_to_rep(
    t: CosetTable, p: Presentation,
    reps: spec_fn(nat) -> Word,
    a: nat, w: Word,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        is_coset_rep_system(t, reps),
        schreier_trivial(t, p, reps),
        a < t.num_cosets,
        word_valid(w, t.num_gens),
        trace_word(t, a, w) is Some,
    ensures
        equiv_in_presentation(p, concat(reps(a), w), reps(trace_word(t, a, w).unwrap())),
    decreases w.len(),
{
    reveal(coset_table_wf);
    let c = trace_word(t, a, w).unwrap();
    if w.len() == 0 {
        assert(concat(reps(a), w) =~= reps(a));
        lemma_equiv_refl(p, reps(a));
    } else {
        let s = w.first();
        let w_tail = w.drop_first();
        let n = t.num_gens;
        let col = symbol_to_column(s);
        assert(symbol_valid(s, n)) by { assert(s == w[0]); }
        lemma_valid_word_columns(w, n);
        let d = t.table[a as int][col as int].unwrap();
        assert(word_valid(w_tail, n)) by {
            assert forall|k: int| 0 <= k < w_tail.len()
                implies symbol_valid(w_tail[k], n)
            by { assert(w_tail[k] == w[k + 1]); }
        }
        lemma_valid_word_columns(w_tail, n);
        lemma_trace_complete(t, d, w_tail);
        lemma_trace_to_rep(t, p, reps, d, w_tail);
        lemma_trace_to_rep_step(t, p, reps, a, w, s, d, c);
    }
}

///  Faithfulness: a complete+consistent+relator-closed table with a Schreier
///  system is faithful. Proved by induction on word length via lemma_trace_to_rep.
pub proof fn lemma_coset_table_faithful(t: CosetTable, p: Presentation)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        t.num_cosets > 0,
    ensures
        coset_table_faithful(t, p),
{
    let reps = choose|reps: spec_fn(nat) -> Word|
        is_coset_rep_system(t, reps) && schreier_trivial(t, p, reps);
    assert forall|w: Word|
        word_valid(w, p.num_generators)
        && trace_word(t, 0 as nat, w) == Some(0 as nat)
        implies equiv_in_presentation(p, w, empty_word())
    by {
        lemma_valid_word_columns(w, p.num_generators);
        lemma_trace_complete(t, 0, w);
        lemma_trace_to_rep(t, p, reps, 0, w);
        //  concat(reps(0), w) ≡ reps(0), and reps(0) =~= ε
        //  so concat(ε, w) ≡ ε, and concat(ε, w) =~= w, so w ≡ ε
        assert(reps(0nat) =~= empty_word());
        assert(concat(empty_word(), w) =~= w);
    }
}

//  ─── Soundness from faithfulness ────────────────────────────────────────────

///  Soundness: if two words trace to the same coset from 0,
///  they are equivalent in the presented group.
///  Proved from faithfulness via group algebra:
///    trace(0, w1) = trace(0, w2) = c
///    → trace(0, w1 · w2⁻¹) = 0
///    → w1 · w2⁻¹ ≡ ε  (faithfulness)
///    → w1 ≡ w2         (group algebra)
pub proof fn axiom_coset_table_sound(t: CosetTable, p: Presentation, w1: Word, w2: Word)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        t.num_cosets > 0,
        trace_word(t, 0 as nat, w1) == trace_word(t, 0 as nat, w2),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let n = p.num_generators;
    let c = trace_word(t, 0 as nat, w1).unwrap();

    //  Step 1: trace(c, inv(w2)) = Some(0)
    lemma_valid_word_columns(w2, n);
    lemma_trace_complete(t, 0, w2);
    lemma_trace_inverse_word(t, 0, w2);
    //  Now: trace(c, inverse_word(w2)) == Some(0)

    //  Step 2: trace(0, concat(w1, inv(w2))) = Some(0)
    lemma_valid_word_columns(w1, n);
    lemma_trace_complete(t, 0, w1);
    lemma_trace_word_concat(t, 0 as nat, w1, inverse_word(w2));
    //  trace(0, concat(w1, inv(w2))) = trace(c, inv(w2)) = Some(0)

    //  Step 3: concat(w1, inv(w2)) is word_valid
    crate::word::lemma_inverse_word_valid(w2, n);
    let inv_w2 = inverse_word(w2);
    lemma_concat_word_valid(w1, inv_w2, n);

    //  Step 4: faithfulness → concat(w1, inv(w2)) ≡ ε
    lemma_coset_table_faithful(t, p);
    assert(trace_word(t, 0 as nat, concat(w1, inv_w2)) == Some(0 as nat));
    assert(equiv_in_presentation(p, concat(w1, inv_w2), empty_word()));

    //  Step 5: Group algebra chain: w1 ≡ w2
    //  w1 ≡ concat(w1, ε)                         [identity_right, symmetric]
    lemma_concat_identity_right(p, w1);
    lemma_equiv_symmetric(p, concat(w1, empty_word()), w1);
    //  w1 ≡ concat(w1, empty_word())

    //  concat(w1, ε) ≡ concat(w1, concat(inv(w2), w2))  [inv_left, symmetric, equiv_concat]
    lemma_word_inverse_left(p, w2);
    lemma_equiv_symmetric(p, concat(inv_w2, w2), empty_word());
    //  empty_word() ≡ concat(inv_w2, w2)
    lemma_equiv_refl(p, w1);
    lemma_equiv_concat(p, w1, w1, empty_word(), concat(inv_w2, w2));
    //  concat(w1, ε) ≡ concat(w1, concat(inv_w2, w2))

    //  concat(w1, concat(inv_w2, w2)) =~= concat(concat(w1, inv_w2), w2)  [assoc]
    lemma_concat_assoc(w1, inv_w2, w2);
    //  These are extensionally equal, so equiv transfers

    //  concat(concat(w1, inv_w2), w2) ≡ concat(ε, w2)  [step 4 + equiv_concat]
    lemma_equiv_refl(p, w2);
    lemma_equiv_concat(p, concat(w1, inv_w2), empty_word(), w2, w2);
    //  concat(concat(w1, inv_w2), w2) ≡ concat(ε, w2)

    //  concat(ε, w2) ≡ w2  [identity_left]
    lemma_concat_identity_left(p, w2);

    //  Chain: w1 ≡ concat(w1, ε) ≡ concat(w1, concat(inv_w2, w2))
    //         == concat(concat(w1, inv_w2), w2) ≡ concat(ε, w2) ≡ w2
    lemma_equiv_transitive(p, w1, concat(w1, empty_word()), concat(w1, concat(inv_w2, w2)));
    //  w1 ≡ concat(w1, concat(inv_w2, w2))

    //  Use =~= to bridge assoc
    assert(concat(w1, concat(inv_w2, w2)) =~= concat(concat(w1, inv_w2), w2));

    lemma_equiv_transitive(p, w1, concat(concat(w1, inv_w2), w2), concat(empty_word(), w2));
    //  w1 ≡ concat(ε, w2)

    lemma_equiv_transitive(p, w1, concat(empty_word(), w2), w2);
    //  w1 ≡ w2
}

//  ─── Well-definedness of coset_mul ───────────────────────────────────────────

///  Any two representatives of the same coset give the same trace from any coset a.
pub proof fn lemma_coset_mul_well_defined(
    t: CosetTable, p: Presentation, a: nat, w: Word, w_prime: Word,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        a < t.num_cosets,
        trace_word(t, 0 as nat, w) == trace_word(t, 0 as nat, w_prime),
        word_valid(w, p.num_generators),
        word_valid(w_prime, p.num_generators),
    ensures
        trace_word(t, a, w) == trace_word(t, a, w_prime),
{
    //  By soundness: w ≡ w' in the presented group
    axiom_coset_table_sound(t, p, w, w_prime);
    //  By completeness: equiv words trace identically from any coset
    lemma_trace_respects_equiv(t, p, a, w, w_prime);
}

//  ─── Coset 0 reachable via empty word ────────────────────────────────────────

///  Coset 0 is reachable via the empty word.
pub proof fn lemma_coset_0_reachable(t: CosetTable)
    requires
        t.num_cosets > 0,
    ensures
        coset_reachable(t, 0),
{
    let w: Word = empty_word();
    lemma_trace_empty(t, 0);
    assert(trace_word(t, 0 as nat, w) == Some(0 as nat));
    assert(forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens);
}

//  ─── Identity: coset 0 is the identity ──────────────────────────────────────

///  Left identity: mul(0, a) = a.
pub proof fn lemma_coset_mul_identity_left(
    t: CosetTable, p: Presentation, a: nat,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        a < t.num_cosets,
        coset_reachable(t, a),
    ensures
        coset_mul(t, 0, a) == a,
{
    let w_a = coset_rep(t, a);
    //  trace(0, w_a) = Some(a) by definition of coset_rep
    assert(trace_word(t, 0 as nat, w_a) == Some(a));
    //  coset_mul(t, 0, a) = trace(0, w_a).unwrap() = a
}

///  Right identity: mul(a, 0) = a.
pub proof fn lemma_coset_mul_identity_right(
    t: CosetTable, p: Presentation, a: nat,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        a < t.num_cosets,
        coset_reachable(t, 0 as nat),
        coset_reachable(t, a),
    ensures
        coset_mul(t, a, 0) == a,
{
    //  rep of 0: coset_rep(t, 0) traces 0 → 0
    let w_0 = coset_rep(t, 0 as nat);
    assert(trace_word(t, 0 as nat, w_0) == Some(0 as nat));

    //  empty word also traces 0 → 0
    let eps: Word = empty_word();
    lemma_trace_empty(t, 0 as nat);

    //  By well-definedness: trace(a, w_0) = trace(a, eps) = a
    lemma_valid_word_columns(w_0, t.num_gens);
    lemma_trace_complete(t, 0, w_0);
    lemma_trace_complete(t, a, w_0);
    //  Need word_valid for well-definedness
    //  w_0 columns valid → word_valid
    lemma_columns_to_word_valid(w_0, t.num_gens);
    lemma_coset_mul_well_defined(t, p, a, w_0, eps);
    lemma_trace_empty(t, a);
}

///  If all symbols have valid columns, the word is word_valid.
pub proof fn lemma_columns_to_word_valid(w: Word, num_gens: nat)
    requires
        forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * num_gens,
    ensures
        word_valid(w, num_gens),
{
    assert forall|k: int| 0 <= k < w.len()
        implies symbol_valid(w[k], num_gens)
    by {
        let s = w[k];
        let col = symbol_to_column(s);
        match s {
            Symbol::Gen(i) => {
                assert(col == 2 * i);
                assert(2 * i < 2 * num_gens);
                assert(i < num_gens) by(nonlinear_arith)
                    requires 2 * i < 2 * num_gens;
            },
            Symbol::Inv(i) => {
                assert(col == 2 * i + 1);
                assert(2 * i + 1 < 2 * num_gens);
                assert(i < num_gens) by(nonlinear_arith)
                    requires 2 * i + 1 < 2 * num_gens;
            },
        }
    }
}

//  ─── Associativity ──────────────────────────────────────────────────────────

///  Core associativity helper: works with explicit trace_word, no coset_mul.
proof fn lemma_assoc_trace_chain(
    t: CosetTable, p: Presentation,
    a: nat, w_b: Word, w_c: Word, w_bc: Word,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        a < t.num_cosets,
        word_valid(w_b, t.num_gens),
        word_valid(w_c, t.num_gens),
        word_valid(w_bc, t.num_gens),
        word_valid(concat(w_b, w_c), t.num_gens),
        trace_word(t, 0 as nat, concat(w_b, w_c))
            == trace_word(t, 0 as nat, w_bc),
    ensures
        trace_word(t, a, concat(w_b, w_c))
            == trace_word(t, a, w_bc),
{
    lemma_coset_mul_well_defined(t, p, a, concat(w_b, w_c), w_bc);
}

///  Associativity helper: LHS chain through concat.
proof fn lemma_assoc_lhs(
    t: CosetTable, a: nat, w_b: Word, w_c: Word,
)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        a < t.num_cosets,
        forall|k: int| 0 <= k < w_b.len() ==> symbol_to_column(w_b[k]) < 2 * t.num_gens,
        forall|k: int| 0 <= k < w_c.len() ==> symbol_to_column(w_c[k]) < 2 * t.num_gens,
    ensures
        trace_word(t, a, concat(w_b, w_c)) is Some,
        trace_word(t, a, w_b) is Some,
        trace_word(t, a, concat(w_b, w_c))
            == trace_word(t, trace_word(t, a, w_b).unwrap(), w_c),
{
    lemma_trace_complete(t, a, w_b);
    let d = trace_word(t, a, w_b).unwrap();
    lemma_trace_complete(t, d, w_c);
    lemma_trace_word_concat(t, a, w_b, w_c);
    //  trace(a, concat(w_b, w_c)) = trace(d, w_c) which is Some
}

///  Associativity: mul(mul(a,b), c) = mul(a, mul(b,c)).
pub proof fn lemma_coset_mul_assoc(
    t: CosetTable, p: Presentation, a: nat, b: nat, c: nat,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        a < t.num_cosets,
        b < t.num_cosets,
        c < t.num_cosets,
        coset_reachable(t, b),
        coset_reachable(t, c),
        coset_reachable(t, coset_mul(t, b, c)),
    ensures
        coset_mul(t, coset_mul(t, a, b), c) == coset_mul(t, a, coset_mul(t, b, c)),
{
    let w_b = coset_rep(t, b);
    let w_c = coset_rep(t, c);
    let bc = coset_mul(t, b, c);
    let w_bc = coset_rep(t, bc);

    lemma_valid_word_columns(w_b, t.num_gens);
    lemma_valid_word_columns(w_c, t.num_gens);
    lemma_columns_to_word_valid(w_b, t.num_gens);
    lemma_columns_to_word_valid(w_c, t.num_gens);
    lemma_columns_to_word_valid(w_bc, t.num_gens);

    //  LHS: trace(a, concat(w_b, w_c)) = trace(ab, w_c)
    lemma_assoc_lhs(t, a, w_b, w_c);
    let ab = trace_word(t, a, w_b).unwrap();
    assert(coset_mul(t, a, b) == ab);

    //  concat(w_b, w_c) traces 0 → bc
    lemma_assoc_lhs(t, 0, w_b, w_c);
    assert(trace_word(t, 0 as nat, concat(w_b, w_c)) == Some(bc));

    //  Well-def: trace(a, concat(w_b, w_c)) = trace(a, w_bc)
    lemma_concat_word_valid(w_b, w_c, t.num_gens);
    lemma_assoc_trace_chain(t, p, a, w_b, w_c, w_bc);
}

///  concat of word_valid words is word_valid.
proof fn lemma_concat_word_valid(w1: Word, w2: Word, n: nat)
    requires word_valid(w1, n), word_valid(w2, n),
    ensures word_valid(concat(w1, w2), n),
{
    assert forall|k: int| 0 <= k < concat(w1, w2).len()
        implies symbol_valid(concat(w1, w2)[k], n)
    by {
        if k < w1.len() {
            assert(concat(w1, w2)[k] == w1[k]);
        } else {
            assert(concat(w1, w2)[k] == w2[k - w1.len()]);
        }
    }
}

//  ─── Inverse ────────────────────────────────────────────────────────────────

///  Helper: trace(a, inv(w_a)) = Some(0) when trace(0, w_a) = Some(a).
proof fn lemma_trace_inv_rep_to_zero(t: CosetTable, a: nat, w_a: Word)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        a < t.num_cosets,
        trace_word(t, 0 as nat, w_a) == Some(a),
        forall|k: int| 0 <= k < w_a.len() ==> symbol_to_column(w_a[k]) < 2 * t.num_gens,
    ensures
        trace_word(t, a, inverse_word(w_a)) == Some(0 as nat),
{
    lemma_trace_inverse_word(t, 0, w_a);
}

///  Helper: two words tracing 0 to same coset → trace(a, w1) = trace(a, w2).
proof fn lemma_same_coset_same_trace(
    t: CosetTable, p: Presentation, a: nat,
    w1: Word, w2: Word, target: nat,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        a < t.num_cosets,
        trace_word(t, 0 as nat, w1) == Some(target),
        trace_word(t, 0 as nat, w2) == Some(target),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
    ensures
        trace_word(t, a, w1) == trace_word(t, a, w2),
{
    lemma_coset_mul_well_defined(t, p, a, w1, w2);
}

///  Helper: inv(w_a) traces 0 → some coset (i.e., trace is Some).
proof fn lemma_inv_word_traceable(
    t: CosetTable, w_a: Word,
)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        t.num_cosets > 0,
        word_valid(w_a, t.num_gens),
    ensures
        trace_word(t, 0 as nat, inverse_word(w_a)) is Some,
{
    crate::word::lemma_inverse_word_valid(w_a, t.num_gens);
    lemma_valid_word_columns(inverse_word(w_a), t.num_gens);
    lemma_trace_complete(t, 0, inverse_word(w_a));
}

///  Right inverse: mul(a, inv(a)) = 0.
pub proof fn lemma_coset_inv_right(
    t: CosetTable, p: Presentation, a: nat,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        a < t.num_cosets,
        coset_reachable(t, a),
        coset_reachable(t, coset_inv(t, a)),
    ensures
        coset_mul(t, a, coset_inv(t, a)) == 0,
{
    let w_a = coset_rep(t, a);
    let inv_a = coset_inv(t, a);
    let w_inv_coset = coset_rep(t, inv_a);
    let inv_w_a = inverse_word(w_a);

    lemma_columns_to_word_valid(w_a, t.num_gens);
    lemma_valid_word_columns(w_a, t.num_gens);

    //  trace(a, inv_w_a) = Some(0)
    lemma_trace_inv_rep_to_zero(t, a, w_a);

    //  trace(0, inv_w_a) is Some
    lemma_inv_word_traceable(t, w_a);

    //  w_inv_coset also traces 0 → inv_a
    lemma_columns_to_word_valid(w_inv_coset, t.num_gens);
    crate::word::lemma_inverse_word_valid(w_a, t.num_gens);
    lemma_same_coset_same_trace(t, p, a, w_inv_coset, inv_w_a, inv_a);
}

///  Left inverse: mul(inv(a), a) = 0.
pub proof fn lemma_coset_inv_left(
    t: CosetTable, p: Presentation, a: nat,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        has_schreier_system(t, p),
        a < t.num_cosets,
        coset_reachable(t, a),
        coset_reachable(t, coset_inv(t, a)),
    ensures
        coset_mul(t, coset_inv(t, a), a) == 0,
{
    let w_a = coset_rep(t, a);
    let inv_a = coset_inv(t, a);
    let w_inv_coset = coset_rep(t, inv_a);
    let inv_w_a = inverse_word(w_a);

    lemma_valid_word_columns(w_a, t.num_gens);
    lemma_trace_inverse_word(t, 0, w_a);
    //  trace(0, inv_w_a) = Some(inv_a)

    //  mul(inv_a, a) = trace(inv_a, w_a)
    //  trace(0, inv_w_a ++ w_a) = trace(inv_a, w_a)
    crate::word::lemma_inverse_word_valid(w_a, t.num_gens);
    lemma_valid_word_columns(inverse_word(w_a), t.num_gens);
    lemma_trace_complete(t, 0, inv_w_a);
    lemma_trace_word_concat(t, 0 as nat, inv_w_a, w_a);
    //  trace(0, inv_w_a ++ w_a) = trace(inv_a, w_a) = mul(inv_a, a)

    //  inv_w_a ++ w_a traces 0 → inv_a → mul(inv_a, a)
    //  Also, inv_w_a ++ w_a ≡ ε in the group (by word_inverse_left)
    //  So trace(0, inv_w_a ++ w_a) = trace(0, ε) = Some(0)
    //  But we need the table-level fact, not the group-level one.

    //  Actually: trace(0, inv_w_a ++ w_a) — we use lemma_trace_inverse_word twice
    //  Simpler: by trace_inverse_word on inv_w_a itself.
    //  trace(0, inv_w_a) = Some(inv_a)
    //  trace(inv_a, inverse_word(inv_w_a)) = Some(0) by lemma_trace_inverse_word
    //  inverse_word(inv_w_a) =~= w_a by lemma_inverse_involution
    crate::word::lemma_inverse_involution(w_a);
    assert(inverse_word(inv_w_a) =~= w_a);

    lemma_trace_inverse_word(t, 0, inv_w_a);
    //  trace(inv_a, inverse_word(inv_w_a)) = Some(0)
    //  inverse_word(inv_w_a) =~= w_a
    //  So trace(inv_a, w_a) = Some(0)

    //  But we need trace(inv_a, w_a_rep) where w_a_rep = coset_rep(t, a)
    //  By well-definedness: both w_a and coset_rep(t, a) trace 0 → a
    //  So trace(inv_a, w_a) = trace(inv_a, coset_rep(t, a))
    lemma_columns_to_word_valid(w_a, t.num_gens);
    lemma_columns_to_word_valid(coset_rep(t, a), t.num_gens);
    lemma_coset_mul_well_defined(t, p, inv_a, w_a, coset_rep(t, a));
}

} //  verus!
