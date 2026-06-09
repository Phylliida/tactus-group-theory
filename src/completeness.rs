use vstd::prelude::*;

verus! {

use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::todd_coxeter::*;
use crate::finite::coset_table_complete;

//  ─── Column/validity helpers ─────────────────────────────────────────────────

///  inverse_column(symbol_to_column(s)) == symbol_to_column(inverse_symbol(s)).
pub proof fn lemma_inverse_column_symbol(s: Symbol)
    ensures
        inverse_column(symbol_to_column(s)) == symbol_to_column(inverse_symbol(s)),
{
    match s {
        Symbol::Gen(i) => {
            assert((2 * i) % 2 == 0) by(nonlinear_arith)
                requires symbol_to_column(s) == 2 * i;
        },
        Symbol::Inv(i) => {
            assert((2 * i + 1) % 2 != 0) by(nonlinear_arith)
                requires symbol_to_column(s) == 2 * i + 1;
        },
    }
}

///  symbol_valid implies symbol_to_column is in range.
pub proof fn lemma_valid_symbol_column(s: Symbol, num_gens: nat)
    requires symbol_valid(s, num_gens),
    ensures symbol_to_column(s) < 2 * num_gens,
{
    match s {
        Symbol::Gen(i) => {
            assert(2 * i < 2 * num_gens) by(nonlinear_arith) requires i < num_gens;
        },
        Symbol::Inv(i) => {
            assert(2 * i + 1 < 2 * num_gens) by(nonlinear_arith) requires i < num_gens;
        },
    }
}

///  word_valid implies all symbol_to_column values are in range.
pub proof fn lemma_valid_word_columns(w: Word, num_gens: nat)
    requires word_valid(w, num_gens),
    ensures forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * num_gens,
{
    assert forall|k: int| 0 <= k < w.len()
        implies symbol_to_column(w[k]) < 2 * num_gens
    by { lemma_valid_symbol_column(w[k], num_gens); }
}

//  ─── Trace completeness: complete table → trace always Some ──────────────────

///  If the table is complete and wf, trace_word always returns Some.
pub proof fn lemma_trace_complete(t: CosetTable, c: nat, w: Word)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        c < t.num_cosets,
        forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens,
    ensures
        trace_word(t, c, w) is Some,
        trace_word(t, c, w).unwrap() < t.num_cosets,
    decreases w.len(),
{
    reveal(coset_table_wf);
    reveal(coset_table_complete);
    if w.len() > 0 {
        let col = symbol_to_column(w.first());
        let d = t.table[c as int][col as int].unwrap();
        assert forall|k: int| 0 <= k < w.drop_first().len()
            implies symbol_to_column(w.drop_first()[k]) < 2 * t.num_gens
        by { assert(w.drop_first()[k] == w[k + 1]); }
        lemma_trace_complete(t, d, w.drop_first());
    }
}

//  ─── Helper: trace_word_split ────────────────────────────────────────────────

///  Splitting a word at position pos: trace w = trace prefix then suffix.
pub proof fn lemma_trace_word_split(t: CosetTable, c: nat, w: Word, pos: int)
    requires
        coset_table_wf(t),
        0 <= pos <= w.len(),
        trace_word(t, c, w.subrange(0, pos)) is Some,
    ensures
        trace_word(t, c, w) ==
            trace_word(t, trace_word(t, c, w.subrange(0, pos)).unwrap(),
                w.subrange(pos, w.len() as int)),
{
    assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
    lemma_trace_word_concat(t, c, w.subrange(0, pos), w.subrange(pos, w.len() as int));
    assert(concat(w.subrange(0, pos), w.subrange(pos, w.len() as int)) =~= w);
}

//  ─── Lemma 1: trace of inverse pair cancels ─────────────────────────────────

///  Tracing a single symbol from coset c.
pub proof fn lemma_trace_single(t: CosetTable, c: nat, s: Symbol)
    requires
        coset_table_wf(t),
        coset_table_complete(t),
        c < t.num_cosets,
        symbol_to_column(s) < 2 * t.num_gens,
    ensures
        trace_word(t, c, seq![s]) == Some(t.table[c as int][symbol_to_column(s) as int].unwrap()),
{
    reveal(coset_table_complete);
    let w: Word = seq![s];
    let col = symbol_to_column(s);
    assert(w.len() == 1);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    //  By completeness, table[c][col] is Some
    assert(t.table[c as int][col as int] is Some);
    let d = t.table[c as int][col as int].unwrap();
    //  trace_word(t, c, [s]) = trace_word(t, d, []) = Some(d)
    assert(trace_word(t, d, Seq::<Symbol>::empty()) == Some(d));
}

///  Tracing [s, inv(s)] returns to the starting coset.
pub proof fn lemma_trace_inverse_pair(t: CosetTable, c: nat, s: Symbol)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        c < t.num_cosets,
        symbol_to_column(s) < 2 * t.num_gens,
    ensures
        trace_word(t, c, seq![s, inverse_symbol(s)]) == Some(c),
{
    let col = symbol_to_column(s);
    let inv_s = inverse_symbol(s);
    assert(t.table[c as int][col as int] is Some) by { reveal(coset_table_complete); }
    let d = t.table[c as int][col as int].unwrap();
    assert(d < t.num_cosets) by { reveal(coset_table_wf); }

    lemma_inverse_column_symbol(s);
    let inv_col = symbol_to_column(inv_s);
    assert(t.table[d as int][inv_col as int] == Some(c)) by { reveal(coset_table_consistent); }

    //  [s, inv_s] = [s] ++ [inv_s]
    assert(seq![s, inv_s] =~= seq![s] + seq![inv_s]);
    lemma_trace_single(t, c, s);
    assert(trace_word(t, c, seq![s]) == Some(d));
    lemma_trace_word_concat(t, c, seq![s], seq![inv_s]);
    //  trace(c, [s, inv_s]) = trace(d, [inv_s])
    lemma_trace_single(t, d, inv_s);
    assert(trace_word(t, d, seq![inv_s]) == Some(c));
}

//  ─── Lemma 2: free reduction preserves trace ────────────────────────────────

///  Removing an inverse pair at position pos preserves trace_word.
pub proof fn lemma_trace_free_reduce(t: CosetTable, c: nat, w: Word, pos: int)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        c < t.num_cosets,
        has_cancellation_at(w, pos),
        forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens,
    ensures
        trace_word(t, c, w) == trace_word(t, c, reduce_at(w, pos)),
{
    let prefix = w.subrange(0, pos);
    let pair = w.subrange(pos, pos + 2);
    let suffix = w.subrange(pos + 2, w.len() as int);
    let s = w[pos];

    assert(pair =~= seq![s, inverse_symbol(s)]);
    assert(w =~= prefix + pair + suffix);

    //  prefix symbols valid
    assert forall|k: int| 0 <= k < prefix.len()
        implies symbol_to_column(prefix[k]) < 2 * t.num_gens
    by { assert(prefix[k] == w[k]); }

    //  trace prefix
    lemma_trace_complete(t, c, prefix);
    let d = trace_word(t, c, prefix).unwrap();

    //  trace(c, w) via split at pos
    lemma_trace_word_split(t, c, w, pos);
    let tail = w.subrange(pos, w.len() as int);
    assert(tail =~= pair + suffix);

    //  pair cancels
    lemma_trace_inverse_pair(t, d, s);
    lemma_trace_word_concat(t, d, pair, suffix);

    //  trace(c, reduce_at(w, pos)) = trace(c, prefix ++ suffix) = trace(d, suffix)
    assert(reduce_at(w, pos) =~= prefix + suffix);
    lemma_trace_word_concat(t, c, prefix, suffix);
}

///  Inserting an inverse pair preserves trace_word.
pub proof fn lemma_trace_free_expand(t: CosetTable, c: nat, w: Word, pos: int, s: Symbol)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        c < t.num_cosets,
        0 <= pos <= w.len(),
        forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens,
        symbol_to_column(s) < 2 * t.num_gens,
    ensures ({
        let pair = seq![s, inverse_symbol(s)];
        let expanded = w.subrange(0, pos) + pair + w.subrange(pos, w.len() as int);
        trace_word(t, c, w) == trace_word(t, c, expanded)
    }),
{
    let pair = seq![s, inverse_symbol(s)];
    let prefix = w.subrange(0, pos);
    let suffix = w.subrange(pos, w.len() as int);

    assert forall|k: int| 0 <= k < prefix.len()
        implies symbol_to_column(prefix[k]) < 2 * t.num_gens
    by { assert(prefix[k] == w[k]); }

    lemma_trace_complete(t, c, prefix);
    let d = trace_word(t, c, prefix).unwrap();

    lemma_trace_inverse_pair(t, d, s);

    //  expanded = prefix ++ pair ++ suffix, pair traces d → d
    //  w = prefix ++ suffix
    //  So trace(c, expanded) = trace(c, w)
    assert(w =~= prefix + suffix);
    //  Use symmetry: trace(c, prefix ++ suffix) = trace(c, prefix ++ pair ++ suffix)
    //  This is lemma_trace_insert_cancel but backwards.
    //  insert_cancel: trace(c, prefix ++ mid ++ suffix) = trace(c, prefix ++ suffix)
    lemma_trace_insert_cancel(t, c, prefix, pair, suffix);
}

//  ─── Lemma 3: relator insertion/deletion preserves trace ─────────────────────

///  If trace(start, w) = Some(end), then trace(end, inverse_word(w)) = Some(start).
pub proof fn lemma_trace_inverse_word(t: CosetTable, start: nat, w: Word)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        start < t.num_cosets,
        trace_word(t, start, w) is Some,
        forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens,
    ensures
        trace_word(t, trace_word(t, start, w).unwrap(), inverse_word(w)) == Some(start),
    decreases w.len(),
{
    reveal(coset_table_wf);
    reveal(coset_table_consistent);
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
        lemma_trace_empty(t, start);
    } else {
        let s = w.first();
        let col = symbol_to_column(s);
        let d = t.table[start as int][col as int].unwrap();
        let rest = w.drop_first();

        assert forall|k: int| 0 <= k < rest.len()
            implies symbol_to_column(rest[k]) < 2 * t.num_gens
        by { assert(rest[k] == w[k + 1]); }
        lemma_trace_complete(t, d, rest);
        let end_coset = trace_word(t, start, w).unwrap();

        //  IH: trace(end, inv(rest)) = Some(d)
        lemma_trace_inverse_word(t, d, rest);

        //  inv(w) = inv(rest) ++ [inv(s)]
        assert(inverse_word(w) =~= inverse_word(rest) + seq![inverse_symbol(s)]);

        //  trace(end, inv(w)) = trace(d, [inv(s)])
        lemma_trace_word_concat(t, end_coset, inverse_word(rest), seq![inverse_symbol(s)]);

        //  table[d][inv_col] = Some(start) by consistency
        lemma_inverse_column_symbol(s);
        let inv_s = inverse_symbol(s);
        lemma_trace_single(t, d, inv_s);
    }
}

///  The inverse of a relator traces back to the starting coset.
proof fn lemma_trace_inverse_relator(t: CosetTable, p: Presentation, c: nat, rel_idx: nat)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        c < t.num_cosets,
        0 <= rel_idx < p.relators.len(),
        t.num_gens == p.num_generators,
        presentation_valid(p),
    ensures
        trace_word(t, c, inverse_word(p.relators[rel_idx as int])) == Some(c),
{
    reveal(relator_closed);
    reveal(presentation_valid);
    let r = p.relators[rel_idx as int];
    //  trace(c, r) = Some(c) by relator_closed
    assert(trace_word(t, c, r) == Some(c));
    //  r is word_valid → columns valid
    assert(word_valid(r, p.num_generators));
    lemma_valid_word_columns(r, p.num_generators);
    //  By lemma_trace_inverse_word: trace(c, inv(r)) = Some(c)
    lemma_trace_inverse_word(t, c, r);
}

///  Helper: trace(c, prefix ++ mid ++ suffix) = trace(c, prefix ++ suffix)
///  when trace(d, mid) = Some(d) and d = trace(c, prefix).unwrap().
proof fn lemma_trace_insert_cancel(
    t: CosetTable, c: nat,
    prefix: Word, mid: Word, suffix: Word,
)
    requires
        coset_table_wf(t),
        trace_word(t, c, prefix) is Some,
        trace_word(t, trace_word(t, c, prefix).unwrap(), mid)
            == Some(trace_word(t, c, prefix).unwrap()),
    ensures
        trace_word(t, c, prefix + mid + suffix) == trace_word(t, c, prefix + suffix),
{
    let d = trace_word(t, c, prefix).unwrap();
    assert(prefix + mid + suffix =~= prefix + (mid + suffix));
    lemma_trace_word_concat(t, c, prefix, mid + suffix);
    lemma_trace_word_concat(t, d, mid, suffix);
    lemma_trace_word_concat(t, c, prefix, suffix);
}

///  Inserting a relator at position pos preserves trace_word.
pub proof fn lemma_trace_relator_insert(
    t: CosetTable, p: Presentation, c: nat, w: Word,
    pos: int, rel_idx: nat, inverted: bool,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        c < t.num_cosets,
        0 <= pos <= w.len(),
        0 <= rel_idx < p.relators.len(),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens,
    ensures ({
        let r = get_relator(p, rel_idx, inverted);
        let inserted = w.subrange(0, pos) + r + w.subrange(pos, w.len() as int);
        trace_word(t, c, w) == trace_word(t, c, inserted)
    }),
{
    reveal(relator_closed);
    let r = get_relator(p, rel_idx, inverted);
    let prefix = w.subrange(0, pos);
    let suffix = w.subrange(pos, w.len() as int);

    assert forall|k: int| 0 <= k < prefix.len()
        implies symbol_to_column(prefix[k]) < 2 * t.num_gens
    by { assert(prefix[k] == w[k]); }

    lemma_trace_complete(t, c, prefix);
    let d = trace_word(t, c, prefix).unwrap();

    if inverted {
        lemma_trace_inverse_relator(t, p, d, rel_idx);
    } else {
        assert(trace_word(t, d, r) == Some(d));
    }

    assert(w =~= prefix + suffix);
    lemma_trace_insert_cancel(t, c, prefix, r, suffix);
}

///  Deleting a relator from position pos preserves trace_word.
pub proof fn lemma_trace_relator_delete(
    t: CosetTable, p: Presentation, c: nat, w: Word,
    pos: int, rel_idx: nat, inverted: bool,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        c < t.num_cosets,
        0 <= rel_idx < p.relators.len(),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        forall|k: int| 0 <= k < w.len() ==> symbol_to_column(w[k]) < 2 * t.num_gens,
        ({
            let r = get_relator(p, rel_idx, inverted);
            0 <= pos && pos + r.len() <= w.len()
            && w.subrange(pos, pos + r.len() as int) == r
        }),
    ensures ({
        let r = get_relator(p, rel_idx, inverted);
        let deleted = w.subrange(0, pos) + w.subrange(pos + r.len() as int, w.len() as int);
        trace_word(t, c, w) == trace_word(t, c, deleted)
    }),
{
    reveal(relator_closed);
    let r = get_relator(p, rel_idx, inverted);
    let rlen = r.len();
    let prefix = w.subrange(0, pos);
    let mid = w.subrange(pos, pos + rlen as int);
    let suffix = w.subrange(pos + rlen as int, w.len() as int);

    assert(w =~= prefix + mid + suffix);
    assert(mid =~= r);

    assert forall|k: int| 0 <= k < prefix.len()
        implies symbol_to_column(prefix[k]) < 2 * t.num_gens
    by { assert(prefix[k] == w[k]); }

    lemma_trace_complete(t, c, prefix);
    let d = trace_word(t, c, prefix).unwrap();

    if inverted {
        lemma_trace_inverse_relator(t, p, d, rel_idx);
    } else {
        assert(trace_word(t, d, r) == Some(d));
    }

    //  w = prefix ++ mid ++ suffix, mid traces d → d
    //  So trace(c, w) = trace(c, prefix ++ suffix)
    lemma_trace_insert_cancel(t, c, prefix, mid, suffix);
}

//  ─── Lemma 4: single derivation step preserves trace ─────────────────────────

///  A single derivation step preserves trace_word.
pub proof fn lemma_trace_single_step(
    t: CosetTable, p: Presentation, c: nat,
    w: Word, step: DerivationStep, w_next: Word,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        c < t.num_cosets,
        apply_step(p, w, step) == Some(w_next),
        word_valid(w, p.num_generators),
        word_valid(w_next, p.num_generators),
    ensures
        trace_word(t, c, w) == trace_word(t, c, w_next),
{
    lemma_valid_word_columns(w, p.num_generators);
    match step {
        DerivationStep::FreeReduce { position } => {
            assert(w_next =~= reduce_at(w, position));
            lemma_trace_free_reduce(t, c, w, position);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = seq![symbol, inverse_symbol(symbol)];
            let expanded = w.subrange(0, position) + pair + w.subrange(position, w.len() as int);
            assert(w_next =~= expanded);
            //  symbol is valid since w_next is word_valid and w_next[position] == symbol
            assert(w_next[position] == symbol) by {
                assert((w.subrange(0, position) + pair).len() == position + 2);
                assert((w.subrange(0, position) + pair)[position] == pair[0]);
                assert(pair[0] == symbol);
            }
            assert(symbol_valid(symbol, p.num_generators));
            lemma_valid_symbol_column(symbol, p.num_generators);
            lemma_trace_free_expand(t, c, w, position, symbol);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            lemma_trace_relator_insert(t, p, c, w, position, relator_index, inverted);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            lemma_trace_relator_delete(t, p, c, w, position, relator_index, inverted);
        },
    }
}

//  ─── Step preserves word_valid ───────────────────────────────────────────────

///  A single step preserves word_valid.
///  Now fully proved: apply_step's FreeExpand guard ensures symbol_valid.
proof fn lemma_step_preserves_word_valid(
    p: Presentation, w: Word, step: DerivationStep, w_next: Word,
)
    requires
        apply_step(p, w, step) == Some(w_next),
        presentation_valid(p),
        word_valid(w, p.num_generators),
    ensures
        word_valid(w_next, p.num_generators),
{
    reveal(presentation_valid);
    let n = p.num_generators;
    match step {
        DerivationStep::FreeReduce { position } => {
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else { assert(w_next[k] == w[k + 2]); }
            }
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  apply_step guard ensures symbol_valid(symbol, n)
            lemma_inverse_preserves_valid(symbol, n);
            let pfx = w.subrange(0, position);
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            let sfx = w.subrange(position, w.len() as int);
            assert(w_next =~= pfx + pair + sfx);
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else if k == position as int { }
                else if k == position + 1 { assert(w_next[k] == inverse_symbol(symbol)); }
                else { assert(w_next[k] == w[k - 2]); }
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            if inverted { crate::word::lemma_inverse_word_valid(p.relators[relator_index as int], n); }
            assert(word_valid(r, n));
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else if k < position + r.len() { assert(w_next[k] == r[k - position]); }
                else { assert(w_next[k] == w[k - r.len() as int]); }
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else { assert(w_next[k] == w[k + r.len() as int]); }
            }
        },
    }
}

//  ─── Lemma 5: full derivation preserves trace ───────────────────────────────

///  A full derivation preserves trace_word.
pub proof fn lemma_trace_derivation(
    t: CosetTable, p: Presentation, c: nat,
    steps: Seq<DerivationStep>, w_start: Word,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        c < t.num_cosets,
        derivation_produces(p, steps, w_start) is Some,
        word_valid(w_start, p.num_generators),
    ensures
        trace_word(t, c, w_start)
            == trace_word(t, c, derivation_produces(p, steps, w_start).unwrap()),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let first_step = steps.first();
        let w_next = apply_step(p, w_start, first_step).unwrap();
        let rest = steps.drop_first();

        //  w_next is word_valid
        lemma_step_preserves_word_valid(p, w_start, first_step, w_next);

        //  Single step: trace(c, w_start) == trace(c, w_next)
        lemma_trace_single_step(t, p, c, w_start, first_step, w_next);

        //  Recurse
        if rest.len() > 0 {
            lemma_trace_derivation(t, p, c, rest, w_next);
        }
    }
}

//  ─── Main Theorem ────────────────────────────────────────────────────────────

///  If two words are equivalent in the presented group, they trace identically
///  through any valid, complete, consistent, relator-closed coset table.
pub proof fn lemma_trace_respects_equiv(
    t: CosetTable, p: Presentation, c: nat, w1: Word, w2: Word,
)
    requires
        coset_table_wf(t),
        coset_table_consistent(t),
        coset_table_complete(t),
        relator_closed(t, p),
        t.num_gens == p.num_generators,
        presentation_valid(p),
        c < t.num_cosets,
        equiv_in_presentation(p, w1, w2),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
    ensures
        trace_word(t, c, w1) == trace_word(t, c, w2),
{
    let d: Derivation = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    assert(derivation_produces(p, d.steps, w1) == Some(w2));
    lemma_trace_derivation(t, p, c, d.steps, w1);
}

} //  verus!
