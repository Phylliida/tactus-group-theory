use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::finite::coset_table_complete;

verus! {

///  Coset table for a finitely presented group.
///  table[coset][column] where column = 2*gen for Gen(gen), 2*gen+1 for Inv(gen).
///  None means undefined.
pub struct CosetTable {
    pub num_cosets: nat,
    pub num_gens: nat,
    pub table: Seq<Seq<Option<nat>>>,
}

///  Map a symbol to a column index.
pub open spec fn symbol_to_column(s: Symbol) -> nat {
    match s {
        Symbol::Gen(i) => 2 * i,
        Symbol::Inv(i) => 2 * i + 1,
    }
}

///  Map a column to its inverse column (Gen ↔ Inv for same generator).
pub open spec fn inverse_column(col: nat) -> nat {
    if col % 2 == 0 {
        col + 1
    } else {
        (col - 1) as nat
    }
}

///  A coset table is well-formed: dimensions match and values in range.
#[verifier::opaque]
pub open spec fn coset_table_wf(t: CosetTable) -> bool {
    let num_cols = 2 * t.num_gens;
    t.table.len() == t.num_cosets
    && (forall|c: int| #![trigger t.table[c]]
        0 <= c < t.num_cosets ==> t.table[c].len() == num_cols)
    && (forall|c: int, col: int| #![trigger t.table[c][col]]
        0 <= c < t.num_cosets && 0 <= col < num_cols ==>
            match t.table[c][col] {
                Some(d) => d < t.num_cosets,
                None => true,
            })
}

///  Inverse consistency: if table[c][col] = Some(d), then table[d][inv_col] = Some(c).
#[verifier::opaque]
pub open spec fn coset_table_consistent(t: CosetTable) -> bool {
    let num_cols = 2 * t.num_gens;
    coset_table_wf(t)
    && (forall|c: int, col: int| #![trigger t.table[c][col]]
        0 <= c < t.num_cosets && 0 <= col < num_cols ==>
            match t.table[c][col] {
                Some(d) => t.table[d as int][inverse_column(col as nat) as int] == Some(c as nat),
                None => true,
            })
}

///  Trace a word through the coset table starting from a coset.
///  Returns None if an undefined entry is hit.
/// Lean backend: axiom + defining equation (`.eq_def`) — drop_first
/// recursion's termination fact is out of decreasing_by's reach in
/// the preamble layout (same as `inverse_word`). Verus verifies
/// termination Z3-side.
#[verifier::lean_axiom_eq]
pub open spec fn trace_word(t: CosetTable, coset: nat, w: Word) -> Option<nat>
    decreases w.len(),
{
    if w.len() == 0 {
        Some(coset)
    } else {
        let col = symbol_to_column(w.first());
        match t.table[coset as int][col as int] {
            Some(next) => trace_word(t, next, w.drop_first()),
            None => None,
        }
    }
}

///  All relators trace back to the starting coset (closed table).
#[verifier::opaque]
pub open spec fn relator_closed(t: CosetTable, p: Presentation) -> bool {
    forall|c: int, r: int| #![trigger t.table[c as int], p.relators[r]]
        0 <= c < t.num_cosets && 0 <= r < p.relators.len() ==>
            trace_word(t, c as nat, p.relators[r]) == Some(c as nat)
}

//  --- Lemmas ---

///  Tracing the empty word returns the starting coset.
pub proof fn lemma_trace_empty(t: CosetTable, coset: nat)
    ensures
        trace_word(t, coset, empty_word()) == Some(coset),
{
}

///  Tracing a concatenation is composition of traces.
pub proof fn lemma_trace_word_concat(t: CosetTable, c: nat, w1: Word, w2: Word)
    requires
        coset_table_wf(t),
        trace_word(t, c, w1) is Some,
    ensures
        trace_word(t, c, concat(w1, w2)) ==
            trace_word(t, trace_word(t, c, w1).unwrap(), w2),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(trace_word(t, c, w1) == Some(c));
    } else {
        let col = symbol_to_column(w1.first());
        let next = t.table[c as int][col as int].unwrap();
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        //  trace_word(t, c, concat(w1, w2))
        //    = trace_word(t, next, concat(w1.drop_first(), w2))
        //  trace_word(t, c, w1)
        //    = trace_word(t, next, w1.drop_first())
        lemma_trace_word_concat(t, next, w1.drop_first(), w2);
    }
}

} //  verus!
