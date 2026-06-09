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

///  Bridge: rt_trace_word agrees with trace_word(rt_to_spec_table(...)).
pub proof fn lemma_rt_trace_equals_spec_trace(rt: RuntimeCosetTable, coset: nat, w: Word)
    requires
        coset < rt.num_cosets,
        rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
        //  flat array validity
        forall|i: int| 0 <= i < rt.table@.len() ==>
            rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
        //  word symbols in range
        forall|k: int| 0 <= k < w.len() ==>
            symbol_to_column(w[k]) < 2 * rt.num_gens,
    ensures
        rt_trace_word(rt, coset, w) == trace_word(rt_to_spec_table(rt), coset, w),
    decreases w.len(),
{
    let spec_t = rt_to_spec_table(rt);
    if w.len() == 0 {
        //  Both return Some(coset)
    } else {
        let col = symbol_to_column(w.first());
        let col_int = col as int;
        let idx = coset as int * 2 * rt.num_gens as int + col_int;

        //  Show idx is in bounds
        assert(col < 2 * rt.num_gens);
        assert(0 <= idx && idx < rt.num_cosets * 2 * rt.num_gens) by(nonlinear_arith)
            requires
                idx == coset as int * 2 * rt.num_gens as int + col_int,
                coset >= 0int, col_int >= 0int,
                coset < rt.num_cosets, col_int < 2 * rt.num_gens,
                rt.num_gens >= 0int, rt.num_cosets >= 0int;
        assert(0 <= idx < rt.table@.len() as int);

        //  Show spec_t.table[coset][col] unfolds to same thing
        assert(spec_t.table[coset as int] ==
            Seq::new(2 * rt.num_gens as nat, |c: int| {
                let val = rt.table@[(coset as int * 2 * rt.num_gens as int + c) as int];
                if val == UNDEF() { None } else { Some(val as nat) }
            }));
        let flat_val = rt.table@[idx];
        assert(spec_t.table[coset as int][col_int] == (
            if flat_val == UNDEF() { None } else { Some(flat_val as nat) }
        ));

        if flat_val == UNDEF() {
            //  Both return None
            assert(rt_trace_word(rt, coset, w) == Option::<nat>::None);
            assert(spec_t.table[coset as int][col_int] == Option::<nat>::None);
            assert(trace_word(spec_t, coset, w) == Option::<nat>::None);
        } else {
            let next = flat_val as nat;
            assert(next < rt.num_cosets);
            assert(spec_t.table[coset as int][col_int] == Some(next));
            //  Recurse
            assert forall|k: int| 0 <= k < w.drop_first().len() implies
                symbol_to_column(w.drop_first()[k]) < 2 * rt.num_gens
            by {
                assert(w.drop_first()[k] == w[k + 1]);
            }
            lemma_rt_trace_equals_spec_trace(rt, next, w.drop_first());
        }
    }
}

//  ============================================================
//  Runtime Coset Enumeration
//  ============================================================

///  Runtime coset table: flat array, usize::MAX = undefined.
pub struct RuntimeCosetTable {
    pub num_cosets: usize,
    pub num_gens: usize,
    ///  Flat table: table[c * 2*num_gens + col].
    pub table: Vec<usize>,
}

///  Undefined sentinel value.
pub open spec fn UNDEF() -> usize { usize::MAX }

///  Access the runtime table at (coset, column).
pub open spec fn rt_table_get(t: &RuntimeCosetTable, c: usize, col: usize) -> usize
    recommends c < t.num_cosets, col < 2 * t.num_gens,
{
    t.table@[(c * 2 * t.num_gens + col) as int]
}

///  Runtime symbol to column.
pub fn symbol_to_column_exec(s: &crate::runtime::RuntimeSymbol) -> (out: usize)
    requires
        symbol_to_column(crate::runtime::runtime_symbol_view(*s)) < usize::MAX,
    ensures
        out == symbol_to_column(crate::runtime::runtime_symbol_view(*s)) as usize,
{
    match s {
        crate::runtime::RuntimeSymbol::Gen(i) => 2 * *i,
        crate::runtime::RuntimeSymbol::Inv(i) => 2 * *i + 1,
    }
}

///  Helper: derive overflow bounds from the multiplication guard.
proof fn lemma_overflow_bounds(num_cosets: usize, num_gens: usize)
    requires
        num_cosets >= 1,
        num_cosets * (2 * num_gens + 1) < usize::MAX,
    ensures
        2 * num_gens < usize::MAX,
        num_cosets * 2 * num_gens < usize::MAX,
{
    assert(2 * num_gens + 1 <= num_cosets * (2 * num_gens + 1)) by(nonlinear_arith)
        requires num_cosets >= 1int, num_gens >= 0int;
    assert(num_cosets * 2 * num_gens <= num_cosets * (2 * num_gens + 1)) by(nonlinear_arith)
        requires num_cosets >= 0int, num_gens >= 0int;
}

///  Convert RuntimeCosetTable to spec CosetTable.
pub open spec fn rt_to_spec_table(rt: RuntimeCosetTable) -> CosetTable {
    CosetTable {
        num_cosets: rt.num_cosets as nat,
        num_gens: rt.num_gens as nat,
        table: Seq::new(rt.num_cosets as nat, |c: int|
            Seq::new(2 * rt.num_gens as nat, |col: int| {
                let val = rt.table@[(c * 2 * rt.num_gens as int + col) as int];
                if val == UNDEF() { None } else { Some(val as nat) }
            })
        ),
    }
}

///  Convert runtime relators to spec Presentation.
pub open spec fn rt_presentation_view(
    num_gens: usize,
    relators: Seq<Vec<crate::runtime::RuntimeSymbol>>,
) -> Presentation {
    Presentation {
        num_generators: num_gens as nat,
        relators: Seq::new(relators.len(), |i: int|
            crate::runtime::runtime_word_view(relators[i]@)),
    }
}

///  Trace a word through the runtime flat table.
///  Avoids going through rt_to_spec_table in loop invariants.
pub open spec fn rt_trace_word(rt: RuntimeCosetTable, coset: nat, w: Word) -> Option<nat>
    decreases w.len(),
{
    if w.len() == 0 {
        Some(coset)
    } else {
        let col = symbol_to_column(w.first()) as int;
        let idx = coset as int * 2 * rt.num_gens as int + col;
        if 0 <= idx < rt.table@.len() as int {
            let val = rt.table@[idx];
            if val == UNDEF() { None }
            else { rt_trace_word(rt, val as nat, w.drop_first()) }
        } else { None }
    }
}

///  Helper: one step of rt_trace_word unfolding.
///  Given a non-empty word w_tail with w_rest = w_tail.drop_first(),
///  shows how rt_trace_word(rt, current, w_tail) relates to the flat table lookup
///  and the recursive call on w_rest.
proof fn lemma_rt_trace_word_unfold(
    rt: RuntimeCosetTable,
    current: nat,
    w_tail: Word,
    w_rest: Word,
    flat_idx: int,
)
    requires
        w_tail.len() > 0,
        w_rest =~= w_tail.drop_first(),
        current < rt.num_cosets,
        rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
        symbol_to_column(w_tail.first()) < 2 * rt.num_gens,
        flat_idx == current as int * 2 * rt.num_gens as int
            + symbol_to_column(w_tail.first()) as int,
        0 <= flat_idx < rt.table@.len() as int,
    ensures
        rt.table@[flat_idx] == UNDEF() ==>
            rt_trace_word(rt, current, w_tail) is None,
        rt.table@[flat_idx] != UNDEF() ==>
            rt_trace_word(rt, current, w_tail)
                == rt_trace_word(rt, rt.table@[flat_idx] as nat, w_rest),
{
    //  rt_trace_word unfolds: col, idx match our flat_idx
}

///  Scan a relator from a coset, returning the final coset or usize::MAX if undefined.
pub fn scan_relator_exec(
    table: &RuntimeCosetTable,
    coset: usize,
    relator: &Vec<crate::runtime::RuntimeSymbol>,
) -> (out: usize)
    requires
        coset < table.num_cosets,
        table.num_cosets >= 1,
        table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
        table.table@.len() >= table.num_cosets * 2 * table.num_gens,
        table.num_gens > 0,
        forall|k: int| 0 <= k < relator@.len() ==>
            symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
        //  Flat array validity
        forall|i: int| 0 <= i < table.table@.len() ==>
            table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
    ensures
        out == UNDEF() || out < table.num_cosets,
        //  Spec bridge: connect result to rt_trace_word
        out != UNDEF() ==>
            rt_trace_word(*table, coset as nat,
                crate::runtime::runtime_word_view(relator@)) == Some(out as nat),
        out == UNDEF() ==>
            rt_trace_word(*table, coset as nat,
                crate::runtime::runtime_word_view(relator@)) is None,
{
    proof { lemma_overflow_bounds(table.num_cosets, table.num_gens); }
    let num_cols: usize = 2 * table.num_gens;
    let rlen = relator.len();
    let mut current = coset;
    let mut i: usize = 0;
    let ghost full_word: Word = crate::runtime::runtime_word_view(relator@);
    proof {
        //  Establish invariant before loop: subrange(0, rlen) =~= full
        assert(relator@.subrange(0, rlen as int) =~= relator@);
        assert(crate::runtime::runtime_word_view(relator@.subrange(0, rlen as int))
            =~= full_word) by {
            let sub = relator@.subrange(0, rlen as int);
            assert(sub =~= relator@);
            assert forall|k: int| 0 <= k < sub.len()
                implies crate::runtime::runtime_symbol_view(sub[k])
                    == crate::runtime::runtime_symbol_view(relator@[k])
            by {}
        }
    }
    while i < rlen
        invariant
            0 <= i <= rlen,
            rlen == relator@.len(),
            current < table.num_cosets,
            table.num_cosets >= 1,
            table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
            table.table@.len() >= table.num_cosets * 2 * table.num_gens,
            num_cols == 2 * table.num_gens,
            table.num_gens > 0,
            2 * table.num_gens < usize::MAX,
            table.num_cosets * 2 * table.num_gens < usize::MAX,
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
            forall|j: int| 0 <= j < table.table@.len() ==>
                table.table@[j] == UNDEF() || table.table@[j] < table.num_cosets,
            full_word == crate::runtime::runtime_word_view(relator@),
            //  Key invariant: trace from coset through full word ==
            //  trace from current through remaining suffix
            rt_trace_word(*table, coset as nat, full_word)
                == rt_trace_word(*table, current as nat,
                    crate::runtime::runtime_word_view(relator@.subrange(i as int, rlen as int))),
        decreases rlen - i,
    {
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[i as int])) < 2 * table.num_gens);
        }
        let col = symbol_to_column_exec(&relator[i]);
        proof {
            assert(current * num_cols + col < table.num_cosets * num_cols) by(nonlinear_arith)
                requires current < table.num_cosets, col < num_cols, num_cols == 2 * table.num_gens,
                    table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx = current * num_cols + col;
        let next = table.table[idx];
        //  Shared proof setup for both branches
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[i as int])) < 2 * table.num_gens);
        }
        let ghost w_tail: Word = crate::runtime::runtime_word_view(
            relator@.subrange(i as int, rlen as int));
        let ghost w_rest: Word = crate::runtime::runtime_word_view(
            relator@.subrange((i + 1) as int, rlen as int));
        proof {
            //  w_tail.first() == runtime_symbol_view(relator@[i])
            assert(w_tail.first() == crate::runtime::runtime_symbol_view(relator@[i as int])) by {
                assert(relator@.subrange(i as int, rlen as int)[0] == relator@[i as int]);
            }
            assert(w_tail.len() > 0) by {
                assert(relator@.subrange(i as int, rlen as int).len() > 0);
            }
            //  Show w_tail.drop_first() =~= w_rest
            assert(w_tail.drop_first() =~= w_rest) by {
                let sub_full = relator@.subrange(i as int, rlen as int);
                let sub_rest = relator@.subrange((i + 1) as int, rlen as int);
                assert(sub_full.drop_first() =~= sub_rest);
                assert forall|k: int| 0 <= k < w_rest.len()
                    implies w_tail.drop_first()[k] == w_rest[k]
                by {
                    assert(w_tail.drop_first()[k] == w_tail[k + 1]);
                    assert(w_tail[k + 1]
                        == crate::runtime::runtime_symbol_view(sub_full[k + 1]));
                    assert(sub_full[k + 1] == relator@[(i + 1 + k) as int]);
                    assert(w_rest[k]
                        == crate::runtime::runtime_symbol_view(sub_rest[k]));
                    assert(sub_rest[k] == relator@[(i + 1 + k) as int]);
                }
            }
            //  Bridge exec idx to spec idx
            assert(symbol_to_column(w_tail.first()) == col as nat);
            //  exec: idx = current * num_cols + col
            //  spec: current as int * 2 * table.num_gens as int + col as int
            //  These are equal since num_cols == 2 * table.num_gens
            assert(idx as int == current as int * num_cols as int + col as int);
            assert(current as int * num_cols as int + col as int
                == current as int * 2 * table.num_gens as int + col as int) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int;
            //  Call the unfold helper
            lemma_rt_trace_word_unfold(*table, current as nat, w_tail, w_rest,
                current as int * 2 * table.num_gens as int + col as int);
        }
        if next == usize::MAX || next >= table.num_cosets {
            proof {
                //  next is UNDEF or >= num_cosets
                //  If >= num_cosets but not UNDEF: contradicts flat array validity
                if next != usize::MAX {
                    assert(table.table@[idx as int] == UNDEF()
                        || table.table@[idx as int] < table.num_cosets);
                    assert(false); //  contradiction
                }
                //  table@[flat_idx] == UNDEF(), so rt_trace_word is None
                assert(table.table@[idx as int] == UNDEF());
            }
            return usize::MAX;
        }
        proof {
            assert(table.table@[idx as int] == next);
            assert(next != UNDEF());
            //  rt_trace_word(table, current, w_tail) == rt_trace_word(table, next, w_rest)
        }
        current = next;
        i = i + 1;
    }
    proof {
        //  At the end, i == rlen, so the subrange is empty
        let w_empty = crate::runtime::runtime_word_view(
            relator@.subrange(rlen as int, rlen as int));
        assert(w_empty.len() == 0) by {
            assert(relator@.subrange(rlen as int, rlen as int).len() == 0);
        }
        assert(rt_trace_word(*table, current as nat, w_empty) == Some(current as nat));
    }
    current
}

///  Result of scanning a relator through the coset table.
pub enum ScanResult {
    ///  Relator traces back correctly, no changes needed.
    Closed,
    ///  Exactly one gap found and filled (+ inverse entry).
    Deduction,
    ///  Multiple gaps remain, no deduction possible.
    Incomplete,
    ///  Conflict detected: two different cosets forced equal.
    Coincidence,
}

///  Compute the inverse column index (exec version).
pub fn inverse_column_exec(col: usize) -> (out: usize)
    requires col < usize::MAX,
    ensures out == inverse_column(col as nat) as usize,
{
    if col % 2 == 0 { col + 1 } else { col - 1 }
}

///  Scan a relator from a coset with forward+backward scanning, filling single-gap deductions.
///
///  Forward scans from `coset` through relator symbols until hitting UNDEF.
///  Backward scans from `coset` through inverse symbols until meeting the forward scan.
///  If exactly one gap remains, fills it (deduction). If the endpoints disagree, returns Coincidence.
pub fn scan_and_fill_exec(
    table: &mut RuntimeCosetTable,
    coset: usize,
    relator: &Vec<crate::runtime::RuntimeSymbol>,
) -> (out: ScanResult)
    requires
        coset < old(table).num_cosets,
        old(table).num_cosets >= 1,
        old(table).num_cosets * (2 * old(table).num_gens + 1) < usize::MAX,
        old(table).table@.len() >= old(table).num_cosets * 2 * old(table).num_gens,
        old(table).num_gens > 0,
        forall|k: int| 0 <= k < relator@.len() ==>
            symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * old(table).num_gens,
        //  Entry validity (flat array): all entries are UNDEF or < num_cosets
        forall|i: int| #![trigger old(table).table@[i]]
            0 <= i < old(table).table@.len() ==>
            old(table).table@[i] == UNDEF() || old(table).table@[i] < old(table).num_cosets,
    ensures
        table.num_cosets == old(table).num_cosets,
        table.num_gens == old(table).num_gens,
        table.table@.len() == old(table).table@.len(),
        //  Entry validity preserved (flat array)
        forall|i: int| #![trigger table.table@[i]]
            0 <= i < table.table@.len() ==>
            table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
{
    proof { lemma_overflow_bounds(table.num_cosets, table.num_gens); }
    let num_cols: usize = 2 * table.num_gens;
    let rlen = relator.len();

    if rlen == 0 {
        return ScanResult::Closed;
    }

    //  --- Forward scan ---
    let mut f_coset: usize = coset;
    let mut f_pos: usize = 0;
    while f_pos < rlen
        invariant
            0 <= f_pos <= rlen,
            f_coset < table.num_cosets,
            table.num_cosets >= 1,
            table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
            table.table@.len() >= table.num_cosets * 2 * table.num_gens,
            num_cols == 2 * table.num_gens,
            table.num_gens > 0,
            2 * table.num_gens < usize::MAX,
            table.num_cosets * 2 * table.num_gens < usize::MAX,
            rlen == relator@.len(),
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
            forall|i: int| #![trigger table.table@[i]]
                0 <= i < table.table@.len() ==>
                table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
        decreases rlen - f_pos,
    {
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[f_pos as int])) < 2 * table.num_gens);
        }
        let col = symbol_to_column_exec(&relator[f_pos]);
        proof {
            assert(f_coset * num_cols + col < table.num_cosets * num_cols) by(nonlinear_arith)
                requires f_coset < table.num_cosets, col < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx = f_coset * num_cols + col;
        let val = table.table[idx];
        if val == usize::MAX {
            break;
        }
        if val >= table.num_cosets {
            break;
        }
        f_coset = val;
        f_pos = f_pos + 1;
    }

    //  If forward scan completed all symbols
    if f_pos == rlen {
        if f_coset == coset {
            return ScanResult::Closed;
        } else {
            return ScanResult::Coincidence;
        }
    }

    //  --- Backward scan ---
    let mut b_coset: usize = coset;
    let mut b_pos: usize = rlen;
    while b_pos > f_pos + 1
        invariant
            f_pos < b_pos,
            b_pos <= rlen,
            b_coset < table.num_cosets,
            table.num_cosets >= 1,
            table.num_cosets * (2 * table.num_gens + 1) < usize::MAX,
            table.table@.len() >= table.num_cosets * 2 * table.num_gens,
            num_cols == 2 * table.num_gens,
            table.num_gens > 0,
            2 * table.num_gens < usize::MAX,
            table.num_cosets * 2 * table.num_gens < usize::MAX,
            rlen == relator@.len(),
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * table.num_gens,
            forall|i: int| #![trigger table.table@[i]]
                0 <= i < table.table@.len() ==>
                table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets,
        decreases b_pos - f_pos,
    {
        let sym_pos = b_pos - 1;
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[sym_pos as int])) < 2 * table.num_gens);
        }
        let col = symbol_to_column_exec(&relator[sym_pos]);
        let inv_col = inverse_column_exec(col);
        proof {
            assert(inv_col < num_cols) by {
                if col % 2 == 0 {
                    assert(inv_col == col + 1);
                } else {
                    assert(inv_col == col - 1);
                }
            }
            assert(b_coset * num_cols + inv_col < table.num_cosets * num_cols) by(nonlinear_arith)
                requires b_coset < table.num_cosets, inv_col < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx = b_coset * num_cols + inv_col;
        let val = table.table[idx];
        if val == usize::MAX {
            break;
        }
        if val >= table.num_cosets {
            break;
        }
        b_coset = val;
        b_pos = b_pos - 1;
    }

    //  --- Gap analysis ---
    if b_pos == f_pos + 1 {
        //  Exactly one gap at position f_pos: fill table[f_coset][col_f] = b_coset
        proof {
            assert(symbol_to_column(crate::runtime::runtime_symbol_view(relator@[f_pos as int])) < 2 * table.num_gens);
        }
        let col_f = symbol_to_column_exec(&relator[f_pos]);
        let inv_col_f = inverse_column_exec(col_f);
        proof {
            assert(inv_col_f < num_cols) by {
                if col_f % 2 == 0 {
                    assert(inv_col_f == col_f + 1);
                } else {
                    assert(inv_col_f == col_f - 1);
                }
            }
        }

        //  Check for coincidence
        proof {
            assert(f_coset * num_cols + col_f < table.num_cosets * num_cols) by(nonlinear_arith)
                requires f_coset < table.num_cosets, col_f < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx_fwd = f_coset * num_cols + col_f;
        let existing_fwd = table.table[idx_fwd];
        if existing_fwd != usize::MAX && existing_fwd != b_coset {
            return ScanResult::Coincidence;
        }

        proof {
            assert(b_coset * num_cols + inv_col_f < table.num_cosets * num_cols) by(nonlinear_arith)
                requires b_coset < table.num_cosets, inv_col_f < num_cols, num_cols == 2 * table.num_gens, table.num_gens > 0int;
            assert(table.num_cosets * num_cols <= table.num_cosets * 2 * table.num_gens) by(nonlinear_arith)
                requires num_cols == 2 * table.num_gens, table.num_gens >= 0int, table.num_cosets >= 0int;
        }
        let idx_bwd = b_coset * num_cols + inv_col_f;
        let existing_bwd = table.table[idx_bwd];
        if existing_bwd != usize::MAX && existing_bwd != f_coset {
            return ScanResult::Coincidence;
        }

        //  Fill the deduction
        table.table.set(idx_fwd, b_coset);
        table.table.set(idx_bwd, f_coset);

        //  Flat array validity preserved: both written values < num_cosets,
        //  and all other entries unchanged from the old valid state.
        proof {
            assert forall|i: int| #![trigger table.table@[i]]
                0 <= i < table.table@.len() implies
                table.table@[i] == UNDEF() || table.table@[i] < table.num_cosets
            by {
                if i == idx_bwd as int {
                    //  f_coset < num_cosets
                } else if i == idx_fwd as int {
                    //  b_coset < num_cosets
                } else {
                    //  unchanged
                }
            }
        }

        return ScanResult::Deduction;
    }

    //  Multiple gaps
    ScanResult::Incomplete
}

//  ============================================================
//  Runtime Checkers (verify spec properties from flat array)
//  ============================================================

///  Check that the runtime coset table is complete (no UNDEF entries in active region).
pub fn check_rt_complete_exec(rt: &RuntimeCosetTable) -> (result: bool)
    requires
        rt.num_cosets >= 1,
        rt.num_gens > 0,
        rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
        rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
        forall|i: int| 0 <= i < rt.table@.len() ==>
            rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
    ensures
        result ==> coset_table_complete(rt_to_spec_table(*rt)),
{
    proof { reveal(coset_table_complete); lemma_overflow_bounds(rt.num_cosets, rt.num_gens); }
    let num_cols: usize = 2 * rt.num_gens;
    //  Scan using nested loops to avoid needing active_size multiplication
    let mut c: usize = 0;
    while c < rt.num_cosets
        invariant
            0 <= c <= rt.num_cosets,
            num_cols == 2 * rt.num_gens,
            rt.num_cosets >= 1,
            rt.num_gens > 0,
            rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
            rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
            rt.num_cosets * 2 * rt.num_gens < usize::MAX,
            2 * rt.num_gens < usize::MAX,
            forall|i: int| 0 <= i < rt.table@.len() ==>
                rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
            //  All entries in rows [0, c) are not UNDEF
            forall|ci: int, coli: int|
                0 <= ci < c && 0 <= coli < num_cols ==>
                    rt.table@[#[trigger](ci * 2 * rt.num_gens as int + coli) as int] != UNDEF(),
        decreases rt.num_cosets - c,
    {
        let mut col: usize = 0;
        while col < num_cols
            invariant
                0 <= col <= num_cols,
                0 <= c < rt.num_cosets,
                num_cols == 2 * rt.num_gens,
                rt.num_cosets >= 1,
                rt.num_gens > 0,
                rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
                rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
                rt.num_cosets * 2 * rt.num_gens < usize::MAX,
                2 * rt.num_gens < usize::MAX,
                forall|i: int| 0 <= i < rt.table@.len() ==>
                    rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
                //  Previous rows
                forall|ci: int, coli: int|
                    0 <= ci < c && 0 <= coli < num_cols ==>
                        rt.table@[#[trigger](ci * 2 * rt.num_gens as int + coli) as int] != UNDEF(),
                //  Current row, checked columns
                forall|coli: int|
                    0 <= coli < col ==>
                        rt.table@[#[trigger](c as int * 2 * rt.num_gens as int + coli) as int] != UNDEF(),
            decreases num_cols - col,
        {
            proof {
                assert(c * num_cols + col < rt.num_cosets * num_cols) by(nonlinear_arith)
                    requires c < rt.num_cosets, col < num_cols, num_cols == 2 * rt.num_gens, rt.num_gens > 0int;
                assert(rt.num_cosets * num_cols <= rt.num_cosets * 2 * rt.num_gens) by(nonlinear_arith)
                    requires num_cols == 2 * rt.num_gens, rt.num_gens >= 0int, rt.num_cosets >= 0int;
            }
            let idx = c * num_cols + col;
            if rt.table[idx] == usize::MAX {
                return false;
            }
            proof {
                //  Show idx == c * 2 * num_gens + col for the invariant trigger
                assert(idx as int == c as int * num_cols as int + col as int);
                assert(c as int * num_cols as int == c as int * 2 * rt.num_gens as int) by(nonlinear_arith)
                    requires num_cols == 2 * rt.num_gens, rt.num_gens >= 0int;
            }
            col = col + 1;
        }
        c = c + 1;
    }
    proof {
        let spec_t = rt_to_spec_table(*rt);
        assert forall|ci: int, coli: int|
            0 <= ci < spec_t.num_cosets && 0 <= coli < 2 * spec_t.num_gens
            implies (#[trigger] spec_t.table[ci][coli]) is Some
        by {
            //  Our invariant gives: table@[ci * 2 * num_gens + coli] != UNDEF
            assert(rt.table@[(ci * 2 * rt.num_gens as int + coli) as int] != UNDEF());
            //  Seq::new unfolding
            assert(spec_t.table[ci] ==
                Seq::new(2 * rt.num_gens as nat, |col2: int| {
                    let val = rt.table@[(ci * 2 * rt.num_gens as int + col2) as int];
                    if val == UNDEF() { None } else { Some(val as nat) }
                }));
        }
    }
    true
}

///  Helper spec: check flat-table consistency at position (ci, coli).
pub open spec fn rt_consistent_at(rt: RuntimeCosetTable, ci: int, coli: int) -> bool {
    let flat = (ci * 2 * rt.num_gens as int + coli) as int;
    let val = rt.table@[flat];
    let inv_col: int = if coli % 2 == 0 { coli + 1 } else { coli - 1 };
    val == UNDEF() ||
        rt.table@[(val as int * 2 * rt.num_gens as int + inv_col) as int] == ci as usize
}

///  Check that the runtime coset table is consistent (inverse symmetry).
pub fn check_rt_consistent_exec(rt: &RuntimeCosetTable) -> (result: bool)
    requires
        rt.num_cosets >= 1,
        rt.num_gens > 0,
        rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
        rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
        forall|i: int| 0 <= i < rt.table@.len() ==>
            rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
    ensures
        result ==> coset_table_consistent(rt_to_spec_table(*rt)),
{
    proof { lemma_overflow_bounds(rt.num_cosets, rt.num_gens); }
    let num_cols: usize = 2 * rt.num_gens;

    let mut c: usize = 0;
    while c < rt.num_cosets
        invariant
            0 <= c <= rt.num_cosets,
            num_cols == 2 * rt.num_gens,
            rt.num_cosets >= 1,
            rt.num_gens > 0,
            rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
            rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
            2 * rt.num_gens < usize::MAX,
            rt.num_cosets * 2 * rt.num_gens < usize::MAX,
            forall|i: int| 0 <= i < rt.table@.len() ==>
                rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
            //  All checked entries satisfy consistency
            forall|ci: int, coli: int| #![trigger rt_consistent_at(*rt, ci, coli)]
                0 <= ci < c && 0 <= coli < num_cols ==>
                    rt_consistent_at(*rt, ci, coli),
        decreases rt.num_cosets - c,
    {
        let mut col: usize = 0;
        while col < num_cols
            invariant
                0 <= col <= num_cols,
                0 <= c < rt.num_cosets,
                num_cols == 2 * rt.num_gens,
                rt.num_cosets >= 1,
                rt.num_gens > 0,
                rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
                rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
                2 * rt.num_gens < usize::MAX,
                rt.num_cosets * 2 * rt.num_gens < usize::MAX,
                forall|i: int| 0 <= i < rt.table@.len() ==>
                    rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
                //  Previously checked rows
                forall|ci: int, coli: int| #![trigger rt_consistent_at(*rt, ci, coli)]
                    0 <= ci < c && 0 <= coli < num_cols ==>
                        rt_consistent_at(*rt, ci, coli),
                //  Current row, checked columns
                forall|coli: int| #![trigger rt_consistent_at(*rt, c as int, coli)]
                    0 <= coli < col ==>
                        rt_consistent_at(*rt, c as int, coli),
            decreases num_cols - col,
        {
            proof {
                assert(c * num_cols + col < rt.num_cosets * num_cols) by(nonlinear_arith)
                    requires c < rt.num_cosets, col < num_cols, num_cols == 2 * rt.num_gens, rt.num_gens > 0int;
                assert(rt.num_cosets * num_cols <= rt.num_cosets * 2 * rt.num_gens) by(nonlinear_arith)
                    requires num_cols == 2 * rt.num_gens, rt.num_gens >= 0int, rt.num_cosets >= 0int;
            }
            let idx = c * num_cols + col;
            let val = rt.table[idx];
            if val != usize::MAX {
                let inv_col: usize = if col % 2 == 0 { col + 1 } else { col - 1 };
                proof {
                    assert(inv_col < num_cols) by {
                        if col % 2 == 0 { assert(inv_col == col + 1); }
                        else { assert(inv_col == col - 1); }
                    }
                    assert(val * num_cols + inv_col < rt.num_cosets * num_cols) by(nonlinear_arith)
                        requires val < rt.num_cosets, inv_col < num_cols,
                            num_cols == 2 * rt.num_gens, rt.num_gens > 0int;
                }
                let inv_idx = val * num_cols + inv_col;
                let back = rt.table[inv_idx];
                if back != c {
                    return false;
                }
                proof {
                    //  Bridge exec indices to spec indices
                    assert(c as int * num_cols as int == c as int * 2 * rt.num_gens as int) by(nonlinear_arith)
                        requires num_cols == 2 * rt.num_gens, rt.num_gens >= 0int;
                    assert(val as int * num_cols as int == val as int * 2 * rt.num_gens as int) by(nonlinear_arith)
                        requires num_cols == 2 * rt.num_gens, rt.num_gens >= 0int;
                    //  back == c, so table@[val * 2 * num_gens + inv_col] == c
                    assert(rt.table@[(val as int * 2 * rt.num_gens as int + inv_col as int) as int] == c);
                    //  rt_consistent_at unfolds: flat = c * 2 * num_gens + col, val = table@[flat],
                    //  inv_col matches, and back == c. All conditions met.
                    assert(rt_consistent_at(*rt, c as int, col as int));
                }
            } else {
                proof {
                    //  val is UNDEF, so rt_consistent_at trivially holds
                    assert(c as int * num_cols as int == c as int * 2 * rt.num_gens as int) by(nonlinear_arith)
                        requires num_cols == 2 * rt.num_gens, rt.num_gens >= 0int;
                    assert(rt_consistent_at(*rt, c as int, col as int));
                }
            }
            col = col + 1;
        }
        c = c + 1;
    }
    proof {
        //  We now have: forall ci, coli in range: rt_consistent_at(*rt, ci, coli)
        lemma_rt_consistent_implies_spec(*rt);
    }
    true
}

///  Bridge: rt_consistent_at for all entries → coset_table_consistent(rt_to_spec_table(rt)).
proof fn lemma_rt_consistent_implies_spec(rt: RuntimeCosetTable)
    requires
        rt.num_cosets >= 1,
        rt.num_gens > 0,
        rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
        rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
        forall|i: int| 0 <= i < rt.table@.len() ==>
            rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
        forall|ci: int, coli: int| #![trigger rt_consistent_at(rt, ci, coli)]
            0 <= ci < rt.num_cosets && 0 <= coli < 2 * rt.num_gens ==>
                rt_consistent_at(rt, ci, coli),
    ensures
        coset_table_consistent(rt_to_spec_table(rt)),
{
    reveal(coset_table_wf);
    reveal(coset_table_consistent);
    lemma_overflow_bounds(rt.num_cosets, rt.num_gens);
    let spec_t = rt_to_spec_table(rt);

    //  Prove wf
    assert(coset_table_wf(spec_t)) by {
        assert(spec_t.table.len() == spec_t.num_cosets);
        assert forall|ci: int| #![trigger spec_t.table[ci]]
            0 <= ci < spec_t.num_cosets implies spec_t.table[ci].len() == 2 * spec_t.num_gens
        by {}
        assert forall|ci: int, coli: int| #![trigger spec_t.table[ci][coli]]
            0 <= ci < spec_t.num_cosets && 0 <= coli < 2 * spec_t.num_gens implies
                match spec_t.table[ci][coli] {
                    Some(d) => d < spec_t.num_cosets,
                    None => true,
                }
        by {
            //  Need flat index in bounds
            let flat = ci * 2 * rt.num_gens as int + coli;
            assert(0 <= flat && flat < rt.table@.len() as int) by(nonlinear_arith)
                requires
                    flat == ci * 2 * rt.num_gens as int + coli,
                    0 <= ci, ci < rt.num_cosets as int,
                    0 <= coli, coli < 2 * rt.num_gens as int,
                    rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
                    rt.num_gens >= 0int, rt.num_cosets >= 0int;
            assert(spec_t.table[ci] ==
                Seq::new(2 * rt.num_gens as nat, |col2: int| {
                    let v = rt.table@[(ci * 2 * rt.num_gens as int + col2) as int];
                    if v == UNDEF() { None } else { Some(v as nat) }
                }));
        }
    }

    //  Prove consistency
    assert forall|ci: int, coli: int| #![trigger spec_t.table[ci][coli]]
        0 <= ci < spec_t.num_cosets && 0 <= coli < 2 * spec_t.num_gens implies
            match spec_t.table[ci][coli] {
                Some(d) => spec_t.table[d as int][inverse_column(coli as nat) as int]
                    == Some(ci as nat),
                None => true,
            }
    by {
        assert(rt_consistent_at(rt, ci, coli));
        let flat = ci * 2 * rt.num_gens as int + coli;
        assert(0 <= flat && flat < rt.table@.len() as int) by(nonlinear_arith)
            requires
                flat == ci * 2 * rt.num_gens as int + coli,
                0 <= ci, ci < rt.num_cosets as int,
                0 <= coli, coli < 2 * rt.num_gens as int,
                rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
                rt.num_gens >= 0int, rt.num_cosets >= 0int;
        let val = rt.table@[flat];
        if val != UNDEF() {
            let inv_col: int = if coli % 2 == 0 { coli + 1 } else { coli - 1 };
            assert(rt.table@[(val as int * 2 * rt.num_gens as int + inv_col) as int] == ci as usize);
            assert(inverse_column(coli as nat) as int == inv_col) by {
                if coli % 2 == 0 {
                    assert(inverse_column(coli as nat) == coli + 1);
                } else {
                    assert(inverse_column(coli as nat) == (coli - 1) as nat);
                }
            }
            let d = val as nat;
            assert(ci as usize != UNDEF()) by {
                let nc = rt.num_cosets as int;
                let ng = rt.num_gens as int;
                let max_usize = usize::MAX as int;
                assert(nc < max_usize) by(nonlinear_arith)
                    requires nc * (2 * ng + 1) < max_usize, ng > 0, nc >= 0;
            }
            //  Unfold spec_t.table[d][inv_col]
            let inv_flat = val as int * 2 * rt.num_gens as int + inv_col;
            assert(0 <= inv_flat && inv_flat < rt.table@.len() as int) by(nonlinear_arith)
                requires
                    inv_flat == val as int * 2 * rt.num_gens as int + inv_col,
                    0 <= val as int, (val as int) < rt.num_cosets as int,
                    0 <= inv_col, inv_col < 2 * rt.num_gens as int,
                    rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
                    rt.num_gens >= 0int, rt.num_cosets >= 0int;
            assert(spec_t.table[d as int] ==
                Seq::new(2 * rt.num_gens as nat, |col2: int| {
                    let v = rt.table@[(d as int * 2 * rt.num_gens as int + col2) as int];
                    if v == UNDEF() { None } else { Some(v as nat) }
                }));
        }
    }
}

///  Helper: scan one relator from all cosets, checking closure.
fn check_one_relator_closed_exec(
    rt: &RuntimeCosetTable,
    relator: &Vec<crate::runtime::RuntimeSymbol>,
) -> (result: bool)
    requires
        rt.num_cosets >= 1,
        rt.num_gens > 0,
        rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
        rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
        forall|i: int| 0 <= i < rt.table@.len() ==>
            rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
        forall|k: int| 0 <= k < relator@.len() ==>
            symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * rt.num_gens,
    ensures
        result ==> forall|ci: nat| ci < rt.num_cosets ==>
            rt_trace_word(*rt, ci,
                crate::runtime::runtime_word_view(relator@)) == Some(ci),
{
    proof { lemma_overflow_bounds(rt.num_cosets, rt.num_gens); }
    let mut ci: usize = 0;
    while ci < rt.num_cosets
        invariant
            0 <= ci <= rt.num_cosets,
            rt.num_cosets >= 1,
            rt.num_gens > 0,
            rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
            rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
            forall|i: int| 0 <= i < rt.table@.len() ==>
                rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
            forall|k: int| 0 <= k < relator@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relator@[k])) < 2 * rt.num_gens,
            forall|cj: nat| cj < ci ==>
                rt_trace_word(*rt, cj,
                    crate::runtime::runtime_word_view(relator@)) == Some(cj),
        decreases rt.num_cosets - ci,
    {
        let out = scan_relator_exec(rt, ci, relator);
        if out == usize::MAX || out != ci {
            return false;
        }
        ci = ci + 1;
    }
    true
}

///  Check that all relators trace back to the starting coset.
pub fn check_rt_relator_closed_exec(
    rt: &RuntimeCosetTable,
    relators: &Vec<Vec<crate::runtime::RuntimeSymbol>>,
) -> (result: bool)
    requires
        rt.num_cosets >= 1,
        rt.num_gens > 0,
        rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
        rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
        forall|i: int| 0 <= i < rt.table@.len() ==>
            rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
        forall|r: int, k: int| #![trigger relators@[r]@[k]]
            0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * rt.num_gens,
    ensures
        result ==> relator_closed(
            rt_to_spec_table(*rt),
            rt_presentation_view(rt.num_gens, relators@),

        ),
{
    proof { reveal(relator_closed); }
    let mut ri: usize = 0;
    while ri < relators.len()
        invariant
            0 <= ri <= relators.len(),
            rt.num_cosets >= 1,
            rt.num_gens > 0,
            rt.num_cosets * (2 * rt.num_gens + 1) < usize::MAX,
            rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens,
            forall|i: int| 0 <= i < rt.table@.len() ==>
                rt.table@[i] == UNDEF() || rt.table@[i] < rt.num_cosets,
            forall|r: int, k: int| #![trigger relators@[r]@[k]]
                0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                    symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * rt.num_gens,
            //  All relators up to ri have been checked
            forall|ci: nat, rj: int|
                #![trigger rt_trace_word(*rt, ci, crate::runtime::runtime_word_view(relators@[rj]@))]
                ci < rt.num_cosets && 0 <= rj < ri ==>
                    rt_trace_word(*rt, ci,
                        crate::runtime::runtime_word_view(relators@[rj]@))
                        == Some(ci),
        decreases relators.len() - ri,
    {
        let ok = check_one_relator_closed_exec(rt, &relators[ri]);
        if !ok {
            return false;
        }
        ri = ri + 1;
    }
    proof {
        let spec_t = rt_to_spec_table(*rt);
        let p = rt_presentation_view(rt.num_gens, relators@);
        assert forall|c: int, r: int| #![trigger spec_t.table[c as int], p.relators[r]]
            0 <= c < spec_t.num_cosets && 0 <= r < p.relators.len() implies
                trace_word(spec_t, c as nat, p.relators[r]) == Some(c as nat)
        by {
            assert(p.relators[r] == crate::runtime::runtime_word_view(relators@[r]@));
            //  Trigger the loop invariant
            assert(relators@[r] == relators@[r]);
            assert(rt_trace_word(*rt, c as nat, p.relators[r]) == Some(c as nat));
            //  Bridge to spec trace
            assert forall|k: int| 0 <= k < p.relators[r].len() implies
                symbol_to_column(p.relators[r][k]) < 2 * rt.num_gens as nat
            by {
                assert(p.relators[r][k]
                    == crate::runtime::runtime_symbol_view(relators@[r]@[k]));
            }
            lemma_rt_trace_equals_spec_trace(*rt, c as nat, p.relators[r]);
        }
    }
    true
}

///  Todd-Coxeter coset enumeration.
///
///  Algorithm:
///    Outer loop (≤ max_cosets iterations, each adds one coset):
///      Phase 1: Saturate deductions by scanning all relators from all cosets.
///      Phase 2: Check completeness — if no UNDEF entries, return the table.
///      Phase 3: Define new coset at first UNDEF entry.
///
///  Returns None if max_cosets exceeded or a coincidence is found.
pub fn enumerate_cosets_exec(
    num_gens: usize,
    relators: &Vec<Vec<crate::runtime::RuntimeSymbol>>,
    max_cosets: usize,
) -> (out: Option<RuntimeCosetTable>)
    requires
        num_gens > 0,
        max_cosets > 0,
        max_cosets * (2 * num_gens + 1) < usize::MAX,
        forall|r: int, k: int| #![trigger relators@[r]@[k]]
            0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
    ensures
        out is Some ==> out.unwrap().num_cosets <= max_cosets,
        out is Some ==> coset_table_consistent(rt_to_spec_table(out.unwrap())),
        out is Some ==> coset_table_complete(rt_to_spec_table(out.unwrap())),
        out is Some ==> relator_closed(
            rt_to_spec_table(out.unwrap()),
            rt_presentation_view(num_gens, relators@),
        ),
        out is Some ==> rt_to_spec_table(out.unwrap()).num_gens
            == rt_presentation_view(num_gens, relators@).num_generators,
{
    proof { lemma_overflow_bounds(max_cosets, num_gens); }
    let num_cols: usize = 2 * num_gens;
    proof {
        assert(max_cosets * num_cols < usize::MAX) by(nonlinear_arith)
            requires num_cols == 2 * num_gens, max_cosets * 2 * num_gens < usize::MAX,
                num_gens >= 0int, max_cosets >= 0int;
    }
    let table_size: usize = max_cosets * num_cols;
    let mut table: Vec<usize> = Vec::new();

    //  Initialize table with UNDEF
    let mut init_i: usize = 0;
    while init_i < table_size
        invariant
            0 <= init_i <= table_size,
            table@.len() == init_i,
            table_size == max_cosets * num_cols,
            num_cols == 2 * num_gens,
            forall|j: int| #![trigger table@[j]]
                0 <= j < init_i ==> table@[j] == UNDEF(),
        decreases table_size - init_i,
    {
        table.push(usize::MAX);
        init_i = init_i + 1;
    }

    let mut rt = RuntimeCosetTable {
        num_cosets: 1,
        num_gens,
        table,
    };

    //  --- Outer loop: each iteration potentially adds one coset ---
    let mut outer_fuel: usize = max_cosets;
    while outer_fuel > 0
        invariant
            rt.num_cosets >= 1,
            rt.num_cosets <= max_cosets,
            rt.num_gens == num_gens,
            num_cols == 2 * num_gens,
            rt.table@.len() == table_size,
            table_size == max_cosets * num_cols,
            max_cosets * (2 * num_gens + 1) < usize::MAX,
            2 * num_gens < usize::MAX,
            max_cosets * 2 * num_gens < usize::MAX,
            num_gens > 0,
            forall|r: int, k: int| #![trigger relators@[r]@[k]]
                0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                    symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
            //  Flat array validity
            forall|j: int| #![trigger rt.table@[j]]
                0 <= j < rt.table@.len() ==>
                rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
        decreases outer_fuel,
    {
        //  === Phase 1: Saturate deductions ===
        let mut deduction_fuel: usize = max_cosets * num_cols;
        let mut any_progress = true;
        while any_progress && deduction_fuel > 0
            invariant
                rt.num_cosets >= 1,
                rt.num_cosets <= max_cosets,
                rt.num_gens == num_gens,
                num_cols == 2 * num_gens,
                rt.table@.len() == table_size,
                table_size == max_cosets * num_cols,
                max_cosets * (2 * num_gens + 1) < usize::MAX,
                2 * num_gens < usize::MAX,
                max_cosets * 2 * num_gens < usize::MAX,
                num_gens > 0,
                forall|r: int, k: int| #![trigger relators@[r]@[k]]
                    0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                        symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
                forall|j: int| #![trigger rt.table@[j]]
                    0 <= j < rt.table@.len() ==>
                    rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
            decreases deduction_fuel,
        {
            any_progress = false;
            let mut ri: usize = 0;
            while ri < relators.len()
                invariant
                    0 <= ri <= relators.len(),
                    rt.num_cosets >= 1,
                    rt.num_cosets <= max_cosets,
                    rt.num_gens == num_gens,
                    num_cols == 2 * num_gens,
                    rt.table@.len() == table_size,
                    table_size == max_cosets * num_cols,
                    max_cosets * (2 * num_gens + 1) < usize::MAX,
                    2 * num_gens < usize::MAX,
                    max_cosets * 2 * num_gens < usize::MAX,
                    num_gens > 0,
                    forall|r: int, k: int| #![trigger relators@[r]@[k]]
                        0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                            symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
                    forall|j: int| #![trigger rt.table@[j]]
                        0 <= j < rt.table@.len() ==>
                        rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
                decreases relators.len() - ri,
            {
                let mut ci: usize = 0;
                while ci < rt.num_cosets
                    invariant
                        0 <= ci <= rt.num_cosets,
                        0 <= ri < relators.len(),
                        rt.num_cosets >= 1,
                        rt.num_cosets <= max_cosets,
                        rt.num_gens == num_gens,
                        num_cols == 2 * num_gens,
                        rt.table@.len() == table_size,
                        table_size == max_cosets * num_cols,
                        max_cosets * (2 * num_gens + 1) < usize::MAX,
                        2 * num_gens < usize::MAX,
                        max_cosets * 2 * num_gens < usize::MAX,
                        num_gens > 0,
                        forall|r: int, k: int| #![trigger relators@[r]@[k]]
                            0 <= r < relators@.len() && 0 <= k < relators@[r]@.len() ==>
                                symbol_to_column(crate::runtime::runtime_symbol_view(relators@[r]@[k])) < 2 * num_gens,
                        forall|j: int| #![trigger rt.table@[j]]
                            0 <= j < rt.table@.len() ==>
                            rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets,
                    decreases rt.num_cosets - ci,
                {
                    proof {
                        assert(rt.num_cosets * (2 * rt.num_gens + 1) <= max_cosets * (2 * num_gens + 1)) by(nonlinear_arith)
                            requires rt.num_cosets <= max_cosets, rt.num_gens == num_gens, num_gens > 0int;
                        assert(rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens) by(nonlinear_arith)
                            requires
                                rt.table@.len() == table_size,
                                table_size == max_cosets * num_cols,
                                num_cols == 2 * num_gens,
                                rt.num_gens == num_gens,
                                rt.num_cosets <= max_cosets,
                                num_gens > 0int;
                    }
                    let result = scan_and_fill_exec(&mut rt, ci, &relators[ri]);
                    match result {
                        ScanResult::Deduction => { any_progress = true; },
                        ScanResult::Coincidence => { return None; },
                        _ => {},
                    }
                    ci = ci + 1;
                }
                ri = ri + 1;
            }
            deduction_fuel = deduction_fuel - 1;
        }

        //  === Phase 2: Check completeness ===
        let mut complete = true;
        let mut fc: usize = 0;
        let mut fcol: usize = 0;

        let mut sc: usize = 0;
        while sc < rt.num_cosets
            invariant
                0 <= sc <= rt.num_cosets,
                rt.num_cosets <= max_cosets,
                num_cols == 2 * num_gens,
                rt.table@.len() == table_size,
                table_size == max_cosets * num_cols,
                max_cosets * (2 * num_gens + 1) < usize::MAX,
                max_cosets * 2 * num_gens < usize::MAX,
                num_gens > 0,
                complete ==> true,
                !complete ==> fc < rt.num_cosets && fcol < num_cols,
            decreases rt.num_cosets - sc,
        {
            if !complete { break; }
            let mut scol: usize = 0;
            while scol < num_cols
                invariant
                    0 <= scol <= num_cols,
                    sc < rt.num_cosets,
                    rt.num_cosets <= max_cosets,
                    num_cols == 2 * num_gens,
                    rt.table@.len() == table_size,
                    table_size == max_cosets * num_cols,
                    max_cosets * (2 * num_gens + 1) < usize::MAX,
                    max_cosets * 2 * num_gens < usize::MAX,
                    num_gens > 0,
                    complete ==> true,
                    !complete ==> fc < rt.num_cosets && fcol < num_cols,
                decreases num_cols - scol,
            {
                if !complete { break; }
                proof {
                    assert(sc * num_cols + scol < max_cosets * num_cols) by(nonlinear_arith)
                        requires sc < max_cosets, scol < num_cols, num_cols > 0int;
                }
                let idx = sc * num_cols + scol;
                if rt.table[idx] == usize::MAX {
                    fc = sc;
                    fcol = scol;
                    complete = false;
                }
                scol = scol + 1;
            }
            sc = sc + 1;
        }

        if complete {
            //  Table is complete — verify before returning.
            proof {
                assert(rt.num_cosets * (2 * rt.num_gens + 1) <= max_cosets * (2 * num_gens + 1))
                    by(nonlinear_arith)
                    requires rt.num_cosets <= max_cosets, rt.num_gens == num_gens, num_gens > 0int;
                assert(rt.table@.len() >= rt.num_cosets * 2 * rt.num_gens) by(nonlinear_arith)
                    requires
                        rt.table@.len() == max_cosets * num_cols,
                        num_cols == 2 * num_gens,
                        rt.num_gens == num_gens,
                        rt.num_cosets <= max_cosets,
                        num_gens > 0int;
            }
            let complete_ok = check_rt_complete_exec(&rt);
            let consistent_ok = check_rt_consistent_exec(&rt);
            let relator_ok = check_rt_relator_closed_exec(&rt, relators);
            if !complete_ok || !consistent_ok || !relator_ok {
                return None;
            }
            return Some(rt);
        }

        //  === Phase 3: Define new coset ===
        if rt.num_cosets >= max_cosets {
            return None;
        }

        let new_coset = rt.num_cosets;
        proof {
            assert(fc * num_cols + fcol < max_cosets * num_cols) by(nonlinear_arith)
                requires fc < max_cosets, fcol < num_cols, num_cols > 0int;
        }
        let idx1 = fc * num_cols + fcol;
        rt.table.set(idx1, new_coset);

        //  Set inverse: table[new_coset][inv_col] = fc
        let inv_col: usize = if fcol % 2 == 0 { fcol + 1 } else { fcol - 1 };
        proof {
            assert(new_coset * num_cols + inv_col < max_cosets * num_cols) by(nonlinear_arith)
                requires new_coset < max_cosets, inv_col < num_cols, num_cols > 0int;
        }
        let idx2 = new_coset * num_cols + inv_col;
        rt.table.set(idx2, fc);

        rt.num_cosets = rt.num_cosets + 1;

        //  Prove flat array validity after adding new coset
        proof {
            //  new_coset == old num_cosets, so new_coset < new num_cosets
            //  fc < old num_cosets < new num_cosets
            assert forall|j: int| #![trigger rt.table@[j]]
                0 <= j < rt.table@.len() implies
                rt.table@[j] == UNDEF() || rt.table@[j] < rt.num_cosets
            by {
                if j == idx2 as int {
                    //  fc < old num_cosets < new num_cosets
                } else if j == idx1 as int {
                    //  new_coset == old num_cosets == new num_cosets - 1 < new num_cosets
                } else {
                    //  unchanged: was UNDEF or < old num_cosets <= new num_cosets
                }
            }
        }

        outer_fuel = outer_fuel - 1;
    }

    None
}

} //  verus!
