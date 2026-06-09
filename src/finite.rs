use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::concrete::*;
use crate::abelianization::gen_word;
use crate::todd_coxeter::*;

verus! {

///  Every entry in the coset table is defined (no None entries).
#[verifier::opaque]
pub open spec fn coset_table_complete(t: CosetTable) -> bool {
    forall|c: int, col: int|
        0 <= c < t.num_cosets && 0 <= col < 2 * t.num_gens ==>
            (#[trigger] t.table[c][col]) is Some
}

///  A presentation defines a finite group of the given order if
///  there exists a valid, consistent, complete, relator-closed coset table with that many cosets.
pub open spec fn is_finite_of_order(p: Presentation, order: nat) -> bool {
    exists|t: CosetTable|
        coset_table_consistent(t)
        && coset_table_complete(t)
        && relator_closed(t, p)
        && t.num_cosets == order
        && t.num_gens == p.num_generators
}

///  A presentation is abelian if all generator pairs commute
///  (i.e., [g_i, g_j] ≡ ε for all i < j).
pub open spec fn is_abelian_presentation(p: Presentation) -> bool {
    forall|i: nat, j: nat|
        i < j && j < p.num_generators ==>
            equiv_in_presentation(p,
                concat(gen_word(i), gen_word(j)),
                concat(gen_word(j), gen_word(i)),
            )
}

///  A presentation is cyclic if it has 1 generator and finite order.
pub open spec fn is_cyclic_presentation(p: Presentation) -> bool {
    p.num_generators == 1
    && exists|n: nat| n > 0 && is_finite_of_order(p, n)
}

//  --- Lemmas ---

///  Z_n has order n (construct explicit coset table).
///
///  Table: n cosets, 1 generator.
///    table[c][Gen(0)] = (c + 1) % n
///    table[c][Inv(0)] = (c + n - 1) % n
pub proof fn lemma_cyclic_is_finite(n: nat)
    requires
        n > 0,
    ensures
        is_finite_of_order(cyclic_presentation(n), n),
{
    reveal(coset_table_wf);
    reveal(coset_table_consistent);
    reveal(coset_table_complete);
    reveal(relator_closed);
    let p = cyclic_presentation(n);

    //  Build the coset table
    let table_rows = Seq::new(n, |c: int| {
        Seq::new(2, |col: int| {
            if col == 0 {
                //  Gen(0): c → (c + 1) % n
                Some(((c + 1) % (n as int)) as nat)
            } else {
                //  Inv(0): c → (c + n - 1) % n
                Some(((c + (n as int) - 1) % (n as int)) as nat)
            }
        })
    });

    let t = CosetTable {
        num_cosets: n,
        num_gens: 1,
        table: table_rows,
    };

    //  Prove well-formedness
    assert(coset_table_wf(t)) by {
        assert(t.table.len() == n);
        assert forall|c: int| #![trigger t.table[c]]
            0 <= c < n implies t.table[c].len() == 2
        by {
            assert(t.table[c] == Seq::new(2, |col: int| {
                if col == 0 {
                    Some(((c + 1) % (n as int)) as nat)
                } else {
                    Some(((c + (n as int) - 1) % (n as int)) as nat)
                }
            }));
        }
        assert forall|c: int, col: int| #![trigger t.table[c][col]]
            0 <= c < n && 0 <= col < 2 implies
                match t.table[c][col] {
                    Some(d) => d < n,
                    None => true,
                }
        by {
            if col == 0 {
                assert(t.table[c][col] == Some(((c + 1) % (n as int)) as nat));
                assert(0 <= (c + 1) % (n as int) < n as int) by {
                    assert(n > 0);
                }
            } else {
                assert(t.table[c][col] == Some(((c + (n as int) - 1) % (n as int)) as nat));
                assert(0 <= (c + (n as int) - 1) % (n as int) < n as int) by {
                    assert(n > 0);
                }
            }
        }
    }

    //  Prove consistency: table[c][0] = d → table[d][1] = c
    assert(coset_table_consistent(t)) by {
        assert forall|c: int, col: int| #![trigger t.table[c][col]]
            0 <= c < n && 0 <= col < 2 implies
                match t.table[c][col] {
                    Some(d) => t.table[d as int][inverse_column(col as nat) as int] == Some(c as nat),
                    None => true,
                }
        by {
            if col == 0 {
                let d = ((c + 1) % (n as int)) as nat;
                //  table[d][1] = (d + n - 1) % n = ((c+1)%n + n - 1) % n
                //  Need: ((c+1)%n + n - 1) % n == c
                assert(inverse_column(0) == 1);
                assert(t.table[d as int][1] == Some(((d as int + (n as int) - 1) % (n as int)) as nat));
                assert(((d as int + (n as int) - 1) % (n as int)) as nat == c as nat) by {
                    assert(d == ((c + 1) % (n as int)) as nat);
                    assert(d as int == (c + 1) % (n as int));
                    assert((d as int + n as int - 1) % (n as int) == c % (n as int)) by(nonlinear_arith)
                        requires 0 <= c < n as int, n > 0, d as int == (c + 1) % (n as int),
                    {}
                    assert(c % (n as int) == c) by(nonlinear_arith)
                        requires 0 <= c < n as int, n > 0,
                    {}
                }
            } else {
                let d = ((c + (n as int) - 1) % (n as int)) as nat;
                assert(inverse_column(1) == 0);
                assert(t.table[d as int][0] == Some(((d as int + 1) % (n as int)) as nat));
                assert(((d as int + 1) % (n as int)) as nat == c as nat) by {
                    assert(d == ((c + (n as int) - 1) % (n as int)) as nat);
                    assert(d as int == (c + (n as int) - 1) % (n as int));
                    assert((d as int + 1) % (n as int) == c % (n as int)) by(nonlinear_arith)
                        requires 0 <= c < n as int, n > 0, d as int == (c + (n as int) - 1) % (n as int),
                    {}
                    assert(c % (n as int) == c) by(nonlinear_arith)
                        requires 0 <= c < n as int, n > 0,
                    {}
                }
            }
        }
    }

    //  Prove completeness: every entry is Some
    assert(coset_table_complete(t)) by {
        assert forall|c: int, col: int|
            0 <= c < n && 0 <= col < 2 implies
                (#[trigger] t.table[c][col]) is Some
        by {
            if col == 0 {
                assert(t.table[c][col] == Some(((c + 1) % (n as int)) as nat));
            } else {
                assert(t.table[c][col] == Some(((c + (n as int) - 1) % (n as int)) as nat));
            }
        }
    }

    //  Prove relator closure: relator is a^n = Gen(0)^n
    //  trace_word(t, c, a^n) traces c → c+1 → c+2 → ... → c+n ≡ c (mod n)
    assert(relator_closed(t, p)) by {
        assert forall|c: int, r: int| #![trigger t.table[c as int], p.relators[r]]
            0 <= c < n && 0 <= r < p.relators.len() implies
                trace_word(t, c as nat, p.relators[r]) == Some(c as nat)
        by {
            //  Only one relator: a^n
            assert(r == 0);
            let word = p.relators[0];
            assert(word == generator_power(0, n));
            lemma_trace_power(t, n, c as nat, n);
            //  trace gives Some(((c + n) % n) as nat), need (c + n) % n == c
            assert((c + n as int) % (n as int) == c) by(nonlinear_arith)
                requires 0 <= c < n as int, n > 0int;
        }
    }
}

///  Helper: tracing Gen(0)^k through the cyclic table from coset c gives (c + k) % n.
proof fn lemma_trace_power(t: CosetTable, n: nat, c: nat, k: nat)
    requires
        n > 0,
        c < n,
        t.num_cosets == n,
        t.num_gens == 1,
        t.table.len() == n,
        forall|ci: int| #![trigger t.table[ci]]
            0 <= ci < n ==> t.table[ci].len() == 2,
        forall|ci: int| #![trigger t.table[ci][0]]
            0 <= ci < n ==> t.table[ci][0] == Some(((ci + 1) % (n as int)) as nat),
    ensures
        trace_word(t, c, generator_power(0, k)) == Some(((c as int + k as int) % (n as int)) as nat),
    decreases k,
{
    if k == 0 {
        assert(generator_power(0, 0) =~= empty_word());
        assert(trace_word(t, c, empty_word()) == Some(c));
        assert(c == ((c as int + 0) % (n as int)) as nat) by(nonlinear_arith)
            requires 0 <= c < n, n > 0,
        {}
    } else {
        let w = generator_power(0, k);
        let rest = generator_power(0, (k - 1) as nat);
        //  w = [Gen(0)] ++ rest
        assert(w.len() > 0);
        assert(w.first() == Symbol::Gen(0));
        assert(w.drop_first() =~= rest);

        //  trace_word(t, c, w) = trace_word(t, table[c][0], rest)
        //  table[c][0] = (c + 1) % n
        let next = ((c as int + 1) % (n as int)) as nat;
        assert(t.table[c as int][0] == Some(next));
        assert(symbol_to_column(Symbol::Gen(0)) == 0);
        assert(next < n) by {
            assert(0 <= (c as int + 1) % (n as int) < n as int) by(nonlinear_arith)
                requires n > 0, 0 <= c < n,
            {}
        }

        lemma_trace_power(t, n, next, (k - 1) as nat);
        //  trace_word(t, next, rest) == Some(((next + k - 1) % n))
        //  ((next + k - 1) % n) == ((c + 1) % n + k - 1) % n == (c + k) % n

        assert(((next as int + (k - 1) as int) % (n as int)) as nat ==
               ((c as int + k as int) % (n as int)) as nat) by(nonlinear_arith)
            requires
                n > 0, 0 <= c < n, k >= 1,
                next as int == (c as int + 1) % (n as int),
        {}
    }
}

///  Z_n with n=1 is trivially abelian.
pub proof fn lemma_cyclic_is_abelian(n: nat)
    requires
        n > 0,
    ensures
        is_abelian_presentation(cyclic_presentation(n)),
{
    //  cyclic_presentation has 1 generator, so there are no pairs i < j < 1
    let p = cyclic_presentation(n);
    assert(p.num_generators == 1);
    //  Vacuously true: no i < j < 1 exist
}

///  Z_n is a cyclic presentation.
pub proof fn lemma_cyclic_is_cyclic(n: nat)
    requires
        n > 0,
    ensures
        is_cyclic_presentation(cyclic_presentation(n)),
{
    let p = cyclic_presentation(n);
    assert(p.num_generators == 1);
    lemma_cyclic_is_finite(n);
}

} //  verus!
