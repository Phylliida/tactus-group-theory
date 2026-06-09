use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::quotient::*;

verus! {

///  Generator power: Gen(i)^n as a word.
pub open spec fn generator_power(i: nat, n: nat) -> Word
    decreases n,
{
    if n == 0 {
        empty_word()
    } else {
        Seq::new(1, |_j: int| Symbol::Gen(i)) + generator_power(i, (n - 1) as nat)
    }
}

///  Cyclic group presentation Z_n = <a | a^n>.
pub open spec fn cyclic_presentation(n: nat) -> Presentation
    recommends n > 0,
{
    Presentation {
        num_generators: 1,
        relators: Seq::new(1, |_i: int| generator_power(0, n)),
    }
}

///  Dihedral group D_n = <r, s | r^n, s^2, (rs)^2>.
///  Generator 0 = r (rotation), Generator 1 = s (reflection).
pub open spec fn dihedral_presentation(n: nat) -> Presentation
    recommends n >= 2,
{
    let r_n = generator_power(0, n);
    let s_2 = generator_power(1, 2);
    //  (rs)^2 = rsrs
    let rs = Seq::new(1, |_i: int| Symbol::Gen(0)) + Seq::new(1, |_i: int| Symbol::Gen(1));
    let rs_2 = rs + rs;
    Presentation {
        num_generators: 2,
        relators: seq![r_n, s_2, rs_2],
    }
}

///  Free group presentation F_n = <x_1, ..., x_n | >.
pub open spec fn free_presentation(n: nat) -> Presentation {
    Presentation {
        num_generators: n,
        relators: Seq::empty(),
    }
}

//  --- Lemmas ---

///  generator_power has the expected length.
pub proof fn lemma_generator_power_len(i: nat, n: nat)
    ensures
        generator_power(i, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_generator_power_len(i, (n - 1) as nat);
    }
}

///  All symbols in generator_power are valid for a group with > i generators.
pub proof fn lemma_generator_power_valid(i: nat, n: nat, num_gens: nat)
    requires
        i < num_gens,
    ensures
        word_valid(generator_power(i, n), num_gens),
    decreases n,
{
    if n > 0 {
        lemma_generator_power_valid(i, (n - 1) as nat, num_gens);
        let w = generator_power(i, n);
        let prefix = Seq::new(1, |_j: int| Symbol::Gen(i));
        let rest = generator_power(i, (n - 1) as nat);
        assert(w =~= prefix + rest);
        assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], num_gens) by {
            if k == 0 {
                assert(w[0] == Symbol::Gen(i));
            } else {
                assert(w[k] == rest[k - 1]);
            }
        }
    }
}

///  Power addition: power(i, a+b) =~= concat(power(i,a), power(i,b)).
pub proof fn lemma_generator_power_add(i: nat, a: nat, b: nat)
    ensures
        generator_power(i, a + b) =~= concat(generator_power(i, a), generator_power(i, b)),
    decreases a,
{
    if a == 0 {
        assert(generator_power(i, 0) =~= empty_word());
        assert(concat(empty_word(), generator_power(i, b)) =~= generator_power(i, b));
    } else {
        let prefix = Seq::new(1, |_j: int| Symbol::Gen(i));
        //  power(i, a+b) = prefix + power(i, a+b-1)
        //  power(i, a) = prefix + power(i, a-1)
        //  concat(power(i, a), power(i, b)) = prefix + power(i, a-1) + power(i, b)
        //  By IH: power(i, (a-1)+b) =~= concat(power(i, a-1), power(i, b))
        lemma_generator_power_add(i, (a - 1) as nat, b);
        assert(((a - 1) + b) as nat == (a + b - 1) as nat);
        //  power(i, a+b) = prefix + power(i, a+b-1) =~= prefix + concat(power(i, a-1), power(i, b))
        //  concat(power(i, a), power(i, b)) = concat(prefix + power(i, a-1), power(i, b))
        //                                   = prefix + power(i, a-1) + power(i, b) (by assoc)
        lemma_concat_assoc(prefix, generator_power(i, (a - 1) as nat), generator_power(i, b));
    }
}

///  Z_n is a valid presentation.
pub proof fn lemma_cyclic_valid(n: nat)
    requires
        n > 0,
    ensures
        presentation_valid(cyclic_presentation(n)),
{
    reveal(presentation_valid);
    let p = cyclic_presentation(n);
    assert(p.relators.len() == 1);
    lemma_generator_power_valid(0, n, 1);
    assert(p.relators[0] == generator_power(0, n));
}

///  D_n is a valid presentation.
pub proof fn lemma_dihedral_valid(n: nat)
    requires
        n >= 2,
    ensures
        presentation_valid(dihedral_presentation(n)),
{
    reveal(presentation_valid);
    let p = dihedral_presentation(n);
    assert(p.relators.len() == 3);

    //  relator 0: r^n — all symbols are Gen(0)
    lemma_generator_power_valid(0, n, 2);

    //  relator 1: s^2 — all symbols are Gen(1)
    lemma_generator_power_valid(1, 2, 2);

    //  relator 2: (rs)^2 = rsrs — Gen(0) and Gen(1), both < 2
    let rs = Seq::new(1, |_i: int| Symbol::Gen(0)) + Seq::new(1, |_i: int| Symbol::Gen(1));
    let rs_2 = rs + rs;
    assert(p.relators[2] =~= rs_2);
    assert forall|k: int| 0 <= k < rs_2.len() implies symbol_valid(#[trigger] rs_2[k], 2) by {
        if k == 0 || k == 2 {
            assert(rs_2[k] == Symbol::Gen(0));
        } else {
            assert(rs_2[k] == Symbol::Gen(1));
        }
    }
}

///  Free group has no relators.
pub proof fn lemma_free_group_no_relators(n: nat)
    ensures
        free_presentation(n).relators.len() == 0,
        presentation_valid(free_presentation(n)),
{
    reveal(presentation_valid);
}

///  In Z_n, a^(kn) ≡ ε for any k >= 1.
pub proof fn lemma_cyclic_generator_order(n: nat, k: nat)
    requires
        n > 0,
        k >= 1,
    ensures
        equiv_in_presentation(cyclic_presentation(n), generator_power(0, k * n), empty_word()),
    decreases k,
{
    let p = cyclic_presentation(n);
    if k == 1 {
        assert(k * n == n) by(nonlinear_arith) requires k == 1nat, n > 0nat, {}
        //  a^n is the relator, so a^n ≡ ε
        assert(p.relators[0] == generator_power(0, n));
        lemma_relator_is_identity(p, 0);
    } else {
        //  a^(kn) = a^n · a^((k-1)n)
        //  a^n ≡ ε, and by IH a^((k-1)n) ≡ ε
        assert(k * n == n + (k - 1) * n) by(nonlinear_arith)
            requires k >= 2, n > 0,
        {}
        assert((k * n) as nat == (n + (k - 1) * n) as nat);
        lemma_generator_power_add(0, n, ((k - 1) * n) as nat);

        //  a^n ≡ ε
        lemma_relator_is_identity(p, 0);
        //  a^((k-1)n) ≡ ε
        lemma_cyclic_generator_order(n, (k - 1) as nat);
        //  concat(a^n, a^((k-1)n)) ≡ concat(ε, ε) = ε
        lemma_equiv_concat(p,
            generator_power(0, n), empty_word(),
            generator_power(0, ((k - 1) * n) as nat), empty_word(),
        );
        assert(concat(empty_word(), empty_word()) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
        lemma_equiv_transitive(p,
            concat(generator_power(0, n), generator_power(0, ((k - 1) * n) as nat)),
            concat(empty_word(), empty_word()),
            empty_word(),
        );
    }
}

///  In D_n, s^2 ≡ ε (reflection has order 2).
pub proof fn lemma_dihedral_reflection_order(n: nat)
    requires
        n >= 2,
    ensures
        equiv_in_presentation(dihedral_presentation(n), generator_power(1, 2), empty_word()),
{
    let p = dihedral_presentation(n);
    //  s^2 is relator at index 1
    assert(p.relators[1] == generator_power(1, 2));
    lemma_relator_is_identity(p, 1);
}

} //  verus!
