use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;

verus! {

//  ============================================================
//  The Aanderaa–Cohen machine group — Layer 1 (the foundation)
//  ============================================================
//
//  Faithful to docs/aanderaa-cohen-construction.md (Aanderaa & Cohen 1980).
//  This replaces a superseded, provably-wrong stub whose config word was
//  q_state·αᵃ·βᵇ.  The CORRECT object:
//
//    Base group   A = ⟨ t, x, y | xy = yx ⟩,    t=Gen(0), x=Gen(1), y=Gen(2)
//    Config word  t(r,s) = y⁻ˢ · x⁻ʳ · t · xʳ · yˢ     (a CONJUGATE of t)
//
//  A machine step is conjugation by a stable letter (built in later bricks);
//  a configuration is one element t carried to the coordinate (r,s), never a
//  heap of stacked symbols.

//  n copies of a single symbol.
pub open spec fn symbol_power(s: Symbol, n: nat) -> Word {
    Seq::new(n, |_i: int| s)
}

//  The base group A = ⟨t, x, y | xy = yx⟩: three generators, the single
//  relator [x, y] = x · y · x⁻¹ · y⁻¹.
pub open spec fn base_A() -> Presentation {
    Presentation {
        num_generators: 3,
        relators: seq![ seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)] ],
    }
}

//  The configuration word  t(r,s) = y⁻ˢ · x⁻ʳ · t · xʳ · yˢ.
pub open spec fn config_word(r: nat, s: nat) -> Word {
    symbol_power(Symbol::Inv(2), s)
        + symbol_power(Symbol::Inv(1), r)
        + seq![Symbol::Gen(0)]
        + symbol_power(Symbol::Gen(1), r)
        + symbol_power(Symbol::Gen(2), s)
}

//  ============================================================
//  Basic validity
//  ============================================================

//  A constant power is valid over k generators whenever the symbol is.
pub proof fn lemma_symbol_power_valid(s: Symbol, n: nat, k: nat)
    requires
        symbol_valid(s, k),
    ensures
        word_valid(symbol_power(s, n), k),
{
    assert forall|i: int| 0 <= i < symbol_power(s, n).len()
        implies symbol_valid(#[trigger] symbol_power(s, n)[i], k)
    by {
        assert(symbol_power(s, n)[i] == s);
    }
}

//  t(r,s) is a valid word over A's three generators.
pub proof fn lemma_config_word_valid(r: nat, s: nat)
    ensures
        word_valid(config_word(r, s), 3),
{
    let a = symbol_power(Symbol::Inv(2), s);
    let b = symbol_power(Symbol::Inv(1), r);
    let c: Word = seq![Symbol::Gen(0)];
    let d = symbol_power(Symbol::Gen(1), r);
    let e = symbol_power(Symbol::Gen(2), s);
    lemma_symbol_power_valid(Symbol::Inv(2), s, 3);
    lemma_symbol_power_valid(Symbol::Inv(1), r, 3);
    assert(word_valid(c, 3)) by {
        assert forall|i: int| 0 <= i < c.len() implies symbol_valid(#[trigger] c[i], 3)
        by { assert(c[i] == Symbol::Gen(0)); }
    }
    lemma_symbol_power_valid(Symbol::Gen(1), r, 3);
    lemma_symbol_power_valid(Symbol::Gen(2), s, 3);
    lemma_concat_word_valid(a, b, 3);
    lemma_concat_word_valid(a + b, c, 3);
    lemma_concat_word_valid(a + b + c, d, 3);
    lemma_concat_word_valid(a + b + c + d, e, 3);
}

//  base_A is a valid presentation.
pub proof fn lemma_base_A_valid()
    ensures
        presentation_valid(base_A()),
{
    reveal(presentation_valid);
    let p = base_A();
    assert forall|i: int| 0 <= i < p.relators.len()
        implies word_valid(#[trigger] p.relators[i], p.num_generators)
    by {
        assert(p.relators[i] == seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)]);
    }
}

} //  verus!
