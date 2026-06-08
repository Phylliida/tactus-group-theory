use vstd::prelude::*;

verus! {

/// A symbol in a group word: either a generator or its formal inverse.
///
/// Generators are identified by natural numbers. A group with `n` generators
/// uses symbols `Gen(0)` through `Gen(n-1)` and their inverses.
#[derive(PartialEq, Eq)]
pub enum Symbol {
    Gen(nat),
    Inv(nat),
}

/// Returns the formal inverse of a symbol.
/// Gen(i) ↔ Inv(i).
pub open spec fn inverse_symbol(s: Symbol) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Inv(i),
        Symbol::Inv(i) => Symbol::Gen(i),
    }
}

/// Two symbols form an inverse pair (cancel each other).
pub open spec fn is_inverse_pair(s1: Symbol, s2: Symbol) -> bool {
    s2 == inverse_symbol(s1)
}

/// The generator index of a symbol.
pub open spec fn generator_index(s: Symbol) -> nat {
    match s {
        Symbol::Gen(i) => i,
        Symbol::Inv(i) => i,
    }
}

/// A symbol is valid for a group with `num_generators` generators.
pub open spec fn symbol_valid(s: Symbol, num_generators: nat) -> bool {
    generator_index(s) < num_generators
}

// --- Lemmas ---

/// Inverse is an involution: inv(inv(s)) == s.
pub proof fn lemma_inverse_involution(s: Symbol)
    ensures
        inverse_symbol(inverse_symbol(s)) == s,
{
}

/// Inverse pair is symmetric.
pub proof fn lemma_inverse_pair_symmetric(s1: Symbol, s2: Symbol)
    ensures
        is_inverse_pair(s1, s2) == is_inverse_pair(s2, s1),
{
    lemma_inverse_involution(s1);
}

/// A symbol is never its own inverse (Gen(i) != Inv(i)).
pub proof fn lemma_not_self_inverse(s: Symbol)
    ensures
        !is_inverse_pair(s, s),
{
}

/// Inverse preserves the generator index.
pub proof fn lemma_inverse_preserves_index(s: Symbol)
    ensures
        generator_index(inverse_symbol(s)) == generator_index(s),
{
}

/// Inverse preserves validity.
pub proof fn lemma_inverse_preserves_valid(s: Symbol, n: nat)
    ensures
        symbol_valid(s, n) == symbol_valid(inverse_symbol(s), n),
{
}

} // verus!
