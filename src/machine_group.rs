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

//  ============================================================
//  The classic Aanderaa–Cohen modular machine (paper §1)
//  ============================================================
//
//  Config (α,β) ∈ N².  Write α = u·m + a, β = v·m + b  (a,b the residues mod m).
//  A quadruple (a,b,c,R) applies when (α mod m, β mod m) = (a,b):
//      R:  α' = u·m² + c,  β' = v
//      L:  α' = u,         β' = v·m² + c
//  At most one quadruple per residue pair (a,b).  H₀(M) = { (α,β) : (α,β) →* (0,0) }.

pub enum Dir { R, L }

pub struct Quad {
    pub a: nat,    //  residue of α  (0 ≤ a < m)
    pub b: nat,    //  residue of β  (0 ≤ b < m)
    pub c: nat,    //  0 ≤ c < m²
    pub dir: Dir,
}

pub struct ModMachine {
    pub m: nat,            //  modulus, > 1
    pub n: nat,            //  0 < n < m (used for input/output)
    pub quads: Seq<Quad>,
}

//  A quadruple matches a configuration: both residues agree.
pub open spec fn quad_matches(q: Quad, m: nat, alpha: nat, beta: nat) -> bool {
    alpha % m == q.a && beta % m == q.b
}

//  The configuration reached by applying one matching quadruple.
pub open spec fn quad_step(q: Quad, m: nat, alpha: nat, beta: nat) -> (nat, nat) {
    match q.dir {
        Dir::R => ((alpha / m) * (m * m) + q.c, beta / m),
        Dir::L => (alpha / m, (beta / m) * (m * m) + q.c),
    }
}

//  (α,β) is terminal: no quadruple matches its residue pair.
pub open spec fn mm_terminal(mm: ModMachine, alpha: nat, beta: nat) -> bool {
    forall|i: int| 0 <= i < mm.quads.len()
        ==> !quad_matches(#[trigger] mm.quads[i], mm.m, alpha, beta)
}

//  One-step yield (α,β) → (α',β').
pub open spec fn mm_yields(mm: ModMachine, alpha: nat, beta: nat, alpha2: nat, beta2: nat) -> bool {
    exists|i: int| 0 <= i < mm.quads.len()
        && quad_matches(#[trigger] mm.quads[i], mm.m, alpha, beta)
        && quad_step(mm.quads[i], mm.m, alpha, beta) == (alpha2, beta2)
}

//  Reachability in exactly k steps:  (a0,b0) →ᵏ (a1,b1).
pub open spec fn mm_reaches(
    mm: ModMachine, a0: nat, b0: nat, a1: nat, b1: nat, k: nat,
) -> bool
    decreases k,
{
    if k == 0 {
        a0 == a1 && b0 == b1
    } else {
        exists|am: nat, bm: nat|
            mm_yields(mm, a0, b0, am, bm)
            && mm_reaches(mm, am, bm, a1, b1, (k - 1) as nat)
    }
}

//  H₀(M): configurations that compute to the terminal origin (0,0).
pub open spec fn mm_in_H0(mm: ModMachine, alpha: nat, beta: nat) -> bool {
    mm_terminal(mm, 0, 0)
    && exists|k: nat| mm_reaches(mm, alpha, beta, 0, 0, k)
}

//  Well-formedness of a quadruple w.r.t. modulus m.
pub open spec fn quad_wf(q: Quad, m: nat) -> bool {
    q.a < m && q.b < m && q.c < m * m
}

//  Well-formed modular machine: m>1, 0<n<m, quads wf, and deterministic
//  (at most one quadruple per residue pair).
pub open spec fn mod_machine_wf(mm: ModMachine) -> bool {
    &&& mm.m > 1
    &&& 0 < mm.n < mm.m
    &&& (forall|i: int| 0 <= i < mm.quads.len() ==> quad_wf(#[trigger] mm.quads[i], mm.m))
    &&& (forall|i: int, j: int|
            0 <= i < mm.quads.len() && 0 <= j < mm.quads.len() && i != j
            && #[trigger] mm.quads[i].a == #[trigger] mm.quads[j].a
            && mm.quads[i].b == mm.quads[j].b
            ==> i == j)
}

//  ============================================================
//  The HNN encoding: stable-letter associations per quadruple
//  ============================================================
//
//  Each quadruple gets ONE stable letter conjugating a rank-3 subgroup of A.
//  An association pair (P, Q) means  stable⁻¹ · P · stable = Q.
//    R-quad (a,b,c):  t(a,b) ↦ t(c,0),   xᵐ ↦ xᵐ²,   yᵐ ↦ y
//    L-quad (a,b,c):  t(a,b) ↦ t(0,c),   xᵐ ↦ x,      yᵐ ↦ yᵐ²
//  The xᵐ/yᵐ relations are what telescope the residue conjugation to the FULL
//  config (the §3 computation in the construction doc).

pub open spec fn quad_associations(q: Quad, m: nat) -> Seq<(Word, Word)> {
    match q.dir {
        Dir::R => seq![
            (config_word(q.a, q.b), config_word(q.c, 0)),
            (symbol_power(Symbol::Gen(1), m), symbol_power(Symbol::Gen(1), m * m)),
            (symbol_power(Symbol::Gen(2), m), symbol_power(Symbol::Gen(2), 1)),
        ],
        Dir::L => seq![
            (config_word(q.a, q.b), config_word(0, q.c)),
            (symbol_power(Symbol::Gen(1), m), symbol_power(Symbol::Gen(1), 1)),
            (symbol_power(Symbol::Gen(2), m), symbol_power(Symbol::Gen(2), m * m)),
        ],
    }
}

//  word_valid is monotone in the generator count.
pub proof fn lemma_word_valid_mono(w: Word, a: nat, b: nat)
    requires
        word_valid(w, a),
        a <= b,
    ensures
        word_valid(w, b),
{
    assert forall|i: int| 0 <= i < w.len() implies symbol_valid(#[trigger] w[i], b)
    by {
        assert(symbol_valid(w[i], a));
    }
}

//  Every association word is valid over any base with at least 3 generators
//  (they only use t, x, y).
pub proof fn lemma_quad_associations_valid(q: Quad, m: nat, k: nat)
    requires
        k >= 3,
    ensures
        forall|i: int| 0 <= i < quad_associations(q, m).len() ==> {
            &&& word_valid(#[trigger] quad_associations(q, m)[i].0, k)
            &&& word_valid(quad_associations(q, m)[i].1, k)
        },
{
    //  config words: valid over 3, lift to k by monotonicity.
    lemma_config_word_valid(q.a, q.b);
    lemma_config_word_valid(q.c, 0);
    lemma_config_word_valid(0, q.c);
    lemma_word_valid_mono(config_word(q.a, q.b), 3, k);
    lemma_word_valid_mono(config_word(q.c, 0), 3, k);
    lemma_word_valid_mono(config_word(0, q.c), 3, k);
    //  x/y powers: x=Gen(1), y=Gen(2) are valid over k≥3 directly.
    lemma_symbol_power_valid(Symbol::Gen(1), m, k);
    lemma_symbol_power_valid(Symbol::Gen(1), m * m, k);
    lemma_symbol_power_valid(Symbol::Gen(1), 1, k);
    lemma_symbol_power_valid(Symbol::Gen(2), m, k);
    lemma_symbol_power_valid(Symbol::Gen(2), m * m, k);
    lemma_symbol_power_valid(Symbol::Gen(2), 1, k);
}

} //  verus!
