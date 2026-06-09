use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::hnn::*;

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

//  ============================================================
//  B(M) as a tower of single-letter HNN steps
//  ============================================================
//
//  Every stable letter associates subgroups of the ORIGINAL A, so B(M) is the
//  iterated HNN extension  A → A∗r₀ → (A∗r₀)∗r₁ → …, one quadruple per level.
//  Level i adds stable letter Gen(3+i) carrying quadruple i's three associations.

//  B(M) restricted to the first i quadruples.
pub open spec fn b_m_upto(mm: ModMachine, i: nat) -> Presentation
    decreases i,
{
    if i == 0 {
        base_A()
    } else {
        hnn_presentation(HNNData {
            base: b_m_upto(mm, (i - 1) as nat),
            associations: quad_associations(mm.quads[(i - 1) as int], mm.m),
        })
    }
}

//  The full B(M): all quadruples folded in.
pub open spec fn b_m(mm: ModMachine) -> Presentation {
    b_m_upto(mm, mm.quads.len())
}

//  The tower adds exactly one generator per level: |gens| = 3 + i.
pub proof fn lemma_b_m_upto_num_generators(mm: ModMachine, i: nat)
    ensures
        b_m_upto(mm, i).num_generators == 3 + i,
    decreases i,
{
    if i == 0 {
    } else {
        lemma_b_m_upto_num_generators(mm, (i - 1) as nat);
    }
}

//  ---- Validity-preservation for a single HNN step (reusable infrastructure) ----

//  One HNN relator t⁻¹·a·t·b⁻¹ is valid over the extended generator set.
pub proof fn lemma_hnn_relator_valid(data: HNNData, j: int)
    requires
        hnn_data_valid(data),
        0 <= j < data.associations.len(),
    ensures
        word_valid(hnn_relator(data, j), data.base.num_generators + 1),
{
    let ng = data.base.num_generators;
    let (a, b) = data.associations[j];
    let p1 = Seq::new(1, |_k: int| stable_letter_inv(data));
    let p3 = Seq::new(1, |_k: int| stable_letter(data));
    assert(word_valid(p1, (ng + 1) as nat)) by {
        assert forall|q: int| 0 <= q < p1.len() implies symbol_valid(#[trigger] p1[q], (ng + 1) as nat)
        by { assert(p1[q] == Symbol::Inv(ng)); }
    }
    assert(word_valid(p3, (ng + 1) as nat)) by {
        assert forall|q: int| 0 <= q < p3.len() implies symbol_valid(#[trigger] p3[q], (ng + 1) as nat)
        by { assert(p3[q] == Symbol::Gen(ng)); }
    }
    lemma_word_valid_mono(a, ng, (ng + 1) as nat);
    lemma_inverse_word_valid(b, ng);
    lemma_word_valid_mono(inverse_word(b), ng, (ng + 1) as nat);
    lemma_concat_word_valid(p1, a, (ng + 1) as nat);
    lemma_concat_word_valid(p1 + a, p3, (ng + 1) as nat);
    lemma_concat_word_valid(p1 + a + p3, inverse_word(b), (ng + 1) as nat);
}

//  A single HNN step preserves presentation validity.
pub proof fn lemma_hnn_presentation_valid(data: HNNData)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(hnn_presentation(data)),
{
    reveal(presentation_valid);
    let hp = hnn_presentation(data);
    let ng = data.base.num_generators;
    let bl = data.base.relators.len();
    assert forall|i: int| 0 <= i < hp.relators.len()
        implies word_valid(#[trigger] hp.relators[i], hp.num_generators)
    by {
        if i < bl {
            assert(hp.relators[i] == data.base.relators[i]);
            lemma_word_valid_mono(data.base.relators[i], ng, (ng + 1) as nat);
        } else {
            assert(hp.relators[i] == hnn_relator(data, i - bl));
            lemma_hnn_relator_valid(data, i - bl);
        }
    }
}

//  B(M) up to level i is a valid presentation.
pub proof fn lemma_b_m_upto_valid(mm: ModMachine, i: nat)
    ensures
        presentation_valid(b_m_upto(mm, i)),
    decreases i,
{
    if i == 0 {
        lemma_base_A_valid();
    } else {
        let prev = b_m_upto(mm, (i - 1) as nat);
        let data = HNNData {
            base: prev,
            associations: quad_associations(mm.quads[(i - 1) as int], mm.m),
        };
        lemma_b_m_upto_valid(mm, (i - 1) as nat);
        lemma_b_m_upto_num_generators(mm, (i - 1) as nat);
        //  associations valid over prev.num_generators = 3 + (i-1) ≥ 3.
        lemma_quad_associations_valid(mm.quads[(i - 1) as int], mm.m, prev.num_generators);
        assert(hnn_data_valid(data));
        lemma_hnn_presentation_valid(data);
    }
}

//  The full B(M) is a valid presentation.
pub proof fn lemma_b_m_valid(mm: ModMachine)
    ensures
        presentation_valid(b_m(mm)),
{
    lemma_b_m_upto_valid(mm, mm.quads.len());
}

//  ============================================================
//  G(M): the finitely presented group
//  ============================================================
//
//  G(M) = ⟨ B(M), k | k commutes with t, r_i, l_j ⟩ — one more HNN step on top
//  of B(M) whose stable letter k = Gen(3+|quads|) has the IDENTITY isomorphism
//  on the subgroup ⟨t, r_i, l_j⟩ (each generator maps to itself: k⁻¹ g k = g).
//  The word-problem instance for a config (α,β) is the commutator [k, t(α,β)].

//  k's associations: t = Gen(0) and every stable letter Gen(3+i) maps to itself.
pub open spec fn g_m_associations(mm: ModMachine) -> Seq<(Word, Word)> {
    seq![ (seq![Symbol::Gen(0)], seq![Symbol::Gen(0)]) ]
    + Seq::new(mm.quads.len(), |i: int| {
        let g = Symbol::Gen((3 + i) as nat);
        (seq![g], seq![g])
    })
}

//  The finitely presented group G(M).
pub open spec fn g_m(mm: ModMachine) -> Presentation {
    hnn_presentation(HNNData { base: b_m(mm), associations: g_m_associations(mm) })
}

//  k's association words are all single generators valid over B(M)'s 3+|quads| gens.
pub proof fn lemma_g_m_associations_valid(mm: ModMachine)
    ensures
        forall|i: int| 0 <= i < g_m_associations(mm).len() ==> {
            &&& word_valid(#[trigger] g_m_associations(mm)[i].0, (3 + mm.quads.len()) as nat)
            &&& word_valid(g_m_associations(mm)[i].1, (3 + mm.quads.len()) as nat)
        },
{
    let nq = mm.quads.len();
    let assocs = g_m_associations(mm);
    let k = (3 + nq) as nat;
    assert forall|i: int| 0 <= i < assocs.len() implies {
        &&& word_valid(#[trigger] assocs[i].0, k)
        &&& word_valid(assocs[i].1, k)
    } by {
        if i == 0 {
            let w: Word = seq![Symbol::Gen(0)];
            assert(assocs[i].0 == w && assocs[i].1 == w);
            assert forall|q: int| 0 <= q < w.len() implies symbol_valid(#[trigger] w[q], k)
            by { assert(w[q] == Symbol::Gen(0)); }
        } else {
            let g = Symbol::Gen((3 + (i - 1)) as nat);
            let w: Word = seq![g];
            assert(assocs[i].0 == w && assocs[i].1 == w);
            assert forall|q: int| 0 <= q < w.len() implies symbol_valid(#[trigger] w[q], k)
            by { assert(w[q] == g); }
        }
    }
}

//  G(M) is a valid presentation. (It is finitely presented by construction:
//  finitely many generators 3+|quads|+1 and finitely many relators.)
pub proof fn lemma_g_m_valid(mm: ModMachine)
    ensures
        presentation_valid(g_m(mm)),
{
    lemma_b_m_valid(mm);
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
    lemma_g_m_associations_valid(mm);
    let data = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    assert(hnn_data_valid(data));
    lemma_hnn_presentation_valid(data);
}

//  G(M) has 4 + |quads| generators (t,x,y + one stable letter per quad + k).
pub proof fn lemma_g_m_num_generators(mm: ModMachine)
    ensures
        g_m(mm).num_generators == 4 + mm.quads.len(),
{
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
}

} //  verus!
