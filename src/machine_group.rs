use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::reduction::*;
use crate::hnn::*;
use crate::benign::{apply_embedding, apply_embedding_symbol,
    lemma_apply_embedding_concat, lemma_apply_embedding_symbol_inverse,
    lemma_apply_embedding_inverse, lemma_apply_embedding_valid};
use crate::normal_form_afp_textbook::lemma_equiv_inverse;
use crate::britton_via_tower::lemma_insert_equiv_empty;
use crate::britton_via_tower::lemma_delete_equiv_empty;
use crate::britton_via_tower::{britton_lemma_full, has_pinch, has_pinch_at,
    has_adjacent_opposite_at, is_stable, has_stable_letter};
use crate::benign::{in_generated_subgroup, concat_all, lemma_concat_all_singleton, lemma_concat_all_empty, is_generator_or_inverse, factors_from_generators};
use crate::free_product::{free_product, shift_relators, shift_word, shift_symbol};

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

//  The stable letter k = Gen(3+|quads|), and "k commutes with w" in G(M).
pub open spec fn k_gen(mm: ModMachine) -> Symbol {
    Symbol::Gen((3 + mm.quads.len()) as nat)
}

pub open spec fn k_commutes(mm: ModMachine, w: Word) -> bool {
    equiv_in_presentation(g_m(mm), seq![k_gen(mm)] + w, w + seq![k_gen(mm)])
}

//  k commutes with t (= Gen(0)), from g_m_associations[0] = (t,t).
pub proof fn lemma_k_commutes_t(mm: ModMachine)
    ensures
        k_commutes(mm, seq![Symbol::Gen(0)]),
{
    let gdata = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    let p = g_m(mm);
    let kk = k_gen(mm);
    let ki = Symbol::Inv((3 + mm.quads.len()) as nat);
    let t: Word = seq![Symbol::Gen(0)];
    lemma_b_m_valid(mm);
    lemma_g_m_associations_valid(mm);
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
    assert(hnn_data_valid(gdata));
    lemma_g_m_valid(mm);
    lemma_g_m_num_generators(mm);
    assert(gdata.associations[0] == (t, t));
    assert(stable_letter(gdata) == kk && stable_letter_inv(gdata) == ki);
    lemma_hnn_conjugation(gdata, 0);
    assert(Seq::new(1, |_j: int| ki) =~= seq![ki]);
    assert(Seq::new(1, |_j: int| kk) =~= seq![kk]);
    assert(equiv_in_presentation(p, seq![ki] + t + seq![kk], t));
    assert(symbol_valid(kk, p.num_generators));
    assert(word_valid(t, p.num_generators)) by {
        assert forall|i: int| 0 <= i < t.len() implies symbol_valid(#[trigger] t[i], p.num_generators) by { }
    }
    lemma_commute_from_conj(p, kk, ki, t);
}

//  k commutes with Inv(3+qi) (invert the stable conjugation relation).
pub proof fn lemma_k_commutes_stable_inv(mm: ModMachine, qi: nat)
    requires
        qi < mm.quads.len(),
    ensures
        k_commutes(mm, seq![Symbol::Inv((3 + qi) as nat)]),
{
    let gdata = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    let p = g_m(mm);
    let kk = k_gen(mm);
    let ki = Symbol::Inv((3 + mm.quads.len()) as nat);
    let g = Symbol::Gen((3 + qi) as nat);
    let gi = Symbol::Inv((3 + qi) as nat);
    let s: Word = seq![g];
    let sgi: Word = seq![gi];
    let kiw: Word = seq![ki];
    let kkw: Word = seq![kk];
    lemma_b_m_valid(mm);
    lemma_g_m_associations_valid(mm);
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
    assert(hnn_data_valid(gdata));
    lemma_g_m_valid(mm);
    lemma_g_m_num_generators(mm);
    let ng = p.num_generators;
    assert(gdata.associations[(1 + qi) as int] == (s, s));
    assert(stable_letter(gdata) == kk && stable_letter_inv(gdata) == ki);
    lemma_hnn_conjugation(gdata, (1 + qi) as int);
    assert(Seq::new(1, |_j: int| ki) =~= seq![ki]);
    assert(Seq::new(1, |_j: int| kk) =~= seq![kk]);
    let conj_g: Word = kiw + s + kkw;
    assert(equiv_in_presentation(p, conj_g, s));
    //  validity
    assert(symbol_valid(kk, ng) && symbol_valid(g, ng) && symbol_valid(gi, ng));
    assert(word_valid(s, ng)) by { assert forall|i: int| 0 <= i < s.len() implies symbol_valid(#[trigger] s[i], ng) by { } }
    assert(word_valid(sgi, ng)) by { assert forall|i: int| 0 <= i < sgi.len() implies symbol_valid(#[trigger] sgi[i], ng) by { } }
    assert(word_valid(kiw, ng)) by { assert forall|i: int| 0 <= i < kiw.len() implies symbol_valid(#[trigger] kiw[i], ng) by { } }
    assert(word_valid(kkw, ng)) by { assert forall|i: int| 0 <= i < kkw.len() implies symbol_valid(#[trigger] kkw[i], ng) by { } }
    lemma_concat_word_valid(kiw, s, ng);
    lemma_concat_word_valid(kiw + s, kkw, ng);
    //  invert the relation
    lemma_equiv_inverse(p, conj_g, s);
    let conj_gi: Word = kiw + sgi + kkw;
    lemma_inverse_word_concat(kiw + s, kkw);
    lemma_inverse_word_concat(kiw, s);
    lemma_inverse_word_one(kk);
    lemma_inverse_word_one(ki);
    lemma_inverse_word_one(g);
    assert(inverse_symbol(kk) == ki && inverse_symbol(ki) == kk && inverse_symbol(g) == gi);
    assert(inverse_word(conj_g) =~= conj_gi);
    assert(inverse_word(s) =~= sgi);
    assert(equiv_in_presentation(p, conj_gi, sgi));
    lemma_commute_from_conj(p, kk, ki, sgi);
}

//  Commuting with k is closed under products.
pub proof fn lemma_k_commutes_product(mm: ModMachine, x: Word, y: Word)
    requires
        k_commutes(mm, x),
        k_commutes(mm, y),
    ensures
        k_commutes(mm, x + y),
{
    let p = g_m(mm);
    let kk = k_gen(mm);
    lemma_equiv_concat_left(p, seq![kk] + x, x + seq![kk], y);
    lemma_equiv_concat_right(p, x, seq![kk] + y, y + seq![kk]);
    assert((x + seq![kk]) + y == x + (seq![kk] + y));
    lemma_equiv_transitive(p, (seq![kk] + x) + y, (x + seq![kk]) + y, x + (y + seq![kk]));
    assert(seq![kk] + (x + y) == (seq![kk] + x) + y);
    assert(x + (y + seq![kk]) == (x + y) + seq![kk]);
}

//  Commuting with k respects equivalence.
pub proof fn lemma_k_commutes_respects_equiv(mm: ModMachine, x: Word, y: Word)
    requires
        k_commutes(mm, x),
        equiv_in_presentation(g_m(mm), x, y),
        word_valid(x, g_m(mm).num_generators),
        presentation_valid(g_m(mm)),
    ensures
        k_commutes(mm, y),
{
    let p = g_m(mm);
    let kk = k_gen(mm);
    lemma_equiv_symmetric(p, x, y);                       //  y ~ x
    lemma_equiv_concat_right(p, seq![kk], y, x);          //  k·y ~ k·x
    lemma_equiv_concat_left(p, x, y, seq![kk]);           //  x·k ~ y·k
    lemma_equiv_transitive(p, seq![kk] + y, seq![kk] + x, x + seq![kk]);
    lemma_equiv_transitive(p, seq![kk] + y, x + seq![kk], y + seq![kk]);
}

//  k commutes with the stable letter Gen(3+qi), from g_m_associations[1+qi].
pub proof fn lemma_k_commutes_stable(mm: ModMachine, qi: nat)
    requires
        qi < mm.quads.len(),
    ensures
        k_commutes(mm, seq![Symbol::Gen((3 + qi) as nat)]),
{
    let gdata = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    let p = g_m(mm);
    let kk = k_gen(mm);
    let ki = Symbol::Inv((3 + mm.quads.len()) as nat);
    let s: Word = seq![Symbol::Gen((3 + qi) as nat)];
    lemma_b_m_valid(mm);
    lemma_g_m_associations_valid(mm);
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
    assert(hnn_data_valid(gdata));
    lemma_g_m_valid(mm);
    lemma_g_m_num_generators(mm);
    assert(gdata.associations[(1 + qi) as int] == (s, s));
    assert(stable_letter(gdata) == kk && stable_letter_inv(gdata) == ki);
    lemma_hnn_conjugation(gdata, (1 + qi) as int);
    assert(Seq::new(1, |_j: int| ki) =~= seq![ki]);
    assert(Seq::new(1, |_j: int| kk) =~= seq![kk]);
    assert(equiv_in_presentation(p, seq![ki] + s + seq![kk], s));
    assert(symbol_valid(kk, p.num_generators));
    assert(word_valid(s, p.num_generators)) by {
        assert forall|i: int| 0 <= i < s.len() implies symbol_valid(#[trigger] s[i], p.num_generators) by { }
    }
    lemma_commute_from_conj(p, kk, ki, s);
}

//  ============================================================
//  Obligation C, foundation: commutativity of x and y in A
//  ============================================================
//
//  In A only x,y commute (t does NOT), so this is derived from the SPECIFIC
//  relator [x,y] = x·y·x⁻¹·y⁻¹ — not abelianization (which would make t commute
//  too).  The keystone:  x·y ~ y·x.

//  The word x·y·x⁻¹·y⁻¹·y·x freely reduces to x·y (cancel y⁻¹y then x⁻¹x).
proof fn lemma_comm_reduces()
    ensures
        reduces_to(
            seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2),
                 Symbol::Gen(2), Symbol::Gen(1)],
            seq![Symbol::Gen(1), Symbol::Gen(2)],
        ),
{
    let x = Symbol::Gen(1); let y = Symbol::Gen(2);
    let xi = Symbol::Inv(1); let yi = Symbol::Inv(2);
    let w0: Word = seq![x, y, xi, yi, y, x];
    let w1: Word = seq![x, y, xi, x];
    let w2: Word = seq![x, y];
    //  w0 → w1 : cancel the (yi, y) pair at position 3.
    assert(has_cancellation_at(w0, 3)) by {
        assert(w0[3] == yi && w0[4] == y);
        assert(is_inverse_pair(yi, y));
    }
    assert(reduce_at(w0, 3) =~= w1) by {
        assert(w0.subrange(0, 3) =~= seq![x, y, xi]);
        assert(w0.subrange(5, 6) =~= seq![x]);
    }
    assert(reduces_one_step(w0, w1)) by {
        assert(has_cancellation_at(w0, 3) && w1 == reduce_at(w0, 3));
    }
    //  w1 → w2 : cancel the (xi, x) pair at position 2.
    assert(has_cancellation_at(w1, 2)) by {
        assert(w1[2] == xi && w1[3] == x);
        assert(is_inverse_pair(xi, x));
    }
    assert(reduce_at(w1, 2) =~= w2) by {
        assert(w1.subrange(0, 2) =~= seq![x, y]);
        assert(w1.subrange(4, 4) =~= Seq::<Symbol>::empty());
    }
    assert(reduces_one_step(w1, w2)) by {
        assert(has_cancellation_at(w1, 2) && w2 == reduce_at(w1, 2));
    }
    //  assemble the 2-step reduction.
    assert(reduces_in_steps(w2, w2, 0));
    assert(reduces_in_steps(w1, w2, 1)) by {
        assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, w2, 0));
    }
    assert(reduces_in_steps(w0, w2, 2)) by {
        assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, w2, 1));
    }
    assert(reduces_to(w0, w2)) by {
        assert(reduces_in_steps(w0, w2, 2));
    }
}

//  ---- Power-word identities (pure Seq facts) ----

//  symbol_power(s, 1) is the singleton [s].
pub proof fn lemma_symbol_power_one(s: Symbol)
    ensures
        symbol_power(s, 1) =~= seq![s],
{
}

//  Powers of the same symbol concatenate by adding exponents.
pub proof fn lemma_symbol_power_merge(s: Symbol, a: nat, b: nat)
    ensures
        symbol_power(s, a) + symbol_power(s, b) =~= symbol_power(s, (a + b) as nat),
{
}

//  A single symbol u commuting with w lifts to commuting with every power wᵠ.
//  General over (p, u, w) so it serves all four x/y sign combinations.
pub proof fn lemma_sym_commutes_power(p: Presentation, u: Symbol, w: Symbol, q: nat)
    requires
        equiv_in_presentation(p, seq![u, w], seq![w, u]),
    ensures
        equiv_in_presentation(p, seq![u] + symbol_power(w, q), symbol_power(w, q) + seq![u]),
    decreases q,
{
    if q == 0 {
        assert(seq![u] + symbol_power(w, 0) =~= seq![u]);
        assert(symbol_power(w, 0) + seq![u] =~= seq![u]);
        lemma_equiv_refl(p, seq![u]);
    } else {
        let k = (q - 1) as nat;
        let wk = symbol_power(w, k);
        let wq = symbol_power(w, q);
        let uw: Word = seq![u, w];
        let wu: Word = seq![w, u];
        //  front split  wq =~= [w] + wk
        lemma_symbol_power_merge(w, 1, k);
        lemma_symbol_power_one(w);
        assert(wq =~= seq![w] + wk);
        //  IH:  [u] + wk ~ wk + [u]
        lemma_sym_commutes_power(p, u, w, k);
        //  step 1:  uw + wk ~ wu + wk
        lemma_equiv_concat_left(p, uw, wu, wk);
        //  step 2:  [w] + ([u] + wk) ~ [w] + (wk + [u])
        lemma_equiv_concat_right(p, seq![w], seq![u] + wk, wk + seq![u]);
        //  align endpoints by =~= and chain
        assert(seq![u] + wq =~= concat(uw, wk));
        assert(concat(wu, wk) =~= seq![w] + (seq![u] + wk));
        assert(seq![w] + (wk + seq![u]) =~= wq + seq![u]);
        assert(seq![u] + wq == concat(uw, wk));
        lemma_equiv_transitive(p, concat(uw, wk), concat(wu, wk), wq + seq![u]);
    }
}

//  Full power commutativity: uᵖ commutes with wᵠ given u·w ~ w·u.
pub proof fn lemma_power_commutes(p: Presentation, u: Symbol, w: Symbol, pp: nat, qq: nat)
    requires
        equiv_in_presentation(p, seq![u, w], seq![w, u]),
    ensures
        equiv_in_presentation(
            p,
            symbol_power(u, pp) + symbol_power(w, qq),
            symbol_power(w, qq) + symbol_power(u, pp),
        ),
    decreases pp,
{
    let wqq = symbol_power(w, qq);
    if pp == 0 {
        assert(symbol_power(u, 0) + wqq =~= wqq);
        assert(wqq + symbol_power(u, 0) =~= wqq);
        lemma_equiv_refl(p, wqq);
    } else {
        let j = (pp - 1) as nat;
        let uj = symbol_power(u, j);
        let upp = symbol_power(u, pp);
        lemma_symbol_power_merge(u, 1, j);
        lemma_symbol_power_one(u);
        assert(upp =~= seq![u] + uj);
        //  IH:  uⱼ·wqq ~ wqq·uⱼ
        lemma_power_commutes(p, u, w, j, qq);
        //  equiv1:  [u]·(uⱼ·wqq) ~ [u]·(wqq·uⱼ)
        lemma_equiv_concat_right(p, seq![u], uj + wqq, wqq + uj);
        //  [u]·wqq ~ wqq·[u]
        lemma_sym_commutes_power(p, u, w, qq);
        //  equiv2:  ([u]·wqq)·uⱼ ~ (wqq·[u])·uⱼ
        lemma_equiv_concat_left(p, seq![u] + wqq, wqq + seq![u], uj);
        //  bridge equiv1.RHS == equiv2.LHS, then chain
        assert(seq![u] + (wqq + uj) == (seq![u] + wqq) + uj);
        lemma_equiv_transitive(p, seq![u] + (uj + wqq), seq![u] + (wqq + uj), (wqq + seq![u]) + uj);
        //  align endpoints A == equiv1.LHS,  equiv2.RHS == F
        assert(upp + wqq == seq![u] + (uj + wqq));
        assert((wqq + seq![u]) + uj == wqq + upp);
    }
}

//  x·y ~ y·x in A.
pub proof fn lemma_xy_commute_in_A()
    ensures
        equiv_in_presentation(
            base_A(),
            seq![Symbol::Gen(1), Symbol::Gen(2)],
            seq![Symbol::Gen(2), Symbol::Gen(1)],
        ),
{
    let a = base_A();
    let x = Symbol::Gen(1); let y = Symbol::Gen(2);
    let xi = Symbol::Inv(1); let yi = Symbol::Inv(2);
    let xy: Word = seq![x, y];
    let yx: Word = seq![y, x];
    let r: Word = seq![x, y, xi, yi];
    let r_yx: Word = seq![x, y, xi, yi, y, x];
    assert(a.relators[0] == r);
    //  R ~ ε   (relator is identity; w = ε).
    lemma_conjugate_relator_is_identity(a, empty_word(), 0);
    assert(concat(concat(empty_word(), a.relators[0]), inverse_word(empty_word())) =~= r) by {
        assert(inverse_word(empty_word()) =~= empty_word());
    }
    assert(equiv_in_presentation(a, r, empty_word()));
    //  append yx:  R·yx ~ ε·yx = yx.
    lemma_equiv_concat_left(a, r, empty_word(), yx);
    assert(concat(r, yx) =~= r_yx);
    assert(concat(empty_word(), yx) =~= yx);
    assert(equiv_in_presentation(a, r_yx, yx));
    //  R·yx freely reduces to xy.
    lemma_comm_reduces();
    lemma_reduces_to_equiv(a, r_yx, xy);
    //  xy ~ R·yx ~ yx.
    lemma_base_A_valid();
    assert(word_valid(r_yx, 3)) by {
        assert forall|i: int| 0 <= i < r_yx.len() implies symbol_valid(#[trigger] r_yx[i], 3) by {}
    }
    lemma_equiv_symmetric(a, r_yx, xy);
    lemma_equiv_transitive(a, xy, r_yx, yx);
}

//  inverse_word distributes (reversing) over concatenation.
pub proof fn lemma_inverse_word_concat(a: Word, b: Word)
    ensures
        inverse_word(a + b) =~= inverse_word(b) + inverse_word(a),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(inverse_word(a) =~= empty_word());
    } else {
        reveal_with_fuel(inverse_word, 1);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        assert((a + b).first() == a.first());
        lemma_inverse_word_concat(a.drop_first(), b);
    }
}

//  inverse_word of a power inverts the symbol.
pub proof fn lemma_inverse_word_sympower(s: Symbol, n: nat)
    ensures
        inverse_word(symbol_power(s, n)) =~= symbol_power(inverse_symbol(s), n),
    decreases n,
{
    if n == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
        assert(symbol_power(inverse_symbol(s), 0) =~= empty_word());
    } else {
        let k = (n - 1) as nat;
        //  symbol_power(s, n) =~= seq![s] + symbol_power(s, k)
        lemma_symbol_power_merge(s, 1, k);
        lemma_symbol_power_one(s);
        assert(symbol_power(s, n) =~= seq![s] + symbol_power(s, k));
        lemma_inverse_word_concat(seq![s], symbol_power(s, k));
        lemma_inverse_word_sympower(s, k);
        //  inverse_word(seq![s]) =~= seq![inverse_symbol(s)]
        reveal_with_fuel(inverse_word, 2);
        assert(seq![s].drop_first() =~= empty_word());
        //  refold:  sp(inv,k) + [inv] =~= sp(inv, n)
        lemma_symbol_power_merge(inverse_symbol(s), k, 1);
        lemma_symbol_power_one(inverse_symbol(s));
    }
}

//  inverse_word of a singleton.
pub proof fn lemma_inverse_word_one(s: Symbol)
    ensures
        inverse_word(seq![s]) =~= seq![inverse_symbol(s)],
{
    reveal_with_fuel(inverse_word, 2);
    assert(seq![s].drop_first() =~= empty_word());
}

//  inverse_word of a two-symbol word (reverses and inverts).
pub proof fn lemma_inverse_word_two(s1: Symbol, s2: Symbol)
    ensures
        inverse_word(seq![s1, s2]) =~= seq![inverse_symbol(s2), inverse_symbol(s1)],
{
    reveal_with_fuel(inverse_word, 3);
    assert(seq![s1, s2].drop_first() =~= seq![s2]);
    assert(seq![s2].drop_first() =~= empty_word());
}

//  ============================================================
//  Obligation C: the config decomposition
//    t(um+a, vm+b) ~ (yᵐ)⁻ᵛ(xᵐ)⁻ᵘ · t(a,b) · (xᵐ)ᵘ(yᵐ)ᵛ
//  ============================================================

//  The intermediate split form (config word with every power broken into its
//  m-multiple and residue parts, residues adjacent to the centre).
pub open spec fn w_mid_word(u: nat, a: nat, v: nat, b: nat, m: nat) -> Word {
    symbol_power(Symbol::Inv(2), v * m) + symbol_power(Symbol::Inv(2), b)
        + symbol_power(Symbol::Inv(1), u * m) + symbol_power(Symbol::Inv(1), a)
        + seq![Symbol::Gen(0)]
        + symbol_power(Symbol::Gen(1), a) + symbol_power(Symbol::Gen(1), u * m)
        + symbol_power(Symbol::Gen(2), b) + symbol_power(Symbol::Gen(2), v * m)
}

//  The decomposition target:  (yᵐ)⁻ᵛ(xᵐ)⁻ᵘ · t(a,b) · (xᵐ)ᵘ(yᵐ)ᵛ.
pub open spec fn config_target(u: nat, a: nat, v: nat, b: nat, m: nat) -> Word {
    symbol_power(Symbol::Inv(2), v * m) + symbol_power(Symbol::Inv(1), u * m)
        + config_word(a, b)
        + symbol_power(Symbol::Gen(1), u * m) + symbol_power(Symbol::Gen(2), v * m)
}

//  Phase 1: config_word(um+a, vm+b) equals W_mid as a word (four power merges).
pub proof fn lemma_config_eq_wmid(u: nat, a: nat, v: nat, b: nat, m: nat)
    ensures
        config_word((u * m + a) as nat, (v * m + b) as nat) =~= w_mid_word(u, a, v, b, m),
{
    let i2 = Symbol::Inv(2); let i1 = Symbol::Inv(1);
    let g0 = Symbol::Gen(0); let g1 = Symbol::Gen(1); let g2 = Symbol::Gen(2);
    lemma_symbol_power_merge(i2, v * m, b);   //  i2^vm · i2^b == i2^(vm+b)
    lemma_symbol_power_merge(i1, u * m, a);   //  i1^um · i1^a == i1^(um+a)
    lemma_symbol_power_merge(g1, a, u * m);   //  g1^a · g1^um == g1^(a+um) = g1^(um+a)
    lemma_symbol_power_merge(g2, b, v * m);   //  g2^b · g2^vm == g2^(b+vm) = g2^(vm+b)
    //  config_word unfolds to the merged 5-segment form; substitute each power,
    //  then the result re-associates to W_mid.
    let sub: Word =
        (symbol_power(i2, v * m) + symbol_power(i2, b))
        + (symbol_power(i1, u * m) + symbol_power(i1, a))
        + seq![g0]
        + (symbol_power(g1, a) + symbol_power(g1, u * m))
        + (symbol_power(g2, b) + symbol_power(g2, v * m));
    assert(config_word((u * m + a) as nat, (v * m + b) as nat) == sub);
    assert(sub =~= w_mid_word(u, a, v, b, m));
}

//  Phase 2: W_mid ~ TARGET via two commutation swaps.
//  swap1 moves i2^b past i1^um; swap2 moves g1^um past g2^b.
pub proof fn lemma_wmid_to_target(u: nat, a: nat, v: nat, b: nat, m: nat)
    ensures
        equiv_in_presentation(base_A(), w_mid_word(u, a, v, b, m), config_target(u, a, v, b, m)),
{
    let p = base_A();
    let i2 = Symbol::Inv(2); let i1 = Symbol::Inv(1);
    let g0 = Symbol::Gen(0); let g1 = Symbol::Gen(1); let g2 = Symbol::Gen(2);
    //  --- swap 1:  i2^b · i1^um  ~  i1^um · i2^b ---
    let p1 = symbol_power(i2, v * m);
    let m1a = symbol_power(i2, b) + symbol_power(i1, u * m);
    let m1b = symbol_power(i1, u * m) + symbol_power(i2, b);
    let s1 = symbol_power(i1, a) + seq![g0] + symbol_power(g1, a)
        + symbol_power(g1, u * m) + symbol_power(g2, b) + symbol_power(g2, v * m);
    lemma_xinv_yinv_commute_in_A();
    lemma_power_commutes(p, i2, i1, b, u * m);              //  equiv(p, m1a, m1b)
    lemma_equiv_concat_left(p, m1a, m1b, s1);              //  m1a·s1 ~ m1b·s1
    lemma_equiv_concat_right(p, p1, m1a + s1, m1b + s1);   //  p1·(m1a·s1) ~ p1·(m1b·s1)
    assert(w_mid_word(u, a, v, b, m) =~= p1 + (m1a + s1));
    //  --- swap 2:  g1^um · g2^b  ~  g2^b · g1^um ---
    let p2 = symbol_power(i2, v * m) + symbol_power(i1, u * m) + symbol_power(i2, b)
        + symbol_power(i1, a) + seq![g0] + symbol_power(g1, a);
    let m2a = symbol_power(g1, u * m) + symbol_power(g2, b);
    let m2b = symbol_power(g2, b) + symbol_power(g1, u * m);
    let s2 = symbol_power(g2, v * m);
    lemma_xy_commute_in_A();
    lemma_power_commutes(p, g1, g2, u * m, b);              //  equiv(p, m2a, m2b)
    lemma_equiv_concat_left(p, m2a, m2b, s2);
    lemma_equiv_concat_right(p, p2, m2a + s2, m2b + s2);    //  p2·(m2a·s2) ~ p2·(m2b·s2)
    //  bridges: align the two swap stages and the final target
    assert(p1 + (m1b + s1) == p2 + (m2a + s2));
    assert(p2 + (m2b + s2) =~= config_target(u, a, v, b, m));
    //  chain:  W_mid ~ p1·(m1b·s1) = p2·(m2a·s2) ~ p2·(m2b·s2) = TARGET
    lemma_equiv_transitive(p, w_mid_word(u, a, v, b, m), p2 + (m2a + s2), p2 + (m2b + s2));
}

//  The single-letter HNN extension of A carrying one R-quadruple's relations.
pub open spec fn r_step_data(a: nat, b: nat, c: nat, m: nat) -> HNNData {
    HNNData { base: base_A(), associations: quad_associations(Quad { a, b, c, dir: Dir::R }, m) }
}

//  Validity of a conjugated power [Inv(ng)]·sᵏ·[Gen(ng)] over ng+1 generators.
pub proof fn lemma_conj_word_valid(s: Symbol, k: nat, ng: nat)
    requires
        symbol_valid(s, ng),
    ensures
        word_valid(seq![Symbol::Inv(ng)] + symbol_power(s, k) + seq![Symbol::Gen(ng)], (ng + 1) as nat),
{
    let ri: Word = seq![Symbol::Inv(ng)];
    let rsw: Word = seq![Symbol::Gen(ng)];
    assert(symbol_valid(s, (ng + 1) as nat));
    assert(word_valid(ri, (ng + 1) as nat)) by {
        assert forall|i: int| 0 <= i < ri.len() implies symbol_valid(#[trigger] ri[i], (ng + 1) as nat)
        by { assert(ri[i] == Symbol::Inv(ng)); }
    }
    assert(word_valid(rsw, (ng + 1) as nat)) by {
        assert forall|i: int| 0 <= i < rsw.len() implies symbol_valid(#[trigger] rsw[i], (ng + 1) as nat)
        by { assert(rsw[i] == Symbol::Gen(ng)); }
    }
    lemma_symbol_power_valid(s, k, (ng + 1) as nat);
    lemma_concat_word_valid(ri, symbol_power(s, k), (ng + 1) as nat);
    lemma_concat_word_valid(ri + symbol_power(s, k), rsw, (ng + 1) as nat);
}

//  Conjugate the decomposed config target by the R-stable-letter, term by term.
//  Generic over any base presentation p_base (so it works at every tower level).
pub proof fn lemma_conj_config_target(p_base: Presentation, n: nat, u: nat, a: nat, v: nat, b: nat, c: nat, m: nat)
    requires
        presentation_valid(p_base),
        p_base.num_generators == n,
        n >= 3,
    ensures
        equiv_in_presentation(
            hnn_presentation(HNNData { base: p_base, associations: quad_associations(Quad { a, b, c, dir: Dir::R }, m) }),
            seq![Symbol::Inv(n)] + config_target(u, a, v, b, m) + seq![Symbol::Gen(n)],
            recompose_target(u, v, c, m),
        ),
{
    let q = Quad { a, b, c, dir: Dir::R };
    let data = HNNData { base: p_base, associations: quad_associations(q, m) };
    let p = hnn_presentation(data);
    let rs = Symbol::Gen(n);
    let ri = Symbol::Inv(n);
    let i1 = Symbol::Inv(1); let i2 = Symbol::Inv(2);
    let g1 = Symbol::Gen(1); let g2 = Symbol::Gen(2);
    //  --- validity & structure ---
    lemma_quad_associations_valid(q, m, n);
    assert(hnn_data_valid(data));
    lemma_hnn_presentation_valid(data);
    assert(p.num_generators == n + 1);
    assert(symbol_valid(g1, n) && symbol_valid(g2, n));
    let pair: Word = seq![rs, ri];
    assert(word_valid(pair, (n + 1) as nat)) by {
        assert forall|i: int| 0 <= i < pair.len() implies symbol_valid(#[trigger] pair[i], (n + 1) as nat)
        by { }
    }
    assert(is_inverse_pair(rs, ri));
    assert(stable_letter(data) == rs && stable_letter_inv(data) == ri);
    assert(data.associations[0] == (config_word(a, b), config_word(c, 0)));
    assert(data.associations[1] == (symbol_power(g1, m), symbol_power(g1, (m * m) as nat)));
    assert(data.associations[2] == (symbol_power(g2, m), symbol_power(g2, 1)));
    assert(v * m == m * v) by (nonlinear_arith);
    assert(u * m == m * u) by (nonlinear_arith);
    //  --- the three base relations (bridge Seq::new(1,..) =~= seq![..]) ---
    lemma_hnn_conjugation(data, 0);
    lemma_hnn_conjugation(data, 1);
    lemma_hnn_conjugation(data, 2);
    assert(Seq::new(1, |_j: int| ri) =~= seq![ri]);
    assert(Seq::new(1, |_j: int| rs) =~= seq![rs]);
    //  base: conj(cw(a,b)) ~ cw(c,0);  conj(g1^m) ~ g1^m²;  conj(g2^m) ~ g2^1
    assert(equiv_in_presentation(p, seq![ri] + config_word(a, b) + seq![rs], config_word(c, 0)));
    assert(equiv_in_presentation(p, seq![ri] + symbol_power(g1, m) + seq![rs], symbol_power(g1, (m * m) as nat)));
    assert(equiv_in_presentation(p, seq![ri] + symbol_power(g2, m) + seq![rs], symbol_power(g2, 1)));
    //  --- inverse base relations for i1, i2 ---
    lemma_conj_word_valid(g1, m, n);
    lemma_conj_word_valid(g2, m, n);
    assert(word_valid(symbol_power(g1, (m * m) as nat), (n + 1) as nat)) by { lemma_symbol_power_valid(g1, (m * m) as nat, (n + 1) as nat); }
    assert(word_valid(symbol_power(g2, 1), (n + 1) as nat)) by { lemma_symbol_power_valid(g2, 1, (n + 1) as nat); }
    lemma_conj_base_inverse(p, rs, ri, g1, g1, m, (m * m) as nat);  //  conj(i1^m) ~ i1^m²
    lemma_conj_base_inverse(p, rs, ri, g2, g2, m, 1);              //  conj(i2^m) ~ i2^1
    assert(inverse_symbol(g1) == i1 && inverse_symbol(g2) == i2);
    //  --- the five per-term conjugations  conj(Ai) ~ Bi ---
    lemma_conj_sympower(p, rs, ri, i2, i2, m, 1, v);          //  conj(i2^{mv}) ~ i2^v
    lemma_conj_sympower(p, rs, ri, i1, i1, m, (m * m) as nat, u);  //  conj(i1^{mu}) ~ i1^{m²u}
    lemma_conj_sympower(p, rs, ri, g1, g1, m, (m * m) as nat, u);  //  conj(g1^{mu}) ~ g1^{m²u}
    lemma_conj_sympower(p, rs, ri, g2, g2, m, 1, v);          //  conj(g2^{mv}) ~ g2^v
    //  the Ai/Bi
    let a1 = symbol_power(i2, (v * m) as nat); let b1 = symbol_power(i2, v);
    let a2 = symbol_power(i1, (u * m) as nat); let b2 = symbol_power(i1, (m * m * u) as nat);
    let a3 = config_word(a, b);                let b3 = config_word(c, 0);
    let a4 = symbol_power(g1, (u * m) as nat); let b4 = symbol_power(g1, (m * m * u) as nat);
    let a5 = symbol_power(g2, (v * m) as nat); let b5 = symbol_power(g2, v);
    //  reconcile exponents (m·v = v·m etc.) so conj(Ai) ~ Bi in the Ai/Bi names
    assert(equiv_in_presentation(p, seq![ri] + a1 + seq![rs], b1));
    assert(equiv_in_presentation(p, seq![ri] + a2 + seq![rs], b2));
    assert(equiv_in_presentation(p, seq![ri] + a3 + seq![rs], b3));
    assert(equiv_in_presentation(p, seq![ri] + a4 + seq![rs], b4));
    assert(equiv_in_presentation(p, seq![ri] + a5 + seq![rs], b5));
    //  --- distribute conj over A1·A2·A3·A4·A5 and replace each term ---
    let conj = |w: Word| seq![ri] + w + seq![rs];
    //  e1: conj(a1·a2) ~ b1·b2
    lemma_conj_distributes(p, ri, rs, a1, a2);
    lemma_equiv_concat_left(p, seq![ri] + a1 + seq![rs], b1, seq![ri] + a2 + seq![rs]);
    lemma_equiv_concat_right(p, b1, seq![ri] + a2 + seq![rs], b2);
    lemma_equiv_transitive(p, seq![ri] + (a1 + a2) + seq![rs],
        (seq![ri] + a1 + seq![rs]) + (seq![ri] + a2 + seq![rs]), b1 + (seq![ri] + a2 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + (a1 + a2) + seq![rs], b1 + (seq![ri] + a2 + seq![rs]), b1 + b2);
    //  e2: conj((a1·a2)·a3) ~ (b1·b2)·b3
    lemma_conj_distributes(p, ri, rs, a1 + a2, a3);
    lemma_equiv_concat_left(p, seq![ri] + (a1 + a2) + seq![rs], b1 + b2, seq![ri] + a3 + seq![rs]);
    lemma_equiv_concat_right(p, b1 + b2, seq![ri] + a3 + seq![rs], b3);
    lemma_equiv_transitive(p, seq![ri] + ((a1 + a2) + a3) + seq![rs],
        (seq![ri] + (a1 + a2) + seq![rs]) + (seq![ri] + a3 + seq![rs]),
        (b1 + b2) + (seq![ri] + a3 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + ((a1 + a2) + a3) + seq![rs],
        (b1 + b2) + (seq![ri] + a3 + seq![rs]), (b1 + b2) + b3);
    //  e3: conj(((a1·a2)·a3)·a4) ~ ((b1·b2)·b3)·b4
    lemma_conj_distributes(p, ri, rs, (a1 + a2) + a3, a4);
    lemma_equiv_concat_left(p, seq![ri] + ((a1 + a2) + a3) + seq![rs], (b1 + b2) + b3, seq![ri] + a4 + seq![rs]);
    lemma_equiv_concat_right(p, (b1 + b2) + b3, seq![ri] + a4 + seq![rs], b4);
    lemma_equiv_transitive(p, seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs],
        (seq![ri] + ((a1 + a2) + a3) + seq![rs]) + (seq![ri] + a4 + seq![rs]),
        ((b1 + b2) + b3) + (seq![ri] + a4 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs],
        ((b1 + b2) + b3) + (seq![ri] + a4 + seq![rs]), ((b1 + b2) + b3) + b4);
    //  e4: conj((((a1·a2)·a3)·a4)·a5) ~ (((b1·b2)·b3)·b4)·b5
    lemma_conj_distributes(p, ri, rs, ((a1 + a2) + a3) + a4, a5);
    lemma_equiv_concat_left(p, seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs], ((b1 + b2) + b3) + b4, seq![ri] + a5 + seq![rs]);
    lemma_equiv_concat_right(p, ((b1 + b2) + b3) + b4, seq![ri] + a5 + seq![rs], b5);
    lemma_equiv_transitive(p, seq![ri] + ((((a1 + a2) + a3) + a4) + a5) + seq![rs],
        (seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs]) + (seq![ri] + a5 + seq![rs]),
        (((b1 + b2) + b3) + b4) + (seq![ri] + a5 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + ((((a1 + a2) + a3) + a4) + a5) + seq![rs],
        (((b1 + b2) + b3) + b4) + (seq![ri] + a5 + seq![rs]), (((b1 + b2) + b3) + b4) + b5);
    //  config_target = a1·a2·a3·a4·a5  and  recompose_target = b1·b2·b3·b4·b5
    assert(config_target(u, a, v, b, m) == ((((a1 + a2) + a3) + a4) + a5));
    assert(recompose_target(u, v, c, m) =~= (((b1 + b2) + b3) + b4) + b5);
}

//  The single-letter HNN extension of A carrying one L-quadruple's relations.
pub open spec fn l_step_data(a: nat, b: nat, c: nat, m: nat) -> HNNData {
    HNNData { base: base_A(), associations: quad_associations(Quad { a, b, c, dir: Dir::L }, m) }
}

//  Conjugate the decomposed config target by the L-stable-letter.  The result is
//  itself a config_target (with modulus 1), so the recompose reuses decomposition.
//  L scalings:  x^m ↦ x,  y^m ↦ y²,  t(a,b) ↦ t(0,c).
pub proof fn lemma_conj_config_target_L(p_base: Presentation, n: nat, u: nat, a: nat, v: nat, b: nat, c: nat, m: nat)
    requires
        presentation_valid(p_base),
        p_base.num_generators == n,
        n >= 3,
    ensures
        equiv_in_presentation(
            hnn_presentation(HNNData { base: p_base, associations: quad_associations(Quad { a, b, c, dir: Dir::L }, m) }),
            seq![Symbol::Inv(n)] + config_target(u, a, v, b, m) + seq![Symbol::Gen(n)],
            config_target(u, 0, (m * m * v) as nat, c, 1),
        ),
{
    let q = Quad { a, b, c, dir: Dir::L };
    let data = HNNData { base: p_base, associations: quad_associations(q, m) };
    let p = hnn_presentation(data);
    let rs = Symbol::Gen(n);
    let ri = Symbol::Inv(n);
    let i1 = Symbol::Inv(1); let i2 = Symbol::Inv(2);
    let g1 = Symbol::Gen(1); let g2 = Symbol::Gen(2);
    lemma_quad_associations_valid(q, m, n);
    assert(hnn_data_valid(data));
    lemma_hnn_presentation_valid(data);
    assert(p.num_generators == n + 1);
    assert(symbol_valid(g1, n) && symbol_valid(g2, n));
    let pair: Word = seq![rs, ri];
    assert(word_valid(pair, (n + 1) as nat)) by {
        assert forall|i: int| 0 <= i < pair.len() implies symbol_valid(#[trigger] pair[i], (n + 1) as nat) by { }
    }
    assert(is_inverse_pair(rs, ri));
    assert(stable_letter(data) == rs && stable_letter_inv(data) == ri);
    assert(data.associations[0] == (config_word(a, b), config_word(0, c)));
    assert(data.associations[1] == (symbol_power(g1, m), symbol_power(g1, 1)));
    assert(data.associations[2] == (symbol_power(g2, m), symbol_power(g2, (m * m) as nat)));
    assert(v * m == m * v) by (nonlinear_arith);
    assert(u * m == m * u) by (nonlinear_arith);
    lemma_hnn_conjugation(data, 0);
    lemma_hnn_conjugation(data, 1);
    lemma_hnn_conjugation(data, 2);
    assert(Seq::new(1, |_j: int| ri) =~= seq![ri]);
    assert(Seq::new(1, |_j: int| rs) =~= seq![rs]);
    assert(equiv_in_presentation(p, seq![ri] + config_word(a, b) + seq![rs], config_word(0, c)));
    assert(equiv_in_presentation(p, seq![ri] + symbol_power(g1, m) + seq![rs], symbol_power(g1, 1)));
    assert(equiv_in_presentation(p, seq![ri] + symbol_power(g2, m) + seq![rs], symbol_power(g2, (m * m) as nat)));
    lemma_conj_word_valid(g1, m, n);
    lemma_conj_word_valid(g2, m, n);
    assert(word_valid(symbol_power(g1, 1), (n + 1) as nat)) by { lemma_symbol_power_valid(g1, 1, (n + 1) as nat); }
    assert(word_valid(symbol_power(g2, (m * m) as nat), (n + 1) as nat)) by { lemma_symbol_power_valid(g2, (m * m) as nat, (n + 1) as nat); }
    lemma_conj_base_inverse(p, rs, ri, g1, g1, m, 1);              //  conj(i1^m) ~ i1^1
    lemma_conj_base_inverse(p, rs, ri, g2, g2, m, (m * m) as nat); //  conj(i2^m) ~ i2^m²
    assert(inverse_symbol(g1) == i1 && inverse_symbol(g2) == i2);
    lemma_conj_sympower(p, rs, ri, i2, i2, m, (m * m) as nat, v);  //  conj(i2^{mv}) ~ i2^{m²v}
    lemma_conj_sympower(p, rs, ri, i1, i1, m, 1, u);              //  conj(i1^{mu}) ~ i1^u
    lemma_conj_sympower(p, rs, ri, g1, g1, m, 1, u);             //  conj(g1^{mu}) ~ g1^u
    lemma_conj_sympower(p, rs, ri, g2, g2, m, (m * m) as nat, v); //  conj(g2^{mv}) ~ g2^{m²v}
    let a1 = symbol_power(i2, (v * m) as nat); let b1 = symbol_power(i2, (m * m * v) as nat);
    let a2 = symbol_power(i1, (u * m) as nat); let b2 = symbol_power(i1, u);
    let a3 = config_word(a, b);                let b3 = config_word(0, c);
    let a4 = symbol_power(g1, (u * m) as nat); let b4 = symbol_power(g1, u);
    let a5 = symbol_power(g2, (v * m) as nat); let b5 = symbol_power(g2, (m * m * v) as nat);
    assert(equiv_in_presentation(p, seq![ri] + a1 + seq![rs], b1));
    assert(equiv_in_presentation(p, seq![ri] + a2 + seq![rs], b2));
    assert(equiv_in_presentation(p, seq![ri] + a3 + seq![rs], b3));
    assert(equiv_in_presentation(p, seq![ri] + a4 + seq![rs], b4));
    assert(equiv_in_presentation(p, seq![ri] + a5 + seq![rs], b5));
    //  distribute (identical chain to the R case)
    lemma_conj_distributes(p, ri, rs, a1, a2);
    lemma_equiv_concat_left(p, seq![ri] + a1 + seq![rs], b1, seq![ri] + a2 + seq![rs]);
    lemma_equiv_concat_right(p, b1, seq![ri] + a2 + seq![rs], b2);
    lemma_equiv_transitive(p, seq![ri] + (a1 + a2) + seq![rs],
        (seq![ri] + a1 + seq![rs]) + (seq![ri] + a2 + seq![rs]), b1 + (seq![ri] + a2 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + (a1 + a2) + seq![rs], b1 + (seq![ri] + a2 + seq![rs]), b1 + b2);
    lemma_conj_distributes(p, ri, rs, a1 + a2, a3);
    lemma_equiv_concat_left(p, seq![ri] + (a1 + a2) + seq![rs], b1 + b2, seq![ri] + a3 + seq![rs]);
    lemma_equiv_concat_right(p, b1 + b2, seq![ri] + a3 + seq![rs], b3);
    lemma_equiv_transitive(p, seq![ri] + ((a1 + a2) + a3) + seq![rs],
        (seq![ri] + (a1 + a2) + seq![rs]) + (seq![ri] + a3 + seq![rs]),
        (b1 + b2) + (seq![ri] + a3 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + ((a1 + a2) + a3) + seq![rs],
        (b1 + b2) + (seq![ri] + a3 + seq![rs]), (b1 + b2) + b3);
    lemma_conj_distributes(p, ri, rs, (a1 + a2) + a3, a4);
    lemma_equiv_concat_left(p, seq![ri] + ((a1 + a2) + a3) + seq![rs], (b1 + b2) + b3, seq![ri] + a4 + seq![rs]);
    lemma_equiv_concat_right(p, (b1 + b2) + b3, seq![ri] + a4 + seq![rs], b4);
    lemma_equiv_transitive(p, seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs],
        (seq![ri] + ((a1 + a2) + a3) + seq![rs]) + (seq![ri] + a4 + seq![rs]),
        ((b1 + b2) + b3) + (seq![ri] + a4 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs],
        ((b1 + b2) + b3) + (seq![ri] + a4 + seq![rs]), ((b1 + b2) + b3) + b4);
    lemma_conj_distributes(p, ri, rs, ((a1 + a2) + a3) + a4, a5);
    lemma_equiv_concat_left(p, seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs], ((b1 + b2) + b3) + b4, seq![ri] + a5 + seq![rs]);
    lemma_equiv_concat_right(p, ((b1 + b2) + b3) + b4, seq![ri] + a5 + seq![rs], b5);
    lemma_equiv_transitive(p, seq![ri] + ((((a1 + a2) + a3) + a4) + a5) + seq![rs],
        (seq![ri] + (((a1 + a2) + a3) + a4) + seq![rs]) + (seq![ri] + a5 + seq![rs]),
        (((b1 + b2) + b3) + b4) + (seq![ri] + a5 + seq![rs]));
    lemma_equiv_transitive(p, seq![ri] + ((((a1 + a2) + a3) + a4) + a5) + seq![rs],
        (((b1 + b2) + b3) + b4) + (seq![ri] + a5 + seq![rs]), (((b1 + b2) + b3) + b4) + b5);
    assert(config_target(u, a, v, b, m) == ((((a1 + a2) + a3) + a4) + a5));
    assert(config_target(u, 0, (m * m * v) as nat, c, 1) =~= (((b1 + b2) + b3) + b4) + b5);
}

//  The full decomposition (Phase 1 ∘ Phase 2).
pub proof fn lemma_config_decompose(u: nat, a: nat, v: nat, b: nat, m: nat)
    ensures
        equiv_in_presentation(
            base_A(),
            config_word((u * m + a) as nat, (v * m + b) as nat),
            config_target(u, a, v, b, m),
        ),
{
    lemma_config_eq_wmid(u, a, v, b, m);
    lemma_wmid_to_target(u, a, v, b, m);
}

//  The conjugated form of config_target by an R-stable-letter:
//    y⁻ᵛ · x⁻ᵘᵐ² · t(c,0) · xᵘᵐ² · yᵛ.
pub open spec fn recompose_target(u: nat, v: nat, c: nat, m: nat) -> Word {
    symbol_power(Symbol::Inv(2), v) + symbol_power(Symbol::Inv(1), (m * m * u) as nat)
        + config_word(c, 0)
        + symbol_power(Symbol::Gen(1), (m * m * u) as nat) + symbol_power(Symbol::Gen(2), v)
}

//  The recompose collapses (two x-power merges) to config_word(um²+c, v).
pub proof fn lemma_recompose(u: nat, v: nat, c: nat, m: nat)
    ensures
        recompose_target(u, v, c, m) =~= config_word((u * m * m + c) as nat, v),
{
    let i2 = Symbol::Inv(2); let i1 = Symbol::Inv(1);
    let g0 = Symbol::Gen(0); let g1 = Symbol::Gen(1); let g2 = Symbol::Gen(2);
    let mmu = (m * m * u) as nat;
    let ap = (u * m * m + c) as nat;
    assert(m * m * u == u * m * m) by (nonlinear_arith);
    assert(mmu + c == ap);
    assert(c + mmu == ap);
    lemma_symbol_power_merge(i1, mmu, c);   //  i1^mmu · i1^c =~= i1^(mmu+c) = i1^ap
    lemma_symbol_power_merge(g1, c, mmu);   //  g1^c · g1^mmu =~= g1^(c+mmu) = g1^ap
    //  config_word(c,0) flattens (i2^0, g2^0 empty)
    let cw: Word = symbol_power(i1, c) + seq![g0] + symbol_power(g1, c);
    assert(config_word(c, 0) =~= cw);
    //  substitute, then merge, then refold into config_word(ap, v)
    let sub: Word = symbol_power(i2, v) + symbol_power(i1, mmu)
        + cw + symbol_power(g1, mmu) + symbol_power(g2, v);
    assert(recompose_target(u, v, c, m) == sub);
    assert(sub =~= config_word(ap, v));
}

//  ============================================================
//  THE FORWARD STEP (obligation C):  r⁻¹ · t(α,β) · r ~ t(α',β')
//  for an R-quadruple, where α=um+a, β=vm+b, α'=um²+c, β'=v.
//  ============================================================
pub proof fn lemma_forward_step_R(u: nat, a: nat, v: nat, b: nat, c: nat, m: nat)
    ensures
        equiv_in_presentation(
            hnn_presentation(r_step_data(a, b, c, m)),
            seq![Symbol::Inv(3)] + config_word((u * m + a) as nat, (v * m + b) as nat) + seq![Symbol::Gen(3)],
            config_word((u * m * m + c) as nat, v),
        ),
{
    let data = r_step_data(a, b, c, m);
    let p = hnn_presentation(data);
    let rs = Symbol::Gen(3);
    let ri = Symbol::Inv(3);
    let cw = config_word((u * m + a) as nat, (v * m + b) as nat);
    let ct = config_target(u, a, v, b, m);
    //  decomposition (in base_A), lifted to p
    lemma_config_decompose(u, a, v, b, m);
    lemma_base_embeds_in_hnn(data, cw, ct);
    //  wrap in r⁻¹ … r
    lemma_equiv_concat_left(p, cw, ct, seq![rs]);
    lemma_equiv_concat_right(p, seq![ri], cw + seq![rs], ct + seq![rs]);
    assert(seq![ri] + cw + seq![rs] == seq![ri] + (cw + seq![rs]));
    assert(seq![ri] + ct + seq![rs] == seq![ri] + (ct + seq![rs]));
    //  conjugate the decomposed target, then recompose
    lemma_base_A_valid();
    lemma_conj_config_target(base_A(), 3, u, a, v, b, c, m);
    lemma_recompose(u, v, c, m);
    lemma_equiv_transitive(p, seq![ri] + cw + seq![rs], seq![ri] + ct + seq![rs],
        recompose_target(u, v, c, m));
}

//  The L recompose reuses the decomposition: config_target(u,0,m²v,c,1) is exactly
//  the decomposition of config_word(u, m²v+c).
pub proof fn lemma_recompose_L(u: nat, v: nat, c: nat, m: nat)
    ensures
        equiv_in_presentation(
            base_A(),
            config_target(u, 0, (m * m * v) as nat, c, 1),
            config_word(u, (v * m * m + c) as nat),
        ),
{
    let x = config_word((u * 1 + 0) as nat, ((m * m * v) * 1 + c) as nat);
    let y = config_target(u, 0, (m * m * v) as nat, c, 1);
    lemma_config_decompose(u, 0, (m * m * v) as nat, c, 1);   //  equiv(base_A, x, y)
    lemma_base_A_valid();
    lemma_config_word_valid((u * 1 + 0) as nat, ((m * m * v) * 1 + c) as nat);
    lemma_equiv_symmetric(base_A(), x, y);                     //  equiv(base_A, y, x)
    assert(m * m * v + c == v * m * m + c) by (nonlinear_arith);
    assert(x == config_word(u, (v * m * m + c) as nat));
}

//  ============================================================
//  THE FORWARD STEP for an L-quadruple:  l⁻¹ · t(α,β) · l ~ t(α',β')
//  where α=um+a, β=vm+b, α'=u, β'=vm²+c.
//  ============================================================
pub proof fn lemma_forward_step_L(u: nat, a: nat, v: nat, b: nat, c: nat, m: nat)
    ensures
        equiv_in_presentation(
            hnn_presentation(l_step_data(a, b, c, m)),
            seq![Symbol::Inv(3)] + config_word((u * m + a) as nat, (v * m + b) as nat) + seq![Symbol::Gen(3)],
            config_word(u, (v * m * m + c) as nat),
        ),
{
    let data = l_step_data(a, b, c, m);
    let p = hnn_presentation(data);
    let rs = Symbol::Gen(3);
    let ri = Symbol::Inv(3);
    let cw = config_word((u * m + a) as nat, (v * m + b) as nat);
    let ct = config_target(u, a, v, b, m);
    let rt = config_target(u, 0, (m * m * v) as nat, c, 1);
    let goal = config_word(u, (v * m * m + c) as nat);
    lemma_config_decompose(u, a, v, b, m);
    lemma_base_embeds_in_hnn(data, cw, ct);
    lemma_equiv_concat_left(p, cw, ct, seq![rs]);
    lemma_equiv_concat_right(p, seq![ri], cw + seq![rs], ct + seq![rs]);
    assert(seq![ri] + cw + seq![rs] == seq![ri] + (cw + seq![rs]));
    assert(seq![ri] + ct + seq![rs] == seq![ri] + (ct + seq![rs]));
    lemma_base_A_valid();
    lemma_conj_config_target_L(base_A(), 3, u, a, v, b, c, m);
    lemma_recompose_L(u, v, c, m);
    lemma_base_embeds_in_hnn(data, rt, goal);
    lemma_equiv_transitive(p, seq![ri] + cw + seq![rs], seq![ri] + ct + seq![rs], rt);
    lemma_equiv_transitive(p, seq![ri] + cw + seq![rs], rt, goal);
}

//  ============================================================
//  Tower lifting: a base_A equivalence holds in every level of B(M) and in G(M).
//  (lemma_base_embeds_in_hnn needs no validity — the lift is purely structural.)
//  ============================================================

pub proof fn lemma_lift_to_bm(mm: ModMachine, i: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(base_A(), w1, w2),
    ensures
        equiv_in_presentation(b_m_upto(mm, i), w1, w2),
    decreases i,
{
    if i == 0 {
    } else {
        lemma_lift_to_bm(mm, (i - 1) as nat, w1, w2);
        let data = HNNData {
            base: b_m_upto(mm, (i - 1) as nat),
            associations: quad_associations(mm.quads[(i - 1) as int], mm.m),
        };
        lemma_base_embeds_in_hnn(data, w1, w2);
    }
}

pub proof fn lemma_lift_to_gm(mm: ModMachine, w1: Word, w2: Word)
    requires
        equiv_in_presentation(base_A(), w1, w2),
    ensures
        equiv_in_presentation(g_m(mm), w1, w2),
{
    lemma_lift_to_bm(mm, mm.quads.len(), w1, w2);
    let data = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    lemma_base_embeds_in_hnn(data, w1, w2);
}

//  An equivalence at tower level j holds at every higher level i ≥ j.
pub proof fn lemma_lift_bm_level(mm: ModMachine, j: nat, i: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(b_m_upto(mm, j), w1, w2),
        j <= i,
    ensures
        equiv_in_presentation(b_m_upto(mm, i), w1, w2),
    decreases i,
{
    if i == j {
    } else {
        lemma_lift_bm_level(mm, j, (i - 1) as nat, w1, w2);
        let data = HNNData {
            base: b_m_upto(mm, (i - 1) as nat),
            associations: quad_associations(mm.quads[(i - 1) as int], mm.m),
        };
        lemma_base_embeds_in_hnn(data, w1, w2);
    }
}

//  The R forward step at tower level qi (stable letter Gen(3+qi)), living in
//  b_m_upto(mm, qi+1).  This is the form Theorem 1 needs.
pub proof fn lemma_forward_step_R_tower(mm: ModMachine, qi: nat, u: nat, v: nat)
    requires
        qi < mm.quads.len(),
        mm.quads[qi as int].dir == Dir::R,
    ensures
        equiv_in_presentation(
            b_m_upto(mm, (qi + 1) as nat),
            seq![Symbol::Inv((3 + qi) as nat)]
                + config_word((u * mm.m + mm.quads[qi as int].a) as nat, (v * mm.m + mm.quads[qi as int].b) as nat)
                + seq![Symbol::Gen((3 + qi) as nat)],
            config_word((u * mm.m * mm.m + mm.quads[qi as int].c) as nat, v),
        ),
{
    let q = mm.quads[qi as int];
    let m = mm.m;
    let n = (3 + qi) as nat;
    let base = b_m_upto(mm, qi);
    let rs = Symbol::Gen(n);
    let ri = Symbol::Inv(n);
    let cw = config_word((u * m + q.a) as nat, (v * m + q.b) as nat);
    let ct = config_target(u, q.a, v, q.b, m);
    lemma_b_m_upto_valid(mm, qi);
    lemma_b_m_upto_num_generators(mm, qi);
    assert(base.num_generators == n);
    assert(q == Quad { a: q.a, b: q.b, c: q.c, dir: Dir::R });
    let data = HNNData { base, associations: quad_associations(q, m) };
    let p = hnn_presentation(data);
    assert(p == b_m_upto(mm, (qi + 1) as nat));
    assert(data == HNNData { base, associations: quad_associations(Quad { a: q.a, b: q.b, c: q.c, dir: Dir::R }, m) });
    //  decomposition (base_A), lifted to base, then into p
    lemma_config_decompose(u, q.a, v, q.b, m);
    lemma_lift_to_bm(mm, qi, cw, ct);
    lemma_base_embeds_in_hnn(data, cw, ct);
    //  wrap in r⁻¹ … r
    lemma_equiv_concat_left(p, cw, ct, seq![rs]);
    lemma_equiv_concat_right(p, seq![ri], cw + seq![rs], ct + seq![rs]);
    assert(seq![ri] + cw + seq![rs] == seq![ri] + (cw + seq![rs]));
    assert(seq![ri] + ct + seq![rs] == seq![ri] + (ct + seq![rs]));
    //  conjugate (generic, at base) + recompose
    lemma_conj_config_target(base, n, u, q.a, v, q.b, q.c, m);
    lemma_recompose(u, v, q.c, m);
    lemma_equiv_transitive(p, seq![ri] + cw + seq![rs], seq![ri] + ct + seq![rs],
        recompose_target(u, v, q.c, m));
}

//  The L forward step at tower level qi, living in b_m_upto(mm, qi+1).
pub proof fn lemma_forward_step_L_tower(mm: ModMachine, qi: nat, u: nat, v: nat)
    requires
        qi < mm.quads.len(),
        mm.quads[qi as int].dir == Dir::L,
    ensures
        equiv_in_presentation(
            b_m_upto(mm, (qi + 1) as nat),
            seq![Symbol::Inv((3 + qi) as nat)]
                + config_word((u * mm.m + mm.quads[qi as int].a) as nat, (v * mm.m + mm.quads[qi as int].b) as nat)
                + seq![Symbol::Gen((3 + qi) as nat)],
            config_word(u, (v * mm.m * mm.m + mm.quads[qi as int].c) as nat),
        ),
{
    let q = mm.quads[qi as int];
    let m = mm.m;
    let n = (3 + qi) as nat;
    let base = b_m_upto(mm, qi);
    let rs = Symbol::Gen(n);
    let ri = Symbol::Inv(n);
    let cw = config_word((u * m + q.a) as nat, (v * m + q.b) as nat);
    let ct = config_target(u, q.a, v, q.b, m);
    let rt = config_target(u, 0, (m * m * v) as nat, q.c, 1);
    let goal = config_word(u, (v * m * m + q.c) as nat);
    lemma_b_m_upto_valid(mm, qi);
    lemma_b_m_upto_num_generators(mm, qi);
    assert(base.num_generators == n);
    assert(q == Quad { a: q.a, b: q.b, c: q.c, dir: Dir::L });
    let data = HNNData { base, associations: quad_associations(q, m) };
    let p = hnn_presentation(data);
    assert(p == b_m_upto(mm, (qi + 1) as nat));
    assert(data == HNNData { base, associations: quad_associations(Quad { a: q.a, b: q.b, c: q.c, dir: Dir::L }, m) });
    lemma_config_decompose(u, q.a, v, q.b, m);
    lemma_lift_to_bm(mm, qi, cw, ct);
    lemma_base_embeds_in_hnn(data, cw, ct);
    lemma_equiv_concat_left(p, cw, ct, seq![rs]);
    lemma_equiv_concat_right(p, seq![ri], cw + seq![rs], ct + seq![rs]);
    assert(seq![ri] + cw + seq![rs] == seq![ri] + (cw + seq![rs]));
    assert(seq![ri] + ct + seq![rs] == seq![ri] + (ct + seq![rs]));
    lemma_conj_config_target_L(base, n, u, q.a, v, q.b, q.c, m);
    lemma_recompose_L(u, v, q.c, m);
    lemma_lift_to_bm(mm, qi, rt, goal);
    lemma_base_embeds_in_hnn(data, rt, goal);
    lemma_equiv_transitive(p, seq![ri] + cw + seq![rs], seq![ri] + ct + seq![rs], rt);
    lemma_equiv_transitive(p, seq![ri] + cw + seq![rs], rt, goal);
}

//  An equivalence at tower level j holds in the full G(M).
pub proof fn lemma_lift_level_to_gm(mm: ModMachine, j: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(b_m_upto(mm, j), w1, w2),
        j <= mm.quads.len(),
    ensures
        equiv_in_presentation(g_m(mm), w1, w2),
{
    lemma_lift_bm_level(mm, j, mm.quads.len(), w1, w2);
    let data = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    lemma_base_embeds_in_hnn(data, w1, w2);
}

//  ============================================================
//  Power conjugation:  r⁻¹·sᵐⁿ·r ~ s'ᵐ'ⁿ  given the single relation r⁻¹·sᵐ·r ~ s'ᵐ'.
//  ============================================================

//  A cancelling pair is trivial.
pub proof fn lemma_cancel_pair_equiv_empty(p: Presentation, rs: Symbol, ri: Symbol)
    requires
        is_inverse_pair(rs, ri),
    ensures
        equiv_in_presentation(p, seq![rs, ri], empty_word()),
{
    let w: Word = seq![rs, ri];
    assert(has_cancellation_at(w, 0)) by {
        assert(w[0] == rs && w[1] == ri);
    }
    assert(reduce_at(w, 0) =~= empty_word());
    assert(reduces_one_step(w, empty_word())) by {
        assert(has_cancellation_at(w, 0) && empty_word() == reduce_at(w, 0));
    }
    assert(reduces_in_steps(w, empty_word(), 1)) by {
        assert(reduces_one_step(w, empty_word()) && reduces_in_steps(empty_word(), empty_word(), 0));
    }
    assert(reduces_to(w, empty_word()));
    lemma_reduces_to_equiv(p, w, empty_word());
}

//  The inverse of a base conjugation relation (invert both sides).
pub proof fn lemma_conj_base_inverse(
    p: Presentation, rs: Symbol, ri: Symbol, s: Symbol, ssp: Symbol, m: nat, mp: nat,
)
    requires
        is_inverse_pair(rs, ri),
        presentation_valid(p),
        word_valid(seq![ri] + symbol_power(s, m) + seq![rs], p.num_generators),
        word_valid(symbol_power(ssp, mp), p.num_generators),
        equiv_in_presentation(p, seq![ri] + symbol_power(s, m) + seq![rs], symbol_power(ssp, mp)),
    ensures
        equiv_in_presentation(
            p,
            seq![ri] + symbol_power(inverse_symbol(s), m) + seq![rs],
            symbol_power(inverse_symbol(ssp), mp),
        ),
{
    let lhs: Word = seq![ri] + symbol_power(s, m) + seq![rs];
    let rhs: Word = symbol_power(ssp, mp);
    lemma_equiv_inverse(p, lhs, rhs);
    lemma_inverse_word_concat(seq![ri] + symbol_power(s, m), seq![rs]);
    lemma_inverse_word_concat(seq![ri], symbol_power(s, m));
    lemma_inverse_word_sympower(s, m);
    lemma_inverse_word_sympower(ssp, mp);
    reveal_with_fuel(inverse_word, 2);
    assert(seq![rs].drop_first() =~= empty_word());
    assert(seq![ri].drop_first() =~= empty_word());
    assert(inverse_symbol(rs) == ri);
    lemma_inverse_involution(rs);
    assert(inverse_word(lhs) =~= seq![ri] + symbol_power(inverse_symbol(s), m) + seq![rs]);
    assert(inverse_word(rhs) =~= symbol_power(inverse_symbol(ssp), mp));
}

//  From the HNN relation  K⁻¹·W·K ~ W,  derive that K commutes with W:  K·W ~ W·K.
pub proof fn lemma_commute_from_conj(p: Presentation, kk: Symbol, ki: Symbol, w: Word)
    requires
        is_inverse_pair(kk, ki),
        symbol_valid(kk, p.num_generators),
        presentation_valid(p),
        word_valid(w, p.num_generators),
        equiv_in_presentation(p, seq![ki] + w + seq![kk], w),
    ensures
        equiv_in_presentation(p, seq![kk] + w, w + seq![kk]),
{
    let ng = p.num_generators;
    lemma_inverse_preserves_index(kk);
    assert(symbol_valid(ki, ng));
    let lhs: Word = seq![kk, ki] + w + seq![kk];
    //  lhs reduces to  w·K  (cancel K·K⁻¹ at position 0)
    assert(has_cancellation_at(lhs, 0)) by { assert(lhs[0] == kk && lhs[1] == ki); }
    assert(reduce_at(lhs, 0) =~= w + seq![kk]) by {
        assert(lhs.subrange(0, 0) =~= empty_word());
        assert(lhs.subrange(2, lhs.len() as int) =~= w + seq![kk]);
    }
    assert(reduces_one_step(lhs, w + seq![kk])) by {
        assert(has_cancellation_at(lhs, 0) && w + seq![kk] == reduce_at(lhs, 0));
    }
    assert(reduces_in_steps(lhs, w + seq![kk], 1)) by {
        assert(reduces_one_step(lhs, w + seq![kk]) && reduces_in_steps(w + seq![kk], w + seq![kk], 0));
    }
    assert(reduces_to(lhs, w + seq![kk]));
    lemma_reduces_to_equiv(p, lhs, w + seq![kk]);                          //  lhs ~ w·K
    lemma_equiv_concat_right(p, seq![kk], seq![ki] + w + seq![kk], w);     //  K·(K⁻¹·w·K) ~ K·w
    assert(seq![kk] + (seq![ki] + w + seq![kk]) == lhs);
    //  word validity of lhs for symmetric
    let kki: Word = seq![kk, ki];
    let kw: Word = seq![kk];
    assert(word_valid(kki, ng)) by {
        assert forall|i: int| 0 <= i < kki.len() implies symbol_valid(#[trigger] kki[i], ng) by { }
    }
    assert(word_valid(kw, ng)) by {
        assert forall|i: int| 0 <= i < kw.len() implies symbol_valid(#[trigger] kw[i], ng) by { }
    }
    lemma_concat_word_valid(kki, w, ng);
    lemma_concat_word_valid(kki + w, kw, ng);
    lemma_equiv_symmetric(p, lhs, w + seq![kk]);                          //  w·K ~ lhs
    lemma_equiv_transitive(p, w + seq![kk], lhs, seq![kk] + w);           //  w·K ~ K·w
    lemma_equiv_symmetric(p, w + seq![kk], seq![kk] + w);                 //  K·w ~ w·K
}

//  From  s⁻¹·W·s ~ V,  solve for W:  W ~ s·V·s⁻¹.
pub proof fn lemma_conj_solve(p: Presentation, s: Symbol, si: Symbol, w: Word, vv: Word)
    requires
        is_inverse_pair(s, si),
        symbol_valid(s, p.num_generators),
        presentation_valid(p),
        word_valid(w, p.num_generators),
        equiv_in_presentation(p, seq![si] + w + seq![s], vv),
    ensures
        equiv_in_presentation(p, w, seq![s] + vv + seq![si]),
{
    let ng = p.num_generators;
    lemma_inverse_preserves_index(s);
    assert(symbol_valid(si, ng));
    //  wrap the hypothesis in s · … · s⁻¹
    lemma_equiv_concat_left(p, seq![si] + w + seq![s], vv, seq![si]);
    lemma_equiv_concat_right(p, seq![s], (seq![si] + w + seq![s]) + seq![si], vv + seq![si]);
    let big: Word = seq![s, si] + w + seq![s, si];
    assert(seq![s] + ((seq![si] + w + seq![s]) + seq![si]) =~= big);
    assert(seq![s] + (vv + seq![si]) == seq![s] + vv + seq![si]);
    //  big collapses to w (delete the two cancelling pairs)
    lemma_cancel_pair_equiv_empty(p, s, si);
    lemma_delete_equiv_empty(p, empty_word(), seq![s, si], w + seq![s, si]);
    lemma_delete_equiv_empty(p, w, seq![s, si], empty_word());
    assert(concat(empty_word(), concat(seq![s, si], w + seq![s, si])) =~= big);
    assert(concat(empty_word(), w + seq![s, si]) =~= w + seq![s, si]);
    assert(concat(w, concat(seq![s, si], empty_word())) =~= w + seq![s, si]);
    assert(concat(w, empty_word()) =~= w);
    lemma_equiv_transitive(p, big, w + seq![s, si], w);
    //  word validity of big for symmetric
    let ssi: Word = seq![s, si];
    assert(word_valid(ssi, ng)) by {
        assert forall|i: int| 0 <= i < ssi.len() implies symbol_valid(#[trigger] ssi[i], ng) by { }
    }
    lemma_concat_word_valid(ssi, w, ng);
    lemma_concat_word_valid(ssi + w, ssi, ng);
    lemma_equiv_symmetric(p, big, w);
    lemma_equiv_transitive(p, w, big, seq![s] + vv + seq![si]);
}

//  Conjugation distributes over a concatenation (insert a cancelling pair).
pub proof fn lemma_conj_distributes(p: Presentation, ri: Symbol, rs: Symbol, aw: Word, bw: Word)
    requires
        is_inverse_pair(rs, ri),
        presentation_valid(p),
        word_valid(seq![rs, ri], p.num_generators),
    ensures
        equiv_in_presentation(
            p,
            seq![ri] + (aw + bw) + seq![rs],
            (seq![ri] + aw + seq![rs]) + (seq![ri] + bw + seq![rs]),
        ),
{
    lemma_cancel_pair_equiv_empty(p, rs, ri);
    lemma_insert_equiv_empty(p, seq![ri] + aw, seq![rs, ri], bw + seq![rs]);
    assert((seq![ri] + aw) + (bw + seq![rs]) =~= seq![ri] + (aw + bw) + seq![rs]);
    assert((seq![ri] + aw) + concat(seq![rs, ri], bw + seq![rs])
        =~= (seq![ri] + aw + seq![rs]) + (seq![ri] + bw + seq![rs]));
}

//  Conjugation distributes over a power, scaling the exponent.
pub proof fn lemma_conj_sympower(
    p: Presentation, rs: Symbol, ri: Symbol, s: Symbol, ssp: Symbol,
    m: nat, mp: nat, n: nat,
)
    requires
        is_inverse_pair(rs, ri),
        presentation_valid(p),
        word_valid(seq![rs, ri], p.num_generators),
        equiv_in_presentation(p, seq![ri] + symbol_power(s, m) + seq![rs], symbol_power(ssp, mp)),
    ensures
        equiv_in_presentation(
            p,
            seq![ri] + symbol_power(s, (m * n) as nat) + seq![rs],
            symbol_power(ssp, (mp * n) as nat),
        ),
    decreases n,
{
    if n == 0 {
        lemma_inverse_pair_symmetric(rs, ri);
        lemma_cancel_pair_equiv_empty(p, ri, rs);
        assert(seq![ri] + symbol_power(s, (m * 0) as nat) + seq![rs] =~= seq![ri, rs]);
        assert(symbol_power(ssp, (mp * 0) as nat) =~= empty_word());
    } else {
        let k = (n - 1) as nat;
        let f1: Word = seq![ri] + symbol_power(s, m) + seq![rs];
        let f2: Word = seq![ri] + symbol_power(s, (m * k) as nat) + seq![rs];
        let lhs0: Word = seq![ri] + symbol_power(s, m) + symbol_power(s, (m * k) as nat) + seq![rs];
        //  exponent arithmetic (nonlinear: m·n = m·(k+1) = m + m·k)
        assert(n == k + 1);
        assert(m * n == m + m * k) by (nonlinear_arith)
            requires n == k + 1;
        assert(mp * n == mp + mp * k) by (nonlinear_arith)
            requires n == k + 1;
        //  goal-LHS =~= lhs0   (merge sᵐ·sᵐᵏ = sᵐ⁽ᵏ⁺¹⁾)
        lemma_symbol_power_merge(s, m, m * k);
        assert(seq![ri] + symbol_power(s, (m * n) as nat) + seq![rs] =~= lhs0);
        //  insert the cancelling pair rs·ri between sᵐ and sᵐᵏ
        lemma_cancel_pair_equiv_empty(p, rs, ri);
        lemma_insert_equiv_empty(
            p,
            seq![ri] + symbol_power(s, m),
            seq![rs, ri],
            symbol_power(s, (m * k) as nat) + seq![rs],
        );
        assert((seq![ri] + symbol_power(s, m)) + (symbol_power(s, (m * k) as nat) + seq![rs]) =~= lhs0);
        assert((seq![ri] + symbol_power(s, m))
            + concat(seq![rs, ri], symbol_power(s, (m * k) as nat) + seq![rs]) =~= f1 + f2);
        //  equiv(p, lhs0, f1 + f2)
        //  hyp gives f1 ~ s'ᵐ'; IH gives f2 ~ s'ᵐ'ᵏ
        lemma_conj_sympower(p, rs, ri, s, ssp, m, mp, k);
        lemma_equiv_concat_left(p, f1, symbol_power(ssp, mp), f2);
        lemma_equiv_concat_right(p, symbol_power(ssp, mp), f2, symbol_power(ssp, (mp * k) as nat));
        //  merge s'ᵐ'·s'ᵐ'ᵏ = s'ᵐ'⁽ᵏ⁺¹⁾
        lemma_symbol_power_merge(ssp, mp, mp * k);
        assert(symbol_power(ssp, mp) + symbol_power(ssp, (mp * k) as nat)
            =~= symbol_power(ssp, (mp * n) as nat));
        //  chain:  lhs0 ~ f1+f2 ~ s'ᵐ'·f2 ~ s'ᵐ'·s'ᵐ'ᵏ
        lemma_equiv_transitive(p, lhs0, f1 + f2, symbol_power(ssp, mp) + f2);
        lemma_equiv_transitive(p, lhs0, symbol_power(ssp, mp) + f2,
            symbol_power(ssp, mp) + symbol_power(ssp, (mp * k) as nat));
    }
}

//  y⁻¹·x⁻¹ ~ x⁻¹·y⁻¹ in A — the inverse of the keystone (the second commutation
//  the decomposition needs).
pub proof fn lemma_xinv_yinv_commute_in_A()
    ensures
        equiv_in_presentation(
            base_A(),
            seq![Symbol::Inv(2), Symbol::Inv(1)],
            seq![Symbol::Inv(1), Symbol::Inv(2)],
        ),
{
    let a = base_A();
    let xy: Word = seq![Symbol::Gen(1), Symbol::Gen(2)];
    let yx: Word = seq![Symbol::Gen(2), Symbol::Gen(1)];
    lemma_xy_commute_in_A();
    lemma_base_A_valid();
    assert(word_valid(xy, 3)) by {
        assert forall|i: int| 0 <= i < xy.len() implies symbol_valid(#[trigger] xy[i], 3) by {}
    }
    assert(word_valid(yx, 3)) by {
        assert forall|i: int| 0 <= i < yx.len() implies symbol_valid(#[trigger] yx[i], 3) by {}
    }
    lemma_equiv_inverse(a, xy, yx);
    lemma_inverse_word_two(Symbol::Gen(1), Symbol::Gen(2));
    lemma_inverse_word_two(Symbol::Gen(2), Symbol::Gen(1));
    assert(inverse_word(xy) =~= seq![Symbol::Inv(2), Symbol::Inv(1)]);
    assert(inverse_word(yx) =~= seq![Symbol::Inv(1), Symbol::Inv(2)]);
}

//  ============================================================
//  ⟸ direction of Theorem 1 — THE CAPSTONE INDUCTION
//  ============================================================
//
//  If the machine drives (α,β) to the terminal origin (0,0) in k steps, then the
//  stable letter k commutes with the configuration word t(α,β).  Each machine step
//  becomes a forward-step conjugation, solved for t(α,β) as a product of three
//  k-commuting pieces: the stable letter rᵢ/lⱼ, the inductive hypothesis on the
//  next configuration, and the stable letter's inverse.

//  Euclidean reconstruction for nat:  x = (x/m)·m + x mod m.
//  On the Lean backend nat is `Nat`, so we discharge with the core `Nat` lemmas:
//  `Nat.div_add_mod` (m·(x/m) + x%m = x) and `Nat.mul_comm`, then omega.
pub proof fn lemma_div_mod_id(x: nat, m: nat)
    requires
        m > 0,
    ensures
        x == (x / m) * m + x % m
by {
    have h1 := Nat.div_add_mod x m
    have h2 := Nat.mul_comm (x / m) m
    omega
}

//  config_word(0,0) is just the bare generator t = Gen(0).
pub proof fn lemma_config_word_zero()
    ensures
        config_word(0, 0) =~= seq![Symbol::Gen(0)],
{
    assert(symbol_power(Symbol::Inv(2), 0) =~= empty_word());
    assert(symbol_power(Symbol::Inv(1), 0) =~= empty_word());
    assert(symbol_power(Symbol::Gen(1), 0) =~= empty_word());
    assert(symbol_power(Symbol::Gen(2), 0) =~= empty_word());
}

pub proof fn lemma_reaches_implies_k_commutes(mm: ModMachine, alpha: nat, beta: nat, k: nat)
    requires
        mod_machine_wf(mm),
        mm_reaches(mm, alpha, beta, 0, 0, k),
    ensures
        k_commutes(mm, config_word(alpha, beta)),
    decreases k,
{
    let p = g_m(mm);
    let m = mm.m;
    lemma_g_m_valid(mm);
    lemma_g_m_num_generators(mm);
    let ng = p.num_generators;          //  == 4 + |quads|
    if k == 0 {
        assert(alpha == 0 && beta == 0);
        lemma_config_word_zero();
        assert(config_word(alpha, beta) == seq![Symbol::Gen(0)]);
        lemma_k_commutes_t(mm);
    } else {
        //  unfold mm_reaches: ∃ am,bm. yields(α,β,am,bm) ∧ reaches(am,bm,0,0,k-1)
        reveal_with_fuel(mm_reaches, 1);
        let ambm: (nat, nat) = choose|am: nat, bm: nat| #![auto]
            mm_yields(mm, alpha, beta, am, bm)
            && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat);
        let am = ambm.0;
        let bm = ambm.1;
        assert(mm_yields(mm, alpha, beta, am, bm)
            && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat));
        //  the matching quadruple
        let qi = choose|qi: int| 0 <= qi < mm.quads.len()
            && quad_matches(mm.quads[qi], m, alpha, beta)
            && quad_step(mm.quads[qi], m, alpha, beta) == (am, bm);
        assert(0 <= qi < mm.quads.len()
            && quad_matches(mm.quads[qi], m, alpha, beta)
            && quad_step(mm.quads[qi], m, alpha, beta) == (am, bm));
        let q = mm.quads[qi];
        let qn = qi as nat;
        assert(mm.quads[qn as int] == q);
        let u = alpha / m;
        let v = beta / m;
        //  div-mod + residue match  ⟹  α = u·m + a, β = v·m + b
        assert(m > 0);
        lemma_div_mod_id(alpha, m);
        lemma_div_mod_id(beta, m);
        assert(alpha % m == q.a && beta % m == q.b);
        assert(alpha == u * m + q.a);
        assert(beta == v * m + q.b);
        //  inductive hypothesis on the next configuration
        lemma_reaches_implies_k_commutes(mm, am, bm, (k - 1) as nat);
        //  RHS pieces and their k-commutation
        let rs: Word = seq![Symbol::Gen((3 + qn) as nat)];
        let ri: Word = seq![Symbol::Inv((3 + qn) as nat)];
        let cwn = config_word(am, bm);
        let cwab = config_word(alpha, beta);
        let rhs: Word = rs + cwn + ri;
        lemma_k_commutes_stable(mm, qn);
        lemma_k_commutes_stable_inv(mm, qn);
        lemma_k_commutes_product(mm, rs, cwn);
        lemma_k_commutes_product(mm, rs + cwn, ri);
        //  validity of t(α,β), t(am,bm), and rhs over ng generators
        lemma_config_word_valid(alpha, beta);
        lemma_word_valid_mono(cwab, 3, ng);
        lemma_config_word_valid(am, bm);
        lemma_word_valid_mono(cwn, 3, ng);
        assert(3 + qn < ng);
        assert(symbol_valid(Symbol::Gen((3 + qn) as nat), ng));
        assert(symbol_valid(Symbol::Inv((3 + qn) as nat), ng));
        assert(word_valid(rs, ng)) by {
            assert forall|i: int| 0 <= i < rs.len() implies symbol_valid(#[trigger] rs[i], ng) by { }
        }
        assert(word_valid(ri, ng)) by {
            assert forall|i: int| 0 <= i < ri.len() implies symbol_valid(#[trigger] ri[i], ng) by { }
        }
        lemma_concat_word_valid(rs, cwn, ng);
        lemma_concat_word_valid(rs + cwn, ri, ng);
        //  the forward step gives  rᵢ⁻¹ · t(α,β) · rᵢ ~ t(am,bm)  in b_m_upto(qi+1);
        //  lift to G(M), conj-solve, and read off k-commutation.
        let lhs_conj: Word = ri + cwab + rs;
        assert(is_inverse_pair(Symbol::Gen((3 + qn) as nat), Symbol::Inv((3 + qn) as nat)));
        match q.dir {
            Dir::R => {
                assert((u * m + q.a) as nat == alpha && (v * m + q.b) as nat == beta);
                //  quad_step (R) gives the next configuration
                assert(am == (alpha / m) * (m * m) + q.c && bm == beta / m);
                assert(u * (m * m) == u * m * m) by (nonlinear_arith);
                assert(am == u * m * m + q.c);
                assert(bm == v);
                assert(config_word((u * m + q.a) as nat, (v * m + q.b) as nat) == cwab);
                assert(config_word((u * m * m + q.c) as nat, v) == cwn);
                lemma_forward_step_R_tower(mm, qn, u, v);
                assert(equiv_in_presentation(b_m_upto(mm, (qn + 1) as nat), lhs_conj, cwn));
            }
            Dir::L => {
                assert((u * m + q.a) as nat == alpha && (v * m + q.b) as nat == beta);
                //  quad_step (L) gives the next configuration
                assert(am == alpha / m && bm == (beta / m) * (m * m) + q.c);
                assert(v * (m * m) == v * m * m) by (nonlinear_arith);
                assert(am == u);
                assert(bm == v * m * m + q.c);
                assert(config_word((u * m + q.a) as nat, (v * m + q.b) as nat) == cwab);
                assert(config_word(u, (v * m * m + q.c) as nat) == cwn);
                lemma_forward_step_L_tower(mm, qn, u, v);
                assert(equiv_in_presentation(b_m_upto(mm, (qn + 1) as nat), lhs_conj, cwn));
            }
        }
        lemma_lift_level_to_gm(mm, (qn + 1) as nat, lhs_conj, cwn);
        lemma_conj_solve(p, Symbol::Gen((3 + qn) as nat), Symbol::Inv((3 + qn) as nat), cwab, cwn);
        assert(equiv_in_presentation(p, cwab, rhs));
        lemma_equiv_symmetric(p, cwab, rhs);
        lemma_k_commutes_respects_equiv(mm, rhs, cwab);
    }
}

//  ============================================================
//  Obligation E (faithfulness, the crux) — E1a: the k-extension's
//  associated subgroups form an isomorphic pair (identity iso).
//  ============================================================
//
//  g_m is HNN(B(M), k) with EVERY association of the form (s, s) — the identity
//  isomorphism on ⟨t, rᵢ, lⱼ⟩.  So `hnn_associations_isomorphic` is reflexive:
//  a_words == b_words, hence apply_embedding agrees, hence the ⟺ is trivial.
//  Needed to invoke britton_lemma_full on the k-extension.
pub proof fn lemma_g_m_associations_isomorphic(mm: ModMachine)
    ensures
        hnn_associations_isomorphic(HNNData { base: b_m(mm), associations: g_m_associations(mm) }),
{
    let gdata = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    let k = gdata.associations.len();
    let a_words = Seq::new(k, |i: int| gdata.associations[i].0);
    let b_words = Seq::new(k, |i: int| gdata.associations[i].1);
    //  every association is (s, s), so the two image lists coincide;
    //  with a_words == b_words the ⟺ in hnn_associations_isomorphic is reflexive.
    assert forall|i: int| 0 <= i < k implies
        gdata.associations[i].0 == gdata.associations[i].1
    by {
        if i == 0 {
        } else {
            assert(gdata.associations[i] == {
                let g = Symbol::Gen((3 + (i - 1)) as nat);
                (seq![g], seq![g])
            });
        }
    }
    assert(a_words =~= b_words);
}

//  The generators of the k-extension's associated subgroup ⟨t, rᵢ, lⱼ⟩
//  (= the b_gens / a_gens of g_m's identity-iso associations).
pub open spec fn g_subgens(mm: ModMachine) -> Seq<Word> {
    Seq::new(g_m_associations(mm).len(), |i: int| g_m_associations(mm)[i].1)
}

//  A word valid over n ≤ base.num_generators contains no stable letter
//  (stable letters live at index exactly base.num_generators).
pub proof fn lemma_no_stable_of_valid(data: HNNData, x: Word, n: nat)
    requires
        word_valid(x, n),
        n <= data.base.num_generators,
    ensures
        forall|pp: int| 0 <= pp < x.len() ==> !is_stable(data, #[trigger] x[pp]),
{
    let ng = data.base.num_generators;
    assert forall|pp: int| 0 <= pp < x.len() implies !is_stable(data, x[pp]) by {
        assert(symbol_valid(x[pp], n));
        assert(generator_index(x[pp]) < n);
        assert(generator_index(Symbol::Gen(ng)) == ng);
        assert(generator_index(Symbol::Inv(ng)) == ng);
    }
}

//  The commutator word [k]·w·[k⁻¹]·w⁻¹ has stable letters ONLY at its two ends
//  (position 0 = k, position 1+|w| = k⁻¹), provided w and w⁻¹ have none.
pub proof fn lemma_commutator_stable_at_ends(
    data: HNNData, kk: Symbol, ki: Symbol, w: Word, pp: int,
)
    requires
        kk == Symbol::Gen(data.base.num_generators),
        ki == Symbol::Inv(data.base.num_generators),
        forall|q: int| 0 <= q < w.len() ==> !is_stable(data, #[trigger] w[q]),
        forall|q: int| 0 <= q < inverse_word(w).len() ==> !is_stable(data, #[trigger] inverse_word(w)[q]),
        0 <= pp < (seq![kk] + w + seq![ki] + inverse_word(w)).len(),
        is_stable(data, (seq![kk] + w + seq![ki] + inverse_word(w))[pp]),
    ensures
        pp == 0 || pp == 1 + w.len(),
{
    let iw = inverse_word(w);
    let c: Word = seq![kk] + w + seq![ki] + iw;
    let l = w.len() as int;
    //  c = (((seq![kk] + w) + seq![ki]) + iw)
    let c3: Word = seq![kk] + w + seq![ki];     //  length 2 + l
    assert(c3.len() == 2 + l);
    if pp == 0 {
    } else if pp < 1 + l {
        //  middle of w: c[pp] == w[pp-1]
        assert(c[pp] == c3[pp]);
        assert(c3[pp] == (seq![kk] + w)[pp]);
        assert((seq![kk] + w)[pp] == w[pp - 1]);
        assert(!is_stable(data, w[pp - 1]));
    } else if pp == 1 + l {
    } else {
        //  tail of w⁻¹: c[pp] == iw[pp - (2 + l)]
        assert(c[pp] == iw[pp - (2 + l)]);
        assert(!is_stable(data, iw[pp - (2 + l)]));
    }
}

//  ============================================================
//  E1 — property (III) for the k-extension:
//        k commutes with t(α,β)  ⟹  t(α,β) ∈ ⟨t, rᵢ, lⱼ⟩.
//  ============================================================
//
//  k_commutes gives [k]·t(α,β) ≡ t(α,β)·[k], so the commutator
//  C = [k]·t(α,β)·[k⁻¹]·t(α,β)⁻¹ ≡ ε.  C carries the stable letter k, so by
//  britton_lemma_full it has a pinch.  t(α,β) has no k, so the pinch is forced
//  to the two ends (0, 1+|t(α,β)|) — the t·g·t⁻¹ case — whose middle is exactly
//  t(α,β), landing it in the associated subgroup ⟨t, rᵢ, lⱼ⟩.
pub proof fn lemma_k_commutes_implies_subgroup(mm: ModMachine, alpha: nat, beta: nat)
    requires
        k_commutes(mm, config_word(alpha, beta)),
    ensures
        in_generated_subgroup(b_m(mm), g_subgens(mm), config_word(alpha, beta)),
{
    let w = config_word(alpha, beta);
    let nq = mm.quads.len();
    let ngb = (3 + nq) as nat;
    let kk = Symbol::Gen(ngb);
    let ki = Symbol::Inv(ngb);
    let kw: Word = seq![kk];
    let kiw: Word = seq![ki];
    let gdata = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    let p = g_m(mm);
    let l = w.len() as int;

    //  --- validity / structure setup ---
    lemma_b_m_valid(mm);
    lemma_g_m_associations_valid(mm);
    lemma_b_m_upto_num_generators(mm, nq);
    assert(b_m(mm).num_generators == ngb);
    assert(hnn_data_valid(gdata));
    lemma_g_m_associations_isomorphic(mm);
    lemma_g_m_valid(mm);
    lemma_g_m_num_generators(mm);
    let ng = p.num_generators;
    assert(k_gen(mm) == kk);

    //  --- the commutator cc ≡ ε ---
    let u: Word = kw + w;
    let v: Word = w + kw;
    assert(equiv_in_presentation(p, u, v));
    lemma_inverse_word_concat(w, kw);
    lemma_inverse_word_one(kk);
    assert(inverse_symbol(kk) == ki);
    assert(inverse_word(v) =~= kiw + inverse_word(w));
    let cc: Word = kw + w + kiw + inverse_word(w);
    assert(u + inverse_word(v) =~= cc);
    lemma_word_inverse_right(p, v);
    lemma_equiv_concat_left(p, u, v, inverse_word(v));
    lemma_equiv_transitive(p, u + inverse_word(v), v + inverse_word(v), empty_word());
    assert(equiv_in_presentation(p, cc, empty_word()));

    //  --- word validity of cc ---
    lemma_config_word_valid(alpha, beta);
    lemma_word_valid_mono(w, 3, ng);
    crate::word::lemma_inverse_word_valid(w, ng);
    assert(symbol_valid(kk, ng) && symbol_valid(ki, ng));
    assert(word_valid(kw, ng)) by {
        assert forall|i: int| 0 <= i < kw.len() implies symbol_valid(#[trigger] kw[i], ng) by { }
    }
    assert(word_valid(kiw, ng)) by {
        assert forall|i: int| 0 <= i < kiw.len() implies symbol_valid(#[trigger] kiw[i], ng) by { }
    }
    lemma_concat_word_valid(kw, w, ng);
    lemma_concat_word_valid(kw + w, kiw, ng);
    lemma_concat_word_valid(kw + w + kiw, inverse_word(w), ng);

    //  --- has_stable_letter(gdata, cc) ---
    assert(cc[0] == kk);
    assert(is_stable(gdata, kk));
    assert(has_stable_letter(gdata, cc)) by {
        assert(0 <= 0 < cc.len() && is_stable(gdata, cc[0]));
    }

    //  --- britton: cc has a pinch ---
    britton_lemma_full(gdata, cc);
    assert(has_pinch(gdata, cc));

    //  --- w and w⁻¹ carry no stable letters (valid over 3 ≤ ngb) ---
    lemma_no_stable_of_valid(gdata, w, 3);
    crate::word::lemma_inverse_word_valid(w, 3);
    lemma_no_stable_of_valid(gdata, inverse_word(w), 3);

    //  --- extract the pinch and force it to the ends (0, 1+l) ---
    let pij: (int, int) = choose|i: int, j: int| has_pinch_at(gdata, cc, i, j);
    let pi = pij.0;
    let pj = pij.1;
    assert(has_pinch_at(gdata, cc, pi, pj));
    assert(has_adjacent_opposite_at(gdata, cc, pi, pj));
    assert(is_stable(gdata, cc[pi]) && is_stable(gdata, cc[pj]) && 0 <= pi < pj < cc.len());
    lemma_commutator_stable_at_ends(gdata, kk, ki, w, pi);
    lemma_commutator_stable_at_ends(gdata, kk, ki, w, pj);
    assert(pi == 0 && pj == 1 + l);

    //  --- read off membership (the t·g·t⁻¹ disjunct) ---
    assert(cc[pi] == Symbol::Gen(gdata.base.num_generators));
    assert(cc[pj] == Symbol::Inv(gdata.base.num_generators));
    let base_word = cc.subrange(pi + 1, pj);
    let bgens = Seq::new(gdata.associations.len(), |i: int| gdata.associations[i].1);
    assert(in_generated_subgroup(gdata.base, bgens, base_word));
    assert(base_word =~= w);
    assert(bgens =~= g_subgens(mm));
    assert(in_generated_subgroup(b_m(mm), g_subgens(mm), w));
}

//  ============================================================
//  E2 base camp — T(M)-membership as a finite-factorization predicate.
//  ============================================================
//
//  T(M) = ⟨ t(α',β') : (α',β') ∈ H₀(M) ⟩ is INFINITELY generated, so we can't
//  use `in_generated_subgroup` with a finite `Seq` of generators.  Instead:
//  `in_T(mm, w)` holds iff w is a finite product of signed H₀ config words,
//  equivalent in A.  The factorization is finite even though the basis isn't.

//  A single factor is ±t(α',β') for some H₀ configuration.
pub open spec fn is_h0_factor(mm: ModMachine, f: Word) -> bool {
    exists|a: nat, b: nat| #![trigger config_word(a, b)]
        mm_in_H0(mm, a, b) && (f == config_word(a, b) || f == inverse_word(config_word(a, b)))
}

pub open spec fn all_h0_factors(mm: ModMachine, factors: Seq<Word>) -> bool {
    forall|i: int| 0 <= i < factors.len() ==> is_h0_factor(mm, #[trigger] factors[i])
}

//  w ∈ T(M): a finite product of signed H₀ config words, ≡ w in A.
pub open spec fn in_T(mm: ModMachine, w: Word) -> bool {
    exists|factors: Seq<Word>|
        #[trigger] all_h0_factors(mm, factors)
        && equiv_in_presentation(base_A(), concat_all(factors), w)
}

//  Each H₀ configuration word lies in T(M) (the length-1 factorization).
pub proof fn lemma_h0_config_in_T(mm: ModMachine, a: nat, b: nat)
    requires
        mm_in_H0(mm, a, b),
    ensures
        in_T(mm, config_word(a, b)),
{
    let f = config_word(a, b);
    let factors: Seq<Word> = seq![f];
    lemma_base_A_valid();
    lemma_config_word_valid(a, b);
    lemma_concat_all_singleton(f);
    assert(concat_all(factors) =~= f);
    lemma_equiv_refl(base_A(), f);
    assert(all_h0_factors(mm, factors)) by {
        assert(factors[0] == f);
        assert(is_h0_factor(mm, f)) by {
            assert(mm_in_H0(mm, a, b) && (f == config_word(a, b)));
        }
    }
    assert(equiv_in_presentation(base_A(), concat_all(factors), f));
    assert(in_T(mm, f));
}

//  ============================================================
//  E2 base camp — T(M) is closed under product (subgroup property 1/2)
//  ============================================================

//  concat_all distributes over list concatenation.
pub proof fn lemma_concat_all_distributes(f1: Seq<Word>, f2: Seq<Word>)
    ensures
        concat_all(f1 + f2) =~= concat(concat_all(f1), concat_all(f2)),
    decreases f1.len(),
{
    reveal_with_fuel(concat_all, 2);
    if f1.len() == 0 {
        lemma_concat_all_empty();
        assert(f1 + f2 =~= f2);
        assert(concat_all(f1) =~= empty_word());
        assert(concat(empty_word(), concat_all(f2)) =~= concat_all(f2));
    } else {
        let rest = f1.drop_first();
        assert((f1 + f2).first() == f1.first());
        assert((f1 + f2).drop_first() =~= rest + f2);
        lemma_concat_all_distributes(rest, f2);
        assert(concat_all(f1) =~= concat(f1.first(), concat_all(rest)));
        assert(concat_all(f1 + f2) =~= concat(f1.first(), concat_all(rest + f2)));
    }
}

//  all_h0_factors is preserved by list concatenation.
pub proof fn lemma_all_h0_factors_concat(mm: ModMachine, f1: Seq<Word>, f2: Seq<Word>)
    requires
        all_h0_factors(mm, f1),
        all_h0_factors(mm, f2),
    ensures
        all_h0_factors(mm, f1 + f2),
{
    assert forall|i: int| 0 <= i < (f1 + f2).len()
        implies is_h0_factor(mm, #[trigger] (f1 + f2)[i]) by {
        if i < f1.len() {
            assert((f1 + f2)[i] == f1[i]);
        } else {
            assert((f1 + f2)[i] == f2[i - f1.len()]);
        }
    }
}

//  T(M) is closed under the group product:  w1, w2 ∈ T(M) ⟹ w1·w2 ∈ T(M).
pub proof fn lemma_in_T_product(mm: ModMachine, w1: Word, w2: Word)
    requires
        in_T(mm, w1),
        in_T(mm, w2),
    ensures
        in_T(mm, w1 + w2),
{
    let f1 = choose|f: Seq<Word>|
        #[trigger] all_h0_factors(mm, f) && equiv_in_presentation(base_A(), concat_all(f), w1);
    let f2 = choose|f: Seq<Word>|
        #[trigger] all_h0_factors(mm, f) && equiv_in_presentation(base_A(), concat_all(f), w2);
    let f = f1 + f2;
    lemma_all_h0_factors_concat(mm, f1, f2);
    lemma_concat_all_distributes(f1, f2);
    lemma_equiv_concat(base_A(), concat_all(f1), w1, concat_all(f2), w2);
    //  concat_all(f) =~= concat(concat_all(f1), concat_all(f2)) ≡ w1·w2
    assert(concat_all(f) =~= concat(concat_all(f1), concat_all(f2)));
    assert(equiv_in_presentation(base_A(), concat_all(f), w1 + w2));
    assert(all_h0_factors(mm, f));
}

//  ============================================================
//  E2 base camp — T(M) is closed under inverse (subgroup property 2/2)
//  ============================================================

//  is_h0_factor is closed under inverse_word:  ±t(a,b) ↦ ∓t(a,b).
pub proof fn lemma_is_h0_factor_inverse(mm: ModMachine, f: Word)
    requires
        is_h0_factor(mm, f),
    ensures
        is_h0_factor(mm, inverse_word(f)),
{
    let ab = choose|a: nat, b: nat| #![trigger config_word(a, b)]
        mm_in_H0(mm, a, b) && (f == config_word(a, b) || f == inverse_word(config_word(a, b)));
    let a = ab.0;
    let b = ab.1;
    assert(mm_in_H0(mm, a, b)
        && (f == config_word(a, b) || f == inverse_word(config_word(a, b))));
    if f != config_word(a, b) {
        crate::word::lemma_inverse_involution(config_word(a, b));   //  inverse_word(inverse_word(cw)) =~= cw
    }
    assert(is_h0_factor(mm, inverse_word(f))) by {
        assert(mm_in_H0(mm, a, b)
            && (inverse_word(f) == config_word(a, b)
                || inverse_word(f) == inverse_word(config_word(a, b))));
    }
}

//  The inverse factorization: reverse the list and invert each factor
//  (so that  inverse_word(g₀·g₁·…·gₙ) = gₙ⁻¹·…·g₀⁻¹).
pub open spec fn inv_rev_factors(factors: Seq<Word>) -> Seq<Word>
    decreases factors.len(),
{
    if factors.len() == 0 {
        Seq::<Word>::empty()
    } else {
        inv_rev_factors(factors.drop_first()) + seq![inverse_word(factors.first())]
    }
}

//  concat_all of the inverse factorization is the inverse of the product.
pub proof fn lemma_concat_all_inverse(factors: Seq<Word>)
    ensures
        inverse_word(concat_all(factors)) =~= concat_all(inv_rev_factors(factors)),
    decreases factors.len(),
{
    reveal_with_fuel(concat_all, 2);
    reveal_with_fuel(inv_rev_factors, 2);
    if factors.len() == 0 {
        lemma_concat_all_empty();
        assert(concat_all(factors) =~= empty_word());
        assert(inverse_word(empty_word()) =~= empty_word());
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        lemma_inverse_word_concat(first, concat_all(rest));
        lemma_concat_all_inverse(rest);
        lemma_concat_all_distributes(inv_rev_factors(rest), seq![inverse_word(first)]);
        lemma_concat_all_singleton(inverse_word(first));
    }
}

//  all_h0_factors is preserved by the inverse factorization.
pub proof fn lemma_all_h0_factors_inv_rev(mm: ModMachine, factors: Seq<Word>)
    requires
        all_h0_factors(mm, factors),
    ensures
        all_h0_factors(mm, inv_rev_factors(factors)),
    decreases factors.len(),
{
    reveal_with_fuel(inv_rev_factors, 2);
    if factors.len() == 0 {
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert(factors[0] == first);
        assert(is_h0_factor(mm, first));
        assert forall|i: int| 0 <= i < rest.len()
            implies is_h0_factor(mm, #[trigger] rest[i]) by {
            assert(rest[i] == factors[i + 1]);
        }
        lemma_all_h0_factors_inv_rev(mm, rest);
        lemma_is_h0_factor_inverse(mm, first);
        let inv1: Seq<Word> = seq![inverse_word(first)];
        assert(all_h0_factors(mm, inv1)) by {
            assert(inv1[0] == inverse_word(first));
        }
        lemma_all_h0_factors_concat(mm, inv_rev_factors(rest), inv1);
    }
}

//  Each H₀ factor is a valid word over A's 3 generators.
pub proof fn lemma_h0_factor_valid(mm: ModMachine, f: Word)
    requires
        is_h0_factor(mm, f),
    ensures
        word_valid(f, 3),
{
    let ab = choose|a: nat, b: nat| #![trigger config_word(a, b)]
        mm_in_H0(mm, a, b) && (f == config_word(a, b) || f == inverse_word(config_word(a, b)));
    lemma_config_word_valid(ab.0, ab.1);
    if f != config_word(ab.0, ab.1) {
        crate::word::lemma_inverse_word_valid(config_word(ab.0, ab.1), 3);
    }
}

//  A finite product of H₀ factors is valid over A's 3 generators.
pub proof fn lemma_concat_all_h0_valid(mm: ModMachine, factors: Seq<Word>)
    requires
        all_h0_factors(mm, factors),
    ensures
        word_valid(concat_all(factors), 3),
    decreases factors.len(),
{
    reveal_with_fuel(concat_all, 2);
    if factors.len() == 0 {
        lemma_concat_all_empty();
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert(factors[0] == first);
        assert(is_h0_factor(mm, first));
        lemma_h0_factor_valid(mm, first);
        assert forall|i: int| 0 <= i < rest.len()
            implies is_h0_factor(mm, #[trigger] rest[i]) by {
            assert(rest[i] == factors[i + 1]);
        }
        lemma_concat_all_h0_valid(mm, rest);
        lemma_concat_word_valid(first, concat_all(rest), 3);
    }
}

//  T(M) is closed under inverse:  w ∈ T(M) ⟹ w⁻¹ ∈ T(M).
pub proof fn lemma_in_T_inverse(mm: ModMachine, w: Word)
    requires
        in_T(mm, w),
        word_valid(w, 3),
    ensures
        in_T(mm, inverse_word(w)),
{
    let factors = choose|f: Seq<Word>|
        #[trigger] all_h0_factors(mm, f) && equiv_in_presentation(base_A(), concat_all(f), w);
    let g = inv_rev_factors(factors);
    lemma_all_h0_factors_inv_rev(mm, factors);
    lemma_concat_all_inverse(factors);
    //  concat_all(g) =~= inverse_word(concat_all(factors)) ≡ inverse_word(w)
    lemma_base_A_valid();
    lemma_concat_all_h0_valid(mm, factors);
    lemma_equiv_inverse(base_A(), concat_all(factors), w);
    assert(concat_all(g) =~= inverse_word(concat_all(factors)));
    assert(equiv_in_presentation(base_A(), concat_all(g), inverse_word(w)));
    assert(all_h0_factors(mm, g));
}

//  ============================================================
//  E2.A — property (vii):  ⟨t, rᵢ, lⱼ⟩ ⊆ ⟨T(M), rᵢ, lⱼ⟩   (the glue direction)
//  ============================================================
//
//  ⟨T(M), rᵢ, lⱼ⟩ is generated by the (infinitely many) H₀ config words together
//  with the (finitely many) stable letters.  Membership = a finite product of
//  signed H₀ config words and signed stable letters, ≡ w in B(M).  The inclusion
//  we need for the faithfulness glue is the forward one: every generator of
//  ⟨t, rᵢ, lⱼ⟩ is already such a factor (t = t(0,0) ∈ T(M) since (0,0) ∈ H₀).

//  The stable letters rᵢ, lⱼ alone (g_subgens minus the leading t).
pub open spec fn stable_subgens(mm: ModMachine) -> Seq<Word> {
    g_subgens(mm).drop_first()
}

//  A signed stable letter.
pub open spec fn is_stable_factor(mm: ModMachine, f: Word) -> bool {
    is_generator_or_inverse(stable_subgens(mm), f)
}

//  A factor of ⟨T(M), rᵢ, lⱼ⟩: a signed H₀ config word or a signed stable letter.
pub open spec fn is_T_stable_factor(mm: ModMachine, f: Word) -> bool {
    is_h0_factor(mm, f) || is_stable_factor(mm, f)
}

pub open spec fn all_T_stable_factors(mm: ModMachine, factors: Seq<Word>) -> bool {
    forall|i: int| 0 <= i < factors.len() ==> is_T_stable_factor(mm, #[trigger] factors[i])
}

//  w ∈ ⟨T(M), rᵢ, lⱼ⟩.
pub open spec fn in_T_stable(mm: ModMachine, w: Word) -> bool {
    exists|factors: Seq<Word>|
        #[trigger] all_T_stable_factors(mm, factors)
        && equiv_in_presentation(b_m(mm), concat_all(factors), w)
}

//  (0,0) ∈ H₀(M) whenever the origin is terminal.
pub proof fn lemma_origin_in_H0(mm: ModMachine)
    requires
        mm_terminal(mm, 0, 0),
    ensures
        mm_in_H0(mm, 0, 0),
{
    reveal_with_fuel(mm_reaches, 1);
    assert(mm_reaches(mm, 0, 0, 0, 0, 0));
}

//  Each generator (or inverse) of ⟨t, rᵢ, lⱼ⟩ is a T-or-stable factor.
pub proof fn lemma_g_subgen_is_T_stable(mm: ModMachine, f: Word)
    requires
        mm_terminal(mm, 0, 0),
        is_generator_or_inverse(g_subgens(mm), f),
    ensures
        is_T_stable_factor(mm, f),
{
    let nq = mm.quads.len();
    let assoc = g_m_associations(mm);
    let tail = Seq::new(nq, |i: int| {
        let g = Symbol::Gen((3 + i) as nat);
        (seq![g], seq![g])
    });
    assert(assoc =~= seq![(seq![Symbol::Gen(0)], seq![Symbol::Gen(0)])] + tail);
    assert(g_subgens(mm).len() == assoc.len());
    assert(assoc.len() == 1 + nq);
    let j = choose|j: int| 0 <= j < g_subgens(mm).len()
        && (f == #[trigger] g_subgens(mm)[j] || f == inverse_word(g_subgens(mm)[j]));
    assert(0 <= j < g_subgens(mm).len()
        && (f == g_subgens(mm)[j] || f == inverse_word(g_subgens(mm)[j])));
    assert(g_subgens(mm)[j] == assoc[j].1);
    if j == 0 {
        //  g_subgens[0] = [t] = config_word(0,0) ∈ T(M)
        assert(assoc[0] == (seq![Symbol::Gen(0)], seq![Symbol::Gen(0)]));
        assert(g_subgens(mm)[0] == seq![Symbol::Gen(0)]);
        lemma_config_word_zero();                       //  config_word(0,0) =~= [Gen0]
        lemma_origin_in_H0(mm);
        let cw0 = config_word(0, 0);
        assert(seq![Symbol::Gen(0)] == cw0);
        if f != g_subgens(mm)[0] {
            assert(f == inverse_word(cw0));
        }
        assert(is_h0_factor(mm, f)) by {
            assert(mm_in_H0(mm, 0, 0) && (f == cw0 || f == inverse_word(cw0)));
        }
    } else {
        //  g_subgens[j] is a stable letter; it equals stable_subgens[j-1].
        let qi = j - 1;
        assert(0 <= qi < nq);
        assert(stable_subgens(mm).len() == nq);
        assert(stable_subgens(mm)[qi] == g_subgens(mm)[j]);   //  drop_first index shift
        assert(is_stable_factor(mm, f)) by {
            assert(0 <= qi < stable_subgens(mm).len()
                && (f == stable_subgens(mm)[qi]
                    || f == inverse_word(stable_subgens(mm)[qi])));
        }
    }
}

//  Property (vii), forward:  w ∈ ⟨t, rᵢ, lⱼ⟩ ⟹ w ∈ ⟨T(M), rᵢ, lⱼ⟩.
pub proof fn lemma_in_gen_implies_in_T_stable(mm: ModMachine, w: Word)
    requires
        mm_terminal(mm, 0, 0),
        in_generated_subgroup(b_m(mm), g_subgens(mm), w),
    ensures
        in_T_stable(mm, w),
{
    let factors = choose|f: Seq<Word>|
        #[trigger] factors_from_generators(g_subgens(mm), f)
        && equiv_in_presentation(b_m(mm), concat_all(f), w);
    assert(all_T_stable_factors(mm, factors)) by {
        assert forall|i: int| 0 <= i < factors.len()
            implies is_T_stable_factor(mm, #[trigger] factors[i]) by {
            assert(is_generator_or_inverse(g_subgens(mm), factors[i]));
            lemma_g_subgen_is_T_stable(mm, factors[i]);
        }
    }
    assert(in_T_stable(mm, w));
}

//  ============================================================
//  E2.C.1 — base case of the property-II induction.
//  ============================================================
//
//  When a ⟨T(M), rᵢ, lⱼ⟩-factorization has been pinched down to NO stable
//  factors — i.e. every factor is an H₀ config word — the product is already an
//  element of T(M).  (The factorization itself witnesses in_T, by reflexivity.)

pub proof fn lemma_all_h0_in_T(mm: ModMachine, factors: Seq<Word>)
    requires
        all_h0_factors(mm, factors),
    ensures
        in_T(mm, concat_all(factors)),
{
    lemma_base_A_valid();
    lemma_concat_all_h0_valid(mm, factors);
    lemma_equiv_refl(base_A(), concat_all(factors));
    assert(all_h0_factors(mm, factors)
        && equiv_in_presentation(base_A(), concat_all(factors), concat_all(factors)));
}

//  ============================================================
//  Free-product structure of A — the foundation for properties (i)–(iii)
//  ============================================================
//
//  A = ⟨t, x, y | xy=yx⟩ is LITERALLY the free product ⟨t⟩ * ⟨x,y|xy=yx⟩:
//  generator t = Gen(0) is the left factor, x=Gen(1),y=Gen(2) the right.  This
//  opens the verified free-product toolbox (injective_left/right, reflects_*) on
//  A, which is exactly what the faithfulness crux (the quad-level HNN isomorphism,
//  paper property (iii)) is built from.

//  Left factor ⟨t⟩ (free, one generator).
pub open spec fn pres_t() -> Presentation {
    Presentation { num_generators: 1, relators: Seq::empty() }
}

//  Right factor ⟨x, y | xy = yx⟩.
pub open spec fn pres_xy() -> Presentation {
    Presentation {
        num_generators: 2,
        relators: seq![ seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(0), Symbol::Inv(1)] ],
    }
}

pub proof fn lemma_pres_t_valid()
    ensures
        presentation_valid(pres_t()),
{
    reveal(presentation_valid);
}

pub proof fn lemma_pres_xy_valid()
    ensures
        presentation_valid(pres_xy()),
{
    reveal(presentation_valid);
    let p = pres_xy();
    assert forall|i: int| 0 <= i < p.relators.len()
        implies word_valid(#[trigger] p.relators[i], p.num_generators)
    by {
        assert(p.relators[i] == seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(0), Symbol::Inv(1)]);
    }
}

//  A is the free product ⟨t⟩ * ⟨x,y|xy=yx⟩, on the nose.
pub proof fn lemma_base_A_is_free_product()
    ensures
        base_A() == free_product(pres_t(), pres_xy()),
{
    let fp = free_product(pres_t(), pres_xy());
    let rxy: Word = seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(0), Symbol::Inv(1)];
    let rA: Word = seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)];
    assert(shift_word(rxy, 1) =~= rA);
    assert(pres_xy().relators.len() == 1 && pres_xy().relators[0] == rxy);
    assert(shift_relators(pres_xy().relators, 1) =~= seq![rA]);
    assert(Seq::<Word>::empty() + shift_relators(pres_xy().relators, 1)
        =~= shift_relators(pres_xy().relators, 1));
    assert(fp.relators =~= base_A().relators);
    assert(fp.num_generators == base_A().num_generators);
    assert(fp == base_A());
}

//  ============================================================
//  Exponent-sum invariant — the bedrock of free-factor triviality
//  ============================================================
//
//  gexp(i, w) = net exponent of generator i in w  (+1 per Gen(i), −1 per Inv(i)).
//  It is preserved by `equiv` whenever every relator has gexp 0 (proved by
//  induction on the derivation), so it DETECTS non-triviality.  Consequence:
//  t = Gen(0) has infinite order in A — tⁿ ≢ ε — the floor under property (i).

pub open spec fn sym_exp(i: nat, s: Symbol) -> int {
    if s == Symbol::Gen(i) { 1 } else if s == Symbol::Inv(i) { -1 } else { 0 }
}

pub open spec fn gexp(i: nat, w: Word) -> int
    decreases w.len(),
{
    if w.len() == 0 { 0 } else { sym_exp(i, w[0]) + gexp(i, w.drop_first()) }
}

pub proof fn lemma_gexp_singleton(i: nat, s: Symbol)
    ensures
        gexp(i, seq![s]) == sym_exp(i, s),
{
    let w: Word = seq![s];
    assert(w.len() == 1);
    assert(w[0] == s);
    assert(w.drop_first() =~= empty_word());
    assert(gexp(i, w) == sym_exp(i, w[0]) + gexp(i, w.drop_first()));
}

pub proof fn lemma_gexp_concat(i: nat, a: Word, b: Word)
    ensures
        gexp(i, a + b) == gexp(i, a) + gexp(i, b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_gexp_concat(i, a.drop_first(), b);
    }
}

//  Inverting a symbol negates its exponent contribution.
pub proof fn lemma_sym_exp_inverse(i: nat, s: Symbol)
    ensures
        sym_exp(i, inverse_symbol(s)) == -sym_exp(i, s),
{
}

pub proof fn lemma_gexp_inverse(i: nat, w: Word)
    ensures
        gexp(i, inverse_word(w)) == -gexp(i, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        lemma_gexp_inverse(i, w.drop_first());
        let tail = Seq::new(1, |_j: int| inverse_symbol(w.first()));
        lemma_gexp_concat(i, inverse_word(w.drop_first()), tail);
        assert(tail =~= seq![inverse_symbol(w.first())]);
        lemma_gexp_singleton(i, inverse_symbol(w.first()));
        lemma_sym_exp_inverse(i, w.first());
        assert(w[0] == w.first());
    }
}

//  A cancelling pair contributes nothing.
pub proof fn lemma_gexp_pair(i: nat, s: Symbol)
    ensures
        gexp(i, seq![s, inverse_symbol(s)]) == 0,
{
    let w: Word = seq![s, inverse_symbol(s)];
    assert(w[0] == s);
    assert(w.drop_first() =~= seq![inverse_symbol(s)]);
    lemma_gexp_singleton(i, inverse_symbol(s));
    lemma_sym_exp_inverse(i, s);
}

//  gexp splits across any subrange boundary.
pub proof fn lemma_gexp_split(i: nat, w: Word, k: int)
    requires
        0 <= k <= w.len(),
    ensures
        gexp(i, w) == gexp(i, w.subrange(0, k)) + gexp(i, w.subrange(k, w.len() as int)),
{
    assert(w =~= w.subrange(0, k) + w.subrange(k, w.len() as int));
    lemma_gexp_concat(i, w.subrange(0, k), w.subrange(k, w.len() as int));
}

//  A constant power scales the exponent.
pub proof fn lemma_gexp_symbol_power(i: nat, s: Symbol, n: nat)
    ensures
        gexp(i, symbol_power(s, n)) == n * sym_exp(i, s),
    decreases n,
{
    if n == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
    } else {
        let np = (n - 1) as nat;
        let e = sym_exp(i, s);
        assert(symbol_power(s, n).len() == n);
        assert(symbol_power(s, n)[0] == s);
        assert(symbol_power(s, n).drop_first() =~= symbol_power(s, np));
        assert(gexp(i, symbol_power(s, n)) == e + gexp(i, symbol_power(s, n).drop_first()));
        lemma_gexp_symbol_power(i, s, np);
        assert(n == np + 1);
        assert((np + 1) * e == e + np * e) by (nonlinear_arith);
    }
}

//  One derivation step preserves gexp, provided every relator has gexp 0.
pub proof fn lemma_apply_step_preserves_gexp(
    p: Presentation, w: Word, w2: Word, step: DerivationStep, i: nat,
)
    requires
        apply_step(p, w, step) == Some(w2),
        forall|j: int| 0 <= j < p.relators.len() ==> gexp(i, #[trigger] p.relators[j]) == 0,
    ensures
        gexp(i, w2) == gexp(i, w),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            let pos = position;
            assert(has_cancellation_at(w, pos));
            assert(w2 == w.subrange(0, pos) + w.subrange(pos + 2, w.len() as int));
            assert(w[pos + 1] == inverse_symbol(w[pos]));
            lemma_gexp_split(i, w, pos);
            let tail = w.subrange(pos, w.len() as int);
            lemma_gexp_split(i, tail, 2);
            assert(tail.subrange(0, 2) =~= seq![w[pos], inverse_symbol(w[pos])]);
            lemma_gexp_pair(i, w[pos]);
            assert(tail.subrange(2, tail.len() as int) =~= w.subrange(pos + 2, w.len() as int));
            lemma_gexp_concat(i, w.subrange(0, pos), w.subrange(pos + 2, w.len() as int));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_k: int| symbol) + Seq::new(1, |_k: int| inverse_symbol(symbol));
            assert(w2 == w.subrange(0, position) + pair + w.subrange(position, w.len() as int));
            assert(pair =~= seq![symbol, inverse_symbol(symbol)]);
            lemma_gexp_pair(i, symbol);
            lemma_gexp_concat(i, w.subrange(0, position) + pair, w.subrange(position, w.len() as int));
            lemma_gexp_concat(i, w.subrange(0, position), pair);
            lemma_gexp_split(i, w, position);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert(w2 == w.subrange(0, position) + r + w.subrange(position, w.len() as int));
            assert(gexp(i, p.relators[relator_index as int]) == 0);
            if inverted {
                lemma_gexp_inverse(i, p.relators[relator_index as int]);
            }
            assert(gexp(i, r) == 0);
            lemma_gexp_concat(i, w.subrange(0, position) + r, w.subrange(position, w.len() as int));
            lemma_gexp_concat(i, w.subrange(0, position), r);
            lemma_gexp_split(i, w, position);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            let rlen = r.len() as int;
            assert(w.subrange(position, position + rlen) == r);
            assert(w2 == w.subrange(0, position) + w.subrange(position + rlen, w.len() as int));
            assert(gexp(i, p.relators[relator_index as int]) == 0);
            if inverted {
                lemma_gexp_inverse(i, p.relators[relator_index as int]);
            }
            assert(gexp(i, r) == 0);
            lemma_gexp_split(i, w, position);
            let tail = w.subrange(position, w.len() as int);
            lemma_gexp_split(i, tail, rlen);
            assert(tail.subrange(0, rlen) =~= r);
            assert(tail.subrange(rlen, tail.len() as int) =~= w.subrange(position + rlen, w.len() as int));
            lemma_gexp_concat(i, w.subrange(0, position), w.subrange(position + rlen, w.len() as int));
        },
    }
}

//  A whole derivation preserves gexp (relators all gexp 0).
pub proof fn lemma_derivation_preserves_gexp(
    p: Presentation, steps: Seq<DerivationStep>, start: Word, end: Word, i: nat,
)
    requires
        derivation_produces(p, steps, start) == Some(end),
        forall|j: int| 0 <= j < p.relators.len() ==> gexp(i, #[trigger] p.relators[j]) == 0,
    ensures
        gexp(i, end) == gexp(i, start),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(start == end);
    } else {
        let first = steps.first();
        match apply_step(p, start, first) {
            Some(next) => {
                lemma_apply_step_preserves_gexp(p, start, next, first, i);
                lemma_derivation_preserves_gexp(p, steps.drop_first(), next, end, i);
            },
            None => {
                assert(false);
            },
        }
    }
}

//  Equivalence preserves gexp (relators all gexp 0).
pub proof fn lemma_equiv_preserves_gexp(p: Presentation, w1: Word, w2: Word, i: nat)
    requires
        equiv_in_presentation(p, w1, w2),
        forall|j: int| 0 <= j < p.relators.len() ==> gexp(i, #[trigger] p.relators[j]) == 0,
    ensures
        gexp(i, w1) == gexp(i, w2),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_derivation_preserves_gexp(p, d.steps, w1, w2, i);
}

//  Every relator of A has zero exponent in every generator.
pub proof fn lemma_base_A_relators_gexp_zero(i: nat)
    ensures
        forall|j: int| 0 <= j < base_A().relators.len()
            ==> gexp(i, #[trigger] base_A().relators[j]) == 0,
{
    reveal_with_fuel(gexp, 5);
    assert(base_A().relators.len() == 1);
    let r = base_A().relators[0];
    assert(r == seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)]);
    assert(gexp(i, r) == sym_exp(i, Symbol::Gen(1)) + sym_exp(i, Symbol::Gen(2))
        + sym_exp(i, Symbol::Inv(1)) + sym_exp(i, Symbol::Inv(2)));
}

//  ★ t = Gen(0) has infinite order in A:  tⁿ ≢ ε for n ≥ 1.  (Property (i)'s floor.)
pub proof fn lemma_t_power_nontrivial(n: nat)
    requires
        n >= 1,
    ensures
        !equiv_in_presentation(base_A(), symbol_power(Symbol::Gen(0), n), empty_word()),
{
    if equiv_in_presentation(base_A(), symbol_power(Symbol::Gen(0), n), empty_word()) {
        lemma_base_A_relators_gexp_zero(0);
        lemma_equiv_preserves_gexp(base_A(), symbol_power(Symbol::Gen(0), n), empty_word(), 0);
        lemma_gexp_symbol_power(0, Symbol::Gen(0), n);
        assert(sym_exp(0, Symbol::Gen(0)) == 1);
        assert(gexp(0, empty_word()) == 0);
        assert(false);
    }
}

//  ============================================================
//  The ℤ² right factor: x and y are independent in A
//  ============================================================

//  Equivalence in A preserves every generator's exponent (A's only relator
//  [x,y] has zero exponent in every generator).
pub proof fn lemma_equiv_in_A_preserves_gexp(i: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(base_A(), w1, w2),
    ensures
        gexp(i, w1) == gexp(i, w2),
{
    lemma_base_A_relators_gexp_zero(i);
    lemma_equiv_preserves_gexp(base_A(), w1, w2, i);
}

//  Every generator has infinite order in A:  Gen(g)ⁿ ≢ ε for n ≥ 1.
//  (t = Gen(0), x = Gen(1), y = Gen(2) are all special cases.)
pub proof fn lemma_gen_power_nontrivial(g: nat, n: nat)
    requires
        n >= 1,
    ensures
        !equiv_in_presentation(base_A(), symbol_power(Symbol::Gen(g), n), empty_word()),
{
    if equiv_in_presentation(base_A(), symbol_power(Symbol::Gen(g), n), empty_word()) {
        lemma_equiv_in_A_preserves_gexp(g, symbol_power(Symbol::Gen(g), n), empty_word());
        lemma_gexp_symbol_power(g, Symbol::Gen(g), n);
        assert(sym_exp(g, Symbol::Gen(g)) == 1);
        assert(gexp(g, empty_word()) == 0);
        assert(false);
    }
}

//  x = Gen(1) and y = Gen(2) are independent:  xᵖ·yᵠ ≡ ε  ⟹  p = q = 0.
pub proof fn lemma_x_pow_y_pow_trivial(p: nat, q: nat)
    requires
        equiv_in_presentation(base_A(),
            symbol_power(Symbol::Gen(1), p) + symbol_power(Symbol::Gen(2), q), empty_word()),
    ensures
        p == 0 && q == 0,
{
    let xp = symbol_power(Symbol::Gen(1), p);
    let yq = symbol_power(Symbol::Gen(2), q);
    let w = xp + yq;
    //  x-exponent reads off p
    lemma_gexp_concat(1, xp, yq);
    lemma_gexp_symbol_power(1, Symbol::Gen(1), p);
    lemma_gexp_symbol_power(1, Symbol::Gen(2), q);
    assert(sym_exp(1, Symbol::Gen(1)) == 1 && sym_exp(1, Symbol::Gen(2)) == 0);
    assert(gexp(1, w) == p);
    lemma_equiv_in_A_preserves_gexp(1, w, empty_word());
    assert(gexp(1, empty_word()) == 0);
    //  y-exponent reads off q
    lemma_gexp_concat(2, xp, yq);
    lemma_gexp_symbol_power(2, Symbol::Gen(1), p);
    lemma_gexp_symbol_power(2, Symbol::Gen(2), q);
    assert(sym_exp(2, Symbol::Gen(1)) == 0 && sym_exp(2, Symbol::Gen(2)) == 1);
    assert(gexp(2, w) == q);
    lemma_equiv_in_A_preserves_gexp(2, w, empty_word());
    assert(gexp(2, empty_word()) == 0);
}

//  ============================================================
//  Property (iii), brick 1: apply_embedding respects image equivalence
//  ============================================================
//
//  Substituting equivalent image words gives equivalent results.  This is the
//  workhorse that lets us replace the quad's a_words by any words equivalent to
//  them (e.g. conjugated/scaled forms) when proving the association isomorphism.

pub proof fn lemma_apply_embedding_respects_image_equiv(
    p: Presentation, images: Seq<Word>, images2: Seq<Word>, w: Word, k: nat,
)
    requires
        images.len() == k,
        images2.len() == k,
        word_valid(w, k),
        presentation_valid(p),
        forall|i: int| 0 <= i < k ==> word_valid(#[trigger] images[i], p.num_generators),
        forall|i: int| 0 <= i < k ==> word_valid(#[trigger] images2[i], p.num_generators),
        forall|i: int| 0 <= i < k ==> equiv_in_presentation(p, #[trigger] images[i], images2[i]),
    ensures
        equiv_in_presentation(p, apply_embedding(images, w), apply_embedding(images2, w)),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_embedding(images, w) =~= empty_word());
        assert(apply_embedding(images2, w) =~= empty_word());
        lemma_equiv_refl(p, apply_embedding(images, w));
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, k)) by { assert(w[0] == s); }
        let head = apply_embedding_symbol(images, s);
        let head2 = apply_embedding_symbol(images2, s);
        //  head ≡ head2
        match s {
            Symbol::Gen(i) => {
                assert(head == images[i as int] && head2 == images2[i as int]);
                assert(0 <= i < k);
                assert(equiv_in_presentation(p, images[i as int], images2[i as int]));
            },
            Symbol::Inv(i) => {
                assert(head == inverse_word(images[i as int]) && head2 == inverse_word(images2[i as int]));
                assert(0 <= i < k);
                lemma_equiv_inverse(p, images[i as int], images2[i as int]);
            },
        }
        assert(equiv_in_presentation(p, head, head2));
        lemma_apply_embedding_respects_image_equiv(p, images, images2, rest, k);
        let tail = apply_embedding(images, rest);
        let tail2 = apply_embedding(images2, rest);
        assert(apply_embedding(images, w) == concat(head, tail));
        assert(apply_embedding(images2, w) == concat(head2, tail2));
        lemma_equiv_concat_left(p, head, head2, tail);
        lemma_equiv_concat_right(p, head2, tail, tail2);
        lemma_equiv_transitive(p, concat(head, tail), concat(head2, tail), concat(head2, tail2));
    }
}

//  ============================================================
//  Property (iii), brick 2: conjugation telescopes through embedding
//  ============================================================

//  Conjugate every image word by g:  imagesᵢ ↦ g⁻¹ · imagesᵢ · g.
pub open spec fn conj_images(g: Word, images: Seq<Word>) -> Seq<Word> {
    Seq::new(images.len(), |i: int| inverse_word(g) + images[i] + g)
}

//  Substituting one symbol through conj_images = g⁻¹ · (image of s) · g.
pub proof fn lemma_apply_embedding_symbol_conj(g: Word, images: Seq<Word>, s: Symbol)
    requires
        generator_index(s) < images.len(),
    ensures
        apply_embedding_symbol(conj_images(g, images), s)
            =~= inverse_word(g) + apply_embedding_symbol(images, s) + g,
{
    let ci = conj_images(g, images);
    match s {
        Symbol::Gen(i) => {
            assert(ci[i as int] == inverse_word(g) + images[i as int] + g);
        },
        Symbol::Inv(i) => {
            assert(ci[i as int] == inverse_word(g) + images[i as int] + g);
            lemma_inverse_word_concat(inverse_word(g) + images[i as int], g);
            lemma_inverse_word_concat(inverse_word(g), images[i as int]);
            crate::word::lemma_inverse_involution(g);
        },
    }
}

//  emb(conj_images(g, images), w)  ≡  g⁻¹ · emb(images, w) · g.
pub proof fn lemma_emb_conj_telescope(
    p: Presentation, g: Word, images: Seq<Word>, w: Word, k: nat,
)
    requires
        images.len() == k,
        word_valid(w, k),
        presentation_valid(p),
        word_valid(g, p.num_generators),
    ensures
        equiv_in_presentation(p, apply_embedding(conj_images(g, images), w),
            inverse_word(g) + apply_embedding(images, w) + g),
    decreases w.len(),
{
    let ci = conj_images(g, images);
    let ig = inverse_word(g);
    if w.len() == 0 {
        assert(apply_embedding(ci, w) =~= empty_word());
        assert(apply_embedding(images, w) =~= empty_word());
        lemma_inverse_word_valid(g, p.num_generators);
        lemma_concat_word_valid(ig, g, p.num_generators);
        lemma_word_inverse_left(p, g);                                   //  ig + g ≡ ε
        lemma_equiv_symmetric(p, ig + g, empty_word());                 //  ε ≡ ig + g
        assert(ig + apply_embedding(images, w) + g =~= ig + g);
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, k)) by { assert(w[0] == s); }
        let m_sym = apply_embedding_symbol(images, s);
        let r = apply_embedding(images, rest);
        let mc = apply_embedding_symbol(ci, s);
        lemma_apply_embedding_symbol_conj(g, images, s);                //  mc =~= ig + m_sym + g
        lemma_emb_conj_telescope(p, g, images, rest, k);               //  emb(ci,rest) ≡ ig + r + g
        assert(apply_embedding(ci, w) == concat(mc, apply_embedding(ci, rest)));
        assert(mc == ig + m_sym + g);
        let big = concat(ig + m_sym + g, ig + r + g);
        //  emb(ci,w) ≡ big   (congruence on the tail with the IH)
        lemma_equiv_concat_right(p, mc, apply_embedding(ci, rest), ig + r + g);
        assert(concat(mc, ig + r + g) == big);
        //  big = (ig+m) (g+ig) (r+g);  delete the middle g+ig ≡ ε
        assert(big =~= (ig + m_sym) + ((g + ig) + (r + g)));
        lemma_word_inverse_right(p, g);                                 //  g + ig ≡ ε
        lemma_delete_equiv_empty(p, ig + m_sym, g + ig, r + g);
        assert((ig + m_sym) + (r + g) =~= ig + apply_embedding(images, w) + g);
        lemma_equiv_transitive(p, apply_embedding(ci, w), big, (ig + m_sym) + (r + g));
    }
}

//  Conjugation preserves triviality:  g⁻¹·W·g ≡ ε  ⟺  W ≡ ε.
pub proof fn lemma_conj_trivial_iff(p: Presentation, g: Word, ww: Word)
    requires
        presentation_valid(p),
        word_valid(g, p.num_generators),
    ensures
        equiv_in_presentation(p, inverse_word(g) + ww + g, empty_word())
        <==> equiv_in_presentation(p, ww, empty_word()),
{
    let ig = inverse_word(g);
    lemma_inverse_word_valid(g, p.num_generators);
    lemma_concat_word_valid(g, ig, p.num_generators);
    //  ⟸ : W ≡ ε  ⟹  ig·W·g ≡ ε   (delete W, then ig·g ≡ ε)
    if equiv_in_presentation(p, ww, empty_word()) {
        lemma_delete_equiv_empty(p, ig, ww, g);
        lemma_word_inverse_left(p, g);
        assert(concat(ig, concat(ww, g)) =~= ig + ww + g);
        assert(concat(ig, g) =~= ig + g);
        lemma_equiv_transitive(p, ig + ww + g, ig + g, empty_word());
    }
    //  ⟹ : ig·W·g ≡ ε  ⟹  W ≡ ε
    if equiv_in_presentation(p, ig + ww + g, empty_word()) {
        lemma_word_inverse_right(p, g);                                 //  g·ig ≡ ε
        //  build  W ≡ (g·ig)·W·(g·ig)  by inserting g·ig ≡ ε at both ends
        lemma_insert_equiv_empty(p, empty_word(), g + ig, ww);
        lemma_insert_equiv_empty(p, g + ig + ww, g + ig, empty_word());
        assert(concat(empty_word(), ww) =~= ww);
        assert(concat(empty_word(), concat(g + ig, ww)) =~= (g + ig) + ww);
        assert(concat(g + ig + ww, empty_word()) =~= (g + ig) + ww);
        assert(concat(g + ig + ww, concat(g + ig, empty_word())) =~= (g + ig) + ww + (g + ig));
        let big_x = (g + ig) + ww + (g + ig);
        lemma_equiv_transitive(p, ww, (g + ig) + ww, big_x);
        //  big_x  =~=  g·(ig·W·g)·ig  ≡  g·ig  ≡  ε
        assert(big_x =~= concat(g, concat(ig + ww + g, ig)));
        lemma_delete_equiv_empty(p, g, ig + ww + g, ig);               //  g·(igWg)·ig ≡ g·ig
        assert(concat(g, ig) =~= g + ig);
        assert(equiv_in_presentation(p, big_x, g + ig));
        lemma_equiv_transitive(p, ww, big_x, g + ig);
        lemma_equiv_transitive(p, ww, g + ig, empty_word());
    }
}

} //  verus!
