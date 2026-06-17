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
use crate::quotient::add_relator;
use crate::tietze::lemma_add_derivable_relator_reverse;
use crate::britton_via_tower::{derivation_min_adj_level, derivation_max_step_level,
    derivation_levels_ok, step_level_ok, step_position, step_is_hnn_relator, net_level,
    lemma_hnn_derivation_to_tower_equiv, lemma_translate_base_word_at, lemma_translate_empty,
    lemma_copy_s_embeds, lemma_tower_textbook_chain_from_hnn_iso, translate_word_at};
use crate::britton_via_tower::{textbook_act_hnn, lemma_no_pinch_action_nontrivial,
    lemma_derivation_preserves_syls, stable_count, lemma_stable_count_concat,
    lemma_stable_count_no_stable, lemma_has_stable_implies_count};
use crate::normal_form_afp_textbook::Syllable;
use crate::tower::tower_presentation;

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
//  ψ_F-injectivity supporting lemmas (F-level / 2-image)
//  ============================================================

//  ψ_F fixes t-words pointwise (the base case of the injectivity peel).
pub proof fn lemma_psi_F_fixes_t_word(p: nat, w: Word)
    requires
        is_t_word(w),
    ensures
        apply_embedding(psi_F_images(p), w) =~= w,
    decreases w.len(),
{
    let imgs = psi_F_images(p);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(s == w[0]);
        assert(s == Symbol::Gen(0) || s == Symbol::Inv(0));
        assert(is_t_word(w.drop_first())) by {
            assert forall|i: int| 0 <= i < w.drop_first().len()
                implies (#[trigger] w.drop_first()[i] == Symbol::Gen(0)
                    || w.drop_first()[i] == Symbol::Inv(0))
            by { assert(w.drop_first()[i] == w[i + 1]); }
        }
        lemma_psi_F_fixes_t_word(p, w.drop_first());
        assert(imgs[0] =~= seq![Symbol::Gen(0)]);
        if s == Symbol::Gen(0) {
            assert(apply_embedding_symbol(imgs, s) =~= seq![Symbol::Gen(0)]);
        } else {
            assert(apply_embedding_symbol(imgs, s) =~= seq![Symbol::Inv(0)]);
        }
        assert(apply_embedding_symbol(imgs, s) =~= seq![s]);
        assert(apply_embedding(imgs, w) =~= seq![s] + apply_embedding(imgs, w.drop_first()));
        assert(w =~= seq![s] + w.drop_first());
    }
}

//  A positive stable count means there really is a stable letter somewhere.
pub proof fn lemma_stable_count_pos_has_stable(data: HNNData, w: Word)
    requires
        stable_count(data, w) >= 1,
    ensures
        has_stable_letter(data, w),
{
    if !has_stable_letter(data, w) {
        assert(forall|k: int| 0 <= k < w.len() ==> !is_stable(data, #[trigger] w[k]));
        lemma_stable_count_no_stable(data, w);
    }
}

//  A valid F-word with no stable letters is a pure t-word.
pub proof fn lemma_stable_count_zero_is_t_word(w: Word)
    requires
        word_valid(w, 2),
        stable_count(f_as_hnn(), w) == 0,
    ensures
        is_t_word(w),
{
    let data = f_as_hnn();
    assert(data.base.num_generators == 1);
    assert(!has_stable_letter(data, w)) by {
        if has_stable_letter(data, w) { lemma_has_stable_implies_count(data, w); }
    }
    assert forall|i: int| 0 <= i < w.len()
        implies (#[trigger] w[i] == Symbol::Gen(0) || w[i] == Symbol::Inv(0))
    by {
        assert(!is_stable(data, w[i]));
        assert(symbol_valid(w[i], 2));
    }
}

//  ============================================================
//  ★ ψ_F IS INJECTIVE ON F ★  (the pieces assembled)
//  ============================================================
//
//  If the p-scaled word ψ_F(w) (t↦t, x↦xᵖ) is trivial in F = ⟨t,x⟩, so is w.
//  Length-induction: a t-word is fixed by ψ_F (base); otherwise ψ_F(w) keeps a
//  stable letter, so (trivial ⟹ Britton-reducible) it has a pinch, which (Corr)
//  pushes back to a pinch in w, which (Q) cancels to a strictly shorter w′ with
//  w ≡ w′ and ψ_F(w′) ≡ ε — then the induction closes.
pub proof fn lemma_psi_F_injective(p: nat, w: Word)
    requires
        word_valid(w, 2),
        p >= 1,
        equiv_in_presentation(pres_tx(), apply_embedding(psi_F_images(p), w), empty_word()),
    ensures
        equiv_in_presentation(pres_tx(), w, empty_word()),
    decreases w.len(),
{
    let data = f_as_hnn();
    let imgs = psi_F_images(p);
    let pw = apply_embedding(imgs, w);
    lemma_f_as_hnn_presentation();
    assert(pres_tx().num_generators == 2);
    assert(presentation_valid(pres_tx())) by { reveal(presentation_valid); }
    //  the two images are valid over 2 generators (they use only t, x)
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    assert forall|k: int| 0 <= k < imgs.len() implies word_valid(#[trigger] imgs[k], 2) by {
        if k == 0 {
            assert forall|m: int| 0 <= m < imgs[0].len() implies symbol_valid(#[trigger] imgs[0][m], 2)
            by { assert(imgs[0][m] == Symbol::Gen(0)); }
        } else {
            lemma_symbol_power_valid(Symbol::Gen(1), p, 2);
        }
    }
    if stable_count(data, w) == 0 {
        //  base case: w is a t-word, fixed by ψ_F
        lemma_stable_count_zero_is_t_word(w);
        lemma_psi_F_fixes_t_word(p, w);
        assert(pw =~= w);
    } else {
        //  step: ψ_F(w) has a stable letter, hence (being trivial) a pinch
        lemma_psi_F_stable_count_scales(p, w);
        assert(stable_count(data, w) >= 1);
        assert(p * stable_count(data, w) >= 1) by (nonlinear_arith)
            requires p >= 1, stable_count(data, w) >= 1;
        assert(stable_count(data, pw) >= 1);
        lemma_stable_count_pos_has_stable(data, pw);
        lemma_apply_embedding_valid(imgs, w, 2);
        lemma_f_as_hnn_valid();
        lemma_f_as_hnn_isomorphic();
        if !has_pinch(data, pw) {
            lemma_no_pinch_stable_nontrivial(data, pw);
        }
        assert(has_pinch(data, pw));
        //  (Corr): the pinch descends to w
        lemma_psi_F_pinch_descends(p, w);
        let ij: (int, int) = choose|i: int, j: int| has_pinch_at(data, w, i, j);
        let i = ij.0;
        let j = ij.1;
        assert(has_pinch_at(data, w, i, j));
        assert(has_adjacent_opposite_at(data, w, i, j));
        let wshort: Word = w.subrange(0, i) + w.subrange(j + 1, w.len() as int);
        //  (Q): pinch-out
        lemma_pinch_out(w, i, j);
        //  wshort is shorter and still valid
        assert(wshort.len() < w.len());
        assert(word_valid(w.subrange(0, i), 2)) by {
            assert forall|k: int| 0 <= k < w.subrange(0, i).len()
                implies symbol_valid(#[trigger] w.subrange(0, i)[k], 2)
            by { assert(w.subrange(0, i)[k] == w[k]); }
        }
        assert(word_valid(w.subrange(j + 1, w.len() as int), 2)) by {
            assert forall|k: int| 0 <= k < w.subrange(j + 1, w.len() as int).len()
                implies symbol_valid(#[trigger] w.subrange(j + 1, w.len() as int)[k], 2)
            by { assert(w.subrange(j + 1, w.len() as int)[k] == w[k + j + 1]); }
        }
        lemma_concat_word_valid(w.subrange(0, i), w.subrange(j + 1, w.len() as int), 2);
        //  ψ_F respects ≡, then transport triviality to ψ_F(wshort)
        let pws = apply_embedding(imgs, wshort);
        lemma_emb_respects_source_equiv(pres_tx(), pres_tx(), imgs, w, wshort);
        lemma_equiv_symmetric(pres_tx(), pw, pws);
        lemma_equiv_transitive(pres_tx(), pws, pw, empty_word());
        //  inductive hypothesis on the shorter word, then close
        lemma_psi_F_injective(p, wshort);
        lemma_equiv_transitive(pres_tx(), w, wshort, empty_word());
    }
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

//  ============================================================
//  Property (iii), A2a foundations: apply_embedding as a homomorphism
//  ============================================================
//
//  Toward "apply_embedding sends source-equivalences to target-equivalences"
//  (the embedding is a homomorphism from the source group when the images
//  satisfy the source relations).  These two stones handle the free-reduction
//  and relator-inverse moves; the full per-step + derivation induction is next.

//  The image of a cancelling pair is trivial:  emb([s, s⁻¹]) ≡ ε.
pub proof fn lemma_emb_inverse_pair_trivial(p: Presentation, images: Seq<Word>, s: Symbol)
    ensures
        equiv_in_presentation(p, apply_embedding(images, seq![s, inverse_symbol(s)]), empty_word()),
{
    reveal_with_fuel(apply_embedding, 3);
    let s2 = inverse_symbol(s);
    let m_sym = apply_embedding_symbol(images, s);
    lemma_apply_embedding_symbol_inverse(images, s);   //  emb_sym(s2) =~= inverse_word(m_sym)
    assert(seq![s, s2].drop_first() =~= seq![s2]);
    assert(seq![s2].drop_first() =~= empty_word());
    assert(apply_embedding(images, seq![s, s2]) =~= m_sym + inverse_word(m_sym));
    lemma_word_inverse_right(p, m_sym);                //  m + m⁻¹ ≡ ε
}

//  If emb(r) ≡ ε then emb(r⁻¹) ≡ ε.
pub proof fn lemma_emb_inverse_word_trivial(p: Presentation, images: Seq<Word>, r: Word)
    requires
        equiv_in_presentation(p, apply_embedding(images, r), empty_word()),
        presentation_valid(p),
        word_valid(apply_embedding(images, r), p.num_generators),
    ensures
        equiv_in_presentation(p, apply_embedding(images, inverse_word(r)), empty_word()),
{
    lemma_apply_embedding_inverse(images, r);   //  emb(inverse_word(r)) =~= inverse_word(emb(r))
    lemma_equiv_inverse(p, apply_embedding(images, r), empty_word());
    assert(inverse_word(empty_word()) =~= empty_word());
}

//  One derivation step in the source maps to an equivalence in the target —
//  provided the images satisfy the source relators.
pub proof fn lemma_emb_step_respects(
    src: Presentation, tgt: Presentation, images: Seq<Word>,
    w: Word, w2: Word, step: DerivationStep,
)
    requires
        apply_step(src, w, step) == Some(w2),
        src.num_generators == images.len(),
        word_valid(w, src.num_generators),
        presentation_valid(src),
        presentation_valid(tgt),
        forall|i: int| 0 <= i < images.len() ==> word_valid(#[trigger] images[i], tgt.num_generators),
        forall|j: int| 0 <= j < src.relators.len()
            ==> equiv_in_presentation(tgt, apply_embedding(images, #[trigger] src.relators[j]), empty_word()),
    ensures
        equiv_in_presentation(tgt, apply_embedding(images, w2), apply_embedding(images, w)),
{
    let k = images.len();
    reveal(presentation_valid);
    match step {
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            let pre = w.subrange(0, position);
            let suf = w.subrange(position, w.len() as int);
            assert(w2 == pre + pair + suf);
            assert(w =~= pre + suf);
            assert(pair =~= seq![symbol, inverse_symbol(symbol)]);
            lemma_emb_inverse_pair_trivial(tgt, images, symbol);
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, pair);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_concat(images, pre + pair, suf);
            lemma_apply_embedding_concat(images, pre, pair);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w2) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w) =~= concat(ep, es));
            lemma_delete_equiv_empty(tgt, ep, ec, es);
        },
        DerivationStep::FreeReduce { position } => {
            let pre = w.subrange(0, position);
            let suf = w.subrange(position + 2, w.len() as int);
            let pair = w.subrange(position, position + 2);
            assert(has_cancellation_at(w, position));
            assert(w[position + 1] == inverse_symbol(w[position]));
            assert(pair =~= seq![w[position], inverse_symbol(w[position])]);
            assert(w =~= pre + pair + suf);
            assert(w2 == pre + suf);
            assert(word_valid(pair, k));
            lemma_emb_inverse_pair_trivial(tgt, images, w[position]);
            lemma_apply_embedding_valid(images, pair, tgt.num_generators);
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, pair);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_concat(images, pre + pair, suf);
            lemma_apply_embedding_concat(images, pre, pair);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w2) =~= concat(ep, es));
            lemma_insert_equiv_empty(tgt, ep, ec, es);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(src, relator_index, inverted);
            let pre = w.subrange(0, position);
            let suf = w.subrange(position, w.len() as int);
            assert(w2 == pre + r + suf);
            assert(w =~= pre + suf);
            assert(word_valid(src.relators[relator_index as int], src.num_generators));
            if inverted {
                lemma_apply_embedding_valid(images, src.relators[relator_index as int], tgt.num_generators);
                lemma_emb_inverse_word_trivial(tgt, images, src.relators[relator_index as int]);
            }
            assert(equiv_in_presentation(tgt, apply_embedding(images, r), empty_word()));
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, r);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_concat(images, pre + r, suf);
            lemma_apply_embedding_concat(images, pre, r);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w2) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w) =~= concat(ep, es));
            lemma_delete_equiv_empty(tgt, ep, ec, es);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(src, relator_index, inverted);
            let rlen = r.len() as int;
            let pre = w.subrange(0, position);
            let suf = w.subrange(position + rlen, w.len() as int);
            assert(w.subrange(position, position + rlen) == r);
            assert(w =~= pre + r + suf);
            assert(w2 == pre + suf);
            assert(word_valid(src.relators[relator_index as int], src.num_generators));
            if inverted {
                lemma_inverse_word_valid(src.relators[relator_index as int], src.num_generators);
                lemma_apply_embedding_valid(images, src.relators[relator_index as int], tgt.num_generators);
                lemma_emb_inverse_word_trivial(tgt, images, src.relators[relator_index as int]);
            }
            assert(equiv_in_presentation(tgt, apply_embedding(images, r), empty_word()));
            assert(word_valid(r, k));
            lemma_apply_embedding_valid(images, r, tgt.num_generators);
            let ep = apply_embedding(images, pre);
            let ec = apply_embedding(images, r);
            let es = apply_embedding(images, suf);
            lemma_apply_embedding_concat(images, pre + r, suf);
            lemma_apply_embedding_concat(images, pre, r);
            lemma_apply_embedding_concat(images, pre, suf);
            assert(apply_embedding(images, w) =~= concat(ep, concat(ec, es)));
            assert(apply_embedding(images, w2) =~= concat(ep, es));
            lemma_insert_equiv_empty(tgt, ep, ec, es);
        },
    }
}

//  A whole source derivation maps to a target equivalence.
pub proof fn lemma_emb_derivation_respects(
    src: Presentation, tgt: Presentation, images: Seq<Word>,
    steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        derivation_produces(src, steps, start) == Some(end),
        src.num_generators == images.len(),
        word_valid(start, src.num_generators),
        presentation_valid(src),
        presentation_valid(tgt),
        forall|i: int| 0 <= i < images.len() ==> word_valid(#[trigger] images[i], tgt.num_generators),
        forall|j: int| 0 <= j < src.relators.len()
            ==> equiv_in_presentation(tgt, apply_embedding(images, #[trigger] src.relators[j]), empty_word()),
    ensures
        equiv_in_presentation(tgt, apply_embedding(images, end), apply_embedding(images, start)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(start == end);
        lemma_equiv_refl(tgt, apply_embedding(images, start));
    } else {
        let first = steps.first();
        match apply_step(src, start, first) {
            Some(next) => {
                lemma_emb_step_respects(src, tgt, images, start, next, first);
                lemma_step_preserves_word_valid_pres(src, start, first, next);
                lemma_emb_derivation_respects(src, tgt, images, steps.drop_first(), next, end);
                lemma_equiv_transitive(tgt, apply_embedding(images, end),
                    apply_embedding(images, next), apply_embedding(images, start));
            },
            None => {
                assert(false);
            },
        }
    }
}

//  ★ apply_embedding is a HOMOMORPHISM from the source group: source-equivalences
//  map to target-equivalences, provided the images satisfy the source relators.
pub proof fn lemma_emb_respects_source_equiv(
    src: Presentation, tgt: Presentation, images: Seq<Word>, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(src, w1, w2),
        src.num_generators == images.len(),
        word_valid(w1, src.num_generators),
        word_valid(w2, src.num_generators),
        presentation_valid(src),
        presentation_valid(tgt),
        forall|i: int| 0 <= i < images.len() ==> word_valid(#[trigger] images[i], tgt.num_generators),
        forall|j: int| 0 <= j < src.relators.len()
            ==> equiv_in_presentation(tgt, apply_embedding(images, #[trigger] src.relators[j]), empty_word()),
    ensures
        equiv_in_presentation(tgt, apply_embedding(images, w1), apply_embedding(images, w2)),
{
    let d = choose|d: Derivation| derivation_valid(src, d, w1, w2);
    lemma_emb_derivation_respects(src, tgt, images, d.steps, w1, w2);
    lemma_apply_embedding_valid(images, w2, tgt.num_generators);
    lemma_equiv_symmetric(tgt, apply_embedding(images, w2), apply_embedding(images, w1));
}

//  ============================================================
//  Property (iii), A2a(b): the abelian normal form (sorting)
//  ============================================================
//
//  A signed power  x^a  (a ∈ ℤ):  Gen(i)ᵃ for a≥0, Inv(i)^|a| for a<0.

pub open spec fn signed_power(i: nat, a: int) -> Word {
    if a >= 0 {
        symbol_power(Symbol::Gen(i), a as nat)
    } else {
        symbol_power(Symbol::Inv(i), (-a) as nat)
    }
}

//  The exponent of a signed power: a in its own generator, 0 in others.
pub proof fn lemma_gexp_signed_power(i: nat, j: nat, a: int)
    ensures
        i == j ==> gexp(j, signed_power(i, a)) == a,
        i != j ==> gexp(j, signed_power(i, a)) == 0,
{
    if a >= 0 {
        lemma_gexp_symbol_power(j, Symbol::Gen(i), a as nat);
        assert(i == j ==> sym_exp(j, Symbol::Gen(i)) == 1);
        assert(i != j ==> sym_exp(j, Symbol::Gen(i)) == 0);
    } else {
        lemma_gexp_symbol_power(j, Symbol::Inv(i), (-a) as nat);
        assert(i == j ==> sym_exp(j, Symbol::Inv(i)) == -1);
        assert(i != j ==> sym_exp(j, Symbol::Inv(i)) == 0);
        assert(i == j ==> (-a) * (-1) == a) by (nonlinear_arith);
    }
}

//  Prepending Gen(i) to x^a gives x^{a+1}  (free reduction when a < 0).
pub proof fn lemma_prepend_gen_signed(p: Presentation, i: nat, a: int)
    ensures
        equiv_in_presentation(p, seq![Symbol::Gen(i)] + signed_power(i, a), signed_power(i, a + 1)),
{
    if a >= 0 {
        assert(seq![Symbol::Gen(i)] + signed_power(i, a) =~= signed_power(i, a + 1));
        lemma_equiv_refl(p, signed_power(i, a + 1));
    } else {
        let n = (-a) as nat;   //  ≥ 1
        let inv: Word = seq![Symbol::Gen(i), Symbol::Inv(i)];
        assert(seq![Symbol::Gen(i)] + signed_power(i, a)
            =~= inv + symbol_power(Symbol::Inv(i), (n - 1) as nat));
        lemma_cancel_pair_equiv_empty(p, Symbol::Gen(i), Symbol::Inv(i));
        lemma_delete_equiv_empty(p, empty_word(), inv, symbol_power(Symbol::Inv(i), (n - 1) as nat));
        assert(concat(empty_word(), concat(inv, symbol_power(Symbol::Inv(i), (n - 1) as nat)))
            =~= inv + symbol_power(Symbol::Inv(i), (n - 1) as nat));
        assert(concat(empty_word(), symbol_power(Symbol::Inv(i), (n - 1) as nat))
            =~= symbol_power(Symbol::Inv(i), (n - 1) as nat));
        assert(signed_power(i, a + 1) =~= symbol_power(Symbol::Inv(i), (n - 1) as nat));
    }
}

//  Prepending Inv(i) to x^a gives x^{a-1}.
pub proof fn lemma_prepend_inv_signed(p: Presentation, i: nat, a: int)
    ensures
        equiv_in_presentation(p, seq![Symbol::Inv(i)] + signed_power(i, a), signed_power(i, a - 1)),
{
    if a <= 0 {
        assert(seq![Symbol::Inv(i)] + signed_power(i, a) =~= signed_power(i, a - 1));
        lemma_equiv_refl(p, signed_power(i, a - 1));
    } else {
        let n = a as nat;   //  ≥ 1
        let inv: Word = seq![Symbol::Inv(i), Symbol::Gen(i)];
        assert(seq![Symbol::Inv(i)] + signed_power(i, a)
            =~= inv + symbol_power(Symbol::Gen(i), (n - 1) as nat));
        lemma_cancel_pair_equiv_empty(p, Symbol::Inv(i), Symbol::Gen(i));
        lemma_delete_equiv_empty(p, empty_word(), inv, symbol_power(Symbol::Gen(i), (n - 1) as nat));
        assert(concat(empty_word(), concat(inv, symbol_power(Symbol::Gen(i), (n - 1) as nat)))
            =~= inv + symbol_power(Symbol::Gen(i), (n - 1) as nat));
        assert(concat(empty_word(), symbol_power(Symbol::Gen(i), (n - 1) as nat))
            =~= symbol_power(Symbol::Gen(i), (n - 1) as nat));
        assert(signed_power(i, a - 1) =~= symbol_power(Symbol::Gen(i), (n - 1) as nat));
    }
}

//  ============================================================
//  The four x/y commuting variants (all from A's [x,y] relator),
//  then: a y-symbol commutes past xᵃ (signed).
//  ============================================================

//  y·x ~ x·y  (symmetric of lemma_xy_commute_in_A).
pub proof fn lemma_comm_y_x()
    ensures
        equiv_in_presentation(base_A(), seq![Symbol::Gen(2), Symbol::Gen(1)],
            seq![Symbol::Gen(1), Symbol::Gen(2)]),
{
    let a = base_A();
    let xy: Word = seq![Symbol::Gen(1), Symbol::Gen(2)];
    let yx: Word = seq![Symbol::Gen(2), Symbol::Gen(1)];
    lemma_base_A_valid();
    lemma_xy_commute_in_A();
    assert(word_valid(xy, 3)) by {
        assert forall|i: int| 0 <= i < xy.len() implies symbol_valid(#[trigger] xy[i], 3) by {}
    }
    lemma_equiv_symmetric(a, xy, yx);
}

//  y·x⁻¹ ~ x⁻¹·y  (the mixed variant, via two free cancellations from y·x ~ x·y).
pub proof fn lemma_comm_y_xinv()
    ensures
        equiv_in_presentation(base_A(), seq![Symbol::Gen(2), Symbol::Inv(1)],
            seq![Symbol::Inv(1), Symbol::Gen(2)]),
{
    let a = base_A();
    lemma_base_A_valid();
    let x = Symbol::Gen(1); let y = Symbol::Gen(2); let xi = Symbol::Inv(1);
    let yx: Word = seq![y, x];
    let xy: Word = seq![x, y];
    let xip: Word = seq![xi];
    let yw: Word = seq![y];
    let xix: Word = seq![xi, x];
    let xxi: Word = seq![x, xi];
    let xiyx: Word = seq![xi, y, x];
    let xixy: Word = seq![xi, x, y];
    let xiy: Word = seq![xi, y];
    let yxi: Word = seq![y, xi];
    let xiyxxi: Word = seq![xi, y, x, xi];
    //  Fact A:  y·x ~ x·y
    lemma_comm_y_x();
    //  1. prepend x⁻¹:  [xi,y,x] ~ [xi,x,y]
    lemma_equiv_concat_right(a, xip, yx, xy);
    assert(xip + yx =~= xiyx);
    assert(xip + xy =~= xixy);
    //  2. [xi,x,y] ~ [y]   (cancel xi·x)
    lemma_cancel_pair_equiv_empty(a, xi, x);
    lemma_delete_equiv_empty(a, empty_word(), xix, yw);
    assert(concat(xix, yw) =~= xixy);
    assert(concat(empty_word(), xixy) =~= xixy);
    assert(concat(empty_word(), yw) =~= yw);
    //  3. xiyx ~ xixy ~ y
    lemma_equiv_transitive(a, xiyx, xixy, yw);
    //  4. append x⁻¹:  [xi,y,x,xi] ~ [y,xi]
    lemma_equiv_concat_left(a, xiyx, yw, xip);
    assert(xiyx + xip =~= xiyxxi);
    assert(yw + xip =~= yxi);
    //  5. [xi,y,x,xi] ~ [xi,y]   (cancel x·xi)
    lemma_cancel_pair_equiv_empty(a, x, xi);
    lemma_delete_equiv_empty(a, xiy, xxi, empty_word());
    assert(concat(xxi, empty_word()) =~= xxi);
    assert(concat(xiy, xxi) =~= xiyxxi);
    assert(concat(xiy, empty_word()) =~= xiy);
    //  6. symmetric of 4 + transitivity:  [y,xi] ~ [xi,y,x,xi] ~ [xi,y]
    assert(word_valid(xiyxxi, 3)) by {
        assert forall|i: int| 0 <= i < xiyxxi.len() implies symbol_valid(#[trigger] xiyxxi[i], 3) by {}
    }
    lemma_equiv_symmetric(a, xiyxxi, yxi);
    lemma_equiv_transitive(a, yxi, xiyxxi, xiy);
}

//  y⁻¹·x ~ x·y⁻¹  (inverse of the mixed variant).
pub proof fn lemma_comm_yinv_x()
    ensures
        equiv_in_presentation(base_A(), seq![Symbol::Inv(2), Symbol::Gen(1)],
            seq![Symbol::Gen(1), Symbol::Inv(2)]),
{
    let a = base_A();
    lemma_base_A_valid();
    let yxi: Word = seq![Symbol::Gen(2), Symbol::Inv(1)];
    let xiy: Word = seq![Symbol::Inv(1), Symbol::Gen(2)];
    let giv: Word = seq![Symbol::Gen(1), Symbol::Inv(2)];
    let ivg: Word = seq![Symbol::Inv(2), Symbol::Gen(1)];
    lemma_comm_y_xinv();   //  equiv(a, yxi, xiy)
    assert(word_valid(yxi, 3)) by {
        assert forall|i: int| 0 <= i < yxi.len() implies symbol_valid(#[trigger] yxi[i], 3) by {}
    }
    assert(word_valid(xiy, 3)) by {
        assert forall|i: int| 0 <= i < xiy.len() implies symbol_valid(#[trigger] xiy[i], 3) by {}
    }
    lemma_equiv_inverse(a, yxi, xiy);
    lemma_inverse_word_two(Symbol::Gen(2), Symbol::Inv(1));   //  inv(yxi) =~= giv
    lemma_inverse_word_two(Symbol::Inv(1), Symbol::Gen(2));   //  inv(xiy) =~= ivg
    assert(inverse_word(yxi) =~= giv);
    assert(inverse_word(xiy) =~= ivg);
    assert(word_valid(giv, 3)) by {
        assert forall|i: int| 0 <= i < giv.len() implies symbol_valid(#[trigger] giv[i], 3) by {}
    }
    lemma_equiv_symmetric(a, giv, ivg);
}

//  A y-symbol (Gen(2) or Inv(2)) commutes past  xᵃ = signed_power(1, a).
pub proof fn lemma_commute_ysym_past_xpow(s: Symbol, a: int)
    requires
        s == Symbol::Gen(2) || s == Symbol::Inv(2),
    ensures
        equiv_in_presentation(base_A(), seq![s] + signed_power(1, a), signed_power(1, a) + seq![s]),
{
    let aa = base_A();
    if a >= 0 {
        assert(signed_power(1, a) == symbol_power(Symbol::Gen(1), a as nat));
        if s == Symbol::Gen(2) {
            lemma_comm_y_x();
        } else {
            lemma_comm_yinv_x();
        }
        lemma_sym_commutes_power(aa, s, Symbol::Gen(1), a as nat);
    } else {
        assert(signed_power(1, a) == symbol_power(Symbol::Inv(1), (-a) as nat));
        if s == Symbol::Gen(2) {
            lemma_comm_y_xinv();
        } else {
            lemma_xinv_yinv_commute_in_A();
        }
        lemma_sym_commutes_power(aa, s, Symbol::Inv(1), (-a) as nat);
    }
}

//  A word using only x,y (and inverses).
pub open spec fn is_xy_word(w: Word) -> bool {
    forall|i: int| 0 <= i < w.len()
        ==> (generator_index(#[trigger] w[i]) == 1 || generator_index(w[i]) == 2)
}

//  THE ABELIAN SORT: any {x,y}-word ~ its normal form  x^{net-x} · y^{net-y}.
pub proof fn lemma_z_word_sorts(w: Word)
    requires
        is_xy_word(w),
    ensures
        equiv_in_presentation(base_A(), w,
            signed_power(1, gexp(1, w)) + signed_power(2, gexp(2, w))),
    decreases w.len(),
{
    let a = base_A();
    lemma_base_A_valid();
    let target = signed_power(1, gexp(1, w)) + signed_power(2, gexp(2, w));
    if w.len() == 0 {
        assert(gexp(1, w) == 0);
        assert(gexp(2, w) == 0);
        assert(signed_power(1, 0) =~= empty_word());
        assert(signed_power(2, 0) =~= empty_word());
        assert(target =~= w);
        lemma_equiv_refl(a, w);
    } else {
        let s = w[0];
        let rest = w.drop_first();
        assert(w =~= seq![s] + rest);
        assert(is_xy_word(rest)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies (generator_index(#[trigger] rest[i]) == 1 || generator_index(rest[i]) == 2)
            by { assert(rest[i] == w[i + 1]); }
        }
        lemma_z_word_sorts(rest);                 //  IH
        let aA = gexp(1, rest);
        let bB = gexp(2, rest);
        let sp1 = signed_power(1, aA);
        let sp2 = signed_power(2, bB);
        assert(gexp(1, w) == sym_exp(1, s) + aA);
        assert(gexp(2, w) == sym_exp(2, s) + bB);
        assert(generator_index(s) == 1 || generator_index(s) == 2);
        //  w ~ [s] + (sp1 + sp2)
        lemma_equiv_concat_right(a, seq![s], rest, sp1 + sp2);
        if generator_index(s) == 1 {
            //  x-case: merge [s] into sp1 (gexp(2,w) unchanged)
            assert(sym_exp(2, s) == 0);
            assert(gexp(2, w) == bB);
            let sp1n = signed_power(1, gexp(1, w));
            assert(seq![s] + (sp1 + sp2) =~= (seq![s] + sp1) + sp2);
            if s == Symbol::Gen(1) {
                lemma_prepend_gen_signed(a, 1, aA);
                assert(gexp(1, w) == aA + 1);
            } else {
                assert(s == Symbol::Inv(1));
                lemma_prepend_inv_signed(a, 1, aA);
                assert(gexp(1, w) == aA - 1);
            }
            assert(equiv_in_presentation(a, seq![s] + sp1, sp1n));
            lemma_equiv_concat_left(a, seq![s] + sp1, sp1n, sp2);
            assert(target =~= sp1n + sp2);
            lemma_equiv_transitive(a, w, (seq![s] + sp1) + sp2, sp1n + sp2);
        } else {
            //  y-case: commute [s] past sp1, then merge into sp2 (gexp(1,w) unchanged)
            assert(sym_exp(1, s) == 0);
            assert(gexp(1, w) == aA);
            assert(s == Symbol::Gen(2) || s == Symbol::Inv(2));
            let sp2n = signed_power(2, gexp(2, w));
            lemma_commute_ysym_past_xpow(s, aA);          //  [s]+sp1 ~ sp1+[s]
            if s == Symbol::Gen(2) {
                lemma_prepend_gen_signed(a, 2, bB);
                assert(gexp(2, w) == bB + 1);
            } else {
                lemma_prepend_inv_signed(a, 2, bB);
                assert(gexp(2, w) == bB - 1);
            }
            assert(equiv_in_presentation(a, seq![s] + sp2, sp2n));
            assert(seq![s] + (sp1 + sp2) =~= (seq![s] + sp1) + sp2);
            lemma_equiv_concat_left(a, seq![s] + sp1, sp1 + seq![s], sp2);
            assert((sp1 + seq![s]) + sp2 =~= sp1 + (seq![s] + sp2));
            lemma_equiv_concat_right(a, sp1, seq![s] + sp2, sp2n);
            assert(target =~= sp1 + sp2n);
            lemma_equiv_transitive(a, w, (seq![s] + sp1) + sp2, (sp1 + seq![s]) + sp2);
            lemma_equiv_transitive(a, w, (sp1 + seq![s]) + sp2, sp1 + sp2n);
        }
    }
}

//  ============================================================
//  A2a(c): the abelian word problem ⟹ μ (x↦xᵖ, y↦yᵠ) injective
//  ============================================================

//  Zero net exponents ⟹ the {x,y}-word is trivial (immediate from the sort).
pub proof fn lemma_xy_word_zero_exp_trivial(w: Word)
    requires
        is_xy_word(w),
        gexp(1, w) == 0,
        gexp(2, w) == 0,
    ensures
        equiv_in_presentation(base_A(), w, empty_word()),
{
    let a = base_A();
    lemma_z_word_sorts(w);
    assert(signed_power(1, 0) =~= empty_word());
    assert(signed_power(2, 0) =~= empty_word());
    assert(signed_power(1, gexp(1, w)) + signed_power(2, gexp(2, w)) =~= empty_word());
}

//  gexp₁ of a scaled embedding scales by p.
pub proof fn lemma_gexp1_scaled_embedding(images: Seq<Word>, p: nat, q: nat, w: Word)
    requires
        images.len() >= 3,
        images[1] == symbol_power(Symbol::Gen(1), p),
        images[2] == symbol_power(Symbol::Gen(2), q),
        is_xy_word(w),
    ensures
        gexp(1, apply_embedding(images, w)) == (p as int) * gexp(1, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_embedding(images, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(is_xy_word(rest)) by {
            assert forall|j: int| 0 <= j < rest.len()
                implies (generator_index(#[trigger] rest[j]) == 1 || generator_index(rest[j]) == 2)
            by { assert(rest[j] == w[j + 1]); }
        }
        lemma_gexp1_scaled_embedding(images, p, q, rest);
        let es = apply_embedding_symbol(images, s);
        assert(apply_embedding(images, w) =~= concat(es, apply_embedding(images, rest)));
        lemma_gexp_concat(1, es, apply_embedding(images, rest));
        assert(generator_index(s) == 1 || generator_index(s) == 2);
        assert(gexp(1, es) == (p as int) * sym_exp(1, s)) by {
            if s == Symbol::Gen(1) {
                lemma_gexp_symbol_power(1, Symbol::Gen(1), p);
            } else if s == Symbol::Inv(1) {
                lemma_gexp_symbol_power(1, Symbol::Gen(1), p);
                lemma_gexp_inverse(1, symbol_power(Symbol::Gen(1), p));
                assert((p as int) * sym_exp(1, Symbol::Inv(1)) == -(p as int)) by (nonlinear_arith);
                assert(-((p as int) * sym_exp(1, Symbol::Gen(1))) == -(p as int)) by (nonlinear_arith);
            } else if s == Symbol::Gen(2) {
                lemma_gexp_symbol_power(1, Symbol::Gen(2), q);
                assert(sym_exp(1, Symbol::Gen(2)) == 0);
                assert((q as int) * 0 == 0) by (nonlinear_arith);
                assert((p as int) * 0 == 0) by (nonlinear_arith);
            } else {
                assert(s == Symbol::Inv(2));
                lemma_gexp_symbol_power(1, Symbol::Gen(2), q);
                lemma_gexp_inverse(1, symbol_power(Symbol::Gen(2), q));
                assert(sym_exp(1, Symbol::Gen(2)) == 0);
                assert(sym_exp(1, Symbol::Inv(2)) == 0);
                assert((q as int) * 0 == 0) by (nonlinear_arith);
                assert((p as int) * 0 == 0) by (nonlinear_arith);
            }
        }
        assert(gexp(1, w) == sym_exp(1, s) + gexp(1, rest));
        assert((p as int) * sym_exp(1, s) + (p as int) * gexp(1, rest)
            == (p as int) * (sym_exp(1, s) + gexp(1, rest))) by (nonlinear_arith);
    }
}

//  gexp₂ of a scaled embedding scales by q.
pub proof fn lemma_gexp2_scaled_embedding(images: Seq<Word>, p: nat, q: nat, w: Word)
    requires
        images.len() >= 3,
        images[1] == symbol_power(Symbol::Gen(1), p),
        images[2] == symbol_power(Symbol::Gen(2), q),
        is_xy_word(w),
    ensures
        gexp(2, apply_embedding(images, w)) == (q as int) * gexp(2, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_embedding(images, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(is_xy_word(rest)) by {
            assert forall|j: int| 0 <= j < rest.len()
                implies (generator_index(#[trigger] rest[j]) == 1 || generator_index(rest[j]) == 2)
            by { assert(rest[j] == w[j + 1]); }
        }
        lemma_gexp2_scaled_embedding(images, p, q, rest);
        let es = apply_embedding_symbol(images, s);
        assert(apply_embedding(images, w) =~= concat(es, apply_embedding(images, rest)));
        lemma_gexp_concat(2, es, apply_embedding(images, rest));
        assert(generator_index(s) == 1 || generator_index(s) == 2);
        assert(gexp(2, es) == (q as int) * sym_exp(2, s)) by {
            if s == Symbol::Gen(2) {
                lemma_gexp_symbol_power(2, Symbol::Gen(2), q);
            } else if s == Symbol::Inv(2) {
                lemma_gexp_symbol_power(2, Symbol::Gen(2), q);
                lemma_gexp_inverse(2, symbol_power(Symbol::Gen(2), q));
                assert((q as int) * sym_exp(2, Symbol::Inv(2)) == -(q as int)) by (nonlinear_arith);
                assert(-((q as int) * sym_exp(2, Symbol::Gen(2))) == -(q as int)) by (nonlinear_arith);
            } else if s == Symbol::Gen(1) {
                lemma_gexp_symbol_power(2, Symbol::Gen(1), p);
                assert(sym_exp(2, Symbol::Gen(1)) == 0);
                assert((p as int) * 0 == 0) by (nonlinear_arith);
                assert((q as int) * 0 == 0) by (nonlinear_arith);
            } else {
                assert(s == Symbol::Inv(1));
                lemma_gexp_symbol_power(2, Symbol::Gen(1), p);
                lemma_gexp_inverse(2, symbol_power(Symbol::Gen(1), p));
                assert(sym_exp(2, Symbol::Gen(1)) == 0);
                assert(sym_exp(2, Symbol::Inv(1)) == 0);
                assert((p as int) * 0 == 0) by (nonlinear_arith);
                assert((q as int) * 0 == 0) by (nonlinear_arith);
            }
        }
        assert(gexp(2, w) == sym_exp(2, s) + gexp(2, rest));
        assert((q as int) * sym_exp(2, s) + (q as int) * gexp(2, rest)
            == (q as int) * (sym_exp(2, s) + gexp(2, rest))) by (nonlinear_arith);
    }
}

//  μ injective: a scaled {x,y}-word trivial ⟹ the original is trivial.
pub proof fn lemma_mu_injective(images: Seq<Word>, p: nat, q: nat, w: Word)
    requires
        images.len() >= 3,
        images[1] == symbol_power(Symbol::Gen(1), p),
        images[2] == symbol_power(Symbol::Gen(2), q),
        p >= 1,
        q >= 1,
        is_xy_word(w),
        equiv_in_presentation(base_A(), apply_embedding(images, w), empty_word()),
    ensures
        equiv_in_presentation(base_A(), w, empty_word()),
{
    let emb = apply_embedding(images, w);
    lemma_gexp1_scaled_embedding(images, p, q, w);
    lemma_gexp2_scaled_embedding(images, p, q, w);
    lemma_equiv_in_A_preserves_gexp(1, emb, empty_word());
    lemma_equiv_in_A_preserves_gexp(2, emb, empty_word());
    assert(gexp(1, empty_word()) == 0);
    assert(gexp(2, empty_word()) == 0);
    //  p·gexp(1,w) == 0  and  p ≥ 1  ⟹  gexp(1,w) == 0
    assert(gexp(1, w) == 0) by (nonlinear_arith)
        requires (p as int) * gexp(1, w) == 0, p >= 1;
    assert(gexp(2, w) == 0) by (nonlinear_arith)
        requires (q as int) * gexp(2, w) == 0, q >= 1;
    lemma_xy_word_zero_exp_trivial(w);
}

//  ============================================================
//  A2b via Britton: A viewed as an HNN extension
//  ============================================================
//
//  A = ⟨t,x,y | xy=yx⟩ is an HNN extension of the free group F = ⟨t,x⟩ with
//  stable letter y and associated subgroup ⟨x⟩ under the IDENTITY iso
//  (y⁻¹·x·y = x).  So the proven britton_lemma_full applies to A, and its
//  isomorphism precondition is trivial (identity, as at the k-level in brick 22).
//  hnn_presentation(a_as_hnn) = ⟨t,x,y | y⁻¹xyx⁻¹⟩ — Tietze-equivalent to base_A
//  (bridge: the two single relators are mutually derivable).

//  The free group ⟨t, x⟩ (the HNN base).
pub open spec fn pres_tx() -> Presentation {
    Presentation { num_generators: 2, relators: Seq::empty() }
}

//  A as an HNN extension: base ⟨t,x⟩, stable letter y=Gen(2), ⟨x⟩ identity iso.
pub open spec fn a_as_hnn() -> HNNData {
    HNNData {
        base: pres_tx(),
        associations: seq![ (seq![Symbol::Gen(1)], seq![Symbol::Gen(1)]) ],
    }
}

pub proof fn lemma_a_as_hnn_valid()
    ensures
        hnn_data_valid(a_as_hnn()),
{
    reveal(presentation_valid);
    let data = a_as_hnn();
    assert(data.base.relators.len() == 0);
    let w: Word = seq![Symbol::Gen(1)];
    assert(word_valid(w, 2)) by {
        assert forall|j: int| 0 <= j < w.len() implies symbol_valid(#[trigger] w[j], 2) by {}
    }
    assert forall|i: int| 0 <= i < data.associations.len() implies {
        &&& word_valid(#[trigger] data.associations[i].0, data.base.num_generators)
        &&& word_valid(data.associations[i].1, data.base.num_generators)
    } by {
        assert(data.associations[i] == (w, w));
    }
}

//  The iso condition is trivial: the association is the identity on ⟨x⟩.
pub proof fn lemma_a_as_hnn_isomorphic()
    ensures
        hnn_associations_isomorphic(a_as_hnn()),
{
    let data = a_as_hnn();
    let k = data.associations.len();
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    assert forall|i: int| 0 <= i < k implies
        data.associations[i].0 == data.associations[i].1
    by {
        assert(data.associations[0] == (seq![Symbol::Gen(1)], seq![Symbol::Gen(1)]));
    }
    assert(a_words =~= b_words);
}

//  The HNN presentation of A has 3 generators and the single relator y⁻¹xyx⁻¹.
pub proof fn lemma_a_as_hnn_presentation()
    ensures
        hnn_presentation(a_as_hnn()).num_generators == 3,
        hnn_presentation(a_as_hnn()).relators.len() == 1,
        hnn_presentation(a_as_hnn()).relators[0]
            =~= seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1)],
{
    lemma_a_as_hnn_valid();
    let data = a_as_hnn();
    assert(data.base.relators.len() == 0);
    assert(hnn_relators(data).len() == 1);
    assert(hnn_presentation(data).relators[0] == hnn_relator(data, 0));
    assert(Seq::new(1, |_j: int| Symbol::Inv(2)) =~= seq![Symbol::Inv(2)]);
    assert(Seq::new(1, |_j: int| Symbol::Gen(2)) =~= seq![Symbol::Gen(2)]);
    assert(inverse_word(seq![Symbol::Gen(1)]) =~= seq![Symbol::Inv(1)]) by {
        reveal_with_fuel(inverse_word, 2);
    }
}

//  ============================================================
//  Tietze bridge:  equiv in base_A  ⟺  equiv in the HNN presentation of A.
//  The two single relators xyx⁻¹y⁻¹ and y⁻¹xyx⁻¹ are conjugate, hence mutually
//  derivable, so the two presentations have identical equivalence.
//  ============================================================

//  R_H = y⁻¹xyx⁻¹ is trivial in base_A (a conjugate of base_A's relator xyx⁻¹y⁻¹).
pub proof fn lemma_rh_trivial_in_base_A()
    ensures
        equiv_in_presentation(base_A(),
            seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1)], empty_word()),
{
    let a = base_A();
    lemma_base_A_valid();
    let ra: Word = seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)];
    let rh: Word = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1)];
    let conj: Word = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1),
        Symbol::Inv(2), Symbol::Gen(2)];
    assert(a.relators[0] == ra);
    lemma_conjugate_relator_is_identity(a, seq![Symbol::Inv(2)], 0);
    assert(inverse_word(seq![Symbol::Inv(2)]) =~= seq![Symbol::Gen(2)]) by {
        reveal_with_fuel(inverse_word, 2);
    }
    assert(concat(concat(seq![Symbol::Inv(2)], a.relators[0]), inverse_word(seq![Symbol::Inv(2)]))
        =~= conj);
    assert(equiv_in_presentation(a, conj, empty_word()));
    //  conj freely reduces to rh: cancel the Inv2·Gen2 pair at positions 4,5.
    assert(has_cancellation_at(conj, 4)) by {
        assert(conj[4] == Symbol::Inv(2) && conj[5] == Symbol::Gen(2));
    }
    assert(reduce_at(conj, 4) =~= rh);
    assert(reduces_one_step(conj, rh)) by {
        assert(has_cancellation_at(conj, 4) && rh == reduce_at(conj, 4));
    }
    assert(reduces_in_steps(conj, rh, 1)) by {
        assert(reduces_one_step(conj, rh) && reduces_in_steps(rh, rh, 0));
    }
    assert(reduces_to(conj, rh));
    lemma_reduces_to_equiv(a, conj, rh);
    assert(word_valid(conj, 3)) by {
        assert forall|i: int| 0 <= i < conj.len() implies symbol_valid(#[trigger] conj[i], 3) by {}
    }
    lemma_equiv_symmetric(a, conj, rh);
    lemma_equiv_transitive(a, rh, conj, empty_word());
}

//  R_A = xyx⁻¹y⁻¹ is trivial in A's HNN presentation (a conjugate of y⁻¹xyx⁻¹).
pub proof fn lemma_ra_trivial_in_a_hnn()
    ensures
        equiv_in_presentation(hnn_presentation(a_as_hnn()),
            seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)], empty_word()),
{
    let data = a_as_hnn();
    let p = hnn_presentation(data);
    lemma_a_as_hnn_valid();
    lemma_hnn_presentation_valid(data);
    lemma_a_as_hnn_presentation();
    let ra: Word = seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)];
    let rh: Word = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1)];
    let conj: Word = seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(2),
        Symbol::Inv(1), Symbol::Inv(2)];
    assert(p.relators[0] =~= rh);
    lemma_conjugate_relator_is_identity(p, seq![Symbol::Gen(2)], 0);
    assert(inverse_word(seq![Symbol::Gen(2)]) =~= seq![Symbol::Inv(2)]) by {
        reveal_with_fuel(inverse_word, 2);
    }
    assert(concat(concat(seq![Symbol::Gen(2)], p.relators[0]), inverse_word(seq![Symbol::Gen(2)]))
        =~= conj);
    assert(equiv_in_presentation(p, conj, empty_word()));
    //  conj freely reduces to ra: cancel the Gen2·Inv2 pair at positions 0,1.
    assert(has_cancellation_at(conj, 0)) by {
        assert(conj[0] == Symbol::Gen(2) && conj[1] == Symbol::Inv(2));
    }
    assert(reduce_at(conj, 0) =~= ra);
    assert(reduces_one_step(conj, ra)) by {
        assert(has_cancellation_at(conj, 0) && ra == reduce_at(conj, 0));
    }
    assert(reduces_in_steps(conj, ra, 1)) by {
        assert(reduces_one_step(conj, ra) && reduces_in_steps(ra, ra, 0));
    }
    assert(reduces_to(conj, ra));
    lemma_reduces_to_equiv(p, conj, ra);
    assert(word_valid(conj, 3)) by {
        assert forall|i: int| 0 <= i < conj.len() implies symbol_valid(#[trigger] conj[i], 3) by {}
    }
    lemma_equiv_symmetric(p, conj, ra);
    lemma_equiv_transitive(p, ra, conj, empty_word());
}

//  Transport: equiv in base_A ⟹ equiv in A's HNN presentation.
pub proof fn lemma_base_A_to_a_hnn(w1: Word, w2: Word)
    requires
        equiv_in_presentation(base_A(), w1, w2),
        word_valid(w1, 3),
    ensures
        equiv_in_presentation(hnn_presentation(a_as_hnn()), w1, w2),
{
    let a = base_A();
    let p = hnn_presentation(a_as_hnn());
    lemma_base_A_valid();
    lemma_a_as_hnn_valid();
    lemma_hnn_presentation_valid(a_as_hnn());
    lemma_a_as_hnn_presentation();
    let ra: Word = seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)];
    let p_ha = add_relator(p, ra);
    //  p_ha = ⟨3 | [rh, ra]⟩ includes base_A's relator ra at index 1.
    assert(p_ha.relators.len() == 2);
    assert(p_ha.relators[1] == ra);
    assert(a.relators[0] == ra);
    assert(relators_included(a, p_ha)) by {
        assert forall|i: int| 0 <= i < a.relators.len() implies
            exists|j: int| 0 <= j < p_ha.relators.len() && p_ha.relators[j] == #[trigger] a.relators[i]
        by { assert(p_ha.relators[1] == a.relators[0]); }
    }
    lemma_relator_inclusion_preserves_equiv(a, p_ha, w1, w2);
    lemma_ra_trivial_in_a_hnn();
    assert(word_valid(ra, 3)) by {
        assert forall|i: int| 0 <= i < ra.len() implies symbol_valid(#[trigger] ra[i], 3) by {}
    }
    lemma_add_derivable_relator_reverse(p, ra, w1, w2);
}

//  Transport: equiv in A's HNN presentation ⟹ equiv in base_A.
pub proof fn lemma_a_hnn_to_base_A(w1: Word, w2: Word)
    requires
        equiv_in_presentation(hnn_presentation(a_as_hnn()), w1, w2),
        word_valid(w1, 3),
    ensures
        equiv_in_presentation(base_A(), w1, w2),
{
    let a = base_A();
    let p = hnn_presentation(a_as_hnn());
    lemma_base_A_valid();
    lemma_a_as_hnn_valid();
    lemma_hnn_presentation_valid(a_as_hnn());
    lemma_a_as_hnn_presentation();
    let rh: Word = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1)];
    let p_ah = add_relator(a, rh);
    //  p_ah = ⟨3 | [ra, rh]⟩ includes the HNN relator rh at index 1.
    assert(p_ah.relators.len() == 2);
    assert(p_ah.relators[1] == rh);
    assert(p.relators[0] =~= rh);
    assert(relators_included(p, p_ah)) by {
        assert forall|i: int| 0 <= i < p.relators.len() implies
            exists|j: int| 0 <= j < p_ah.relators.len() && p_ah.relators[j] == #[trigger] p.relators[i]
        by { assert(p_ah.relators[1] == p.relators[0]); }
    }
    lemma_relator_inclusion_preserves_equiv(p, p_ah, w1, w2);
    lemma_rh_trivial_in_base_A();
    assert(word_valid(rh, 3)) by {
        assert forall|i: int| 0 <= i < rh.len() implies symbol_valid(#[trigger] rh[i], 3) by {}
    }
    lemma_add_derivable_relator_reverse(a, rh, w1, w2);
}

//  ============================================================
//  ψ_{p,q} : A → A,  t↦t, x↦xᵖ, y↦yᵠ  is a WELL-DEFINED endomorphism
//  (the scaling map of property (iii); injectivity for p,q≥1 is the A2b crux).
//  ============================================================

//  The substitution images of ψ_{p,q}:  Gen0↦t, Gen1↦xᵖ, Gen2↦yᵠ.
pub open spec fn psi_images(p: nat, q: nat) -> Seq<Word> {
    seq![ seq![Symbol::Gen(0)], symbol_power(Symbol::Gen(1), p), symbol_power(Symbol::Gen(2), q) ]
}

//  ψ respects A's relator: ψ(xyx⁻¹y⁻¹) = xᵖyᵠx⁻ᵖy⁻ᵠ ≡ ε (the powers commute).
//  This makes ψ a homomorphism A→A (usable with lemma_emb_respects_source_equiv),
//  giving the easy direction emb(images,w)≡ε ⟸ w≡ε of the L2 isomorphism.
pub proof fn lemma_psi_respects_relator(p: nat, q: nat)
    ensures
        equiv_in_presentation(base_A(),
            apply_embedding(psi_images(p, q), base_A().relators[0]), empty_word()),
{
    let a = base_A();
    lemma_base_A_valid();
    let imgs = psi_images(p, q);
    let xp = symbol_power(Symbol::Gen(1), p);
    let yq = symbol_power(Symbol::Gen(2), q);
    let xinv = symbol_power(Symbol::Inv(1), p);
    let yinv = symbol_power(Symbol::Inv(2), q);
    assert(a.relators[0] == seq![Symbol::Gen(1), Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(2)]);
    assert(imgs[1] == xp && imgs[2] == yq);
    lemma_inverse_word_sympower(Symbol::Gen(1), p);
    lemma_inverse_word_sympower(Symbol::Gen(2), q);
    assert(inverse_word(xp) =~= xinv);
    assert(inverse_word(yq) =~= yinv);
    //  ψ(R_A) = xᵖ · yᵠ · x⁻ᵖ · y⁻ᵠ
    let psra = apply_embedding(imgs, a.relators[0]);
    assert(psra =~= xp + yq + xinv + yinv) by {
        reveal_with_fuel(apply_embedding, 5);
    }
    //  the cancellation chain
    lemma_xy_commute_in_A();
    lemma_power_commutes(a, Symbol::Gen(1), Symbol::Gen(2), p, q);   //  xᵖyᵠ ~ yᵠxᵖ
    let suf: Word = xinv + yinv;
    lemma_equiv_concat_left(a, xp + yq, yq + xp, suf);              //  (xᵖyᵠ)·suf ~ (yᵠxᵖ)·suf
    lemma_word_inverse_right(a, xp);
    assert(equiv_in_presentation(a, xp + xinv, empty_word())) by {
        assert(concat(xp, inverse_word(xp)) =~= xp + xinv);
    }
    lemma_delete_equiv_empty(a, yq, xp + xinv, yinv);              //  yᵠ(xᵖx⁻ᵖ)y⁻ᵠ ~ yᵠy⁻ᵠ
    lemma_word_inverse_right(a, yq);
    assert(equiv_in_presentation(a, yq + yinv, empty_word())) by {
        assert(concat(yq, inverse_word(yq)) =~= yq + yinv);
    }
    //  assemble: psra == (xᵖyᵠ)suf ~ (yᵠxᵖ)suf == yᵠ(xᵖx⁻ᵖ)y⁻ᵠ ~ yᵠy⁻ᵠ ~ ε
    assert((xp + yq) + suf =~= psra);
    assert((yq + xp) + suf =~= yq + ((xp + xinv) + yinv));
    assert(concat(yq, yinv) =~= yq + yinv);
    lemma_equiv_transitive(a, yq + ((xp + xinv) + yinv), yq + yinv, empty_word());
    lemma_equiv_transitive(a, (xp + yq) + suf, (yq + xp) + suf, empty_word());
}

//  ============================================================
//  Single-HNN base faithfulness (property I) — built by generalizing
//  britton_via_tower::britton_lemma to a free base_level = -min_adj, so a
//  derivation that dips below the base is shifted up into the tower; we land
//  via lemma_copy_s_embeds (copy s) instead of the copy-0 embedding.
//  ============================================================

//  The min adjusted level is ≤ 0 (the recursion bottoms out at 0 and takes mins).
proof fn lemma_min_adj_nonpos(data: HNNData, steps: Seq<DerivationStep>, start: Word)
    ensures
        derivation_min_adj_level(data, steps, start) <= 0,
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        match apply_step(hnn_presentation(data), start, steps.first()) {
            Some(next) => { lemma_min_adj_nonpos(data, steps.drop_first(), next); },
            None => {},
        }
    }
}

//  The max step level is ≥ 0 (bottoms at 0 and takes maxes).
proof fn lemma_max_step_nonneg(data: HNNData, steps: Seq<DerivationStep>, start: Word)
    ensures
        derivation_max_step_level(data, steps, start) >= 0,
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        match apply_step(hnn_presentation(data), start, steps.first()) {
            Some(next) => { lemma_max_step_nonneg(data, steps.drop_first(), next); },
            None => {},
        }
    }
}

//  Replication of the (private) britton_via_tower bounds helper: a high-enough
//  tower with a base_level above the dip makes every step's level legal.
proof fn lemma_levels_ok_from_bounds(
    data: HNNData, m: nat, base_level: int, steps: Seq<DerivationStep>, start: Word,
)
    requires
        derivation_produces(hnn_presentation(data), steps, start) is Some,
        base_level >= -derivation_min_adj_level(data, steps, start),
        m as int >= derivation_max_step_level(data, steps, start) + base_level,
    ensures
        derivation_levels_ok(data, m, base_level, steps, start),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let hp = hnn_presentation(data);
        let step = steps.first();
        let next = apply_step(hp, start, step).unwrap();
        let pos = step_position(step);
        let level = net_level(data, start.subrange(0, pos));
        let adj = if step_is_hnn_relator(data, step) { level - 1 } else { level };
        let rest_min = derivation_min_adj_level(data, steps.drop_first(), next);
        let rest_max = derivation_max_step_level(data, steps.drop_first(), next);
        assert(adj >= derivation_min_adj_level(data, steps, start));
        assert(level <= derivation_max_step_level(data, steps, start));
        assert(rest_min >= derivation_min_adj_level(data, steps, start)) by {
            if adj < rest_min {} else {}
        }
        assert(rest_max <= derivation_max_step_level(data, steps, start)) by {
            if level > rest_max {} else {}
        }
        lemma_levels_ok_from_bounds(data, m, base_level, steps.drop_first(), next);
    }
}

//  Property I: a base word trivial in the HNN extension is trivial in the base.
pub proof fn lemma_single_hnn_base_faithful(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let ng = data.base.num_generators;
    let d: Derivation = choose|d: Derivation| derivation_valid(hp, d, w, empty_word());
    assert(derivation_valid(hp, d, w, empty_word()));
    let steps = d.steps;
    assert(derivation_produces(hp, steps, w) == Some(empty_word()));
    //  level bounds
    lemma_min_adj_nonpos(data, steps, w);
    lemma_max_step_nonneg(data, steps, w);
    let min_adj = derivation_min_adj_level(data, steps, w);
    let max_lvl = derivation_max_step_level(data, steps, w);
    let base_level: int = -min_adj;
    assert(base_level >= 0);
    let m: nat = (max_lvl + base_level) as nat;
    assert(max_lvl + base_level >= 0);
    assert(m as int == max_lvl + base_level);
    //  w valid over the (larger) HNN presentation
    assert(ng <= hp.num_generators);
    lemma_word_valid_mono(w, ng, hp.num_generators);
    //  discharge the level fit, the textbook chain, and lift the derivation to the tower
    lemma_levels_ok_from_bounds(data, m, base_level, steps, w);
    lemma_tower_textbook_chain_from_hnn_iso(data, m);
    lemma_hnn_derivation_to_tower_equiv(data, m, base_level, steps, w, empty_word());
    //  translate(w, base_level) = shift_word(w, base_level·ng); translate(ε) = ε
    lemma_translate_base_word_at(data, w, base_level as nat);
    lemma_translate_empty(data);
    assert((base_level as nat) as int == base_level);
    assert(translate_word_at(data, w, base_level) =~= shift_word(w, (base_level as nat) * ng));
    assert(translate_word_at(data, empty_word(), base_level) =~= empty_word());
    //  equiv(tower(m), shift_word(w, base_level·ng), ε); descend via the copy-s embedding
    assert(equiv_in_presentation(tower_presentation(data, m),
        shift_word(w, (base_level as nat) * ng), empty_word()));
    assert((base_level as nat) <= m);
    lemma_copy_s_embeds(data, m, base_level as nat, w);
}

//  ============================================================
//  F = ⟨t,x⟩ as an HNN extension of ⟨t⟩ (stable letter x, trivial associated
//  subgroup / empty associations) — the lower level of the double-HNN peel.
//  ============================================================

pub open spec fn f_as_hnn() -> HNNData {
    HNNData { base: pres_t(), associations: Seq::empty() }
}

pub proof fn lemma_f_as_hnn_valid()
    ensures
        hnn_data_valid(f_as_hnn()),
{
    lemma_pres_t_valid();
}

pub proof fn lemma_f_as_hnn_isomorphic()
    ensures
        hnn_associations_isomorphic(f_as_hnn()),
{
    //  empty associations: a_words == b_words == [], so the iff is reflexive.
    let data = f_as_hnn();
    let a_words = Seq::new(0nat as int as nat, |i: int| data.associations[i].0);
    assert forall|w: Word| word_valid(w, 0nat) implies (
        equiv_in_presentation(data.base,
            apply_embedding(Seq::new(0, |i: int| data.associations[i].0), w), empty_word())
        <==>
        equiv_in_presentation(data.base,
            apply_embedding(Seq::new(0, |i: int| data.associations[i].1), w), empty_word())
    ) by {
        assert(Seq::new(0, |i: int| data.associations[i].0)
            =~= Seq::new(0, |i: int| data.associations[i].1));
    }
}

//  The HNN presentation of f_as_hnn is exactly the free group ⟨t,x⟩ = pres_tx.
pub proof fn lemma_f_as_hnn_presentation()
    ensures
        hnn_presentation(f_as_hnn()) == pres_tx(),
{
    let data = f_as_hnn();
    assert(hnn_relators(data).len() == 0);
    assert(hnn_presentation(data).relators =~= pres_tx().relators);
    assert(hnn_presentation(data).num_generators == 2);
}

//  Base faithfulness F → ⟨t⟩: a t-word trivial in F = ⟨t,x⟩ is trivial in ⟨t⟩.
pub proof fn lemma_f_base_faithful(w: Word)
    requires
        word_valid(w, 1),
        equiv_in_presentation(pres_tx(), w, empty_word()),
    ensures
        equiv_in_presentation(pres_t(), w, empty_word()),
{
    lemma_f_as_hnn_valid();
    lemma_f_as_hnn_isomorphic();
    lemma_f_as_hnn_presentation();
    lemma_single_hnn_base_faithful(f_as_hnn(), w);
}

//  A word over only t = Gen(0) / t⁻¹ = Inv(0).
pub open spec fn is_t_word(w: Word) -> bool {
    forall|i: int| 0 <= i < w.len()
        ==> (#[trigger] w[i] == Symbol::Gen(0) || w[i] == Symbol::Inv(0))
}

//  ψ fixes t-words pointwise (t ↦ t, and t-words use no x or y) — the base case
//  of the ψ-injectivity peel and the (trivial) middle-correspondence at the
//  F-level, where pinch middles lie in the trivial ⟨t⟩ associated subgroup.
pub proof fn lemma_psi_fixes_t_word(p: nat, q: nat, w: Word)
    requires
        is_t_word(w),
    ensures
        apply_embedding(psi_images(p, q), w) =~= w,
    decreases w.len(),
{
    let imgs = psi_images(p, q);
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(s == w[0]);
        assert(s == Symbol::Gen(0) || s == Symbol::Inv(0));
        assert(is_t_word(w.drop_first())) by {
            assert forall|i: int| 0 <= i < w.drop_first().len() implies
                (#[trigger] w.drop_first()[i] == Symbol::Gen(0) || w.drop_first()[i] == Symbol::Inv(0))
            by { assert(w.drop_first()[i] == w[i + 1]); }
        }
        lemma_psi_fixes_t_word(p, q, w.drop_first());
        reveal_with_fuel(inverse_word, 2);
        reveal_with_fuel(apply_embedding, 2);
        assert(imgs[0] =~= seq![Symbol::Gen(0)]);
        assert(apply_embedding_symbol(imgs, s) =~= seq![s]) by {
            if s == Symbol::Inv(0) {
                assert(inverse_word(imgs[0]) =~= seq![Symbol::Inv(0)]);
            }
        }
        assert(apply_embedding(imgs, w)
            =~= concat(seq![s], apply_embedding(imgs, w.drop_first())));
        assert(w =~= seq![s] + w.drop_first());
    }
}

//  Contrapositive of Britton's lemma: a Britton-reduced word (no pinch) that
//  still contains a stable letter is NONTRIVIAL.  The engine of the
//  ψ-injectivity peel — a scaled word that stays reduced cannot vanish.
pub proof fn lemma_no_pinch_stable_nontrivial(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, hnn_presentation(data).num_generators),
        has_stable_letter(data, w),
        !has_pinch(data, w),
    ensures
        !equiv_in_presentation(hnn_presentation(data), w, empty_word()),
{
    if equiv_in_presentation(hnn_presentation(data), w, empty_word()) {
        britton_lemma_full(data, w);
        assert(has_pinch(data, w));   //  contradicts !has_pinch
    }
}

//  ============================================================
//  Britton normal-form syllable interface (for the ψ-injectivity peel)
//  ============================================================
//
//  textbook_act_hnn(data, w, ε, []).1 is the Britton normal-form syllable list.
//  It is an ≡-invariant; the peel reasons about its length (= stable_count for a
//  reduced word), which ψ scales but never zeroes.

pub open spec fn act_syls(data: HNNData, w: Word) -> Seq<Syllable> {
    textbook_act_hnn(data, w, empty_word(), Seq::<Syllable>::empty()).1
}

//  A word trivial in the HNN extension has NO normal-form syllables.
pub proof fn lemma_trivial_implies_syls_empty(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, hnn_presentation(data).num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        act_syls(data, w) =~= Seq::<Syllable>::empty(),
{
    let d = choose|d: Derivation| derivation_valid(hnn_presentation(data), d, w, empty_word());
    lemma_derivation_preserves_syls(data, d.steps, w);
}

//  A Britton-reduced word (no pinch) that still has a stable letter has ≥1
//  normal-form syllable — hence (with the previous lemma) is nontrivial.
pub proof fn lemma_reduced_stable_implies_syls_nonempty(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        has_stable_letter(data, w),
        !has_pinch(data, w),
    ensures
        act_syls(data, w).len() >= 1,
{
    lemma_no_pinch_action_nontrivial(data, w);
}

//  In the trivial subgroup (no generators), only the identity lives.
pub proof fn lemma_in_empty_subgroup_trivial(p: Presentation, w: Word)
    requires
        presentation_valid(p),
        in_generated_subgroup(p, Seq::<Word>::empty(), w),
    ensures
        equiv_in_presentation(p, w, empty_word()),
{
    let factors = choose|factors: Seq<Word>|
        #[trigger] factors_from_generators(Seq::<Word>::empty(), factors)
        && equiv_in_presentation(p, concat_all(factors), w);
    assert(factors.len() == 0) by {
        if factors.len() > 0 {
            assert(is_generator_or_inverse(Seq::<Word>::empty(), factors[0]));
        }
    }
    assert(concat_all(factors) =~= empty_word());
    lemma_equiv_symmetric(p, concat_all(factors), w);
}

//  ============================================================
//  (Corr) foundation: ψ_F scales the stable-letter count by p.
//  ============================================================
//
//  The F-level scaling ψ_F: t ↦ t, x ↦ xᵖ  (images over F's two generators).
pub open spec fn psi_F_images(p: nat) -> Seq<Word> {
    seq![ seq![Symbol::Gen(0)], symbol_power(Symbol::Gen(1), p) ]
}

//  stable_count of a constant power: n if the symbol is stable, else 0.
pub proof fn lemma_stable_count_symbol_power(data: HNNData, s: Symbol, n: nat)
    ensures
        stable_count(data, symbol_power(s, n)) == (if is_stable(data, s) { n } else { 0nat }),
    decreases n,
{
    if n == 0 {
        assert(symbol_power(s, n) =~= Seq::<Symbol>::empty());
    } else {
        assert(symbol_power(s, n).last() == s);
        assert(symbol_power(s, n).drop_last() =~= symbol_power(s, (n - 1) as nat));
        lemma_stable_count_symbol_power(data, s, (n - 1) as nat);
    }
}

//  ψ_F applied to a single symbol contributes p stable letters iff the symbol
//  was an x/x⁻¹ (stable), else 0.
pub proof fn lemma_psi_F_emb_symbol_stable_count(p: nat, s: Symbol)
    requires
        symbol_valid(s, 2),
    ensures
        stable_count(f_as_hnn(),
            apply_embedding(psi_F_images(p), seq![s]))
            == (if is_stable(f_as_hnn(), s) { p } else { 0nat }),
{
    let data = f_as_hnn();
    let imgs = psi_F_images(p);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    reveal_with_fuel(stable_count, 2);
    assert(data.base.num_generators == 1);
    assert(apply_embedding(imgs, seq![s]) =~= apply_embedding_symbol(imgs, s));
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    //  symbol_valid(s, 2) ⟹ generator_index(s) ∈ {0, 1}
    match s {
        Symbol::Gen(i) => {
            if i == 0 {
                assert(apply_embedding_symbol(imgs, s) =~= seq![Symbol::Gen(0)]);
                assert(!is_stable(data, s));
            } else {
                assert(i == 1);
                lemma_stable_count_symbol_power(data, Symbol::Gen(1), p);
                assert(apply_embedding_symbol(imgs, s) =~= symbol_power(Symbol::Gen(1), p));
                assert(is_stable(data, s));
            }
        }
        Symbol::Inv(i) => {
            if i == 0 {
                assert(apply_embedding_symbol(imgs, s) =~= seq![Symbol::Inv(0)]);
                assert(!is_stable(data, s));
            } else {
                assert(i == 1);
                lemma_inverse_word_sympower(Symbol::Gen(1), p);
                assert(apply_embedding_symbol(imgs, s) =~= symbol_power(Symbol::Inv(1), p));
                lemma_stable_count_symbol_power(data, Symbol::Inv(1), p);
                assert(is_stable(data, s));
            }
        }
    }
}

//  ψ_F multiplies the stable-letter count by p — so w has an x iff ψ_F(w) does.
pub proof fn lemma_psi_F_stable_count_scales(p: nat, w: Word)
    requires
        word_valid(w, 2),
    ensures
        stable_count(f_as_hnn(), apply_embedding(psi_F_images(p), w))
            == p * stable_count(f_as_hnn(), w),
    decreases w.len(),
{
    let data = f_as_hnn();
    let imgs = psi_F_images(p);
    if w.len() == 0 {
        assert(apply_embedding(imgs, w) =~= Seq::<Symbol>::empty());
    } else {
        let last = w.last();
        let pre = w.drop_last();
        assert(w =~= pre + seq![last]);
        assert(word_valid(pre, 2)) by {
            assert forall|k: int| 0 <= k < pre.len() implies symbol_valid(#[trigger] pre[k], 2)
            by { assert(pre[k] == w[k]); }
        }
        assert(symbol_valid(last, 2));
        lemma_apply_embedding_concat(imgs, pre, seq![last]);
        assert(apply_embedding(imgs, w)
            =~= apply_embedding(imgs, pre) + apply_embedding(imgs, seq![last]));
        lemma_stable_count_concat(data,
            apply_embedding(imgs, pre), apply_embedding(imgs, seq![last]));
        lemma_psi_F_emb_symbol_stable_count(p, last);
        lemma_psi_F_stable_count_scales(p, pre);
        //  extract the if-else value so nonlinear_arith stays linear in `inc`
        let inc: nat = if is_stable(data, last) { 1nat } else { 0nat };
        assert(stable_count(data, w) == stable_count(data, pre) + inc) by {
            reveal_with_fuel(stable_count, 2);
        }
        assert(stable_count(data, apply_embedding(imgs, seq![last])) == p * inc) by {
            if is_stable(data, last) { } else { }
        }
        assert(p * (stable_count(data, pre) + inc)
            == p * stable_count(data, pre) + p * inc) by (nonlinear_arith);
        //  assemble: stable_count(ψ_F(w)) = p·stable_count(pre) + p·inc = p·stable_count(w)
        assert(stable_count(data, apply_embedding(imgs, w))
            == p * stable_count(data, pre) + p * inc);
        assert(stable_count(data, apply_embedding(imgs, w)) == p * stable_count(data, w));
    }
}

//  ============================================================
//  (Corr) core support: prepending a symbol preserves a pinch.
//  ============================================================
//
//  A pinch at (i,j) in w is still a pinch at (i+1,j+1) in [s]·w: the prepended
//  symbol sits at position 0, strictly before both endpoints, so it disturbs
//  neither the adjacency/opposition nor the (unchanged) middle.
pub proof fn lemma_prepend_preserves_pinch(data: HNNData, s: Symbol, w: Word)
    requires
        has_pinch(data, w),
    ensures
        has_pinch(data, seq![s] + w),
{
    let w2: Word = seq![s] + w;
    let ij: (int, int) = choose|i: int, j: int| has_pinch_at(data, w, i, j);
    let i = ij.0;
    let j = ij.1;
    assert(has_pinch_at(data, w, i, j));
    //  index shift: w2[k+1] == w[k]
    assert(forall|k: int| 0 <= k < w.len() ==> #[trigger] w2[k + 1] == w[k]);
    //  middle is preserved verbatim
    assert(w2.subrange(i + 2, j + 1) =~= w.subrange(i + 1, j));
    //  no stable letter strictly between the shifted endpoints
    assert forall|k: int| (i + 1) < k < (j + 1) implies !is_stable(data, #[trigger] w2[k]) by {
        assert(w2[k] == w[k - 1]);
    }
    assert(has_pinch_at(data, w2, i + 1, j + 1));
    assert(has_pinch(data, w2)) by {
        assert(has_pinch_at(data, w2, i + 1, j + 1));
    }
}

//  First-stable correspondence: if the first stable letter of ψ_F(w) is at
//  position l (everything before it non-stable), then w has its first stable
//  letter at the SAME index l, with the same letter, and the prefixes agree.
//  (Leading t-symbols expand 1:1, so the index is preserved; the first x's run
//  starts exactly at l and its first letter is the x itself.)
pub proof fn lemma_psi_F_spanning(p: nat, w: Word, l: int)
    requires
        word_valid(w, 2),
        p >= 1,
        0 <= l < apply_embedding(psi_F_images(p), w).len(),
        is_stable(f_as_hnn(), apply_embedding(psi_F_images(p), w)[l]),
        forall|k: int| 0 <= k < l
            ==> !is_stable(f_as_hnn(), #[trigger] apply_embedding(psi_F_images(p), w)[k]),
    ensures
        l < w.len(),
        is_stable(f_as_hnn(), w[l]),
        w[l] == apply_embedding(psi_F_images(p), w)[l],
        w.subrange(0, l) =~= apply_embedding(psi_F_images(p), w).subrange(0, l),
        forall|k: int| 0 <= k < l ==> !is_stable(f_as_hnn(), #[trigger] w[k]),
    decreases w.len(),
{
    let data = f_as_hnn();
    let imgs = psi_F_images(p);
    let pw = apply_embedding(imgs, w);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    assert(data.base.num_generators == 1);
    assert(w.len() > 0) by {
        if w.len() == 0 { assert(apply_embedding(imgs, w) =~= Seq::<Symbol>::empty()); }
    }
    let c = w[0];
    let w2 = w.drop_first();
    assert(w =~= seq![c] + w2);
    assert(word_valid(w2, 2)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], 2)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(imgs, seq![c], w2);
    let ec = apply_embedding(imgs, seq![c]);
    let pw2 = apply_embedding(imgs, w2);
    assert(pw =~= ec + pw2);
    assert(ec =~= apply_embedding_symbol(imgs, c));
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    if is_stable(data, c) {
        //  c is x/x⁻¹: ec is the length-p run, ec[0] = c is stable, so l must be 0
        assert(c == Symbol::Gen(1) || c == Symbol::Inv(1));
        if c == Symbol::Gen(1) {
            assert(ec =~= symbol_power(Symbol::Gen(1), p));
        } else {
            lemma_inverse_word_sympower(Symbol::Gen(1), p);
            assert(ec =~= symbol_power(Symbol::Inv(1), p));
        }
        assert(ec =~= symbol_power(c, p));
        assert(ec.len() == p);
        assert(ec[0] == c);
        assert(pw[0] == c);
        assert(l == 0);
        assert(w.subrange(0, 0) =~= pw.subrange(0, 0));
    } else {
        //  c is t/t⁻¹: ec = [c] (length 1, non-stable); peel it and recurse
        assert(ec =~= seq![c]);
        assert(ec.len() == 1);
        assert(pw[0] == c);
        assert(!is_stable(data, pw[0]));
        assert(l >= 1);
        assert(forall|m: int| 1 <= m < pw.len() ==> #[trigger] pw[m] == pw2[m - 1]);
        assert(is_stable(data, pw2[l - 1]));
        assert forall|k: int| 0 <= k < l - 1 implies !is_stable(data, #[trigger] pw2[k]) by {
            assert(pw2[k] == pw[k + 1]);
        }
        lemma_psi_F_spanning(p, w2, l - 1);
        //  reassemble for w
        assert(w[l] == w2[l - 1]);
        assert(w.subrange(0, l) =~= seq![c] + w2.subrange(0, l - 1));
        assert(pw.subrange(0, l) =~= seq![c] + pw2.subrange(0, l - 1));
        assert(w.subrange(0, l) =~= pw.subrange(0, l));
        assert forall|k: int| 0 <= k < l implies !is_stable(data, #[trigger] w[k]) by {
            if k != 0 { assert(w[k] == w2[k - 1]); }
        }
    }
}

//  A pinch whose left endpoint lies past a prefix descends to the suffix.
pub proof fn lemma_strip_prefix_preserves_pinch(data: HNNData, pre: Word, suf: Word, i: int, j: int)
    requires
        has_pinch_at(data, pre + suf, i, j),
        pre.len() <= i,
    ensures
        has_pinch(data, suf),
{
    let w2: Word = pre + suf;
    let pl = pre.len() as int;
    let i2 = i - pl;
    let j2 = j - pl;
    //  index shift on the suffix side
    assert(forall|k: int| pl <= k < w2.len() ==> #[trigger] w2[k] == suf[k - pl]);
    assert(suf.subrange(i2 + 1, j2) =~= w2.subrange(i + 1, j));
    assert forall|k: int| i2 < k < j2 implies !is_stable(data, #[trigger] suf[k]) by {
        assert(suf[k] == w2[k + pl]);
    }
    assert(has_pinch_at(data, suf, i2, j2));
    assert(has_pinch(data, suf)) by {
        assert(has_pinch_at(data, suf, i2, j2));
    }
}

//  ============================================================
//  (Corr) CORE: a pinch in ψ_F(w) descends to a pinch in w.
//  ============================================================
//
//  Structural induction on w. With w = c·w', ψ_F(w) = E(c)·ψ_F(w'):
//   • a pinch lying entirely past E(c) descends (strip-prefix), recurses (IH),
//     and re-prepends c;
//   • the spanning case (c an x, left endpoint at the run's last position p-1,
//     right endpoint the first stable of ψ_F(w')) reconstructs a pinch at (0, l+1)
//     of w via the first-stable correspondence — the run forces no new pinch.
pub proof fn lemma_psi_F_pinch_descends(p: nat, w: Word)
    requires
        word_valid(w, 2),
        p >= 1,
        has_pinch(f_as_hnn(), apply_embedding(psi_F_images(p), w)),
    ensures
        has_pinch(f_as_hnn(), w),
    decreases w.len(),
{
    let data = f_as_hnn();
    let imgs = psi_F_images(p);
    let pw = apply_embedding(imgs, w);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    assert(data.base.num_generators == 1);
    let ij: (int, int) = choose|i: int, j: int| has_pinch_at(data, pw, i, j);
    let i = ij.0;
    let j = ij.1;
    assert(has_pinch_at(data, pw, i, j));
    assert(has_adjacent_opposite_at(data, pw, i, j));
    assert(w.len() > 0) by {
        if w.len() == 0 { assert(pw =~= Seq::<Symbol>::empty()); }
    }
    let c = w[0];
    let w2 = w.drop_first();
    assert(w =~= seq![c] + w2);
    assert(word_valid(w2, 2)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], 2)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(imgs, seq![c], w2);
    let ec = apply_embedding(imgs, seq![c]);
    let pw2 = apply_embedding(imgs, w2);
    assert(pw =~= ec + pw2);
    assert(ec =~= apply_embedding_symbol(imgs, c));
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    if is_stable(data, c) {
        assert(c == Symbol::Gen(1) || c == Symbol::Inv(1));
        if c == Symbol::Gen(1) {
            assert(ec =~= symbol_power(Symbol::Gen(1), p));
        } else {
            lemma_inverse_word_sympower(Symbol::Gen(1), p);
            assert(ec =~= symbol_power(Symbol::Inv(1), p));
        }
        assert(ec =~= symbol_power(c, p));
        assert(ec.len() == p);
        assert(forall|m: int| 0 <= m < p ==> #[trigger] ec[m] == c);
        if i >= p as int {
            //  pinch entirely past the run: strip, recurse, re-prepend
            lemma_strip_prefix_preserves_pinch(data, ec, pw2, i, j);
            lemma_psi_F_pinch_descends(p, w2);
            lemma_prepend_preserves_pinch(data, c, w2);
        } else {
            //  spanning case
            assert(forall|m: int| 0 <= m < p ==> #[trigger] pw[m] == c) by {
                assert forall|m: int| 0 <= m < p implies pw[m] == c
                by { assert(pw[m] == ec[m]); }
            }
            //  j >= p, else both endpoints sit in the run and would be equal
            assert(j >= p as int) by {
                if j < p as int { assert(pw[j] == c && pw[i] == c); }
            }
            //  i = p-1, else a run position i+1 (<p<=j) is a stable letter between i and j
            assert(i == p - 1) by {
                if i < p - 1 { assert(pw[i + 1] == c && i < i + 1 < j); }
            }
            let ll = j - (p as int);
            assert(forall|m: int| 0 <= m < pw2.len() ==> #[trigger] pw[m + p] == pw2[m]);
            assert(0 <= ll < pw2.len());
            assert(is_stable(data, pw2[ll]));
            assert forall|k: int| 0 <= k < ll implies !is_stable(data, #[trigger] pw2[k]) by {
                assert(pw2[k] == pw[k + p]);
            }
            lemma_psi_F_spanning(p, w2, ll);
            //  reconstruct the pinch at (0, ll+1) of w
            assert(w[ll + 1] == w2[ll]);
            assert(w.subrange(1, ll + 1) =~= w2.subrange(0, ll));
            assert(pw.subrange(i + 1, j) =~= pw2.subrange(0, ll));
            assert(w.subrange(1, ll + 1) =~= pw.subrange(i + 1, j));
            assert(pw[i] == c && pw[j] == pw2[ll]);
            assert(c != w2[ll]);
            assert forall|k: int| 0 < k < ll + 1 implies !is_stable(data, #[trigger] w[k]) by {
                assert(w[k] == w2[k - 1]);
            }
            assert(has_pinch_at(data, w, 0, ll + 1));
            assert(has_pinch(data, w)) by {
                assert(has_pinch_at(data, w, 0, ll + 1));
            }
        }
    } else {
        //  c non-stable: pw[0] = c can't be a (stable) pinch endpoint, so i >= 1
        assert(ec =~= seq![c]);
        assert(ec.len() == 1);
        assert(pw[0] == c) by { assert(pw[0] == ec[0]); }
        assert(is_stable(data, pw[i]));
        assert(i >= 1);
        lemma_strip_prefix_preserves_pinch(data, ec, pw2, i, j);
        lemma_psi_F_pinch_descends(p, w2);
        lemma_prepend_preserves_pinch(data, c, w2);
    }
}

//  ============================================================
//  (Q) Pinch-out at the F-level: deleting a pinch shrinks the word.
//  ============================================================
//
//  A pinch  x^ε · u · x^{-ε}  (u in the trivial ⟨t⟩ subgroup, hence ≡ε) equals
//  the empty word, so w ≡ w with positions i..j removed — strictly shorter.
//  The reduction engine of the ψ-injectivity induction (on word length).
pub proof fn lemma_pinch_out(w: Word, i: int, j: int)
    requires
        word_valid(w, 2),
        has_pinch_at(f_as_hnn(), w, i, j),
    ensures
        equiv_in_presentation(pres_tx(),
            w, w.subrange(0, i) + w.subrange(j + 1, w.len() as int)),
{
    let data = f_as_hnn();
    let u = w.subrange(i + 1, j);
    let mid = w.subrange(i, j + 1);
    let si = w[i];
    let sj = w[j];
    lemma_pres_t_valid();
    lemma_f_as_hnn_presentation();   //  hnn_presentation(f_as_hnn) == pres_tx
    //  both associated-subgroup generator lists are empty
    assert(Seq::new(0, |k: int| data.associations[k].0) =~= Seq::<Word>::empty());
    assert(Seq::new(0, |k: int| data.associations[k].1) =~= Seq::<Word>::empty());
    //  the pinch middle lies in the trivial ⟨t⟩ subgroup ⟹ u ≡ ε
    assert(in_generated_subgroup(pres_t(), Seq::<Word>::empty(), u));
    assert(is_inverse_pair(si, sj));
    lemma_in_empty_subgroup_trivial(pres_t(), u);
    lemma_base_embeds_in_hnn(data, u, empty_word());     //  u ≡ ε in pres_tx
    //  mid = [si] · (u · [sj]) ≡ [si] · [sj] ≡ ε  (right-assoc matches delete's output)
    assert(mid =~= concat(seq![si], concat(u, seq![sj])));
    lemma_delete_equiv_empty(pres_tx(), seq![si], u, seq![sj]);
    assert(concat(seq![si], seq![sj]) =~= seq![si, sj]);
    lemma_cancel_pair_equiv_empty(pres_tx(), si, sj);
    lemma_equiv_transitive(pres_tx(), mid, concat(seq![si], seq![sj]), empty_word());
    //  w = w[0..i] · (mid · w[j+1..])  ⟹  w ≡ w[0..i] · w[j+1..]
    assert(w =~= concat(w.subrange(0, i), concat(mid, w.subrange(j + 1, w.len() as int))));
    lemma_delete_equiv_empty(pres_tx(),
        w.subrange(0, i), mid, w.subrange(j + 1, w.len() as int));
    assert(w.subrange(0, i) + w.subrange(j + 1, w.len() as int)
        =~= concat(w.subrange(0, i), w.subrange(j + 1, w.len() as int)));
}

//  ============================================================
//  Step 2 foundation: ψ (t↦t, x↦xᵖ, y↦yᵠ) scales the y-stable-count by q.
//  ============================================================
//
//  Over a_as_hnn the stable letter is y = Gen(2); t and x are base symbols.
//  So each y/y⁻¹ in w expands to a length-q run of stable letters, and t,x
//  contribute none — the count multiplies by q.

//  Per-symbol y-contribution under ψ.
pub proof fn lemma_psi_A_emb_symbol_stable_count(p: nat, q: nat, s: Symbol)
    requires
        symbol_valid(s, 3),
    ensures
        stable_count(a_as_hnn(), apply_embedding(psi_images(p, q), seq![s]))
            == (if is_stable(a_as_hnn(), s) { q } else { 0nat }),
{
    let data = a_as_hnn();
    let imgs = psi_images(p, q);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    reveal_with_fuel(stable_count, 2);
    assert(data.base.num_generators == 2);
    assert(apply_embedding(imgs, seq![s]) =~= apply_embedding_symbol(imgs, s));
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    assert(imgs[2] =~= symbol_power(Symbol::Gen(2), q));
    match s {
        Symbol::Gen(i) => {
            if i == 0 {
                assert(apply_embedding_symbol(imgs, s) =~= seq![Symbol::Gen(0)]);
                assert(!is_stable(data, s));
            } else if i == 1 {
                lemma_stable_count_symbol_power(data, Symbol::Gen(1), p);
                assert(apply_embedding_symbol(imgs, s) =~= symbol_power(Symbol::Gen(1), p));
                assert(!is_stable(data, s));
            } else {
                assert(i == 2);
                lemma_stable_count_symbol_power(data, Symbol::Gen(2), q);
                assert(apply_embedding_symbol(imgs, s) =~= symbol_power(Symbol::Gen(2), q));
                assert(is_stable(data, s));
            }
        }
        Symbol::Inv(i) => {
            if i == 0 {
                assert(apply_embedding_symbol(imgs, s) =~= seq![Symbol::Inv(0)]);
                assert(!is_stable(data, s));
            } else if i == 1 {
                lemma_inverse_word_sympower(Symbol::Gen(1), p);
                assert(apply_embedding_symbol(imgs, s) =~= symbol_power(Symbol::Inv(1), p));
                lemma_stable_count_symbol_power(data, Symbol::Inv(1), p);
                assert(!is_stable(data, s));
            } else {
                assert(i == 2);
                lemma_inverse_word_sympower(Symbol::Gen(2), q);
                assert(apply_embedding_symbol(imgs, s) =~= symbol_power(Symbol::Inv(2), q));
                lemma_stable_count_symbol_power(data, Symbol::Inv(2), q);
                assert(is_stable(data, s));
            }
        }
    }
}

//  ============================================================
//  χₓ : the signed x-exponent-sum  (the ⟨x⟩-membership detector)
//  ============================================================
//
//  The engine of the y-pinch middle-correspondence: a y-pinch's middle must lie
//  in ⟨x⟩, and χₓ reads that off.  χₓ is a ℤ-homomorphism (additive over concat),
//  it scales by p under ψ_F (x↦xᵖ), and — the hard step, next — it is ≡-invariant
//  on the free group F, so ψ_F(u) ≡ xⁿ forces n = p·χₓ(u), handing us the witness.

pub open spec fn x_exp_sum(w: Word) -> int
    decreases w.len()
{
    if w.len() == 0 {
        0int
    } else {
        (if w.first() == Symbol::Gen(1) { 1int }
         else if w.first() == Symbol::Inv(1) { -1int }
         else { 0int })
        + x_exp_sum(w.drop_first())
    }
}

//  χₓ is additive over concatenation.
pub proof fn lemma_x_exp_sum_concat(w1: Word, w2: Word)
    ensures
        x_exp_sum(w1 + w2) == x_exp_sum(w1) + x_exp_sum(w2),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(w1 + w2 =~= w2);
    } else {
        assert((w1 + w2).first() == w1.first());
        assert((w1 + w2).drop_first() =~= w1.drop_first() + w2);
        lemma_x_exp_sum_concat(w1.drop_first(), w2);
    }
}

//  χₓ of a constant power.
pub proof fn lemma_x_exp_sum_symbol_power(s: Symbol, n: nat)
    ensures
        x_exp_sum(symbol_power(s, n))
            == (if s == Symbol::Gen(1) { n as int }
                else if s == Symbol::Inv(1) { -(n as int) }
                else { 0int }),
    decreases n,
{
    if n == 0 {
        assert(symbol_power(s, n) =~= Seq::<Symbol>::empty());
    } else {
        assert(symbol_power(s, n).first() == s);
        assert(symbol_power(s, n).drop_first() =~= symbol_power(s, (n - 1) as nat));
        lemma_x_exp_sum_symbol_power(s, (n - 1) as nat);
    }
}

//  ψ_F scales χₓ by p  (x↦xᵖ multiplies the x-count, t↦t contributes none).
pub proof fn lemma_x_exp_sum_psi_F(p: nat, u: Word)
    requires
        word_valid(u, 2),
    ensures
        x_exp_sum(apply_embedding(psi_F_images(p), u)) == p * x_exp_sum(u),
    decreases u.len(),
{
    let imgs = psi_F_images(p);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    if u.len() == 0 {
        assert(apply_embedding(imgs, u) =~= Seq::<Symbol>::empty());
    } else {
        let c = u.first();
        let rest = u.drop_first();
        assert(u =~= seq![c] + rest);
        assert(word_valid(rest, 2)) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], 2)
            by { assert(rest[k] == u[k + 1]); }
        }
        lemma_apply_embedding_concat(imgs, seq![c], rest);
        assert(apply_embedding(imgs, u)
            =~= apply_embedding(imgs, seq![c]) + apply_embedding(imgs, rest));
        lemma_x_exp_sum_concat(apply_embedding(imgs, seq![c]), apply_embedding(imgs, rest));
        lemma_x_exp_sum_psi_F(p, rest);
        //  per-symbol: χₓ(ψ_F([c])) == p · χₓ([c])
        reveal_with_fuel(x_exp_sum, 2);
        assert(apply_embedding(imgs, seq![c]) =~= apply_embedding_symbol(imgs, c));
        assert(imgs[0] =~= seq![Symbol::Gen(0)]);
        assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
        if c == Symbol::Gen(1) {
            assert(apply_embedding_symbol(imgs, c) =~= symbol_power(Symbol::Gen(1), p));
            lemma_x_exp_sum_symbol_power(Symbol::Gen(1), p);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == p);
            assert(x_exp_sum(seq![c]) == 1);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == p * x_exp_sum(seq![c]));
        } else if c == Symbol::Inv(1) {
            lemma_inverse_word_sympower(Symbol::Gen(1), p);
            assert(apply_embedding_symbol(imgs, c) =~= symbol_power(Symbol::Inv(1), p));
            lemma_x_exp_sum_symbol_power(Symbol::Inv(1), p);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == -(p as int));
            assert(x_exp_sum(seq![c]) == -1);
            assert(p * (-1int) == -(p as int)) by (nonlinear_arith);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == p * x_exp_sum(seq![c]));
        } else if c == Symbol::Gen(0) {
            assert(apply_embedding_symbol(imgs, c) =~= seq![Symbol::Gen(0)]);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == 0);
            assert(x_exp_sum(seq![c]) == 0);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == p * x_exp_sum(seq![c]));
        } else {
            assert(c == Symbol::Inv(0));
            assert(apply_embedding_symbol(imgs, c) =~= seq![Symbol::Inv(0)]);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == 0);
            assert(x_exp_sum(seq![c]) == 0);
            assert(x_exp_sum(apply_embedding(imgs, seq![c])) == p * x_exp_sum(seq![c]));
        }
        assert(x_exp_sum(seq![c] + rest) == x_exp_sum(seq![c]) + x_exp_sum(rest)) by {
            lemma_x_exp_sum_concat(seq![c], rest);
        }
        assert(p * (x_exp_sum(seq![c]) + x_exp_sum(rest))
            == p * x_exp_sum(seq![c]) + p * x_exp_sum(rest)) by (nonlinear_arith);
    }
}

//  ============================================================
//  χₓ is ≡-invariant on the free group F = ⟨t,x⟩  (the hard nut)
//  ============================================================
//
//  F = pres_tx() has NO relators, so every derivation step is a free reduction or
//  expansion — inserting/deleting an inverse pair, which is χₓ-neutral.  (The two
//  Relator steps return None when there are no relators, so they never occur in a
//  valid derivation.)  Hence χₓ is constant along any derivation, i.e. ≡-invariant.

//  An inverse pair contributes 0 to χₓ.
pub proof fn lemma_x_exp_sum_inverse_pair(s1: Symbol, s2: Symbol)
    requires
        is_inverse_pair(s1, s2),
    ensures
        x_exp_sum(seq![s1, s2]) == 0,
{
    reveal_with_fuel(x_exp_sum, 3);
    assert(seq![s1, s2].drop_first() =~= seq![s2]);
    assert(seq![s2].drop_first() =~= Seq::<Symbol>::empty());
    assert(s2 == inverse_symbol(s1));
    //  case on s1: in every case x_val(s1) + x_val(s2) = 0
    match s1 {
        Symbol::Gen(i) => { assert(s2 == Symbol::Inv(i)); }
        Symbol::Inv(i) => { assert(s2 == Symbol::Gen(i)); }
    }
}

//  A single valid derivation step preserves χₓ (no relators ⟹ only free moves).
pub proof fn lemma_x_exp_sum_step_invariant(
    p: Presentation, w: Word, step: DerivationStep, w2: Word,
)
    requires
        p.relators.len() == 0,
        apply_step(p, w, step) == Some(w2),
    ensures
        x_exp_sum(w2) == x_exp_sum(w),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            let i = position;
            assert(has_cancellation_at(w, i));
            assert(w2 == reduce_at(w, i));
            let a = w.subrange(0, i);
            let mid = w.subrange(i, i + 2);
            let b = w.subrange(i + 2, w.len() as int);
            assert(w =~= a + mid + b);
            assert(w2 =~= a + b);
            assert(mid =~= seq![w[i], w[i + 1]]);
            assert(is_inverse_pair(w[i], w[i + 1]));
            lemma_x_exp_sum_inverse_pair(w[i], w[i + 1]);
            lemma_x_exp_sum_concat(a + mid, b);
            lemma_x_exp_sum_concat(a, mid);
            lemma_x_exp_sum_concat(a, b);
        }
        DerivationStep::FreeExpand { position, symbol } => {
            let i = position;
            let pair: Word =
                Seq::new(1, |_j: int| symbol) + Seq::new(1, |_j: int| inverse_symbol(symbol));
            let a = w.subrange(0, i);
            let b = w.subrange(i, w.len() as int);
            assert(w2 =~= a + pair + b);
            assert(w =~= a + b);
            assert(pair =~= seq![symbol, inverse_symbol(symbol)]);
            assert(is_inverse_pair(symbol, inverse_symbol(symbol)));
            lemma_x_exp_sum_inverse_pair(symbol, inverse_symbol(symbol));
            lemma_x_exp_sum_concat(a + pair, b);
            lemma_x_exp_sum_concat(a, pair);
            lemma_x_exp_sum_concat(a, b);
        }
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(!(0 <= relator_index < p.relators.len()));
            assert(apply_step(p, w, step) is None);
        }
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(!(0 <= relator_index < p.relators.len()));
            assert(apply_step(p, w, step) is None);
        }
    }
}

//  A full derivation preserves χₓ.
pub proof fn lemma_x_exp_sum_derivation_invariant(
    p: Presentation, steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        p.relators.len() == 0,
        derivation_produces(p, steps, start) == Some(end),
    ensures
        x_exp_sum(start) == x_exp_sum(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(start == end);
    } else {
        match apply_step(p, start, steps.first()) {
            Some(w_next) => {
                lemma_x_exp_sum_step_invariant(p, start, steps.first(), w_next);
                lemma_x_exp_sum_derivation_invariant(p, steps.drop_first(), w_next, end);
            }
            None => {
                assert(false);
            }
        }
    }
}

//  χₓ is ≡-invariant on F.
pub proof fn lemma_x_exp_sum_equiv_invariant(w1: Word, w2: Word)
    requires
        equiv_in_presentation(pres_tx(), w1, w2),
    ensures
        x_exp_sum(w1) == x_exp_sum(w2),
{
    let d = choose|d: Derivation| derivation_valid(pres_tx(), d, w1, w2);
    assert(derivation_valid(pres_tx(), d, w1, w2));
    lemma_x_exp_sum_derivation_invariant(pres_tx(), d.steps, w1, w2);
}

//  ============================================================
//  x^k (signed) and the cancelling free reductions
//  ============================================================

//  x^k as a word:  k≥0 ↦ xᵏ,  k<0 ↦ (x⁻¹)^(−k).
pub open spec fn x_pow(k: int) -> Word {
    if k >= 0 {
        symbol_power(Symbol::Gen(1), k as nat)
    } else {
        symbol_power(Symbol::Inv(1), (-k) as nat)
    }
}

//  χₓ(x^k) == k.
pub proof fn lemma_x_exp_sum_x_pow(k: int)
    ensures
        x_exp_sum(x_pow(k)) == k,
{
    if k >= 0 {
        lemma_x_exp_sum_symbol_power(Symbol::Gen(1), k as nat);
    } else {
        lemma_x_exp_sum_symbol_power(Symbol::Inv(1), (-k) as nat);
    }
}

//  x · x⁻ᵏ  freely reduces to  x⁻⁽ᵏ⁻¹⁾.
pub proof fn lemma_x_cancel_gen(k: nat)
    requires
        k >= 1,
    ensures
        equiv_in_presentation(pres_tx(),
            seq![Symbol::Gen(1)] + symbol_power(Symbol::Inv(1), k),
            symbol_power(Symbol::Inv(1), (k - 1) as nat)),
{
    let target = symbol_power(Symbol::Inv(1), (k - 1) as nat);
    let w: Word = seq![Symbol::Gen(1)] + symbol_power(Symbol::Inv(1), k);
    assert(symbol_power(Symbol::Inv(1), k)
        =~= seq![Symbol::Inv(1)] + target);
    assert(w =~= seq![Symbol::Gen(1), Symbol::Inv(1)] + target);
    assert(w[0] == Symbol::Gen(1) && w[1] == Symbol::Inv(1));
    assert(is_inverse_pair(Symbol::Gen(1), Symbol::Inv(1)));
    assert(has_cancellation_at(w, 0));
    assert(reduce_at(w, 0) =~= target);
    assert(reduces_one_step(w, target)) by {
        assert(has_cancellation_at(w, 0) && target == reduce_at(w, 0));
    }
    assert(reduces_in_steps(w, target, 1)) by {
        assert(reduces_one_step(w, target) && reduces_in_steps(target, target, 0));
    }
    assert(reduces_to(w, target));
    lemma_reduces_to_equiv(pres_tx(), w, target);
}

//  x⁻¹ · xᵏ  freely reduces to  x^(k−1).
pub proof fn lemma_x_cancel_inv(k: nat)
    requires
        k >= 1,
    ensures
        equiv_in_presentation(pres_tx(),
            seq![Symbol::Inv(1)] + symbol_power(Symbol::Gen(1), k),
            symbol_power(Symbol::Gen(1), (k - 1) as nat)),
{
    let target = symbol_power(Symbol::Gen(1), (k - 1) as nat);
    let w: Word = seq![Symbol::Inv(1)] + symbol_power(Symbol::Gen(1), k);
    assert(symbol_power(Symbol::Gen(1), k)
        =~= seq![Symbol::Gen(1)] + target);
    assert(w =~= seq![Symbol::Inv(1), Symbol::Gen(1)] + target);
    assert(w[0] == Symbol::Inv(1) && w[1] == Symbol::Gen(1));
    assert(is_inverse_pair(Symbol::Inv(1), Symbol::Gen(1)));
    assert(has_cancellation_at(w, 0));
    assert(reduce_at(w, 0) =~= target);
    assert(reduces_one_step(w, target)) by {
        assert(has_cancellation_at(w, 0) && target == reduce_at(w, 0));
    }
    assert(reduces_in_steps(w, target, 1)) by {
        assert(reduces_one_step(w, target) && reduces_in_steps(target, target, 0));
    }
    assert(reduces_to(w, target));
    lemma_reduces_to_equiv(pres_tx(), w, target);
}

//  Prepending x shifts the exponent up by one:  x · xᵐ ~ x^(m+1).
pub proof fn lemma_x_pow_prepend_gen(m: int)
    ensures
        equiv_in_presentation(pres_tx(), seq![Symbol::Gen(1)] + x_pow(m), x_pow(m + 1)),
{
    let lhs: Word = seq![Symbol::Gen(1)] + x_pow(m);
    if m >= 0 {
        lemma_symbol_power_merge(Symbol::Gen(1), 1, m as nat);
        assert(seq![Symbol::Gen(1)] =~= symbol_power(Symbol::Gen(1), 1));
        assert(lhs =~= symbol_power(Symbol::Gen(1), (1 + m) as nat));
        assert(x_pow(m + 1) =~= symbol_power(Symbol::Gen(1), (1 + m) as nat));
        assert(lhs =~= x_pow(m + 1));
        lemma_equiv_refl(pres_tx(), x_pow(m + 1));
    } else {
        let kk: nat = (-m) as nat;
        assert(x_pow(m) =~= symbol_power(Symbol::Inv(1), kk));
        assert(lhs =~= seq![Symbol::Gen(1)] + symbol_power(Symbol::Inv(1), kk));
        lemma_x_cancel_gen(kk);
        if m + 1 >= 0 {
            assert(kk == 1);
            assert(symbol_power(Symbol::Inv(1), (kk - 1) as nat) =~= x_pow(m + 1));
        } else {
            assert(symbol_power(Symbol::Inv(1), (kk - 1) as nat) =~= x_pow(m + 1));
        }
    }
}

//  Prepending x⁻¹ shifts the exponent down by one:  x⁻¹ · xᵐ ~ x^(m−1).
pub proof fn lemma_x_pow_prepend_inv(m: int)
    ensures
        equiv_in_presentation(pres_tx(), seq![Symbol::Inv(1)] + x_pow(m), x_pow(m - 1)),
{
    let lhs: Word = seq![Symbol::Inv(1)] + x_pow(m);
    if m > 0 {
        assert(x_pow(m) =~= symbol_power(Symbol::Gen(1), m as nat));
        assert(lhs =~= seq![Symbol::Inv(1)] + symbol_power(Symbol::Gen(1), m as nat));
        lemma_x_cancel_inv(m as nat);
        assert(symbol_power(Symbol::Gen(1), (m as nat - 1) as nat) =~= x_pow(m - 1));
    } else {
        let kk: nat = (-m) as nat;
        assert(x_pow(m) =~= symbol_power(Symbol::Inv(1), kk));
        lemma_symbol_power_merge(Symbol::Inv(1), 1, kk);
        assert(seq![Symbol::Inv(1)] =~= symbol_power(Symbol::Inv(1), 1));
        assert(lhs =~= symbol_power(Symbol::Inv(1), (1 + kk) as nat));
        assert(x_pow(m - 1) =~= symbol_power(Symbol::Inv(1), (1 + kk) as nat));
        assert(lhs =~= x_pow(m - 1));
        lemma_equiv_refl(pres_tx(), x_pow(m - 1));
    }
}

//  A product of x's and x⁻¹'s reduces to x raised to its net exponent.
pub proof fn lemma_x_factors_to_pow(factors: Seq<Word>)
    requires
        factors_from_generators(seq![seq![Symbol::Gen(1)]], factors),
    ensures
        equiv_in_presentation(pres_tx(),
            concat_all(factors), x_pow(x_exp_sum(concat_all(factors)))),
    decreases factors.len(),
{
    reveal_with_fuel(concat_all, 1);
    reveal_with_fuel(x_exp_sum, 2);
    reveal_with_fuel(inverse_word, 2);
    let g = seq![seq![Symbol::Gen(1)]];
    if factors.len() == 0 {
        assert(concat_all(factors) =~= Seq::<Symbol>::empty());
        assert(x_exp_sum(concat_all(factors)) == 0);
        assert(x_pow(0) =~= Seq::<Symbol>::empty());
        lemma_equiv_refl(pres_tx(), concat_all(factors));
    } else {
        let f = factors.first();
        let rest = factors.drop_first();
        let cr = concat_all(rest);
        assert(concat_all(factors) =~= f + cr);
        assert(factors_from_generators(g, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(g, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_x_factors_to_pow(rest);
        let m = x_exp_sum(cr);
        assert(is_generator_or_inverse(g, f)) by { assert(f == factors[0]); }
        assert(inverse_word(seq![Symbol::Gen(1)]) =~= seq![Symbol::Inv(1)]);
        lemma_x_exp_sum_concat(f, cr);
        if f == seq![Symbol::Gen(1)] {
            assert(x_exp_sum(f) == 1);
            assert(x_exp_sum(concat_all(factors)) == m + 1);
            lemma_equiv_concat_right(pres_tx(), seq![Symbol::Gen(1)], cr, x_pow(m));
            lemma_x_pow_prepend_gen(m);
            lemma_equiv_transitive(pres_tx(),
                f + cr, seq![Symbol::Gen(1)] + x_pow(m), x_pow(m + 1));
            assert(x_pow(m + 1) =~= x_pow(x_exp_sum(concat_all(factors))));
        } else {
            assert(f == seq![Symbol::Inv(1)]);
            assert(x_exp_sum(f) == -1);
            assert(x_exp_sum(concat_all(factors)) == m - 1);
            lemma_equiv_concat_right(pres_tx(), seq![Symbol::Inv(1)], cr, x_pow(m));
            lemma_x_pow_prepend_inv(m);
            lemma_equiv_transitive(pres_tx(),
                f + cr, seq![Symbol::Inv(1)] + x_pow(m), x_pow(m - 1));
            assert(x_pow(m - 1) =~= x_pow(x_exp_sum(concat_all(factors))));
        }
    }
}

//  concat_all of x-factors is a valid word over ⟨t,x⟩ (each factor is x^±1).
pub proof fn lemma_x_factors_concat_valid(factors: Seq<Word>)
    requires
        factors_from_generators(seq![seq![Symbol::Gen(1)]], factors),
    ensures
        word_valid(concat_all(factors), 2),
    decreases factors.len(),
{
    reveal_with_fuel(concat_all, 1);
    reveal_with_fuel(inverse_word, 2);
    let g = seq![seq![Symbol::Gen(1)]];
    if factors.len() == 0 {
        assert(concat_all(factors) =~= Seq::<Symbol>::empty());
    } else {
        let f = factors.first();
        let rest = factors.drop_first();
        assert(factors_from_generators(g, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(g, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_x_factors_concat_valid(rest);
        assert(is_generator_or_inverse(g, f)) by { assert(f == factors[0]); }
        assert(inverse_word(seq![Symbol::Gen(1)]) =~= seq![Symbol::Inv(1)]);
        assert(word_valid(f, 2)) by {
            assert forall|k: int| 0 <= k < f.len() implies symbol_valid(#[trigger] f[k], 2) by { }
        }
        assert(concat_all(factors) =~= f + concat_all(rest));
        lemma_concat_word_valid(f, concat_all(rest), 2);
    }
}

//  (A): an element of ⟨x⟩ is ≡ to x raised to its x-exponent-sum.
pub proof fn lemma_x_subgroup_is_pow(v: Word)
    requires
        in_generated_subgroup(pres_tx(), seq![seq![Symbol::Gen(1)]], v),
    ensures
        equiv_in_presentation(pres_tx(), v, x_pow(x_exp_sum(v))),
{
    let g = seq![seq![Symbol::Gen(1)]];
    let factors = choose|factors: Seq<Word>|
        factors_from_generators(g, factors)
        && equiv_in_presentation(pres_tx(), concat_all(factors), v);
    assert(factors_from_generators(g, factors)
        && equiv_in_presentation(pres_tx(), concat_all(factors), v));
    let cf = concat_all(factors);
    lemma_x_factors_to_pow(factors);                       //  cf ~ x_pow(χₓ(cf))
    lemma_x_exp_sum_equiv_invariant(cf, v);                //  χₓ(cf) == χₓ(v)
    assert(x_pow(x_exp_sum(cf)) == x_pow(x_exp_sum(v)));
    lemma_x_factors_concat_valid(factors);                 //  word_valid(cf, 2)
    assert(presentation_valid(pres_tx())) by { reveal(presentation_valid); }
    lemma_equiv_symmetric(pres_tx(), cf, v);               //  v ~ cf
    lemma_equiv_transitive(pres_tx(), v, cf, x_pow(x_exp_sum(v)));
}

//  ============================================================
//  (B) the middle-correspondence:  ψ_F(u) ∈ ⟨x⟩  ⟹  u ∈ ⟨x⟩
//  ============================================================

//  ψ_F sends xⁿ to x^(pn).
pub proof fn lemma_psi_F_emb_genpow(p: nat, n: nat)
    ensures
        apply_embedding(psi_F_images(p), symbol_power(Symbol::Gen(1), n))
            =~= symbol_power(Symbol::Gen(1), p * n),
    decreases n,
{
    let imgs = psi_F_images(p);
    reveal_with_fuel(apply_embedding, 2);
    if n == 0 {
        assert(symbol_power(Symbol::Gen(1), n) =~= Seq::<Symbol>::empty());
        assert(apply_embedding(imgs, symbol_power(Symbol::Gen(1), n)) =~= Seq::<Symbol>::empty());
        assert(symbol_power(Symbol::Gen(1), p * n) =~= Seq::<Symbol>::empty());
    } else {
        let n1: nat = (n - 1) as nat;
        let tail = symbol_power(Symbol::Gen(1), n1);
        assert(n == n1 + 1);
        assert(symbol_power(Symbol::Gen(1), n) =~= seq![Symbol::Gen(1)] + tail);
        lemma_apply_embedding_concat(imgs, seq![Symbol::Gen(1)], tail);
        assert(apply_embedding(imgs, seq![Symbol::Gen(1)]) =~= symbol_power(Symbol::Gen(1), p));
        lemma_psi_F_emb_genpow(p, n1);
        lemma_symbol_power_merge(Symbol::Gen(1), p, p * n1);
        assert(p + p * n1 == p * n) by (nonlinear_arith)
            requires n == n1 + 1;
    }
}

//  ψ_F sends x⁻ⁿ to x^(−pn).
pub proof fn lemma_psi_F_emb_invpow(p: nat, n: nat)
    ensures
        apply_embedding(psi_F_images(p), symbol_power(Symbol::Inv(1), n))
            =~= symbol_power(Symbol::Inv(1), p * n),
    decreases n,
{
    let imgs = psi_F_images(p);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    if n == 0 {
        assert(symbol_power(Symbol::Inv(1), n) =~= Seq::<Symbol>::empty());
        assert(apply_embedding(imgs, symbol_power(Symbol::Inv(1), n)) =~= Seq::<Symbol>::empty());
        assert(symbol_power(Symbol::Inv(1), p * n) =~= Seq::<Symbol>::empty());
    } else {
        let n1: nat = (n - 1) as nat;
        let tail = symbol_power(Symbol::Inv(1), n1);
        assert(n == n1 + 1);
        assert(symbol_power(Symbol::Inv(1), n) =~= seq![Symbol::Inv(1)] + tail);
        lemma_apply_embedding_concat(imgs, seq![Symbol::Inv(1)], tail);
        lemma_inverse_word_sympower(Symbol::Gen(1), p);
        assert(apply_embedding(imgs, seq![Symbol::Inv(1)]) =~= symbol_power(Symbol::Inv(1), p));
        lemma_psi_F_emb_invpow(p, n1);
        lemma_symbol_power_merge(Symbol::Inv(1), p, p * n1);
        assert(p + p * n1 == p * n) by (nonlinear_arith)
            requires n == n1 + 1;
    }
}

//  ψ_F sends x^k to x^(pk)  (signed).
pub proof fn lemma_psi_F_x_pow(p: nat, k: int)
    ensures
        apply_embedding(psi_F_images(p), x_pow(k)) =~= x_pow(p * k),
{
    if k >= 0 {
        let kn: nat = k as nat;
        assert(k == kn);
        lemma_psi_F_emb_genpow(p, kn);
        assert(p * k == p * kn) by (nonlinear_arith) requires k == kn;
        assert(p * k >= 0) by (nonlinear_arith) requires k >= 0;
        assert((p * k) as nat == p * kn);
        assert(x_pow(k) =~= symbol_power(Symbol::Gen(1), kn));
        assert(x_pow(p * k) =~= symbol_power(Symbol::Gen(1), p * kn));
    } else {
        let kn: nat = (-k) as nat;
        assert(-k == kn);
        lemma_psi_F_emb_invpow(p, kn);
        assert(p * (-k) == p * kn) by (nonlinear_arith) requires -k == kn;
        assert(p * k == -(p * kn)) by (nonlinear_arith) requires -k == kn;
        assert(p * k <= 0) by (nonlinear_arith) requires k <= 0;
        assert((-(p * k)) as nat == p * kn);
        assert(x_pow(k) =~= symbol_power(Symbol::Inv(1), kn));
        assert(x_pow(p * k) =~= symbol_power(Symbol::Inv(1), p * kn));
    }
}

//  concat_all of n copies of [s] is sⁿ.
pub proof fn lemma_concat_all_const(s: Symbol, n: nat)
    ensures
        concat_all(Seq::new(n, |_j: int| seq![s])) =~= symbol_power(s, n),
    decreases n,
{
    reveal_with_fuel(concat_all, 1);
    if n == 0 {
        assert(Seq::new(n, |_j: int| seq![s]) =~= Seq::<Word>::empty());
        assert(symbol_power(s, n) =~= Seq::<Symbol>::empty());
    } else {
        let full = Seq::new(n, |_j: int| seq![s]);
        let tail = Seq::new((n - 1) as nat, |_j: int| seq![s]);
        assert(full.first() =~= seq![s]);
        assert(full.drop_first() =~= tail);
        lemma_concat_all_const(s, (n - 1) as nat);
        assert(symbol_power(s, n) =~= seq![s] + symbol_power(s, (n - 1) as nat));
    }
}

//  x^k is a valid word over ⟨t,x⟩.
pub proof fn lemma_x_pow_valid(k: int)
    ensures
        word_valid(x_pow(k), 2),
{
    if k >= 0 {
        lemma_symbol_power_valid(Symbol::Gen(1), k as nat, 2);
    } else {
        lemma_symbol_power_valid(Symbol::Inv(1), (-k) as nat, 2);
    }
}

//  Subgroup membership is preserved when the target moves to an equivalent word.
pub proof fn lemma_in_subgroup_respects_equiv(p: Presentation, gens: Seq<Word>, v: Word, u: Word)
    requires
        in_generated_subgroup(p, gens, v),
        equiv_in_presentation(p, v, u),
    ensures
        in_generated_subgroup(p, gens, u),
{
    let factors = choose|factors: Seq<Word>|
        factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), v);
    assert(factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), v));
    lemma_equiv_transitive(p, concat_all(factors), v, u);
    assert(in_generated_subgroup(p, gens, u)) by {
        assert(factors_from_generators(gens, factors)
            && equiv_in_presentation(p, concat_all(factors), u));
    }
}

//  x^k lies in ⟨x⟩.
pub proof fn lemma_x_pow_in_subgroup(k: int)
    ensures
        in_generated_subgroup(pres_tx(), seq![seq![Symbol::Gen(1)]], x_pow(k)),
{
    let g = seq![seq![Symbol::Gen(1)]];
    reveal_with_fuel(inverse_word, 2);
    assert(inverse_word(seq![Symbol::Gen(1)]) =~= seq![Symbol::Inv(1)]);
    let sym = if k >= 0 { Symbol::Gen(1) } else { Symbol::Inv(1) };
    let cnt: nat = if k >= 0 { k as nat } else { (-k) as nat };
    let factors = Seq::new(cnt, |_j: int| seq![sym]);
    lemma_concat_all_const(sym, cnt);
    assert(concat_all(factors) =~= x_pow(k));
    assert(factors_from_generators(g, factors)) by {
        assert forall|j: int| 0 <= j < factors.len()
            implies is_generator_or_inverse(g, #[trigger] factors[j])
        by {
            assert(factors[j] == seq![sym]);
            assert(g[0] == seq![Symbol::Gen(1)]);
            if k >= 0 {
                assert(factors[j] == g[0]);
            } else {
                assert(factors[j] == inverse_word(g[0]));
            }
            assert(0 <= 0 < g.len()
                && (factors[j] == g[0] || factors[j] == inverse_word(g[0])));
        }
    }
    lemma_equiv_refl(pres_tx(), x_pow(k));
    assert(in_generated_subgroup(pres_tx(), g, x_pow(k))) by {
        assert(factors_from_generators(g, factors)
            && equiv_in_presentation(pres_tx(), concat_all(factors), x_pow(k)));
    }
}

//  THE MIDDLE-CORRESPONDENCE:  ψ_F(u) ∈ ⟨x⟩  ⟹  u ∈ ⟨x⟩.
pub proof fn lemma_psi_F_in_x_subgroup(p: nat, u: Word)
    requires
        word_valid(u, 2),
        p >= 1,
        in_generated_subgroup(pres_tx(), seq![seq![Symbol::Gen(1)]],
            apply_embedding(psi_F_images(p), u)),
    ensures
        in_generated_subgroup(pres_tx(), seq![seq![Symbol::Gen(1)]], u),
{
    let pt = pres_tx();
    let g = seq![seq![Symbol::Gen(1)]];
    let imgs = psi_F_images(p);
    let pu = apply_embedding(imgs, u);
    let kk = x_exp_sum(u);
    let xk = x_pow(kk);
    let xpk = x_pow(p * kk);
    assert(presentation_valid(pt)) by { reveal(presentation_valid); }

    //  (A) + scaling:  pu ~ x^(p·k)
    lemma_x_subgroup_is_pow(pu);
    lemma_x_exp_sum_psi_F(p, u);
    assert(x_pow(x_exp_sum(pu)) =~= xpk);
    assert(equiv_in_presentation(pt, pu, xpk));
    lemma_psi_F_x_pow(p, kk);                     //  ψ_F(xk) =~= xpk

    //  validities
    lemma_x_pow_valid(kk);
    lemma_x_pow_valid(p * kk);
    lemma_inverse_word_valid(xk, 2);
    let w: Word = u + inverse_word(xk);
    lemma_concat_word_valid(u, inverse_word(xk), 2);

    //  ψ_F(w) =~= pu + inverse_word(xpk)  ~  xpk + inverse_word(xpk)  ~  ε
    lemma_apply_embedding_concat(imgs, u, inverse_word(xk));
    lemma_apply_embedding_inverse(imgs, xk);
    assert(apply_embedding(imgs, w) =~= pu + inverse_word(xpk));
    lemma_equiv_concat_left(pt, pu, xpk, inverse_word(xpk));
    lemma_word_inverse_right(pt, xpk);
    lemma_equiv_transitive(pt,
        pu + inverse_word(xpk), xpk + inverse_word(xpk), empty_word());
    assert(equiv_in_presentation(pt, apply_embedding(imgs, w), empty_word()));

    //  injectivity:  w ~ ε
    lemma_psi_F_injective(p, w);

    //  u ~ xk:  u ~ u+(inv(xk)+xk) = w+xk ~ ε+xk = xk
    lemma_word_inverse_left(pt, xk);
    lemma_equiv_concat_right(pt, u, inverse_word(xk) + xk, empty_word());
    assert(u + empty_word() =~= u);
    assert(u + (inverse_word(xk) + xk) =~= w + xk);
    assert(equiv_in_presentation(pt, w + xk, u));
    lemma_equiv_concat_left(pt, w, empty_word(), xk);
    assert(empty_word() + xk =~= xk);
    lemma_concat_word_valid(inverse_word(xk), xk, 2);
    lemma_concat_word_valid(w, xk, 2);
    lemma_equiv_symmetric(pt, w + xk, u);
    lemma_equiv_transitive(pt, u, w + xk, xk);

    //  membership transport
    lemma_x_pow_in_subgroup(kk);
    lemma_equiv_symmetric(pt, u, xk);
    lemma_in_subgroup_respects_equiv(pt, g, xk, u);
}

//  ============================================================
//  Step 2 (Corr): y-spanning + y-pinch descent
//  ============================================================

//  On an F-word (t's and x's only, no y), ψ_A agrees with ψ_F — both send t↦t,
//  x↦xᵖ, and the only difference (y↦yᵠ) never fires.  Lets the pinch-middle (an
//  F-word) be fed to lemma_psi_F_in_x_subgroup.
pub proof fn lemma_psi_A_eq_psi_F_on_fword(p: nat, q: nat, w: Word)
    requires
        word_valid(w, 2),
    ensures
        apply_embedding(psi_images(p, q), w) =~= apply_embedding(psi_F_images(p), w),
    decreases w.len(),
{
    let ia = psi_images(p, q);
    let iff = psi_F_images(p);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    if w.len() == 0 {
        assert(apply_embedding(ia, w) =~= Seq::<Symbol>::empty());
        assert(apply_embedding(iff, w) =~= Seq::<Symbol>::empty());
    } else {
        let c = w.first();
        let rest = w.drop_first();
        assert(w =~= seq![c] + rest);
        assert(word_valid(rest, 2)) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], 2)
            by { assert(rest[k] == w[k + 1]); }
        }
        lemma_apply_embedding_concat(ia, seq![c], rest);
        lemma_apply_embedding_concat(iff, seq![c], rest);
        lemma_psi_A_eq_psi_F_on_fword(p, q, rest);
        assert(symbol_valid(c, 2));
        assert(apply_embedding(ia, seq![c]) =~= apply_embedding_symbol(ia, c));
        assert(apply_embedding(iff, seq![c]) =~= apply_embedding_symbol(iff, c));
        assert(apply_embedding_symbol(ia, c) =~= apply_embedding_symbol(iff, c)) by {
            match c {
                Symbol::Gen(i) => { assert(ia[i as int] =~= iff[i as int]); }
                Symbol::Inv(i) => { assert(ia[i as int] =~= iff[i as int]); }
            }
        }
    }
}

//  Index of the first stable (y) symbol of w, or w.len() if none.
pub open spec fn first_stable_idx(data: HNNData, w: Word) -> int
    decreases w.len(),
{
    if w.len() == 0 {
        0
    } else if is_stable(data, w[0]) {
        0
    } else {
        1 + first_stable_idx(data, w.drop_first())
    }
}

pub proof fn lemma_first_stable_idx_nonneg(data: HNNData, w: Word)
    ensures
        first_stable_idx(data, w) >= 0,
    decreases w.len(),
{
    reveal_with_fuel(first_stable_idx, 1);
    if w.len() == 0 {
    } else if is_stable(data, w[0]) {
    } else {
        lemma_first_stable_idx_nonneg(data, w.drop_first());
    }
}

//  First-y correspondence over a_as_hnn.  Unlike ψ_F (where the only non-stable
//  symbol t expands 1:1, preserving the index), here x also expands (to xᵖ), so the
//  first-y index in ψ_A(w) is the ψ_A-image-length of w's pre-y prefix, not the
//  prefix length.  The output is driven by first_stable_idx(w); the pre-y prefix of
//  ψ_A(w) is exactly ψ_A of w's pre-y prefix.
pub proof fn lemma_psi_A_spanning(p: nat, q: nat, w: Word, l: int)
    requires
        word_valid(w, 3),
        p >= 1,
        q >= 1,
        0 <= l < apply_embedding(psi_images(p, q), w).len(),
        is_stable(a_as_hnn(), apply_embedding(psi_images(p, q), w)[l]),
        forall|k: int| 0 <= k < l
            ==> !is_stable(a_as_hnn(), #[trigger] apply_embedding(psi_images(p, q), w)[k]),
    ensures
        first_stable_idx(a_as_hnn(), w) < w.len(),
        is_stable(a_as_hnn(), w[first_stable_idx(a_as_hnn(), w)]),
        w[first_stable_idx(a_as_hnn(), w)] == apply_embedding(psi_images(p, q), w)[l],
        apply_embedding(psi_images(p, q), w).subrange(0, l)
            =~= apply_embedding(psi_images(p, q),
                w.subrange(0, first_stable_idx(a_as_hnn(), w))),
        forall|k: int| 0 <= k < first_stable_idx(a_as_hnn(), w)
            ==> !is_stable(a_as_hnn(), #[trigger] w[k]),
    decreases w.len(),
{
    let data = a_as_hnn();
    let imgs = psi_images(p, q);
    let pw = apply_embedding(imgs, w);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    reveal_with_fuel(first_stable_idx, 2);
    assert(data.base.num_generators == 2);
    assert(w.len() > 0) by {
        if w.len() == 0 { assert(pw =~= Seq::<Symbol>::empty()); }
    }
    let c = w[0];
    let w2 = w.drop_first();
    assert(w =~= seq![c] + w2);
    assert(word_valid(w2, 3)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], 3)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(imgs, seq![c], w2);
    let ec = apply_embedding(imgs, seq![c]);
    let pw2 = apply_embedding(imgs, w2);
    assert(pw =~= ec + pw2);
    assert(ec =~= apply_embedding_symbol(imgs, c));
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    assert(imgs[2] =~= symbol_power(Symbol::Gen(2), q));
    if is_stable(data, c) {
        //  c is y: pw[0] = c is stable, so l = 0 and first_stable_idx(w) = 0
        assert(c == Symbol::Gen(2) || c == Symbol::Inv(2));
        if c == Symbol::Gen(2) {
            assert(ec =~= symbol_power(Symbol::Gen(2), q));
        } else {
            lemma_inverse_word_sympower(Symbol::Gen(2), q);
            assert(ec =~= symbol_power(Symbol::Inv(2), q));
        }
        assert(ec[0] == c);
        assert(pw[0] == c) by { assert(pw[0] == ec[0]); }
        assert(l == 0) by { if l > 0 { assert(!is_stable(data, pw[0])); } }
        assert(first_stable_idx(data, w) == 0);
        assert(w.subrange(0, 0) =~= Seq::<Symbol>::empty());
        assert(pw.subrange(0, 0) =~= Seq::<Symbol>::empty());
    } else {
        //  c non-stable (t or x):  ec = c^elen (elen = 1 or p), all non-stable
        assert(c == Symbol::Gen(0) || c == Symbol::Inv(0)
            || c == Symbol::Gen(1) || c == Symbol::Inv(1));
        let elen: int = if c == Symbol::Gen(1) || c == Symbol::Inv(1) { p as int } else { 1int };
        if c == Symbol::Gen(0) {
            assert(ec =~= symbol_power(Symbol::Gen(0), 1));
        } else if c == Symbol::Inv(0) {
            assert(ec =~= symbol_power(Symbol::Inv(0), 1));
        } else if c == Symbol::Gen(1) {
            assert(ec =~= symbol_power(Symbol::Gen(1), p));
        } else {
            lemma_inverse_word_sympower(Symbol::Gen(1), p);
            assert(ec =~= symbol_power(Symbol::Inv(1), p));
        }
        assert(ec =~= symbol_power(c, elen as nat));
        assert(ec.len() == elen && elen >= 1);
        assert(forall|m: int| 0 <= m < elen ==> #[trigger] ec[m] == c);
        assert(forall|m: int| 0 <= m < elen ==> !is_stable(data, #[trigger] ec[m]));
        //  pw[0..elen) = ec all non-stable ⟹ l ≥ elen
        assert(forall|m: int| 0 <= m < elen ==> #[trigger] pw[m] == ec[m]);
        assert(l >= elen) by { if l < elen { assert(pw[l] == ec[l]); } }
        let l2 = l - elen;
        assert(forall|m: int| 0 <= m < pw2.len() ==> #[trigger] pw[m + elen] == pw2[m]);
        assert(0 <= l2 < pw2.len());
        assert(is_stable(data, pw2[l2])) by { assert(pw2[l2] == pw[l2 + elen]); }
        assert forall|k: int| 0 <= k < l2 implies !is_stable(data, #[trigger] pw2[k]) by {
            assert(pw2[k] == pw[k + elen]);
        }
        lemma_psi_A_spanning(p, q, w2, l2);
        let lp2 = first_stable_idx(data, w2);
        lemma_first_stable_idx_nonneg(data, w2);
        assert(0 <= lp2 < w2.len());
        assert(w =~= seq![c] + w2);
        assert(forall|m: int| 0 <= m < w2.len() ==> #[trigger] w[m + 1] == w2[m]);
        assert(first_stable_idx(data, w) == 1 + lp2);
        assert(w[lp2 + 1] == w2[lp2]);
        assert(w[1 + lp2] == w2[lp2]);
        assert(pw2[l2] == pw[l]);
        assert(w.subrange(0, 1 + lp2) =~= seq![c] + w2.subrange(0, lp2));
        lemma_apply_embedding_concat(imgs, seq![c], w2.subrange(0, lp2));
        assert(apply_embedding(imgs, w.subrange(0, 1 + lp2))
            =~= ec + apply_embedding(imgs, w2.subrange(0, lp2)));
        assert(pw.subrange(0, l) =~= ec + pw2.subrange(0, l2));
        assert forall|k: int| 0 <= k < 1 + lp2 implies !is_stable(data, #[trigger] w[k]) by {
            if k != 0 { assert(w[k] == w2[k - 1]); }
        }
    }
}

//  (Corr) CORE for Step 2: a y-pinch in ψ_A(w) descends to a y-pinch in w.
//  Structural induction on w, mirroring lemma_psi_F_pinch_descends, with two changes:
//   • a non-stable x now expands to xᵖ (not 1:1), so the strip-prefix case strips the
//     whole run (elen = p);
//   • the spanning case's pinch middle lies in ⟨x⟩ (not trivial), so it descends via
//     lemma_psi_A_spanning + lemma_psi_A_eq_psi_F_on_fword + lemma_psi_F_in_x_subgroup.
pub proof fn lemma_psi_A_pinch_descends(p: nat, q: nat, w: Word)
    requires
        word_valid(w, 3),
        p >= 1,
        q >= 1,
        has_pinch(a_as_hnn(), apply_embedding(psi_images(p, q), w)),
    ensures
        has_pinch(a_as_hnn(), w),
    decreases w.len(),
{
    let data = a_as_hnn();
    let imgs = psi_images(p, q);
    let pw = apply_embedding(imgs, w);
    reveal_with_fuel(apply_embedding, 2);
    reveal_with_fuel(inverse_word, 2);
    assert(data.base.num_generators == 2);
    let ng = data.base.num_generators;
    let ij: (int, int) = choose|i: int, j: int| has_pinch_at(data, pw, i, j);
    let i = ij.0;
    let j = ij.1;
    assert(has_pinch_at(data, pw, i, j));
    assert(has_adjacent_opposite_at(data, pw, i, j));
    assert(is_stable(data, pw[i]) && is_stable(data, pw[j]) && pw[i] != pw[j]);
    assert(w.len() > 0) by {
        if w.len() == 0 { assert(pw =~= Seq::<Symbol>::empty()); }
    }
    let c = w[0];
    let w2 = w.drop_first();
    assert(w =~= seq![c] + w2);
    assert(word_valid(w2, 3)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], 3)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(imgs, seq![c], w2);
    let ec = apply_embedding(imgs, seq![c]);
    let pw2 = apply_embedding(imgs, w2);
    assert(pw =~= ec + pw2);
    assert(ec =~= apply_embedding_symbol(imgs, c));
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    assert(imgs[2] =~= symbol_power(Symbol::Gen(2), q));
    if is_stable(data, c) {
        //  c is y: ec is the length-q run of c
        assert(c == Symbol::Gen(2) || c == Symbol::Inv(2));
        if c == Symbol::Gen(2) {
            assert(ec =~= symbol_power(Symbol::Gen(2), q));
        } else {
            lemma_inverse_word_sympower(Symbol::Gen(2), q);
            assert(ec =~= symbol_power(Symbol::Inv(2), q));
        }
        assert(ec =~= symbol_power(c, q));
        assert(ec.len() == q);
        assert(forall|m: int| 0 <= m < q ==> #[trigger] ec[m] == c);
        assert(forall|m: int| 0 <= m < q ==> #[trigger] pw[m] == c) by {
            assert forall|m: int| 0 <= m < q implies pw[m] == c by { assert(pw[m] == ec[m]); }
        }
        if i >= q as int {
            lemma_strip_prefix_preserves_pinch(data, ec, pw2, i, j);
            lemma_psi_A_pinch_descends(p, q, w2);
            lemma_prepend_preserves_pinch(data, c, w2);
        } else {
            //  spanning: pinch's left endpoint inside the run
            assert(j >= q as int) by {
                if j < q as int { assert(pw[j] == c && pw[i] == c); }
            }
            assert(i == q - 1) by {
                if i < q - 1 { assert(pw[i + 1] == c && i < i + 1 < j); }
            }
            let bigl = j - (q as int);
            assert(forall|m: int| 0 <= m < pw2.len() ==> #[trigger] pw[m + q] == pw2[m]);
            assert(0 <= bigl < pw2.len());
            assert(pw2[bigl] == pw[j]) by { assert(pw2[bigl] == pw[bigl + q]); }
            assert(is_stable(data, pw2[bigl]));
            assert forall|k: int| 0 <= k < bigl implies !is_stable(data, #[trigger] pw2[k]) by {
                assert(pw2[k] == pw[k + q]);
            }
            lemma_psi_A_spanning(p, q, w2, bigl);
            let lp = first_stable_idx(data, w2);
            lemma_first_stable_idx_nonneg(data, w2);
            assert(0 <= lp < w2.len());
            //  endpoints in w: w[0] = c (= pw[i]) and w[lp+1] = w2[lp] (= pw[j])
            assert(w[lp + 1] == w2[lp]);
            assert(w2[lp] == pw2[bigl]);
            assert(w[lp + 1] == pw[j] && w[0] == pw[i]);
            //  the pinch middle in w is the pre-y prefix, which descends into ⟨x⟩
            let midw = w2.subrange(0, lp);
            assert(word_valid(midw, 2)) by {
                assert forall|k: int| 0 <= k < midw.len() implies symbol_valid(#[trigger] midw[k], 2)
                by {
                    assert(midw[k] == w2[k]);
                    assert(!is_stable(data, w2[k]));
                }
            }
            //  pinch condition in pw: middle pw.subrange(q, j) = pw2.subrange(0, bigl) ∈ ⟨x⟩
            let bgens = Seq::new(data.associations.len(), |k: int| data.associations[k].1);
            let agens = Seq::new(data.associations.len(), |k: int| data.associations[k].0);
            assert(agens =~= seq![seq![Symbol::Gen(1)]]);
            assert(bgens =~= seq![seq![Symbol::Gen(1)]]);
            assert(pw.subrange(i + 1, j) =~= pw2.subrange(0, bigl)) by {
                assert forall|k: int| 0 <= k < bigl implies #[trigger] pw.subrange(i + 1, j)[k] == pw2[k]
                by { assert(pw.subrange(i + 1, j)[k] == pw[i + 1 + k] && pw[q + k] == pw2[k]); }
            }
            //  descend: pw2.subrange(0,bigl) = ψ_A(midw) = ψ_F(midw) ∈ ⟨x⟩ ⟹ midw ∈ ⟨x⟩
            assert(pw2.subrange(0, bigl) =~= apply_embedding(imgs, midw));
            lemma_psi_A_eq_psi_F_on_fword(p, q, midw);
            assert(apply_embedding(imgs, midw) =~= apply_embedding(psi_F_images(p), midw));
            assert(in_generated_subgroup(pres_tx(), seq![seq![Symbol::Gen(1)]],
                apply_embedding(psi_F_images(p), midw)));
            lemma_psi_F_in_x_subgroup(p, midw);
            assert(in_generated_subgroup(pres_tx(), seq![seq![Symbol::Gen(1)]], midw));
            //  reconstruct the pinch at (0, lp+1) of w
            assert(w.subrange(1, lp + 1) =~= midw);
            assert forall|k: int| 0 < k < lp + 1 implies !is_stable(data, #[trigger] w[k]) by {
                assert(w[k] == w2[k - 1]);
            }
            assert(has_adjacent_opposite_at(data, w, 0, lp + 1));
            assert(has_pinch_at(data, w, 0, lp + 1));
            assert(has_pinch(data, w)) by { assert(has_pinch_at(data, w, 0, lp + 1)); }
        }
    } else {
        //  c is t or x: ec = c^elen all non-stable; pinch endpoint i ≥ elen
        assert(c == Symbol::Gen(0) || c == Symbol::Inv(0)
            || c == Symbol::Gen(1) || c == Symbol::Inv(1));
        let elen: int = if c == Symbol::Gen(1) || c == Symbol::Inv(1) { p as int } else { 1int };
        if c == Symbol::Gen(0) {
            assert(ec =~= symbol_power(Symbol::Gen(0), 1));
        } else if c == Symbol::Inv(0) {
            assert(ec =~= symbol_power(Symbol::Inv(0), 1));
        } else if c == Symbol::Gen(1) {
            assert(ec =~= symbol_power(Symbol::Gen(1), p));
        } else {
            lemma_inverse_word_sympower(Symbol::Gen(1), p);
            assert(ec =~= symbol_power(Symbol::Inv(1), p));
        }
        assert(ec =~= symbol_power(c, elen as nat));
        assert(ec.len() == elen && elen >= 1);
        assert(forall|m: int| 0 <= m < elen ==> #[trigger] ec[m] == c);
        assert(forall|m: int| 0 <= m < elen ==> #[trigger] pw[m] == ec[m]);
        assert(i >= elen) by { if i < elen { assert(pw[i] == ec[i]); } }
        lemma_strip_prefix_preserves_pinch(data, ec, pw2, i, j);
        lemma_psi_A_pinch_descends(p, q, w2);
        lemma_prepend_preserves_pinch(data, c, w2);
    }
}

//  ============================================================
//  Step 2 (Q) + assembly:  pinch-out and ψ_A injectivity
//  ============================================================

//  x⁻¹ commutes with y in A:  [x⁻¹, y] ≡ [y, x⁻¹]  (derived from xy≡yx via xyx⁻¹≡y).
pub proof fn lemma_xinv_y_commute_in_A()
    ensures
        equiv_in_presentation(base_A(),
            seq![Symbol::Inv(1), Symbol::Gen(2)], seq![Symbol::Gen(2), Symbol::Inv(1)]),
{
    let a = base_A();
    let x = Symbol::Gen(1);
    let y = Symbol::Gen(2);
    let xi = Symbol::Inv(1);
    lemma_base_A_valid();
    lemma_xy_commute_in_A();
    lemma_equiv_concat_left(a, seq![x, y], seq![y, x], seq![xi]);
    assert(seq![x, y] + seq![xi] =~= seq![x, y, xi]);
    assert(seq![y, x] + seq![xi] =~= seq![y, x, xi]);
    lemma_cancel_pair_equiv_empty(a, x, xi);
    assert(seq![y, x, xi] =~= seq![y] + seq![x, xi]);
    lemma_equiv_concat_right(a, seq![y], seq![x, xi], empty_word());
    assert(seq![y] + empty_word() =~= seq![y]);
    lemma_equiv_transitive(a, seq![x, y, xi], seq![y, x, xi], seq![y]);
    assert(seq![x] + seq![y] + seq![xi] =~= seq![x, y, xi]);
    assert(presentation_valid(a)) by { reveal(presentation_valid); }
    lemma_commute_from_conj(a, xi, x, seq![y]);
    assert(seq![xi] + seq![y] =~= seq![xi, y]);
    assert(seq![y] + seq![xi] =~= seq![y, xi]);
}

//  x commutes with y⁻¹ in A:  [x, y⁻¹] ≡ [y⁻¹, x]  (derived from xy≡yx via yxy⁻¹≡x).
pub proof fn lemma_x_yinv_commute_in_A()
    ensures
        equiv_in_presentation(base_A(),
            seq![Symbol::Gen(1), Symbol::Inv(2)], seq![Symbol::Inv(2), Symbol::Gen(1)]),
{
    let a = base_A();
    let x = Symbol::Gen(1);
    let y = Symbol::Gen(2);
    let yi = Symbol::Inv(2);
    lemma_base_A_valid();
    lemma_xy_commute_in_A();
    lemma_equiv_symmetric(a, seq![x, y], seq![y, x]);
    lemma_equiv_concat_left(a, seq![y, x], seq![x, y], seq![yi]);
    assert(seq![y, x] + seq![yi] =~= seq![y, x, yi]);
    assert(seq![x, y] + seq![yi] =~= seq![x, y, yi]);
    lemma_cancel_pair_equiv_empty(a, y, yi);
    assert(seq![x, y, yi] =~= seq![x] + seq![y, yi]);
    lemma_equiv_concat_right(a, seq![x], seq![y, yi], empty_word());
    assert(seq![x] + empty_word() =~= seq![x]);
    lemma_equiv_transitive(a, seq![y, x, yi], seq![x, y, yi], seq![x]);
    assert(seq![y] + seq![x] + seq![yi] =~= seq![y, x, yi]);
    assert(presentation_valid(a)) by { reveal(presentation_valid); }
    lemma_commute_from_conj(a, yi, y, seq![x]);
    assert(seq![yi] + seq![x] =~= seq![yi, x]);
    assert(seq![x] + seq![yi] =~= seq![x, yi]);
    lemma_equiv_symmetric(a, seq![yi, x], seq![x, yi]);
}

//  x^k commutes with a stable letter y / y⁻¹ in A.
pub proof fn lemma_x_pow_commutes_stable(k: int, si: Symbol)
    requires
        si == Symbol::Gen(2) || si == Symbol::Inv(2),
    ensures
        equiv_in_presentation(base_A(), x_pow(k) + seq![si], seq![si] + x_pow(k)),
{
    let a = base_A();
    lemma_base_A_valid();
    assert(presentation_valid(a)) by { reveal(presentation_valid); }
    assert(symbol_power(si, 1) =~= seq![si]);
    if k >= 0 {
        let n = k as nat;
        assert(x_pow(k) =~= symbol_power(Symbol::Gen(1), n));
        if si == Symbol::Gen(2) {
            lemma_xy_commute_in_A();
            lemma_power_commutes(a, Symbol::Gen(1), Symbol::Gen(2), n, 1);
        } else {
            lemma_x_yinv_commute_in_A();
            lemma_power_commutes(a, Symbol::Gen(1), Symbol::Inv(2), n, 1);
        }
        assert(x_pow(k) + seq![si] =~= symbol_power(Symbol::Gen(1), n) + symbol_power(si, 1));
        assert(seq![si] + x_pow(k) =~= symbol_power(si, 1) + symbol_power(Symbol::Gen(1), n));
    } else {
        let n = (-k) as nat;
        assert(x_pow(k) =~= symbol_power(Symbol::Inv(1), n));
        if si == Symbol::Gen(2) {
            lemma_xinv_y_commute_in_A();
            lemma_power_commutes(a, Symbol::Inv(1), Symbol::Gen(2), n, 1);
        } else {
            lemma_xinv_yinv_commute_in_A();
            let wv: Word = seq![Symbol::Inv(2), Symbol::Inv(1)];
            assert(word_valid(wv, 3)) by {
                assert forall|m: int| 0 <= m < wv.len()
                    implies symbol_valid(#[trigger] wv[m], 3) by {}
            }
            lemma_equiv_symmetric(a, seq![Symbol::Inv(2), Symbol::Inv(1)],
                seq![Symbol::Inv(1), Symbol::Inv(2)]);
            lemma_power_commutes(a, Symbol::Inv(1), Symbol::Inv(2), n, 1);
        }
        assert(x_pow(k) + seq![si] =~= symbol_power(Symbol::Inv(1), n) + symbol_power(si, 1));
        assert(seq![si] + x_pow(k) =~= symbol_power(si, 1) + symbol_power(Symbol::Inv(1), n));
    }
}

//  Base faithfulness for A:  an F-word (over t,x) trivial in A is trivial in F.
//  The injectivity base case (no y) lands here.
pub proof fn lemma_a_base_faithful(w: Word)
    requires
        word_valid(w, 2),
        equiv_in_presentation(base_A(), w, empty_word()),
    ensures
        equiv_in_presentation(pres_tx(), w, empty_word()),
{
    lemma_a_as_hnn_valid();
    lemma_a_as_hnn_isomorphic();
    assert(word_valid(w, 3)) by {
        assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], 3)
        by { assert(symbol_valid(w[k], 2)); }
    }
    lemma_base_A_to_a_hnn(w, empty_word());
    lemma_single_hnn_base_faithful(a_as_hnn(), w);
}

//  (Q) at the A-level:  deleting a y-pinch (y·u·y⁻¹ with u∈⟨x⟩) removes the two y's,
//  keeping the (commuting) middle.  w ≡ w with positions i, j deleted.
pub proof fn lemma_pinch_out_A(w: Word, i: int, j: int)
    requires
        word_valid(w, 3),
        has_pinch_at(a_as_hnn(), w, i, j),
    ensures
        equiv_in_presentation(base_A(),
            w, w.subrange(0, i) + w.subrange(i + 1, j) + w.subrange(j + 1, w.len() as int)),
{
    let data = a_as_hnn();
    let a = base_A();
    lemma_base_A_valid();
    assert(presentation_valid(a)) by { reveal(presentation_valid); }
    assert(data.base.num_generators == 2);
    assert(has_adjacent_opposite_at(data, w, i, j));
    assert(0 <= i < j < w.len());
    let si = w[i];
    let sj = w[j];
    let u = w.subrange(i + 1, j);
    assert(is_stable(data, si) && is_stable(data, sj) && si != sj);
    assert(word_valid(u, 3)) by {
        assert forall|k: int| 0 <= k < u.len() implies symbol_valid(#[trigger] u[k], 3)
        by { assert(u[k] == w[i + 1 + k]); }
    }
    let agens = Seq::new(data.associations.len(), |k: int| data.associations[k].0);
    let bgens = Seq::new(data.associations.len(), |k: int| data.associations[k].1);
    assert(agens =~= seq![seq![Symbol::Gen(1)]]);
    assert(bgens =~= seq![seq![Symbol::Gen(1)]]);
    //  extract u ∈ ⟨x⟩ and the inverse-pair endpoints
    assert(is_inverse_pair(si, sj) && in_generated_subgroup(pres_tx(), seq![seq![Symbol::Gen(1)]], u)) by {
        if si == Symbol::Gen(2) {
            assert(sj == Symbol::Inv(2));
            assert(in_generated_subgroup(pres_tx(), bgens, u));
        } else {
            assert(si == Symbol::Inv(2) && sj == Symbol::Gen(2));
            assert(in_generated_subgroup(pres_tx(), agens, u));
        }
    }
    let k = x_exp_sum(u);
    let xk = x_pow(k);
    lemma_x_pow_valid(k);
    assert(word_valid(xk, 3)) by {
        assert forall|m: int| 0 <= m < xk.len() implies symbol_valid(#[trigger] xk[m], 3)
        by { assert(symbol_valid(xk[m], 2)); }
    }
    //  u ≡_A xk
    lemma_x_subgroup_is_pow(u);
    lemma_base_embeds_in_hnn(data, u, xk);
    lemma_a_hnn_to_base_A(u, xk);
    assert(equiv_in_presentation(a, u, xk));
    lemma_equiv_symmetric(a, u, xk);
    //  conjugation:  [si]+xk+[sj] ≡ xk
    lemma_x_pow_commutes_stable(k, si);                 //  xk+[si] ≡ [si]+xk
    lemma_equiv_symmetric(a, xk + seq![si], seq![si] + xk);
    lemma_equiv_concat_left(a, seq![si] + xk, xk + seq![si], seq![sj]);
    assert((seq![si] + xk) + seq![sj] =~= seq![si] + xk + seq![sj]);
    assert((xk + seq![si]) + seq![sj] =~= xk + seq![si, sj]);
    lemma_cancel_pair_equiv_empty(a, si, sj);
    lemma_equiv_concat_right(a, xk, seq![si, sj], empty_word());
    assert(xk + empty_word() =~= xk);
    lemma_equiv_transitive(a, seq![si] + xk + seq![sj], xk + seq![si, sj], xk);
    //  mid = [si]+u+[sj] ≡ [si]+xk+[sj] ≡ xk ≡ u
    let mid = w.subrange(i, j + 1);
    assert(mid =~= seq![si] + u + seq![sj]);
    lemma_equiv_concat_right(a, seq![si], u, xk);
    lemma_equiv_concat_left(a, seq![si] + u, seq![si] + xk, seq![sj]);
    assert((seq![si] + u) + seq![sj] =~= seq![si] + u + seq![sj]);
    assert((seq![si] + xk) + seq![sj] =~= seq![si] + xk + seq![sj]);
    lemma_equiv_transitive(a, seq![si] + u + seq![sj], seq![si] + xk + seq![sj], xk);
    lemma_equiv_transitive(a, seq![si] + u + seq![sj], xk, u);
    assert(equiv_in_presentation(a, mid, u));
    //  w = w[0..i] + mid + w[j+1..] ≡ w[0..i] + u + w[j+1..]
    let pre = w.subrange(0, i);
    let post = w.subrange(j + 1, w.len() as int);
    assert(w =~= pre + mid + post);
    lemma_equiv_concat_right(a, pre, mid, u);
    lemma_equiv_concat_left(a, pre + mid, pre + u, post);
    assert((pre + mid) + post =~= pre + mid + post);
    assert((pre + u) + post =~= pre + u + post);
    assert(pre + u + post =~= pre + w.subrange(i + 1, j) + post);
}

//  No y (stable_count 0) ⟹ every symbol is non-stable.
pub proof fn lemma_stable_count_zero_no_stable(data: HNNData, w: Word)
    requires
        stable_count(data, w) == 0,
    ensures
        forall|k: int| 0 <= k < w.len() ==> !is_stable(data, #[trigger] w[k]),
    decreases w.len(),
{
    reveal_with_fuel(stable_count, 2);
    if w.len() == 0 {
    } else {
        let pre = w.drop_last();
        lemma_stable_count_zero_no_stable(data, pre);
        assert(forall|k: int| 0 <= k < pre.len() ==> pre[k] == w[k]);
        assert(!is_stable(data, w[w.len() - 1]));
    }
}

//  THE STEP-2 CAPSTONE:  ψ_A is injective on A.
//  equiv_in_presentation(base_A, ψ_A(w), ε)  ⟹  equiv_in_presentation(base_A, w, ε).
pub proof fn lemma_psi_A_injective(p: nat, q: nat, w: Word)
    requires
        word_valid(w, 3),
        p >= 1,
        q >= 1,
        equiv_in_presentation(base_A(), apply_embedding(psi_images(p, q), w), empty_word()),
    ensures
        equiv_in_presentation(base_A(), w, empty_word()),
    decreases w.len(),
{
    let data = a_as_hnn();
    let a = base_A();
    let imgs = psi_images(p, q);
    let pw = apply_embedding(imgs, w);
    lemma_a_as_hnn_valid();
    lemma_a_as_hnn_isomorphic();
    lemma_a_as_hnn_presentation();
    lemma_base_A_valid();
    assert(presentation_valid(a)) by { reveal(presentation_valid); }
    assert(data.base.num_generators == 2);
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    assert(imgs[2] =~= symbol_power(Symbol::Gen(2), q));
    assert forall|kk: int| 0 <= kk < imgs.len() implies word_valid(#[trigger] imgs[kk], 3) by {
        if kk == 0 {
            assert forall|m: int| 0 <= m < imgs[0].len() implies symbol_valid(#[trigger] imgs[0][m], 3)
            by { assert(imgs[0][m] == Symbol::Gen(0)); }
        } else if kk == 1 {
            lemma_symbol_power_valid(Symbol::Gen(1), p, 3);
        } else {
            lemma_symbol_power_valid(Symbol::Gen(2), q, 3);
        }
    }
    if stable_count(data, w) == 0 {
        //  base case: no y ⟹ w is an F-word, ψ_A(w) = ψ_F(w)
        lemma_stable_count_zero_no_stable(data, w);
        assert(word_valid(w, 2)) by {
            assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], 2) by {
                assert(!is_stable(data, w[k]));
                assert(symbol_valid(w[k], 3));
            }
        }
        lemma_psi_A_eq_psi_F_on_fword(p, q, w);
        let pwf = apply_embedding(psi_F_images(p), w);
        assert(equiv_in_presentation(a, pwf, empty_word()));
        assert forall|kk: int| 0 <= kk < psi_F_images(p).len()
            implies word_valid(#[trigger] psi_F_images(p)[kk], 2) by {
            if kk == 0 {
                assert forall|m: int| 0 <= m < psi_F_images(p)[0].len()
                    implies symbol_valid(#[trigger] psi_F_images(p)[0][m], 2)
                by { assert(psi_F_images(p)[0][m] == Symbol::Gen(0)); }
            } else {
                lemma_symbol_power_valid(Symbol::Gen(1), p, 2);
            }
        }
        lemma_apply_embedding_valid(psi_F_images(p), w, 2);
        lemma_a_base_faithful(pwf);
        lemma_psi_F_injective(p, w);
        lemma_base_embeds_in_hnn(data, w, empty_word());
        lemma_a_hnn_to_base_A(w, empty_word());
    } else {
        //  step case: ψ_A(w) has a y, hence a pinch
        lemma_psi_A_stable_count_scales(p, q, w);
        assert(stable_count(data, w) >= 1);
        assert(q * stable_count(data, w) >= 1) by (nonlinear_arith)
            requires q >= 1, stable_count(data, w) >= 1;
        assert(stable_count(data, pw) >= 1);
        lemma_apply_embedding_valid(imgs, w, 3);
        lemma_stable_count_pos_has_stable(data, pw);
        lemma_base_A_to_a_hnn(pw, empty_word());
        if !has_pinch(data, pw) {
            lemma_no_pinch_stable_nontrivial(data, pw);
        }
        assert(has_pinch(data, pw));
        lemma_psi_A_pinch_descends(p, q, w);
        let ij: (int, int) = choose|i: int, j: int| has_pinch_at(data, w, i, j);
        let i = ij.0;
        let j = ij.1;
        assert(has_pinch_at(data, w, i, j));
        assert(has_adjacent_opposite_at(data, w, i, j));
        let wshort: Word =
            w.subrange(0, i) + w.subrange(i + 1, j) + w.subrange(j + 1, w.len() as int);
        lemma_pinch_out_A(w, i, j);
        assert(wshort.len() < w.len());
        assert(word_valid(w.subrange(0, i), 3)) by {
            assert forall|k: int| 0 <= k < w.subrange(0, i).len()
                implies symbol_valid(#[trigger] w.subrange(0, i)[k], 3)
            by { assert(w.subrange(0, i)[k] == w[k]); }
        }
        assert(word_valid(w.subrange(i + 1, j), 3)) by {
            assert forall|k: int| 0 <= k < w.subrange(i + 1, j).len()
                implies symbol_valid(#[trigger] w.subrange(i + 1, j)[k], 3)
            by { assert(w.subrange(i + 1, j)[k] == w[k + i + 1]); }
        }
        assert(word_valid(w.subrange(j + 1, w.len() as int), 3)) by {
            assert forall|k: int| 0 <= k < w.subrange(j + 1, w.len() as int).len()
                implies symbol_valid(#[trigger] w.subrange(j + 1, w.len() as int)[k], 3)
            by { assert(w.subrange(j + 1, w.len() as int)[k] == w[k + j + 1]); }
        }
        lemma_concat_word_valid(w.subrange(0, i), w.subrange(i + 1, j), 3);
        lemma_concat_word_valid(w.subrange(0, i) + w.subrange(i + 1, j),
            w.subrange(j + 1, w.len() as int), 3);
        //  ψ_A respects ≡ over base_A (ψ kills the relator)
        lemma_psi_respects_relator(p, q);
        let pws = apply_embedding(imgs, wshort);
        lemma_emb_respects_source_equiv(a, a, imgs, w, wshort);
        lemma_equiv_symmetric(a, pw, pws);
        lemma_equiv_transitive(a, pws, pw, empty_word());
        lemma_psi_A_injective(p, q, wshort);
        lemma_equiv_transitive(a, w, wshort, empty_word());
    }
}

//  ============================================================
//  Property (iii): the quad associations are isomorphic
//  ============================================================
//
//  The rᵢ/lⱼ conjugation t(a,b)↦t(c,0), xᵐ↦xᵐ², yᵐ↦y must be an isomorphism of
//  the associated subgroups for the HNN extension to be valid (Britton).  Route:
//  t(a,b) = (xᵃyᵇ)⁻¹·t·(xᵃyᵇ), and xᵃyᵇ commutes with xᵐ,yᵐ, so the a-side word
//  emb([t(a,b),xᵐ,yᵐ],w) is a conjugate of the scaling ψ_{m,m}(w); it is trivial
//  iff ψ_{m,m}(w) is iff w is (ψ_A injectivity).  Same for the b-side via ψ_{m²,1}.

//  Conjugation by a commuting element is trivial:  a·b ≡ b·a  ⟹  a⁻¹·b·a ≡ b.
pub proof fn lemma_conj_of_commuting(p: Presentation, aw: Word, bw: Word)
    requires
        presentation_valid(p),
        word_valid(aw, p.num_generators),
        word_valid(bw, p.num_generators),
        equiv_in_presentation(p, aw + bw, bw + aw),
    ensures
        equiv_in_presentation(p, inverse_word(aw) + bw + aw, bw),
{
    let ng = p.num_generators;
    let ia = inverse_word(aw);
    lemma_inverse_word_valid(aw, ng);
    //  bw·aw ≡ aw·bw  (symmetric of the hypothesis)
    lemma_concat_word_valid(aw, bw, ng);
    lemma_equiv_symmetric(p, aw + bw, bw + aw);
    //  ia·(bw·aw) ≡ ia·(aw·bw)
    lemma_equiv_concat_right(p, ia, bw + aw, aw + bw);
    assert(ia + bw + aw =~= ia + (bw + aw));
    assert(ia + (aw + bw) =~= (ia + aw) + bw);
    //  (ia·aw)·bw ≡ ε·bw ≡ bw
    lemma_word_inverse_left(p, aw);                     //  ia + aw ≡ ε
    lemma_equiv_concat_left(p, ia + aw, empty_word(), bw);
    assert(empty_word() + bw =~= bw);
    //  chain:  ia·bw·aw ≡ ia·(aw·bw) ≡ bw
    lemma_equiv_transitive(p, ia + bw + aw, ia + (aw + bw), bw);
}

//  xᵃyᵇ commutes with xᵐ in A.
pub proof fn lemma_xayb_commutes_xpow(a: nat, b: nat, m: nat)
    ensures
        equiv_in_presentation(base_A(),
            (symbol_power(Symbol::Gen(1), a) + symbol_power(Symbol::Gen(2), b))
                + symbol_power(Symbol::Gen(1), m),
            symbol_power(Symbol::Gen(1), m)
                + (symbol_power(Symbol::Gen(1), a) + symbol_power(Symbol::Gen(2), b))),
{
    let aa = base_A();
    lemma_base_A_valid();
    assert(presentation_valid(aa)) by { reveal(presentation_valid); }
    let xa = symbol_power(Symbol::Gen(1), a);
    let yb = symbol_power(Symbol::Gen(2), b);
    let xm = symbol_power(Symbol::Gen(1), m);
    //  yᵇ·xᵐ ~ xᵐ·yᵇ
    lemma_xy_commute_in_A();
    let xy: Word = seq![Symbol::Gen(1), Symbol::Gen(2)];
    assert(word_valid(xy, 3)) by {
        assert forall|k: int| 0 <= k < xy.len() implies symbol_valid(#[trigger] xy[k], 3) by { }
    }
    lemma_equiv_symmetric(aa, xy, seq![Symbol::Gen(2), Symbol::Gen(1)]);
    lemma_power_commutes(aa, Symbol::Gen(2), Symbol::Gen(1), b, m);
    //  xᵃ·(yᵇ·xᵐ) ~ xᵃ·(xᵐ·yᵇ)
    lemma_equiv_concat_right(aa, xa, yb + xm, xm + yb);
    //  xᵃ·xᵐ =~= xᵐ·xᵃ
    lemma_symbol_power_merge(Symbol::Gen(1), a, m);
    lemma_symbol_power_merge(Symbol::Gen(1), m, a);
    assert(xa + xm =~= xm + xa);
    //  assemble  (xa+yb)+xm =~= xa+(yb+xm) ~ xa+(xm+yb) =~= (xm+xa)+yb =~= xm+(xa+yb)
    assert((xa + yb) + xm =~= xa + (yb + xm));
    assert(xa + (xm + yb) =~= xm + (xa + yb));
}

//  xᵃyᵇ commutes with yᵐ in A.
pub proof fn lemma_xayb_commutes_ypow(a: nat, b: nat, m: nat)
    ensures
        equiv_in_presentation(base_A(),
            (symbol_power(Symbol::Gen(1), a) + symbol_power(Symbol::Gen(2), b))
                + symbol_power(Symbol::Gen(2), m),
            symbol_power(Symbol::Gen(2), m)
                + (symbol_power(Symbol::Gen(1), a) + symbol_power(Symbol::Gen(2), b))),
{
    let aa = base_A();
    lemma_base_A_valid();
    assert(presentation_valid(aa)) by { reveal(presentation_valid); }
    let xa = symbol_power(Symbol::Gen(1), a);
    let yb = symbol_power(Symbol::Gen(2), b);
    let ym = symbol_power(Symbol::Gen(2), m);
    //  xᵃ·yᵐ ~ yᵐ·xᵃ
    lemma_xy_commute_in_A();
    lemma_power_commutes(aa, Symbol::Gen(1), Symbol::Gen(2), a, m);
    //  yᵇ·yᵐ =~= yᵐ·yᵇ
    lemma_symbol_power_merge(Symbol::Gen(2), b, m);
    lemma_symbol_power_merge(Symbol::Gen(2), m, b);
    assert(yb + ym =~= ym + yb);
    //  (xa+yb)+ym =~= xa+(yb+ym) =~= xa+(ym+yb) =~= (xa+ym)+yb ~ (ym+xa)+yb =~= ym+(xa+yb)
    assert((xa + yb) + ym =~= (xa + ym) + yb);
    lemma_equiv_concat_left(aa, xa + ym, ym + xa, yb);
    assert((ym + xa) + yb =~= ym + (xa + yb));
}

//  ψ_{p,q} is trivial-faithful:  ψ(w) ≡ ε  ⟺  w ≡ ε  (in A).
pub proof fn lemma_psi_trivial_iff(p: nat, q: nat, w: Word)
    requires
        word_valid(w, 3),
        p >= 1,
        q >= 1,
    ensures
        equiv_in_presentation(base_A(), apply_embedding(psi_images(p, q), w), empty_word())
            <==> equiv_in_presentation(base_A(), w, empty_word()),
{
    let aa = base_A();
    let imgs = psi_images(p, q);
    lemma_base_A_valid();
    assert(presentation_valid(aa)) by { reveal(presentation_valid); }
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= symbol_power(Symbol::Gen(1), p));
    assert(imgs[2] =~= symbol_power(Symbol::Gen(2), q));
    assert forall|i: int| 0 <= i < imgs.len() implies word_valid(#[trigger] imgs[i], 3) by {
        if i == 0 {
            assert(word_valid(imgs[0], 3)) by {
                assert forall|kk: int| 0 <= kk < imgs[0].len() implies symbol_valid(#[trigger] imgs[0][kk], 3) by { }
            }
        } else if i == 1 {
            lemma_symbol_power_valid(Symbol::Gen(1), p, 3);
        } else {
            lemma_symbol_power_valid(Symbol::Gen(2), q, 3);
        }
    }
    //  forward:  ψ(w) ≡ ε  ⟹  w ≡ ε
    if equiv_in_presentation(aa, apply_embedding(imgs, w), empty_word()) {
        lemma_psi_A_injective(p, q, w);
    }
    //  backward:  w ≡ ε  ⟹  ψ(w) ≡ ψ(ε) = ε
    if equiv_in_presentation(aa, w, empty_word()) {
        assert forall|j: int| 0 <= j < aa.relators.len()
            implies equiv_in_presentation(aa, apply_embedding(imgs, #[trigger] aa.relators[j]), empty_word())
        by { lemma_psi_respects_relator(p, q); }
        lemma_emb_respects_source_equiv(aa, aa, imgs, w, empty_word());
        assert(apply_embedding(imgs, empty_word()) =~= empty_word());
    }
}

//  The conjugated scaling is trivial-faithful: for g = xᵃyᵇ,
//  emb([t(a,b), x^px, y^py], w) ≡ ε  ⟺  w ≡ ε.   (serves both quad sides)
pub proof fn lemma_conj_scaling_trivial_iff(a: nat, b: nat, px: nat, py: nat, w: Word)
    requires
        px >= 1,
        py >= 1,
        word_valid(w, 3),
    ensures
        equiv_in_presentation(base_A(),
            apply_embedding(seq![config_word(a, b), symbol_power(Symbol::Gen(1), px),
                symbol_power(Symbol::Gen(2), py)], w),
            empty_word())
        <==> equiv_in_presentation(base_A(), w, empty_word()),
{
    let aa = base_A();
    lemma_base_A_valid();
    assert(presentation_valid(aa)) by { reveal(presentation_valid); }
    reveal_with_fuel(inverse_word, 2);
    let xpx = symbol_power(Symbol::Gen(1), px);
    let ypy = symbol_power(Symbol::Gen(2), py);
    let g = symbol_power(Symbol::Gen(1), a) + symbol_power(Symbol::Gen(2), b);
    let ig = inverse_word(g);
    let imgs = psi_images(px, py);
    let aw: Seq<Word> = seq![config_word(a, b), xpx, ypy];
    let ci = conj_images(g, imgs);
    let pw = apply_embedding(imgs, w);
    //  validity of g and ig
    lemma_symbol_power_valid(Symbol::Gen(1), a, 3);
    lemma_symbol_power_valid(Symbol::Gen(2), b, 3);
    lemma_concat_word_valid(symbol_power(Symbol::Gen(1), a), symbol_power(Symbol::Gen(2), b), 3);
    lemma_inverse_word_valid(g, 3);
    //  imgs structure + validity
    assert(imgs[0] =~= seq![Symbol::Gen(0)]);
    assert(imgs[1] =~= xpx);
    assert(imgs[2] =~= ypy);
    lemma_symbol_power_valid(Symbol::Gen(1), px, 3);
    lemma_symbol_power_valid(Symbol::Gen(2), py, 3);
    //  ig = x⁻ᵃ y⁻ᵇ  (reversed); config_word(a,b) =~= ig + [t] + g
    lemma_inverse_word_concat(symbol_power(Symbol::Gen(1), a), symbol_power(Symbol::Gen(2), b));
    lemma_inverse_word_sympower(Symbol::Gen(1), a);
    lemma_inverse_word_sympower(Symbol::Gen(2), b);
    assert(config_word(a, b) =~= ig + seq![Symbol::Gen(0)] + g);
    //  componentwise equiv  aw[i] ≡ ci[i]
    assert(ci[0] =~= ig + seq![Symbol::Gen(0)] + g);
    assert(ci[1] =~= ig + xpx + g);
    assert(ci[2] =~= ig + ypy + g);
    lemma_xayb_commutes_xpow(a, b, px);
    lemma_conj_of_commuting(aa, g, xpx);                   //  ig·xpx·g ≡ xpx
    lemma_equiv_symmetric(aa, ig + xpx + g, xpx);
    lemma_xayb_commutes_ypow(a, b, py);
    lemma_conj_of_commuting(aa, g, ypy);
    lemma_equiv_symmetric(aa, ig + ypy + g, ypy);
    //  validities for respects_image_equiv
    lemma_config_word_valid(a, b);
    lemma_concat_word_valid(ig + xpx, g, 3);
    lemma_concat_word_valid(ig, xpx, 3);
    lemma_concat_word_valid(ig + ypy, g, 3);
    lemma_concat_word_valid(ig, ypy, 3);
    lemma_concat_word_valid(ig + seq![Symbol::Gen(0)], g, 3);
    assert(word_valid(seq![Symbol::Gen(0)], 3)) by {
        assert forall|kk: int| 0 <= kk < 1 implies symbol_valid(#[trigger] seq![Symbol::Gen(0)][kk], 3) by { }
    }
    lemma_concat_word_valid(ig, seq![Symbol::Gen(0)], 3);
    assert forall|i: int| 0 <= i < 3 implies (word_valid(#[trigger] aw[i], 3)
        && word_valid(ci[i], 3) && equiv_in_presentation(aa, aw[i], ci[i])) by {
        if i == 0 {
            lemma_equiv_refl(aa, aw[0]);
        } else if i == 1 {
        } else {
        }
    }
    //  emb(aw,w) ≡ emb(ci,w) ≡ ig·pw·g
    lemma_apply_embedding_respects_image_equiv(aa, aw, ci, w, 3);
    lemma_emb_conj_telescope(aa, g, imgs, w, 3);
    lemma_equiv_transitive(aa, apply_embedding(aw, w), apply_embedding(ci, w), ig + pw + g);
    //  ⟺ chain:  emb(aw,w)≡ε  ⟺  ig·pw·g≡ε  ⟺  pw≡ε  ⟺  w≡ε
    lemma_conj_trivial_iff(aa, g, pw);
    lemma_psi_trivial_iff(px, py, w);
    lemma_apply_embedding_valid(aw, w, 3);
    //  bridge emb(aw,w)≡ε ⟺ ig·pw·g≡ε via the established equiv
    if equiv_in_presentation(aa, apply_embedding(aw, w), empty_word()) {
        lemma_equiv_symmetric(aa, apply_embedding(aw, w), ig + pw + g);
        lemma_equiv_transitive(aa, ig + pw + g, apply_embedding(aw, w), empty_word());
    }
    if equiv_in_presentation(aa, ig + pw + g, empty_word()) {
        lemma_equiv_transitive(aa, apply_embedding(aw, w), ig + pw + g, empty_word());
    }
}

//  Property (iii) for an R-quad: the associations are isomorphic.
pub proof fn lemma_r_step_associations_isomorphic(a: nat, b: nat, c: nat, m: nat)
    requires
        m >= 1,
    ensures
        hnn_associations_isomorphic(r_step_data(a, b, c, m)),
{
    let data = r_step_data(a, b, c, m);
    let k = data.associations.len();
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    assert(k == 3);
    assert(a_words =~= seq![config_word(a, b), symbol_power(Symbol::Gen(1), m),
        symbol_power(Symbol::Gen(2), m)]);
    assert(b_words =~= seq![config_word(c, 0), symbol_power(Symbol::Gen(1), m * m),
        symbol_power(Symbol::Gen(2), 1)]);
    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word())
    ) by {
        assert(word_valid(w, 3));
        assert(m * m >= 1) by (nonlinear_arith) requires m >= 1;
        lemma_conj_scaling_trivial_iff(a, b, m, m, w);
        lemma_conj_scaling_trivial_iff(c, 0, m * m, 1, w);
    }
}

//  Property (iii) for an L-quad: the associations are isomorphic.
pub proof fn lemma_l_step_associations_isomorphic(a: nat, b: nat, c: nat, m: nat)
    requires
        m >= 1,
    ensures
        hnn_associations_isomorphic(l_step_data(a, b, c, m)),
{
    let data = l_step_data(a, b, c, m);
    let k = data.associations.len();
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    assert(k == 3);
    assert(a_words =~= seq![config_word(a, b), symbol_power(Symbol::Gen(1), m),
        symbol_power(Symbol::Gen(2), m)]);
    assert(b_words =~= seq![config_word(0, c), symbol_power(Symbol::Gen(1), 1),
        symbol_power(Symbol::Gen(2), m * m)]);
    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word())
    ) by {
        assert(word_valid(w, 3));
        assert(m * m >= 1) by (nonlinear_arith) requires m >= 1;
        lemma_conj_scaling_trivial_iff(a, b, m, m, w);
        lemma_conj_scaling_trivial_iff(0, c, 1, m * m, w);
    }
}

//  ============================================================
//  Tower base-faithfulness: an A-word trivial in B(M) up to level i is
//  trivial in A.  Lifts property (iii) to every tower level (the per-step
//  iso is built inline from the induction hypothesis).
//  ============================================================
pub proof fn lemma_b_m_upto_faithful(mm: ModMachine, i: nat, w: Word)
    requires
        mod_machine_wf(mm),
        i <= mm.quads.len(),
        word_valid(w, 3),
        equiv_in_presentation(b_m_upto(mm, i), w, empty_word()),
    ensures
        equiv_in_presentation(base_A(), w, empty_word()),
    decreases i,
{
    if i == 0 {
        assert(b_m_upto(mm, 0) == base_A());
    } else {
        let qi = (i - 1) as nat;
        let q = mm.quads[qi as int];
        let m = mm.m;
        let base = b_m_upto(mm, qi);
        let assoc = quad_associations(q, m);
        let step = HNNData { base, associations: assoc };
        assert(b_m_upto(mm, i) == hnn_presentation(step));
        lemma_b_m_upto_valid(mm, qi);
        lemma_b_m_upto_num_generators(mm, qi);
        assert(base.num_generators == (3 + qi) as nat);
        let k = assoc.len();
        assert(k == 3);
        let a_words = Seq::new(k, |idx: int| assoc[idx].0);
        let b_words = Seq::new(k, |idx: int| assoc[idx].1);
        //  a-side is the same for R and L:  [t(a,b), xᵐ, yᵐ]
        assert(a_words =~= seq![config_word(q.a, q.b), symbol_power(Symbol::Gen(1), m),
            symbol_power(Symbol::Gen(2), m)]);
        //  ---- (1) the per-step iso, built inline from the IH ----
        lemma_quad_associations_valid(q, m, 3);
        assert(hnn_associations_isomorphic(step)) by {
            assert forall|ww: Word| word_valid(ww, k as nat) implies (
                equiv_in_presentation(base, apply_embedding(a_words, ww), empty_word())
                <==> equiv_in_presentation(base, apply_embedding(b_words, ww), empty_word())
            ) by {
                assert(m >= 1);
                assert(m * m >= 1) by (nonlinear_arith) requires m >= 1;
                lemma_quad_associations_valid(q, m, 3);
                lemma_apply_embedding_valid(a_words, ww, 3);
                lemma_apply_embedding_valid(b_words, ww, 3);
                let ea = apply_embedding(a_words, ww);
                let eb = apply_embedding(b_words, ww);
                //  a-side:  emb(a_words,ww)≡_base ε  ⟺  ww≡_A ε
                lemma_conj_scaling_trivial_iff(q.a, q.b, m, m, ww);
                assert(apply_embedding(seq![config_word(q.a, q.b), symbol_power(Symbol::Gen(1), m),
                    symbol_power(Symbol::Gen(2), m)], ww) =~= ea);
                if equiv_in_presentation(base, ea, empty_word()) {
                    lemma_b_m_upto_faithful(mm, qi, ea);
                }
                if equiv_in_presentation(base_A(), ea, empty_word()) {
                    lemma_lift_bm_level(mm, 0, qi, ea, empty_word());
                }
                //  b-side:  dispatch on direction, same bridge
                match q.dir {
                    Dir::R => {
                        assert(b_words =~= seq![config_word(q.c, 0), symbol_power(Symbol::Gen(1), m * m),
                            symbol_power(Symbol::Gen(2), 1)]);
                        lemma_conj_scaling_trivial_iff(q.c, 0, m * m, 1, ww);
                        assert(apply_embedding(seq![config_word(q.c, 0), symbol_power(Symbol::Gen(1), m * m),
                            symbol_power(Symbol::Gen(2), 1)], ww) =~= eb);
                    }
                    Dir::L => {
                        assert(b_words =~= seq![config_word(0, q.c), symbol_power(Symbol::Gen(1), 1),
                            symbol_power(Symbol::Gen(2), m * m)]);
                        lemma_conj_scaling_trivial_iff(0, q.c, 1, m * m, ww);
                        assert(apply_embedding(seq![config_word(0, q.c), symbol_power(Symbol::Gen(1), 1),
                            symbol_power(Symbol::Gen(2), m * m)], ww) =~= eb);
                    }
                }
                if equiv_in_presentation(base, eb, empty_word()) {
                    lemma_b_m_upto_faithful(mm, qi, eb);
                }
                if equiv_in_presentation(base_A(), eb, empty_word()) {
                    lemma_lift_bm_level(mm, 0, qi, eb, empty_word());
                }
            }
        }
        //  ---- (2) hnn_data_valid(step) ----
        lemma_quad_associations_valid(q, m, base.num_generators);
        assert(hnn_data_valid(step));
        //  ---- (3) descend one level via single-HNN base faithfulness ----
        lemma_word_valid_mono(w, 3, base.num_generators);
        lemma_single_hnn_base_faithful(step, w);
        //  ---- (4) descend the rest by induction ----
        lemma_b_m_upto_faithful(mm, qi, w);
    }
}

//  The qi-th B(M) tower step's associations are isomorphic (exposed as a
//  standalone fact for Britton, via the now-proven tower base-faithfulness).
pub proof fn lemma_b_m_step_isomorphic(mm: ModMachine, qi: nat)
    requires
        mod_machine_wf(mm),
        qi < mm.quads.len(),
    ensures
        hnn_associations_isomorphic(HNNData {
            base: b_m_upto(mm, qi),
            associations: quad_associations(mm.quads[qi as int], mm.m),
        }),
{
    let q = mm.quads[qi as int];
    let m = mm.m;
    let base = b_m_upto(mm, qi);
    let assoc = quad_associations(q, m);
    let step = HNNData { base, associations: assoc };
    lemma_b_m_upto_valid(mm, qi);
    lemma_b_m_upto_num_generators(mm, qi);
    let k = assoc.len();
    assert(k == 3);
    let a_words = Seq::new(k, |idx: int| assoc[idx].0);
    let b_words = Seq::new(k, |idx: int| assoc[idx].1);
    assert(a_words =~= seq![config_word(q.a, q.b), symbol_power(Symbol::Gen(1), m),
        symbol_power(Symbol::Gen(2), m)]);
    assert forall|ww: Word| word_valid(ww, k as nat) implies (
        equiv_in_presentation(base, apply_embedding(a_words, ww), empty_word())
        <==> equiv_in_presentation(base, apply_embedding(b_words, ww), empty_word())
    ) by {
        assert(m >= 1);
        assert(m * m >= 1) by (nonlinear_arith) requires m >= 1;
        lemma_quad_associations_valid(q, m, 3);
        lemma_apply_embedding_valid(a_words, ww, 3);
        lemma_apply_embedding_valid(b_words, ww, 3);
        let ea = apply_embedding(a_words, ww);
        let eb = apply_embedding(b_words, ww);
        lemma_conj_scaling_trivial_iff(q.a, q.b, m, m, ww);
        assert(apply_embedding(seq![config_word(q.a, q.b), symbol_power(Symbol::Gen(1), m),
            symbol_power(Symbol::Gen(2), m)], ww) =~= ea);
        if equiv_in_presentation(base, ea, empty_word()) {
            lemma_b_m_upto_faithful(mm, qi, ea);
        }
        if equiv_in_presentation(base_A(), ea, empty_word()) {
            lemma_lift_bm_level(mm, 0, qi, ea, empty_word());
        }
        match q.dir {
            Dir::R => {
                assert(b_words =~= seq![config_word(q.c, 0), symbol_power(Symbol::Gen(1), m * m),
                    symbol_power(Symbol::Gen(2), 1)]);
                lemma_conj_scaling_trivial_iff(q.c, 0, m * m, 1, ww);
                assert(apply_embedding(seq![config_word(q.c, 0), symbol_power(Symbol::Gen(1), m * m),
                    symbol_power(Symbol::Gen(2), 1)], ww) =~= eb);
            }
            Dir::L => {
                assert(b_words =~= seq![config_word(0, q.c), symbol_power(Symbol::Gen(1), 1),
                    symbol_power(Symbol::Gen(2), m * m)]);
                lemma_conj_scaling_trivial_iff(0, q.c, 1, m * m, ww);
                assert(apply_embedding(seq![config_word(0, q.c), symbol_power(Symbol::Gen(1), 1),
                    symbol_power(Symbol::Gen(2), m * m)], ww) =~= eb);
            }
        }
        if equiv_in_presentation(base, eb, empty_word()) {
            lemma_b_m_upto_faithful(mm, qi, eb);
        }
        if equiv_in_presentation(base_A(), eb, empty_word()) {
            lemma_lift_bm_level(mm, 0, qi, eb, empty_word());
        }
    }
}

//  ψ multiplies the y-stable-count by q.
pub proof fn lemma_psi_A_stable_count_scales(p: nat, q: nat, w: Word)
    requires
        word_valid(w, 3),
    ensures
        stable_count(a_as_hnn(), apply_embedding(psi_images(p, q), w))
            == q * stable_count(a_as_hnn(), w),
    decreases w.len(),
{
    let data = a_as_hnn();
    let imgs = psi_images(p, q);
    if w.len() == 0 {
        assert(apply_embedding(imgs, w) =~= Seq::<Symbol>::empty());
    } else {
        let last = w.last();
        let pre = w.drop_last();
        assert(w =~= pre + seq![last]);
        assert(word_valid(pre, 3)) by {
            assert forall|k: int| 0 <= k < pre.len() implies symbol_valid(#[trigger] pre[k], 3)
            by { assert(pre[k] == w[k]); }
        }
        assert(symbol_valid(last, 3));
        lemma_apply_embedding_concat(imgs, pre, seq![last]);
        assert(apply_embedding(imgs, w)
            =~= apply_embedding(imgs, pre) + apply_embedding(imgs, seq![last]));
        lemma_stable_count_concat(data,
            apply_embedding(imgs, pre), apply_embedding(imgs, seq![last]));
        lemma_psi_A_emb_symbol_stable_count(p, q, last);
        lemma_psi_A_stable_count_scales(p, q, pre);
        let inc: nat = if is_stable(data, last) { 1nat } else { 0nat };
        assert(stable_count(data, w) == stable_count(data, pre) + inc) by {
            reveal_with_fuel(stable_count, 2);
        }
        assert(stable_count(data, apply_embedding(imgs, seq![last])) == q * inc) by {
            if is_stable(data, last) { } else { }
        }
        assert(q * (stable_count(data, pre) + inc)
            == q * stable_count(data, pre) + q * inc) by (nonlinear_arith);
        assert(stable_count(data, apply_embedding(imgs, w))
            == q * stable_count(data, pre) + q * inc);
        assert(stable_count(data, apply_embedding(imgs, w)) == q * stable_count(data, w));
    }
}

} //  verus!
