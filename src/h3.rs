// Layer 2 — Brick 4 (`h3.rs`): the top of the Higman tower.
//
// `H₃ = ⟨ H₂, a_i (1≤i≤2n), k ∣ a_i: A↔A_i, k: A₊↔A₋ ⟩` — the finitely presented
// group. The `a_i` and `k` HNN associations are the last members of finite set (I).
//
// Under Approach (b) we realize `H₃` as an ITERATED single-letter HNN tower over
// `h2_pres` (h2.rs): add `a_1,…,a_{2n}` one at a time, then `k`. The global layout
// (layout.rs) was designed so each new stable letter lands exactly at its slot:
// `a_l` at `a_idx(nk,n,l)`, `k` at `k_top(nk,n)`. All associated subgroups
// (`A, A_i, A₊, A₋`) live inside `H₂`, so the iteration equals Cohen's
// multi-stable-letter HNN (cross-checked with the local model, 2026-06-20).
//
// Generator conventions (from the layout, K_M at offset 0 so its indices are
// unchanged): `t=Gen(0)`, `x=Gen(1)`, `d=Gen(d_idx)`, `p=Gen(p_idx)`, `b_j` (literal
// generator) `=Gen(b_idx(j))`, `c_j=Gen(c_idx(j))`, `U=g_subgens(mm)` (each a single
// K_M generator). The image `t_i = config_word(i,0)`, `xᵐ = symbol_power(Gen(1),m)`,
// and in `b_i d` the `b_i` uses the 2n-letter alphabet (`alphabet_letter(b_base,n,i)`,
// i.e. `b_{n+i}=b_i⁻¹`) — distinct from the literal `b_j↦b_j` block (1≤j≤n).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::hnn::*;
use crate::machine_group::*;
use crate::word_numbering::*;
use crate::layout::*;
use crate::h2::*;

verus! {

// ----------------------------------------------------------------------------
// Small word-validity helpers + the association-list validity predicate
// ----------------------------------------------------------------------------

/// A single-generator word `[Gen(g)]` is valid when `g < ng`.
pub proof fn lemma_single_gen_valid(g: nat, ng: nat)
    requires g < ng,
    ensures word_valid(seq![Symbol::Gen(g)], ng),
{
    let w: Word = seq![Symbol::Gen(g)];
    assert forall|j: int| 0 <= j < w.len() implies symbol_valid(#[trigger] w[j], ng) by {
        assert(w[0] == Symbol::Gen(g));
    }
}

/// A two-symbol word `[s0, s1]` is valid when both symbols are.
pub proof fn lemma_pair_word_valid(s0: Symbol, s1: Symbol, ng: nat)
    requires symbol_valid(s0, ng), symbol_valid(s1, ng),
    ensures word_valid(seq![s0, s1], ng),
{
    let w: Word = seq![s0, s1];
    assert forall|j: int| 0 <= j < w.len() implies symbol_valid(#[trigger] w[j], ng) by {
        if j == 0 { assert(w[0] == s0); } else { assert(w[1] == s1); }
    }
}

/// Every association pair in `assocs` has both words valid over `ng`.
pub open spec fn assocs_valid(assocs: Seq<(Word, Word)>, ng: nat) -> bool {
    forall|i: int| #![trigger assocs[i]] 0 <= i < assocs.len() ==>
        word_valid(assocs[i].0, ng) && word_valid(assocs[i].1, ng)
}

/// `assocs_valid` is closed under list concatenation.
pub proof fn lemma_assocs_valid_concat(a: Seq<(Word, Word)>, b: Seq<(Word, Word)>, ng: nat)
    requires assocs_valid(a, ng), assocs_valid(b, ng),
    ensures assocs_valid(a + b, ng),
{
    assert forall|i: int| #![trigger (a + b)[i]] 0 <= i < (a + b).len() implies
        word_valid((a + b)[i].0, ng) && word_valid((a + b)[i].1, ng) by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// `assocs_valid(assocs, ng)` discharges the association half of `hnn_data_valid`
/// for an HNN datum whose base has exactly `ng` generators.
pub proof fn lemma_hnn_data_valid_from(data: HNNData, ng: nat)
    requires
        presentation_valid(data.base),
        data.base.num_generators == ng,
        assocs_valid(data.associations, ng),
    ensures hnn_data_valid(data),
{
    assert forall|i: int| #![trigger data.associations[i]] 0 <= i < data.associations.len() implies
        word_valid(data.associations[i].0, data.base.num_generators)
        && word_valid(data.associations[i].1, data.base.num_generators) by {
        assert(data.associations[i] == data.associations[i]);  // fire assocs_valid trigger
    }
}

// ----------------------------------------------------------------------------
// φ_i : A → A_i   (one per stable letter a_i, 1 ≤ i ≤ 2n)
//   t ↦ t_i = config(i,0),  x ↦ xᵐ,  d ↦ b_i d,  b_j ↦ b_j (1≤j≤n),  p ↦ p
// ----------------------------------------------------------------------------

/// The `n` identity associations `b_j ↦ b_j` (literal generators, 1 ≤ j ≤ n).
pub open spec fn phi_bblock(nk: nat, n: nat) -> Seq<(Word, Word)> {
    Seq::new(n, |j: int| {
        let bj = Symbol::Gen(b_idx(nk, n, (j + 1) as nat));
        (seq![bj], seq![bj])
    })
}

/// The association list of `φ_i` (stated-gen ↦ image), `a_i`'s HNN relations.
pub open spec fn phi_assoc(nk: nat, n: nat, m: nat, i: nat) -> Seq<(Word, Word)> {
    seq![
        (seq![Symbol::Gen(0)], config_word(i, 0)),                          // t ↦ t_i
        (seq![Symbol::Gen(1)], symbol_power(Symbol::Gen(1), m)),            // x ↦ xᵐ
        (seq![Symbol::Gen(d_idx(nk, n))],
            seq![alphabet_letter(b_base(nk, n), n, i), Symbol::Gen(d_idx(nk, n))]),  // d ↦ b_i d
    ]
    + phi_bblock(nk, n)
    + seq![ (seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))]) ]      // p ↦ p
}

/// The `b_j ↦ b_j` block is valid (every literal `b_j` index < ng).
pub proof fn lemma_phi_bblock_valid(nk: nat, n: nat, ng: nat)
    requires nk + 2 * n + 2 <= ng,
    ensures assocs_valid(phi_bblock(nk, n), ng),
{
    assert forall|j: int| #![trigger phi_bblock(nk, n)[j]] 0 <= j < phi_bblock(nk, n).len() implies
        word_valid(phi_bblock(nk, n)[j].0, ng) && word_valid(phi_bblock(nk, n)[j].1, ng) by {
        let bj = Symbol::Gen(b_idx(nk, n, (j + 1) as nat));
        assert(phi_bblock(nk, n)[j] == (seq![bj], seq![bj]));
        // b_idx(nk,n,j+1) = nk + n + j ≤ nk + 2n - 1 < ng  (since 0 ≤ j < n).
        assert(b_idx(nk, n, (j + 1) as nat) == nk + n + j);
        lemma_single_gen_valid(b_idx(nk, n, (j + 1) as nat), ng);
    }
}

/// Every association word of `φ_i` is valid over `ng ≥ nk + 2n + 2`.
pub proof fn lemma_phi_assoc_valid(nk: nat, n: nat, m: nat, i: nat, ng: nat)
    requires 1 <= i <= 2 * n, nk + 2 * n + 2 <= ng,
    ensures assocs_valid(phi_assoc(nk, n, m, i), ng),
{
    // 1 ≤ i ≤ 2n forces n ≥ 1, hence ng ≥ nk + 4 ≥ 4.
    let d = d_idx(nk, n);
    let p = p_idx(nk, n);
    let bbase = b_base(nk, n);

    // --- the fixed 3-pair head:  t↦t_i, x↦xᵐ, d↦b_i d ---
    let head: Seq<(Word, Word)> = seq![
        (seq![Symbol::Gen(0)], config_word(i, 0)),
        (seq![Symbol::Gen(1)], symbol_power(Symbol::Gen(1), m)),
        (seq![Symbol::Gen(d)], seq![alphabet_letter(bbase, n, i), Symbol::Gen(d)]),
    ];
    // word validities used by the head:
    lemma_config_word_valid(i, 0);
    lemma_word_valid_mono(config_word(i, 0), 3, ng);                 // 3 ≤ ng
    lemma_single_gen_valid(0, ng);
    lemma_single_gen_valid(1, ng);
    lemma_symbol_power_valid(Symbol::Gen(1), m, ng);                 // 1 < ng
    lemma_single_gen_valid(d, ng);                                  // d_idx = nk+2n < ng
    lemma_alphabet_letter_valid(bbase, n, i, ng);                   // b_base+n = nk+2n ≤ ng
    lemma_pair_word_valid(alphabet_letter(bbase, n, i), Symbol::Gen(d), ng);
    assert(assocs_valid(head, ng)) by {
        assert forall|j: int| #![trigger head[j]] 0 <= j < head.len() implies
            word_valid(head[j].0, ng) && word_valid(head[j].1, ng) by {
            if j == 0 {
                assert(head[0] == (seq![Symbol::Gen(0)], config_word(i, 0)));
            } else if j == 1 {
                assert(head[1] == (seq![Symbol::Gen(1)], symbol_power(Symbol::Gen(1), m)));
            } else {
                assert(head[2] == (seq![Symbol::Gen(d)], seq![alphabet_letter(bbase, n, i), Symbol::Gen(d)]));
            }
        }
    }

    // --- the b_j↦b_j block ---
    lemma_phi_bblock_valid(nk, n, ng);

    // --- the p↦p tail ---
    let tail: Seq<(Word, Word)> = seq![ (seq![Symbol::Gen(p)], seq![Symbol::Gen(p)]) ];
    lemma_single_gen_valid(p, ng);                                  // p_idx = nk+2n+1 < ng
    assert(assocs_valid(tail, ng)) by {
        assert forall|j: int| #![trigger tail[j]] 0 <= j < tail.len() implies
            word_valid(tail[j].0, ng) && word_valid(tail[j].1, ng) by {
            assert(tail[0] == (seq![Symbol::Gen(p)], seq![Symbol::Gen(p)]));
        }
    }

    // --- compose:  head + phi_bblock + tail = phi_assoc ---
    lemma_assocs_valid_concat(head, phi_bblock(nk, n), ng);
    lemma_assocs_valid_concat(head + phi_bblock(nk, n), tail, ng);
    assert(phi_assoc(nk, n, m, i) =~= head + phi_bblock(nk, n) + tail);
}

// ----------------------------------------------------------------------------
// ψ : A₊ → A₋   (the single stable letter k)
//   u ↦ u (u ∈ U = g_subgens),  d ↦ d,  b_j ↦ b_j c_j (1≤j≤n),  p ↦ p
// ----------------------------------------------------------------------------

/// The `U ↦ U` identity block (`U = g_subgens(mm)`, each a single K_M generator).
pub open spec fn psi_ublock(mm: ModMachine) -> Seq<(Word, Word)> {
    Seq::new(g_subgens(mm).len(), |i: int| (g_subgens(mm)[i], g_subgens(mm)[i]))
}

/// The `b_j ↦ b_j c_j` block (1 ≤ j ≤ n).
pub open spec fn psi_bcblock(nk: nat, n: nat) -> Seq<(Word, Word)> {
    Seq::new(n, |j: int| {
        let bj = Symbol::Gen(b_idx(nk, n, (j + 1) as nat));
        let cj = Symbol::Gen(c_idx(nk, (j + 1) as nat));
        (seq![bj], seq![bj, cj])
    })
}

/// The association list of `ψ` (`k`'s HNN relations).
pub open spec fn psi_assoc(mm: ModMachine, n: nat) -> Seq<(Word, Word)> {
    let nk = g_m(mm).num_generators;
    psi_ublock(mm)
    + seq![ (seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))]) ]   // d ↦ d
    + psi_bcblock(nk, n)
    + seq![ (seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))]) ]   // p ↦ p
}

/// The `U↦U` block is valid: each `g_subgens` word is valid over `3+|quads| ≤ ng`.
pub proof fn lemma_psi_ublock_valid(mm: ModMachine, ng: nat)
    requires (3 + mm.quads.len()) as nat <= ng,
    ensures assocs_valid(psi_ublock(mm), ng),
{
    lemma_g_m_associations_valid(mm);
    assert forall|i: int| #![trigger psi_ublock(mm)[i]] 0 <= i < psi_ublock(mm).len() implies
        word_valid(psi_ublock(mm)[i].0, ng) && word_valid(psi_ublock(mm)[i].1, ng) by {
        assert(psi_ublock(mm)[i] == (g_subgens(mm)[i], g_subgens(mm)[i]));
        // g_subgens[i] = g_m_associations[i].1, valid over 3+|quads|; lift to ng.
        assert(g_subgens(mm)[i] == g_m_associations(mm)[i].1);
        lemma_word_valid_mono(g_subgens(mm)[i], (3 + mm.quads.len()) as nat, ng);
    }
}

/// The `b_j ↦ b_j c_j` block is valid (`b_idx`, `c_idx` < ng for 1≤j≤n).
pub proof fn lemma_psi_bcblock_valid(nk: nat, n: nat, ng: nat)
    requires nk + 2 * n + 2 <= ng,
    ensures assocs_valid(psi_bcblock(nk, n), ng),
{
    assert forall|j: int| #![trigger psi_bcblock(nk, n)[j]] 0 <= j < psi_bcblock(nk, n).len() implies
        word_valid(psi_bcblock(nk, n)[j].0, ng) && word_valid(psi_bcblock(nk, n)[j].1, ng) by {
        let bj = Symbol::Gen(b_idx(nk, n, (j + 1) as nat));
        let cj = Symbol::Gen(c_idx(nk, (j + 1) as nat));
        assert(psi_bcblock(nk, n)[j] == (seq![bj], seq![bj, cj]));
        // b_idx = nk+n+j < ng, c_idx = nk+j < ng  (0 ≤ j < n).
        assert(b_idx(nk, n, (j + 1) as nat) == nk + n + j);
        assert(c_idx(nk, (j + 1) as nat) == nk + j);
        lemma_single_gen_valid(b_idx(nk, n, (j + 1) as nat), ng);
        lemma_pair_word_valid(bj, cj, ng);
    }
}

/// Every association word of `ψ` is valid over `ng ≥ nk + 2n + 2` (nk = K_M gens).
pub proof fn lemma_psi_assoc_valid(mm: ModMachine, n: nat, ng: nat)
    requires (g_m(mm).num_generators + 2 * n + 2) as nat <= ng,
    ensures assocs_valid(psi_assoc(mm, n), ng),
{
    let nk = g_m(mm).num_generators;
    let d = d_idx(nk, n);
    let p = p_idx(nk, n);
    lemma_g_m_num_generators(mm);            // nk = 4 + |quads|, so 3+|quads| = nk-1 ≤ ng

    lemma_psi_ublock_valid(mm, ng);
    lemma_psi_bcblock_valid(nk, n, ng);

    let dpair: Seq<(Word, Word)> = seq![ (seq![Symbol::Gen(d)], seq![Symbol::Gen(d)]) ];
    let ppair: Seq<(Word, Word)> = seq![ (seq![Symbol::Gen(p)], seq![Symbol::Gen(p)]) ];
    lemma_single_gen_valid(d, ng);
    lemma_single_gen_valid(p, ng);
    assert(assocs_valid(dpair, ng)) by {
        assert forall|j: int| #![trigger dpair[j]] 0 <= j < dpair.len() implies
            word_valid(dpair[j].0, ng) && word_valid(dpair[j].1, ng) by {
            assert(dpair[0] == (seq![Symbol::Gen(d)], seq![Symbol::Gen(d)]));
        }
    }
    assert(assocs_valid(ppair, ng)) by {
        assert forall|j: int| #![trigger ppair[j]] 0 <= j < ppair.len() implies
            word_valid(ppair[j].0, ng) && word_valid(ppair[j].1, ng) by {
            assert(ppair[0] == (seq![Symbol::Gen(p)], seq![Symbol::Gen(p)]));
        }
    }

    // compose:  psi_ublock + dpair + psi_bcblock + ppair = psi_assoc
    lemma_assocs_valid_concat(psi_ublock(mm), dpair, ng);
    lemma_assocs_valid_concat(psi_ublock(mm) + dpair, psi_bcblock(nk, n), ng);
    lemma_assocs_valid_concat(psi_ublock(mm) + dpair + psi_bcblock(nk, n), ppair, ng);
    assert(psi_assoc(mm, n) =~= psi_ublock(mm) + dpair + psi_bcblock(nk, n) + ppair);
}

// ----------------------------------------------------------------------------
// The iterated single-letter HNN tower:  H₂ → +a_1 → … → +a_{2n} → +k = H₃
// ----------------------------------------------------------------------------

/// `H₂` with `a_1,…,a_l` added — `l` levels of single-letter HNN (0 ≤ l ≤ 2n).
/// Level `l` adds stable letter `a_l` carrying the `φ_l : A→A_l` associations.
pub open spec fn h3_upto(mm: ModMachine, n: nat, m: nat, l: nat) -> Presentation
    decreases l,
{
    if l == 0 {
        h2_pres(mm, n)
    } else {
        hnn_presentation(HNNData {
            base: h3_upto(mm, n, m, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        })
    }
}

/// `H₃ = HNN(h3_upto(2n); k ∣ k: A₊↔A₋)` — the finitely presented group: the
/// literal finite presentation of Cohen's set (I).
pub open spec fn h3_pres(mm: ModMachine, n: nat, m: nat) -> Presentation {
    hnn_presentation(HNNData {
        base: h3_upto(mm, n, m, (2 * n) as nat),
        associations: psi_assoc(mm, n),
    })
}

/// `h3_upto(l)` has `h2_num_gens + l` generators (one per added `a_i`).
pub proof fn lemma_h3_upto_num_generators(mm: ModMachine, n: nat, m: nat, l: nat)
    ensures h3_upto(mm, n, m, l).num_generators
        == h2_num_gens((4 + mm.quads.len()) as nat, n) + l,
    decreases l,
{
    if l == 0 {
        lemma_h2_num_generators(mm, n);
    } else {
        lemma_h3_upto_num_generators(mm, n, m, (l - 1) as nat);  // adds 1 per level
    }
}

/// `H₃` has `h3_num_gens(4+|quads|, n) = nk + 4n + 3` generators.
pub proof fn lemma_h3_num_generators(mm: ModMachine, n: nat, m: nat)
    ensures h3_pres(mm, n, m).num_generators == h3_num_gens((4 + mm.quads.len()) as nat, n),
{
    lemma_h3_upto_num_generators(mm, n, m, (2 * n) as nat);
}

/// The level-`l` stable letter is exactly the layout's `a_l = Gen(a_idx(nk,n,l))`.
pub proof fn lemma_h3_a_stable_letter(mm: ModMachine, n: nat, m: nat, l: nat)
    requires 1 <= l <= 2 * n,
    ensures stable_letter(HNNData {
            base: h3_upto(mm, n, m, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        }) == Symbol::Gen(a_idx((4 + mm.quads.len()) as nat, n, l)),
{
    lemma_h3_upto_num_generators(mm, n, m, (l - 1) as nat);
    lemma_g_m_num_generators(mm);
}

/// The top stable letter is exactly the layout's `k = Gen(k_top(nk,n))`.
pub proof fn lemma_h3_k_stable_letter(mm: ModMachine, n: nat, m: nat)
    ensures stable_letter(HNNData {
            base: h3_upto(mm, n, m, (2 * n) as nat),
            associations: psi_assoc(mm, n),
        }) == Symbol::Gen(k_top((4 + mm.quads.len()) as nat, n)),
{
    lemma_h3_upto_num_generators(mm, n, m, (2 * n) as nat);
    lemma_g_m_num_generators(mm);
}

/// `h3_upto(l)` is a valid presentation: each added `a_i` carries valid `φ_i`
/// associations over the (strictly larger) running generator set.
pub proof fn lemma_h3_upto_valid(mm: ModMachine, n: nat, m: nat, l: nat)
    requires l <= 2 * n,
    ensures presentation_valid(h3_upto(mm, n, m, l)),
    decreases l,
{
    if l == 0 {
        lemma_h2_pres_valid(mm, n);
    } else {
        let nk = g_m(mm).num_generators;
        let base = h3_upto(mm, n, m, (l - 1) as nat);
        let data = HNNData { base, associations: phi_assoc(nk, n, m, l) };
        lemma_h3_upto_valid(mm, n, m, (l - 1) as nat);            // presentation_valid(base)
        lemma_h3_upto_num_generators(mm, n, m, (l - 1) as nat);   // base.num = nk+2n+1+l
        lemma_g_m_num_generators(mm);                            // nk = 4+|quads|
        // ng := base.num_generators = nk + 2n + 1 + l ≥ nk + 2n + 2  (since l ≥ 1).
        lemma_phi_assoc_valid(nk, n, m, l, base.num_generators);
        lemma_hnn_data_valid_from(data, base.num_generators);
        lemma_hnn_presentation_valid(data);
    }
}

/// `H₃` is a valid presentation — the finite set (I) is well-formed.
pub proof fn lemma_h3_pres_valid(mm: ModMachine, n: nat, m: nat)
    ensures presentation_valid(h3_pres(mm, n, m)),
{
    let nk = g_m(mm).num_generators;
    let base = h3_upto(mm, n, m, (2 * n) as nat);
    let data = HNNData { base, associations: psi_assoc(mm, n) };
    lemma_h3_upto_valid(mm, n, m, (2 * n) as nat);               // presentation_valid(base)
    lemma_h3_upto_num_generators(mm, n, m, (2 * n) as nat);      // base.num = nk+4n+2
    lemma_g_m_num_generators(mm);
    // ng := base.num_generators = nk + 4n + 2 ≥ nk + 2n + 2.
    lemma_psi_assoc_valid(mm, n, base.num_generators);
    lemma_hnn_data_valid_from(data, base.num_generators);
    lemma_hnn_presentation_valid(data);
}

} // verus!
