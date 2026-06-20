// Layer 2 — Brick 2 (`h1.rs`): the H₁-level generators / relators of the Higman tower.
//
// Under the Approach-(b) decision (docs/layer2-build-plan.md, 2026-06-20): all literal
// `Presentation`s stay FINITE. This module defines the finite, unambiguous H₁ pieces — the
// `word_numbering` maps instantiated at the global layout (`layout.rs`), and the `n²` commutator
// relators `b_i c_j = c_j b_i` (a member of the final finite relation set (I)). The recursively
// presented `C = ⟨c;S⟩` is carried by a `spec_fn(Word)->bool` predicate (NOT relators here), and
// the deep embedding-faithfulness goes through `benign.rs` + the `kp_pinch` engine (brick 5).
//
// Self-contained on `word_numbering` + `layout` (both pure-arithmetic / abstract over `nk` = the
// K_M generator count). The concrete `nk = g_m(mm).num_generators` is plugged in when this is
// composed with K_M.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::machine_group::*;
use crate::word_numbering::*;
use crate::layout::*;

verus! {

// ----------------------------------------------------------------------------
// The word-numbering maps at the global layout bases
// ----------------------------------------------------------------------------

/// `w_α(c)` placed at the c-block (`c_base(nk) = nk`).
pub open spec fn h_w_c(nk: nat, n: nat, m: nat, alpha: nat) -> Word {
    w_c(c_base(nk), n, m, alpha)
}

/// `w_α(b)` placed at the b-block (`b_base(nk, n) = nk + n`).
pub open spec fn h_w_b(nk: nat, n: nat, m: nat, alpha: nat) -> Word {
    w_b(b_base(nk, n), n, m, alpha)
}

/// `w_α(bc)` placed at the b/c-blocks.
pub open spec fn h_w_bc(nk: nat, n: nat, m: nat, alpha: nat) -> Word {
    w_bc(b_base(nk, n), c_base(nk), n, m, alpha)
}

/// `h_w_c` is valid whenever `α` numbers a word and `ng` covers the c-block.
pub proof fn lemma_h_w_c_valid(nk: nat, n: nat, m: nat, alpha: nat, ng: nat)
    requires numbers_word(n, m, alpha), c_base(nk) + n <= ng, 2 * n < m,
    ensures word_valid(h_w_c(nk, n, m, alpha), ng),
{
    lemma_w_c_valid(c_base(nk), n, m, alpha, ng);
}

/// `h_w_b` is valid whenever `α` numbers a word and `ng` covers the b-block (`w_b := w_c` shifted).
pub proof fn lemma_h_w_b_valid(nk: nat, n: nat, m: nat, alpha: nat, ng: nat)
    requires numbers_word(n, m, alpha), b_base(nk, n) + n <= ng, 2 * n < m,
    ensures word_valid(h_w_b(nk, n, m, alpha), ng),
{
    lemma_w_c_valid(b_base(nk, n), n, m, alpha, ng);
}

// ----------------------------------------------------------------------------
// The commutator relators  b_i c_j = c_j b_i   (relator: b_i c_j b_i⁻¹ c_j⁻¹)
// ----------------------------------------------------------------------------

/// The relator word witnessing `b_i c_j = c_j b_i`, i.e. `b_i c_j b_i⁻¹ c_j⁻¹` (1 ≤ i,j ≤ n).
pub open spec fn comm_relator(nk: nat, n: nat, i: nat, j: nat) -> Word {
    seq![
        Symbol::Gen(b_idx(nk, n, i)),
        Symbol::Gen(c_idx(nk, j)),
        Symbol::Inv(b_idx(nk, n, i)),
        Symbol::Inv(c_idx(nk, j)),
    ]
}

/// Each commutator uses only c-block / b-block generators, hence is valid for any
/// `ng ≥ nk + 2n` (= `b_base + n`, the end of the b-block).
pub proof fn lemma_comm_relator_valid(nk: nat, n: nat, i: nat, j: nat, ng: nat)
    requires 1 <= i <= n, 1 <= j <= n, nk + 2 * n <= ng,
    ensures word_valid(comm_relator(nk, n, i, j), ng),
{
    let bi = b_idx(nk, n, i);
    let cj = c_idx(nk, j);
    // bi = nk + n + (i-1) ≤ nk + 2n - 1 < ng ;  cj = nk + (j-1) ≤ nk + n - 1 < ng.
    assert(bi < ng);
    assert(cj < ng);
    let w = comm_relator(nk, n, i, j);
    assert(w.len() == 4);
    assert(w[0] == Symbol::Gen(bi));
    assert(w[1] == Symbol::Gen(cj));
    assert(w[2] == Symbol::Inv(bi));
    assert(w[3] == Symbol::Inv(cj));
    assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], ng) by {
        if k == 0 {
        } else if k == 1 {
        } else if k == 2 {
        } else {
        }
    }
}

// ----------------------------------------------------------------------------
// The full commutator family + the H₁-literal base presentation (Approach (b))
// ----------------------------------------------------------------------------

/// All `n²` commutator relators `b_i c_j = c_j b_i` (1 ≤ i,j ≤ n), flattened
/// row-major: index `idx` ↦ `(i,j)` with `i = idx/n + 1`, `j = idx%n + 1`.
pub open spec fn comm_relators(nk: nat, n: nat) -> Seq<Word> {
    Seq::new((n * n) as nat,
        |idx: int| comm_relator(nk, n, (idx / (n as int) + 1) as nat, (idx % (n as int) + 1) as nat))
}

/// Every commutator relator is valid for any `ng ≥ nk + 2n`.
pub proof fn lemma_comm_relators_valid(nk: nat, n: nat, ng: nat)
    requires nk + 2 * n <= ng,
    ensures forall|idx: int| 0 <= idx < comm_relators(nk, n).len()
        ==> word_valid(#[trigger] comm_relators(nk, n)[idx], ng),
{
    assert forall|idx: int| 0 <= idx < comm_relators(nk, n).len()
        implies word_valid(#[trigger] comm_relators(nk, n)[idx], ng) by {
        // 0 ≤ idx < n·n forces n ≥ 1, then idx/n ∈ [0,n) and idx%n ∈ [0,n).
        assert(n > 0) by { if n == 0 { assert(n * n == 0); } }
        vstd::arithmetic::div_mod::lemma_multiply_divide_lt(idx, n as int, n as int);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(idx, n as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(idx, n as int);
        let i = (idx / (n as int) + 1) as nat;
        let j = (idx % (n as int) + 1) as nat;
        assert(1 <= i <= n);
        assert(1 <= j <= n);
        assert(comm_relators(nk, n)[idx] == comm_relator(nk, n, i, j));
        lemma_comm_relator_valid(nk, n, i, j, ng);
    }
}

/// The H₁-literal base presentation under Approach (b): the K_M presentation
/// `g_m(mm)` (at offset 0; its generator indices are unchanged) together with
/// the free c/b/d generators and the `n²` commutators of set (I). Crucially it
/// does NOT carry `C`'s relator set `S` — `S` (= relation family (III)) holds in
/// `H₃` only as a DERIVED consequence of the finite set (I).
pub open spec fn h1_base(mm: ModMachine, n: nat) -> Presentation {
    Presentation {
        num_generators: h1_num_gens(g_m(mm).num_generators, n),
        relators: g_m(mm).relators + comm_relators(g_m(mm).num_generators, n),
    }
}

/// `h1_base` has `h1_num_gens(4+|quads|, n)` generators.
pub proof fn lemma_h1_base_num_generators(mm: ModMachine, n: nat)
    ensures h1_base(mm, n).num_generators == h1_num_gens((4 + mm.quads.len()) as nat, n),
{
    lemma_g_m_num_generators(mm);
}

/// `h1_base` is a valid presentation: every K_M relator is valid (monotone lift
/// from `g_m`'s `nk` generators) and every commutator is valid over `nk + 2n`.
pub proof fn lemma_h1_base_valid(mm: ModMachine, n: nat)
    ensures presentation_valid(h1_base(mm, n)),
{
    reveal(presentation_valid);
    let nk = g_m(mm).num_generators;
    let ng = h1_num_gens(nk, n);
    let p = h1_base(mm, n);
    let grels = g_m(mm).relators;
    let crels = comm_relators(nk, n);

    lemma_g_m_valid(mm);                 // presentation_valid(g_m(mm))
    lemma_comm_relators_valid(nk, n, ng); // nk + 2n ≤ ng = nk + 2n + 1

    assert(p.relators =~= grels + crels);
    assert forall|i: int| 0 <= i < p.relators.len()
        implies word_valid(#[trigger] p.relators[i], ng) by {
        if i < grels.len() {
            assert(p.relators[i] == grels[i]);
            // K_M relator: valid over nk, lift monotonically to ng = nk + 2n + 1.
            assert(word_valid(grels[i], nk));
            lemma_word_valid_mono(grels[i], nk, ng);
        } else {
            assert(p.relators[i] == crels[i - grels.len()]);
        }
    }
}

} // verus!
