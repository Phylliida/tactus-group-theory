// Layer 2 — the global generator layout table for the Higman tower H₁ ⊆ H₂ ⊆ H₃.
//
// One fixed index convention, reused across bricks 2–5 (`h1.rs`/`h2.rs`/`h3.rs`/
// `higman_consequences.rs`) so no brick hard-codes a magic offset. Pure arithmetic,
// self-contained (NO machine_group / hnn dependency): parameterized by
//   * `nk` — the number of K_M = G(M) generators (caller passes `g_m(mm).num_generators`,
//            which Layer 1 proves equals `4 + |mm.quads|`).
//   * `n`  — the number of c-generators (= number of b-generators).
//
// The factors are laid out left→right as  K_M , (C × ⟨b⟩) , ⟨d⟩ , p , a-block , k
// so that `free_product`'s offset rule (`free_product(p1,p2)` puts p2 at indices
// `≥ p1.num_generators`) and `hnn`'s stable letter (`Gen(base.num_generators)`) place
// every block exactly at the base index below.
//
//   block        symbols          base index           count   end (excl)
//   K_M          t,x,y,(r/l)…,k'  0                    nk      nk
//   c            c₁…cₙ            c_base = nk          n       nk+n
//   b            b₁…bₙ            b_base = nk+n        n       nk+2n
//   d            d                d_idx  = nk+2n       1       nk+2n+1     (= H₁ count)
//   p (H₂ stbl)  p                p_idx  = nk+2n+1     1       nk+2n+2     (= H₂ count)
//   a (H₃ stbl)  a₁…a₂ₙ           a_base = nk+2n+2     2n      nk+4n+2
//   k (H₃ top)   k                k_top  = nk+4n+2     1       nk+4n+3     (= H₃ count)
//
// NAMING-CLASH GUARD: K_M's own commutator witness `k'` (= machine_group `k_gen`, index
// `nk-1 = 3+|quads|`) is DISTINCT from Layer-2's top stable letter `k` (index `k_top`).

use vstd::prelude::*;

verus! {

// ----------------------------------------------------------------------------
// Block base indices
// ----------------------------------------------------------------------------

/// Index of c₁ (the c-block is `c_base .. c_base + n`).
pub open spec fn c_base(nk: nat) -> nat { nk }

/// Index of b₁ (the b-block is `b_base .. b_base + n`).
pub open spec fn b_base(nk: nat, n: nat) -> nat { nk + n }

/// Index of `d`.
pub open spec fn d_idx(nk: nat, n: nat) -> nat { nk + 2 * n }

/// Index of the H₂ stable letter `p`.
pub open spec fn p_idx(nk: nat, n: nat) -> nat { nk + 2 * n + 1 }

/// Index of a₁ (the a-block is `a_base .. a_base + 2n`, one per alphabet digit 1..=2n).
pub open spec fn a_base(nk: nat, n: nat) -> nat { nk + 2 * n + 2 }

/// Index of the H₃ top stable letter `k`.
pub open spec fn k_top(nk: nat, n: nat) -> nat { nk + 4 * n + 2 }

// ----------------------------------------------------------------------------
// Per-index helpers for the c / b / a blocks (1-based digit/letter j)
// ----------------------------------------------------------------------------

/// Index of `c_j`, 1 ≤ j ≤ n.
pub open spec fn c_idx(nk: nat, j: nat) -> nat { c_base(nk) + (j - 1) as nat }

/// Index of `b_j`, 1 ≤ j ≤ n.
pub open spec fn b_idx(nk: nat, n: nat, j: nat) -> nat { b_base(nk, n) + (j - 1) as nat }

/// Index of `a_i`, 1 ≤ i ≤ 2n.
pub open spec fn a_idx(nk: nat, n: nat, i: nat) -> nat { a_base(nk, n) + (i - 1) as nat }

// ----------------------------------------------------------------------------
// Generator counts at each tower level
// ----------------------------------------------------------------------------

/// Generators of H₁ = K_M ∗ (C × ⟨b⟩) ∗ ⟨d⟩.
pub open spec fn h1_num_gens(nk: nat, n: nat) -> nat { nk + 2 * n + 1 }

/// Generators of H₂ = HNN(H₁, p).
pub open spec fn h2_num_gens(nk: nat, n: nat) -> nat { nk + 2 * n + 2 }

/// Generators of H₃ = HNN(H₂; a₁…a₂ₙ, k).
pub open spec fn h3_num_gens(nk: nat, n: nat) -> nat { nk + 4 * n + 3 }

// ----------------------------------------------------------------------------
// Consistency: blocks partition 0..h3_num_gens, strictly ordered (n ≥ 1)
// ----------------------------------------------------------------------------

/// The block bases are strictly increasing and the counts tile `0 .. h3_num_gens`
/// exactly. Confirms the table is internally consistent (no overlap, no gap).
pub proof fn lemma_layout_consistent(nk: nat, n: nat)
    requires 1 <= n,
    ensures
        // strict left-to-right ordering of the block bases
        c_base(nk) < b_base(nk, n),
        b_base(nk, n) < d_idx(nk, n),
        d_idx(nk, n) < p_idx(nk, n),
        p_idx(nk, n) < a_base(nk, n),
        a_base(nk, n) < k_top(nk, n),
        k_top(nk, n) < h3_num_gens(nk, n),
        // each block's end meets the next block's base (tiling, no gaps)
        c_base(nk) + n == b_base(nk, n),
        b_base(nk, n) + n == d_idx(nk, n),
        d_idx(nk, n) + 1 == p_idx(nk, n),
        p_idx(nk, n) + 1 == a_base(nk, n),
        a_base(nk, n) + 2 * n == k_top(nk, n),
        k_top(nk, n) + 1 == h3_num_gens(nk, n),
        // level counts agree with the running ends
        h1_num_gens(nk, n) == d_idx(nk, n) + 1,
        h2_num_gens(nk, n) == p_idx(nk, n) + 1,
{
}

} // verus!
