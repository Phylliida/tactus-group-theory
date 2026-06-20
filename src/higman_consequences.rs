// Layer 2 — Brick 5 (`higman_consequences.rs`): the Higman payoff.
//
// The BRIDGE THEOREM (soundness direction this session):
//
//     (α,0) ∈ H₀(M)   ⟹   h3_pres(mm,n,m) ⊢ w_α(c) = 1.
//
// This is Cohen's "(II),(III) are consequences of the finite set (I)" (book p.281): the
// recursively-presented relations of `C = ⟨c;S⟩` hold in the FINITE presentation `h3_pres` as
// derived theorems. Combined with Layer 1 (`lemma_theorem1`) it realizes the c.e. set
// `S = { w_α(c) : (α,0)∈H₀(M) }` as the word problem of `H₃` among the c-generators.
//
// See `docs/brick5-plan.md` for the full decomposition and the (deferred) completeness routing.
//
// Sub-brick 0 (this file, first): the LIFTING HELPERS. Every relation we use lives at some tower
// level (`h2_pres`, `h3_upto(l)`); we lift it up to `h3_pres` via repeated `lemma_base_embeds_in_hnn`
// (an HNN base embeds in its extension — no validity / iso hypothesis needed).

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::*;
use crate::hnn::*;
use crate::machine_group::*;
use crate::layout::*;
use crate::h1::*;
use crate::h2::*;
use crate::h3::*;

verus! {

// ----------------------------------------------------------------------------
// Sub-brick 0 — lifting equivalences up the iterated HNN tower to h3_pres.
// ----------------------------------------------------------------------------

/// One rung: an equivalence in `h3_upto(l)` lifts to `h3_upto(l+1)` (the `a_{l+1}` HNN whose
/// base is exactly `h3_upto(l)`).
pub proof fn lemma_h3_upto_step_embeds(mm: ModMachine, n: nat, m: nat, l: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_upto(mm, n, m, (l + 1) as nat), w1, w2),
{
    let data = HNNData {
        base: h3_upto(mm, n, m, l),
        associations: phi_assoc(g_m(mm).num_generators, n, m, (l + 1) as nat),
    };
    // h3_upto(l+1) = hnn_presentation(data), and data.base = h3_upto(l).
    assert(h3_upto(mm, n, m, (l + 1) as nat) == hnn_presentation(data));
    lemma_base_embeds_in_hnn(data, w1, w2);
}

/// Climb from level `l` up to level `hi` (`l ≤ hi ≤ 2n`): equivalence is preserved up the tower.
pub proof fn lemma_h3_upto_climbs(mm: ModMachine, n: nat, m: nat, l: nat, hi: nat, w1: Word, w2: Word)
    requires
        l <= hi,
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_upto(mm, n, m, hi), w1, w2),
    decreases hi - l,
{
    if l == hi {
    } else {
        lemma_h3_upto_step_embeds(mm, n, m, l, w1, w2);
        lemma_h3_upto_climbs(mm, n, m, (l + 1) as nat, hi, w1, w2);
    }
}

/// Top rung: an equivalence in `h3_upto(2n)` lifts to `h3_pres` (the `k` HNN whose base is
/// `h3_upto(2n)`).
pub proof fn lemma_h3_upto_top_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h3_upto(mm, n, m, (2 * n) as nat), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    let data = HNNData {
        base: h3_upto(mm, n, m, (2 * n) as nat),
        associations: psi_assoc(mm, n),
    };
    assert(h3_pres(mm, n, m) == hnn_presentation(data));
    lemma_base_embeds_in_hnn(data, w1, w2);
}

/// **Lift from any tower level `l ≤ 2n` to `h3_pres`.**
pub proof fn lemma_h3_upto_in_h3(mm: ModMachine, n: nat, m: nat, l: nat, w1: Word, w2: Word)
    requires
        l <= 2 * n,
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    lemma_h3_upto_climbs(mm, n, m, l, (2 * n) as nat, w1, w2);
    lemma_h3_upto_top_in_h3(mm, n, m, w1, w2);
}

/// **Lift from `h2_pres` to `h3_pres`** (= the `l = 0` base of the tower).
pub proof fn lemma_h2_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h2_pres(mm, n), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    // h3_upto(0) == h2_pres.
    assert(h3_upto(mm, n, m, 0) == h2_pres(mm, n));
    lemma_h3_upto_in_h3(mm, n, m, 0, w1, w2);
}

/// **Lift from `h1_base` to `h3_pres`** (through the `p` HNN, then the tower). `h2_pres` is the
/// `p`-HNN over `h1_base`, so an `h1_base` equivalence first lifts to `h2_pres`.
pub proof fn lemma_h1_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h1_base(mm, n), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    // h2_pres = hnn_presentation(h2_data), h2_data.base = h1_base.
    let data = h2_data(mm, n);
    assert(h2_pres(mm, n) == hnn_presentation(data));
    assert(data.base == h1_base(mm, n));
    lemma_base_embeds_in_hnn(data, w1, w2);
    lemma_h2_in_h3(mm, n, m, w1, w2);
}

} // verus!
