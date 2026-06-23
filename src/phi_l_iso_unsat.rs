// Layer 2 — Brick 5, C3.2: MACHINE-CHECKED RECORD of the σ-saturation obstruction.
//
// `sigma_sat_upto` (the per-level side condition of the a-tower isos `lemma_phi_l_iso` /
// `lemma_h3_II_upto_faithful` in `phi_l_iso_tower.rs`) is UNSATISFIABLE for every finite `alphas`.
// A finite `Seq<nat>` cannot be closed under the strictly-increasing map `x ↦ m·x + 1`.  This file
// proves that fact, so the vacuity of those isos is undeniable and machine-checked.  See the
// `sigma_sat_upto` doc-comment and `docs/brick5-c4-plan.md` §7 for the architectural consequence
// (C3.2 must be reframed to a WORD-RESTRICTED virtual iso; the R1–R4 directional machinery is reused).
//
// This lives in its own module so its quantifier helper does not pollute the trigger selection of the
// (delicate) isos in `phi_l_iso_tower.rs` (CLAUDE.md: "Helper Functions Pollute Module Triggers").

use vstd::prelude::*;
use crate::phi_l_iso_tower::sigma_sat_upto;
use crate::r_prime::sigma_backsat;
use crate::f_free_a1::{betas, lemma_betas_index};

verus! {

/// A non-empty `Seq<nat>` has a maximum element (at some index `i`).
proof fn lemma_seq_nat_has_max(s: Seq<nat>) -> (i: int)
    requires
        s.len() > 0,
    ensures
        0 <= i < s.len(),
        forall|j: int| 0 <= j < s.len() ==> s[j] <= s[i],
    decreases s.len(),
{
    if s.len() == 1 {
        0int
    } else {
        let pre = s.drop_last();
        let i2 = lemma_seq_nat_has_max(pre);
        assert(forall|j: int| 0 <= j < pre.len() ==> pre[j] == s[j]);
        if s[s.len() - 1] >= s[i2] {
            (s.len() - 1) as int
        } else {
            i2
        }
    }
}

/// **MACHINE-CHECKED RECORD of the C3.2 obstruction:** `sigma_sat_upto(alphas, m, l)` is UNSATISFIABLE
/// for every (finite) `alphas` when `l ≥ 1`, `m ≥ 1`.  A finite `Seq<nat>` cannot be closed under the
/// strictly-increasing map `x ↦ m·x + 1`: the finite-slice at `j = 1` forces `1 ∈ alphas` (from
/// `betas[0] = 0`), and then forces `m·M + 1 ∈ alphas` for `M = max(alphas)`, but `m·M + 1 > M` — a
/// contradiction.  Consequently `lemma_phi_l_iso` / `lemma_h3_II_upto_faithful` (which take
/// `sigma_sat_upto` as a hypothesis) are VACUOUSLY verified and CANNOT be instantiated.  This lemma is
/// never called — it exists to make the vacuity undeniable, so no future session re-declares C3.2
/// "done".  (In context the side conditions `2n < m` and `l ≥ 1` give `m ≥ 1`.)
pub proof fn lemma_sigma_sat_upto_unsatisfiable(alphas: Seq<nat>, m: nat, l: nat)
    requires
        l >= 1,
        m >= 1,
        sigma_sat_upto(alphas, m, l),
    ensures
        false,
{
    let bet = betas(alphas);
    lemma_betas_index(alphas);
    // instantiate the bundle at j = 1 (1 ≤ 1 ≤ l).
    assert(sigma_backsat(bet, m, 1) && (forall|jj: int| 0 <= jj < bet.len() ==>
        exists|kk: int| 0 <= kk < alphas.len() && alphas[kk] == m * (#[trigger] bet[jj]) + 1));
    // γ = betas[0] = 0  ⟹  m·0 + 1 = 1 ∈ alphas  ⟹  alphas non-empty.
    assert(bet[0] == 0);
    assert(exists|kk: int| 0 <= kk < alphas.len() && alphas[kk] == m * bet[0] + 1);
    let k0 = choose|kk: int| 0 <= kk < alphas.len() && alphas[kk] == m * bet[0] + 1;
    assert(0 <= k0 < alphas.len());
    assert(alphas.len() > 0);
    // M = max(alphas), at index iM.
    let iM = lemma_seq_nat_has_max(alphas);
    let big_m = alphas[iM];
    assert(forall|j: int| 0 <= j < alphas.len() ==> alphas[j] <= big_m);
    // M ∈ betas: betas[iM + 1] == alphas[iM] == M.
    assert(bet[iM + 1] == alphas[iM]);
    assert(0 <= iM + 1 < bet.len());
    // finite-slice at γ = betas[iM+1] = M  ⟹  m·M + 1 ∈ alphas.
    assert(exists|kk: int| 0 <= kk < alphas.len() && alphas[kk] == m * bet[iM + 1] + 1);
    let k1 = choose|kk: int| 0 <= kk < alphas.len() && alphas[kk] == m * bet[iM + 1] + 1;
    assert(0 <= k1 < alphas.len() && alphas[k1] == m * big_m + 1);
    // but m·M + 1 > M = max  ⟹  contradiction.
    assert(m * big_m >= big_m) by (nonlinear_arith)
        requires m >= 1;
    assert(alphas[k1] == m * big_m + 1 > big_m);
    assert(alphas[k1] <= big_m);     // from max
    assert(false);
}

} // verus!
