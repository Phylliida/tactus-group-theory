// Layer 2 — Cohen §1 assembly, brick CS-3: the predicate H₃ tower scaffold.
//
// `docs/cohen-section1-assembly-plan.md` §1, §5. The finite-association top HNN
// `H₃ = HNN(H₂, a_i (1≤i≤2n), k)` over the predicate base `h2_pred` (CS-1), built —
// exactly like the finite `h3_upto`/`h3_pres` (`h3.rs`) — as a TOWER of single-letter
// predicate HNNs: `H₂ → +a_1 → … → +a_{2n} → +k`. The association word-lists
// `phi_assoc` (a_i) and `psi_assoc` (k) are S-independent stated-gen pairs, REUSED
// verbatim from `h3.rs`; only the base goes predicate.
//
// This brick is defs + validity + num-gens (the FA-4-style scaffold). The genuine
// work — `hnn_pred_associations_isomorphic` at each level (the a_i relabeling iso §1a,
// the k von-Dyck iso §1b) — is CS-4/CS-5; with those, `britton_lemma_unconditional`
// descends `w_α(c)=1` down this tower to `h2_pred`, then CS-2 lands it in `C`.
//
// Additive/reversible; no regression.

use vstd::prelude::*;
use crate::word::*;
use crate::pred_presentation::*;
use crate::pred_hnn::*;
use crate::machine_group::*;
use crate::layout::*;
use crate::h3::*;
use crate::cohen_h2::*;

verus! {

// ----------------------------------------------------------------------------
// The single-letter predicate HNN tower
// ----------------------------------------------------------------------------

/// `H₂` with `a_1,…,a_l` added — `l` levels of single-letter predicate HNN
/// (0 ≤ l ≤ 2n). Mirror of `h3_upto`, base `h2_pred`. Level `l` adds stable letter
/// `a_l` carrying the `φ_l : A→A_l` associations (`phi_assoc`).
pub open spec fn h3_pred_upto(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat,
) -> PredPresentation
    decreases l,
{
    if l == 0 {
        h2_pred(mm, n, m, is_S)
    } else {
        hnn_pred_presentation(PredHNNData {
            base: h3_pred_upto(mm, n, m, is_S, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        })
    }
}

/// The top HNN datum: `k : A₊↔A₋` over `h3_pred_upto(2n)`.
pub open spec fn h3_pred_data(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool,
) -> PredHNNData {
    PredHNNData {
        base: h3_pred_upto(mm, n, m, is_S, (2 * n) as nat),
        associations: psi_assoc(mm, n),
    }
}

/// `H₃ = HNN(h3_pred_upto(2n); k)` — the predicate-base Higman group; its base carries
/// the full family (II) + S, so (unlike the finite `h3_pres`) the a_i/k associations
/// are GENUINE isomorphisms (CS-4/CS-5).
pub open spec fn h3_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool,
) -> PredPresentation {
    hnn_pred_presentation(h3_pred_data(mm, n, m, is_S))
}

// ----------------------------------------------------------------------------
// Generator counts (one per added stable letter, atop `h2_num_gens`)
// ----------------------------------------------------------------------------

/// `h3_pred_upto(l)` has `h2_num_gens(nk,n) + l` generators (one per added `a_i`).
pub proof fn lemma_h3_pred_upto_num_generators(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat,
)
    ensures
        h3_pred_upto(mm, n, m, is_S, l).num_generators
            == h2_num_gens(g_m(mm).num_generators, n) + l,
    decreases l,
{
    if l == 0 {
    } else {
        lemma_h3_pred_upto_num_generators(mm, n, m, is_S, (l - 1) as nat);
    }
}

/// `H₃` has `h3_num_gens(nk,n) = nk + 4n + 3` generators.
pub proof fn lemma_h3_pred_num_generators(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    ensures
        h3_pred(mm, n, m, is_S).num_generators == h2_num_gens(g_m(mm).num_generators, n) + 2 * n + 1,
{
    lemma_h3_pred_upto_num_generators(mm, n, m, is_S, (2 * n) as nat);
}

// ----------------------------------------------------------------------------
// Validity (each added stable letter carries valid associations)
// ----------------------------------------------------------------------------

/// The single-letter HNN datum at level `l` (1 ≤ l ≤ 2n) is a valid predicate-HNN
/// datum: the base is valid and `phi_assoc(l)`'s words are valid over the base's
/// (strictly larger) generator set.
pub proof fn lemma_h3_pred_level_data_valid(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat,
)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        pred_presentation_valid(h3_pred_upto(mm, n, m, is_S, (l - 1) as nat)),  // from the caller's IH
    ensures
        hnn_pred_data_valid(PredHNNData {
            base: h3_pred_upto(mm, n, m, is_S, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        }),
{
    let nk = g_m(mm).num_generators;
    let base = h3_pred_upto(mm, n, m, is_S, (l - 1) as nat);
    let data = PredHNNData { base, associations: phi_assoc(nk, n, m, l) };
    lemma_h3_pred_upto_num_generators(mm, n, m, is_S, (l - 1) as nat);   // base.num = nk+2n+2+(l-1) ≥ nk+2n+2
    lemma_phi_assoc_valid(nk, n, m, l, base.num_generators);            // assocs_valid(phi_assoc, base.num)
    assert forall|i: int| #![trigger data.associations[i]] 0 <= i < data.associations.len() implies
        word_valid(data.associations[i].0, base.num_generators)
        && word_valid(data.associations[i].1, base.num_generators) by {
        // from assocs_valid(phi_assoc(nk,n,m,l), base.num_generators)
    }
}

/// `h3_pred_upto(l)` is a valid predicate presentation (0 ≤ l ≤ 2n).
pub proof fn lemma_h3_pred_upto_valid(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat,
)
    requires
        l <= 2 * n,
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        pred_presentation_valid(h3_pred_upto(mm, n, m, is_S, l)),
    decreases l,
{
    if l == 0 {
        lemma_h2_pred_valid(mm, n, m, is_S);
    } else {
        let nk = g_m(mm).num_generators;
        let data = PredHNNData {
            base: h3_pred_upto(mm, n, m, is_S, (l - 1) as nat),
            associations: phi_assoc(nk, n, m, l),
        };
        lemma_h3_pred_upto_valid(mm, n, m, is_S, (l - 1) as nat);   // IH: base valid
        lemma_h3_pred_level_data_valid(mm, n, m, is_S, l);
        lemma_hnn_pred_presentation_valid(data);
    }
}

/// The top HNN datum (`k`) is valid.
pub proof fn lemma_h3_pred_data_valid(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        hnn_pred_data_valid(h3_pred_data(mm, n, m, is_S)),
{
    let nk = g_m(mm).num_generators;
    let base = h3_pred_upto(mm, n, m, is_S, (2 * n) as nat);
    let data = h3_pred_data(mm, n, m, is_S);
    lemma_h3_pred_upto_valid(mm, n, m, is_S, (2 * n) as nat);            // pred_presentation_valid(base)
    lemma_h3_pred_upto_num_generators(mm, n, m, is_S, (2 * n) as nat);   // base.num = nk+4n+2 ≥ nk+2n+2
    lemma_psi_assoc_valid(mm, n, base.num_generators);                  // assocs_valid(psi_assoc, base.num)
    assert forall|i: int| #![trigger data.associations[i]] 0 <= i < data.associations.len() implies
        word_valid(data.associations[i].0, base.num_generators)
        && word_valid(data.associations[i].1, base.num_generators) by {
        // from assocs_valid(psi_assoc(mm,n), base.num_generators)
    }
}

/// `H₃` is a valid predicate presentation.
pub proof fn lemma_h3_pred_valid(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        pred_presentation_valid(h3_pred(mm, n, m, is_S)),
{
    lemma_h3_pred_data_valid(mm, n, m, is_S);
    lemma_hnn_pred_presentation_valid(h3_pred_data(mm, n, m, is_S));
}

} // verus!
