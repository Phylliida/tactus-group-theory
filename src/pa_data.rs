// Layer 2 — Brick 5, C3.2c / the C-arc: the abstract source presentation `P_A`.
//
// `P_A = HNN(F = free_group(n+3), p | family II over F)` — the abstract subgroup
// `A = ⟨t,x,d,b_j,p⟩` of `h2_II`, recognized as an HNN extension of the FREE base
// `F = free⟨t,x,d,b_j⟩` by the stable letter `p` with the family-(II) `p`-conjugations.
//
// **F-indexing (matches the C-arc `a_words` order, Route A — see `free_family_perm.rs`):**
//   `t = 0`, `x = 1`, `d = 2`, `b_j = 2+j` (so `b_1..b_n` at indices `3..n+2`), `p = n+3` (stable).
// The family-(II) associations are F-words: `config_word(β,0) = x⁻ᵝtxᵝ` uses only `t,x` (gens 0,1),
// and the b-substitution `w_β(b)` lives at the F-b-block `b_base = 3` (`w_c(3,n,m,β)`), `d = Gen(2)`.
//
// The C-arc crux (`lemma_phi_l_iso_at_h2II`) routes both directions through `w ≡_{P_A} ε` via two
// faithful embeddings `P_A ↪ h2_II` (`map_a` = inclusion, `map_b` = φ_l). This module pins `P_A`'s
// definition + validity; the column-translation + faithfulness live in the C-lift modules.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::hnn::{HNNData, hnn_data_valid};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::machine_group::{config_word, lemma_config_word_valid, lemma_word_valid_mono};
use crate::word_numbering::{w_c, numbers_word, lemma_w_c_valid};
use crate::h3::lemma_single_gen_valid;

verus! {

/// The F-index of the b-block (`b_1`): `d = 2`, so `b_1 = 3`, …, `b_n = n+2`.
pub open spec fn pa_b_base() -> nat { 3 }

/// The F-indexed family-(II) RHS for `β`: `t_β · w_β(b) · d` = `config(β,0) · w_c(3,n,m,β) · [d]`,
/// with `d = Gen(2)`.  (The h2_II analog is `family_II_rhs`; here everything sits over `F`.)
pub open spec fn pa_rhs(n: nat, m: nat, beta: nat) -> Word {
    config_word(beta, 0) + w_c(pa_b_base(), n, m, beta) + seq![Symbol::Gen(2)]
}

/// The F-indexed family-(II) association pairs `(t_β, t_β w_β(b) d)`, one per `β ∈ gammas`.
pub open spec fn pa_assoc(n: nat, m: nat, gammas: Seq<nat>) -> Seq<(Word, Word)> {
    Seq::new(gammas.len(), |i: int| (config_word(gammas[i], 0), pa_rhs(n, m, gammas[i])))
}

/// **`P_A = HNN(F = free_group(n+3), p | family II over F)`.**  Base = the free group on the
/// `n+3` F-generators `[t,x,d,b_1..b_n]`; stable letter `p = Gen(n+3)`; associations the F-indexed
/// family-(II) `p`-conjugations over `gammas`.
///
/// **At the crux, `gammas = betas(alphas) = [0] ++ alphas`** (NOT `alphas`): `recog_data`'s
/// associated subgroups are over `betas` (A1: its columns are `config_emb(betas)`/`basis_emb(betas)`,
/// the `α=0` head being the `p_assoc` relation `p⁻¹tp=td`).  For the lifting lemma's pinch to descend
/// index-for-index, `P_A`'s associations must match `recog_data`'s, so `P_A` is over `betas` too —
/// the `β=0` case `config(0,0)=t`, `w_0(b)=ε` recovers the `(t, td)` head.
pub open spec fn pa_data(n: nat, m: nat, gammas: Seq<nat>) -> HNNData {
    HNNData {
        base: free_group((n + 3) as nat),
        associations: pa_assoc(n, m, gammas),
    }
}

/// Structural facts: base has `n+3` generators, and there are `|gammas|` associations.
pub proof fn lemma_pa_data_shape(n: nat, m: nat, gammas: Seq<nat>)
    ensures
        pa_data(n, m, gammas).base.num_generators == n + 3,
        pa_data(n, m, gammas).associations.len() == gammas.len(),
{
}

/// **`P_A` is a valid HNN datum.**  Base `free_group(n+3)` valid; each association word valid over
/// `n+3`: `config(β,0)` uses gens `{0,1} ⊂ [0,n+3)`, the b-substitution `w_c(3,n,m,β)` uses the
/// F-b-block `[3, n+3)`, and `d = Gen(2) < n+3`.
pub proof fn lemma_pa_data_valid(n: nat, m: nat, gammas: Seq<nat>)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < gammas.len() ==> numbers_word(n, m, #[trigger] gammas[i]),
    ensures
        hnn_data_valid(pa_data(n, m, gammas)),
{
    let ng = (n + 3) as nat;
    let data = pa_data(n, m, gammas);
    lemma_free_group_valid(ng);                            // presentation_valid(base)
    assert(data.base.num_generators == ng);
    let assocs = pa_assoc(n, m, gammas);
    assert forall|i: int| #![trigger assocs[i]] 0 <= i < assocs.len() implies
        word_valid(assocs[i].0, ng) && word_valid(assocs[i].1, ng) by {
        let beta = gammas[i];
        assert(assocs[i] == (config_word(beta, 0), pa_rhs(n, m, beta)));
        // a-column: config(β,0) valid over 3 ≤ n+3.
        lemma_config_word_valid(beta, 0);                  // word_valid(·, 3)
        lemma_word_valid_mono(config_word(beta, 0), 3, ng);
        // b-column: config · w_c(3,…) · [Gen(2)].
        lemma_w_c_valid(pa_b_base(), n, m, beta, ng);      // 3 + n ≤ n + 3
        lemma_single_gen_valid(2, ng);                     // [Gen(2)], 2 < n+3
        lemma_concat_word_valid(config_word(beta, 0), w_c(pa_b_base(), n, m, beta), ng);
        lemma_concat_word_valid(config_word(beta, 0) + w_c(pa_b_base(), n, m, beta),
            seq![Symbol::Gen(2)], ng);
        assert(pa_rhs(n, m, beta) =~= (config_word(beta, 0) + w_c(pa_b_base(), n, m, beta))
            + seq![Symbol::Gen(2)]);
    }
}

} // verus!
