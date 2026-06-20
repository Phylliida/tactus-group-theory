// Layer 2 — Brick 3 (`h2.rs`): the p-level of the Higman tower.
//
// `H₂ = HNN(H₁, p ∣ p⁻¹ t_α p = t_α w_α(b) d)`. Under Approach (b) only the SINGLE
// schematic relation `p⁻¹ t p = t d` (the α=0 case: `t_0 = t`, `w_0(b)=1`) belongs
// to the finite set (I); the infinite family (II) holds in `H₃` as a derived theorem.
//
// This module builds that single p-HNN over the H₁-literal base `h1_base` (h1.rs).
// The stable letter is `p = Gen(h1_num_gens(nk,n)) = Gen(p_idx(nk,n))`, exactly the
// `p` slot of the global layout (layout.rs) — `hnn_presentation` puts the stable
// letter at `base.num_generators`, which the layout was designed to match.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::hnn::*;
use crate::machine_group::*;
use crate::layout::*;
use crate::h1::*;

verus! {

// ----------------------------------------------------------------------------
// The single p-HNN association  p⁻¹ t p = t d
// ----------------------------------------------------------------------------

/// `t·d`: the image of `t` under `p⁻¹ t p = t d`. `t = Gen(0)` (K_M's first
/// generator, layout offset 0) and `d = Gen(d_idx(nk,n))`.
pub open spec fn td_word(nk: nat, n: nat) -> Word {
    seq![ Symbol::Gen(0), Symbol::Gen(d_idx(nk, n)) ]
}

/// The single p-HNN association `(t, t·d)`, i.e. the relation `p⁻¹ t p = t d`.
/// This is the only p-relation in finite set (I).
pub open spec fn p_assoc(nk: nat, n: nat) -> Seq<(Word, Word)> {
    seq![ (seq![Symbol::Gen(0)], td_word(nk, n)) ]
}

/// The HNN data for `H₂`: the p-HNN over the H₁-literal base.
pub open spec fn h2_data(mm: ModMachine, n: nat) -> HNNData {
    HNNData { base: h1_base(mm, n), associations: p_assoc(g_m(mm).num_generators, n) }
}

/// `H₂ = HNN(H₁, p ∣ p⁻¹ t p = t d)`.
pub open spec fn h2_pres(mm: ModMachine, n: nat) -> Presentation {
    hnn_presentation(h2_data(mm, n))
}

// ----------------------------------------------------------------------------
// Generator-count / stable-letter facts (tie to the global layout)
// ----------------------------------------------------------------------------

/// The p-HNN stable letter is exactly the layout's `p = Gen(p_idx(nk,n))`.
pub proof fn lemma_h2_stable_letter(mm: ModMachine, n: nat)
    ensures stable_letter(h2_data(mm, n)) == Symbol::Gen(p_idx(g_m(mm).num_generators, n)),
{
    // stable_letter = Gen(base.num_generators) = Gen(h1_num_gens(nk,n)) = Gen(p_idx(nk,n)).
}

/// `H₂` has `h2_num_gens(4+|quads|, n)` generators (= `h1_num_gens + 1`).
pub proof fn lemma_h2_num_generators(mm: ModMachine, n: nat)
    ensures h2_pres(mm, n).num_generators == h2_num_gens((4 + mm.quads.len()) as nat, n),
{
    lemma_g_m_num_generators(mm);
}

// ----------------------------------------------------------------------------
// Validity
// ----------------------------------------------------------------------------

/// `h2_data` is a valid HNN datum: the base is valid (`h1_base`) and both
/// association words (`t` and `t·d`) are valid over the base's generators.
pub proof fn lemma_h2_data_valid(mm: ModMachine, n: nat)
    ensures hnn_data_valid(h2_data(mm, n)),
{
    let nk = g_m(mm).num_generators;
    let ng = h1_num_gens(nk, n);
    let data = h2_data(mm, n);

    lemma_h1_base_valid(mm, n);          // presentation_valid(data.base)
    assert(data.base.num_generators == ng);

    assert forall|i: int| #![trigger data.associations[i]] 0 <= i < data.associations.len() implies
        word_valid(data.associations[i].0, ng) && word_valid(data.associations[i].1, ng) by {
        // the only index is 0: association (t, t·d).
        let a0 = data.associations[0].0;
        let a1 = data.associations[0].1;
        assert(a0 == seq![Symbol::Gen(0)]);
        assert(a1 == td_word(nk, n));
        assert(d_idx(nk, n) < ng);       // nk + 2n < nk + 2n + 1
        assert forall|j: int| 0 <= j < a0.len() implies symbol_valid(#[trigger] a0[j], ng) by { }
        assert forall|j: int| 0 <= j < a1.len() implies symbol_valid(#[trigger] a1[j], ng) by {
            if j == 0 { assert(a1[0] == Symbol::Gen(0)); }
            else { assert(a1[1] == Symbol::Gen(d_idx(nk, n))); }
        }
    }
}

/// `H₂` is a valid presentation.
pub proof fn lemma_h2_pres_valid(mm: ModMachine, n: nat)
    ensures presentation_valid(h2_pres(mm, n)),
{
    lemma_h2_data_valid(mm, n);
    lemma_hnn_presentation_valid(h2_data(mm, n));
}

// ----------------------------------------------------------------------------
// The defining relation as a derived theorem of `H₂`
// ----------------------------------------------------------------------------

/// `p⁻¹ · t · p ≡ t·d` in `H₂` — the single schematic relation, recovered from
/// the HNN conjugation axiom. (Confirms the set-(I) relator does its job.)
pub proof fn lemma_h2_p_conjugates_t(mm: ModMachine, n: nat)
    ensures ({
        let p = p_idx(g_m(mm).num_generators, n);
        equiv_in_presentation(
            h2_pres(mm, n),
            seq![Symbol::Inv(p)] + seq![Symbol::Gen(0)] + seq![Symbol::Gen(p)],
            td_word(g_m(mm).num_generators, n))
    }),
{
    let nk = g_m(mm).num_generators;
    let p = p_idx(nk, n);
    let data = h2_data(mm, n);

    lemma_h2_data_valid(mm, n);
    lemma_hnn_conjugation(data, 0);
    // The conjugation lemma states the relation with `Seq::new(1, …)` forms and
    // `data.associations[0]`; bridge those to the seq![…] forms of the goal.
    let lhs_lemma = Seq::new(1, |_j: int| stable_letter_inv(data))
        + data.associations[0].0
        + Seq::new(1, |_j: int| stable_letter(data));
    let lhs_goal = seq![Symbol::Inv(p)] + seq![Symbol::Gen(0)] + seq![Symbol::Gen(p)];
    assert(stable_letter(data) == Symbol::Gen(p));
    assert(stable_letter_inv(data) == Symbol::Inv(p));
    assert(data.associations[0].0 == seq![Symbol::Gen(0)]);
    assert(data.associations[0].1 == td_word(nk, n));
    assert(lhs_lemma =~= lhs_goal);
}

} // verus!
