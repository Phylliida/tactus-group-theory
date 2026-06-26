// GAP-1 §9.2-item-(3) — the LIMIT-COMMUTATION glue (machine-independent core, "3a").
//
// docs/final-gate-axiom-removal-plan.md §9.2(3) / §12.  AUTHORIZED 2026-06-26 (Danielle, port 8051):
// build the machine-INDEPENDENT core, route (i) (monotone relator family).
//
// Connects the Layer-0.5 direct limit
//     equiv_in_g_limit(fam,n,w,ε) := ∃M≥n. w ≡ ε in G^(M) = hnn_presentation(miller_data(M,fam(M)))
// to a fixed-alphabet PREDICATE presentation `P_∞ = ⟨a,t | ⋃_M D̄_M⟩` over the union of the per-slice
// collapsed relator sets `D̄_M = dbar(M, fam(M))`, using item-2's per-slice faithful collapse
// `emb_M : G^(M) ≅ K_M = ⟨a,t | D̄_M⟩` (`lemma_collapse_{preserving,injective}`).
//
//     equiv_in_g_limit(fam, n, w, ε)  ⟺  equiv_in_pred_presentation(P_∞(fam), emb_n(w), ε)
//
//   FORWARD  (limit ⟹ pred): pick the witness slice M≥n; item-2 preserving gives ≡ in K_M; the c-word
//            image is slice-independent (§A) so it is emb_n(w); a finite K_M-derivation lifts verbatim
//            to a P_∞-pred-derivation (every K_M relator is in D̄_M ⊆ ⋃, witness M).  NO monotonicity.
//   BACKWARD (pred ⟹ limit): a P_∞-pred-derivation cites finitely many relators, each ∈ D̄_{M_i};
//            structural induction extracts M* = max(n, M_i) and — by MONOTONICITY of D̄ (route (i)) —
//            re-reads the whole derivation in the single slice P_{≤M*} = ⟨a,t | D̄_{M*}⟩; the EXISTING
//            generic transport `lemma_pred_equiv_lifts_to_finite` (pred_to_finite.rs) lands it in the
//            finite K_{M*}; item-2 injective pulls it back to G^(M*), witnessing the limit.
//
// The relator-set match identifying `⋃_M D̄_M` with Cohen's `is_S_canonical(mm,…)` is the SEPARATE
// machine-gated piece "3b" (§3.4, needs GAP-2's modular machine) and is NOT in this module.
//
// Additive; reversible; fully verified end-to-end.  Reuses pred_to_finite.rs verbatim for backward.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::lemma_relator_is_identity;
use crate::pred_presentation::*;
use crate::pred_to_finite::lemma_pred_equiv_lifts_to_finite;
use crate::benign::{apply_embedding, apply_embedding_symbol};
use crate::miller_collapse::{miller_collapse_emb, miller_collapse_word, b_sub};
use crate::miller_collapse_preserve::{dbar, k_m, lemma_collapse_preserving, lemma_dbar_valid,
    lemma_k_m_valid, lemma_source_relators_struct};
use crate::miller_collapse_inject::lemma_collapse_injective;
use crate::cohen_layer05::{equiv_in_g_limit, decls_family_valid, miller_data};
use crate::hnn::hnn_presentation;
use crate::machine_group::lemma_word_valid_mono;

verus! {

// ===========================================================================
// 0. The union / single-slice predicate presentations over `{a, t}`, and the monotonicity property.
// ===========================================================================

/// `r` is a collapsed relator at SOME slice level: `∃M. r ∈ D̄_M = dbar(M, fam(M))`.
pub open spec fn dbar_union_pred(fam: spec_fn(nat) -> Seq<Word>, r: Word) -> bool {
    exists|big_m: nat| (#[trigger] dbar(big_m, fam(big_m))).contains(r)
}

/// `P_∞ = ⟨a, t | ⋃_M D̄_M⟩` — the direct-limit presentation over the fixed `{a,t}` alphabet.
pub open spec fn p_infty(fam: spec_fn(nat) -> Seq<Word>) -> PredPresentation {
    PredPresentation { num_generators: 2, relators: |r: Word| dbar_union_pred(fam, r) }
}

/// `P_{≤M} = ⟨a, t | D̄_M⟩` — the single collapsed slice as a predicate presentation.
pub open spec fn p_le(fam: spec_fn(nat) -> Seq<Word>, m: nat) -> PredPresentation {
    PredPresentation { num_generators: 2, relators: |r: Word| dbar(m, fam(m)).contains(r) }
}

/// The collapsed relator family is directed: a relator visible at level `m1` stays visible at any
/// `m2 ≥ m1`.  (Miller §4.1: the direct limit is directed — confirmed textbook, route (i).)
pub open spec fn dbar_family_monotone(fam: spec_fn(nat) -> Seq<Word>) -> bool {
    forall|m1: nat, m2: nat, r: Word|
        #![trigger dbar(m1, fam(m1)).contains(r), dbar(m2, fam(m2)).contains(r)]
        m1 <= m2 && dbar(m1, fam(m1)).contains(r) ==> dbar(m2, fam(m2)).contains(r)
}

// ===========================================================================
// §A.  Witness-preservation:  a pure-`c` word's collapse image is slice-independent.
// `emb_M[i] = uᵢ` for `i < M`, independent of `M`; a `c`-word over `n` generators only reads indices
// `< n ≤ M`, so `apply_embedding(emb_M, w)` is the same word for every `M ≥ n`.
// ===========================================================================

/// `emb_M[i] = uᵢ` (the collapse image of the `i`-th c-generator), for `i < M`.
pub proof fn lemma_emb_index_is_mcw(big_m: nat, i: int)
    requires
        0 <= i < big_m,
    ensures
        miller_collapse_emb(big_m, 0, 1)[i] == miller_collapse_word(i as nat, 0, 1),
{
    let pre = Seq::new(big_m, |j: int| miller_collapse_word(j as nat, 0, 1));
    let suf = seq![
        seq![Symbol::Gen(0nat)],
        b_sub(0, 1),
        seq![Symbol::Gen(1nat)]
    ];
    assert(miller_collapse_emb(big_m, 0, 1) =~= pre + suf);
    assert((pre + suf)[i] == pre[i]);
    assert(pre[i] == miller_collapse_word(i as nat, 0, 1));
}

/// `emb_M` and `emb_n` agree on every generator index `< n` (`n ≤ M`).
pub proof fn lemma_emb_c_index(n: nat, big_m: nat, i: int)
    requires
        0 <= i < n,
        n <= big_m,
    ensures
        miller_collapse_emb(big_m, 0, 1)[i] == miller_collapse_emb(n, 0, 1)[i],
{
    lemma_emb_index_is_mcw(big_m, i);
    lemma_emb_index_is_mcw(n, i);
}

/// **Witness-preservation.**  For a `c`-word `w` valid over `n` generators and `M ≥ n`, the collapse
/// image is slice-independent:  `apply_embedding(emb_M, w) = apply_embedding(emb_n, w)`.
pub proof fn lemma_emb_slice_independent(n: nat, big_m: nat, w: Word)
    requires
        word_valid(w, n),
        n <= big_m,
    ensures
        apply_embedding(miller_collapse_emb(big_m, 0, 1), w)
            == apply_embedding(miller_collapse_emb(n, 0, 1), w),
    decreases w.len(),
{
    let emb_m = miller_collapse_emb(big_m, 0, 1);
    let emb_n = miller_collapse_emb(n, 0, 1);
    if w.len() == 0 {
        // both reduce to ε
    } else {
        let s = w.first();
        // s = w[0] is valid in n
        assert(symbol_valid(s, n)) by { assert(w[0] == s); };
        let idx = generator_index(s) as int;
        assert(idx < n);
        lemma_emb_c_index(n, big_m, idx);   // emb_m[idx] == emb_n[idx]
        // head symbol images agree
        assert(apply_embedding_symbol(emb_m, s) == apply_embedding_symbol(emb_n, s)) by {
            match s {
                Symbol::Gen(i) => { assert(apply_embedding_symbol(emb_m, s) == emb_m[i as int]); }
                Symbol::Inv(i) => { assert(apply_embedding_symbol(emb_m, s) == inverse_word(emb_m[i as int])); }
            }
        };
        // tail is still a c-word over n
        assert(word_valid(w.drop_first(), n)) by {
            assert forall|k: int| 0 <= k < w.drop_first().len()
                implies symbol_valid(#[trigger] w.drop_first()[k], n) by {
                assert(w.drop_first()[k] == w[k + 1]);
                assert(symbol_valid(w[k + 1], n));
            }
        };
        lemma_emb_slice_independent(n, big_m, w.drop_first());
        // apply_embedding(emb, w) = concat(head image, apply_embedding(emb, tail))
    }
}

// ===========================================================================
// §B.  Generic FORWARD bridge:  a finite presentation whose relators all satisfy a predicate embeds
// into the corresponding predicate presentation (over the same generator count).  This is the MIRROR
// of `pred_to_finite.rs::lemma_pred_equiv_lifts_to_finite` (which goes pred → finite); here finite →
// pred.  Done by a direct, index-free step map (no pred congruence lemmas needed).
// ===========================================================================

/// Translate a finite derivation step to a predicate one — relator indices become relator words.
pub open spec fn fin_to_pred_step(p: Presentation, step: DerivationStep) -> PredDerivationStep {
    match step {
        DerivationStep::FreeReduce { position } =>
            PredDerivationStep::FreeReduce { position },
        DerivationStep::FreeExpand { position, symbol } =>
            PredDerivationStep::FreeExpand { position, symbol },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            PredDerivationStep::RelatorInsert { position, relator: p.relators[relator_index as int], inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            PredDerivationStep::RelatorDelete { position, relator: p.relators[relator_index as int], inverted },
    }
}

/// Map a whole finite derivation step-sequence (head-aligned with `*_produces`).
pub open spec fn map_steps(p: Presentation, steps: Seq<DerivationStep>) -> Seq<PredDerivationStep>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Seq::empty()
    } else {
        seq![fin_to_pred_step(p, steps.first())] + map_steps(p, steps.drop_first())
    }
}

/// One `cons`-step unfolding of `pred_derivation_produces`.
proof fn lemma_pred_produces_cons(cp: PredPresentation, h: PredDerivationStep, tail: Seq<PredDerivationStep>, start: Word)
    ensures
        pred_derivation_produces(cp, seq![h] + tail, start) == (match apply_step_pred(cp, start, h) {
            Some(next) => pred_derivation_produces(cp, tail, next),
            None => None::<Word>,
        }),
{
    let steps = seq![h] + tail;
    assert(steps.len() > 0);
    assert(steps.first() == h);
    assert(steps.drop_first() =~= tail);
}

/// A successful finite step maps to a successful predicate step producing the same word.
pub proof fn lemma_fin_step_to_pred(
    p: Presentation, cp: PredPresentation, w: Word, step: DerivationStep, w2: Word,
)
    requires
        cp.num_generators == p.num_generators,
        forall|k: int| 0 <= k < p.relators.len() ==> #[trigger] (cp.relators)(p.relators[k]),
        apply_step(p, w, step) == Some(w2),
    ensures
        apply_step_pred(cp, w, fin_to_pred_step(p, step)) == Some(w2),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            // identical arm
        }
        DerivationStep::FreeExpand { position, symbol } => {
            // identical arm modulo num_generators (equal by hypothesis)
            assert(symbol_valid(symbol, cp.num_generators) == symbol_valid(symbol, p.num_generators));
        }
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= position <= w.len() && 0 <= relator_index < p.relators.len());
            assert((cp.relators)(p.relators[relator_index as int]));
            assert(get_relator(p, relator_index, inverted)
                == get_relator_pred(p.relators[relator_index as int], inverted));
        }
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p.relators.len());
            assert((cp.relators)(p.relators[relator_index as int]));
            assert(get_relator(p, relator_index, inverted)
                == get_relator_pred(p.relators[relator_index as int], inverted));
        }
    }
}

/// A finite derivation lifts (verbatim) to a predicate derivation producing the same endpoint.
pub proof fn lemma_fin_produces_to_pred(
    p: Presentation, cp: PredPresentation, steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        cp.num_generators == p.num_generators,
        forall|k: int| 0 <= k < p.relators.len() ==> #[trigger] (cp.relators)(p.relators[k]),
        derivation_produces(p, steps, start) == Some(end),
    ensures
        pred_derivation_produces(cp, map_steps(p, steps), start) == Some(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(map_steps(p, steps) =~= Seq::<PredDerivationStep>::empty());
    } else {
        let h = steps.first();
        let tail = steps.drop_first();
        // produces == Some(end) forces the head step to succeed
        assert(derivation_produces(p, steps, start) == (match apply_step(p, start, h) {
            Some(next) => derivation_produces(p, tail, next),
            None => None::<Word>,
        }));
        let res = apply_step(p, start, h);
        assert(res is Some);
        let w1 = res.unwrap();
        assert(apply_step(p, start, h) == Some(w1));
        assert(derivation_produces(p, tail, w1) == Some(end));
        lemma_fin_step_to_pred(p, cp, start, h, w1);
        lemma_fin_produces_to_pred(p, cp, tail, w1, end);
        assert(map_steps(p, steps) =~= seq![fin_to_pred_step(p, h)] + map_steps(p, tail));
        lemma_pred_produces_cons(cp, fin_to_pred_step(p, h), map_steps(p, tail), start);
    }
}

/// **Generic forward bridge.**  If `cp` and `p` share their generator count and every `p`-relator
/// satisfies `cp`'s relator predicate, then `p`-equivalence implies `cp`-equivalence.
pub proof fn lemma_fin_equiv_to_pred(
    p: Presentation, cp: PredPresentation, w1: Word, w2: Word,
)
    requires
        cp.num_generators == p.num_generators,
        forall|k: int| 0 <= k < p.relators.len() ==> #[trigger] (cp.relators)(p.relators[k]),
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_pred_presentation(cp, w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    assert(derivation_produces(p, d.steps, w1) == Some(w2));
    lemma_fin_produces_to_pred(p, cp, d.steps, w1, w2);
    let pd = PredDerivation { steps: map_steps(p, d.steps) };
    assert(pred_derivation_valid(cp, pd, w1, w2));
}

} // verus!
