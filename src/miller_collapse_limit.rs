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

/// The collapsed relator family is directed: a NON-TRIVIAL relator visible at level `m1` stays
/// visible at any `m2 ≥ m1`.  (Miller §4.1: the direct limit is directed — confirmed textbook,
/// route (i).)  The `r != empty_word()` guard is essential: the trivial (empty) relator is an
/// administrative padding artifact of the per-slice family (`ceer_decls_fam` pads non-fitting
/// stages with `empty_word()`), and it is NOT slice-monotone (it can appear at one slice and vanish
/// at a larger one).  Since the empty relator is the identity — inserting/deleting it is a no-op —
/// directedness need only hold for the genuine group relators; the backward extraction strips the
/// empty no-op steps first (see `strip_empty_steps`).
pub open spec fn dbar_family_monotone(fam: spec_fn(nat) -> Seq<Word>) -> bool {
    forall|m1: nat, m2: nat, r: Word|
        #![trigger dbar(m1, fam(m1)).contains(r), dbar(m2, fam(m2)).contains(r)]
        r != empty_word() && m1 <= m2 && dbar(m1, fam(m1)).contains(r) ==> dbar(m2, fam(m2)).contains(r)
}

// ===========================================================================
// Empty-relator (no-op) step handling, for the backward extraction.
//
// A `PredDerivationStep` that inserts/deletes the EMPTY relator is a no-op (it leaves the word
// unchanged) — but it is only a *valid* step at a slice where the empty word is a relator, and the
// empty relator is not slice-monotone.  So before re-reading a `P_∞` derivation at a single finite
// slice we drop the empty-relator steps; the surviving steps cite only genuine relators, which ARE
// monotone (`dbar_family_monotone`).  This keeps the abstract monotonicity hypothesis honest while
// making it satisfiable by the concrete CEER family.
// ===========================================================================

/// A derivation step that does NOT cite the trivial (empty) relator.
pub open spec fn step_nonempty(step: PredDerivationStep) -> bool {
    match step {
        PredDerivationStep::RelatorInsert { relator, .. } => relator != empty_word(),
        PredDerivationStep::RelatorDelete { relator, .. } => relator != empty_word(),
        _ => true,
    }
}

/// Every step avoids the trivial (empty) relator.
pub open spec fn derivation_nonempty(steps: Seq<PredDerivationStep>) -> bool {
    forall|i: int| 0 <= i < steps.len() ==> step_nonempty(#[trigger] steps[i])
}

/// Drop every empty-relator step (each is a no-op).
pub open spec fn strip_empty_steps(steps: Seq<PredDerivationStep>) -> Seq<PredDerivationStep>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Seq::<PredDerivationStep>::empty()
    } else if step_nonempty(steps.first()) {
        seq![steps.first()] + strip_empty_steps(steps.drop_first())
    } else {
        strip_empty_steps(steps.drop_first())
    }
}

/// An empty-relator step is a no-op: when it succeeds, it produces the input word unchanged.
proof fn lemma_empty_step_noop(p: PredPresentation, w: Word, h: PredDerivationStep, w1: Word)
    requires
        !step_nonempty(h),
        apply_step_pred(p, w, h) == Some(w1),
    ensures
        w1 == w,
{
    match h {
        PredDerivationStep::FreeReduce { .. } => { assert(false); }
        PredDerivationStep::FreeExpand { .. } => { assert(false); }
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            assert(relator == empty_word());
            let r = get_relator_pred(relator, inverted);
            // get_relator_pred(empty, _) == empty (inverse_word(empty) == empty)
            assert(r == empty_word());
            // success ⟹ 0 <= position <= w.len() and w1 = w[0..position] + r + w[position..]
            assert(w1 == w.subrange(0, position) + r + w.subrange(position, w.len() as int));
            assert(0 <= position <= w.len());
            assert(w1 =~= w);
        }
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert(relator == empty_word());
            let r = get_relator_pred(relator, inverted);
            assert(r == empty_word());
            lemma_inverse_word_len(relator);
            assert(r.len() == 0);
            // success ⟹ w1 = w[0..position] + w[position+0..]
            assert(w1 == w.subrange(0, position) + w.subrange(position + 0, w.len() as int));
            assert(0 <= position <= w.len());
            assert(w1 =~= w);
        }
    }
}

/// Unfold `pred_derivation_produces` over a cons `[h] ++ rest`.
proof fn lemma_produces_cons(
    p: PredPresentation, h: PredDerivationStep, rest: Seq<PredDerivationStep>,
    start: Word, w1: Word, end: Word,
)
    requires
        apply_step_pred(p, start, h) == Some(w1),
        pred_derivation_produces(p, rest, w1) == Some(end),
    ensures
        pred_derivation_produces(p, seq![h] + rest, start) == Some(end),
{
    let s = seq![h] + rest;
    assert(s.len() == rest.len() + 1);
    assert(s.first() == h);
    assert(s.drop_first() =~= rest);
    assert(pred_derivation_produces(p, s, start) == (match apply_step_pred(p, start, s.first()) {
        Some(next) => pred_derivation_produces(p, s.drop_first(), next),
        None => None::<Word>,
    }));
}

/// Stripping empty (no-op) steps preserves the produced word.
proof fn lemma_strip_preserves_produces(
    p: PredPresentation, steps: Seq<PredDerivationStep>, start: Word, end: Word,
)
    requires
        pred_derivation_produces(p, steps, start) == Some(end),
    ensures
        pred_derivation_produces(p, strip_empty_steps(steps), start) == Some(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let h = steps.first();
        let tail = steps.drop_first();
        assert(pred_derivation_produces(p, steps, start) == (match apply_step_pred(p, start, h) {
            Some(next) => pred_derivation_produces(p, tail, next),
            None => None::<Word>,
        }));
        let res = apply_step_pred(p, start, h);
        assert(res is Some);
        let w1 = res.unwrap();
        assert(pred_derivation_produces(p, tail, w1) == Some(end));
        if step_nonempty(h) {
            lemma_strip_preserves_produces(p, tail, w1, end);
            assert(strip_empty_steps(steps) == seq![h] + strip_empty_steps(tail));
            lemma_produces_cons(p, h, strip_empty_steps(tail), start, w1, end);
        } else {
            lemma_empty_step_noop(p, start, h, w1);
            assert(w1 == start);
            assert(pred_derivation_produces(p, tail, start) == Some(end));
            lemma_strip_preserves_produces(p, tail, start, end);
            assert(strip_empty_steps(steps) == strip_empty_steps(tail));
        }
    }
}

/// The stripped derivation has no empty-relator steps.
proof fn lemma_strip_yields_nonempty(steps: Seq<PredDerivationStep>)
    ensures
        derivation_nonempty(strip_empty_steps(steps)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(strip_empty_steps(steps) == Seq::<PredDerivationStep>::empty());
    } else {
        lemma_strip_yields_nonempty(steps.drop_first());
        if step_nonempty(steps.first()) {
            let stripped = strip_empty_steps(steps);
            let tail_stripped = strip_empty_steps(steps.drop_first());
            assert(stripped == seq![steps.first()] + tail_stripped);
            assert forall|i: int| 0 <= i < stripped.len() implies
                step_nonempty(#[trigger] stripped[i]) by {
                if i == 0 {
                    assert(stripped[0] == steps.first());
                } else {
                    assert(stripped[i] == tail_stripped[i - 1]);
                }
            }
        }
    }
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

// ===========================================================================
// §C.  FORWARD:  equiv_in_g_limit ⟹ equiv_in_pred_presentation(P_∞).  (No monotonicity needed.)
// ===========================================================================

/// `apply_embedding` fixes `ε`.
pub proof fn lemma_apply_embedding_empty(emb: Seq<Word>)
    ensures
        apply_embedding(emb, empty_word()) == empty_word(),
{
    assert(empty_word().len() == 0);
}

/// A sequence contains the element at any in-range index.
pub proof fn lemma_seq_index_contains(s: Seq<Word>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.contains(s[i]),
{
    assert(s[i] == s[i]);
}

/// **FORWARD.**  If `w` (a `c`-word over `n` generators) is trivial in the direct limit, then its
/// collapse image `emb_n(w)` is trivial in the union predicate presentation `P_∞`.
pub proof fn lemma_limit_to_pred(fam: spec_fn(nat) -> Seq<Word>, n: nat, w: Word)
    requires
        decls_family_valid(fam),
        word_valid(w, n),
        equiv_in_g_limit(fam, n, w, empty_word()),
    ensures
        equiv_in_pred_presentation(p_infty(fam),
            apply_embedding(miller_collapse_emb(n, 0, 1), w), empty_word()),
{
    // 1. extract the witness slice M ≥ n
    let big_m = choose|big_m: nat| n <= big_m
        && equiv_in_presentation(#[trigger] hnn_presentation(miller_data(big_m, fam(big_m))), w, empty_word());
    assert(n <= big_m && equiv_in_presentation(hnn_presentation(miller_data(big_m, fam(big_m))), w, empty_word()));

    let decls = fam(big_m);
    assert forall|k: int| 0 <= k < decls.len() implies word_valid(#[trigger] decls[k], big_m) by {
        assert(decls[k] == fam(big_m)[k]);   // fire decls_family_valid at (big_m, k)
    }
    let g = hnn_presentation(miller_data(big_m, decls));
    let km = k_m(big_m, decls);
    let emb_m = miller_collapse_emb(big_m, 0, 1);
    let emb_n = miller_collapse_emb(n, 0, 1);

    // 2. item-2 preserving:  equiv(km, emb_m(w), emb_m(ε)) ⟹ equiv(km, emb_m(w), ε)
    lemma_collapse_preserving(big_m, decls);     // embedding_preserving(g, km, emb_m)
    lemma_source_relators_struct(big_m, decls);  // g.num_generators == big_m + 3
    lemma_word_valid_mono(w, n, (big_m + 3) as nat);
    lemma_apply_embedding_empty(emb_m);
    assert(equiv_in_presentation(km, apply_embedding(emb_m, w), apply_embedding(emb_m, empty_word())));
    assert(equiv_in_presentation(km, apply_embedding(emb_m, w), empty_word()));

    // 3. witness-preservation:  emb_m(w) == emb_n(w)
    lemma_emb_slice_independent(n, big_m, w);
    assert(equiv_in_presentation(km, apply_embedding(emb_n, w), empty_word()));

    // 4. forward bridge:  km ↪ P_∞(fam)  (every km relator is in D̄_{big_m} ⊆ ⋃, witness big_m)
    assert forall|k: int| 0 <= k < km.relators.len()
        implies #[trigger] (p_infty(fam).relators)(km.relators[k]) by {
        assert(km.relators == dbar(big_m, fam(big_m)));
        lemma_seq_index_contains(dbar(big_m, fam(big_m)), k);   // dbar(big_m,·).contains(km.relators[k])
        assert(dbar_union_pred(fam, km.relators[k]));           // witness big_m
    }
    lemma_fin_equiv_to_pred(km, p_infty(fam), apply_embedding(emb_n, w), empty_word());
}

// ===========================================================================
// §D.  BACKWARD:  equiv_in_pred_presentation(P_∞) ⟹ equiv_in_g_limit.  (Compactness, route (i).)
// ===========================================================================

/// A successful `P_{≤m1}` step is a successful `P_{≤m2}` step (`m1 ≤ m2`), by monotonicity.
proof fn lemma_step_slice_monotone(
    fam: spec_fn(nat) -> Seq<Word>, m1: nat, m2: nat, w: Word, step: PredDerivationStep, w2: Word,
)
    requires
        dbar_family_monotone(fam),
        step_nonempty(step),
        m1 <= m2,
        apply_step_pred(p_le(fam, m1), w, step) == Some(w2),
    ensures
        apply_step_pred(p_le(fam, m2), w, step) == Some(w2),
{
    match step {
        PredDerivationStep::FreeReduce { position } => { }
        PredDerivationStep::FreeExpand { position, symbol } => { }
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            assert(relator != empty_word());              // from step_nonempty
            assert(dbar(m1, fam(m1)).contains(relator));   // from success
            assert(dbar(m2, fam(m2)).contains(relator));   // fires (non-empty) monotonicity
        }
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert(relator != empty_word());              // from step_nonempty
            assert(dbar(m1, fam(m1)).contains(relator));
            assert(dbar(m2, fam(m2)).contains(relator));
        }
    }
}

/// A whole `P_{≤m1}` derivation is a `P_{≤m2}` derivation (`m1 ≤ m2`).
proof fn lemma_produces_slice_monotone(
    fam: spec_fn(nat) -> Seq<Word>, m1: nat, m2: nat, steps: Seq<PredDerivationStep>, start: Word, end: Word,
)
    requires
        dbar_family_monotone(fam),
        derivation_nonempty(steps),
        m1 <= m2,
        pred_derivation_produces(p_le(fam, m1), steps, start) == Some(end),
    ensures
        pred_derivation_produces(p_le(fam, m2), steps, start) == Some(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let h = steps.first();
        let tail = steps.drop_first();
        assert(step_nonempty(h)) by { assert(steps[0] == h); }   // derivation_nonempty at index 0
        assert(derivation_nonempty(tail)) by {
            assert forall|i: int| 0 <= i < tail.len() implies step_nonempty(#[trigger] tail[i]) by {
                assert(tail[i] == steps[i + 1]);
            }
        }
        assert(pred_derivation_produces(p_le(fam, m1), steps, start) == (match apply_step_pred(p_le(fam, m1), start, h) {
            Some(next) => pred_derivation_produces(p_le(fam, m1), tail, next),
            None => None::<Word>,
        }));
        let res1 = apply_step_pred(p_le(fam, m1), start, h);
        assert(res1 is Some);
        let w1 = res1.unwrap();
        assert(apply_step_pred(p_le(fam, m1), start, h) == Some(w1));
        assert(pred_derivation_produces(p_le(fam, m1), tail, w1) == Some(end));
        lemma_step_slice_monotone(fam, m1, m2, start, h, w1);
        lemma_produces_slice_monotone(fam, m1, m2, tail, w1, end);
        assert(pred_derivation_produces(p_le(fam, m2), steps, start) == (match apply_step_pred(p_le(fam, m2), start, h) {
            Some(next) => pred_derivation_produces(p_le(fam, m2), tail, next),
            None => None::<Word>,
        }));
    }
}

/// A single `P_∞` step is realized in SOME slice `P_{≤m0}` with `m0 ≥ n` (the relator's witness level,
/// raised to `n`).
proof fn lemma_first_step_slice(
    fam: spec_fn(nat) -> Seq<Word>, n: nat, w: Word, step: PredDerivationStep, w2: Word,
)
    requires
        dbar_family_monotone(fam),
        step_nonempty(step),
        apply_step_pred(p_infty(fam), w, step) == Some(w2),
    ensures
        exists|m0: nat| #![trigger apply_step_pred(p_le(fam, m0), w, step)]
            n <= m0 && apply_step_pred(p_le(fam, m0), w, step) == Some(w2),
{
    match step {
        PredDerivationStep::FreeReduce { position } => {
            assert(n <= n && apply_step_pred(p_le(fam, n), w, step) == Some(w2));
        }
        PredDerivationStep::FreeExpand { position, symbol } => {
            assert(n <= n && apply_step_pred(p_le(fam, n), w, step) == Some(w2));
        }
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            assert(relator != empty_word());                // from step_nonempty
            assert(dbar_union_pred(fam, relator));
            let big_m0 = choose|big_m0: nat| (#[trigger] dbar(big_m0, fam(big_m0))).contains(relator);
            assert(dbar(big_m0, fam(big_m0)).contains(relator));
            let m0: nat = if big_m0 >= n { big_m0 } else { n };
            assert(dbar(m0, fam(m0)).contains(relator));    // fires (non-empty) monotonicity (big_m0 <= m0)
            assert(n <= m0 && apply_step_pred(p_le(fam, m0), w, step) == Some(w2));
        }
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert(relator != empty_word());                // from step_nonempty
            assert(dbar_union_pred(fam, relator));
            let big_m0 = choose|big_m0: nat| (#[trigger] dbar(big_m0, fam(big_m0))).contains(relator);
            assert(dbar(big_m0, fam(big_m0)).contains(relator));
            let m0: nat = if big_m0 >= n { big_m0 } else { n };
            assert(dbar(m0, fam(m0)).contains(relator));
            assert(n <= m0 && apply_step_pred(p_le(fam, m0), w, step) == Some(w2));
        }
    }
}

/// **Compactness extraction.**  A `P_∞`-derivation lives in a single slice `P_{≤M*}` (`M* ≥ n`):
/// take the max of `n` and the per-step relator witness levels; monotonicity stabilizes all of them.
proof fn lemma_extract_slice(
    fam: spec_fn(nat) -> Seq<Word>, n: nat, steps: Seq<PredDerivationStep>, start: Word, end: Word,
)
    requires
        dbar_family_monotone(fam),
        derivation_nonempty(steps),
        pred_derivation_produces(p_infty(fam), steps, start) == Some(end),
    ensures
        exists|m: nat| #![trigger pred_derivation_produces(p_le(fam, m), steps, start)]
            n <= m && pred_derivation_produces(p_le(fam, m), steps, start) == Some(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(n <= n && pred_derivation_produces(p_le(fam, n), steps, start) == Some(end));
    } else {
        let h = steps.first();
        let tail = steps.drop_first();
        assert(step_nonempty(h)) by { assert(steps[0] == h); }   // derivation_nonempty at index 0
        assert(derivation_nonempty(tail)) by {
            assert forall|i: int| 0 <= i < tail.len() implies step_nonempty(#[trigger] tail[i]) by {
                assert(tail[i] == steps[i + 1]);
            }
        }
        assert(pred_derivation_produces(p_infty(fam), steps, start) == (match apply_step_pred(p_infty(fam), start, h) {
            Some(next) => pred_derivation_produces(p_infty(fam), tail, next),
            None => None::<Word>,
        }));
        let res = apply_step_pred(p_infty(fam), start, h);
        assert(res is Some);
        let w1 = res.unwrap();
        assert(apply_step_pred(p_infty(fam), start, h) == Some(w1));
        assert(pred_derivation_produces(p_infty(fam), tail, w1) == Some(end));

        lemma_extract_slice(fam, n, tail, w1, end);
        let m1 = choose|m1: nat| #![trigger pred_derivation_produces(p_le(fam, m1), tail, w1)]
            n <= m1 && pred_derivation_produces(p_le(fam, m1), tail, w1) == Some(end);
        assert(n <= m1 && pred_derivation_produces(p_le(fam, m1), tail, w1) == Some(end));

        lemma_first_step_slice(fam, n, start, h, w1);
        let m0 = choose|m0: nat| #![trigger apply_step_pred(p_le(fam, m0), start, h)]
            n <= m0 && apply_step_pred(p_le(fam, m0), start, h) == Some(w1);
        assert(n <= m0 && apply_step_pred(p_le(fam, m0), start, h) == Some(w1));

        let mf: nat = if m0 >= m1 { m0 } else { m1 };
        lemma_step_slice_monotone(fam, m0, mf, start, h, w1);       // head succeeds in mf
        lemma_produces_slice_monotone(fam, m1, mf, tail, w1, end);  // tail produces in mf
        assert(pred_derivation_produces(p_le(fam, mf), steps, start) == (match apply_step_pred(p_le(fam, mf), start, h) {
            Some(next) => pred_derivation_produces(p_le(fam, mf), tail, next),
            None => None::<Word>,
        }));
        assert(n <= mf && pred_derivation_produces(p_le(fam, mf), steps, start) == Some(end));
    }
}

/// **BACKWARD.**  If the collapse image `emb_n(w)` is trivial in the union presentation `P_∞`, then
/// the original `c`-word `w` is trivial in the direct limit.
pub proof fn lemma_pred_to_limit(fam: spec_fn(nat) -> Seq<Word>, n: nat, w: Word)
    requires
        decls_family_valid(fam),
        dbar_family_monotone(fam),
        word_valid(w, n),
        equiv_in_pred_presentation(p_infty(fam),
            apply_embedding(miller_collapse_emb(n, 0, 1), w), empty_word()),
    ensures
        equiv_in_g_limit(fam, n, w, empty_word()),
{
    let emb_n = miller_collapse_emb(n, 0, 1);
    let v = apply_embedding(emb_n, w);

    // 1. extract a single slice mf ≥ n in which the (collapsed) derivation lives.
    //    First STRIP the empty-relator (no-op) steps: the trivial relator is not slice-monotone,
    //    so the surviving (genuine) relators are exactly what `dbar_family_monotone` covers.
    let d = choose|d: PredDerivation| pred_derivation_valid(p_infty(fam), d, v, empty_word());
    assert(pred_derivation_produces(p_infty(fam), d.steps, v) == Some(empty_word()));
    let stripped = strip_empty_steps(d.steps);
    lemma_strip_preserves_produces(p_infty(fam), d.steps, v, empty_word());
    lemma_strip_yields_nonempty(d.steps);
    assert(pred_derivation_produces(p_infty(fam), stripped, v) == Some(empty_word()));
    assert(derivation_nonempty(stripped));
    lemma_extract_slice(fam, n, stripped, v, empty_word());
    let mf = choose|mf: nat| #![trigger pred_derivation_produces(p_le(fam, mf), stripped, v)]
        n <= mf && pred_derivation_produces(p_le(fam, mf), stripped, v) == Some(empty_word());
    assert(n <= mf && pred_derivation_produces(p_le(fam, mf), stripped, v) == Some(empty_word()));
    let pd = PredDerivation { steps: stripped };
    assert(pred_derivation_valid(p_le(fam, mf), pd, v, empty_word()));
    assert(equiv_in_pred_presentation(p_le(fam, mf), v, empty_word()));

    // 2. existing generic transport P_{≤mf} → finite K_{mf}
    let decls = fam(mf);
    assert forall|k: int| 0 <= k < decls.len() implies word_valid(#[trigger] decls[k], mf) by {
        assert(decls[k] == fam(mf)[k]);
    }
    let km = k_m(mf, decls);
    lemma_k_m_valid(mf, decls);
    lemma_dbar_valid(mf, decls);
    assert forall|r: Word| #[trigger] (p_le(fam, mf).relators)(r) implies
        (equiv_in_presentation(km, r, empty_word()) && word_valid(r, 2)) by {
        assert(dbar(mf, decls).contains(r));   // = (p_le(fam,mf).relators)(r), decls = fam(mf)
        let idx = choose|idx: int| 0 <= idx < dbar(mf, decls).len() && dbar(mf, decls)[idx] == r;
        assert(0 <= idx < dbar(mf, decls).len() && dbar(mf, decls)[idx] == r);
        assert(km.relators[idx] == r);
        lemma_relator_is_identity(km, idx);
    }
    lemma_pred_equiv_lifts_to_finite(p_le(fam, mf), km, v, empty_word());
    assert(equiv_in_presentation(km, v, empty_word()));

    // 3. witness-preservation: v = emb_n(w) == emb_mf(w)
    lemma_emb_slice_independent(n, mf, w);
    let emb_mf = miller_collapse_emb(mf, 0, 1);
    assert(v == apply_embedding(emb_mf, w));
    lemma_apply_embedding_empty(emb_mf);
    assert(equiv_in_presentation(km, apply_embedding(emb_mf, w), apply_embedding(emb_mf, empty_word())));

    // 4. item-2 injective pulls back to G^(mf)
    lemma_collapse_injective(mf, decls);
    lemma_source_relators_struct(mf, decls);
    lemma_word_valid_mono(w, n, (mf + 3) as nat);
    let g = hnn_presentation(miller_data(mf, decls));
    assert(equiv_in_presentation(g, w, empty_word()));
    assert(equiv_in_g_limit(fam, n, w, empty_word()));   // witness mf ≥ n
}

// ===========================================================================
// §E.  HEADLINE — the limit-commutation iff (machine-independent core, "3a").
// ===========================================================================

/// **★ LIMIT-COMMUTATION (GAP-1 item-3, machine-independent core).**  For a valid, directed collapsed
/// relator family and any `c`-word `w` over `n` generators:
///
///     equiv_in_g_limit(fam, n, w, ε)  ⟺  equiv_in_pred_presentation(P_∞(fam), emb_n(w), ε)
///
/// The direct limit `C = ⋃_M G^(M)`'s `c`-word problem equals the word problem of the fixed-`{a,t}`
/// presentation `P_∞ = ⟨a,t | ⋃_M D̄_M⟩`.  Identifying `⋃_M D̄_M` with Cohen's `is_S_canonical(mm,…)`
/// (item "3b", §3.4) is the remaining machine-gated step (needs GAP-2).
pub proof fn lemma_limit_commutation(fam: spec_fn(nat) -> Seq<Word>, n: nat, w: Word)
    requires
        decls_family_valid(fam),
        dbar_family_monotone(fam),
        word_valid(w, n),
    ensures
        equiv_in_g_limit(fam, n, w, empty_word())
            <==> equiv_in_pred_presentation(p_infty(fam),
                    apply_embedding(miller_collapse_emb(n, 0, 1), w), empty_word()),
{
    if equiv_in_g_limit(fam, n, w, empty_word()) {
        lemma_limit_to_pred(fam, n, w);
    }
    if equiv_in_pred_presentation(p_infty(fam),
        apply_embedding(miller_collapse_emb(n, 0, 1), w), empty_word()) {
        lemma_pred_to_limit(fam, n, w);
    }
}

} // verus!
