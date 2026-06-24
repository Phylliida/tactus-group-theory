// Layer 2 — Cohen §1 assembly, bricks CS-5a/CS-5b: the k von-Dyck iso `A₊ ≅ A₋`, scaffold + BACKWARD.
//
// `docs/cohen-cs5-blueprint.md`. The top HNN datum `h3_pred_data` (CS-3) carries the `k` stable
// letter with associations `psi_assoc`:  `a_col = [U…,d,b_j…,p]` (A₊), `b_col = [U…,d,(b_j c_j)…,p]`
// (A₋), `U = g_subgens`. The CS-5 target `hnn_pred_associations_isomorphic(h3_pred_data)` reduces (by
// CS-4e base-faithfulness up the a-tower) to the iso `(★k)` over `h2_pred`:
//
//   emb(a_col, w) ≡_{h2_pred} ε   ⟺   emb(b_col, w) ≡_{h2_pred} ε
//
// This file does:
//   * the two GENERIC predicate helpers `(★k)` needs (a hom∘embedding compose + relator monotonicity),
//   * the column accessors `k_a_col`/`k_b_col` (= the `psi_assoc` columns),
//   * **CS-5b — the BACKWARD `b ⟹ a`** = Cohen's c-killing endomorphism, here realized by REUSING
//     CS-4b's `s_strip` (kill every c, fix non-c) `h2_pred → h2_noS_pred`: `s_strip ∘ b_col = a_col`
//     pointwise, then lift `≡_{h2_noS_pred}` back to `≡_{h2_pred}` by relator monotonicity.
//
// CS-5c (the hard von-Dyck-forward recognition) and CS-5d (the tower lift) are the next bricks.
// Additive/reversible; no regression.

use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::presentation::{Presentation, DerivationStep, Derivation, get_relator, apply_step,
    derivation_produces, derivation_valid, equiv_in_presentation};
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::{lemma_pred_equiv_concat_left, lemma_pred_equiv_concat_right,
    lemma_pred_word_inverse_left, lemma_pred_word_inverse_right, lemma_pred_relator_is_identity};
use crate::pred_homomorphism::{PredHomomorphismData, apply_hom_pred, apply_hom_symbol_pred,
    is_valid_pred_homomorphism, lemma_hom_pred_respects_concat, lemma_hom_pred_respects_inverse,
    lemma_hom_pred_preserves_equiv, lemma_hom_pred_empty, lemma_hom_pred_singleton};
use crate::benign::{apply_embedding, apply_embedding_symbol};
use crate::machine_group::{ModMachine, g_m, g_subgens, g_m_associations, mod_machine_wf, mm_in_H0,
    config_word, lemma_g_m_num_generators, lemma_g_m_associations_valid, lemma_word_valid_mono,
    lemma_config_word_valid};
use crate::layout::{h2_num_gens, h1_num_gens, d_idx, p_idx, c_base, b_base};
use crate::word_numbering::{numbers_word, w_b, w_c, w_bc, bc_letter};
use crate::h1::{h1_base, comm_relators};
use crate::h3::{psi_assoc, psi_ublock, psi_bcblock, lemma_psi_assoc_valid};
use crate::h3_ii::{family_II_lhs, family_II_rhs, family_II_relator};
use crate::higman_consequences::lemma_w_bc_split;
use crate::cohen_h2::{h2_pred, h2_pred_relator, c_symbol, s_relators_valid, s_realizes,
    lemma_h2_pred_valid};
use crate::h3_ii::lemma_family_II_relator_valid;
use crate::cohen_cs4::lemma_family_II_relator_in_h2_pred;
use crate::cohen_cs4b::{s_strip, h2_noS_pred, h2_noS_pred_relator, lemma_s_strip_valid,
    lemma_strip_fixes_noc_word, lemma_strip_symbol_c, lemma_strip_symbol_noc, lemma_cs4b_compactness};
use crate::cohen_retraction::{no_c_word, lemma_no_c_inverse, lemma_no_c_concat};
use crate::h3_ii::h2_II;
use crate::benign::lemma_apply_embedding_valid;

verus! {

// ============================================================================
// Generic predicate helpers
// ============================================================================

/// The composite images `comp[i] = apply_hom_pred(h, emb[i])` (pred analog of `free_basis::comp_images`).
pub open spec fn comp_images_pred(h: PredHomomorphismData, emb: Seq<Word>) -> Seq<Word> {
    Seq::new(emb.len(), |i: int| apply_hom_pred(h, emb[i]))
}

/// **Hom ∘ embedding compose.** `apply_hom_pred(h, emb(imgs, w)) = emb(comp_images_pred(h, imgs), w)`
/// — a hom applied to an embedded word is the embedding by the hom-images. Pred port of
/// `free_basis::lemma_apply_hom_embedding_compose`.
pub proof fn lemma_apply_hom_pred_embedding_compose(h: PredHomomorphismData, emb: Seq<Word>, w: Word)
    requires
        word_valid(w, emb.len()),
    ensures
        apply_hom_pred(h, apply_embedding(emb, w)) =~= apply_embedding(comp_images_pred(h, emb), w),
    decreases w.len(),
{
    let comp = comp_images_pred(h, emb);
    assert(comp.len() == emb.len());
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, emb.len())) by { assert(w[0] == s); }
        assert(word_valid(rest, emb.len())) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(#[trigger] rest[k], emb.len()) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_apply_hom_pred_embedding_compose(h, emb, rest);
        match s {
            Symbol::Gen(i) => {
                assert(i < emb.len());
                assert(apply_embedding_symbol(emb, s) == emb[i as int]);
                assert(comp[i as int] == apply_hom_pred(h, emb[i as int]));
                assert(apply_embedding_symbol(comp, s) == comp[i as int]);
            },
            Symbol::Inv(i) => {
                assert(i < emb.len());
                assert(apply_embedding_symbol(emb, s) == inverse_word(emb[i as int]));
                lemma_hom_pred_respects_inverse(h, emb[i as int]);
                assert(comp[i as int] == apply_hom_pred(h, emb[i as int]));
                assert(apply_embedding_symbol(comp, s) == inverse_word(comp[i as int]));
            },
        }
        assert(apply_embedding(emb, w)
            =~= concat(apply_embedding_symbol(emb, s), apply_embedding(emb, rest)));
        lemma_hom_pred_respects_concat(h, apply_embedding_symbol(emb, s), apply_embedding(emb, rest));
        assert(apply_embedding(comp, w)
            =~= concat(apply_embedding_symbol(comp, s), apply_embedding(comp, rest)));
    }
}

/// A derivation valid in `p1` is valid in `p2` when `p2` accepts every relator `p1` does
/// (and they share generators) — `apply_step_pred` depends on `p` only via num-gens + relator guard.
proof fn lemma_pred_produces_mono(
    p1: PredPresentation, p2: PredPresentation, steps: Seq<PredDerivationStep>, start: Word, end: Word,
)
    requires
        p1.num_generators == p2.num_generators,
        forall|w: Word| #[trigger] (p1.relators)(w) ==> (p2.relators)(w),
        pred_derivation_produces(p1, steps, start) == Some(end),
    ensures
        pred_derivation_produces(p2, steps, start) == Some(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step_pred(p1, start, step).unwrap();
        assert(apply_step_pred(p1, start, step) == Some(next));
        assert(apply_step_pred(p2, start, step) == Some(next)) by {
            match step {
                PredDerivationStep::FreeReduce { position } => {},
                PredDerivationStep::FreeExpand { position, symbol } => {},
                PredDerivationStep::RelatorInsert { position, relator, inverted } => {
                    assert((p1.relators)(relator));
                    assert((p2.relators)(relator));
                },
                PredDerivationStep::RelatorDelete { position, relator, inverted } => {
                    assert((p1.relators)(relator));
                    assert((p2.relators)(relator));
                },
            }
        }
        lemma_pred_produces_mono(p1, p2, steps.drop_first(), next, end);
    }
}

/// **Relator monotonicity.** If `p2`'s relators include `p1`'s (same generators), equivalence lifts
/// `p1 → p2`. Used to lift `≡_{h2_noS_pred}` to `≡_{h2_pred}` (h2_noS relators ⊆ h2_pred relators).
pub proof fn lemma_pred_equiv_relator_mono(
    p1: PredPresentation, p2: PredPresentation, a: Word, b: Word,
)
    requires
        p1.num_generators == p2.num_generators,
        forall|w: Word| #[trigger] (p1.relators)(w) ==> (p2.relators)(w),
        equiv_in_pred_presentation(p1, a, b),
    ensures
        equiv_in_pred_presentation(p2, a, b),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(p1, d, a, b);
    lemma_pred_produces_mono(p1, p2, d.steps, a, b);
    assert(pred_derivation_valid(p2, d, a, b));
}

// ============================================================================
// CS-5a — the k-iso columns
// ============================================================================

/// `A₊` stated generators — the `.0` column of `psi_assoc`: `[U_1..U_q, d, b_1..b_n, p]`.
pub open spec fn k_a_col(mm: ModMachine, n: nat) -> Seq<Word> {
    Seq::new(psi_assoc(mm, n).len(), |i: int| psi_assoc(mm, n)[i].0)
}

/// `A₋` stated generators — the `.1` column of `psi_assoc`: `[U_1..U_q, d, b_1c_1..b_nc_n, p]`.
pub open spec fn k_b_col(mm: ModMachine, n: nat) -> Seq<Word> {
    Seq::new(psi_assoc(mm, n).len(), |i: int| psi_assoc(mm, n)[i].1)
}

// ============================================================================
// CS-5b — the BACKWARD direction (c-killing endomorphism via `s_strip`)
// ============================================================================

/// **`s_strip` carries each `b_col` entry to the matching `a_col` entry.** For U/d/p entries the
/// `.1` column equals the c-free `.0` column and `s_strip` fixes it; for the `b_j c_j` entries
/// `s_strip([b_j, c_j]) = [b_j]·ε = [b_j]`.
proof fn lemma_s_strip_psi_entry(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, i: int,
)
    requires
        0 <= i < psi_assoc(mm, n).len(),
    ensures
        apply_hom_pred(s_strip(mm, n, m, is_S), psi_assoc(mm, n)[i].1) =~= psi_assoc(mm, n)[i].0,
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                  // nk = 4 + |quads|
    assert(c_base(nk) == nk);
    let h = s_strip(mm, n, m, is_S);
    let ng = h2_num_gens(nk, n);
    let up = psi_ublock(mm);
    let dpair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))])];
    let bc = psi_bcblock(nk, n);
    let ppair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))])];
    let nu = g_subgens(mm).len();
    assert(up.len() == nu);
    assert(bc.len() == n);
    assert(psi_assoc(mm, n) =~= ((up + dpair) + bc) + ppair);

    if i < nu {
        // U block — psi[i] = (g_subgens[i], g_subgens[i]), a c-free machine word.
        assert(((up + dpair) + bc)[i] == (up + dpair)[i]);
        assert((up + dpair)[i] == up[i]);
        assert(up[i] == (g_subgens(mm)[i], g_subgens(mm)[i]));
        let u = g_subgens(mm)[i];
        lemma_g_m_associations_valid(mm);
        assert(u == g_m_associations(mm)[i].1);
        assert(word_valid(u, (3 + mm.quads.len()) as nat));
        lemma_word_valid_mono(u, (3 + mm.quads.len()) as nat, ng);
        assert(no_c_word(nk, n, u)) by {
            assert forall|t: int| 0 <= t < u.len() implies !c_symbol(nk, n, #[trigger] u[t]) by {
                assert(symbol_valid(u[t], (3 + mm.quads.len()) as nat));
                assert(generator_index(u[t]) < (3 + mm.quads.len()) as nat);
            }
        }
        lemma_strip_fixes_noc_word(mm, n, m, is_S, u);
    } else if i == nu {
        // d entry — single non-c gen, fixed.
        assert(((up + dpair) + bc)[i] == (up + dpair)[i]);
        assert((up + dpair)[i] == dpair[i - nu]);
        let dw: Word = seq![Symbol::Gen(d_idx(nk, n))];
        assert(psi_assoc(mm, n)[i] == (dw, dw));
        assert(word_valid(dw, ng)) by { assert(d_idx(nk, n) < ng); }
        assert(no_c_word(nk, n, dw)) by {
            assert(!c_symbol(nk, n, dw[0])) by { assert(generator_index(dw[0]) == d_idx(nk, n)); }
        }
        lemma_strip_fixes_noc_word(mm, n, m, is_S, dw);
    } else if i < nu + 1 + n {
        // bc block — psi[i] = ([b_j], [b_j, c_j]), j = i - nu.
        assert(((up + dpair) + bc)[i] == bc[i - (nu + 1)]);
        let j = (i - nu) as nat;                   // 1 ≤ j ≤ n
        assert(i - (nu + 1) == (j - 1) as int);
        let bj = Symbol::Gen(crate::layout::b_idx(nk, n, j));
        let cj = Symbol::Gen(crate::layout::c_idx(nk, j));
        assert(bc[(j - 1) as int] == (seq![bj], seq![bj, cj]));
        assert(psi_assoc(mm, n)[i].1 == seq![bj, cj]);
        assert(psi_assoc(mm, n)[i].0 == seq![bj]);
        // apply_hom_pred(h, [bj, cj]) = s_strip_sym(bj) · apply_hom_pred(h, [cj]) = [bj] · ε.
        let bcw: Word = seq![bj, cj];
        assert(bcw.len() == 2);
        assert(bcw.first() == bj);
        let tail = bcw.drop_first();
        assert(tail =~= Seq::new(1, |_i: int| cj)) by {
            assert(tail.len() == 1);
            assert(tail[0] == cj) by { assert(bcw[1] == cj); }
        }
        // bj is non-c (b-block), valid; cj is c.
        assert(!c_symbol(nk, n, bj)) by {
            assert(generator_index(bj) == crate::layout::b_idx(nk, n, j));
            assert(crate::layout::b_idx(nk, n, j) == nk + n + (j - 1));   // ≥ c_base+n
        }
        assert(symbol_valid(bj, ng)) by {
            assert(crate::layout::b_idx(nk, n, j) == nk + n + (j - 1));
        }
        lemma_strip_symbol_noc(mm, n, m, is_S, bj);   // s_strip_sym(bj) =~= [bj]
        assert(c_symbol(nk, n, cj)) by {
            assert(generator_index(cj) == crate::layout::c_idx(nk, j));
            assert(crate::layout::c_idx(nk, j) == nk + (j - 1));          // ∈ [c_base, c_base+n)
        }
        lemma_strip_symbol_c(mm, n, m, is_S, cj);     // s_strip_sym(cj) =~= ε
        lemma_hom_pred_singleton(h, cj);              // apply_hom_pred(h, Seq::new(1,|_|cj)) = s_strip_sym(cj)
        assert(apply_hom_pred(h, tail) =~= empty_word());   // tail =~= Seq::new(1,|_|cj)
        // apply_hom_pred(h, bcw) = concat(s_strip_sym(bj), apply_hom_pred(h, tail)) = [bj]·ε = [bj].
        assert(apply_hom_pred(h, bcw)
            =~= concat(apply_hom_symbol_pred(h, bcw.first()), apply_hom_pred(h, tail)));
        assert(apply_hom_symbol_pred(h, bj) =~= seq![bj]);
        assert(concat(seq![bj], empty_word()) =~= seq![bj]);
    } else {
        // p entry — single non-c gen, fixed.  i == nu + 1 + n.
        assert(i == ((up + dpair) + bc).len());
        let pw: Word = seq![Symbol::Gen(p_idx(nk, n))];
        assert(psi_assoc(mm, n)[i] == ppair[0]);
        assert(ppair[0] == (pw, pw));
        assert(word_valid(pw, ng)) by { assert(p_idx(nk, n) < ng); }
        assert(no_c_word(nk, n, pw)) by {
            assert(!c_symbol(nk, n, pw[0])) by { assert(generator_index(pw[0]) == p_idx(nk, n)); }
        }
        lemma_strip_fixes_noc_word(mm, n, m, is_S, pw);
    }
}

/// `s_strip`-images of `k_b_col` are exactly `k_a_col`.
proof fn lemma_comp_b_col_is_a_col(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    ensures
        comp_images_pred(s_strip(mm, n, m, is_S), k_b_col(mm, n)) =~= k_a_col(mm, n),
{
    let h = s_strip(mm, n, m, is_S);
    let comp = comp_images_pred(h, k_b_col(mm, n));
    assert(comp.len() == k_a_col(mm, n).len());
    assert forall|i: int| 0 <= i < comp.len()
        implies comp[i] =~= k_a_col(mm, n)[i] by {
        assert(comp[i] == apply_hom_pred(h, k_b_col(mm, n)[i]));
        assert(k_b_col(mm, n)[i] == psi_assoc(mm, n)[i].1);
        lemma_s_strip_psi_entry(mm, n, m, is_S, i);
        assert(k_a_col(mm, n)[i] == psi_assoc(mm, n)[i].0);
    }
}

/// **CS-5b — the BACKWARD half of `(★k)`.** `emb(b_col, w) ≡_{h2_pred} ε ⟹ emb(a_col, w) ≡_{h2_pred}
/// ε`. The c-killing endomorphism (Cohen §1b inverse): `s_strip(emb(b_col,w)) = emb(a_col,w)`, then
/// lift the resulting `≡_{h2_noS_pred}` to `≡_{h2_pred}` by relator monotonicity.
pub proof fn lemma_cs5_backward(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        word_valid(w, psi_assoc(mm, n).len()),
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(k_b_col(mm, n), w), empty_word()),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(k_a_col(mm, n), w), empty_word()),
{
    let nk = g_m(mm).num_generators;
    let h = s_strip(mm, n, m, is_S);
    let bw = apply_embedding(k_b_col(mm, n), w);
    let aw = apply_embedding(k_a_col(mm, n), w);

    lemma_s_strip_valid(mm, n, m, is_S);                       // is_valid_pred_homomorphism(h)
    assert(h.source == h2_pred(mm, n, m, is_S));
    assert(h.target == h2_noS_pred(mm, n, m));

    // s_strip(emb(b_col,w)) = emb(comp, w) = emb(a_col, w).
    assert(k_b_col(mm, n).len() == psi_assoc(mm, n).len());
    assert(word_valid(w, k_b_col(mm, n).len()));
    lemma_apply_hom_pred_embedding_compose(h, k_b_col(mm, n), w);
    lemma_comp_b_col_is_a_col(mm, n, m, is_S);
    assert(apply_hom_pred(h, bw) =~= aw);

    // push the b_col-triviality through s_strip: emb(a_col,w) ≡_{h2_noS_pred} ε.
    lemma_hom_pred_preserves_equiv(h, bw, empty_word());
    lemma_hom_pred_empty(h);                                   // apply_hom_pred(h, ε) = ε
    assert(equiv_in_pred_presentation(h2_noS_pred(mm, n, m), aw, empty_word()));

    // lift to h2_pred: h2_noS relators ⊆ h2_pred relators.
    let p1 = h2_noS_pred(mm, n, m);
    let p2 = h2_pred(mm, n, m, is_S);
    assert(p1.num_generators == p2.num_generators);
    assert forall|u: Word| #[trigger] (p1.relators)(u) implies (p2.relators)(u) by {
        assert((p1.relators)(u) == h2_noS_pred_relator(mm, n, m, u));
        assert((p2.relators)(u) == crate::cohen_h2::h2_pred_relator(mm, n, m, is_S, u));
        // h2_noS = K_M ∨ comm ∨ family_ii ⟹ h2_pred = K_M ∨ comm ∨ is_S ∨ family_ii.
    }
    lemma_pred_equiv_relator_mono(p1, p2, aw, empty_word());
}

// ============================================================================
// CS-5c (von-Dyck kernel) — a finite→pred equivalence lift, and the bc-von-Dyck
// word identity (the EASY half of the forward; the hard recognition is the next brick).
// ============================================================================

/// Convert one finite derivation step to a predicate step carrying the relator WORD.
pub open spec fn pred_step_of_finite(fp: Presentation, step: DerivationStep) -> PredDerivationStep {
    match step {
        DerivationStep::FreeReduce { position } => PredDerivationStep::FreeReduce { position },
        DerivationStep::FreeExpand { position, symbol } =>
            PredDerivationStep::FreeExpand { position, symbol },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            PredDerivationStep::RelatorInsert {
                position, relator: fp.relators[relator_index as int], inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            PredDerivationStep::RelatorDelete {
                position, relator: fp.relators[relator_index as int], inverted },
    }
}

/// The step-by-step conversion of a finite derivation.
pub open spec fn conv_steps(fp: Presentation, steps: Seq<DerivationStep>) -> Seq<PredDerivationStep> {
    Seq::new(steps.len(), |i: int| pred_step_of_finite(fp, steps[i]))
}

/// A successful finite step replays as the converted predicate step (same result), when `pp` has at
/// least as many generators and accepts every `fp` relator.
proof fn lemma_apply_step_from_finite(
    fp: Presentation, pp: PredPresentation, w: Word, step: DerivationStep,
)
    requires
        fp.num_generators <= pp.num_generators,
        forall|i: int| 0 <= i < fp.relators.len() ==> (pp.relators)(#[trigger] fp.relators[i]),
        apply_step(fp, w, step) is Some,
    ensures
        apply_step_pred(pp, w, pred_step_of_finite(fp, step)) == apply_step(fp, w, step),
{
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {
            assert(symbol_valid(symbol, fp.num_generators));
            assert(symbol_valid(symbol, pp.num_generators)) by {
                assert(generator_index(symbol) < fp.num_generators);
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < fp.relators.len());
            assert((pp.relators)(fp.relators[relator_index as int]));
            assert(get_relator_pred(fp.relators[relator_index as int], inverted)
                == get_relator(fp, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < fp.relators.len());
            assert((pp.relators)(fp.relators[relator_index as int]));
            assert(get_relator_pred(fp.relators[relator_index as int], inverted)
                == get_relator(fp, relator_index, inverted));
        },
    }
}

/// A finite derivation replays as its converted predicate derivation.
proof fn lemma_pred_produces_from_finite(
    fp: Presentation, pp: PredPresentation, steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        fp.num_generators <= pp.num_generators,
        forall|i: int| 0 <= i < fp.relators.len() ==> (pp.relators)(#[trigger] fp.relators[i]),
        derivation_produces(fp, steps, start) == Some(end),
    ensures
        pred_derivation_produces(pp, conv_steps(fp, steps), start) == Some(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(conv_steps(fp, steps) =~= Seq::<PredDerivationStep>::empty());
    } else {
        let step = steps.first();
        let next = apply_step(fp, start, step).unwrap();
        assert(apply_step(fp, start, step) == Some(next));
        lemma_apply_step_from_finite(fp, pp, start, step);
        let cs = conv_steps(fp, steps);
        assert(cs.first() == pred_step_of_finite(fp, step)) by { assert(steps[0] == step); }
        assert(cs.drop_first() =~= conv_steps(fp, steps.drop_first())) by {
            assert forall|k: int| 0 <= k < cs.drop_first().len()
                implies cs.drop_first()[k] == conv_steps(fp, steps.drop_first())[k] by {
                assert(cs.drop_first()[k] == cs[k + 1]);
                assert(steps.drop_first()[k] == steps[k + 1]);
            }
        }
        assert(apply_step_pred(pp, start, cs.first()) == Some(next));
        lemma_pred_produces_from_finite(fp, pp, steps.drop_first(), next, end);
    }
}

/// **Finite→pred equivalence lift.** If `pp` accepts every relator of the finite `fp` (and has at
/// least as many generators), an `fp`-equivalence lifts to a `pp`-equivalence. Used to bring
/// Layer-1 / soundness facts (proven over finite `h1_base` etc.) up to the predicate base `h2_pred`.
pub proof fn lemma_pred_equiv_from_finite(
    fp: Presentation, pp: PredPresentation, w1: Word, w2: Word,
)
    requires
        fp.num_generators <= pp.num_generators,
        forall|i: int| 0 <= i < fp.relators.len() ==> (pp.relators)(#[trigger] fp.relators[i]),
        equiv_in_presentation(fp, w1, w2),
    ensures
        equiv_in_pred_presentation(pp, w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(fp, d, w1, w2);
    lemma_pred_produces_from_finite(fp, pp, d.steps, w1, w2);
    let pd = PredDerivation { steps: conv_steps(fp, d.steps) };
    assert(pred_derivation_valid(pp, pd, w1, w2));
}

/// `h2_pred` accepts every `h1_base` relator (K_M ∨ comm), and has one more generator (`p`) —
/// so any `h1_base`-equivalence lifts to `h2_pred`.
proof fn lemma_h1_base_lifts_to_h2_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(h1_base(mm, n), w1, w2),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), w1, w2),
{
    let nk = g_m(mm).num_generators;
    let fp = h1_base(mm, n);
    let pp = h2_pred(mm, n, m, is_S);
    lemma_g_m_num_generators(mm);
    assert(fp.num_generators == h1_num_gens(nk, n));
    assert(pp.num_generators == h2_num_gens(nk, n));
    assert(fp.num_generators <= pp.num_generators);   // nk+2n+1 ≤ nk+2n+2
    assert(fp.relators == g_m(mm).relators + comm_relators(nk, n));
    assert forall|i: int| 0 <= i < fp.relators.len()
        implies (pp.relators)(#[trigger] fp.relators[i]) by {
        let r = fp.relators[i];
        assert((pp.relators)(r) == h2_pred_relator(mm, n, m, is_S, r));
        if i < g_m(mm).relators.len() {
            assert(r == g_m(mm).relators[i]);
            assert(g_m(mm).relators.contains(r));   // witness i
        } else {
            let j = i - g_m(mm).relators.len();
            assert(r == comm_relators(nk, n)[j]);
            assert(comm_relators(nk, n).contains(r));   // witness j
        }
    }
    lemma_pred_equiv_from_finite(fp, pp, w1, w2);
}

/// **`w_α(c) ≡_{h2_pred} ε`** for `(α,0)∈H₀` (via the realization hypothesis): `s_realizes` puts
/// `w_α(c)` into `S`, hence it is an `h2_pred` relator, hence `≡ ε`.
pub proof fn lemma_cs5_wc_trivial(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, alpha: nat,
)
    requires
        s_realizes(is_S, mm, n, m),
        numbers_word(n, m, alpha),
        mm_in_H0(mm, alpha, 0),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            w_c(c_base(g_m(mm).num_generators), n, m, alpha), empty_word()),
{
    let nk = g_m(mm).num_generators;
    let wc = w_c(c_base(nk), n, m, alpha);
    assert(is_S(wc));                                  // s_realizes at alpha (trigger is_S(w_c(..)))
    assert((h2_pred(mm, n, m, is_S).relators)(wc)) by {
        assert((h2_pred(mm, n, m, is_S).relators)(wc) == h2_pred_relator(mm, n, m, is_S, wc));
    }
    lemma_pred_relator_is_identity(h2_pred(mm, n, m, is_S), wc);
}

/// **`w_α(bc) ≡_{h2_pred} w_α(b)·w_α(c)`** — the soundness split (`lemma_w_bc_split`, over `h1_base`)
/// lifted to the predicate base.
pub proof fn lemma_cs5_wbc_split_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, alpha: nat,
)
    requires
        numbers_word(n, m, alpha),
        2 * n < m,
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            w_bc(b_base(g_m(mm).num_generators, n), c_base(g_m(mm).num_generators), n, m, alpha),
            w_b(b_base(g_m(mm).num_generators, n), n, m, alpha)
                + w_c(c_base(g_m(mm).num_generators), n, m, alpha)),
{
    lemma_w_bc_split(mm, n, m, alpha);
    lemma_h1_base_lifts_to_h2_pred(mm, n, m, is_S,
        w_bc(b_base(g_m(mm).num_generators, n), c_base(g_m(mm).num_generators), n, m, alpha),
        w_b(b_base(g_m(mm).num_generators, n), n, m, alpha)
            + w_c(c_base(g_m(mm).num_generators), n, m, alpha));
}

/// **Generic right-cancel.** `a·b⁻¹ ≡ ε ⟹ a ≡ b` (in any valid predicate presentation, for valid
/// words). Bridges a relator `≡ ε` to the equality of its two halves.
pub proof fn lemma_pred_cancel_inverse_right(p: PredPresentation, a: Word, b: Word)
    requires
        equiv_in_pred_presentation(p, concat(a, inverse_word(b)), empty_word()),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        pred_presentation_valid(p),
    ensures
        equiv_in_pred_presentation(p, a, b),
{
    let xx = concat(concat(a, inverse_word(b)), b);
    // xx ≡ concat(ε, b) = b.
    lemma_pred_equiv_concat_left(p, concat(a, inverse_word(b)), empty_word(), b);
    assert(concat(empty_word(), b) =~= b);
    // xx = concat(a, concat(b⁻¹, b))  [assoc];  b⁻¹·b ≡ ε ⟹ xx ≡ a·ε = a.
    lemma_concat_assoc(a, inverse_word(b), b);
    lemma_pred_word_inverse_left(p, b);
    lemma_pred_equiv_concat_right(p, a, concat(inverse_word(b), b), empty_word());
    assert(concat(a, empty_word()) =~= a);
    // flip xx ≡ a → a ≡ xx (needs word_valid(xx)), then transitive a ≡ xx ≡ b.
    lemma_inverse_word_valid(b, p.num_generators);
    lemma_concat_word_valid(a, inverse_word(b), p.num_generators);
    lemma_concat_word_valid(concat(a, inverse_word(b)), b, p.num_generators);
    lemma_pred_equiv_symmetric(p, xx, a);
    lemma_pred_equiv_transitive(p, a, xx, b);
}

/// `w_α(bc)` is a valid word over `ng ≥ max(b_base,c_base)+n` (recursive, mirror of `lemma_w_c_valid`;
/// each `bc_letter(d)` is a ≤2-symbol word with indices in the `b`/`c` blocks).
proof fn lemma_w_bc_valid(b_base: nat, c_base: nat, n: nat, m: nat, alpha: nat, ng: nat)
    requires
        numbers_word(n, m, alpha),
        b_base + n <= ng,
        c_base + n <= ng,
        2 * n < m,
    ensures
        word_valid(w_bc(b_base, c_base, n, m, alpha), ng),
    decreases alpha,
{
    if alpha == 0 || m <= 1 {
        assert(w_bc(b_base, c_base, n, m, alpha) =~= empty_word());
    } else {
        let d = alpha % m;                                   // 1 ≤ d ≤ 2n
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
        lemma_w_bc_valid(b_base, c_base, n, m, alpha / m, ng);
        let pref = w_bc(b_base, c_base, n, m, alpha / m);
        let last = bc_letter(b_base, c_base, n, d);
        assert(w_bc(b_base, c_base, n, m, alpha) =~= pref + last);
        assert(word_valid(last, ng)) by {
            assert forall|k: int| 0 <= k < last.len()
                implies symbol_valid(#[trigger] last[k], ng) by {
                // d ∈ [1, 2n]: both letters land in the b/c blocks, indices < base+n ≤ ng.
            }
        }
        assert forall|k: int| #![trigger (pref + last)[k]] 0 <= k < (pref + last).len()
            implies symbol_valid((pref + last)[k], ng) by {
            if k < pref.len() { assert((pref + last)[k] == pref[k]); }
            else { assert((pref + last)[k] == last[k - pref.len()]); }
        }
    }
}

/// The `b_col`-image of the A₊ p-relation `R_α`, in config-form: `t_α w_α(bc) d` (vs the family-(II)
/// rhs `t_α w_α(b) d`). The bc-von-Dyck atom shows the corresponding relator `≡ ε`.
pub open spec fn family_II_bc_rhs(mm: ModMachine, n: nat, m: nat, alpha: nat) -> Word {
    let nk = g_m(mm).num_generators;
    config_word(alpha, 0) + w_bc(b_base(nk, n), c_base(nk), n, m, alpha)
        + seq![Symbol::Gen(d_idx(nk, n))]
}

/// **CS-5c bc-von-Dyck atom (config form).** For `(α,0)∈H₀` and `numbers_word(α)`, the bc-version of
/// the family-(II) relator `p⁻¹ t_α p · (t_α w_α(bc) d)⁻¹ ≡_{h2_pred} ε`. This is the image of the A₊
/// p-relation `R_α` under `b_col` (`b_j ↦ b_j c_j`), the well-definedness obligation of the von-Dyck
/// forward: `w_α(bc) = w_α(b) w_α(c)` and `w_α(c) ≡ ε` collapse it to the family-(II) relator (CS-4a).
pub proof fn lemma_cs5_bc_config_trivial(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, alpha: nat,
)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        s_realizes(is_S, mm, n, m),
        numbers_word(n, m, alpha),
        mm_in_H0(mm, alpha, 0),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            family_II_lhs(mm, n, alpha) + inverse_word(family_II_bc_rhs(mm, n, m, alpha)),
            empty_word()),
{
    let nk = g_m(mm).num_generators;
    let p2 = h2_pred(mm, n, m, is_S);
    let lhs = family_II_lhs(mm, n, alpha);
    let rhs = family_II_rhs(mm, n, m, alpha);
    let bcrhs = family_II_bc_rhs(mm, n, m, alpha);
    let config = config_word(alpha, 0);
    let wb = w_b(b_base(nk, n), n, m, alpha);
    let wc = w_c(c_base(nk), n, m, alpha);
    let wbc = w_bc(b_base(nk, n), c_base(nk), n, m, alpha);
    let dw: Word = seq![Symbol::Gen(d_idx(nk, n))];
    assert(rhs == config + wb + dw);
    assert(bcrhs == config + wbc + dw);

    // --- Step A: lhs ≡ rhs, from family_II_relator(α) = lhs·rhs⁻¹ ≡ ε (CS-4a). ---
    lemma_family_II_relator_in_h2_pred(mm, n, m, is_S, alpha);
    assert(family_II_relator(mm, n, m, alpha) == concat(lhs, inverse_word(rhs)));
    lemma_h2_pred_valid(mm, n, m, is_S);
    lemma_g_m_num_generators(mm);
    lemma_family_II_relator_valid(mm, n, m, alpha, h2_num_gens(nk, n));   // word_valid(lhs), (rhs)
    assert(p2.num_generators == h2_num_gens(nk, n));
    lemma_pred_cancel_inverse_right(p2, lhs, rhs);          // lhs ≡ rhs

    // --- Step B: rhs ≡ bcrhs, from wbc ≡ wb (split + wc≡ε). ---
    lemma_cs5_wbc_split_pred(mm, n, m, is_S, alpha);          // wbc ≡ wb·wc
    lemma_cs5_wc_trivial(mm, n, m, is_S, alpha);             // wc ≡ ε
    lemma_pred_equiv_concat_right(p2, wb, wc, empty_word());  // wb·wc ≡ wb·ε
    assert(concat(wb, empty_word()) =~= wb);
    lemma_pred_equiv_transitive(p2, wbc, concat(wb, wc), wb); // wbc ≡ wb
    // config·wbc ≡ config·wb, then ·dw.
    lemma_pred_equiv_concat_right(p2, config, wbc, wb);
    lemma_pred_equiv_concat_left(p2, concat(config, wbc), concat(config, wb), dw);
    assert(bcrhs == concat(concat(config, wbc), dw));
    assert(rhs == concat(concat(config, wb), dw));
    // bcrhs ≡ rhs.

    // --- Step C: lhs ≡ rhs ≡ bcrhs, then lhs·bcrhs⁻¹ ≡ bcrhs·bcrhs⁻¹ ≡ ε. ---
    // word_valid(bcrhs) for the symmetric flip: config (over 3) + w_bc + [d], all < h2_num_gens.
    lemma_config_word_valid(alpha, 0);
    lemma_word_valid_mono(config, 3, h2_num_gens(nk, n));
    lemma_w_bc_valid(b_base(nk, n), c_base(nk), n, m, alpha, h2_num_gens(nk, n));
    assert(word_valid(dw, h2_num_gens(nk, n))) by { assert(d_idx(nk, n) < h2_num_gens(nk, n)); }
    lemma_concat_word_valid(config, wbc, h2_num_gens(nk, n));
    lemma_concat_word_valid(concat(config, wbc), dw, h2_num_gens(nk, n));
    assert(word_valid(bcrhs, h2_num_gens(nk, n)));
    lemma_pred_equiv_symmetric(p2, bcrhs, rhs);
    lemma_pred_equiv_transitive(p2, lhs, rhs, bcrhs);        // lhs ≡ bcrhs
    lemma_pred_equiv_concat_left(p2, lhs, bcrhs, inverse_word(bcrhs));
    lemma_pred_word_inverse_right(p2, bcrhs);                // bcrhs·bcrhs⁻¹ ≡ ε
    lemma_pred_equiv_transitive(p2, concat(lhs, inverse_word(bcrhs)),
        concat(bcrhs, inverse_word(bcrhs)), empty_word());
    assert(lhs + inverse_word(bcrhs) == concat(lhs, inverse_word(bcrhs)));
}

// ============================================================================
// CS-5c (recognition OPENING) — `emb(a_col, w)` is c-free, so the forward triviality
// over the infinite `h2_pred` reduces to a finite slice (the compactness bridge).
// The HARD recognition core (the Britton-peel of `p` with property-(vii) at the pinch
// middle, blueprint §4) consumes this finite-slice triviality.
// ============================================================================

/// Each `a_col` (= `psi_assoc.0`) entry is a c-free word: U entries are machine words (index `< nk =
/// c_base`); `d`, `b_j`, `p` are single gens at index `≥ c_base + n`.
proof fn lemma_k_a_col_entry_no_c(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < psi_assoc(mm, n).len(),
    ensures
        no_c_word(g_m(mm).num_generators, n, k_a_col(mm, n)[i]),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    assert(c_base(nk) == nk);
    let up = psi_ublock(mm);
    let dpair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))])];
    let bc = psi_bcblock(nk, n);
    let ppair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))])];
    let nu = g_subgens(mm).len();
    assert(up.len() == nu);
    assert(bc.len() == n);
    assert(psi_assoc(mm, n) =~= ((up + dpair) + bc) + ppair);
    assert(k_a_col(mm, n)[i] == psi_assoc(mm, n)[i].0);

    if i < nu {
        assert(((up + dpair) + bc)[i] == (up + dpair)[i]);
        assert((up + dpair)[i] == up[i]);
        assert(up[i] == (g_subgens(mm)[i], g_subgens(mm)[i]));
        let u = g_subgens(mm)[i];
        lemma_g_m_associations_valid(mm);
        assert(u == g_m_associations(mm)[i].1);
        assert(word_valid(u, (3 + mm.quads.len()) as nat));
        assert(no_c_word(nk, n, u)) by {
            assert forall|t: int| 0 <= t < u.len() implies !c_symbol(nk, n, #[trigger] u[t]) by {
                assert(symbol_valid(u[t], (3 + mm.quads.len()) as nat));
                assert(generator_index(u[t]) < (3 + mm.quads.len()) as nat);   // < nk = c_base
            }
        }
    } else if i == nu {
        assert(((up + dpair) + bc)[i] == (up + dpair)[i]);
        assert((up + dpair)[i] == dpair[i - nu]);
        let dw: Word = seq![Symbol::Gen(d_idx(nk, n))];
        assert(k_a_col(mm, n)[i] == dw);
        assert(no_c_word(nk, n, dw)) by {
            assert(!c_symbol(nk, n, dw[0])) by { assert(generator_index(dw[0]) == d_idx(nk, n)); }
        }
    } else if i < nu + 1 + n {
        assert(((up + dpair) + bc)[i] == bc[i - (nu + 1)]);
        let j = (i - nu) as nat;
        assert(i - (nu + 1) == (j - 1) as int);
        let bj = Symbol::Gen(crate::layout::b_idx(nk, n, j));
        let cj = Symbol::Gen(crate::layout::c_idx(nk, j));
        assert(bc[(j - 1) as int] == (seq![bj], seq![bj, cj]));
        assert(k_a_col(mm, n)[i] == seq![bj]);
        assert(no_c_word(nk, n, seq![bj])) by {
            assert(!c_symbol(nk, n, bj)) by {
                assert(generator_index(bj) == crate::layout::b_idx(nk, n, j));
                assert(crate::layout::b_idx(nk, n, j) == nk + n + (j - 1));   // ≥ c_base + n
            }
        }
    } else {
        assert(i == ((up + dpair) + bc).len());
        let pw: Word = seq![Symbol::Gen(p_idx(nk, n))];
        assert(psi_assoc(mm, n)[i] == ppair[0]);
        assert(k_a_col(mm, n)[i] == pw);
        assert(no_c_word(nk, n, pw)) by {
            assert(!c_symbol(nk, n, pw[0])) by { assert(generator_index(pw[0]) == p_idx(nk, n)); }
        }
    }
}

/// `emb(a_col, w)` is c-free (each image entry is c-free; inversion/concatenation preserve it).
/// Mirror of CS-4c's `lemma_emb_a_words_no_c`.
proof fn lemma_emb_k_a_col_no_c(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, psi_assoc(mm, n).len()),
    ensures
        no_c_word(g_m(mm).num_generators, n, apply_embedding(k_a_col(mm, n), w)),
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let ac = k_a_col(mm, n);
    assert(ac.len() == psi_assoc(mm, n).len());
    if w.len() == 0 {
        assert(apply_embedding(ac, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let g = generator_index(s);
        assert(symbol_valid(s, ac.len())) by { assert(w[0] == s); }
        assert(g < ac.len());
        lemma_k_a_col_entry_no_c(mm, n, g as int);             // no_c_word(nk, n, ac[g])
        assert(no_c_word(nk, n, apply_embedding_symbol(ac, s))) by {
            match s {
                Symbol::Gen(gg) => { assert(apply_embedding_symbol(ac, s) == ac[gg as int]); },
                Symbol::Inv(gg) => {
                    assert(apply_embedding_symbol(ac, s) == inverse_word(ac[gg as int]));
                    lemma_no_c_inverse(nk, n, ac[gg as int]);
                },
            }
        }
        assert(word_valid(rest, ac.len())) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(#[trigger] rest[k], ac.len()) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_emb_k_a_col_no_c(mm, n, rest);
        assert(apply_embedding(ac, w)
            =~= concat(apply_embedding_symbol(ac, s), apply_embedding(ac, rest)));
        lemma_no_c_concat(nk, n, apply_embedding_symbol(ac, s), apply_embedding(ac, rest));
    }
}

/// **CS-5c recognition opening.** A forward triviality `emb(a_col, w) ≡_{h2_pred} ε` reduces to a
/// finite slice: `emb(a_col, w)` is c-free, so the compactness bridge (CS-4b) gives a number-word
/// slice `alphas` with `emb(a_col, w) ≡_{h2_II(alphas)} ε`. The next brick (the recognition core,
/// blueprint §4) peels `p` over this finite slice with property-(vii) at the pinch middle.
pub proof fn lemma_cs5_recog_compactness(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        word_valid(w, psi_assoc(mm, n).len()),
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(k_a_col(mm, n), w), empty_word()),
    ensures
        exists|alphas: Seq<nat>|
            (forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(h2_II(mm, n, m, alphas),
                apply_embedding(k_a_col(mm, n), w), empty_word()),
{
    let nk = g_m(mm).num_generators;
    let ac = k_a_col(mm, n);
    let u = apply_embedding(ac, w);
    lemma_g_m_num_generators(mm);
    // u is c-free.
    lemma_emb_k_a_col_no_c(mm, n, w);
    // u is valid over h2_num_gens (each a_col entry is valid; w valid over ac.len()).
    lemma_psi_assoc_valid(mm, n, h2_num_gens(nk, n));
    assert(ac.len() == psi_assoc(mm, n).len());
    assert forall|i: int| 0 <= i < ac.len()
        implies word_valid(#[trigger] ac[i], h2_num_gens(nk, n)) by {
        assert(ac[i] == psi_assoc(mm, n)[i].0);
    }
    assert(word_valid(w, ac.len()));
    lemma_apply_embedding_valid(ac, w, h2_num_gens(nk, n));
    // compactness.
    lemma_cs4b_compactness(mm, n, m, is_S, u);
}

} // verus!
