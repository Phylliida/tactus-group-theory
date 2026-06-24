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
use crate::pred_presentation::*;
use crate::pred_homomorphism::{PredHomomorphismData, apply_hom_pred, apply_hom_symbol_pred,
    is_valid_pred_homomorphism, lemma_hom_pred_respects_concat, lemma_hom_pred_respects_inverse,
    lemma_hom_pred_preserves_equiv, lemma_hom_pred_empty, lemma_hom_pred_singleton};
use crate::benign::{apply_embedding, apply_embedding_symbol};
use crate::machine_group::{ModMachine, g_m, g_subgens, g_m_associations, lemma_g_m_num_generators,
    lemma_g_m_associations_valid, lemma_word_valid_mono};
use crate::layout::{h2_num_gens, d_idx, p_idx, c_base};
use crate::h3::{psi_assoc, psi_ublock, psi_bcblock, lemma_psi_assoc_valid};
use crate::cohen_h2::{h2_pred, c_symbol, s_relators_valid};
use crate::cohen_cs4b::{s_strip, h2_noS_pred, h2_noS_pred_relator, lemma_s_strip_valid,
    lemma_strip_fixes_noc_word, lemma_strip_symbol_c, lemma_strip_symbol_noc};
use crate::cohen_retraction::no_c_word;

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

} // verus!
