// Layer 2 — Cohen §1, CS-5c RECOGNITION CORE (Route R1, the single-gen relabel).
//
// `docs/cohen-cs5-blueprint.md` §5. The forward `(★k)` `emb(a_col,w) ≡_{h2_pred} ε ⟹
// emb(b_col,w) ≡_{h2_pred} ε` is recognized over the CONCRETE machine base, NOT an abstract ⟨U⟩
// presentation, because `a_col`'s U-block is a single-generator relabel (`g_subgens(mm)[i] =
// [Gen(0)]`/`[Gen(3+i)]`, a SINGLE machine gen). This module builds the **relabel bridge** (step 1):
//
//   * `base_A_plus_base` = `Presentation{ num_generators: nk+n+1, relators: g_m.relators }`
//     (= `g_m ∗ free(d,b_j)` — g_m's relators only touch gens `0..nk-1`, so gens `nk..nk+n` are free).
//   * `a_col_machine` / `b_col_machine` — the machine-scheme columns (over `nk+n+2` gens incl. `p`),
//     the inclusion `a_col_machine` and the `b_j↦b_j c_j` von-Dyck image `b_col_machine`.
//   * `relabel_col` — the injective single-gen relabel psi-scheme → machine-scheme.
//   * the plain emb∘emb compose (`comp_emb` + `lemma_emb_emb_compose`),
//   * **the factoring** `a_col =~= comp_emb(a_col_machine, relabel_col)`,
//     `b_col =~= comp_emb(b_col_machine, relabel_col)`, giving the bridge identities
//     `emb(a_col,w) = emb(a_col_machine, relabel(w))`, `emb(b_col,w) = emb(b_col_machine, relabel(w))`.
//
// So psi-scheme `(★k)` forward reduces to the machine-scheme recognition (step 3) + von-Dyck (step 4).
// Additive/reversible; no regression.

use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::presentation::{Presentation, presentation_valid, equiv_in_presentation};
use crate::presentation_lemmas::lemma_relator_is_identity;
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat,
    lemma_apply_embedding_inverse};
use crate::homomorphism::{HomomorphismData, apply_hom, apply_hom_symbol, is_valid_homomorphism,
    lemma_hom_preserves_equiv};
use crate::free_basis::{comp_images, lemma_apply_hom_embedding_compose};
use crate::machine_group::{ModMachine, g_m, g_subgens, g_m_associations, config_word, mod_machine_wf,
    mm_in_H0, lemma_g_m_num_generators, lemma_g_m_associations_valid, lemma_g_m_valid,
    lemma_word_valid_mono, lemma_cancel_pair_equiv_empty, lemma_config_word_valid};
use crate::layout::{h1_num_gens, h2_num_gens, c_base, b_base, d_idx, p_idx, b_idx, c_idx};
use crate::h1::{h1_base, comm_relators, comm_relator, lemma_h1_base_valid, lemma_h1_base_num_generators};
use crate::h3::{psi_assoc, psi_ublock, psi_bcblock, lemma_single_gen_valid};
use crate::word_numbering::{w_b, w_c, w_bc, bc_letter, numbers_word, alphabet_letter, lemma_w_c_valid};
use crate::h3_ii::{family_II_rhs, family_II_lhs};
use crate::hnn::{HNNData, hnn_data_valid, hnn_relator, hnn_relators, hnn_presentation,
    stable_letter, stable_letter_inv};
use crate::pred_presentation::{equiv_in_pred_presentation, pred_presentation_valid};
use crate::pred_presentation_lemmas::lemma_pred_relator_is_identity;
use crate::cohen_h2::{h2_pred, h2_pred_relator, s_relators_valid, s_realizes, lemma_h2_pred_valid};
use crate::cohen_cs5::{k_a_col, k_b_col, family_II_bc_rhs, lemma_cs5_bc_config_trivial};

verus! {

// ============================================================================
// Plain embedding compose: `emb(outer, emb(inner, w)) = emb(comp_emb(outer, inner), w)`.
// ============================================================================

/// The composite images `comp_emb(outer, inner)[i] = apply_embedding(outer, inner[i])` — the
/// outer embedding applied to each inner image (plain analog of `free_basis::comp_images`).
pub open spec fn comp_emb(outer: Seq<Word>, inner: Seq<Word>) -> Seq<Word> {
    Seq::new(inner.len(), |i: int| apply_embedding(outer, inner[i]))
}

/// **emb∘emb compose.** Applying `outer` to an `inner`-embedded word equals embedding by the
/// composite. Mirror of `lemma_apply_hom_pred_embedding_compose` with `apply_embedding` outer.
pub proof fn lemma_emb_emb_compose(outer: Seq<Word>, inner: Seq<Word>, w: Word)
    requires
        word_valid(w, inner.len()),
    ensures
        apply_embedding(outer, apply_embedding(inner, w)) =~= apply_embedding(comp_emb(outer, inner), w),
    decreases w.len(),
{
    let comp = comp_emb(outer, inner);
    assert(comp.len() == inner.len());
    if w.len() == 0 {
        assert(apply_embedding(inner, w) =~= empty_word());
        assert(apply_embedding(outer, empty_word()) =~= empty_word());
        assert(apply_embedding(comp, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, inner.len())) by { assert(w[0] == s); }
        assert(word_valid(rest, inner.len())) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(#[trigger] rest[k], inner.len()) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_emb_emb_compose(outer, inner, rest);
        // outer(inner_sym(s)) = comp_sym(s).
        match s {
            Symbol::Gen(i) => {
                assert(i < inner.len());
                assert(apply_embedding_symbol(inner, s) == inner[i as int]);
                assert(comp[i as int] == apply_embedding(outer, inner[i as int]));
                assert(apply_embedding_symbol(comp, s) == comp[i as int]);
            },
            Symbol::Inv(i) => {
                assert(i < inner.len());
                assert(apply_embedding_symbol(inner, s) == inverse_word(inner[i as int]));
                lemma_apply_embedding_inverse(outer, inner[i as int]);
                assert(comp[i as int] == apply_embedding(outer, inner[i as int]));
                assert(apply_embedding_symbol(comp, s) == inverse_word(comp[i as int]));
            },
        }
        // emb(inner, w) = inner_sym(s) · emb(inner, rest); apply outer over the concat.
        assert(apply_embedding(inner, w)
            =~= concat(apply_embedding_symbol(inner, s), apply_embedding(inner, rest)));
        lemma_apply_embedding_concat(outer, apply_embedding_symbol(inner, s),
            apply_embedding(inner, rest));
        assert(apply_embedding(comp, w)
            =~= concat(apply_embedding_symbol(comp, s), apply_embedding(comp, rest)));
    }
}

// ============================================================================
// The machine-scheme objects (step 1 definitions).
// ============================================================================

/// `base_A₊` HNN base `= g_m ∗ free(d, b_j)`: `nk+n+1` gens (machine `0..nk-1`, b's `nk..nk+n-1`,
/// d at `nk+n`), relators = `g_m`'s (which only touch gens `0..nk-1`, so b/d are free).
pub open spec fn base_A_plus_base(mm: ModMachine, n: nat) -> Presentation {
    let nk = g_m(mm).num_generators;
    Presentation { num_generators: (nk + n + 1) as nat, relators: g_m(mm).relators }
}

/// The machine-scheme inclusion column `a_col_machine` (length `nk+n+2`, incl. the HNN letter `p`):
/// machine gen `i ↦ [Gen(i)]`, abstract `b_{j+1} ↦ [Gen(b_idx)]`, `d ↦ [Gen(d_idx)]`, `p ↦ [Gen(p_idx)]`.
pub open spec fn a_col_machine(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    Seq::new(nk, |i: int| seq![Symbol::Gen(i as nat)])
    + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))])
    + seq![ seq![Symbol::Gen(d_idx(nk, n))] ]
    + seq![ seq![Symbol::Gen(p_idx(nk, n))] ]
}

/// The machine-scheme von-Dyck image column `b_col_machine` (= `a_col_machine` with `b_{j+1} ↦
/// [Gen(b_idx), Gen(c_idx)]`).
pub open spec fn b_col_machine(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    Seq::new(nk, |i: int| seq![Symbol::Gen(i as nat)])
    + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)),
                                Symbol::Gen(c_idx(nk, (j + 1) as nat))])
    + seq![ seq![Symbol::Gen(d_idx(nk, n))] ]
    + seq![ seq![Symbol::Gen(p_idx(nk, n))] ]
}

/// The injective single-gen relabel, psi-scheme → machine-scheme (length `q+n+2 = psi_assoc.len()`):
/// U-gen `i ↦ g_subgens[i]` (a SINGLE machine gen `[Gen(gi)]`, `gi<nk`), `d ↦ [Gen(nk+n)]`,
/// `b_{j+1} ↦ [Gen(nk+j)]`, `p ↦ [Gen(nk+n+1)]`.
pub open spec fn relabel_col(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    Seq::new(g_subgens(mm).len(), |i: int| g_subgens(mm)[i])
    + seq![ seq![Symbol::Gen((nk + n) as nat)] ]
    + Seq::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)])
    + seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ]
}

/// `relabel(w)` — the machine-scheme word for a psi-scheme `w`.
pub open spec fn relabel(mm: ModMachine, n: nat, w: Word) -> Word {
    apply_embedding(relabel_col(mm, n), w)
}

// ============================================================================
// The factoring (step 1) — `a_col = comp_emb(a_col_machine, relabel_col)` entry-wise.
// ============================================================================

/// `a_col_machine` / `b_col_machine` have length `nk+n+2`; `relabel_col` entries are valid over it.
proof fn lemma_machine_col_len(mm: ModMachine, n: nat)
    ensures
        a_col_machine(mm, n).len() == g_m(mm).num_generators + n + 2,
        b_col_machine(mm, n).len() == g_m(mm).num_generators + n + 2,
        relabel_col(mm, n).len() == psi_assoc(mm, n).len(),
        relabel_col(mm, n).len() == g_subgens(mm).len() + n + 2,
{
    let nk = g_m(mm).num_generators;
    assert(a_col_machine(mm, n).len() == nk + n + 2);
    assert(b_col_machine(mm, n).len() == nk + n + 2);
    assert(relabel_col(mm, n).len() == g_subgens(mm).len() + n + 2);
    assert(psi_assoc(mm, n).len() == g_subgens(mm).len() + n + 2) by {
        assert(psi_ublock(mm).len() == g_subgens(mm).len());
        assert(psi_bcblock(nk, n).len() == n);
    }
}

/// **The a-factoring, entry-wise.** `comp_emb(a_col_machine, relabel_col)[i] = k_a_col[i]` for each
/// psi-index `i`: U-block `apply_embedding(a_col_machine, g_subgens[i]) = a_col_machine[gi] =
/// [Gen(gi)] = g_subgens[i]`; d/b/p blocks pick the single machine-scheme image.
proof fn lemma_a_factor_entry(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < psi_assoc(mm, n).len(),
    ensures
        apply_embedding(a_col_machine(mm, n), relabel_col(mm, n)[i]) =~= k_a_col(mm, n)[i],
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let am = a_col_machine(mm, n);
    let rc = relabel_col(mm, n);
    let q = g_subgens(mm).len();
    lemma_machine_col_len(mm, n);
    assert(am.len() == nk + n + 2);

    // psi_assoc block decomposition (mirror lemma_s_strip_psi_entry).
    let up = psi_ublock(mm);
    let dpair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))])];
    let bc = psi_bcblock(nk, n);
    let ppair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))])];
    assert(up.len() == q);
    assert(bc.len() == n);
    assert(psi_assoc(mm, n) =~= ((up + dpair) + bc) + ppair);
    assert(k_a_col(mm, n)[i] == psi_assoc(mm, n)[i].0);

    // relabel_col block decomposition.
    let r_d: Seq<Word> = seq![ seq![Symbol::Gen((nk + n) as nat)] ];
    let r_b: Seq<Word> = Seq::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)]);
    let r_p: Seq<Word> = seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ];
    let r_u: Seq<Word> = Seq::new(q, |i2: int| g_subgens(mm)[i2]);
    assert(rc =~= ((r_u + r_d) + r_b) + r_p);

    if i < q {
        // U-block: rc[i] = g_subgens[i] = [Gen(gi)], gi < nk; am[gi] = [Gen(gi)].
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_u[i]);
        assert(r_u[i] == g_subgens(mm)[i]);
        let u = g_subgens(mm)[i];
        lemma_g_m_associations_valid(mm);
        assert(u == g_m_associations(mm)[i].1);
        assert(word_valid(u, (3 + mm.quads.len()) as nat));
        // g_subgens[i] is a single gen [Gen(gi)] with gi < nk.
        assert(u.len() == 1) by { assert(word_valid(u, (3 + mm.quads.len()) as nat)); }
        let gi = generator_index(u[0]);
        assert(symbol_valid(u[0], (3 + mm.quads.len()) as nat));
        assert(gi < 3 + mm.quads.len());
        assert(gi < nk);
        assert(u[0] == Symbol::Gen(gi)) by { assert(symbol_valid(u[0], nk)); }
        assert(u =~= seq![Symbol::Gen(gi)]);
        // apply_embedding(am, [Gen(gi)]) = am[gi] = [Gen(gi)].
        assert(am[gi as int] == seq![Symbol::Gen(gi)]) by {
            assert(((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]))
                + seq![ seq![Symbol::Gen(d_idx(nk, n))] ])[gi as int]
                == Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])[gi as int]);
        }
        lemma_emb_single_gen(am, gi);
        assert(apply_embedding(am, u) =~= am[gi as int]);
        assert(k_a_col(mm, n)[i] == g_subgens(mm)[i]);
    } else if i == q {
        // d: rc[q] = [Gen(nk+n)]; am[nk+n] = [Gen(d_idx)].
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_d[i - q]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + n) as nat)]);
        assert(am[(nk + n) as int] == seq![Symbol::Gen(d_idx(nk, n))]);
        lemma_emb_single_gen(am, (nk + n) as nat);
        assert(psi_assoc(mm, n)[i] == dpair[i - q]);
        assert(k_a_col(mm, n)[i] =~= seq![Symbol::Gen(d_idx(nk, n))]);
    } else if i < q + 1 + n {
        // b-block: rc[i] = [Gen(nk + (i-q-1))]; am[nk+(i-q-1)] = [Gen(b_idx(.., i-q))].
        let j = (i - q - 1) as int;     // 0 ≤ j < n
        assert(((r_u + r_d) + r_b)[i] == r_b[j]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + j) as nat)]);
        assert(am[(nk + j) as int] == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]) by {
            assert((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))]))[(nk + j) as int]
                == Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))])[j]);
        }
        lemma_emb_single_gen(am, (nk + j) as nat);
        // k_a_col[i] = psi_bcblock[i-q-1].0 = [Gen(b_idx(.., j+1))].
        assert(psi_assoc(mm, n)[i] == bc[j]);
        assert(bc[j].0 =~= seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
    } else {
        // p: i == q+1+n; rc[i] = [Gen(nk+n+1)]; am[nk+n+1] = [Gen(p_idx)].
        assert(i == ((r_u + r_d) + r_b).len());
        assert(rc[i] =~= seq![Symbol::Gen((nk + n + 1) as nat)]);
        assert(am[(nk + n + 1) as int] == seq![Symbol::Gen(p_idx(nk, n))]);
        lemma_emb_single_gen(am, (nk + n + 1) as nat);
        assert(psi_assoc(mm, n)[i] == ppair[0]);
        assert(k_a_col(mm, n)[i] =~= seq![Symbol::Gen(p_idx(nk, n))]);
    }
}

/// `apply_embedding(images, [Gen(g)]) = images[g]` (single positive generator).
proof fn lemma_emb_single_gen(images: Seq<Word>, g: nat)
    ensures
        apply_embedding(images, seq![Symbol::Gen(g)]) =~= images[g as int],
{
    let w: Word = seq![Symbol::Gen(g)];
    assert(w.len() == 1);
    assert(w.first() == Symbol::Gen(g));
    assert(w.drop_first() =~= empty_word());
    assert(apply_embedding(images, w.drop_first()) =~= empty_word());
    assert(apply_embedding_symbol(images, w.first()) == images[g as int]);
    assert(apply_embedding(images, w)
        =~= concat(apply_embedding_symbol(images, w.first()), empty_word()));
    lemma_concat_empty_right(images[g as int]);
}

/// **The b-factoring, entry-wise** (mirror of `lemma_a_factor_entry`; the bc-block image is
/// `[Gen(b_idx), Gen(c_idx)]` instead of `[Gen(b_idx)]`; U/d/p identical to the a-side).
proof fn lemma_b_factor_entry(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < psi_assoc(mm, n).len(),
    ensures
        apply_embedding(b_col_machine(mm, n), relabel_col(mm, n)[i]) =~= k_b_col(mm, n)[i],
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bm = b_col_machine(mm, n);
    let rc = relabel_col(mm, n);
    let q = g_subgens(mm).len();
    lemma_machine_col_len(mm, n);
    assert(bm.len() == nk + n + 2);

    let up = psi_ublock(mm);
    let dpair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))])];
    let bc = psi_bcblock(nk, n);
    let ppair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))])];
    assert(up.len() == q);
    assert(bc.len() == n);
    assert(psi_assoc(mm, n) =~= ((up + dpair) + bc) + ppair);
    assert(k_b_col(mm, n)[i] == psi_assoc(mm, n)[i].1);

    let r_d: Seq<Word> = seq![ seq![Symbol::Gen((nk + n) as nat)] ];
    let r_b: Seq<Word> = Seq::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)]);
    let r_p: Seq<Word> = seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ];
    let r_u: Seq<Word> = Seq::new(q, |i2: int| g_subgens(mm)[i2]);
    assert(rc =~= ((r_u + r_d) + r_b) + r_p);

    if i < q {
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_u[i]);
        assert(r_u[i] == g_subgens(mm)[i]);
        let u = g_subgens(mm)[i];
        lemma_g_m_associations_valid(mm);
        assert(u == g_m_associations(mm)[i].1);
        assert(word_valid(u, (3 + mm.quads.len()) as nat));
        assert(u.len() == 1) by { assert(word_valid(u, (3 + mm.quads.len()) as nat)); }
        let gi = generator_index(u[0]);
        assert(symbol_valid(u[0], (3 + mm.quads.len()) as nat));
        assert(gi < 3 + mm.quads.len());
        assert(gi < nk);
        assert(u[0] == Symbol::Gen(gi)) by { assert(symbol_valid(u[0], nk)); }
        assert(u =~= seq![Symbol::Gen(gi)]);
        assert(bm[gi as int] == seq![Symbol::Gen(gi)]) by {
            assert(((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)),
                                            Symbol::Gen(c_idx(nk, (j + 1) as nat))]))
                + seq![ seq![Symbol::Gen(d_idx(nk, n))] ])[gi as int]
                == Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])[gi as int]);
        }
        lemma_emb_single_gen(bm, gi);
        assert(apply_embedding(bm, u) =~= bm[gi as int]);
        assert(k_b_col(mm, n)[i] == g_subgens(mm)[i]);
    } else if i == q {
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_d[i - q]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + n) as nat)]);
        assert(bm[(nk + n) as int] == seq![Symbol::Gen(d_idx(nk, n))]);
        lemma_emb_single_gen(bm, (nk + n) as nat);
        assert(psi_assoc(mm, n)[i] == dpair[i - q]);
        assert(k_b_col(mm, n)[i] =~= seq![Symbol::Gen(d_idx(nk, n))]);
    } else if i < q + 1 + n {
        let j = (i - q - 1) as int;
        assert(((r_u + r_d) + r_b)[i] == r_b[j]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + j) as nat)]);
        assert(bm[(nk + j) as int]
            == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)), Symbol::Gen(c_idx(nk, (j + 1) as nat))])
        by {
            assert((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat)),
                                             Symbol::Gen(c_idx(nk, (jj + 1) as nat))]))[(nk + j) as int]
                == Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat)),
                                              Symbol::Gen(c_idx(nk, (jj + 1) as nat))])[j]);
        }
        lemma_emb_single_gen(bm, (nk + j) as nat);
        assert(psi_assoc(mm, n)[i] == bc[j]);
        assert(bc[j].1 =~= seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)),
                                Symbol::Gen(c_idx(nk, (j + 1) as nat))]);
    } else {
        assert(i == ((r_u + r_d) + r_b).len());
        assert(rc[i] =~= seq![Symbol::Gen((nk + n + 1) as nat)]);
        assert(bm[(nk + n + 1) as int] == seq![Symbol::Gen(p_idx(nk, n))]);
        lemma_emb_single_gen(bm, (nk + n + 1) as nat);
        assert(psi_assoc(mm, n)[i] == ppair[0]);
        assert(k_b_col(mm, n)[i] =~= seq![Symbol::Gen(p_idx(nk, n))]);
    }
}

// ============================================================================
// Full factoring + the bridge identities (step 1 output).
// ============================================================================

/// `k_a_col = comp_emb(a_col_machine, relabel_col)` (Seq equality, from the per-entry lemma).
pub proof fn lemma_a_col_factors(mm: ModMachine, n: nat)
    ensures
        k_a_col(mm, n) =~= comp_emb(a_col_machine(mm, n), relabel_col(mm, n)),
{
    let comp = comp_emb(a_col_machine(mm, n), relabel_col(mm, n));
    lemma_machine_col_len(mm, n);
    assert(comp.len() == k_a_col(mm, n).len());
    assert forall|i: int| 0 <= i < comp.len() implies comp[i] =~= k_a_col(mm, n)[i] by {
        assert(comp[i] == apply_embedding(a_col_machine(mm, n), relabel_col(mm, n)[i]));
        lemma_a_factor_entry(mm, n, i);
    }
}

/// `k_b_col = comp_emb(b_col_machine, relabel_col)`.
pub proof fn lemma_b_col_factors(mm: ModMachine, n: nat)
    ensures
        k_b_col(mm, n) =~= comp_emb(b_col_machine(mm, n), relabel_col(mm, n)),
{
    let comp = comp_emb(b_col_machine(mm, n), relabel_col(mm, n));
    lemma_machine_col_len(mm, n);
    assert(comp.len() == k_b_col(mm, n).len());
    assert forall|i: int| 0 <= i < comp.len() implies comp[i] =~= k_b_col(mm, n)[i] by {
        assert(comp[i] == apply_embedding(b_col_machine(mm, n), relabel_col(mm, n)[i]));
        lemma_b_factor_entry(mm, n, i);
    }
}

/// **The a-bridge:** `emb(k_a_col, w) = emb(a_col_machine, relabel(w))`. So a psi-scheme `a_col`
/// embedding equals the machine-scheme `a_col_machine` embedding of the relabeled word.
pub proof fn lemma_emb_a_col_via_relabel(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, psi_assoc(mm, n).len()),
    ensures
        apply_embedding(k_a_col(mm, n), w)
            =~= apply_embedding(a_col_machine(mm, n), relabel(mm, n, w)),
{
    lemma_machine_col_len(mm, n);
    assert(word_valid(w, relabel_col(mm, n).len()));
    lemma_emb_emb_compose(a_col_machine(mm, n), relabel_col(mm, n), w);
    lemma_a_col_factors(mm, n);
    // emb(k_a_col, w) = emb(comp_emb(am, rc), w) = emb(am, emb(rc, w)) = emb(am, relabel(w)).
    assert(apply_embedding(k_a_col(mm, n), w)
        =~= apply_embedding(comp_emb(a_col_machine(mm, n), relabel_col(mm, n)), w));
}

/// **The b-bridge:** `emb(k_b_col, w) = emb(b_col_machine, relabel(w))`.
pub proof fn lemma_emb_b_col_via_relabel(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, psi_assoc(mm, n).len()),
    ensures
        apply_embedding(k_b_col(mm, n), w)
            =~= apply_embedding(b_col_machine(mm, n), relabel(mm, n, w)),
{
    lemma_machine_col_len(mm, n);
    assert(word_valid(w, relabel_col(mm, n).len()));
    lemma_emb_emb_compose(b_col_machine(mm, n), relabel_col(mm, n), w);
    lemma_b_col_factors(mm, n);
    assert(apply_embedding(k_b_col(mm, n), w)
        =~= apply_embedding(comp_emb(b_col_machine(mm, n), relabel_col(mm, n)), w));
}

// ============================================================================
// Step 2 — the base-case faithfulness retraction `ρ : h1_base → base_A_plus_base`.
// A c-free machine-scheme base-word trivial in `h1_base` is trivial in `g_m∗free(d,b_j)`. The tool
// is the c-killing retraction (kill c, fix machine, shift b/d down by n into the c-free layout).
// ============================================================================

/// `inverse_word([s]) = [inverse_symbol(s)]` (singleton, in `seq!` form).
proof fn lemma_inverse_word_singleton(s: Symbol)
    ensures
        inverse_word(seq![s]) =~= seq![inverse_symbol(s)],
{
    assert(seq![s] =~= Seq::new(1, |_i: int| s));
    lemma_inverse_singleton(s);
    assert(Seq::new(1, |_i: int| inverse_symbol(s)) =~= seq![inverse_symbol(s)]);
}

/// Generic: `apply_hom(h, w) = apply_embedding(h.generator_images, w)` (same recursion).
proof fn lemma_apply_hom_eq_emb(h: HomomorphismData, w: Word)
    ensures
        apply_hom(h, w) =~= apply_embedding(h.generator_images, w),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        lemma_apply_hom_eq_emb(h, w.drop_first());
        assert(apply_hom_symbol(h, w.first()) == apply_embedding_symbol(h.generator_images, w.first()))
        by {
            match w.first() {
                Symbol::Gen(i) => {},
                Symbol::Inv(i) => {},
            }
        }
    }
}

/// Generic: an embedding whose first `k` images are `[Gen(i)]` fixes any `k`-valid word.
proof fn lemma_emb_identity_prefix(imgs: Seq<Word>, w: Word, k: nat)
    requires
        word_valid(w, k),
        forall|i: int| 0 <= i < k ==> #[trigger] imgs[i] =~= seq![Symbol::Gen(i as nat)],
    ensures
        apply_embedding(imgs, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_embedding(imgs, w) =~= empty_word());
        assert(w =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, k)) by { assert(w[0] == s); }
        assert(word_valid(rest, k)) by {
            assert forall|j: int| 0 <= j < rest.len() implies symbol_valid(#[trigger] rest[j], k) by {
                assert(rest[j] == w[j + 1]);
            }
        }
        lemma_emb_identity_prefix(imgs, rest, k);
        let g = generator_index(s);
        assert(g < k);
        assert(imgs[g as int] =~= seq![Symbol::Gen(g)]);
        assert(apply_embedding_symbol(imgs, s) =~= seq![s]) by {
            match s {
                Symbol::Gen(gg) => { assert(apply_embedding_symbol(imgs, s) == imgs[gg as int]); },
                Symbol::Inv(gg) => {
                    assert(apply_embedding_symbol(imgs, s) == inverse_word(imgs[gg as int]));
                    assert(imgs[gg as int] =~= seq![Symbol::Gen(g)]);
                    lemma_inverse_word_singleton(Symbol::Gen(g));
                    assert(inverse_symbol(Symbol::Gen(g)) == Symbol::Inv(g));
                    assert(inverse_word(imgs[gg as int]) =~= seq![Symbol::Inv(g)]);
                    assert(seq![s] =~= seq![Symbol::Inv(g)]);
                },
            }
        }
        assert(apply_embedding(imgs, w)
            =~= concat(apply_embedding_symbol(imgs, s), apply_embedding(imgs, rest)));
        assert(apply_embedding(imgs, w) =~= concat(seq![s], rest));
        assert(concat(seq![s], rest) =~= w);
    }
}

/// The c-killing retraction `ρ : h1_base → base_A_plus_base`. Machine gen `i<nk ↦ [Gen(i)]`;
/// c gen (`nk≤i<nk+n`) `↦ ε`; b/d gen (`i≥nk+n`) `↦ [Gen(i−n)]` (down-shift into the c-free layout).
pub open spec fn base_retraction(mm: ModMachine, n: nat) -> HomomorphismData {
    let nk = g_m(mm).num_generators;
    HomomorphismData {
        source: h1_base(mm, n),
        target: base_A_plus_base(mm, n),
        generator_images: Seq::new(h1_num_gens(nk, n), |g: int| {
            if g < nk {
                seq![Symbol::Gen(g as nat)]
            } else if g < nk + n {
                empty_word()
            } else {
                seq![Symbol::Gen((g - n) as nat)]
            }
        }),
    }
}

/// `base_A_plus_base` is a valid presentation (g_m's relators, lifted to `nk+n+1` gens).
pub proof fn lemma_base_A_plus_base_valid(mm: ModMachine, n: nat)
    ensures
        presentation_valid(base_A_plus_base(mm, n)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_valid(mm);
    reveal(presentation_valid);
    let p = base_A_plus_base(mm, n);
    assert forall|i: int| 0 <= i < p.relators.len()
        implies word_valid(#[trigger] p.relators[i], p.num_generators) by {
        assert(p.relators[i] == g_m(mm).relators[i]);
        assert(word_valid(g_m(mm).relators[i], nk));
        lemma_word_valid_mono(g_m(mm).relators[i], nk, (nk + n + 1) as nat);
    }
}

/// `ρ` fixes a machine word (valid over `nk`): `apply_hom(ρ, r) = r`.
proof fn lemma_rho_fixes_machine_word(mm: ModMachine, n: nat, r: Word)
    requires
        word_valid(r, g_m(mm).num_generators),
    ensures
        apply_hom(base_retraction(mm, n), r) =~= r,
{
    let nk = g_m(mm).num_generators;
    let rho = base_retraction(mm, n);
    lemma_apply_hom_eq_emb(rho, r);
    assert forall|i: int| 0 <= i < nk
        implies #[trigger] rho.generator_images[i] =~= seq![Symbol::Gen(i as nat)] by {}
    lemma_emb_identity_prefix(rho.generator_images, r, nk);
}

/// `ρ` sends a comm relator to a self-cancelling pair `[Gen(g), Inv(g)] ≡ ε` (`g = b_idx − n`).
proof fn lemma_rho_on_comm(mm: ModMachine, n: nat, bi: nat, cj: nat)
    requires
        1 <= bi <= n,
        1 <= cj <= n,
    ensures
        equiv_in_presentation(base_A_plus_base(mm, n),
            apply_hom(base_retraction(mm, n), comm_relator(g_m(mm).num_generators, n, bi, cj)),
            empty_word()),
{
    let nk = g_m(mm).num_generators;
    let rho = base_retraction(mm, n);
    let bb = b_idx(nk, n, bi);
    let cc = c_idx(nk, cj);
    let comm = comm_relator(nk, n, bi, cj);
    assert(comm =~= seq![Symbol::Gen(bb), Symbol::Gen(cc), Symbol::Inv(bb), Symbol::Inv(cc)]);
    // index ranges: bb ∈ [nk+n, nk+2n), cc ∈ [nk, nk+n).
    assert(bb == b_base(nk, n) + (bi - 1) && b_base(nk, n) == nk + n);
    assert(cc == c_base(nk) + (cj - 1) && c_base(nk) == nk);
    assert(nk + n <= bb < nk + 2 * n);
    assert(nk <= cc < nk + n);
    let g = (bb - n) as nat;
    // per-symbol action of ρ.
    assert(rho.generator_images[bb as int] =~= seq![Symbol::Gen(g)]);
    assert(rho.generator_images[cc as int] =~= empty_word());
    assert(apply_hom_symbol(rho, Symbol::Gen(bb)) =~= seq![Symbol::Gen(g)]);
    assert(apply_hom_symbol(rho, Symbol::Gen(cc)) =~= empty_word());
    assert(apply_hom_symbol(rho, Symbol::Inv(bb)) =~= seq![Symbol::Inv(g)]) by {
        assert(apply_hom_symbol(rho, Symbol::Inv(bb)) == inverse_word(rho.generator_images[bb as int]));
        assert(rho.generator_images[bb as int] =~= seq![Symbol::Gen(g)]);
        lemma_inverse_word_singleton(Symbol::Gen(g));
        assert(inverse_symbol(Symbol::Gen(g)) == Symbol::Inv(g));
    }
    assert(apply_hom_symbol(rho, Symbol::Inv(cc)) =~= empty_word()) by {
        assert(apply_hom_symbol(rho, Symbol::Inv(cc)) == inverse_word(rho.generator_images[cc as int]));
        assert(inverse_word(empty_word()) =~= empty_word());
    }
    // unfold apply_hom over the 4-symbol word.
    reveal_with_fuel(apply_hom, 5);
    assert(apply_hom(rho, comm) =~= seq![Symbol::Gen(g), Symbol::Inv(g)]);
    // self-cancelling pair ≡ ε.
    assert(is_inverse_pair(Symbol::Gen(g), Symbol::Inv(g)));
    lemma_cancel_pair_equiv_empty(base_A_plus_base(mm, n), Symbol::Gen(g), Symbol::Inv(g));
}

/// `ρ` is a valid homomorphism `h1_base → base_A_plus_base`.
pub proof fn lemma_base_retraction_valid(mm: ModMachine, n: nat)
    ensures
        is_valid_homomorphism(base_retraction(mm, n)),
{
    let nk = g_m(mm).num_generators;
    let rho = base_retraction(mm, n);
    lemma_h1_base_valid(mm, n);
    lemma_h1_base_num_generators(mm, n);
    lemma_base_A_plus_base_valid(mm, n);
    assert(rho.source.num_generators == h1_num_gens(nk, n));
    assert(rho.generator_images.len() == h1_num_gens(nk, n));
    assert(rho.target.num_generators == nk + n + 1);
    // images valid over nk+n+1.
    assert forall|i: int| 0 <= i < rho.generator_images.len()
        implies word_valid(#[trigger] rho.generator_images[i], (nk + n + 1) as nat) by {
        if i < nk {
            assert(rho.generator_images[i] =~= seq![Symbol::Gen(i as nat)]);
        } else if i < nk + n {
            assert(rho.generator_images[i] =~= empty_word());
        } else {
            assert(rho.generator_images[i] =~= seq![Symbol::Gen((i - n) as nat)]);
            assert(i - n < nk + n + 1);   // i < h1_num_gens = nk+2n+1 ⟹ i-n < nk+n+1
        }
    }
    // relators map to ≡ ε.
    let gr = g_m(mm).relators;
    assert(rho.source.relators == gr + comm_relators(nk, n));
    assert forall|i: int| 0 <= i < rho.source.relators.len()
        implies equiv_in_presentation(rho.target, apply_hom(rho, #[trigger] rho.source.relators[i]),
            empty_word()) by {
        if i < gr.len() {
            // K_M relator: ρ fixes it; it is a base_A_plus_base relator (index i).
            assert(rho.source.relators[i] == gr[i]);
            lemma_g_m_valid(mm);
            reveal(presentation_valid);
            assert(word_valid(gr[i], nk));
            lemma_rho_fixes_machine_word(mm, n, gr[i]);
            assert(base_A_plus_base(mm, n).relators[i] == gr[i]);
            lemma_relator_is_identity(base_A_plus_base(mm, n), i);
        } else {
            // comm relator: ρ kills the c, leaves b·b⁻¹ ≡ ε.
            let j = i - gr.len();
            assert(rho.source.relators[i] == comm_relators(nk, n)[j]);
            assert(comm_relators(nk, n)[j]
                == comm_relator(nk, n, (j / (n as int) + 1) as nat, (j % (n as int) + 1) as nat));
            let bi = (j / (n as int) + 1) as nat;
            let cj = (j % (n as int) + 1) as nat;
            assert(comm_relators(nk, n).len() == n * n);
            assert(0 <= j < n * n);
            assert(n > 0) by { if n == 0 { assert(n * n == 0); } }
            vstd::arithmetic::div_mod::lemma_multiply_divide_lt(j, n as int, n as int);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, n as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(j, n as int);
            assert(1 <= bi <= n);
            assert(1 <= cj <= n);
            lemma_rho_on_comm(mm, n, bi, cj);
        }
    }
}

/// `comp_images(ρ, a_col_machine)[i] = [Gen(i)]` for each base gen `i ≤ nk+n` (the retraction
/// inverts the inclusion on the base generators).
proof fn lemma_comp_rho_acol_identity(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < g_m(mm).num_generators + n + 1,
    ensures
        comp_images(base_retraction(mm, n), a_col_machine(mm, n))[i]
            =~= seq![Symbol::Gen(i as nat)],
{
    let nk = g_m(mm).num_generators;
    let rho = base_retraction(mm, n);
    let am = a_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    assert(comp_images(rho, am)[i] == apply_hom(rho, am[i]));
    if i < nk {
        // a_col_machine[i] = [Gen(i)], ρ([Gen(i)]) = [Gen(i)].
        assert(am[i] =~= seq![Symbol::Gen(i as nat)]) by {
            assert(am[i] == Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])[i]);
        }
        assert(apply_hom_symbol(rho, Symbol::Gen(i as nat)) =~= seq![Symbol::Gen(i as nat)]) by {
            assert(rho.generator_images[i] =~= seq![Symbol::Gen(i as nat)]);
        }
        reveal_with_fuel(apply_hom, 2);
        assert(apply_hom(rho, am[i]) =~= seq![Symbol::Gen(i as nat)]);
    } else if i < nk + n {
        // a_col_machine[i] = [Gen(b_idx(.., i-nk+1))] = [Gen(n+i)]; ρ([Gen(n+i)]) = [Gen(i)].
        let jj = (i - nk) as int;
        assert(am[i] =~= seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))]) by {
            assert(am[i] == Seq::new(n, |j2: int| seq![Symbol::Gen(b_idx(nk, n, (j2 + 1) as nat))])[jj]);
        }
        assert(b_idx(nk, n, (jj + 1) as nat) == nk + n + jj);
        assert(b_idx(nk, n, (jj + 1) as nat) == n + i);
        assert(apply_hom_symbol(rho, Symbol::Gen((n + i) as nat)) =~= seq![Symbol::Gen(i as nat)]) by {
            assert(n + i >= nk + n);
            assert(rho.generator_images[n + i] =~= seq![Symbol::Gen(((n + i) - n) as nat)]);
            assert(((n + i) - n) as nat == i as nat);
        }
        reveal_with_fuel(apply_hom, 2);
        assert(apply_hom(rho, am[i]) =~= seq![Symbol::Gen(i as nat)]);
    } else {
        // i == nk+n (d): a_col_machine[nk+n] = [Gen(d_idx=nk+2n)]; ρ([Gen(nk+2n)]) = [Gen(nk+n)].
        assert(i == nk + n);
        assert(am[i] =~= seq![Symbol::Gen(d_idx(nk, n))]) by {
            assert(am[i] == ((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |j2: int| seq![Symbol::Gen(b_idx(nk, n, (j2 + 1) as nat))]))
                + seq![ seq![Symbol::Gen(d_idx(nk, n))] ])[i]);
        }
        assert(d_idx(nk, n) == nk + 2 * n);
        assert(apply_hom_symbol(rho, Symbol::Gen(d_idx(nk, n))) =~= seq![Symbol::Gen(i as nat)]) by {
            assert(d_idx(nk, n) >= nk + n);
            assert(rho.generator_images[d_idx(nk, n) as int]
                =~= seq![Symbol::Gen((d_idx(nk, n) - n) as nat)]);
            assert((d_idx(nk, n) - n) as nat == i as nat);
        }
        reveal_with_fuel(apply_hom, 2);
        assert(apply_hom(rho, am[i]) =~= seq![Symbol::Gen(i as nat)]);
    }
}

// ============================================================================
// `a_col_machine` / `b_col_machine` fix machine words (gens `< nk`) — both columns are the identity
// on the machine block. Subsumes config-fix (config ⊂ machine) and powers step-4 K_M base relators.
// ============================================================================

/// `a_col_machine` fixes any machine word (valid over `nk`): `emb(a_col_machine, r) = r`.
pub proof fn lemma_a_col_machine_fixes_machine_word(mm: ModMachine, n: nat, r: Word)
    requires
        word_valid(r, g_m(mm).num_generators),
    ensures
        apply_embedding(a_col_machine(mm, n), r) =~= r,
{
    let nk = g_m(mm).num_generators;
    let am = a_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    assert forall|i: int| 0 <= i < nk implies #[trigger] am[i] =~= seq![Symbol::Gen(i as nat)] by {
        assert(am[i] == Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])[i]);
    }
    lemma_emb_identity_prefix(am, r, nk);
}

/// `b_col_machine` fixes any machine word (the machine block of `b_col_machine` is also the identity).
pub proof fn lemma_b_col_machine_fixes_machine_word(mm: ModMachine, n: nat, r: Word)
    requires
        word_valid(r, g_m(mm).num_generators),
    ensures
        apply_embedding(b_col_machine(mm, n), r) =~= r,
{
    let nk = g_m(mm).num_generators;
    let bm = b_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    assert forall|i: int| 0 <= i < nk implies #[trigger] bm[i] =~= seq![Symbol::Gen(i as nat)] by {
        assert(bm[i] == Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])[i]);
    }
    lemma_emb_identity_prefix(bm, r, nk);
}

/// **Step-4 von-Dyck, base K_M relators.** For a `g_m` (K_M) relator `r`, `emb(b_col_machine, r) =
/// r ≡_{h2_pred} ε` (b_col_machine fixes machine words; `r` is an `h2_pred` relator via its K_M
/// clause). The base-relator half of the von-Dyck homomorphism condition (step 4).
pub proof fn lemma_cs5_vondyck_KM_relator(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, r: Word,
)
    requires
        g_m(mm).relators.contains(r),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(b_col_machine(mm, n), r), empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_valid(mm);
    reveal(presentation_valid);
    let idx = choose|i: int| 0 <= i < g_m(mm).relators.len() && g_m(mm).relators[i] == r;
    assert(word_valid(g_m(mm).relators[idx], nk));
    assert(word_valid(r, nk));
    lemma_b_col_machine_fixes_machine_word(mm, n, r);     // emb(b_col_machine, r) = r
    // r is an h2_pred relator (K_M clause).
    assert((h2_pred(mm, n, m, is_S).relators)(r)) by {
        assert((h2_pred(mm, n, m, is_S).relators)(r) == h2_pred_relator(mm, n, m, is_S, r));
        assert(g_m(mm).relators.contains(r));
    }
    lemma_pred_relator_is_identity(h2_pred(mm, n, m, is_S), r);
}

// ============================================================================
// Step 3a — `base_A_plus_data` : the machine-scheme HNN (analog of `pa_data`/`recog_data`).
// Base = `base_A_plus_base` (= g_m∗free(d,b_j)); one p-association per `slice` index, in the
// MACHINE-SCHEME layout (b's at `nk..nk+n−1`, d at `nk+n`) — so the rhs uses `w_b(nk, …)` and
// `[Gen(nk+n)]`, NOT the h2 `w_b(nk+n, …)`/`[Gen(nk+2n)]`. The peel (step 3d) produces
// `relabel(w) ≡_{hnn_presentation(base_A_plus_data(H₀-slice))} ε`; `a_col_machine` carries it to the
// h2-layout `recog_data` (step 3b). The `slice` is H₀-restricted (needed by step-4 von-Dyck + the
// step-3c intersection); validity needs only `numbers_word` per index.
// ============================================================================

/// The machine-scheme family-(II) rhs `t_β · w_β(b) · d` over the `base_A_plus_base` layout
/// (b-base `nk`, d at `nk+n`). Maps under `a_col_machine` to the h2 `family_II_rhs` (step 3b).
pub open spec fn assoc_rhs_machine(mm: ModMachine, n: nat, m: nat, beta: nat) -> Word {
    let nk = g_m(mm).num_generators;
    config_word(beta, 0) + w_b(nk, n, m, beta) + seq![Symbol::Gen((nk + n) as nat)]
}

/// The machine-scheme p-associations: `(t_β, t_β w_β(b) d)` for each `β` in `slice`.
pub open spec fn base_A_plus_assoc(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>) -> Seq<(Word, Word)> {
    Seq::new(slice.len(), |i: int| (config_word(slice[i], 0), assoc_rhs_machine(mm, n, m, slice[i])))
}

/// **`base_A₊ = HNN(g_m∗free(d,b_j), p | R_β : β∈slice)`** — the recognized group (machine scheme).
pub open spec fn base_A_plus_data(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>) -> HNNData {
    HNNData { base: base_A_plus_base(mm, n), associations: base_A_plus_assoc(mm, n, m, slice) }
}

/// Structural facts: base has `nk+n+1` gens, `|slice|` associations.
pub proof fn lemma_base_A_plus_data_shape(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>)
    ensures
        base_A_plus_data(mm, n, m, slice).base.num_generators == g_m(mm).num_generators + n + 1,
        base_A_plus_data(mm, n, m, slice).associations.len() == slice.len(),
{
}

/// **`base_A_plus_data` is a valid HNN datum.** Base valid (step-2 `lemma_base_A_plus_base_valid`);
/// each association word valid over `nk+n+1`: `config(β,0)` uses gens {0,1}⊂nk; `w_b(nk,…)` the
/// b-block `[nk, nk+n)`; `d = nk+n`. Mirror of `lemma_pa_data_valid`.
pub proof fn lemma_base_A_plus_data_valid(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < slice.len() ==> numbers_word(n, m, #[trigger] slice[i]),
    ensures
        hnn_data_valid(base_A_plus_data(mm, n, m, slice)),
{
    let nk = g_m(mm).num_generators;
    let ng = (nk + n + 1) as nat;
    let data = base_A_plus_data(mm, n, m, slice);
    lemma_base_A_plus_base_valid(mm, n);
    assert(data.base.num_generators == ng);
    let assocs = base_A_plus_assoc(mm, n, m, slice);
    assert forall|i: int| #![trigger assocs[i]] 0 <= i < assocs.len() implies
        word_valid(assocs[i].0, ng) && word_valid(assocs[i].1, ng) by {
        let beta = slice[i];
        assert(assocs[i] == (config_word(beta, 0), assoc_rhs_machine(mm, n, m, beta)));
        // a-column: config(β,0) valid over 3 ≤ nk+n+1.
        lemma_config_word_valid(beta, 0);                   // word_valid(·, 3)
        lemma_word_valid_mono(config_word(beta, 0), 3, ng);
        // b-column: config · w_b(nk,…) · [Gen(nk+n)].
        lemma_w_c_valid(nk, n, m, beta, ng);                // w_b = w_c; nk + n ≤ ng
        lemma_single_gen_valid((nk + n) as nat, ng);        // [Gen(nk+n)], nk+n < ng
        lemma_concat_word_valid(config_word(beta, 0), w_b(nk, n, m, beta), ng);
        lemma_concat_word_valid(config_word(beta, 0) + w_b(nk, n, m, beta),
            seq![Symbol::Gen((nk + n) as nat)], ng);
        assert(assoc_rhs_machine(mm, n, m, beta)
            =~= (config_word(beta, 0) + w_b(nk, n, m, beta)) + seq![Symbol::Gen((nk + n) as nat)]);
    }
}

// ============================================================================
// Step 3b (a-side) — `a_col_machine` carries the machine-scheme `assoc_rhs_machine` to the h2
// `family_II_rhs` (the descent bridge). The core is the `w_c` base-relabel `nk → nk+n` (mirror of
// CS-4 `lemma_a_words_relabel_wc`).
// ============================================================================

/// `a_col_machine`'s b-block: `a_col_machine[nk+j] = [Gen(b_idx(nk,n,j+1))]` for `0 ≤ j < n`.
proof fn lemma_a_col_machine_bblock(mm: ModMachine, n: nat, j: int)
    requires
        0 <= j < n,
    ensures
        a_col_machine(mm, n)[(g_m(mm).num_generators + j) as int]
            =~= seq![Symbol::Gen(b_idx(g_m(mm).num_generators, n, (j + 1) as nat))],
{
    let nk = g_m(mm).num_generators;
    let am = a_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    let blk_m: Seq<Word> = Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)]);
    let blk_b: Seq<Word> = Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))]);
    let blk_d: Seq<Word> = seq![ seq![Symbol::Gen(d_idx(nk, n))] ];
    assert(am == ((blk_m + blk_b) + blk_d) + seq![ seq![Symbol::Gen(p_idx(nk, n))] ]);
    assert(((blk_m + blk_b) + blk_d)[(nk + j) as int] == (blk_m + blk_b)[(nk + j) as int]);
    assert((blk_m + blk_b)[(nk + j) as int] == blk_b[j]);
    assert(blk_b[j] == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
}

/// Digit relabel: `emb(a_col_machine, [al(nk,n,d)]) = [al(nk+n,n,d)]` (mirror of
/// `lemma_a_words_on_alpha_letter`; machine-scheme b-base `nk` → h2 b-base `nk+n`).
proof fn lemma_a_col_machine_on_alpha_letter(mm: ModMachine, n: nat, d: nat)
    requires
        1 <= d <= 2 * n,
    ensures
        apply_embedding(a_col_machine(mm, n), seq![alphabet_letter(g_m(mm).num_generators, n, d)])
            =~= seq![alphabet_letter((g_m(mm).num_generators + n) as nat, n, d)],
{
    let nk = g_m(mm).num_generators;
    let am = a_col_machine(mm, n);
    let bb = (nk + n) as nat;
    reveal_with_fuel(apply_embedding, 2);
    if d <= n {
        // al(nk,n,d) = Gen(nk+d-1); j = d-1 ∈ [0,n).
        let jj = (d - 1) as int;
        assert(alphabet_letter(nk, n, d) == Symbol::Gen((nk + d - 1) as nat));
        assert((nk + d - 1) as nat == (nk + jj) as nat);
        lemma_a_col_machine_bblock(mm, n, jj);
        assert(am[(nk + jj) as int] =~= seq![Symbol::Gen(b_idx(nk, n, d))]);
        assert(b_idx(nk, n, d) == bb + d - 1);
        lemma_concat_empty_right(am[(nk + jj) as int]);
        assert(apply_embedding(am, seq![Symbol::Gen((nk + d - 1) as nat)]) =~= am[(nk + jj) as int]);
        assert(alphabet_letter(bb, n, d) == Symbol::Gen((bb + d - 1) as nat));
    } else {
        // al(nk,n,d) = Inv(nk+(d-n)-1); e = d-n ∈ [1,n], j = e-1.
        let e = (d - n) as nat;
        let jj = (e - 1) as int;
        assert(alphabet_letter(nk, n, d) == Symbol::Inv((nk + e - 1) as nat));
        assert((nk + e - 1) as nat == (nk + jj) as nat);
        lemma_a_col_machine_bblock(mm, n, jj);
        assert(am[(nk + jj) as int] =~= seq![Symbol::Gen(b_idx(nk, n, e))]);
        assert(b_idx(nk, n, e) == bb + e - 1);
        assert(apply_embedding_symbol(am, Symbol::Inv((nk + e - 1) as nat))
            =~= inverse_word(am[(nk + jj) as int]));
        reveal_with_fuel(inverse_word, 2);
        lemma_concat_empty_right(inverse_word(am[(nk + jj) as int]));
        assert(apply_embedding(am, seq![Symbol::Inv((nk + e - 1) as nat)])
            =~= inverse_word(am[(nk + jj) as int]));
        assert(inverse_word(seq![Symbol::Gen((bb + e - 1) as nat)]) =~= seq![Symbol::Inv((bb + e - 1) as nat)])
        by { lemma_inverse_word_singleton(Symbol::Gen((bb + e - 1) as nat)); }
        assert(alphabet_letter(bb, n, d) == Symbol::Inv((bb + (d - n) - 1) as nat));
    }
}

/// **The `w_c` base-relabel** `emb(a_col_machine, w_c(nk,n,m,γ)) = w_c(nk+n,n,m,γ)` (mirror of
/// `lemma_a_words_relabel_wc`; induction on `γ`'s digit recursion).
pub proof fn lemma_a_col_machine_relabel_wc(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        apply_embedding(a_col_machine(mm, n), w_c(g_m(mm).num_generators, n, m, gamma))
            =~= w_c((g_m(mm).num_generators + n) as nat, n, m, gamma),
    decreases gamma,
{
    let nk = g_m(mm).num_generators;
    let am = a_col_machine(mm, n);
    let bb = (nk + n) as nat;
    if gamma == 0 || m <= 1 {
        assert(w_c(nk, n, m, gamma) =~= empty_word());
        assert(w_c(bb, n, m, gamma) =~= empty_word());
        assert(apply_embedding(am, empty_word()) =~= empty_word());
    } else {
        let d = (gamma % m) as nat;
        assert(1 <= d <= 2 * n);
        assert(numbers_word(n, m, (gamma / m) as nat));
        let pre = w_c(nk, n, m, (gamma / m) as nat);
        let letter: Word = Seq::new(1, |_i: int| alphabet_letter(nk, n, d));
        assert(w_c(nk, n, m, gamma) =~= pre + letter);
        lemma_apply_embedding_concat(am, pre, letter);
        lemma_a_col_machine_relabel_wc(mm, n, m, (gamma / m) as nat);
        assert(letter =~= seq![alphabet_letter(nk, n, d)]);
        lemma_a_col_machine_on_alpha_letter(mm, n, d);
        let preB = w_c(bb, n, m, (gamma / m) as nat);
        let letterB: Word = Seq::new(1, |_i: int| alphabet_letter(bb, n, d));
        assert(w_c(bb, n, m, gamma) =~= preB + letterB);
        assert(letterB =~= seq![alphabet_letter(bb, n, d)]);
    }
}

/// **Step-3b descent bridge (a-side):** `emb(a_col_machine, assoc_rhs_machine(β)) = family_II_rhs(β)`.
/// `a_col_machine` fixes the config (machine), relabels `w_b(nk,…)→w_b(nk+n,…)`, and maps machine-d
/// `Gen(nk+n) ↦ h2-d Gen(nk+2n)`.
pub proof fn lemma_a_col_machine_assoc_rhs(mm: ModMachine, n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
    ensures
        apply_embedding(a_col_machine(mm, n), assoc_rhs_machine(mm, n, m, beta))
            =~= family_II_rhs(mm, n, m, beta),
{
    let nk = g_m(mm).num_generators;
    let am = a_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    lemma_g_m_num_generators(mm);                  // nk = 4 + |quads| ≥ 4 > 3
    let cfg = config_word(beta, 0);
    let wb_m = w_b(nk, n, m, beta);
    let dw_m: Word = seq![Symbol::Gen((nk + n) as nat)];
    assert(assoc_rhs_machine(mm, n, m, beta) =~= (cfg + wb_m) + dw_m);
    // distribute apply_embedding over the two concats.
    lemma_apply_embedding_concat(am, cfg + wb_m, dw_m);
    lemma_apply_embedding_concat(am, cfg, wb_m);
    // config: fixed (machine word over 3 ≤ nk).
    lemma_config_word_valid(beta, 0);
    lemma_word_valid_mono(cfg, 3, nk);
    lemma_a_col_machine_fixes_machine_word(mm, n, cfg);
    // w_b(nk,…) = w_c(nk,…) relabels to w_b(nk+n,…).
    lemma_a_col_machine_relabel_wc(mm, n, m, beta);
    // machine-d → h2-d.
    assert(am[(nk + n) as int] =~= seq![Symbol::Gen(d_idx(nk, n))]) by {
        assert(am[(nk + n) as int]
            == ((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))]))
                + seq![ seq![Symbol::Gen(d_idx(nk, n))] ])[(nk + n) as int]);
    }
    lemma_emb_single_gen(am, (nk + n) as nat);
    assert(apply_embedding(am, dw_m) =~= seq![Symbol::Gen(d_idx(nk, n))]);
    // assemble: family_II_rhs = config + w_b(nk+n,…) + [Gen(d_idx)].
    assert(family_II_rhs(mm, n, m, beta)
        =~= (cfg + w_b(b_base(nk, n), n, m, beta)) + seq![Symbol::Gen(d_idx(nk, n))]);
    assert(b_base(nk, n) == nk + n);
}

/// **CS-5c base-case faithfulness.** A machine-scheme base-word whose `a_col_machine`-image is trivial
/// in `h1_base` is trivial in `base_A_plus_base = g_m∗free(d,b_j)`. (Apply `ρ`; `ρ∘a_col_machine = id`
/// on base gens.) The base case of the step-3 p-peel.
pub proof fn lemma_cs5_base_case_faithful(mm: ModMachine, n: nat, w_base: Word)
    requires
        word_valid(w_base, (g_m(mm).num_generators + n + 1) as nat),
        equiv_in_presentation(h1_base(mm, n),
            apply_embedding(a_col_machine(mm, n), w_base), empty_word()),
    ensures
        equiv_in_presentation(base_A_plus_base(mm, n), w_base, empty_word()),
{
    let nk = g_m(mm).num_generators;
    let rho = base_retraction(mm, n);
    let am = a_col_machine(mm, n);
    let img = apply_embedding(am, w_base);
    lemma_machine_col_len(mm, n);
    lemma_base_retraction_valid(mm, n);
    // push the h1_base-triviality through ρ.
    lemma_hom_preserves_equiv(rho, img, empty_word());
    assert(apply_hom(rho, empty_word()) =~= empty_word());
    assert(equiv_in_presentation(base_A_plus_base(mm, n), apply_hom(rho, img), empty_word()));
    // apply_hom(ρ, emb(am, w_base)) = emb(comp_images(ρ, am), w_base) = w_base.
    assert(word_valid(w_base, am.len())) by {
        lemma_word_valid_mono(w_base, (nk + n + 1) as nat, am.len());
    }
    lemma_apply_hom_embedding_compose(rho, am, w_base);
    let comp = comp_images(rho, am);
    assert forall|i: int| 0 <= i < nk + n + 1
        implies #[trigger] comp[i] =~= seq![Symbol::Gen(i as nat)] by {
        lemma_comp_rho_acol_identity(mm, n, i);
    }
    lemma_emb_identity_prefix(comp, w_base, (nk + n + 1) as nat);
    assert(apply_hom(rho, img) =~= w_base);
}

// ============================================================================
// Step 3b (b-side) — `b_col_machine` carries the machine-scheme `assoc_rhs_machine` to the h2
// `family_II_bc_rhs` (bc-config form). Mirror of the a-side, but `b_col_machine`'s b-block image is
// the 2-symbol `[Gen(b_idx), Gen(c_idx)]`, so `w_b(nk,…)` relabels to `w_bc(nk+n, nk, …)` (b's gain
// c's). Powers the step-4 HNN relator (`lemma_cs5_bc_config_trivial` then closes it).
// ============================================================================

/// `b_col_machine`'s b-block: `b_col_machine[nk+j] = [Gen(b_idx(nk,n,j+1)), Gen(c_idx(nk,j+1))]`.
proof fn lemma_b_col_machine_bblock(mm: ModMachine, n: nat, j: int)
    requires
        0 <= j < n,
    ensures
        b_col_machine(mm, n)[(g_m(mm).num_generators + j) as int]
            =~= seq![Symbol::Gen(b_idx(g_m(mm).num_generators, n, (j + 1) as nat)),
                     Symbol::Gen(c_idx(g_m(mm).num_generators, (j + 1) as nat))],
{
    let nk = g_m(mm).num_generators;
    let bm = b_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    let blk_m: Seq<Word> = Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)]);
    let blk_b: Seq<Word> = Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat)),
                                                       Symbol::Gen(c_idx(nk, (jj + 1) as nat))]);
    let blk_d: Seq<Word> = seq![ seq![Symbol::Gen(d_idx(nk, n))] ];
    assert(bm == ((blk_m + blk_b) + blk_d) + seq![ seq![Symbol::Gen(p_idx(nk, n))] ]);
    assert(((blk_m + blk_b) + blk_d)[(nk + j) as int] == (blk_m + blk_b)[(nk + j) as int]);
    assert((blk_m + blk_b)[(nk + j) as int] == blk_b[j]);
    assert(blk_b[j] == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)),
                            Symbol::Gen(c_idx(nk, (j + 1) as nat))]);
}

/// `inverse_word([s0, s1]) = [inverse_symbol(s1), inverse_symbol(s0)]` (2-symbol reverse-invert).
proof fn lemma_inverse_word_pair(s0: Symbol, s1: Symbol)
    ensures
        inverse_word(seq![s0, s1]) =~= seq![inverse_symbol(s1), inverse_symbol(s0)],
{
    let w: Word = seq![s0, s1];
    assert(w.len() == 2);
    assert(w.first() == s0);
    assert(w.drop_first() =~= seq![s1]);
    lemma_inverse_word_singleton(s1);                    // inverse_word([s1]) = [inverse_symbol(s1)]
    assert(inverse_word(w.drop_first()) =~= seq![inverse_symbol(s1)]);
    // one unfold of inverse_word(w):
    assert(inverse_word(w)
        =~= inverse_word(w.drop_first()) + Seq::new(1, |_i: int| inverse_symbol(w.first())));
    assert(Seq::new(1, |_i: int| inverse_symbol(s0)) =~= seq![inverse_symbol(s0)]);
}

/// Digit relabel (b-side): `emb(b_col_machine, [al(nk,n,d)]) = bc_letter(nk+n, nk, n, d)`. The 2-symbol
/// bc-image replaces the a-side single `alphabet_letter`; inverse case reverses the pair.
proof fn lemma_b_col_machine_on_alpha_letter(mm: ModMachine, n: nat, d: nat)
    requires
        1 <= d <= 2 * n,
    ensures
        apply_embedding(b_col_machine(mm, n), seq![alphabet_letter(g_m(mm).num_generators, n, d)])
            =~= bc_letter((g_m(mm).num_generators + n) as nat, g_m(mm).num_generators, n, d),
{
    let nk = g_m(mm).num_generators;
    let bm = b_col_machine(mm, n);
    reveal_with_fuel(apply_embedding, 2);
    if d <= n {
        // al(nk,n,d) = Gen(nk+d-1); j = d-1 ∈ [0,n); bm[nk+j] = [Gen(b_idx(nk,n,d)), Gen(c_idx(nk,d))].
        let jj = (d - 1) as int;
        assert(alphabet_letter(nk, n, d) == Symbol::Gen((nk + d - 1) as nat));
        assert((nk + d - 1) as nat == (nk + jj) as nat);
        lemma_b_col_machine_bblock(mm, n, jj);
        assert(bm[(nk + jj) as int] =~= seq![Symbol::Gen(b_idx(nk, n, d)), Symbol::Gen(c_idx(nk, d))]);
        lemma_concat_empty_right(bm[(nk + jj) as int]);
        assert(apply_embedding(bm, seq![Symbol::Gen((nk + d - 1) as nat)]) =~= bm[(nk + jj) as int]);
        // bc_letter(nk+n, nk, n, d), d ≤ n = [Gen((nk+n)+d-1), Gen(nk+d-1)].
        assert(b_idx(nk, n, d) == (nk + n) + d - 1);
        assert(c_idx(nk, d) == nk + d - 1);
        assert(bc_letter((nk + n) as nat, nk, n, d)
            =~= seq![Symbol::Gen(((nk + n) + d - 1) as nat), Symbol::Gen((nk + d - 1) as nat)]);
    } else {
        // al(nk,n,d) = Inv(nk+e-1), e = d-n ∈ [1,n]; bm[nk+(e-1)] = [Gen(b_idx(nk,n,e)), Gen(c_idx(nk,e))],
        // so the image is its inverse = [Inv(c_idx(nk,e)), Inv(b_idx(nk,n,e))].
        let e = (d - n) as nat;
        let jj = (e - 1) as int;
        assert(alphabet_letter(nk, n, d) == Symbol::Inv((nk + e - 1) as nat));
        assert((nk + e - 1) as nat == (nk + jj) as nat);
        lemma_b_col_machine_bblock(mm, n, jj);
        assert(bm[(nk + jj) as int] =~= seq![Symbol::Gen(b_idx(nk, n, e)), Symbol::Gen(c_idx(nk, e))]);
        assert(apply_embedding_symbol(bm, Symbol::Inv((nk + e - 1) as nat))
            =~= inverse_word(bm[(nk + jj) as int]));
        lemma_inverse_word_pair(Symbol::Gen(b_idx(nk, n, e)), Symbol::Gen(c_idx(nk, e)));
        assert(inverse_word(bm[(nk + jj) as int])
            =~= seq![Symbol::Inv(c_idx(nk, e)), Symbol::Inv(b_idx(nk, n, e))]);
        lemma_concat_empty_right(inverse_word(bm[(nk + jj) as int]));
        assert(apply_embedding(bm, seq![Symbol::Inv((nk + e - 1) as nat)])
            =~= inverse_word(bm[(nk + jj) as int]));
        // bc_letter(nk+n, nk, n, d), d > n = [Inv(c_base+(e-1)), Inv(b_base+(e-1))]
        //   = [Inv(nk+e-1), Inv((nk+n)+e-1)] = [Inv(c_idx(nk,e)), Inv(b_idx(nk,n,e))].
        assert(c_idx(nk, e) == nk + e - 1);
        assert(b_idx(nk, n, e) == (nk + n) + e - 1);
        assert(bc_letter((nk + n) as nat, nk, n, d)
            =~= seq![Symbol::Inv((nk + e - 1) as nat), Symbol::Inv(((nk + n) + e - 1) as nat)]);
    }
}

/// **The `w_b`→`w_bc` base-relabel** `emb(b_col_machine, w_b(nk,n,m,γ)) = w_bc(nk+n, nk, n, m, γ)`
/// (mirror of `lemma_a_col_machine_relabel_wc`; induction on `γ`'s digit recursion). `w_b = w_c` so the
/// recursion appends one `alphabet_letter` per digit, each mapped to its bc-pair.
pub proof fn lemma_b_col_machine_relabel_wbc(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        apply_embedding(b_col_machine(mm, n), w_b(g_m(mm).num_generators, n, m, gamma))
            =~= w_bc((g_m(mm).num_generators + n) as nat, g_m(mm).num_generators, n, m, gamma),
    decreases gamma,
{
    let nk = g_m(mm).num_generators;
    let bm = b_col_machine(mm, n);
    let bb = (nk + n) as nat;
    if gamma == 0 || m <= 1 {
        assert(w_b(nk, n, m, gamma) =~= empty_word());
        assert(w_bc(bb, nk, n, m, gamma) =~= empty_word());
        assert(apply_embedding(bm, empty_word()) =~= empty_word());
    } else {
        let d = (gamma % m) as nat;
        assert(1 <= d <= 2 * n);
        assert(numbers_word(n, m, (gamma / m) as nat));
        // w_b(nk,γ) = w_b(nk,γ/m) · [al(nk,n,d)]; w_bc(bb,nk,γ) = w_bc(bb,nk,γ/m) · bc_letter(bb,nk,n,d).
        let pre = w_b(nk, n, m, (gamma / m) as nat);
        let letter: Word = Seq::new(1, |_i: int| alphabet_letter(nk, n, d));
        assert(w_b(nk, n, m, gamma) =~= pre + letter);
        lemma_apply_embedding_concat(bm, pre, letter);
        lemma_b_col_machine_relabel_wbc(mm, n, m, (gamma / m) as nat);
        assert(letter =~= seq![alphabet_letter(nk, n, d)]);
        lemma_b_col_machine_on_alpha_letter(mm, n, d);
        let preB = w_bc(bb, nk, n, m, (gamma / m) as nat);
        let letterB: Word = bc_letter(bb, nk, n, d);
        assert(w_bc(bb, nk, n, m, gamma) =~= preB + letterB);
    }
}

/// **Step-3b descent bridge (b-side):** `emb(b_col_machine, assoc_rhs_machine(β)) = family_II_bc_rhs(β)`.
/// `b_col_machine` fixes the config (machine), relabels `w_b(nk,…)→w_bc(nk+n,nk,…)`, and maps machine-d
/// `Gen(nk+n) ↦ h2-d Gen(nk+2n)`. The b-analog of `lemma_a_col_machine_assoc_rhs`; powers step-4's HNN
/// relator via the bc-atom `lemma_cs5_bc_config_trivial`.
pub proof fn lemma_b_col_machine_assoc_rhs(mm: ModMachine, n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
    ensures
        apply_embedding(b_col_machine(mm, n), assoc_rhs_machine(mm, n, m, beta))
            =~= family_II_bc_rhs(mm, n, m, beta),
{
    let nk = g_m(mm).num_generators;
    let bm = b_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    lemma_g_m_num_generators(mm);                  // nk = 4 + |quads| ≥ 4 > 3
    let cfg = config_word(beta, 0);
    let wb_m = w_b(nk, n, m, beta);
    let dw_m: Word = seq![Symbol::Gen((nk + n) as nat)];
    assert(assoc_rhs_machine(mm, n, m, beta) =~= (cfg + wb_m) + dw_m);
    // distribute apply_embedding over the two concats.
    lemma_apply_embedding_concat(bm, cfg + wb_m, dw_m);
    lemma_apply_embedding_concat(bm, cfg, wb_m);
    // config: fixed (machine word over 3 ≤ nk).
    lemma_config_word_valid(beta, 0);
    lemma_word_valid_mono(cfg, 3, nk);
    lemma_b_col_machine_fixes_machine_word(mm, n, cfg);
    // w_b(nk,…) relabels to w_bc(nk+n, nk, …).
    lemma_b_col_machine_relabel_wbc(mm, n, m, beta);
    // machine-d → h2-d.
    assert(bm[(nk + n) as int] =~= seq![Symbol::Gen(d_idx(nk, n))]) by {
        assert(bm[(nk + n) as int]
            == ((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat)),
                                            Symbol::Gen(c_idx(nk, (jj + 1) as nat))]))
                + seq![ seq![Symbol::Gen(d_idx(nk, n))] ])[(nk + n) as int]);
    }
    lemma_emb_single_gen(bm, (nk + n) as nat);
    assert(apply_embedding(bm, dw_m) =~= seq![Symbol::Gen(d_idx(nk, n))]);
    // assemble: family_II_bc_rhs = config + w_bc(nk+n,nk,…) + [Gen(d_idx)].
    assert(family_II_bc_rhs(mm, n, m, beta)
        =~= (cfg + w_bc(b_base(nk, n), c_base(nk), n, m, beta)) + seq![Symbol::Gen(d_idx(nk, n))]);
    assert(b_base(nk, n) == nk + n);
    assert(c_base(nk) == nk);
}

// ============================================================================
// Step 4 — the von-Dyck homomorphism conditions for `b_col_machine : base_A_plus_data → h2_pred`.
// Each relator of `hnn_presentation(base_A_plus_data(H0-slice))` maps to `≡_{h2_pred} ε`: base K_M
// relators via `lemma_cs5_vondyck_KM_relator` (b_col_machine fixes machine words), HNN relators `R_α`
// via the bc-atom `lemma_cs5_bc_config_trivial` (b_col_machine carries the machine-scheme `R_α` to the
// bc-config form). This is the relator-condition of `lemma_emb_respects_source_equiv_pred` — the
// well-definedness obligation of the forward von-Dyck (step 4), ready before the recognition (3c/3d).
// ============================================================================

/// `apply_embedding(images, [Inv(g)]) = inverse_word(images[g])` (single negative generator).
proof fn lemma_emb_single_inv_gen(images: Seq<Word>, g: nat)
    ensures
        apply_embedding(images, seq![Symbol::Inv(g)]) =~= inverse_word(images[g as int]),
{
    let w: Word = seq![Symbol::Inv(g)];
    assert(w.len() == 1);
    assert(w.first() == Symbol::Inv(g));
    assert(w.drop_first() =~= empty_word());
    assert(apply_embedding(images, w.drop_first()) =~= empty_word());
    assert(apply_embedding_symbol(images, w.first()) == inverse_word(images[g as int]));
    assert(apply_embedding(images, w)
        =~= concat(apply_embedding_symbol(images, w.first()), empty_word()));
    lemma_concat_empty_right(inverse_word(images[g as int]));
}

/// **Step-4 von-Dyck, HNN relator.** For `α = slice[i]` with `(α,0)∈H₀`, the `b_col_machine`-image of
/// the i-th HNN relator of `base_A_plus_data` is the bc-config relator `family_II_lhs(α) ·
/// family_II_bc_rhs(α)⁻¹ ≡_{h2_pred} ε` (`lemma_cs5_bc_config_trivial`). The machine-scheme stable
/// letter `Gen(nk+n+1)` is carried by `b_col_machine` to the h2 `Gen(p_idx)`; config/`w_b`→bc via 3b-b.
pub proof fn lemma_cs5_vondyck_hnn_relator(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, slice: Seq<nat>, i: int,
)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        s_realizes(is_S, mm, n, m),
        0 <= i < slice.len(),
        numbers_word(n, m, slice[i]),
        mm_in_H0(mm, slice[i], 0),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(b_col_machine(mm, n), hnn_relator(base_A_plus_data(mm, n, m, slice), i)),
            empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bm = b_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    let data = base_A_plus_data(mm, n, m, slice);
    let alpha = slice[i];
    let t = stable_letter(data);          // Gen(nk+n+1)
    let t_inv = stable_letter_inv(data);  // Inv(nk+n+1)
    let a_i = config_word(alpha, 0);
    let b_i = assoc_rhs_machine(mm, n, m, alpha);
    assert(data.base.num_generators == nk + n + 1) by { lemma_base_A_plus_data_shape(mm, n, m, slice); }
    assert(t == Symbol::Gen((nk + n + 1) as nat));
    assert(t_inv == Symbol::Inv((nk + n + 1) as nat));
    assert(data.associations[i] == (config_word(alpha, 0), assoc_rhs_machine(mm, n, m, alpha))) by {
        assert(data.associations[i]
            == (config_word(slice[i], 0), assoc_rhs_machine(mm, n, m, slice[i])));
    }
    // hnn_relator = [t_inv] + a_i + [t] + inverse_word(b_i).
    let r = hnn_relator(data, i);
    assert(r =~= ((seq![t_inv] + a_i) + seq![t]) + inverse_word(b_i)) by {
        assert(r == Seq::new(1, |_j: int| t_inv) + a_i + Seq::new(1, |_j: int| t)
            + inverse_word(b_i));
        assert(Seq::new(1, |_j: int| t_inv) =~= seq![t_inv]);
        assert(Seq::new(1, |_j: int| t) =~= seq![t]);
    }
    // distribute apply_embedding over the three concats.
    lemma_apply_embedding_concat(bm, (seq![t_inv] + a_i) + seq![t], inverse_word(b_i));
    lemma_apply_embedding_concat(bm, seq![t_inv] + a_i, seq![t]);
    lemma_apply_embedding_concat(bm, seq![t_inv], a_i);
    // emb(bm, [t_inv]) = inverse_word(bm[nk+n+1]) = [Inv(p_idx)].
    assert(bm[(nk + n + 1) as int] =~= seq![Symbol::Gen(p_idx(nk, n))]);
    lemma_emb_single_inv_gen(bm, (nk + n + 1) as nat);
    lemma_inverse_word_singleton(Symbol::Gen(p_idx(nk, n)));
    assert(apply_embedding(bm, seq![t_inv]) =~= seq![Symbol::Inv(p_idx(nk, n))]);
    // emb(bm, a_i) = config(α,0) (machine word over 3 ≤ nk).
    lemma_config_word_valid(alpha, 0);
    lemma_word_valid_mono(a_i, 3, nk);
    lemma_b_col_machine_fixes_machine_word(mm, n, a_i);
    // emb(bm, [t]) = bm[nk+n+1] = [Gen(p_idx)].
    lemma_emb_single_gen(bm, (nk + n + 1) as nat);
    // emb(bm, inverse_word(b_i)) = inverse_word(emb(bm, b_i)) = inverse_word(family_II_bc_rhs(α)).
    lemma_apply_embedding_inverse(bm, b_i);
    lemma_b_col_machine_assoc_rhs(mm, n, m, alpha);
    // assemble: emb(bm, r) = family_II_lhs(α) + inverse_word(family_II_bc_rhs(α)).
    let lhs = family_II_lhs(mm, n, alpha);
    let bcrhs = family_II_bc_rhs(mm, n, m, alpha);
    assert(lhs =~= (seq![Symbol::Inv(p_idx(nk, n))] + a_i) + seq![Symbol::Gen(p_idx(nk, n))]);
    assert(apply_embedding(bm, r) =~= lhs + inverse_word(bcrhs));
    lemma_cs5_bc_config_trivial(mm, n, m, is_S, alpha);
}

/// **Step-4 von-Dyck relator condition.** Each relator of `hnn_presentation(base_A_plus_data(slice))`
/// (slice all number-words AND `(·,0)∈H₀`) maps to `≡_{h2_pred} ε` under `b_col_machine`: base K_M
/// relators (j < |g_m.relators|) via `lemma_cs5_vondyck_KM_relator`, HNN relators via
/// `lemma_cs5_vondyck_hnn_relator`. The forward `lemma_emb_respects_source_equiv_pred` hypothesis.
pub proof fn lemma_cs5_vondyck_relator(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, slice: Seq<nat>, j: int,
)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        s_realizes(is_S, mm, n, m),
        forall|k: int| 0 <= k < slice.len() ==> numbers_word(n, m, #[trigger] slice[k]),
        forall|k: int| 0 <= k < slice.len() ==> mm_in_H0(mm, #[trigger] slice[k], 0),
        0 <= j < hnn_presentation(base_A_plus_data(mm, n, m, slice)).relators.len(),
    ensures
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S),
            apply_embedding(b_col_machine(mm, n),
                hnn_presentation(base_A_plus_data(mm, n, m, slice)).relators[j]),
            empty_word()),
{
    let data = base_A_plus_data(mm, n, m, slice);
    let hp = hnn_presentation(data);
    let glen = g_m(mm).relators.len();
    assert(data.base == base_A_plus_base(mm, n));
    assert(data.base.relators == g_m(mm).relators);
    assert(hp.relators == data.base.relators + hnn_relators(data));
    if j < glen {
        // base K_M relator.
        assert(hp.relators[j] == g_m(mm).relators[j]);
        assert(g_m(mm).relators.contains(g_m(mm).relators[j])) by {
            assert(g_m(mm).relators[j] == g_m(mm).relators[j]);
        }
        lemma_cs5_vondyck_KM_relator(mm, n, m, is_S, g_m(mm).relators[j]);
    } else {
        // HNN relator at index i = j - glen.
        let i = j - glen;
        assert(hnn_relators(data).len() == slice.len()) by {
            lemma_base_A_plus_data_shape(mm, n, m, slice);
        }
        assert(0 <= i < slice.len());
        assert(hp.relators[j] == hnn_relators(data)[i]);
        assert(hnn_relators(data)[i] == hnn_relator(data, i));
        lemma_cs5_vondyck_hnn_relator(mm, n, m, is_S, slice, i);
    }
}

} // verus!
