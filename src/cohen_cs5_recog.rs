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
use crate::benign::{apply_embedding, apply_embedding_symbol, in_generated_subgroup,
    lemma_apply_embedding_concat, lemma_apply_embedding_inverse, lemma_apply_embedding_valid,
    concat_all, factors_from_generators, is_generator_or_inverse};
use crate::homomorphism::{HomomorphismData, apply_hom, apply_hom_symbol, is_valid_homomorphism,
    lemma_hom_preserves_equiv, lemma_hom_respects_inverse};
use crate::phi_l_forward::lemma_apply_embedding_concat_all;
use crate::machine_group::lemma_product_in_subgroup;
use crate::r_prime::lemma_empty_in_subgroup;
use crate::free_basis::{comp_images, lemma_apply_hom_embedding_compose};
use crate::h3_ii::{compose_embeddings, lemma_apply_embedding_compose};
use crate::normal_form_afp_textbook::lemma_subgroup_to_k_word;
use crate::presentation::lemma_equiv_symmetric;
use crate::machine_group::{ModMachine, g_m, g_subgens, g_m_associations, config_word, mod_machine_wf,
    mm_in_H0, lemma_g_m_num_generators, lemma_g_m_associations_valid, lemma_g_m_valid,
    lemma_word_valid_mono, lemma_cancel_pair_equiv_empty, lemma_config_word_valid,
    lemma_apply_embedding_in_subgroup, lemma_in_subgroup_respects_equiv,
    b_m, b_m_upto, mm_terminal, hnn_a_gens, in_TM, in_TMstable,
    lemma_b_m_valid, lemma_b_m_upto_num_generators, lemma_vii_subset, lemma_single_hnn_base_faithful};
use crate::tower_peel::lemma_vi;
use crate::prop_v::lemma_equiv_from_concat_inv_trivial;
use crate::free_basis::{lemma_g_m_data_isomorphic, config_emb, w_to_canon, lemma_config_emb_eq_canw};
use crate::machine_group::{CanonLetter, canw_eval, base_A, lemma_base_A_valid, lemma_canw_eval_valid,
    lemma_no_relator_equiv_implies_freely_equivalent};
use crate::config_reduce::{coord_in, cw_reduce, lemma_in_TM_to_canon, lemma_tfree_coord_restrict,
    lemma_cw_reduce_eval, lemma_cw_reduce_coords};
use crate::r_prime::{lemma_membership_to_canon, lemma_canw_in_config_subgroup, lemma_free_cw_reduce_eval};
use crate::presentation_lemmas::lemma_freely_equivalent_implies_equiv;
use crate::higman_operations::free_group;
use crate::presentation::{lemma_equiv_refl, lemma_equiv_transitive};
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_word_inverse_right};
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
use crate::h3_ii::{recog_data, family_II_assoc};
use crate::h2::{p_assoc, td_word};
use crate::f_free_a1::{betas, lemma_betas_index};
use crate::machine_group::lemma_config_word_zero;
use crate::f_free::is_free_family;
use crate::free_basis::lemma_config_emb_free;

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

// ============================================================================
// Step 3c (C1) — the ρ-reflection: the NON-FREE-base analog of `lemma_intersection_property`.
// CS-4's `lemma_intersection_property` reflects subgroup membership across a FREE family `a_words_F`
// (via `lemma_free_family_injective`). A₊'s base `g_m∗free(d,b)` is non-free, so we use the c-killing
// retraction `ρ` instead: `ρ∘a_col_machine = id` on base words makes `a_col_machine` injective, and
// reflection composes exactly as in CS-4 (subgroup_to_k_word → compose → inject → in_subgroup).
// ============================================================================

/// `apply_hom(ρ, emb(a_col_machine, x)) = x` for any base word `x` (the retraction inverts the
/// inclusion). Generalizes the second half of `lemma_cs5_base_case_faithful` to arbitrary base words.
proof fn lemma_rho_acol_identity_word(mm: ModMachine, n: nat, x: Word)
    requires
        word_valid(x, (g_m(mm).num_generators + n + 1) as nat),
    ensures
        apply_hom(base_retraction(mm, n), apply_embedding(a_col_machine(mm, n), x)) =~= x,
{
    let nk = g_m(mm).num_generators;
    let rho = base_retraction(mm, n);
    let am = a_col_machine(mm, n);
    lemma_machine_col_len(mm, n);
    lemma_base_retraction_valid(mm, n);
    assert(word_valid(x, am.len())) by {
        lemma_word_valid_mono(x, (nk + n + 1) as nat, am.len());
    }
    lemma_apply_hom_embedding_compose(rho, am, x);
    let comp = comp_images(rho, am);
    assert forall|i: int| 0 <= i < nk + n + 1
        implies #[trigger] comp[i] =~= seq![Symbol::Gen(i as nat)] by {
        lemma_comp_rho_acol_identity(mm, n, i);
    }
    lemma_emb_identity_prefix(comp, x, (nk + n + 1) as nat);
}

/// **`a_col_machine` is injective on base words** (faithfulness): two base words with `≡_{h1_base}`-equal
/// `a_col_machine`-images are `≡_{base_A_plus_base}`-equal. The non-free replacement for
/// `lemma_free_family_injective` — via the retraction `ρ` (`apply_hom(ρ, ψ(·)) = id`).
pub proof fn lemma_a_col_machine_injective(mm: ModMachine, n: nat, a: Word, b: Word)
    requires
        word_valid(a, (g_m(mm).num_generators + n + 1) as nat),
        word_valid(b, (g_m(mm).num_generators + n + 1) as nat),
        equiv_in_presentation(h1_base(mm, n),
            apply_embedding(a_col_machine(mm, n), a), apply_embedding(a_col_machine(mm, n), b)),
    ensures
        equiv_in_presentation(base_A_plus_base(mm, n), a, b),
{
    let rho = base_retraction(mm, n);
    let am = a_col_machine(mm, n);
    lemma_base_retraction_valid(mm, n);
    let ia = apply_embedding(am, a);
    let ib = apply_embedding(am, b);
    // ρ pushes the h1_base equiv to a base_A_plus_base equiv of the retracted images.
    lemma_hom_preserves_equiv(rho, ia, ib);
    lemma_rho_acol_identity_word(mm, n, a);            // apply_hom(ρ, ia) = a
    lemma_rho_acol_identity_word(mm, n, b);            // apply_hom(ρ, ib) = b
}

/// **C1 — ρ-reflection (the non-free intersection).** If `emb(a_col_machine, u)` lies in the subgroup
/// `⟨compose_embeddings(a_col_machine, cols)⟩` of `h1_base` (`cols` all base words), then `u` lies in
/// `⟨cols⟩` of `base_A_plus_base`. Mirror of `lemma_intersection_property` with `ρ`-injectivity in
/// place of free-family injectivity. The base-word reflection of a recog pinch-middle membership.
pub proof fn lemma_cs5_middle_reflect(mm: ModMachine, n: nat, cols: Seq<Word>, u: Word)
    requires
        word_valid(u, (g_m(mm).num_generators + n + 1) as nat),
        forall|k: int| 0 <= k < cols.len()
            ==> word_valid(#[trigger] cols[k], (g_m(mm).num_generators + n + 1) as nat),
        in_generated_subgroup(h1_base(mm, n),
            compose_embeddings(a_col_machine(mm, n), cols),
            apply_embedding(a_col_machine(mm, n), u)),
    ensures
        in_generated_subgroup(base_A_plus_base(mm, n), cols, u),
{
    let nk = g_m(mm).num_generators;
    let ng = (nk + n + 1) as nat;
    let am = a_col_machine(mm, n);
    let bp = base_A_plus_base(mm, n);
    let recog_gens = compose_embeddings(am, cols);
    let psi_u = apply_embedding(am, u);
    assert(recog_gens.len() == cols.len());

    // pull ψ(u) back to a preimage word h over the recog gens.
    lemma_subgroup_to_k_word(h1_base(mm, n), recog_gens, psi_u);
    let h = choose|h: Word| word_valid(h, recog_gens.len())
        && equiv_in_presentation(h1_base(mm, n), apply_embedding(recog_gens, h), psi_u);
    assert(word_valid(h, recog_gens.len())
        && equiv_in_presentation(h1_base(mm, n), apply_embedding(recog_gens, h), psi_u));
    assert(word_valid(h, cols.len()));

    // emb(recog_gens, h) = ψ(emb(cols, h)) = ψ(ph).
    lemma_apply_embedding_compose(am, cols, h);
    let ph = apply_embedding(cols, h);
    assert(apply_embedding(recog_gens, h) =~= apply_embedding(am, ph));

    // ψ(ph) ≡_{h1_base} ψ(u); ρ-injectivity ⟹ ph ≡_{base_A_plus_base} u.
    lemma_apply_embedding_valid(cols, h, ng);                    // ph valid over ng
    assert(equiv_in_presentation(h1_base(mm, n),
        apply_embedding(am, ph), apply_embedding(am, u)));
    lemma_a_col_machine_injective(mm, n, ph, u);
    assert(equiv_in_presentation(bp, ph, u));

    // ph ∈ ⟨cols⟩, ph ≡ u ⟹ u ∈ ⟨cols⟩.
    lemma_apply_embedding_in_subgroup(bp, cols, h);
    lemma_in_subgroup_respects_equiv(bp, cols, ph, u);
}

// ============================================================================
// Step 3c (C2 groundwork) — the `d,b`-killing projection `π : base_A_plus_base → g_m`.
// Kills the free factor (b-block `nk..nk+n-1`, d at `nk+n`), fixes the machine gens `0..nk-1`.
// Blueprint §7.1 step 1: reduces a recog pinch-middle that is `∈ ⟨g_subgens,d,b⟩` (the 3d
// `⟨U,d,b,p⟩`-subgroup INVARIANT) `∩ ⟨config:slice⟩` to a g_m element `∈ ⟨g_subgens⟩ ∩ ⟨config:slice⟩`,
// where property (vii)/(vi) + coordinate survival force the H₀-restriction.
// ============================================================================

/// `π : base_A_plus_base → g_m` — machine gen `i<nk ↦ [Gen(i)]`; free gen (`nk ≤ i ≤ nk+n`,
/// the b-block + d) `↦ ε`. (No `p` — `base_A_plus_base` is the HNN BASE, no stable letter.)
pub open spec fn db_projection(mm: ModMachine, n: nat) -> HomomorphismData {
    let nk = g_m(mm).num_generators;
    HomomorphismData {
        source: base_A_plus_base(mm, n),
        target: g_m(mm),
        generator_images: Seq::new((nk + n + 1) as nat, |g: int| {
            if g < nk { seq![Symbol::Gen(g as nat)] } else { empty_word() }
        }),
    }
}

/// `π` fixes a machine word (valid over `nk`): `apply_hom(π, r) = r`. (Mirror of
/// `lemma_rho_fixes_machine_word`; `π`'s first `nk` images are `[Gen(i)]`.)
proof fn lemma_db_proj_fixes_machine_word(mm: ModMachine, n: nat, r: Word)
    requires
        word_valid(r, g_m(mm).num_generators),
    ensures
        apply_hom(db_projection(mm, n), r) =~= r,
{
    let nk = g_m(mm).num_generators;
    let pi = db_projection(mm, n);
    lemma_apply_hom_eq_emb(pi, r);
    assert forall|i: int| 0 <= i < nk
        implies #[trigger] pi.generator_images[i] =~= seq![Symbol::Gen(i as nat)] by {}
    lemma_emb_identity_prefix(pi.generator_images, r, nk);
}

/// `π` fixes a config word `t_β = config_word(β,0)` (a machine word over `3 ≤ nk` gens).
pub proof fn lemma_db_proj_fixes_config(mm: ModMachine, n: nat, beta: nat)
    ensures
        apply_hom(db_projection(mm, n), config_word(beta, 0)) =~= config_word(beta, 0),
{
    let nk = g_m(mm).num_generators;
    lemma_config_word_valid(beta, 0);                       // word_valid(·, 3)
    lemma_g_m_num_generators(mm);                           // nk = 4 + |quads| ≥ 4 > 3
    lemma_word_valid_mono(config_word(beta, 0), 3, nk);
    lemma_db_proj_fixes_machine_word(mm, n, config_word(beta, 0));
}

/// **`π` is a valid homomorphism `base_A_plus_base → g_m`.** Images valid over `nk` (machine gens
/// or `ε`); `base_A_plus_base.relators == g_m.relators` (machine words `< nk`), `π` fixes each, and
/// it is a `g_m` relator ⟹ `≡_{g_m} ε`.
pub proof fn lemma_db_projection_valid(mm: ModMachine, n: nat)
    ensures
        is_valid_homomorphism(db_projection(mm, n)),
{
    let nk = g_m(mm).num_generators;
    let pi = db_projection(mm, n);
    lemma_base_A_plus_base_valid(mm, n);
    lemma_g_m_valid(mm);
    assert(pi.source.num_generators == nk + n + 1);
    assert(pi.generator_images.len() == nk + n + 1);
    assert(pi.target.num_generators == nk);                // g_m(mm).num_generators == nk by def
    // images valid over nk.
    assert forall|i: int| 0 <= i < pi.generator_images.len()
        implies word_valid(#[trigger] pi.generator_images[i], nk) by {
        if i < nk {
            assert(pi.generator_images[i] =~= seq![Symbol::Gen(i as nat)]);
        } else {
            assert(pi.generator_images[i] =~= empty_word());
        }
    }
    // relators map to ≡ ε.
    let gr = g_m(mm).relators;
    assert(pi.source.relators == gr);
    assert forall|i: int| 0 <= i < pi.source.relators.len()
        implies equiv_in_presentation(pi.target, apply_hom(pi, #[trigger] pi.source.relators[i]),
            empty_word()) by {
        assert(pi.source.relators[i] == gr[i]);
        reveal(presentation_valid);
        assert(word_valid(gr[i], nk));
        lemma_db_proj_fixes_machine_word(mm, n, gr[i]);    // apply_hom(π, gr[i]) = gr[i]
        lemma_relator_is_identity(g_m(mm), i);             // gr[i] ≡_{g_m} ε
    }
}

// ============================================================================
// Step 3c-C2 (step 1) — general subgroup-transfer machinery (presentation-agnostic).
// `lemma_hom_maps_subgroup`: a valid hom maps `⟨gens⟩`-membership to `⟨φ(gens)⟩`-membership.
// `lemma_in_subgroup_gens_in_core`: if every generator (and its inverse) already lies in
// `⟨core⟩`, then `⟨gens⟩ ⊆ ⟨core⟩` — used to drop the `ε`-images of `d,b` after projecting.
// ============================================================================

/// `apply_hom` distributes over `concat_all` (via the `apply_embedding` bridge).
proof fn lemma_apply_hom_distributes_concat_all(h: HomomorphismData, factors: Seq<Word>)
    ensures
        apply_hom(h, concat_all(factors))
            =~= concat_all(Seq::new(factors.len(), |k: int| apply_hom(h, factors[k]))),
{
    let imgs = h.generator_images;
    lemma_apply_hom_eq_emb(h, concat_all(factors));
    lemma_apply_embedding_concat_all(imgs, factors);
    let me = Seq::new(factors.len(), |k: int| apply_embedding(imgs, factors[k]));
    let mh = Seq::new(factors.len(), |k: int| apply_hom(h, factors[k]));
    assert(me =~= mh) by {
        assert forall|k: int| 0 <= k < factors.len() implies me[k] =~= mh[k] by {
            lemma_apply_hom_eq_emb(h, factors[k]);
        }
    }
}

/// **General: a valid homomorphism maps subgroup membership to subgroup membership.**
/// `w ∈ ⟨gens⟩` over `h.source` ⟹ `φ(w) ∈ ⟨φ(gens)⟩` over `h.target`.
pub proof fn lemma_hom_maps_subgroup(h: HomomorphismData, gens: Seq<Word>, w: Word)
    requires
        is_valid_homomorphism(h),
        in_generated_subgroup(h.source, gens, w),
    ensures
        in_generated_subgroup(h.target,
            Seq::new(gens.len(), |i: int| apply_hom(h, gens[i])),
            apply_hom(h, w)),
{
    let img_gens = Seq::new(gens.len(), |i: int| apply_hom(h, gens[i]));
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(gens, f)
        && equiv_in_presentation(h.source, concat_all(f), w);
    assert(factors_from_generators(gens, factors)
        && equiv_in_presentation(h.source, concat_all(factors), w));
    let img_factors = Seq::new(factors.len(), |k: int| apply_hom(h, factors[k]));
    // 1. each φ-image factor is a generator-or-inverse of `img_gens`.
    assert(factors_from_generators(img_gens, img_factors)) by {
        assert forall|k: int| 0 <= k < img_factors.len()
            implies is_generator_or_inverse(img_gens, #[trigger] img_factors[k]) by {
            assert(is_generator_or_inverse(gens, factors[k]));
            let j = choose|j: int| 0 <= j < gens.len()
                && (factors[k] == gens[j] || factors[k] == inverse_word(gens[j]));
            assert(0 <= j < gens.len()
                && (factors[k] == gens[j] || factors[k] == inverse_word(gens[j])));
            assert(img_factors[k] == apply_hom(h, factors[k]));
            assert(img_gens[j] == apply_hom(h, gens[j]));
            if factors[k] == gens[j] {
            } else {
                lemma_hom_respects_inverse(h, gens[j]);
            }
        }
    }
    // 2. concat_all(img_factors) = φ(concat_all(factors)).
    lemma_apply_hom_distributes_concat_all(h, factors);
    // 3. φ preserves equiv.
    lemma_hom_preserves_equiv(h, concat_all(factors), w);
    assert(factors_from_generators(img_gens, img_factors)
        && equiv_in_presentation(h.target, concat_all(img_factors), apply_hom(h, w)));
}

/// Closure: a `concat_all` of `⟨core⟩`-members lies in `⟨core⟩`.
proof fn lemma_concat_all_in_subgroup(p: Presentation, core: Seq<Word>, factors: Seq<Word>)
    requires
        presentation_valid(p),
        forall|j: int| 0 <= j < factors.len()
            ==> in_generated_subgroup(p, core, #[trigger] factors[j]),
    ensures
        in_generated_subgroup(p, core, concat_all(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word()) by { reveal_with_fuel(concat_all, 1); }
        lemma_empty_in_subgroup(p, core);
    } else {
        let rest = factors.drop_first();
        assert forall|j: int| 0 <= j < rest.len()
            implies in_generated_subgroup(p, core, #[trigger] rest[j]) by {
            assert(rest[j] == factors[j + 1]);
        }
        lemma_concat_all_in_subgroup(p, core, rest);
        assert(in_generated_subgroup(p, core, factors[0]));
        assert(concat_all(factors) =~= factors.first() + concat_all(rest)) by {
            reveal_with_fuel(concat_all, 1);
        }
        lemma_product_in_subgroup(p, core, factors.first(), concat_all(rest));
    }
}

/// **General: drop redundant generators.** If every `gens[j]` and its inverse already lie in
/// `⟨core⟩`, then `w ∈ ⟨gens⟩ ⟹ w ∈ ⟨core⟩`.
pub proof fn lemma_in_subgroup_gens_in_core(p: Presentation, gens: Seq<Word>, core: Seq<Word>, w: Word)
    requires
        presentation_valid(p),
        in_generated_subgroup(p, gens, w),
        forall|j: int| 0 <= j < gens.len() ==>
            in_generated_subgroup(p, core, #[trigger] gens[j])
            && in_generated_subgroup(p, core, inverse_word(gens[j])),
    ensures
        in_generated_subgroup(p, core, w),
{
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(gens, f)
        && equiv_in_presentation(p, concat_all(f), w);
    assert(factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), w));
    assert forall|k: int| 0 <= k < factors.len()
        implies in_generated_subgroup(p, core, #[trigger] factors[k]) by {
        assert(is_generator_or_inverse(gens, factors[k]));
        let j = choose|j: int| 0 <= j < gens.len()
            && (factors[k] == gens[j] || factors[k] == inverse_word(gens[j]));
        assert(0 <= j < gens.len()
            && (factors[k] == gens[j] || factors[k] == inverse_word(gens[j])));
    }
    lemma_concat_all_in_subgroup(p, core, factors);
    lemma_in_subgroup_respects_equiv(p, core, concat_all(factors), w);
}

// ============================================================================
// Step 3c-C2 (step 1, specialized) — the `⟨g_subgens, d, b⟩` generating set + the projection
// application. `π` kills the free `d,b`-block (uniform tail `[Gen(nk+j)]_{j=0..n}` = b-block then
// d) and fixes the machine gens, so a machine word in `⟨g_subgens, d, b⟩` over `base_A_plus_base`
// lands in `⟨g_subgens⟩` over `g_m`.
// ============================================================================

/// The base subgroup `⟨g_subgens, d, b⟩` of `base_A_plus_base` (the 3d `⟨U,d,b,p⟩`-invariant's
/// base part, no `p`). Tail entry `j` is the free gen `[Gen(nk+j)]` (b-block `j<n`, d at `j=n`).
pub open spec fn ublock_db_gens(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    g_subgens(mm) + Seq::new((n + 1) as nat, |j: int| seq![Symbol::Gen((nk + j) as nat)])
}

/// `π` kills a free-block single gen `[Gen(idx)]`, `nk ≤ idx < nk+n+1` ⟹ `apply_hom(π,·) = ε`.
proof fn lemma_db_proj_kills_high(mm: ModMachine, n: nat, idx: nat)
    requires
        g_m(mm).num_generators <= idx,
        idx < g_m(mm).num_generators + n + 1,
    ensures
        apply_hom(db_projection(mm, n), seq![Symbol::Gen(idx)]) =~= empty_word(),
{
    let pi = db_projection(mm, n);
    let w: Word = seq![Symbol::Gen(idx)];
    assert(w.len() == 1 && w.first() == Symbol::Gen(idx) && w.drop_first() =~= empty_word());
    reveal_with_fuel(apply_hom, 2);
    assert(apply_hom(pi, w.drop_first()) =~= empty_word());
    assert(apply_hom_symbol(pi, w.first()) == pi.generator_images[idx as int]);
    assert(pi.generator_images[idx as int] =~= empty_word());      // idx ≥ nk branch of db_projection
    lemma_concat_empty_right(pi.generator_images[idx as int]);
}

/// A generator and its inverse both lie in the subgroup they generate.
proof fn lemma_gen_and_inv_in_subgroup(p: Presentation, gens: Seq<Word>, j: int)
    requires
        0 <= j < gens.len(),
    ensures
        in_generated_subgroup(p, gens, gens[j]),
        in_generated_subgroup(p, gens, inverse_word(gens[j])),
{
    let g: Word = seq![Symbol::Gen(j as nat)];
    let gi: Word = seq![Symbol::Inv(j as nat)];
    assert(word_valid(g, gens.len() as nat) && word_valid(gi, gens.len() as nat));
    lemma_apply_embedding_in_subgroup(p, gens, g);
    lemma_emb_single_gen(gens, j as nat);
    lemma_apply_embedding_in_subgroup(p, gens, gi);
    lemma_emb_single_inv_gen(gens, j as nat);
}

/// **CS-5c step 1 (projection application).** A machine word `cfg_rep` (valid over `nk`) lying in
/// `⟨g_subgens, d, b⟩` over `base_A_plus_base` lies in `⟨g_subgens⟩` over `g_m`.
pub proof fn lemma_cs5_project_to_gsubgens(mm: ModMachine, n: nat, cfg_rep: Word)
    requires
        word_valid(cfg_rep, g_m(mm).num_generators),
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), cfg_rep),
    ensures
        in_generated_subgroup(g_m(mm), g_subgens(mm), cfg_rep),
{
    let nk = g_m(mm).num_generators;
    let pi = db_projection(mm, n);
    let ub = ublock_db_gens(mm, n);
    let gs = g_subgens(mm);
    lemma_db_projection_valid(mm, n);
    lemma_g_m_valid(mm);
    lemma_g_m_num_generators(mm);
    lemma_g_m_associations_valid(mm);

    // 1. transfer membership through π; π fixes the machine word cfg_rep.
    lemma_hom_maps_subgroup(pi, ub, cfg_rep);
    let img_gens = Seq::new(ub.len(), |i: int| apply_hom(pi, ub[i]));
    lemma_db_proj_fixes_machine_word(mm, n, cfg_rep);
    assert(in_generated_subgroup(g_m(mm), img_gens, cfg_rep));     // π.target == g_m, π(cfg_rep)=cfg_rep

    // 2. every img_gens[j] (and inverse) lies in ⟨gs⟩ — g_subgens entries are fixed, d/b → ε.
    assert(gs.len() == g_m_associations(mm).len());
    assert forall|j: int| 0 <= j < img_gens.len()
        implies in_generated_subgroup(g_m(mm), gs, #[trigger] img_gens[j])
            && in_generated_subgroup(g_m(mm), gs, inverse_word(img_gens[j])) by {
        assert(img_gens[j] == apply_hom(pi, ub[j]));
        if j < gs.len() {
            assert(ub[j] == gs[j]);                                // prefix index of `gs + tail`
            assert(gs[j] == g_m_associations(mm)[j].1);
            lemma_word_valid_mono(gs[j], (3 + mm.quads.len()) as nat, nk);
            lemma_db_proj_fixes_machine_word(mm, n, gs[j]);        // π fixes gs[j]
            assert(img_gens[j] =~= gs[j]);
            lemma_gen_and_inv_in_subgroup(g_m(mm), gs, j);
        } else {
            let k = j - gs.len();
            assert(0 <= k < n + 1);
            assert(ub[j] =~= seq![Symbol::Gen((nk + k) as nat)]);  // tail index
            lemma_db_proj_kills_high(mm, n, (nk + k) as nat);
            assert(img_gens[j] =~= empty_word());
            lemma_empty_in_subgroup(g_m(mm), gs);
            assert(inverse_word(img_gens[j]) =~= empty_word());
            lemma_empty_in_subgroup(g_m(mm), gs);
        }
    }
    // 3. drop the ε-images, landing in ⟨gs⟩.
    lemma_in_subgroup_gens_in_core(g_m(mm), img_gens, gs, cfg_rep);
}

// ============================================================================
// Step 3c-C2 (step 2) — `cfg_rep ∈ ⟨g_subgens⟩ over g_m` ⟹ `in_TM(cfg_rep)`.
// Base-faithfulness of the `g_m` HNN (`b_m`-words) lands the membership in `b_m`, then the
// Layer-1 chain property (vii) (`lemma_vii_subset`) + property (vi) (`lemma_vi`).
// ============================================================================

/// Two-word base-faithfulness of `g_m = HNN(b_m, g_m_associations)`: `b_m`-words equiv over `g_m`
/// are equiv over `b_m`. (Mirror of `lemma_quad_base_faithful` at the `k`-layer.)
pub proof fn lemma_g_m_base_faithful_2word(mm: ModMachine, w1: Word, w2: Word)
    requires
        mod_machine_wf(mm),
        word_valid(w1, b_m(mm).num_generators),
        word_valid(w2, b_m(mm).num_generators),
        equiv_in_presentation(g_m(mm), w1, w2),
    ensures
        equiv_in_presentation(b_m(mm), w1, w2),
{
    let data = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    let hp = g_m(mm);
    let p = b_m(mm);
    let ng = p.num_generators;
    lemma_b_m_valid(mm);
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
    assert(p == b_m_upto(mm, mm.quads.len()));
    assert(ng == (3 + mm.quads.len()) as nat);
    lemma_g_m_associations_valid(mm);
    assert(hnn_data_valid(data));
    lemma_g_m_data_isomorphic(mm);
    assert(hp == hnn_presentation(data));
    let iw2 = inverse_word(w2);
    lemma_inverse_word_valid(w2, ng);
    lemma_concat_word_valid(w1, iw2, ng);
    // (a) w1 ≡_hp w2 ⟹ w1·w2⁻¹ ≡_hp ε
    lemma_equiv_concat_left(hp, w1, w2, iw2);
    lemma_word_inverse_right(hp, w2);
    lemma_equiv_transitive(hp, w1 + iw2, w2 + iw2, empty_word());
    // single-layer base-faithful: w1·w2⁻¹ ≡_{b_m} ε
    lemma_single_hnn_base_faithful(data, w1 + iw2);
    // (b) w1·w2⁻¹ ≡_p ε ⟹ w1 ≡_p w2
    lemma_equiv_from_concat_inv_trivial(p, w1, w2);
}

/// A `concat_all` of generator-or-inverse factors is valid over `ng` when every generator is.
proof fn lemma_factors_concat_valid(gens: Seq<Word>, factors: Seq<Word>, ng: nat)
    requires
        factors_from_generators(gens, factors),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], ng),
    ensures
        word_valid(concat_all(factors), ng),
    decreases factors.len(),
{
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word()) by { reveal_with_fuel(concat_all, 1); }
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k]) by {
                assert(rest[k] == factors[k + 1]);
            }
        }
        lemma_factors_concat_valid(gens, rest, ng);
        assert(is_generator_or_inverse(gens, factors[0]));
        let j = choose|j: int| 0 <= j < gens.len()
            && (factors[0] == gens[j] || factors[0] == inverse_word(gens[j]));
        assert(0 <= j < gens.len()
            && (factors[0] == gens[j] || factors[0] == inverse_word(gens[j])));
        if factors[0] != gens[j] {
            lemma_inverse_word_valid(gens[j], ng);
        }
        assert(concat_all(factors) =~= factors.first() + concat_all(rest)) by {
            reveal_with_fuel(concat_all, 1);
        }
        lemma_concat_word_valid(factors.first(), concat_all(rest), ng);
    }
}

/// **CS-5c step 2.** A config representative (a `{t,x,y}`-word) lying in `⟨g_subgens⟩` over `g_m`
/// lies in `T(M)` over `base_A`.
pub proof fn lemma_cs5_cfg_in_TM(mm: ModMachine, cfg_rep: Word)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        word_valid(cfg_rep, 3),
        in_generated_subgroup(g_m(mm), g_subgens(mm), cfg_rep),
    ensures
        in_TM(mm, cfg_rep),
{
    let gs = g_subgens(mm);
    let bm = b_m(mm);
    lemma_b_m_valid(mm);
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
    let bng = bm.num_generators;
    assert(bng == (3 + mm.quads.len()) as nat);
    lemma_g_m_associations_valid(mm);

    // extract a g_subgens factorisation; v = concat_all(factors) is a b_m word.
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(gs, f)
        && equiv_in_presentation(g_m(mm), concat_all(f), cfg_rep);
    assert(factors_from_generators(gs, factors)
        && equiv_in_presentation(g_m(mm), concat_all(factors), cfg_rep));
    let v = concat_all(factors);
    assert forall|i: int| 0 <= i < gs.len() implies word_valid(#[trigger] gs[i], bng) by {
        assert(gs[i] == g_m_associations(mm)[i].1);
    }
    lemma_factors_concat_valid(gs, factors, bng);
    lemma_word_valid_mono(cfg_rep, 3, bng);

    // base-faithful g_m → b_m: v ≡_{b_m} cfg_rep, so cfg_rep ∈ ⟨g_subgens⟩ over b_m.
    lemma_g_m_base_faithful_2word(mm, v, cfg_rep);
    lemma_equiv_refl(bm, v);
    assert(in_generated_subgroup(bm, gs, v));               // witness `factors` (concat_all = v ≡ v)
    lemma_in_subgroup_respects_equiv(bm, gs, v, cfg_rep);

    // diagonal associations: g_subgens == hnn_a_gens(gdata).
    let gdata = HNNData { base: bm, associations: g_m_associations(mm) };
    assert(gs =~= hnn_a_gens(gdata)) by {
        assert(gs.len() == hnn_a_gens(gdata).len());
        assert forall|i: int| 0 <= i < gs.len() implies gs[i] == hnn_a_gens(gdata)[i] by {
            assert(gs[i] == g_m_associations(mm)[i].1);
            assert(hnn_a_gens(gdata)[i] == g_m_associations(mm)[i].0);
            assert(g_m_associations(mm)[i].0 == g_m_associations(mm)[i].1);
        }
    }
    assert(in_generated_subgroup(bm, hnn_a_gens(gdata), cfg_rep));
    lemma_vii_subset(mm, cfg_rep);                          // ∈ ⟨T(M), rᵢ, lⱼ⟩
    lemma_vi(mm, cfg_rep);                                  // ∈ T(M)
}

// ============================================================================
// Step 3c-C2 (step 3) — the product coordinate-survival.  A CanonLetter list `cs` whose
// evaluation lies in `T(M)` has every surviving (post-`cw_reduce`) coordinate in `H₀`.
// Generalizes `lemma_in_TM_config_implies_H0` from a single config to a product, by applying the
// E2.E coordinate-survival core (`lemma_tfree_coord_restrict`) at each reduced coordinate.
// ============================================================================

/// **CS-5c step 3.** `canw_eval(cs) ∈ T(M)` ⟹ every coordinate of `cw_reduce(cs)` is an `H₀` config.
pub proof fn lemma_cs5_canon_coords_h0(mm: ModMachine, cs: Seq<CanonLetter>)
    requires
        in_TM(mm, canw_eval(cs)),
    ensures
        forall|j: int| 0 <= j < cw_reduce(cs).len() ==>
            mm_in_H0(mm, (#[trigger] cw_reduce(cs)[j]).r as nat, cw_reduce(cs)[j].s as nat),
{
    let g = canw_eval(cs);
    let red = cw_reduce(cs);
    lemma_base_A_valid();
    let p_canon = lemma_in_TM_to_canon(mm, g);              // canw(p_canon) ≡_A g, coords ∈ H₀
    lemma_canw_eval_valid(p_canon);
    lemma_equiv_symmetric(base_A(), canw_eval(p_canon), g);
    assert(equiv_in_presentation(base_A(), canw_eval(cs), canw_eval(p_canon)));
    assert forall|j: int| 0 <= j < red.len() implies
        mm_in_H0(mm, (#[trigger] red[j]).r as nat, red[j].s as nat) by {
        assert(coord_in(red, red[j].r, red[j].s));          // red[j] is its own witness
        lemma_tfree_coord_restrict(cs, p_canon, red[j].r, red[j].s);
        let k = choose|k: int| 0 <= k < p_canon.len()
            && p_canon[k].r == red[j].r && p_canon[k].s == red[j].s;
        assert(0 <= k < p_canon.len() && p_canon[k].r == red[j].r && p_canon[k].s == red[j].s);
        assert(mm_in_H0(mm, p_canon[k].r as nat, p_canon[k].s as nat)
            && p_canon[k].r >= 0 && p_canon[k].s >= 0);     // from lemma_in_TM_to_canon
        assert(p_canon[k].r as nat == red[j].r as nat && p_canon[k].s as nat == red[j].s as nat);
    }
}

// ============================================================================
// Step 3c-C2 (step 4) — reconstruction + assembly of `lemma_cs5_middle_h0_restrict`.
// `h0_filter` keeps the `slice` indices whose config is `H₀`; the reconstruction rebuilds the
// reduced canon as a `config_emb(h0_filter)` product over `free_group(3)` and lifts it (free
// reduction is sound in any presentation) to `base_A_plus_base`.
// ============================================================================

/// The `H₀`-restriction of a `slice`: the indices `β ∈ slice` with `(β,0) ∈ H₀`.
pub open spec fn h0_filter(mm: ModMachine, slice: Seq<nat>) -> Seq<nat>
    decreases slice.len(),
{
    if slice.len() == 0 {
        Seq::<nat>::empty()
    } else if mm_in_H0(mm, slice[0], 0) {
        seq![slice[0]] + h0_filter(mm, slice.drop_first())
    } else {
        h0_filter(mm, slice.drop_first())
    }
}

/// `β ∈ slice ∧ (β,0)∈H₀ ⟹ β ∈ h0_filter(slice)`.
proof fn lemma_h0_filter_contains(mm: ModMachine, slice: Seq<nat>, b: nat)
    requires
        slice.contains(b),
        mm_in_H0(mm, b, 0),
    ensures
        exists|k: int| 0 <= k < h0_filter(mm, slice).len() && h0_filter(mm, slice)[k] == b,
    decreases slice.len(),
{
    let hf = h0_filter(mm, slice);
    if slice.len() == 0 {
        assert(!slice.contains(b));
    } else if slice[0] == b {
        assert(mm_in_H0(mm, slice[0], 0));
        assert(hf =~= seq![slice[0]] + h0_filter(mm, slice.drop_first()));
        assert(hf[0] == b);                                // k = 0
    } else {
        let rest = slice.drop_first();
        assert(rest.contains(b)) by {
            let i = choose|i: int| 0 <= i < slice.len() && slice[i] == b;
            assert(0 <= i < slice.len() && slice[i] == b);
            assert(i != 0);
            assert(rest[i - 1] == slice[i]);
        }
        lemma_h0_filter_contains(mm, rest, b);
        let kr = choose|kr: int| 0 <= kr < h0_filter(mm, rest).len() && h0_filter(mm, rest)[kr] == b;
        assert(0 <= kr < h0_filter(mm, rest).len() && h0_filter(mm, rest)[kr] == b);
        if mm_in_H0(mm, slice[0], 0) {
            assert(hf =~= seq![slice[0]] + h0_filter(mm, rest));
            assert(hf[kr + 1] == h0_filter(mm, rest)[kr]);    // shifted witness
        } else {
            assert(hf =~= h0_filter(mm, rest));
            assert(hf[kr] == h0_filter(mm, rest)[kr]);
        }
    }
}

/// **Membership lift** `free_group(k) → p`: free reduction is sound in any presentation, so a
/// `⟨gens⟩`-membership over a free group transfers to any presentation (over which `gens`/`w` are valid).
proof fn lemma_free_subgroup_to_pres(p: Presentation, k: nat, gens: Seq<Word>, w: Word)
    requires
        presentation_valid(p),
        in_generated_subgroup(free_group(k), gens, w),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], p.num_generators),
        word_valid(w, p.num_generators),
    ensures
        in_generated_subgroup(p, gens, w),
{
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(gens, f)
        && equiv_in_presentation(free_group(k), concat_all(f), w);
    assert(factors_from_generators(gens, factors)
        && equiv_in_presentation(free_group(k), concat_all(factors), w));
    lemma_factors_concat_valid(gens, factors, p.num_generators);
    assert(free_group(k).relators.len() == 0);
    lemma_no_relator_equiv_implies_freely_equivalent(free_group(k), concat_all(factors), w);
    lemma_freely_equivalent_implies_equiv(p, concat_all(factors), w);
    assert(in_generated_subgroup(p, gens, w));             // witness `factors`
}

/// **CS-5c 3c-C2 — THE H₀-restriction intersection lemma.** A base word `mid_w` of
/// `base_A_plus_base` that lies in BOTH `⟨g_subgens, d, b⟩` (the 3d `⟨U,d,b,p⟩`-invariant, no `p`)
/// and `⟨config(β,0) : β ∈ slice⟩` actually lies in `⟨config(β,0) : β ∈ slice ∧ (β,0)∈H₀⟩`.
/// (E2.E generalised from a single config to a product — `docs/cohen-cs5-blueprint.md` §7.1.)
pub proof fn lemma_cs5_middle_h0_restrict(mm: ModMachine, n: nat, slice: Seq<nat>, mid_w: Word)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), mid_w),
        in_generated_subgroup(base_A_plus_base(mm, n), config_emb(slice), mid_w),
    ensures
        in_generated_subgroup(base_A_plus_base(mm, n), config_emb(h0_filter(mm, slice)), mid_w),
{
    let nk = g_m(mm).num_generators;
    let bp = base_A_plus_base(mm, n);
    let ng1 = (nk + n + 1) as nat;
    lemma_g_m_num_generators(mm);
    lemma_g_m_valid(mm);
    lemma_base_A_plus_base_valid(mm, n);
    assert(bp.num_generators == ng1);

    // ---- the config representative cfg_rep = canw_eval(cs), ≡_bp mid_w ----
    let cfactors = choose|f: Seq<Word>| #[trigger] factors_from_generators(config_emb(slice), f)
        && equiv_in_presentation(bp, concat_all(f), mid_w);
    assert(factors_from_generators(config_emb(slice), cfactors)
        && equiv_in_presentation(bp, concat_all(cfactors), mid_w));
    let cfg_rep = concat_all(cfactors);
    let cs = lemma_membership_to_canon(slice, cfactors);
    assert(cfg_rep =~= canw_eval(cs));

    // cfg_rep valid over {t,x,y}=3.
    assert forall|i: int| 0 <= i < config_emb(slice).len()
        implies word_valid(#[trigger] config_emb(slice)[i], 3) by {
        assert(config_emb(slice)[i] == config_word(slice[i], 0));
        lemma_config_word_valid(slice[i], 0);
    }
    lemma_factors_concat_valid(config_emb(slice), cfactors, 3);
    lemma_word_valid_mono(cfg_rep, 3, nk);

    // ---- step 1: cfg_rep ∈ ⟨g_subgens⟩ over g_m ----
    lemma_equiv_symmetric(bp, cfg_rep, mid_w);
    lemma_in_subgroup_respects_equiv(bp, ublock_db_gens(mm, n), mid_w, cfg_rep);
    lemma_cs5_project_to_gsubgens(mm, n, cfg_rep);

    // ---- step 2: in_TM(cfg_rep) ----
    lemma_cs5_cfg_in_TM(mm, cfg_rep);

    // ---- step 3: every cw_reduce(cs) coordinate is H₀ ----
    assert(in_TM(mm, canw_eval(cs)));                      // cfg_rep =~= canw_eval(cs)
    lemma_cs5_canon_coords_h0(mm, cs);

    // ---- step 4: reconstruct over free_group(3) (coords ∈ h0_filter), lift to bp ----
    let hf = h0_filter(mm, slice);
    let red = cw_reduce(cs);
    lemma_cw_reduce_coords(cs);
    assert forall|i: int| 0 <= i < red.len() implies {
        &&& (#[trigger] red[i]).s == 0
        &&& (exists|kk: int| 0 <= kk < hf.len() && hf[kk] as int == red[i].r)
    } by {
        assert(coord_in(cs, red[i].r, red[i].s));
        let j = choose|j: int| 0 <= j < cs.len() && cs[j].r == red[i].r && cs[j].s == red[i].s;
        assert(0 <= j < cs.len() && cs[j].r == red[i].r && cs[j].s == red[i].s);
        assert(cs[j].s == 0);                              // from lemma_membership_to_canon
        let m = choose|m: int| 0 <= m < slice.len() && slice[m] as int == cs[j].r;
        assert(0 <= m < slice.len() && slice[m] as int == cs[j].r);
        assert(red[i].s == 0 && red[i].r == slice[m] as int);
        assert(mm_in_H0(mm, red[i].r as nat, red[i].s as nat));   // step 3
        assert(red[i].r as nat == slice[m]);
        assert(mm_in_H0(mm, slice[m], 0));
        assert(slice.contains(slice[m]));
        lemma_h0_filter_contains(mm, slice, slice[m]);
        let kk0 = choose|kk: int| 0 <= kk < hf.len() && hf[kk] == slice[m];
        assert(0 <= kk0 < hf.len() && hf[kk0] == slice[m] && hf[kk0] as int == red[i].r);
    }
    lemma_canw_in_config_subgroup(hf, 0, red);             // ∈ ⟨config_emb(hf)⟩ over free_group(3)

    assert forall|i: int| 0 <= i < cs.len() implies (#[trigger] cs[i]).s == 0 by {}
    lemma_free_cw_reduce_eval(0, cs);                      // canw(red) ≡ canw(cs) over free_group(3)
    lemma_in_subgroup_respects_equiv(free_group(3), config_emb(hf), canw_eval(red), cfg_rep);

    // ---- lift free_group(3) → bp, then respects_equiv to mid_w ----
    assert forall|i: int| 0 <= i < config_emb(hf).len()
        implies word_valid(#[trigger] config_emb(hf)[i], ng1) by {
        assert(config_emb(hf)[i] == config_word(hf[i], 0));
        lemma_config_word_valid(hf[i], 0);
        lemma_word_valid_mono(config_word(hf[i], 0), 3, ng1);
    }
    lemma_word_valid_mono(cfg_rep, 3, ng1);
    lemma_free_subgroup_to_pres(bp, 3, config_emb(hf), cfg_rep);
    lemma_in_subgroup_respects_equiv(bp, config_emb(hf), cfg_rep, mid_w);
}

// ============================================================================
// Brick A (3d) — the recog↔base_A_plus column correspondence.
// `recog_data(alphas)` a-col = `compose_embeddings(a_col_machine, config_emb(betas))`,
// b-col = `compose_embeddings(a_col_machine, assoc_rhs_emb(betas))`.  These are the
// `recog_gens = compose(a_col_machine, base_A_plus cols)` hypotheses that C1
// (`lemma_cs5_middle_reflect`) needs to reflect a recog-pinch middle to the base_A_plus columns.
// Mirror of CS-4 `lemma_a_col_correspondence`/`lemma_b_col_correspondence` (with a_col_machine in
// place of a_words_F, config_emb/assoc_rhs_emb over `betas` in place of the pa columns).
// ============================================================================

/// The machine-scheme b-column generating sequence: `assoc_rhs_machine(β)` for each `β` in `slice`.
pub open spec fn assoc_rhs_emb(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>) -> Seq<Word> {
    Seq::new(slice.len(), |k: int| assoc_rhs_machine(mm, n, m, slice[k]))
}

/// `recog_data`'s a-column at index `k` (over `betas`) is `config(betas[k],0)`: head `k=0` is the
/// `p_assoc` `[Gen0] = config(0,0)`; `k≥1` is the family-(II) `config(alphas[k-1],0)`.
proof fn lemma_cs5_recog_acol_entry(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, k: int)
    requires
        0 <= k < betas(alphas).len(),
    ensures
        recog_data(mm, n, m, alphas).associations[k].0 =~= config_word(betas(alphas)[k], 0),
{
    let nk = g_m(mm).num_generators;
    let bet = betas(alphas);
    let rd = recog_data(mm, n, m, alphas);
    lemma_betas_index(alphas);
    let pa = p_assoc(nk, n);
    let fa = family_II_assoc(mm, n, m, alphas);
    assert(rd.associations =~= pa + fa);
    assert(pa.len() == 1);
    if k == 0 {
        assert(bet[0] == 0);
        assert(rd.associations[0] == pa[0]);
        assert(pa[0].0 == seq![Symbol::Gen(0)]);
        lemma_config_word_zero();                            // config(0,0) =~= [Gen0]
    } else {
        assert(bet[k] == alphas[k - 1]);
        assert(rd.associations[k] == fa[k - 1]);
        assert(fa[k - 1].0 == config_word(alphas[k - 1], 0));
    }
}

/// `recog_data`'s b-column at index `k` (over `betas`) is `family_II_rhs(betas[k])`: head `k=0` is
/// `td_word = family_II_rhs(0)`; `k≥1` is `family_II_rhs(alphas[k-1])`.
proof fn lemma_cs5_recog_bcol_entry(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, k: int)
    requires
        2 * n < m,
        0 <= k < betas(alphas).len(),
    ensures
        recog_data(mm, n, m, alphas).associations[k].1 =~= family_II_rhs(mm, n, m, betas(alphas)[k]),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bet = betas(alphas);
    let rd = recog_data(mm, n, m, alphas);
    lemma_betas_index(alphas);
    let pa = p_assoc(nk, n);
    let fa = family_II_assoc(mm, n, m, alphas);
    assert(rd.associations =~= pa + fa);
    assert(pa.len() == 1);
    if k == 0 {
        assert(bet[0] == 0);
        assert(rd.associations[0] == pa[0]);
        assert(pa[0].1 == td_word(nk, n));
        // family_II_rhs(0) =~= td_word:  config(0,0)=[Gen0], w_b(_,0)=ε.
        lemma_config_word_zero();
        assert(w_b(b_base(nk, n), n, m, 0) =~= empty_word());
        assert(family_II_rhs(mm, n, m, 0)
            =~= (seq![Symbol::Gen(0)] + empty_word()) + seq![Symbol::Gen(d_idx(nk, n))]);
        assert(td_word(nk, n) == seq![Symbol::Gen(0), Symbol::Gen(d_idx(nk, n))]);
    } else {
        assert(bet[k] == alphas[k - 1]);
        assert(rd.associations[k] == fa[k - 1]);
        assert(fa[k - 1].1 == family_II_rhs(mm, n, m, alphas[k - 1]));
    }
}

/// **Brick A (a-side):** `recog`'s a-column equals `compose_embeddings(a_col_machine, config_emb(betas))`.
/// (Entry-wise: both are `config(betas[k],0)`, and `a_col_machine` fixes config — a machine word.)
pub proof fn lemma_cs5_a_col_correspondence(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    ensures
        Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                 |k: int| recog_data(mm, n, m, alphas).associations[k].0)
        =~= compose_embeddings(a_col_machine(mm, n), config_emb(betas(alphas))),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bet = betas(alphas);
    let rd = recog_data(mm, n, m, alphas);
    let rcol = Seq::new(rd.associations.len(), |k: int| rd.associations[k].0);
    let comp = compose_embeddings(a_col_machine(mm, n), config_emb(bet));
    lemma_betas_index(alphas);
    assert(rd.associations.len() == bet.len());
    assert(config_emb(bet).len() == bet.len());
    assert(comp.len() == bet.len());
    assert forall|k: int| 0 <= k < bet.len() implies rcol[k] =~= comp[k] by {
        lemma_cs5_recog_acol_entry(mm, n, m, alphas, k);     // rcol[k] =~= config(bet[k],0)
        assert(comp[k] == apply_embedding(a_col_machine(mm, n), config_emb(bet)[k]));
        assert(config_emb(bet)[k] == config_word(bet[k], 0));
        // a_col_machine fixes config(bet[k],0) (machine word over 3 ≤ nk).
        lemma_config_word_valid(bet[k], 0);
        lemma_word_valid_mono(config_word(bet[k], 0), 3, nk);
        lemma_a_col_machine_fixes_machine_word(mm, n, config_word(bet[k], 0));
    }
}

/// **Brick A (b-side):** `recog`'s b-column equals `compose_embeddings(a_col_machine, assoc_rhs_emb(betas))`.
/// (Entry-wise: `recog`'s is `family_II_rhs(betas[k])`, `assoc_rhs_emb`'s is `assoc_rhs_machine(betas[k])`,
/// and `a_col_machine` carries `assoc_rhs_machine ↦ family_II_rhs` — `lemma_a_col_machine_assoc_rhs`.)
pub proof fn lemma_cs5_b_col_correspondence(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                 |k: int| recog_data(mm, n, m, alphas).associations[k].1)
        =~= compose_embeddings(a_col_machine(mm, n), assoc_rhs_emb(mm, n, m, betas(alphas))),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bet = betas(alphas);
    let rd = recog_data(mm, n, m, alphas);
    let rcol = Seq::new(rd.associations.len(), |k: int| rd.associations[k].1);
    let comp = compose_embeddings(a_col_machine(mm, n), assoc_rhs_emb(mm, n, m, bet));
    lemma_betas_index(alphas);
    assert(rd.associations.len() == bet.len());
    assert(assoc_rhs_emb(mm, n, m, bet).len() == bet.len());
    assert(comp.len() == bet.len());
    assert forall|k: int| 0 <= k < bet.len() implies rcol[k] =~= comp[k] by {
        lemma_cs5_recog_bcol_entry(mm, n, m, alphas, k);     // rcol[k] =~= family_II_rhs(bet[k])
        assert(numbers_word(n, m, bet[k])) by {
            if k == 0 { assert(bet[0] == 0); } else { assert(bet[k] == alphas[k - 1]); }
        }
        assert(comp[k] == apply_embedding(a_col_machine(mm, n), assoc_rhs_emb(mm, n, m, bet)[k]));
        assert(assoc_rhs_emb(mm, n, m, bet)[k] == assoc_rhs_machine(mm, n, m, bet[k]));
        lemma_a_col_machine_assoc_rhs(mm, n, m, bet[k]);     // → family_II_rhs(bet[k])
    }
}

// ============================================================================
// Brick C (3d) — the B-SIDE H₀-restriction `C2-b` (`lemma_cs5_middle_h0_restrict_b`).
// `mid ∈ ⟨ublock_db_gens⟩ ∩ ⟨assoc_rhs_emb(slice)⟩ ⟹ mid ∈ ⟨assoc_rhs_emb(h0_filter(slice))⟩`.
// Route (blueprint §7.3): pull a coord word `u` over the b-gens (`lemma_subgroup_to_k_word`); `π`
// (d,b-kill, `db_projection`) maps the assoc product to the config product `cw = emb(config_emb,u)`
// (`π∘assoc_rhs = config`); `cw ∈ ⟨g_subgens⟩` + a-side **C2** ⟹ `cw ∈ ⟨config_emb(h0_filter)⟩`;
// `config_emb(slice)` FREE (over g_m) + the intersection property (`lemma_intersection_property`)
// restrict `u` to the `h0_filter` positions `⟨h0_sel⟩`; carry `u` back through `assoc_rhs_emb`.
// ============================================================================

/// Generic: `apply_hom` distributes over a two-part concat (via the `apply_embedding` bridge).
proof fn lemma_apply_hom_concat(h: HomomorphismData, a: Word, b: Word)
    ensures
        apply_hom(h, a + b) =~= concat(apply_hom(h, a), apply_hom(h, b)),
{
    let imgs = h.generator_images;
    lemma_apply_hom_eq_emb(h, a + b);
    lemma_apply_hom_eq_emb(h, a);
    lemma_apply_hom_eq_emb(h, b);
    lemma_apply_embedding_concat(imgs, a, b);
}

/// `π` kills a single `alphabet_letter(nk,n,d)` (1≤d≤2n) — its index is in the b-block `[nk,nk+n)`.
proof fn lemma_db_proj_kills_alpha_letter(mm: ModMachine, n: nat, d: nat)
    requires
        1 <= d <= 2 * n,
    ensures
        apply_hom(db_projection(mm, n), seq![alphabet_letter(g_m(mm).num_generators, n, d)])
            =~= empty_word(),
{
    let nk = g_m(mm).num_generators;
    let pi = db_projection(mm, n);
    if d <= n {
        assert(alphabet_letter(nk, n, d) == Symbol::Gen((nk + d - 1) as nat));
        lemma_db_proj_kills_high(mm, n, (nk + d - 1) as nat);     // index nk+d-1 ∈ [nk, nk+n)
    } else {
        let idx = (nk + (d - n) - 1) as nat;
        assert(alphabet_letter(nk, n, d) == Symbol::Inv(idx));
        let w: Word = seq![Symbol::Inv(idx)];
        assert(w.len() == 1 && w.first() == Symbol::Inv(idx) && w.drop_first() =~= empty_word());
        reveal_with_fuel(apply_hom, 2);
        assert(apply_hom(pi, w.drop_first()) =~= empty_word());
        assert(apply_hom_symbol(pi, w.first()) == inverse_word(pi.generator_images[idx as int]));
        assert(pi.generator_images[idx as int] =~= empty_word());   // idx ≥ nk branch
        assert(inverse_word(empty_word()) =~= empty_word());
        lemma_concat_empty_right(inverse_word(pi.generator_images[idx as int]));
    }
}

/// `π` kills `w_c(nk,n,m,γ)` entirely (every letter is an `alphabet_letter` in the b-block).
proof fn lemma_db_proj_kills_wc(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        apply_hom(db_projection(mm, n), w_c(g_m(mm).num_generators, n, m, gamma)) =~= empty_word(),
    decreases gamma,
{
    let nk = g_m(mm).num_generators;
    let pi = db_projection(mm, n);
    if gamma == 0 || m <= 1 {
        assert(w_c(nk, n, m, gamma) =~= empty_word());
        assert(apply_hom(pi, empty_word()) =~= empty_word()) by { reveal_with_fuel(apply_hom, 1); }
    } else {
        let d = (gamma % m) as nat;
        assert(1 <= d <= 2 * n);
        assert(numbers_word(n, m, (gamma / m) as nat));
        let pre = w_c(nk, n, m, (gamma / m) as nat);
        let letter: Word = Seq::new(1, |_i: int| alphabet_letter(nk, n, d));
        assert(w_c(nk, n, m, gamma) =~= pre + letter);
        lemma_apply_hom_concat(pi, pre, letter);
        lemma_db_proj_kills_wc(mm, n, m, (gamma / m) as nat);     // IH: π(pre) = ε
        assert(letter =~= seq![alphabet_letter(nk, n, d)]);
        lemma_db_proj_kills_alpha_letter(mm, n, d);              // π(letter) = ε
        assert(concat(empty_word(), empty_word()) =~= empty_word());
    }
}

/// **`π` carries `assoc_rhs_machine(β) ↦ config(β,0)`**: `π` fixes the config (machine word), and
/// kills `w_b(nk,…)` (b-block) and the machine-d `Gen(nk+n)`.
pub proof fn lemma_db_proj_assoc_rhs(mm: ModMachine, n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
    ensures
        apply_hom(db_projection(mm, n), assoc_rhs_machine(mm, n, m, beta)) =~= config_word(beta, 0),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let pi = db_projection(mm, n);
    let cfg = config_word(beta, 0);
    let wb = w_b(nk, n, m, beta);
    let dw: Word = seq![Symbol::Gen((nk + n) as nat)];
    assert(assoc_rhs_machine(mm, n, m, beta) =~= (cfg + wb) + dw);
    lemma_apply_hom_concat(pi, cfg + wb, dw);
    lemma_apply_hom_concat(pi, cfg, wb);
    // π fixes config (machine word over 3 ≤ nk).
    lemma_db_proj_fixes_config(mm, n, beta);
    // π kills w_b = w_c.
    lemma_db_proj_kills_wc(mm, n, m, beta);
    // π kills machine-d.
    lemma_db_proj_kills_high(mm, n, (nk + n) as nat);
    assert(apply_hom(pi, dw) =~= empty_word());
    assert(concat(cfg, empty_word()) =~= cfg) by { lemma_concat_empty_right(cfg); }
    assert(concat(cfg, empty_word()) =~= apply_hom(pi, cfg + wb));
    assert(concat(apply_hom(pi, cfg + wb), empty_word()) =~= apply_hom(pi, cfg + wb)) by {
        lemma_concat_empty_right(apply_hom(pi, cfg + wb));
    }
}

/// The inclusion `ι : g_m → base_A_plus_base` (machine gen `i ↦ [Gen(i)]`); `base_A_plus_base` has
/// the same relators as `g_m`, so `ι` is valid and a machine word is fixed by it.
pub open spec fn gm_incl_bp(mm: ModMachine, n: nat) -> HomomorphismData {
    let nk = g_m(mm).num_generators;
    HomomorphismData {
        source: g_m(mm),
        target: base_A_plus_base(mm, n),
        generator_images: Seq::new(nk, |g: int| seq![Symbol::Gen(g as nat)]),
    }
}

/// `ι` fixes a machine word (valid over `nk`): `apply_hom(ι, r) = r`.
proof fn lemma_incl_fixes_machine_word(mm: ModMachine, n: nat, r: Word)
    requires
        word_valid(r, g_m(mm).num_generators),
    ensures
        apply_hom(gm_incl_bp(mm, n), r) =~= r,
{
    let nk = g_m(mm).num_generators;
    let io = gm_incl_bp(mm, n);
    lemma_apply_hom_eq_emb(io, r);
    assert forall|i: int| 0 <= i < nk
        implies #[trigger] io.generator_images[i] =~= seq![Symbol::Gen(i as nat)] by {}
    lemma_emb_identity_prefix(io.generator_images, r, nk);
}

/// **`ι` is a valid homomorphism `g_m → base_A_plus_base`.** Same relators as `g_m`; `ι` fixes each
/// machine relator, which is a `base_A_plus_base` relator ⟹ `≡ ε`.
pub proof fn lemma_gm_incl_bp_valid(mm: ModMachine, n: nat)
    ensures
        is_valid_homomorphism(gm_incl_bp(mm, n)),
{
    let nk = g_m(mm).num_generators;
    let io = gm_incl_bp(mm, n);
    lemma_g_m_valid(mm);
    lemma_base_A_plus_base_valid(mm, n);
    assert(io.source.num_generators == nk);
    assert(io.generator_images.len() == nk);
    assert(io.target.num_generators == nk + n + 1);
    assert forall|i: int| 0 <= i < io.generator_images.len()
        implies word_valid(#[trigger] io.generator_images[i], (nk + n + 1) as nat) by {
        assert(io.generator_images[i] =~= seq![Symbol::Gen(i as nat)]);
    }
    let gr = g_m(mm).relators;
    assert(io.source.relators == gr);
    assert(base_A_plus_base(mm, n).relators == gr);
    assert forall|i: int| 0 <= i < io.source.relators.len()
        implies equiv_in_presentation(io.target, apply_hom(io, #[trigger] io.source.relators[i]),
            empty_word()) by {
        assert(io.source.relators[i] == gr[i]);
        reveal(presentation_valid);
        assert(word_valid(gr[i], nk));
        lemma_incl_fixes_machine_word(mm, n, gr[i]);           // apply_hom(ι, gr[i]) = gr[i]
        lemma_relator_is_identity(base_A_plus_base(mm, n), i); // gr[i] ≡_bp ε
    }
}

/// **Membership lift `g_m → base_A_plus_base`** for machine words: a machine word `w` in
/// `⟨gens⟩` over `g_m` (machine `gens`) lies in `⟨gens⟩` over `base_A_plus_base` (via `ι`).
pub proof fn lemma_machine_subgroup_gm_to_bp(mm: ModMachine, n: nat, gens: Seq<Word>, w: Word)
    requires
        word_valid(w, g_m(mm).num_generators),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], g_m(mm).num_generators),
        in_generated_subgroup(g_m(mm), gens, w),
    ensures
        in_generated_subgroup(base_A_plus_base(mm, n), gens, w),
{
    let io = gm_incl_bp(mm, n);
    lemma_gm_incl_bp_valid(mm, n);
    lemma_hom_maps_subgroup(io, gens, w);
    let img_gens = Seq::new(gens.len(), |i: int| apply_hom(io, gens[i]));
    // ι fixes each machine gen and w.
    assert(img_gens =~= gens) by {
        assert forall|i: int| 0 <= i < gens.len() implies img_gens[i] =~= gens[i] by {
            assert(img_gens[i] == apply_hom(io, gens[i]));
            lemma_incl_fixes_machine_word(mm, n, gens[i]);
        }
    }
    lemma_incl_fixes_machine_word(mm, n, w);                   // apply_hom(ι, w) = w
}

/// **Generic subgroup generator-superset** (local copy of `r_prime_b`'s): `⟨gens1⟩ ⊆ ⟨gens2⟩`
/// when every `gens1[i]` appears in `gens2`.
pub proof fn lemma_in_subgroup_gens_superset(p: Presentation, gens1: Seq<Word>, gens2: Seq<Word>,
    w: Word)
    requires
        in_generated_subgroup(p, gens1, w),
        forall|i: int| 0 <= i < gens1.len()
            ==> exists|k: int| 0 <= k < gens2.len() && (#[trigger] gens1[i]) == gens2[k],
    ensures
        in_generated_subgroup(p, gens2, w),
{
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(gens1, f)
        && equiv_in_presentation(p, concat_all(f), w);
    assert(factors_from_generators(gens1, factors)
        && equiv_in_presentation(p, concat_all(factors), w));
    assert(factors_from_generators(gens2, factors)) by {
        assert forall|k: int| 0 <= k < factors.len()
            implies is_generator_or_inverse(gens2, #[trigger] factors[k]) by {
            assert(is_generator_or_inverse(gens1, factors[k]));
            let j = choose|j: int| 0 <= j < gens1.len()
                && (factors[k] == gens1[j] || factors[k] == inverse_word(gens1[j]));
            assert(0 <= j < gens1.len()
                && (factors[k] == gens1[j] || factors[k] == inverse_word(gens1[j])));
            let kk = choose|kk: int| 0 <= kk < gens2.len() && gens1[j] == gens2[kk];
            assert(gens1[j] == gens2[kk]);
        }
    }
}

/// **`π`-image lands in `⟨g_subgens⟩`.** If `A ∈ ⟨ublock_db_gens⟩` over `base_A_plus_base` then
/// `π(A) ∈ ⟨g_subgens⟩` over `g_m` (the `d,b`-images of `π` are `ε`). Generalizes the projection
/// half of `lemma_cs5_project_to_gsubgens` to an arbitrary `⟨ublock_db_gens⟩`-element `A`.
pub proof fn lemma_pi_image_in_gsubgens(mm: ModMachine, n: nat, av: Word)
    requires
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), av),
    ensures
        in_generated_subgroup(g_m(mm), g_subgens(mm), apply_hom(db_projection(mm, n), av)),
{
    let nk = g_m(mm).num_generators;
    let pi = db_projection(mm, n);
    let ub = ublock_db_gens(mm, n);
    let gs = g_subgens(mm);
    lemma_db_projection_valid(mm, n);
    lemma_g_m_valid(mm);
    lemma_g_m_num_generators(mm);
    lemma_g_m_associations_valid(mm);
    lemma_hom_maps_subgroup(pi, ub, av);
    let img_gens = Seq::new(ub.len(), |i: int| apply_hom(pi, ub[i]));
    assert(gs.len() == g_m_associations(mm).len());
    assert forall|j: int| 0 <= j < img_gens.len()
        implies in_generated_subgroup(g_m(mm), gs, #[trigger] img_gens[j])
            && in_generated_subgroup(g_m(mm), gs, inverse_word(img_gens[j])) by {
        assert(img_gens[j] == apply_hom(pi, ub[j]));
        if j < gs.len() {
            assert(ub[j] == gs[j]);
            assert(gs[j] == g_m_associations(mm)[j].1);
            lemma_word_valid_mono(gs[j], (3 + mm.quads.len()) as nat, nk);
            lemma_db_proj_fixes_machine_word(mm, n, gs[j]);
            assert(img_gens[j] =~= gs[j]);
            lemma_gen_and_inv_in_subgroup(g_m(mm), gs, j);
        } else {
            let k = j - gs.len();
            assert(0 <= k < n + 1);
            assert(ub[j] =~= seq![Symbol::Gen((nk + k) as nat)]);
            lemma_db_proj_kills_high(mm, n, (nk + k) as nat);
            assert(img_gens[j] =~= empty_word());
            lemma_empty_in_subgroup(g_m(mm), gs);
            assert(inverse_word(img_gens[j]) =~= empty_word());
        }
    }
    lemma_in_subgroup_gens_in_core(g_m(mm), img_gens, gs, apply_hom(pi, av));
}

/// **`config_emb(slice)` is a free family over `g_m`** (for `no_duplicates` slice). The freeness
/// implication is `lemma_config_emb_free`; the validity is `config(β,0)` over `3 ≤ nk`.
pub proof fn lemma_config_emb_is_free_family_gm(mm: ModMachine, slice: Seq<nat>)
    requires
        mod_machine_wf(mm),
        slice.no_duplicates(),
    ensures
        is_free_family(g_m(mm), config_emb(slice)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let ce = config_emb(slice);
    assert forall|i: int| 0 <= i < ce.len() implies word_valid(#[trigger] ce[i], nk) by {
        assert(ce[i] == config_word(slice[i], 0));
        lemma_config_word_valid(slice[i], 0);
        lemma_word_valid_mono(config_word(slice[i], 0), 3, nk);
    }
    assert forall|w: Word| (#[trigger] word_valid(w, ce.len())
        && equiv_in_presentation(g_m(mm), apply_embedding(ce, w), empty_word()))
        implies equiv_in_presentation(free_group(ce.len()), w, empty_word()) by {
        assert(ce.len() == slice.len());
        lemma_config_emb_free(mm, slice, w);
    }
}

/// **`comp_images(π, assoc_rhs_emb(slice)) = config_emb(slice)`** (entry-wise `lemma_db_proj_assoc_rhs`).
pub proof fn lemma_comp_pi_assoc_is_config(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < slice.len() ==> numbers_word(n, m, #[trigger] slice[i]),
    ensures
        comp_images(db_projection(mm, n), assoc_rhs_emb(mm, n, m, slice)) =~= config_emb(slice),
{
    let pi = db_projection(mm, n);
    let ae = assoc_rhs_emb(mm, n, m, slice);
    let comp = comp_images(pi, ae);
    let ce = config_emb(slice);
    assert(comp.len() == ae.len() == slice.len());
    assert(ce.len() == slice.len());
    assert forall|i: int| 0 <= i < slice.len() implies comp[i] =~= ce[i] by {
        assert(comp[i] == apply_hom(pi, ae[i]));
        assert(ae[i] == assoc_rhs_machine(mm, n, m, slice[i]));
        lemma_db_proj_assoc_rhs(mm, n, m, slice[i]);
        assert(ce[i] == config_word(slice[i], 0));
    }
}

} // verus!
