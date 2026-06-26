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
use crate::prop_v::{lemma_equiv_from_concat_inv_trivial, lemma_theorem1};
use crate::machine_group::{k_commutes, lemma_k_commutes_implies_subgroup};
use crate::hnn::lemma_base_embeds_in_hnn;
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
use crate::f_free_a1::{betas, lemma_betas_index, lemma_betas_numbers_word, lemma_betas_no_duplicates};
use crate::britton_via_tower::{has_pinch, has_pinch_at};
use crate::machine_group::lemma_config_word_zero;
use crate::f_free::is_free_family;
use crate::free_basis::lemma_config_emb_free;
use crate::higman_operations::lemma_free_group_valid;
use crate::phi_l_forward::lemma_intersection_property;
use crate::phi_l_forward::{relabel_symbol, lemma_single_gen_relabel, lemma_single_gen_relabel_subrange};
use crate::f_free::lemma_apply_embedding_agree_prefix;
use crate::britton_via_tower::{is_stable, has_adjacent_opposite_at};

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

// ----------------------------------------------------------------------------
// The `h0_filter` position selector — `h0_sel[k] = [Gen(p_k)]` with `slice[p_k] = h0_filter(slice)[k]`.
// One selector serves BOTH columns: `compose(config_emb(slice), h0_sel) = config_emb(h0_filter)` and
// `compose(assoc_rhs_emb(slice), h0_sel) = assoc_rhs_emb(h0_filter)`.
// ----------------------------------------------------------------------------

/// A `slice`-position holding `val` (well-defined whenever `slice.contains(val)`).
spec fn slice_pos(slice: Seq<nat>, val: nat) -> int {
    choose|p: int| 0 <= p < slice.len() && slice[p] == val
}

/// The selector picking, for each `h0_filter(slice)` entry, a `slice`-position holding it.
spec fn h0_sel(mm: ModMachine, slice: Seq<nat>) -> Seq<Word> {
    Seq::new(h0_filter(mm, slice).len(),
        |k: int| seq![Symbol::Gen(slice_pos(slice, h0_filter(mm, slice)[k]) as nat)])
}

/// `slice.contains(val) ⟹ slice_pos` is a valid position holding `val`.
proof fn lemma_slice_pos_valid(slice: Seq<nat>, val: nat)
    requires
        slice.contains(val),
    ensures
        0 <= slice_pos(slice, val) < slice.len(),
        slice[slice_pos(slice, val)] == val,
{
    assert(exists|p: int| 0 <= p < slice.len() && slice[p] == val) by { assert(slice.contains(val)); }
}

/// Every `h0_filter(slice)` entry lies in `slice` (it keeps a subset).
proof fn lemma_h0_filter_in_slice(mm: ModMachine, slice: Seq<nat>, k: int)
    requires
        0 <= k < h0_filter(mm, slice).len(),
    ensures
        slice.contains(h0_filter(mm, slice)[k]),
    decreases slice.len(),
{
    let hf = h0_filter(mm, slice);
    if slice.len() == 0 {
        assert(hf.len() == 0);
    } else {
        let rest = slice.drop_first();
        if mm_in_H0(mm, slice[0], 0) {
            assert(hf =~= seq![slice[0]] + h0_filter(mm, rest));
            if k == 0 {
                assert(hf[0] == slice[0]);
                assert(slice[0] == slice[0]);
            } else {
                assert(hf[k] == h0_filter(mm, rest)[k - 1]);
                lemma_h0_filter_in_slice(mm, rest, k - 1);
                let i = choose|i: int| 0 <= i < rest.len() && rest[i] == hf[k];
                assert(0 <= i < rest.len() && rest[i] == hf[k]);
                assert(rest[i] == slice[i + 1]);
            }
        } else {
            assert(hf =~= h0_filter(mm, rest));
            lemma_h0_filter_in_slice(mm, rest, k);
            let i = choose|i: int| 0 <= i < rest.len() && rest[i] == hf[k];
            assert(0 <= i < rest.len() && rest[i] == hf[k]);
            assert(rest[i] == slice[i + 1]);
        }
    }
}

/// `h0_sel[k]` is valid over `slice.len()` (its single generator index is a `slice`-position).
proof fn lemma_h0_sel_valid(mm: ModMachine, slice: Seq<nat>, k: int)
    requires
        0 <= k < h0_filter(mm, slice).len(),
    ensures
        word_valid(h0_sel(mm, slice)[k], slice.len()),
        slice[slice_pos(slice, h0_filter(mm, slice)[k]) as int] == h0_filter(mm, slice)[k],
        0 <= slice_pos(slice, h0_filter(mm, slice)[k]) < slice.len(),
{
    let hf = h0_filter(mm, slice);
    lemma_h0_filter_in_slice(mm, slice, k);
    lemma_slice_pos_valid(slice, hf[k]);
    let p = slice_pos(slice, hf[k]);
    assert(h0_sel(mm, slice)[k] =~= seq![Symbol::Gen(p as nat)]);
}

/// **`compose_embeddings(config_emb(slice), h0_sel) = config_emb(h0_filter(slice))`.**
proof fn lemma_compose_config_h0_sel(mm: ModMachine, n: nat, slice: Seq<nat>)
    ensures
        compose_embeddings(config_emb(slice), h0_sel(mm, slice)) =~= config_emb(h0_filter(mm, slice)),
{
    let hf = h0_filter(mm, slice);
    let sel = h0_sel(mm, slice);
    let ce = config_emb(slice);
    let comp = compose_embeddings(ce, sel);
    assert(comp.len() == sel.len() == hf.len());
    assert(config_emb(hf).len() == hf.len());
    assert forall|k: int| 0 <= k < hf.len() implies comp[k] =~= config_emb(hf)[k] by {
        lemma_h0_sel_valid(mm, slice, k);
        let p = slice_pos(slice, hf[k]);
        assert(comp[k] == apply_embedding(ce, sel[k]));
        assert(sel[k] =~= seq![Symbol::Gen(p as nat)]);
        lemma_emb_single_gen(ce, p as nat);                  // = ce[p] = config(slice[p],0)
        assert(ce[p] == config_word(slice[p], 0));
        assert(slice[p] == hf[k]);
        assert(config_emb(hf)[k] == config_word(hf[k], 0));
    }
}

/// **`compose_embeddings(assoc_rhs_emb(slice), h0_sel) = assoc_rhs_emb(h0_filter(slice))`.**
proof fn lemma_compose_assoc_h0_sel(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>)
    ensures
        compose_embeddings(assoc_rhs_emb(mm, n, m, slice), h0_sel(mm, slice))
            =~= assoc_rhs_emb(mm, n, m, h0_filter(mm, slice)),
{
    let hf = h0_filter(mm, slice);
    let sel = h0_sel(mm, slice);
    let ae = assoc_rhs_emb(mm, n, m, slice);
    let comp = compose_embeddings(ae, sel);
    assert(comp.len() == sel.len() == hf.len());
    assert(assoc_rhs_emb(mm, n, m, hf).len() == hf.len());
    assert forall|k: int| 0 <= k < hf.len() implies comp[k] =~= assoc_rhs_emb(mm, n, m, hf)[k] by {
        lemma_h0_sel_valid(mm, slice, k);
        let p = slice_pos(slice, hf[k]);
        assert(comp[k] == apply_embedding(ae, sel[k]));
        assert(sel[k] =~= seq![Symbol::Gen(p as nat)]);
        lemma_emb_single_gen(ae, p as nat);                  // = ae[p] = assoc_rhs_machine(slice[p])
        assert(ae[p] == assoc_rhs_machine(mm, n, m, slice[p]));
        assert(slice[p] == hf[k]);
        assert(assoc_rhs_emb(mm, n, m, hf)[k] == assoc_rhs_machine(mm, n, m, hf[k]));
    }
}

/// **CS-5c 3d Brick C — THE B-SIDE H₀-restriction (`C2-b`).** A base word `mid_w` of
/// `base_A_plus_base` lying in BOTH `⟨ublock_db_gens⟩` (the 3d invariant, no `p`) and
/// `⟨assoc_rhs_emb(slice)⟩` lies in `⟨assoc_rhs_emb(h0_filter(slice))⟩`. The b-orientation analog of
/// `lemma_cs5_middle_h0_restrict` — reduces to the a-side via `π` + config freeness + intersection.
pub proof fn lemma_cs5_middle_h0_restrict_b(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>,
    mid_w: Word)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        2 * n < m,
        slice.no_duplicates(),
        forall|i: int| 0 <= i < slice.len() ==> numbers_word(n, m, #[trigger] slice[i]),
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), mid_w),
        in_generated_subgroup(base_A_plus_base(mm, n), assoc_rhs_emb(mm, n, m, slice), mid_w),
    ensures
        in_generated_subgroup(base_A_plus_base(mm, n),
            assoc_rhs_emb(mm, n, m, h0_filter(mm, slice)), mid_w),
{
    let nk = g_m(mm).num_generators;
    let bp = base_A_plus_base(mm, n);
    let ng1 = (nk + n + 1) as nat;
    let pi = db_projection(mm, n);
    let ae = assoc_rhs_emb(mm, n, m, slice);
    let ce = config_emb(slice);
    lemma_g_m_num_generators(mm);
    lemma_g_m_valid(mm);
    lemma_base_A_plus_base_valid(mm, n);
    lemma_db_projection_valid(mm, n);
    assert(bp.num_generators == ng1);

    // assoc_rhs_emb / config_emb validities.
    assert(ae.len() == slice.len());
    assert forall|i: int| 0 <= i < ae.len() implies word_valid(#[trigger] ae[i], ng1) by {
        assert(ae[i] == assoc_rhs_machine(mm, n, m, slice[i]));
        lemma_w_c_valid(nk, n, m, slice[i], ng1);
        lemma_single_gen_valid((nk + n) as nat, ng1);
        lemma_config_word_valid(slice[i], 0);
        lemma_word_valid_mono(config_word(slice[i], 0), 3, ng1);
        lemma_concat_word_valid(config_word(slice[i], 0), w_b(nk, n, m, slice[i]), ng1);
        lemma_concat_word_valid(config_word(slice[i], 0) + w_b(nk, n, m, slice[i]),
            seq![Symbol::Gen((nk + n) as nat)], ng1);
        assert(assoc_rhs_machine(mm, n, m, slice[i])
            =~= (config_word(slice[i], 0) + w_b(nk, n, m, slice[i])) + seq![Symbol::Gen((nk + n) as nat)]);
    }
    assert(ce.len() == slice.len());
    assert forall|i: int| 0 <= i < ce.len() implies word_valid(#[trigger] ce[i], nk) by {
        assert(ce[i] == config_word(slice[i], 0));
        lemma_config_word_valid(slice[i], 0);
        lemma_word_valid_mono(config_word(slice[i], 0), 3, nk);
    }

    // ---- 1. coord word u over assoc_rhs_emb(slice); A = emb(ae, u) ≡_bp mid_w ----
    lemma_subgroup_to_k_word(bp, ae, mid_w);
    let u = choose|u: Word| word_valid(u, ae.len())
        && equiv_in_presentation(bp, apply_embedding(ae, u), mid_w);
    assert(word_valid(u, ae.len()) && equiv_in_presentation(bp, apply_embedding(ae, u), mid_w));
    let av = apply_embedding(ae, u);
    assert(word_valid(u, slice.len()));
    lemma_apply_embedding_valid(ae, u, ng1);                 // av valid over bp

    // ---- 2. A ∈ ⟨ublock_db_gens⟩ over bp ----
    lemma_equiv_symmetric(bp, av, mid_w);
    lemma_in_subgroup_respects_equiv(bp, ublock_db_gens(mm, n), mid_w, av);

    // ---- 3. cw = π(A) = emb(config_emb(slice), u) ----
    lemma_apply_hom_embedding_compose(pi, ae, u);
    lemma_comp_pi_assoc_is_config(mm, n, m, slice);
    let cw = apply_embedding(ce, u);
    assert(apply_hom(pi, av) =~= cw);
    lemma_apply_embedding_valid(ce, u, nk);                  // cw valid over nk

    // ---- 4. cw ∈ ⟨g_subgens⟩ over g_m ----
    lemma_pi_image_in_gsubgens(mm, n, av);
    assert(in_generated_subgroup(g_m(mm), g_subgens(mm), cw));

    // ---- 5. lift cw to bp, a-side C2 ⟹ cw ∈ ⟨config_emb(h0_filter)⟩ over bp ----
    assert forall|i: int| 0 <= i < g_subgens(mm).len()
        implies word_valid(#[trigger] g_subgens(mm)[i], nk) by {
        lemma_g_m_associations_valid(mm);
        assert(g_subgens(mm)[i] == g_m_associations(mm)[i].1);
        lemma_word_valid_mono(g_subgens(mm)[i], (3 + mm.quads.len()) as nat, nk);
    }
    lemma_machine_subgroup_gm_to_bp(mm, n, g_subgens(mm), cw);
    // g_subgens ⊆ ublock_db_gens (prefix).
    assert forall|i: int| 0 <= i < g_subgens(mm).len()
        implies exists|kk: int| 0 <= kk < ublock_db_gens(mm, n).len()
            && (#[trigger] g_subgens(mm)[i]) == ublock_db_gens(mm, n)[kk] by {
        assert(ublock_db_gens(mm, n)[i] == g_subgens(mm)[i]);   // prefix
    }
    lemma_in_subgroup_gens_superset(bp, g_subgens(mm), ublock_db_gens(mm, n), cw);
    lemma_apply_embedding_in_subgroup(bp, ce, u);            // cw ∈ ⟨config_emb(slice)⟩ over bp
    lemma_cs5_middle_h0_restrict(mm, n, slice, cw);
    let hf = h0_filter(mm, slice);
    assert(in_generated_subgroup(bp, config_emb(hf), cw));

    // ---- 6. descend cw ∈ ⟨config_emb(hf)⟩ to g_m (π fixes cw and config_emb(hf)) ----
    lemma_hom_maps_subgroup(pi, config_emb(hf), cw);
    let dimg = Seq::new(config_emb(hf).len(), |i: int| apply_hom(pi, config_emb(hf)[i]));
    assert(dimg =~= config_emb(hf)) by {
        assert forall|i: int| 0 <= i < config_emb(hf).len() implies dimg[i] =~= config_emb(hf)[i] by {
            assert(config_emb(hf)[i] == config_word(hf[i], 0));
            lemma_db_proj_fixes_config(mm, n, hf[i]);
        }
    }
    lemma_db_proj_fixes_machine_word(mm, n, cw);             // π(cw) = cw
    assert(in_generated_subgroup(g_m(mm), config_emb(hf), cw));

    // ---- 7. intersection over g_m: config free + config_emb(hf) = compose(config_emb(slice), h0_sel) ----
    lemma_config_emb_is_free_family_gm(mm, slice);
    lemma_compose_config_h0_sel(mm, n, slice);
    assert(in_generated_subgroup(g_m(mm), compose_embeddings(ce, h0_sel(mm, slice)), cw));
    assert forall|k: int| 0 <= k < h0_sel(mm, slice).len()
        implies word_valid(#[trigger] h0_sel(mm, slice)[k], slice.len()) by {
        lemma_h0_sel_valid(mm, slice, k);
    }
    lemma_intersection_property(g_m(mm), ce, h0_sel(mm, slice), u);
    assert(in_generated_subgroup(free_group(slice.len()), h0_sel(mm, slice), u));

    // ---- 8. carry u back through assoc_rhs_emb (emb-as-hom) ----
    let eh = HomomorphismData { source: free_group(slice.len()), target: bp, generator_images: ae };
    lemma_free_group_valid(slice.len());
    assert(is_valid_homomorphism(eh)) by {
        reveal(presentation_valid);
        assert(eh.source.relators.len() == 0);
        assert forall|i: int| 0 <= i < eh.generator_images.len()
            implies word_valid(#[trigger] eh.generator_images[i], eh.target.num_generators) by {
            assert(eh.generator_images[i] == ae[i]);
        }
    }
    lemma_hom_maps_subgroup(eh, h0_sel(mm, slice), u);
    let aimg = Seq::new(h0_sel(mm, slice).len(), |i: int| apply_hom(eh, h0_sel(mm, slice)[i]));
    assert(apply_hom(eh, u) =~= av) by { lemma_apply_hom_eq_emb(eh, u); }
    lemma_compose_assoc_h0_sel(mm, n, m, slice);
    assert(aimg =~= assoc_rhs_emb(mm, n, m, hf)) by {
        assert forall|i: int| 0 <= i < h0_sel(mm, slice).len()
            implies aimg[i] =~= assoc_rhs_emb(mm, n, m, hf)[i] by {
            lemma_apply_hom_eq_emb(eh, h0_sel(mm, slice)[i]);
            assert(apply_hom(eh, h0_sel(mm, slice)[i]) == apply_embedding(ae, h0_sel(mm, slice)[i]));
            assert(compose_embeddings(ae, h0_sel(mm, slice))[i] == apply_embedding(ae, h0_sel(mm, slice)[i]));
        }
    }
    assert(in_generated_subgroup(bp, assoc_rhs_emb(mm, n, m, hf), av));

    // ---- 9. mid_w ≡_bp A ⟹ mid_w ∈ ⟨assoc_rhs_emb(hf)⟩ ----
    lemma_in_subgroup_respects_equiv(bp, assoc_rhs_emb(mm, n, m, hf), av, mid_w);
}

// ============================================================================
// Brick D (3d) — the SEGMENT-WISE INVARIANT (blueprint §7.3).  Every maximal stable-free run of the
// word being peeled lies in `⟨ublock_db_gens⟩` (= `⟨g_subgens,d,b⟩`) over `base_A_plus_base`. This is
// the combinatorial property that supplies the `∈⟨U,d,b⟩` hypothesis for C2 / C2-b at each pinch
// middle, WITHOUT circularity (it tracks the reduction-sequence's word structure, not group
// membership in A₊).  This file defines the invariant + the middle-extraction (the direction Brick E
// consumes); the base case + pinch-out preservation are the remaining Brick D work.
// ============================================================================

/// `s` is the `base_A_plus_data` stable letter `p^± = Gen/Inv(nk+n+1)` (slice/m-independent — every
/// `base_A_plus_data(…,slice)` shares the base `base_A_plus_base(mm,n)` with `nk+n+1` generators).
pub open spec fn seg_stable(mm: ModMachine, n: nat, s: Symbol) -> bool {
    let p = (g_m(mm).num_generators + n + 1) as nat;
    s == Symbol::Gen(p) || s == Symbol::Inv(p)
}

/// **The segment invariant.** Every maximal stable-free run `wm[a..b]` (bounded by `p^±` letters or
/// the word ends, stable-free inside) lies in `⟨ublock_db_gens⟩` over `base_A_plus_base`.
pub open spec fn seg_inv(mm: ModMachine, n: nat, wm: Word) -> bool {
    forall|a: int, b: int|
        (0 <= a <= b <= wm.len()
            && (a == 0 || seg_stable(mm, n, wm[a - 1]))
            && (b == wm.len() || seg_stable(mm, n, wm[b]))
            && (forall|k: int| a <= k < b ==> !seg_stable(mm, n, wm[k])))
        ==> #[trigger] in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n),
                wm.subrange(a, b))
}

/// `seg_stable` agrees with `is_stable` over any `base_A_plus_data(…,slice)` (same base gen count).
pub proof fn lemma_seg_stable_iff(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>, s: Symbol)
    ensures
        seg_stable(mm, n, s) <==> is_stable(base_A_plus_data(mm, n, m, slice), s),
{
    lemma_base_A_plus_data_shape(mm, n, m, slice);
    assert(base_A_plus_data(mm, n, m, slice).base.num_generators == g_m(mm).num_generators + n + 1);
}

/// **Middle extraction** (the direction Brick E consumes): the stable-free middle `wm[i+1..j]` of a
/// `base_A_plus_data` pinch lies in `⟨ublock_db_gens⟩`, by instantiating `seg_inv` at `(i+1, j)`.
pub proof fn lemma_seg_inv_middle(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>, wm: Word,
    i: int, j: int)
    requires
        seg_inv(mm, n, wm),
        has_adjacent_opposite_at(base_A_plus_data(mm, n, m, slice), wm, i, j),
    ensures
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), wm.subrange(i + 1, j)),
{
    let data = base_A_plus_data(mm, n, m, slice);
    assert(0 <= i < j < wm.len());
    // boundary stables (a-1 = i, b = j).
    lemma_seg_stable_iff(mm, n, m, slice, wm[i]);
    lemma_seg_stable_iff(mm, n, m, slice, wm[j]);
    assert(seg_stable(mm, n, wm[(i + 1) - 1]));
    assert(j == wm.len() || seg_stable(mm, n, wm[j]));
    // interior stable-free.
    assert forall|k: int| (i + 1) <= k < j implies !seg_stable(mm, n, wm[k]) by {
        assert(i < k < j);
        assert(!is_stable(data, wm[k]));                     // from has_adjacent_opposite_at
        lemma_seg_stable_iff(mm, n, m, slice, wm[k]);
    }
    // instantiate seg_inv at (i+1, j).
    assert(in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n),
        wm.subrange(i + 1, j)));
}

// ----------------------------------------------------------------------------
// Brick D — the BASE CASE: `relabel(w)` satisfies `seg_inv`.  `relabel_col` is a single-gen
// relabeling whose non-`p` entries are exactly the `ublock_db_gens` generators, so every
// stable-free run of `relabel(w)` is a literal product of `ublock_db_gens` generators.
// ----------------------------------------------------------------------------

/// The `relabel_col` block decomposition `((r_u + r_d) + r_b) + r_p` (mirror `lemma_a_factor_entry`).
proof fn lemma_relabel_col_blocks(mm: ModMachine, n: nat) -> (r: (Seq<Word>, Seq<Word>, Seq<Word>, Seq<Word>))
    ensures
        ({ let nk = g_m(mm).num_generators; let q = g_subgens(mm).len();
           &&& r.0 == Seq::<Word>::new(q as nat, |i: int| g_subgens(mm)[i])
           &&& r.1 == seq![ seq![Symbol::Gen((nk + n) as nat)] ]
           &&& r.2 == Seq::<Word>::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)])
           &&& r.3 == seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ]
           &&& relabel_col(mm, n) =~= ((r.0 + r.1) + r.2) + r.3 }),
{
    let nk = g_m(mm).num_generators;
    let q = g_subgens(mm).len();
    let r_u: Seq<Word> = Seq::new(q as nat, |i: int| g_subgens(mm)[i]);
    let r_d: Seq<Word> = seq![ seq![Symbol::Gen((nk + n) as nat)] ];
    let r_b: Seq<Word> = Seq::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)]);
    let r_p: Seq<Word> = seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ];
    assert(relabel_col(mm, n) =~= ((r_u + r_d) + r_b) + r_p);
    (r_u, r_d, r_b, r_p)
}

/// Every `relabel_col` entry is a single generator (`lemma_single_gen_relabel` precondition).
proof fn lemma_relabel_col_single_gen(mm: ModMachine, n: nat)
    ensures
        forall|i: int| 0 <= i < relabel_col(mm, n).len() ==>
            exists|g: nat| #[trigger] relabel_col(mm, n)[i] == seq![Symbol::Gen(g)],
{
    let nk = g_m(mm).num_generators;
    let q = g_subgens(mm).len();
    lemma_machine_col_len(mm, n);
    lemma_g_m_num_generators(mm);
    lemma_g_m_associations_valid(mm);
    let blk = lemma_relabel_col_blocks(mm, n);
    let rc = relabel_col(mm, n);
    assert forall|i: int| 0 <= i < rc.len()
        implies exists|g: nat| #[trigger] rc[i] == seq![Symbol::Gen(g)] by {
        if i < q {
            assert(rc[i] == g_subgens(mm)[i]) by {
                assert(((blk.0 + blk.1) + blk.2)[i] == (blk.0 + blk.1)[i]);
                assert((blk.0 + blk.1)[i] == blk.0[i]);
            }
            let u = g_subgens(mm)[i];
            assert(u == g_m_associations(mm)[i].1);
            assert(word_valid(u, (3 + mm.quads.len()) as nat));
            assert(u.len() == 1);
            let gi = generator_index(u[0]);
            assert(symbol_valid(u[0], (3 + mm.quads.len()) as nat));
            assert(u[0] == Symbol::Gen(gi)) by { assert(symbol_valid(u[0], nk)); }
            assert(u =~= seq![Symbol::Gen(gi)]);
        } else if i == q {
            assert(rc[i] =~= seq![Symbol::Gen((nk + n) as nat)]) by {
                assert(((blk.0 + blk.1) + blk.2)[i] == (blk.0 + blk.1)[i]);
                assert((blk.0 + blk.1)[i] == blk.1[i - q]);
            }
        } else if i < q + 1 + n {
            let j = i - q - 1;
            assert(rc[i] =~= seq![Symbol::Gen((nk + j) as nat)]) by {
                assert(((blk.0 + blk.1) + blk.2)[i] == blk.2[j]);
            }
        } else {
            assert(rc[i] =~= seq![Symbol::Gen((nk + n + 1) as nat)]);
        }
    }
}

/// A non-`p` `relabel_col` entry (`i < q+n+1`) is a single gen with index `< nk+n+1` (so NOT the
/// stable letter `Gen(nk+n+1)`) AND appears in `ublock_db_gens`.
proof fn lemma_relabel_col_nonp(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < g_subgens(mm).len() + n + 1,
    ensures
        ({ let nk = g_m(mm).num_generators;
           exists|g: nat| relabel_col(mm, n)[i] == seq![Symbol::Gen(g)] && g < nk + n + 1 }),
        exists|k: int| 0 <= k < ublock_db_gens(mm, n).len()
            && relabel_col(mm, n)[i] == #[trigger] ublock_db_gens(mm, n)[k],
{
    let nk = g_m(mm).num_generators;
    let q = g_subgens(mm).len();
    lemma_machine_col_len(mm, n);
    lemma_g_m_num_generators(mm);
    lemma_g_m_associations_valid(mm);
    let blk = lemma_relabel_col_blocks(mm, n);
    let rc = relabel_col(mm, n);
    let ub = ublock_db_gens(mm, n);
    // ub = g_subgens + Seq::new(n+1, |j| [Gen(nk+j)]).
    assert(ub.len() == q + n + 1);
    let ub_tail: Seq<Word> = Seq::new((n + 1) as nat, |j: int| seq![Symbol::Gen((nk + j) as nat)]);
    assert(ub =~= g_subgens(mm) + ub_tail);
    if i < q {
        assert(rc[i] == g_subgens(mm)[i]) by {
            assert(((blk.0 + blk.1) + blk.2)[i] == (blk.0 + blk.1)[i]);
            assert((blk.0 + blk.1)[i] == blk.0[i]);
        }
        let u = g_subgens(mm)[i];
        assert(u == g_m_associations(mm)[i].1);
        assert(word_valid(u, (3 + mm.quads.len()) as nat));
        assert(u.len() == 1);
        let gi = generator_index(u[0]);
        assert(symbol_valid(u[0], (3 + mm.quads.len()) as nat));
        assert(gi < 3 + mm.quads.len());
        assert(gi < nk);                                         // < nk < nk+n+1
        assert(u[0] == Symbol::Gen(gi)) by { assert(symbol_valid(u[0], nk)); }
        assert(u =~= seq![Symbol::Gen(gi)]);
        assert(ub[i] == g_subgens(mm)[i]);                       // k = i (prefix)
    } else if i == q {
        // d: rc[q] = [Gen(nk+n)]; ub_tail[n] = [Gen(nk+n)] ⟹ ub[q+n].
        assert(rc[i] =~= seq![Symbol::Gen((nk + n) as nat)]) by {
            assert(((blk.0 + blk.1) + blk.2)[i] == (blk.0 + blk.1)[i]);
            assert((blk.0 + blk.1)[i] == blk.1[i - q]);
        }
        assert(ub[(q + n) as int] == ub_tail[n as int]);
        assert(ub_tail[n as int] =~= seq![Symbol::Gen((nk + n) as nat)]);   // k = q+n
    } else {
        // b: i = q+1+j, j ∈ [0,n); rc[i] = [Gen(nk+j)]; ub_tail[j] = [Gen(nk+j)] ⟹ ub[q+j].
        let j = i - q - 1;
        assert(0 <= j < n);
        assert(rc[i] =~= seq![Symbol::Gen((nk + j) as nat)]) by {
            assert(((blk.0 + blk.1) + blk.2)[i] == blk.2[j]);
        }
        assert(ub[(q as int) + j] == ub_tail[j]);
        assert(ub_tail[j] =~= seq![Symbol::Gen((nk + j) as nat)]);          // k = q+j
    }
}

/// **Brick D base case:** `relabel(w)` satisfies `seg_inv` — every stable-free run is a literal
/// product of `ublock_db_gens` generators (the non-`p` `relabel_col` images).
pub proof fn lemma_seg_inv_relabel(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, psi_assoc(mm, n).len()),
    ensures
        seg_inv(mm, n, relabel(mm, n, w)),
{
    let nk = g_m(mm).num_generators;
    let q = g_subgens(mm).len();
    let rc = relabel_col(mm, n);
    let wm = relabel(mm, n, w);
    let bp = base_A_plus_base(mm, n);
    let ub = ublock_db_gens(mm, n);
    lemma_machine_col_len(mm, n);
    lemma_g_m_num_generators(mm);
    assert(rc.len() == q + n + 2);
    assert(word_valid(w, rc.len()));
    lemma_relabel_col_single_gen(mm, n);
    lemma_single_gen_relabel(rc, w);                            // wm length-preserving relabel
    assert(wm.len() == w.len());

    assert forall|a: int, b: int|
        (0 <= a <= b <= wm.len()
            && (a == 0 || seg_stable(mm, n, wm[a - 1]))
            && (b == wm.len() || seg_stable(mm, n, wm[b]))
            && (forall|k: int| a <= k < b ==> !seg_stable(mm, n, wm[k])))
        implies #[trigger] in_generated_subgroup(bp, ub, wm.subrange(a, b)) by {
        // wm.subrange(a,b) = emb(rc, w.subrange(a,b)).
        lemma_single_gen_relabel_subrange(rc, w, a, b);
        let ws = w.subrange(a, b);
        assert(wm.subrange(a, b) =~= apply_embedding(rc, ws));
        // ws valid over q+n+1 (the run avoids psi-p = index q+n+1).
        assert(word_valid(ws, (q + n + 1) as nat)) by {
            assert forall|t: int| 0 <= t < ws.len()
                implies symbol_valid(#[trigger] ws[t], (q + n + 1) as nat) by {
                assert(ws[t] == w[a + t]);
                assert(a <= a + t < b);
                assert(!seg_stable(mm, n, wm[a + t]));
                assert(wm[a + t] == relabel_symbol(rc, w[a + t]));
                let idx = generator_index(w[a + t]);
                assert(symbol_valid(w[a + t], rc.len()));      // idx < q+n+2
                // if idx == q+n+1 (psi-p) then wm[a+t] = p^± ⟹ seg_stable, contradiction.
                if idx == q + n + 1 {
                    assert(rc[idx as int] =~= seq![Symbol::Gen((nk + n + 1) as nat)]);
                    match w[a + t] {
                        Symbol::Gen(gg) => {
                            assert(relabel_symbol(rc, w[a + t]) == Symbol::Gen((nk + n + 1) as nat));
                        },
                        Symbol::Inv(gg) => {
                            assert(relabel_symbol(rc, w[a + t]) == Symbol::Inv((nk + n + 1) as nat));
                        },
                    }
                }
            }
        }
        // emb(rc, ws) = emb(rc_prefix, ws) (agree on the non-p prefix).
        let rc_prefix = rc.subrange(0, (q + n + 1) as int);
        assert(forall|ii: int| 0 <= ii < q + n + 1 ==> rc[ii] == rc_prefix[ii]);
        lemma_apply_embedding_agree_prefix(rc, rc_prefix, ws, (q + n + 1) as nat);
        assert(apply_embedding(rc, ws) =~= apply_embedding(rc_prefix, ws));
        // ∈ ⟨rc_prefix⟩.
        lemma_apply_embedding_in_subgroup(bp, rc_prefix, ws);
        // rc_prefix ⊆ ublock_db_gens (each entry appears).
        assert forall|ii: int| 0 <= ii < rc_prefix.len()
            implies exists|k: int| 0 <= k < ub.len() && (#[trigger] rc_prefix[ii]) == ub[k] by {
            assert(rc_prefix[ii] == rc[ii]);                   // ii < q+n+1
            lemma_relabel_col_nonp(mm, n, ii);
        }
        lemma_in_subgroup_gens_superset(bp, rc_prefix, ub, apply_embedding(rc_prefix, ws));
        assert(apply_embedding(rc_prefix, ws) =~= wm.subrange(a, b));
    }
}

// ----------------------------------------------------------------------------
// Brick D — D-PRESERVATION: `seg_inv` survives a pinch-out splice.
// ----------------------------------------------------------------------------

/// Three-region indexing of the spliced word `wshort = wm[0..i] + phi_g + wm[j+1..]`:
/// positions `< i` come from `wm`, positions `[i, i+|phi_g|)` from `phi_g`, positions `>= i+|phi_g|`
/// from the suffix `wm[j+1..]` (shifted).
proof fn lemma_wshort_at(wm: Word, phi_g: Word, i: int, j: int, k: int)
    requires
        0 <= i,
        i < j,
        j < wm.len(),
        0 <= k < i + phi_g.len() + (wm.len() - j - 1),
    ensures
        ({
            let pre = wm.subrange(0, i);
            let suf = wm.subrange(j + 1, wm.len() as int);
            let wshort = (pre + phi_g) + suf;
            let lp = phi_g.len() as int;
            &&& wshort.len() == i + lp + (wm.len() - j - 1)
            &&& (0 <= k < i ==> wshort[k] == wm[k])
            &&& (i <= k < i + lp ==> wshort[k] == phi_g[k - i])
            &&& (i + lp <= k ==> wshort[k] == wm[k - i - lp + j + 1])
        }),
{
    let pre = wm.subrange(0, i);
    let suf = wm.subrange(j + 1, wm.len() as int);
    let pf = pre + phi_g;
    let wshort = pf + suf;
    let lp = phi_g.len() as int;
    assert(pre.len() == i);
    assert(suf.len() == wm.len() - j - 1);
    assert(pf.len() == i + lp);
    assert(wshort.len() == i + lp + (wm.len() - j - 1));
    if 0 <= k < i {
        assert(wshort[k] == pf[k]);          // k < pf.len()
        assert(pf[k] == pre[k]);             // k < pre.len()
        assert(pre[k] == wm[k]);             // subrange(0,i)
    } else if i <= k < i + lp {
        assert(wshort[k] == pf[k]);          // k < pf.len() = i+lp
        assert(pf[k] == phi_g[k - i]);       // k >= pre.len() = i
    } else {
        assert(wshort[k] == suf[k - (i + lp)]);                       // k >= pf.len()
        assert(suf[k - (i + lp)] == wm[(j + 1) + (k - (i + lp))]);    // subrange(j+1, _)
        assert((j + 1) + (k - (i + lp)) == k - i - lp + j + 1);
    }
}

/// `seg_inv(wm)` instantiated at one maximal stable-free run `[a,b)`: directly gives `wm[a..b] ∈
/// ⟨ublock_db_gens⟩`.  (A thin wrapper so each call site only has to discharge the run conditions.)
proof fn lemma_seg_inv_run_in_ub(mm: ModMachine, n: nat, wm: Word, a: int, b: int)
    requires
        seg_inv(mm, n, wm),
        0 <= a <= b <= wm.len(),
        a == 0 || seg_stable(mm, n, wm[a - 1]),
        b == wm.len() || seg_stable(mm, n, wm[b]),
        forall|kk: int| a <= kk < b ==> !seg_stable(mm, n, wm[kk]),
    ensures
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), wm.subrange(a, b)),
{
    assert(in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), wm.subrange(a, b)));
}

// ----------------------------------------------------------------------------
// Brick E groundwork — `a_col_machine` as a single-gen relabel (mirror `a_words`).
// ----------------------------------------------------------------------------

/// `a_col_machine[i]` is a single generator `[Gen(g)]`, and `g` is the recog stable letter `p_idx`
/// IFF `i` is the machine stable letter index `nk+n+1`.  (The block layout: machine gens `0..nk`,
/// b-block `nk..nk+n`, `d = nk+n`, `p = nk+n+1`; images stay `< p_idx` except at the `p` slot.)
proof fn lemma_a_col_machine_entry(mm: ModMachine, n: nat, i: int) -> (g: nat)
    requires
        0 <= i < g_m(mm).num_generators + n + 2,
    ensures
        a_col_machine(mm, n)[i] == seq![Symbol::Gen(g)],
        g == p_idx(g_m(mm).num_generators, n) <==> i == g_m(mm).num_generators + n + 1,
{
    let nk = g_m(mm).num_generators;
    let am = a_col_machine(mm, n);
    let blk_m = Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)]);
    let blk_b = Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))]);
    let blk_d: Seq<Word> = seq![ seq![Symbol::Gen(d_idx(nk, n))] ];
    let blk_p: Seq<Word> = seq![ seq![Symbol::Gen(p_idx(nk, n))] ];
    assert(am =~= ((blk_m + blk_b) + blk_d) + blk_p);
    assert(blk_m.len() == nk && blk_b.len() == n);
    if i < nk {
        assert(((blk_m + blk_b) + blk_d)[i] == (blk_m + blk_b)[i]);
        assert((blk_m + blk_b)[i] == blk_m[i]);
        assert(am[i] == seq![Symbol::Gen(i as nat)]);
        (i as nat)
    } else if i < nk + n {
        let j = i - nk;
        assert(((blk_m + blk_b) + blk_d)[i] == (blk_m + blk_b)[i]);
        assert((blk_m + blk_b)[i] == blk_b[j]);
        assert(b_idx(nk, n, (j + 1) as nat) == nk + n + j);             // < nk+2n < p_idx
        assert(am[i] == seq![Symbol::Gen((nk + n + j) as nat)]);
        (nk + n + j) as nat
    } else if i == nk + n {
        assert(((blk_m + blk_b) + blk_d)[i] == blk_d[0]);
        assert(d_idx(nk, n) == nk + 2 * n);                            // != p_idx = nk+2n+1
        assert(am[i] == seq![Symbol::Gen(d_idx(nk, n))]);
        d_idx(nk, n)
    } else {
        assert(i == nk + n + 1);
        assert(am[i] == blk_p[0]);
        assert(am[i] == seq![Symbol::Gen(p_idx(nk, n))]);
        p_idx(nk, n)
    }
}

/// `a_col_machine` is a length-`nk+n+2` single-generator relabel.
proof fn lemma_a_col_machine_single_gen(mm: ModMachine, n: nat)
    ensures
        a_col_machine(mm, n).len() == g_m(mm).num_generators + n + 2,
        forall|i: int| 0 <= i < a_col_machine(mm, n).len() ==>
            exists|g: nat| #[trigger] a_col_machine(mm, n)[i] == seq![Symbol::Gen(g)],
{
    lemma_machine_col_len(mm, n);
    assert forall|i: int| 0 <= i < a_col_machine(mm, n).len()
        implies exists|g: nat| #[trigger] a_col_machine(mm, n)[i] == seq![Symbol::Gen(g)] by {
        let g = lemma_a_col_machine_entry(mm, n, i);
        assert(a_col_machine(mm, n)[i] == seq![Symbol::Gen(g)]);
    }
}

/// **The relabel preserves the machine stable letter exactly**: `relabel_symbol(a_col_machine, s)` is
/// the recog stable letter `Gen/Inv(p_idx)` IFF `s` is the machine stable letter `Gen/Inv(nk+n+1)`.
/// Transfers `has_adjacent_opposite_at` between `recog_data` and `base_A_plus_data` at the same index.
proof fn lemma_a_col_machine_relabel_sym(mm: ModMachine, n: nat, s: Symbol)
    requires
        symbol_valid(s, (g_m(mm).num_generators + n + 2) as nat),
    ensures
        ({ let nk = g_m(mm).num_generators;
           &&& (relabel_symbol(a_col_machine(mm, n), s) == Symbol::Gen(p_idx(nk, n))
                 <==> s == Symbol::Gen((nk + n + 1) as nat))
           &&& (relabel_symbol(a_col_machine(mm, n), s) == Symbol::Inv(p_idx(nk, n))
                 <==> s == Symbol::Inv((nk + n + 1) as nat)) }),
{
    let nk = g_m(mm).num_generators;
    let am = a_col_machine(mm, n);
    let i = generator_index(s);
    lemma_machine_col_len(mm, n);
    assert(0 <= i < nk + n + 2);
    let g = lemma_a_col_machine_entry(mm, n, i as int);
    assert(am[i as int] == seq![Symbol::Gen(g)]);
    assert(am[i as int][0] == Symbol::Gen(g));
    // g == p_idx  ⟺  i == nk+n+1.
    match s {
        Symbol::Gen(ii) => {
            assert(ii == i);
            assert(relabel_symbol(am, s) == am[i as int][0]);
            assert(relabel_symbol(am, s) == Symbol::Gen(g));
        },
        Symbol::Inv(ii) => {
            assert(ii == i);
            assert(relabel_symbol(am, s) == inverse_symbol(am[i as int][0]));
            assert(inverse_symbol(Symbol::Gen(g)) == Symbol::Inv(g));
            assert(relabel_symbol(am, s) == Symbol::Inv(g));
        },
    }
}

/// **Brick D preservation:** `seg_inv` survives a pinch-out splice.  Given a `base_A_plus_data` pinch
/// at `(i,j)`, with the replacement middle `phi_g` stable-free and `∈ ⟨ublock_db_gens⟩`, the spliced
/// word `wshort = wm[0..i] + phi_g + wm[j+1..]` again satisfies `seg_inv`.  The only *new* maximal
/// stable-free run is the merged `wm[s..i] · phi_g · wm[j+1..e]` (the pre/suf runs are bounded by the
/// removed `p`-letters at `i,j`, hence maximal runs of `wm` ⟹ in `⟨ublock⟩` by IH; `phi_g` is in by
/// hypothesis; product ∈ subgroup).  All other runs of `wshort` are runs of `wm`.  (Companion-confirmed
/// case split; blueprint §7.3.)
pub proof fn lemma_seg_inv_pinch_out(mm: ModMachine, n: nat, m: nat, slice: Seq<nat>,
    wm: Word, phi_g: Word, i: int, j: int)
    requires
        seg_inv(mm, n, wm),
        has_adjacent_opposite_at(base_A_plus_data(mm, n, m, slice), wm, i, j),
        forall|t: int| 0 <= t < phi_g.len() ==> !seg_stable(mm, n, phi_g[t]),
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), phi_g),
    ensures
        seg_inv(mm, n, wm.subrange(0, i) + phi_g + wm.subrange(j + 1, wm.len() as int)),
{
    let bp = base_A_plus_base(mm, n);
    let ub = ublock_db_gens(mm, n);
    let data = base_A_plus_data(mm, n, m, slice);
    let pre = wm.subrange(0, i);
    let suf = wm.subrange(j + 1, wm.len() as int);
    let wshort = pre + phi_g + suf;                  // = (pre + phi_g) + suf
    let big_m = wm.len() as int;
    let lp = phi_g.len() as int;
    let cap_w = i + lp + (big_m - j - 1);
    let dd = j + 1 - i - lp;                          // suffix shift: region-3 wshort[k] = wm[k+dd]
    lemma_base_A_plus_base_valid(mm, n);
    // bounds + pinch stability of wm[i], wm[j].
    assert(0 <= i < j < big_m);
    lemma_seg_stable_iff(mm, n, m, slice, wm[i]);
    lemma_seg_stable_iff(mm, n, m, slice, wm[j]);
    assert(seg_stable(mm, n, wm[i]));
    assert(seg_stable(mm, n, wm[j]));
    assert(pre.len() == i);
    assert(suf.len() == big_m - j - 1);
    assert(wshort.len() == cap_w);

    assert forall|a: int, b: int|
        (0 <= a <= b <= wshort.len()
            && (a == 0 || seg_stable(mm, n, wshort[a - 1]))
            && (b == wshort.len() || seg_stable(mm, n, wshort[b]))
            && (forall|k: int| a <= k < b ==> !seg_stable(mm, n, wshort[k])))
        implies #[trigger] in_generated_subgroup(bp, ub, wshort.subrange(a, b)) by {
        // ---- exclusion: a,b ∉ (i, i+lp) (the phi-region is stable-free, so a maximal run can't
        //      have a boundary strictly inside it). ----
        if i < a < i + lp {
            lemma_wshort_at(wm, phi_g, i, j, a - 1);
            assert(wshort[a - 1] == phi_g[a - 1 - i]);
            assert(!seg_stable(mm, n, phi_g[a - 1 - i]));    // 0 <= a-1-i < lp
            assert(a != 0);
            assert(false);
        }
        if i < b < i + lp {
            lemma_wshort_at(wm, phi_g, i, j, b);
            assert(wshort[b] == phi_g[b - i]);
            assert(!seg_stable(mm, n, phi_g[b - i]));
            assert(b < cap_w);                                // b < i+lp <= cap_w
            assert(false);
        }
        // now a <= i || a >= i+lp, and b <= i || b >= i+lp.

        if b <= i {
            // ======== Config 1: run inside the prefix → a maximal run of wm. ========
            // wshort[a..b] == wm[a..b].
            assert(wshort.subrange(a, b) =~= wm.subrange(a, b)) by {
                assert forall|r: int| 0 <= r < b - a
                    implies wshort.subrange(a, b)[r] == wm.subrange(a, b)[r] by {
                    lemma_wshort_at(wm, phi_g, i, j, a + r);   // a+r < b <= i ⟹ region 1
                    assert(wshort.subrange(a, b)[r] == wshort[a + r]);
                    assert(wm.subrange(a, b)[r] == wm[a + r]);
                }
            }
            // wm run conditions for [a,b).
            assert(a == 0 || seg_stable(mm, n, wm[a - 1])) by {
                if a != 0 {
                    lemma_wshort_at(wm, phi_g, i, j, a - 1);    // a-1 < i ⟹ region 1
                    assert(wshort[a - 1] == wm[a - 1]);
                }
            }
            assert(b == big_m || seg_stable(mm, n, wm[b])) by {
                if b < i {
                    lemma_wshort_at(wm, phi_g, i, j, b);        // region 1
                    assert(wshort[b] == wm[b]);
                    assert(b < cap_w);
                } // else b == i: seg_stable(wm[i]) already in scope.
            }
            assert forall|kk: int| a <= kk < b implies !seg_stable(mm, n, wm[kk]) by {
                lemma_wshort_at(wm, phi_g, i, j, kk);           // kk < b <= i ⟹ region 1
                assert(wshort[kk] == wm[kk]);
            }
            lemma_seg_inv_run_in_ub(mm, n, wm, a, b);
        } else if a >= i + lp {
            // ======== Config 3: run inside the suffix → a maximal run of wm (shifted by dd). ========
            assert(wshort.subrange(a, b) =~= wm.subrange(a + dd, b + dd)) by {
                assert forall|r: int| 0 <= r < b - a
                    implies wshort.subrange(a, b)[r] == wm.subrange(a + dd, b + dd)[r] by {
                    lemma_wshort_at(wm, phi_g, i, j, a + r);    // a+r >= i+lp ⟹ region 3
                    assert(wshort.subrange(a, b)[r] == wshort[a + r]);
                    assert(wshort[a + r] == wm[(a + r) - i - lp + j + 1]);
                    assert((a + r) - i - lp + j + 1 == (a + dd) + r);
                    assert(wm.subrange(a + dd, b + dd)[r] == wm[(a + dd) + r]);
                }
            }
            // wm run conditions for [a+dd, b+dd).  a+dd >= j+1 >= 1.
            assert(a + dd >= j + 1);
            assert(b + dd <= big_m);
            assert((a + dd) == 0 || seg_stable(mm, n, wm[(a + dd) - 1])) by {
                if a == i + lp {
                    assert((a + dd) - 1 == j);                   // seg_stable(wm[j])
                } else {
                    assert(a > i + lp && a != 0);
                    lemma_wshort_at(wm, phi_g, i, j, a - 1);     // a-1 >= i+lp ⟹ region 3
                    assert(wshort[a - 1] == wm[(a - 1) - i - lp + j + 1]);
                    assert((a - 1) - i - lp + j + 1 == (a + dd) - 1);
                }
            }
            assert((b + dd) == big_m || seg_stable(mm, n, wm[b + dd])) by {
                if b < cap_w {
                    lemma_wshort_at(wm, phi_g, i, j, b);         // b >= a >= i+lp ⟹ region 3
                    assert(wshort[b] == wm[b - i - lp + j + 1]);
                    assert(b - i - lp + j + 1 == b + dd);
                }
            }
            assert forall|kk: int| (a + dd) <= kk < (b + dd) implies !seg_stable(mm, n, wm[kk]) by {
                let k0 = kk - dd;                                 // k0 in [a,b), region 3
                assert(a <= k0 < b);
                lemma_wshort_at(wm, phi_g, i, j, k0);
                assert(wshort[k0] == wm[k0 - i - lp + j + 1]);
                assert(k0 - i - lp + j + 1 == kk);
            }
            lemma_seg_inv_run_in_ub(mm, n, wm, a + dd, b + dd);
        } else {
            // ======== Config 2: the MERGED run = wm[a..i] · phi_g · wm[j+1..b+dd]. ========
            assert(a <= i && b >= i + lp);
            let bd = b + dd;                                      // = b - i - lp + j + 1
            let cap_p = wm.subrange(a, i);                        // pre piece
            let cap_y = wm.subrange(j + 1, bd);                   // suf piece
            assert(j + 1 <= bd <= big_m);
            // splice equality: wshort[a..b] == (cap_p + phi_g) + cap_y.
            assert(wshort.subrange(a, b) =~= (cap_p + phi_g) + cap_y) by {
                let tgt = (cap_p + phi_g) + cap_y;
                assert(cap_p.len() == i - a);
                assert(cap_y.len() == bd - (j + 1));
                assert(tgt.len() == b - a);
                assert forall|r: int| 0 <= r < b - a
                    implies wshort.subrange(a, b)[r] == tgt[r] by {
                    lemma_wshort_at(wm, phi_g, i, j, a + r);
                    assert(wshort.subrange(a, b)[r] == wshort[a + r]);
                    if r < i - a {
                        assert(a + r < i);                       // region 1
                        assert(tgt[r] == (cap_p + phi_g)[r]);
                        assert((cap_p + phi_g)[r] == cap_p[r]);
                        assert(cap_p[r] == wm[a + r]);
                    } else if r < (i - a) + lp {
                        assert(i <= a + r < i + lp);             // region 2
                        assert(tgt[r] == (cap_p + phi_g)[r]);
                        assert((cap_p + phi_g)[r] == phi_g[r - (i - a)]);
                        assert(r - (i - a) == a + r - i);
                    } else {
                        assert(a + r >= i + lp);                 // region 3
                        assert(tgt[r] == cap_y[r - ((i - a) + lp)]);
                        assert(cap_y[r - ((i - a) + lp)] == wm[(j + 1) + (r - ((i - a) + lp))]);
                        assert((j + 1) + (r - ((i - a) + lp)) == (a + r) - i - lp + j + 1);
                    }
                }
            }
            // cap_p ∈ ⟨ub⟩: maximal run of wm (right end = stable wm[i]), or empty when a == i.
            if a < i {
                assert(a == 0 || seg_stable(mm, n, wm[a - 1])) by {
                    if a != 0 {
                        lemma_wshort_at(wm, phi_g, i, j, a - 1);  // a-1 < i ⟹ region 1
                        assert(wshort[a - 1] == wm[a - 1]);
                    }
                }
                assert forall|kk: int| a <= kk < i implies !seg_stable(mm, n, wm[kk]) by {
                    lemma_wshort_at(wm, phi_g, i, j, kk);          // kk < i ⟹ region 1
                    assert(wshort[kk] == wm[kk]);
                    assert(a <= kk < b);                           // i <= b
                }
                lemma_seg_inv_run_in_ub(mm, n, wm, a, i);
            } else {
                assert(a == i);
                assert(cap_p =~= empty_word());
                lemma_empty_in_subgroup(bp, ub);
            }
            assert(in_generated_subgroup(bp, ub, cap_p));
            // cap_y ∈ ⟨ub⟩: maximal run of wm (left end = stable wm[j]), or empty when b == i+lp.
            if b > i + lp {
                assert(j + 1 < bd);
                assert((bd) == big_m || seg_stable(mm, n, wm[bd])) by {
                    if b < cap_w {
                        lemma_wshort_at(wm, phi_g, i, j, b);       // b >= i+lp ⟹ region 3
                        assert(wshort[b] == wm[b - i - lp + j + 1]);
                        assert(b - i - lp + j + 1 == bd);
                    }
                }
                assert forall|kk: int| (j + 1) <= kk < bd implies !seg_stable(mm, n, wm[kk]) by {
                    let k0 = kk - dd;                              // k0 in [i+lp, b), region 3
                    assert(i + lp <= k0 < b);
                    lemma_wshort_at(wm, phi_g, i, j, k0);
                    assert(wshort[k0] == wm[k0 - i - lp + j + 1]);
                    assert(k0 - i - lp + j + 1 == kk);
                    assert(a <= k0 < b);                           // a <= i <= i+lp <= k0
                }
                lemma_seg_inv_run_in_ub(mm, n, wm, j + 1, bd);
            } else {
                assert(b == i + lp);
                assert(bd == j + 1);
                assert(cap_y =~= empty_word());
                lemma_empty_in_subgroup(bp, ub);
            }
            assert(in_generated_subgroup(bp, ub, cap_y));
            // product: (cap_p + phi_g) + cap_y ∈ ⟨ub⟩.
            lemma_product_in_subgroup(bp, ub, cap_p, phi_g);
            lemma_product_in_subgroup(bp, ub, cap_p + phi_g, cap_y);
            assert(in_generated_subgroup(bp, ub, wshort.subrange(a, b)));
        }
    }
    assert(seg_inv(mm, n, wshort));
}

// ----------------------------------------------------------------------------
// Brick E — the pinch-descent (mirror `lemma_map_a_pinch_descends`).
// ----------------------------------------------------------------------------

/// **Brick E — `lemma_cs5_pinch_descends`.**  A `recog_data` pinch of `emb(a_col_machine, wm)`
/// descends (given `seg_inv(wm)`) to a `base_A_plus_data(h0_filter(betas))` pinch of `wm`.  Mirror of
/// `lemma_map_a_pinch_descends`: the single-gen relabel `a_col_machine` carries stable↔stable; the
/// recog pinch-middle membership reflects through `ρ` (C1, `lemma_cs5_middle_reflect`) to a
/// `base_A_plus_base` membership in the recog column (`config`/`assoc_rhs` over `betas`), `seg_inv`
/// lands it in `⟨ublock_db_gens⟩` (`lemma_seg_inv_middle`), and the H₀-restriction (C2 / C2-b) cuts the
/// slice to `h0_filter(betas)` — the target a/b-column.
pub proof fn lemma_cs5_pinch_descends(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, wm: Word)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        2 * n < m,
        alphas.no_duplicates(),
        !alphas.contains(0nat),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(wm, (g_m(mm).num_generators + n + 2) as nat),
        seg_inv(mm, n, wm),
        has_pinch(recog_data(mm, n, m, alphas), apply_embedding(a_col_machine(mm, n), wm)),
    ensures
        has_pinch(base_A_plus_data(mm, n, m, h0_filter(mm, betas(alphas))), wm),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let ng1 = (nk + n + 1) as nat;           // base_A_plus_base gens = machine/target stable index
    let bet = betas(alphas);
    let hf = h0_filter(mm, bet);
    let rd = recog_data(mm, n, m, alphas);
    let am = a_col_machine(mm, n);
    let pw = apply_embedding(am, wm);
    let p_rec = p_idx(nk, n);                 // recog stable letter index
    let bp = base_A_plus_base(mm, n);
    let target = base_A_plus_data(mm, n, m, hf);

    lemma_betas_index(alphas);
    lemma_betas_numbers_word(n, m, alphas);
    lemma_betas_no_duplicates(alphas);
    assert(bet.len() == alphas.len() + 1);

    lemma_machine_col_len(mm, n);
    assert(am.len() == nk + n + 2);
    lemma_h1_base_num_generators(mm, n);
    assert(rd.base.num_generators == p_rec);
    assert(rd.base == h1_base(mm, n));
    lemma_base_A_plus_data_shape(mm, n, m, hf);
    assert(target.base.num_generators == ng1);
    assert(target.base == bp);

    // single-gen relabel.
    lemma_a_col_machine_single_gen(mm, n);
    lemma_single_gen_relabel(am, wm);
    assert(pw.len() == wm.len());
    assert(forall|k: int| 0 <= k < wm.len() ==> #[trigger] pw[k] == relabel_symbol(am, wm[k]));

    // find the recog pinch.
    let ij = choose|i: int, j: int| has_pinch_at(rd, pw, i, j);
    let i = ij.0;
    let j = ij.1;
    assert(has_pinch_at(rd, pw, i, j));
    assert(has_adjacent_opposite_at(rd, pw, i, j));
    assert(0 <= i < j < wm.len());

    // per-symbol stable correspondence (machine stable ↔ recog stable).
    assert forall|k: int| 0 <= k < wm.len() implies (
        (pw[k] == Symbol::Gen(p_rec) <==> wm[k] == Symbol::Gen(ng1))
        && (pw[k] == Symbol::Inv(p_rec) <==> wm[k] == Symbol::Inv(ng1))
        && (is_stable(rd, pw[k]) <==> seg_stable(mm, n, wm[k]))
    ) by {
        assert(symbol_valid(wm[k], (nk + n + 2) as nat));
        lemma_a_col_machine_relabel_sym(mm, n, wm[k]);
        assert(pw[k] == relabel_symbol(am, wm[k]));
    }

    // has_adjacent_opposite_at(target, wm, i, j).
    assert(has_adjacent_opposite_at(target, wm, i, j)) by {
        lemma_seg_stable_iff(mm, n, m, hf, wm[i]);
        lemma_seg_stable_iff(mm, n, m, hf, wm[j]);
        assert(is_stable(rd, pw[i]) && is_stable(rd, pw[j]));
        assert(is_stable(target, wm[i]) && is_stable(target, wm[j]));
        assert(wm[i] != wm[j]) by {
            if wm[i] == wm[j] {
                assert(pw[i] == relabel_symbol(am, wm[i]));
                assert(pw[j] == relabel_symbol(am, wm[j]));
            }
        }
        assert forall|k: int| i < k < j implies !is_stable(target, #[trigger] wm[k]) by {
            assert(!is_stable(rd, pw[k]));
            lemma_seg_stable_iff(mm, n, m, hf, wm[k]);
        }
    }

    // the middle word, valid over ng1 (interior avoids the machine stable letter).
    let mid_w = wm.subrange(i + 1, j);
    assert(word_valid(mid_w, ng1)) by {
        assert forall|t: int| 0 <= t < mid_w.len() implies symbol_valid(#[trigger] mid_w[t], ng1) by {
            assert(mid_w[t] == wm[i + 1 + t]);
            assert(i < i + 1 + t < j);
            assert(!is_stable(target, wm[i + 1 + t]));
            assert(symbol_valid(wm[i + 1 + t], (nk + n + 2) as nat));
            assert(generator_index(wm[i + 1 + t]) != ng1) by {
                if generator_index(wm[i + 1 + t]) == ng1 {
                    match wm[i + 1 + t] {
                        Symbol::Gen(gg) => { assert(wm[i + 1 + t] == Symbol::Gen(ng1)); },
                        Symbol::Inv(gg) => { assert(wm[i + 1 + t] == Symbol::Inv(ng1)); },
                    }
                }
            }
        }
    }
    lemma_single_gen_relabel_subrange(am, wm, i + 1, j);
    assert(pw.subrange(i + 1, j) =~= apply_embedding(am, mid_w));

    // recog / target columns.
    let rd_a_col = Seq::new(rd.associations.len(), |k: int| rd.associations[k].0);
    let rd_b_col = Seq::new(rd.associations.len(), |k: int| rd.associations[k].1);
    let tgt_a_col = Seq::new(target.associations.len(), |k: int| target.associations[k].0);
    let tgt_b_col = Seq::new(target.associations.len(), |k: int| target.associations[k].1);
    assert(tgt_a_col =~= config_emb(hf)) by {
        assert(target.associations.len() == hf.len());
        assert forall|k: int| 0 <= k < hf.len() implies tgt_a_col[k] =~= config_emb(hf)[k] by {
            assert(target.associations[k].0 == config_word(hf[k], 0));
        }
    }
    assert(tgt_b_col =~= assoc_rhs_emb(mm, n, m, hf)) by {
        assert(target.associations.len() == hf.len());
        assert forall|k: int| 0 <= k < hf.len()
            implies tgt_b_col[k] =~= assoc_rhs_emb(mm, n, m, hf)[k] by {
            assert(target.associations[k].1 == assoc_rhs_machine(mm, n, m, hf[k]));
        }
    }

    // betas-column validities over ng1 (C1 preconds).
    assert forall|k: int| 0 <= k < config_emb(bet).len()
        implies word_valid(#[trigger] config_emb(bet)[k], ng1) by {
        assert(config_emb(bet)[k] == config_word(bet[k], 0));
        lemma_config_word_valid(bet[k], 0);
        lemma_word_valid_mono(config_word(bet[k], 0), 3, ng1);
    }
    assert forall|k: int| 0 <= k < assoc_rhs_emb(mm, n, m, bet).len()
        implies word_valid(#[trigger] assoc_rhs_emb(mm, n, m, bet)[k], ng1) by {
        assert(assoc_rhs_emb(mm, n, m, bet)[k] == assoc_rhs_machine(mm, n, m, bet[k]));
        lemma_w_c_valid(nk, n, m, bet[k], ng1);
        lemma_single_gen_valid((nk + n) as nat, ng1);
        lemma_config_word_valid(bet[k], 0);
        lemma_word_valid_mono(config_word(bet[k], 0), 3, ng1);
        lemma_concat_word_valid(config_word(bet[k], 0), w_b(nk, n, m, bet[k]), ng1);
        lemma_concat_word_valid(config_word(bet[k], 0) + w_b(nk, n, m, bet[k]),
            seq![Symbol::Gen((nk + n) as nat)], ng1);
        assert(assoc_rhs_machine(mm, n, m, bet[k])
            =~= (config_word(bet[k], 0) + w_b(nk, n, m, bet[k])) + seq![Symbol::Gen((nk + n) as nat)]);
    }

    // seg_inv: middle ∈ ⟨ublock_db_gens⟩ (orientation-independent).
    lemma_seg_inv_middle(mm, n, m, hf, wm, i, j);
    assert(in_generated_subgroup(bp, ublock_db_gens(mm, n), mid_w));

    // orientation + middle descent.
    assert(has_pinch_at(target, wm, i, j)) by {
        assert(is_stable(rd, pw[i]));
        if pw[i] == Symbol::Gen(p_rec) {
            // t·g·t⁻¹: recog middle ∈ ⟨rd b-col⟩ = ⟨compose(am, assoc_rhs_emb(betas))⟩.
            assert(pw[j] == Symbol::Inv(p_rec));
            assert(wm[i] == Symbol::Gen(ng1));
            assert(wm[j] == Symbol::Inv(ng1));
            assert(in_generated_subgroup(rd.base, rd_b_col, pw.subrange(i + 1, j)));
            lemma_cs5_b_col_correspondence(mm, n, m, alphas);
            assert(rd_b_col =~= compose_embeddings(am, assoc_rhs_emb(mm, n, m, bet)));
            assert(in_generated_subgroup(h1_base(mm, n),
                compose_embeddings(am, assoc_rhs_emb(mm, n, m, bet)), apply_embedding(am, mid_w)));
            lemma_cs5_middle_reflect(mm, n, assoc_rhs_emb(mm, n, m, bet), mid_w);
            assert(in_generated_subgroup(bp, assoc_rhs_emb(mm, n, m, bet), mid_w));
            lemma_cs5_middle_h0_restrict_b(mm, n, m, bet, mid_w);
            assert(in_generated_subgroup(bp, assoc_rhs_emb(mm, n, m, hf), mid_w));
            assert(in_generated_subgroup(bp, tgt_b_col, mid_w));
        } else {
            // t⁻¹·g·t: recog middle ∈ ⟨rd a-col⟩ = ⟨compose(am, config_emb(betas))⟩.
            assert(pw[i] == Symbol::Inv(p_rec));
            assert(pw[j] == Symbol::Gen(p_rec));
            assert(wm[i] == Symbol::Inv(ng1));
            assert(wm[j] == Symbol::Gen(ng1));
            assert(in_generated_subgroup(rd.base, rd_a_col, pw.subrange(i + 1, j)));
            lemma_cs5_a_col_correspondence(mm, n, m, alphas);
            assert(rd_a_col =~= compose_embeddings(am, config_emb(bet)));
            assert(in_generated_subgroup(h1_base(mm, n),
                compose_embeddings(am, config_emb(bet)), apply_embedding(am, mid_w)));
            lemma_cs5_middle_reflect(mm, n, config_emb(bet), mid_w);
            assert(in_generated_subgroup(bp, config_emb(bet), mid_w));
            lemma_cs5_middle_h0_restrict(mm, n, bet, mid_w);
            assert(in_generated_subgroup(bp, config_emb(hf), mid_w));
            assert(in_generated_subgroup(bp, tgt_a_col, mid_w));
        }
    }
    assert(has_pinch(target, wm)) by { assert(has_pinch_at(target, wm, i, j)); }
}

// ----------------------------------------------------------------------------
// Brick F groundwork — `phi_g ∈ ⟨ublock⟩` (the pinch-out replacement middle stays in the segment
// subgroup).  Core: `config(β,0) ∈ ⟨g_subgens⟩` REQUIRES `(β,0)∈H₀` (k_commutes), so the H₀-filtered
// slice is exactly what keeps `seg_inv` alive across the splice.
// ----------------------------------------------------------------------------

/// Generic: a subgroup membership over an HNN base lifts to the HNN presentation (the base-derivation
/// is an HNN-derivation — more relators).
pub proof fn lemma_subgroup_base_to_hnn(data: HNNData, gens: Seq<Word>, w: Word)
    requires
        in_generated_subgroup(data.base, gens, w),
    ensures
        in_generated_subgroup(hnn_presentation(data), gens, w),
{
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(gens, f)
        && equiv_in_presentation(data.base, concat_all(f), w);
    assert(factors_from_generators(gens, factors)
        && equiv_in_presentation(data.base, concat_all(factors), w));
    lemma_base_embeds_in_hnn(data, concat_all(factors), w);
    assert(in_generated_subgroup(hnn_presentation(data), gens, w));    // same factors witness
}

/// **The H₀-restricted config landing.** For `(β,0)∈H₀`, `config(β,0) ∈ ⟨ublock_db_gens⟩` over
/// `base_A_plus_base`.  Chain: `lemma_theorem1` (H₀ ⟹ k_commutes) → `lemma_k_commutes_implies_subgroup`
/// (∈ ⟨g_subgens⟩ over `b_m`) → base→HNN lift (over `g_m`) → `gm_to_bp` (over `base_A_plus_base`) →
/// `g_subgens` is a prefix of `ublock_db_gens` (superset).
pub proof fn lemma_config_in_ublock(mm: ModMachine, n: nat, beta: nat)
    requires
        mod_machine_wf(mm),
        mm_in_H0(mm, beta, 0),
    ensures
        in_generated_subgroup(base_A_plus_base(mm, n), ublock_db_gens(mm, n), config_word(beta, 0)),
{
    let nk = g_m(mm).num_generators;
    let bp = base_A_plus_base(mm, n);
    let gs = g_subgens(mm);
    let ub = ublock_db_gens(mm, n);
    lemma_g_m_num_generators(mm);
    // H₀ ⟹ k_commutes ⟹ config ∈ ⟨g_subgens⟩ over b_m.
    lemma_theorem1(mm, beta, 0);
    assert(k_commutes(mm, config_word(beta, 0)));
    lemma_k_commutes_implies_subgroup(mm, beta, 0);
    let gdata = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    assert(hnn_presentation(gdata) == g_m(mm));
    assert(in_generated_subgroup(gdata.base, gs, config_word(beta, 0)));
    // lift b_m → g_m.
    lemma_subgroup_base_to_hnn(gdata, gs, config_word(beta, 0));
    assert(in_generated_subgroup(g_m(mm), gs, config_word(beta, 0)));
    // transfer g_m → base_A_plus_base (validities).
    lemma_config_word_valid(beta, 0);
    lemma_word_valid_mono(config_word(beta, 0), 3, nk);
    lemma_g_m_associations_valid(mm);
    assert forall|i: int| 0 <= i < gs.len() implies word_valid(#[trigger] gs[i], nk) by {
        assert(gs[i] == g_m_associations(mm)[i].1);
        assert(word_valid(gs[i], (3 + mm.quads.len()) as nat));
        lemma_word_valid_mono(gs[i], (3 + mm.quads.len()) as nat, nk);
    }
    lemma_machine_subgroup_gm_to_bp(mm, n, gs, config_word(beta, 0));
    assert(in_generated_subgroup(bp, gs, config_word(beta, 0)));
    // ⟨g_subgens⟩ ⊆ ⟨ublock⟩ (g_subgens is a prefix of ublock).
    assert forall|i: int| 0 <= i < gs.len()
        implies exists|k: int| 0 <= k < ub.len() && (#[trigger] gs[i]) == ub[k] by {
        assert(ub[i] == gs[i]);                                  // prefix: ub = gs + tail
    }
    lemma_in_subgroup_gens_superset(bp, gs, ub, config_word(beta, 0));
}

} // verus!
