// Layer 2 — Brick 5, C3.2c / the C-arc: `map_a`'s forward Britton-peel assembly.
//
// Wires the generic forward leaves (`phi_l_forward`: relabel facts + intersection property) to the
// concrete `recog_data` / `pa_data` columns: the column correspondence (`recog` columns are the
// `a_words_F`-images of `pa` columns), the pinch-descent (same-index, since `a_words` is a
// relabeling), and the forward injectivity induction.  See `docs/brick5-c3.2c-plan.md` §5.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, config_word, lemma_g_m_num_generators,
    lemma_config_word_valid, lemma_word_valid_mono, lemma_config_word_zero};
use crate::layout::{d_idx, b_base, b_idx, p_idx, h2_num_gens};
use crate::h3_ii::lemma_phi_assoc_index;
use crate::h3::phi_assoc;
use crate::phi_l_maps::lemma_a_words_is_phi_col0;
use crate::benign::{apply_embedding, in_generated_subgroup, lemma_apply_embedding_valid};
use crate::britton_via_tower::{has_pinch, has_pinch_at, has_adjacent_opposite_at, is_stable,
    has_stable_letter, stable_count, lemma_stable_count_concat, lemma_stable_count_no_stable,
    britton_lemma_full};
use crate::hnn::{HNNData, hnn_presentation, hnn_relator, hnn_relators, stable_letter,
    stable_letter_inv, hnn_data_valid, lemma_base_embeds_in_hnn};
use crate::machine_group::{hnn_a_gens, hnn_b_gens, lemma_stable_conj_factorization,
    lemma_stable_conj_factorization_rev, lemma_emb_respects_source_equiv,
    lemma_stable_count_pos_has_stable, lemma_stable_count_zero_no_stable};
use crate::britton_infra::lemma_hnn_presentation_valid;
use crate::normal_form_afp_textbook::lemma_subgroup_to_k_word;
use crate::presentation::{equiv_in_presentation, presentation_valid, lemma_equiv_transitive,
    lemma_equiv_symmetric};
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_equiv_concat_right};
use crate::phi_l_forward::{relabel_symbol, lemma_a_words_single_gen, lemma_single_gen_relabel,
    lemma_single_gen_relabel_subrange, lemma_a_words_relabel_sym};
use crate::phi_l_lift::{lemma_a_words_on_hnn_relator, lemma_family_II_relator_head_in_h2_II};
use crate::phi_l_iso::lemma_family_II_relator_in_h2_II;
use crate::h3_ii::{h2_II, lemma_recog_data_valid, lemma_recog_presentation};
use crate::f_free_a1::{lemma_recog_associations_isomorphic, lemma_h1_faithful_in_h2_II};
use crate::h1::{lemma_h1_base_num_generators};
use crate::word_numbering::{w_b, w_c, numbers_word, lemma_w_c_valid};
use crate::f_free::{is_free_family, lemma_apply_embedding_agree_prefix};
use crate::higman_operations::free_group;
use crate::h1::{h1_base, lemma_h1_base_valid};
use crate::phi_l_maps::{a_words, a_words_F, lemma_a_words_fixes_config, lemma_a_words_on_pa_rhs,
    lemma_map_a_faithful};
use crate::phi_l_forward::lemma_intersection_property;
use crate::pa_data::{pa_data, pa_rhs, pa_assoc, pa_b_base, lemma_pa_data_shape, lemma_pa_data_valid};
use crate::h2::{p_assoc, td_word};
use crate::h3::lemma_single_gen_valid;
use crate::h3_ii::{recog_data, family_II_assoc, family_II_rhs, compose_embeddings};
use crate::f_free_a1::{betas, lemma_betas_index};

verus! {

// ----------------------------------------------------------------------------
// The a_words / a_words_F agreement bridge + a_words_F column fixes.
// ----------------------------------------------------------------------------

/// **The relabeling bridge**: `a_words = a_words_F.push([p])`, so the two embeddings AGREE on every
/// word valid over `n+3` (the F-generators) — `apply_embedding(a_words, u) =~= apply_embedding(
/// a_words_F, u)`.  Lets the (pub) `a_words` column translations feed the `a_words_F`-based
/// intersection property (`a_words_F` is the free family in `h1_base`).
pub proof fn lemma_a_words_eq_a_words_F(mm: ModMachine, n: nat, u: Word)
    requires
        word_valid(u, (n + 3) as nat),
    ensures
        apply_embedding(a_words(mm, n), u) =~= apply_embedding(a_words_F(mm, n), u),
{
    let aw = a_words(mm, n);
    let awf = a_words_F(mm, n);
    // a_words = a_words_F.push(...) ⟹ len n+4, agrees with a_words_F on [0, n+3).
    assert(aw.len() == n + 4);
    assert(awf.len() == n + 3);
    assert forall|i: int| 0 <= i < n + 3 implies aw[i] == awf[i] by {}
    lemma_apply_embedding_agree_prefix(aw, awf, u, (n + 3) as nat);
}

/// **`a_words_F` fixes a config word**: `apply_embedding(a_words_F, config(γ,0)) =~= config(γ,0)`.
/// Bridges `lemma_a_words_fixes_config` (stated for `a_words`) to `a_words_F` (the free family).
pub proof fn lemma_a_words_F_fixes_config(mm: ModMachine, n: nat, gamma: nat)
    ensures
        apply_embedding(a_words_F(mm, n), config_word(gamma, 0)) =~= config_word(gamma, 0),
{
    lemma_config_word_valid(gamma, 0);                       // word_valid(config(γ,0), 3)
    lemma_word_valid_mono(config_word(gamma, 0), 3, (n + 3) as nat);
    lemma_a_words_eq_a_words_F(mm, n, config_word(gamma, 0));
    lemma_a_words_fixes_config(mm, n, gamma);
}

/// **`a_words_F` carries `pa_rhs` onto `family_II_rhs`**: `apply_embedding(a_words_F, pa_rhs(γ)) =~=
/// family_II_rhs(γ)`.  Bridges `lemma_a_words_on_pa_rhs` (stated for `a_words`) to `a_words_F`.
pub proof fn lemma_a_words_F_on_pa_rhs(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        apply_embedding(a_words_F(mm, n), pa_rhs(n, m, gamma)) =~= family_II_rhs(mm, n, m, gamma),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    // pa_rhs(γ) = config(γ,0) + w_c(3,n,m,γ) + [Gen2], valid over n+3.
    lemma_pa_rhs_valid_n3(mm, n, m, gamma);
    lemma_a_words_eq_a_words_F(mm, n, pa_rhs(n, m, gamma));
    lemma_a_words_on_pa_rhs(mm, n, m, gamma);
}

/// `pa_rhs(γ)` is valid over `n+3` (config uses `{0,1}`, the F-b-block `w_c(3,…)` sits in `[3,n+3)`,
/// `d = Gen(2) < n+3`).  (Re-derives the validity `pa_data` uses, without the full HNN datum.)
proof fn lemma_pa_rhs_valid_n3(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        word_valid(pa_rhs(n, m, gamma), (n + 3) as nat),
{
    let ng = (n + 3) as nat;
    lemma_config_word_valid(gamma, 0);
    lemma_word_valid_mono(config_word(gamma, 0), 3, ng);
    lemma_w_c_valid(pa_b_base(), n, m, gamma, ng);            // 3 + n ≤ n + 3
    lemma_single_gen_valid(2, ng);
    lemma_concat_word_valid(config_word(gamma, 0), w_c(pa_b_base(), n, m, gamma), ng);
    lemma_concat_word_valid(config_word(gamma, 0) + w_c(pa_b_base(), n, m, gamma),
        seq![Symbol::Gen(2)], ng);
    assert(pa_rhs(n, m, gamma) =~= (config_word(gamma, 0) + w_c(pa_b_base(), n, m, gamma))
        + seq![Symbol::Gen(2)]);
}

// ----------------------------------------------------------------------------
// The column correspondence: recog columns = a_words_F-images of pa columns (over betas).
// ----------------------------------------------------------------------------

/// `recog_data`'s a-column and `pa_data(betas)`'s a-column, by index `k` over `betas = [0]++alphas`:
/// both are `config(betas[k], 0)` (recog's `k=0` head `[Gen0]` is `config(0,0)`; `k≥1` is
/// `config(alphas[k-1],0)`).  And `a_words_F` fixes config, so they correspond under `a_words_F`.
proof fn lemma_recog_pa_a_entry(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, k: int)
    requires
        0 <= k < betas(alphas).len(),
    ensures
        recog_data(mm, n, m, alphas).associations[k].0 =~= config_word(betas(alphas)[k], 0),
        pa_data(n, m, betas(alphas)).associations[k].0 == config_word(betas(alphas)[k], 0),
{
    let nk = g_m(mm).num_generators;
    let alp = alphas;
    let bet = betas(alp);
    let rd = recog_data(mm, n, m, alp);
    lemma_betas_index(alp);
    let pa = p_assoc(nk, n);
    let fa = family_II_assoc(mm, n, m, alp);
    assert(rd.associations =~= pa + fa);
    assert(pa.len() == 1);
    // pa_data column.
    assert(pa_data(n, m, bet).associations =~= pa_assoc(n, m, bet));
    assert(pa_data(n, m, bet).associations[k].0 == config_word(bet[k], 0));
    if k == 0 {
        assert(bet[0] == 0);
        assert(rd.associations[0] == pa[0]);
        assert(pa[0].0 == seq![Symbol::Gen(0)]);
        lemma_config_word_zero();                            // config(0,0) =~= [Gen0]
    } else {
        assert(bet[k] == alp[k - 1]);
        assert(rd.associations[k] == fa[k - 1]);
        assert(fa[k - 1].0 == config_word(alp[k - 1], 0));
    }
}

/// `recog_data`'s b-column and `pa_data(betas)`'s b-column, by index `k`: recog's is
/// `family_II_rhs(betas[k])` (`k=0` head `td_word = family_II_rhs(0)`); pa's is `pa_rhs(betas[k])`,
/// and `a_words_F` carries `pa_rhs ↦ family_II_rhs`, so they correspond under `a_words_F`.
proof fn lemma_recog_pa_b_entry(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, k: int)
    requires
        2 * n < m,
        0 <= k < betas(alphas).len(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        recog_data(mm, n, m, alphas).associations[k].1 =~= family_II_rhs(mm, n, m, betas(alphas)[k]),
        pa_data(n, m, betas(alphas)).associations[k].1 == pa_rhs(n, m, betas(alphas)[k]),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let alp = alphas;
    let bet = betas(alp);
    let rd = recog_data(mm, n, m, alp);
    lemma_betas_index(alp);
    let pa = p_assoc(nk, n);
    let fa = family_II_assoc(mm, n, m, alp);
    assert(rd.associations =~= pa + fa);
    assert(pa.len() == 1);
    assert(pa_data(n, m, bet).associations[k].1 == pa_rhs(n, m, bet[k]));
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
        assert(bet[k] == alp[k - 1]);
        assert(rd.associations[k] == fa[k - 1]);
        assert(fa[k - 1].1 == family_II_rhs(mm, n, m, alp[k - 1]));
    }
}

/// **The a-side column correspondence**: `recog`'s a-column equals `compose_embeddings(a_words_F,
/// pa`'s a-column`)`.  (Entry-wise: both are `config(betas[k],0)`, fixed by `a_words_F`.)  This is
/// the `recog_gens = compose_embeddings(ψ, pa_gens)` hypothesis the intersection property needs.
pub proof fn lemma_a_col_correspondence(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    ensures
        Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                 |k: int| recog_data(mm, n, m, alphas).associations[k].0)
        =~= compose_embeddings(a_words_F(mm, n),
                Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                         |k: int| pa_data(n, m, betas(alphas)).associations[k].0)),
{
    let bet = betas(alphas);
    let rd = recog_data(mm, n, m, alphas);
    let pd = pa_data(n, m, bet);
    let rcol = Seq::new(rd.associations.len(), |k: int| rd.associations[k].0);
    let pcol = Seq::new(pd.associations.len(), |k: int| pd.associations[k].0);
    let comp = compose_embeddings(a_words_F(mm, n), pcol);
    assert(rd.associations.len() == bet.len());
    assert(pd.associations.len() == bet.len());
    assert(comp.len() == pcol.len() == bet.len());
    assert forall|k: int| 0 <= k < bet.len() implies rcol[k] =~= comp[k] by {
        lemma_recog_pa_a_entry(mm, n, m, alphas, k);
        // rcol[k] =~= config(bet[k],0);  pcol[k] = config(bet[k],0);
        // comp[k] = apply_embedding(a_words_F, config(bet[k],0)) =~= config(bet[k],0).
        lemma_a_words_F_fixes_config(mm, n, bet[k]);
        assert(comp[k] == apply_embedding(a_words_F(mm, n), pcol[k]));
        assert(pcol[k] == config_word(bet[k], 0));
    }
}

/// **The b-side column correspondence**: `recog`'s b-column equals `compose_embeddings(a_words_F,
/// pa`'s b-column`)`.  (Entry-wise: `recog`'s is `family_II_rhs(betas[k])`, `pa`'s is
/// `pa_rhs(betas[k])`, and `a_words_F` carries `pa_rhs ↦ family_II_rhs`.)
pub proof fn lemma_b_col_correspondence(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                 |k: int| recog_data(mm, n, m, alphas).associations[k].1)
        =~= compose_embeddings(a_words_F(mm, n),
                Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                         |k: int| pa_data(n, m, betas(alphas)).associations[k].1)),
{
    let bet = betas(alphas);
    let rd = recog_data(mm, n, m, alphas);
    let pd = pa_data(n, m, bet);
    let rcol = Seq::new(rd.associations.len(), |k: int| rd.associations[k].1);
    let pcol = Seq::new(pd.associations.len(), |k: int| pd.associations[k].1);
    let comp = compose_embeddings(a_words_F(mm, n), pcol);
    lemma_betas_index(alphas);
    assert(rd.associations.len() == bet.len());
    assert(pd.associations.len() == bet.len());
    assert forall|k: int| 0 <= k < bet.len() implies rcol[k] =~= comp[k] by {
        lemma_recog_pa_b_entry(mm, n, m, alphas, k);
        // numbers_word(bet[k]).
        assert(numbers_word(n, m, bet[k])) by {
            if k == 0 { assert(bet[0] == 0); } else { assert(bet[k] == alphas[k - 1]); }
        }
        lemma_a_words_F_on_pa_rhs(mm, n, m, bet[k]);
        assert(comp[k] == apply_embedding(a_words_F(mm, n), pcol[k]));
        assert(pcol[k] == pa_rhs(n, m, bet[k]));
    }
}

// ----------------------------------------------------------------------------
// The per-side middle descent (intersection property + column correspondence packaged).
// ----------------------------------------------------------------------------

/// **a-side middle descent**: a pinch middle `u` (stable-free, over `n+3`) whose `a_words_F`-image
/// lies in `recog`'s a-subgroup descends to `pa`'s a-subgroup over the free group.  = the
/// intersection property at the a-column, with the column correspondence discharging its hypothesis.
pub proof fn lemma_middle_descent_a(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, u: Word)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(u, (n + 3) as nat),
        in_generated_subgroup(h1_base(mm, n),
            Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                     |k: int| recog_data(mm, n, m, alphas).associations[k].0),
            apply_embedding(a_words_F(mm, n), u)),
    ensures
        in_generated_subgroup(pa_data(n, m, betas(alphas)).base,
            Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                     |k: int| pa_data(n, m, betas(alphas)).associations[k].0),
            u),
{
    let awf = a_words_F(mm, n);
    let pd = pa_data(n, m, betas(alphas));
    let pcol = Seq::new(pd.associations.len(), |k: int| pd.associations[k].0);
    lemma_h1_base_valid(mm, n);
    lemma_pa_data_shape(n, m, betas(alphas));
    lemma_pa_data_valid(n, m, betas(alphas));               // hnn_data_valid(pd): cols valid over n+3
    lemma_map_a_faithful(mm, n);                            // is_free_family(h1_base, awf)
    lemma_a_col_correspondence(mm, n, m, alphas);           // rd a-col == compose(awf, pcol)
    assert(awf.len() == n + 3);
    assert(pd.base == free_group((n + 3) as nat));
    assert(pd.base.num_generators == n + 3);
    assert(hnn_data_valid(pd));
    assert forall|k: int| 0 <= k < pcol.len() implies word_valid(#[trigger] pcol[k], awf.len()) by {
        assert(pcol[k] == pd.associations[k].0);
    }
    lemma_intersection_property(h1_base(mm, n), awf, pcol, u);
}

/// **b-side middle descent**: the mirror at `recog`/`pa`'s b-columns.
pub proof fn lemma_middle_descent_b(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, u: Word)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(u, (n + 3) as nat),
        in_generated_subgroup(h1_base(mm, n),
            Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                     |k: int| recog_data(mm, n, m, alphas).associations[k].1),
            apply_embedding(a_words_F(mm, n), u)),
    ensures
        in_generated_subgroup(pa_data(n, m, betas(alphas)).base,
            Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                     |k: int| pa_data(n, m, betas(alphas)).associations[k].1),
            u),
{
    let awf = a_words_F(mm, n);
    let pd = pa_data(n, m, betas(alphas));
    let pcol = Seq::new(pd.associations.len(), |k: int| pd.associations[k].1);
    lemma_h1_base_valid(mm, n);
    lemma_pa_data_shape(n, m, betas(alphas));
    lemma_pa_data_valid(n, m, betas(alphas));
    lemma_map_a_faithful(mm, n);
    lemma_b_col_correspondence(mm, n, m, alphas);           // rd b-col == compose(awf, pcol)
    assert(awf.len() == n + 3);
    assert(pd.base == free_group((n + 3) as nat));
    assert(pd.base.num_generators == n + 3);
    assert(hnn_data_valid(pd));
    assert forall|k: int| 0 <= k < pcol.len() implies word_valid(#[trigger] pcol[k], awf.len()) by {
        assert(pcol[k] == pd.associations[k].1);
    }
    lemma_intersection_property(h1_base(mm, n), awf, pcol, u);
}

// ----------------------------------------------------------------------------
// The pinch descent (same-index, since a_words is a relabeling).
// ----------------------------------------------------------------------------

/// **`map_a` pinch descent**: a pinch of `apply_embedding(a_words, w)` over `recog_data` descends to
/// a pinch of `w` over `pa_data` — at the SAME indices, since `a_words` is a length-preserving
/// relabeling that maps the `P_A` stable letter to the `recog` one (and F-gens to non-stable gens).
/// The middle membership is the only real content (the per-side intersection descent).
pub proof fn lemma_map_a_pinch_descends(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(w, (n + 4) as nat),
        has_pinch(recog_data(mm, n, m, alphas), apply_embedding(a_words(mm, n), w)),
    ensures
        has_pinch(pa_data(n, m, betas(alphas)), w),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let rd = recog_data(mm, n, m, alphas);
    let pd = pa_data(n, m, betas(alphas));
    let aw = a_words(mm, n);
    let pw = apply_embedding(aw, w);
    let p = p_idx(nk, n);
    let st: nat = (n + 3) as nat;

    lemma_h1_base_num_generators(mm, n);
    assert(rd.base.num_generators == p);
    lemma_pa_data_shape(n, m, betas(alphas));
    assert(pd.base.num_generators == st);

    lemma_a_words_single_gen(mm, n);
    lemma_single_gen_relabel(aw, w);
    assert(pw.len() == w.len());
    assert(forall|k: int| 0 <= k < w.len() ==> #[trigger] pw[k] == relabel_symbol(aw, w[k]));

    let ij = choose|i: int, j: int| has_pinch_at(rd, pw, i, j);
    let i = ij.0;
    let j = ij.1;
    assert(has_pinch_at(rd, pw, i, j));
    assert(has_adjacent_opposite_at(rd, pw, i, j));
    assert(0 <= i < j < w.len());

    // per-symbol stable correspondence (relabel sends P_A stable ↔ recog stable, preserving Gen/Inv).
    assert forall|k: int| 0 <= k < w.len() implies (
        (pw[k] == Symbol::Gen(p) <==> w[k] == Symbol::Gen(st))
        && (pw[k] == Symbol::Inv(p) <==> w[k] == Symbol::Inv(st))
        && (is_stable(rd, pw[k]) <==> is_stable(pd, w[k]))
    ) by {
        assert(symbol_valid(w[k], (n + 4) as nat));
        lemma_a_words_relabel_sym(mm, n, w[k]);
        assert(pw[k] == relabel_symbol(aw, w[k]));
    }

    // has_adjacent_opposite_at(pd, w, i, j).
    assert(has_adjacent_opposite_at(pd, w, i, j)) by {
        assert(is_stable(pd, w[i]) && is_stable(pd, w[j]));
        assert(w[i] != w[j]) by {
            if w[i] == w[j] {
                assert(pw[i] == relabel_symbol(aw, w[i]));
                assert(pw[j] == relabel_symbol(aw, w[j]));
            }
        }
        assert forall|k: int| i < k < j implies !is_stable(pd, #[trigger] w[k]) by {
            assert(!is_stable(rd, pw[k]));
        }
    }

    // the middle word.
    let mid_w = w.subrange(i + 1, j);
    assert(word_valid(mid_w, st)) by {
        assert forall|t: int| 0 <= t < mid_w.len() implies symbol_valid(#[trigger] mid_w[t], st) by {
            assert(mid_w[t] == w[i + 1 + t]);
            assert(i < i + 1 + t < j);
            assert(!is_stable(pd, w[i + 1 + t]));
            assert(symbol_valid(w[i + 1 + t], (n + 4) as nat));
            assert(generator_index(w[i + 1 + t]) != st) by {
                if generator_index(w[i + 1 + t]) == st {
                    match w[i + 1 + t] {
                        Symbol::Gen(gg) => { assert(w[i + 1 + t] == Symbol::Gen(st)); },
                        Symbol::Inv(gg) => { assert(w[i + 1 + t] == Symbol::Inv(st)); },
                    }
                }
            }
        }
    }
    lemma_single_gen_relabel_subrange(aw, w, i + 1, j);
    assert(pw.subrange(i + 1, j) =~= apply_embedding(aw, mid_w));
    lemma_a_words_eq_a_words_F(mm, n, mid_w);
    assert(pw.subrange(i + 1, j) == apply_embedding(a_words_F(mm, n), mid_w));

    let rd_b_col = Seq::new(rd.associations.len(), |k: int| rd.associations[k].1);
    let rd_a_col = Seq::new(rd.associations.len(), |k: int| rd.associations[k].0);
    let pd_b_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].1);
    let pd_a_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].0);
    assert(rd.base == h1_base(mm, n));

    // orientation + middle descent.
    assert(has_pinch_at(pd, w, i, j)) by {
        assert(is_stable(rd, pw[i]));
        if pw[i] == Symbol::Gen(p) {
            // first disjunct of recog pinch: pw[j]=Inv(p), middle ∈ ⟨rd b-gens⟩.
            assert(pw[j] == Symbol::Inv(p));
            assert(w[i] == Symbol::Gen(st));
            assert(w[j] == Symbol::Inv(st));
            assert(in_generated_subgroup(rd.base, rd_b_col, pw.subrange(i + 1, j)));
            assert(in_generated_subgroup(h1_base(mm, n), rd_b_col,
                apply_embedding(a_words_F(mm, n), mid_w)));
            lemma_middle_descent_b(mm, n, m, alphas, mid_w);
            assert(w.subrange(i + 1, j) == mid_w);
            assert(in_generated_subgroup(pd.base, pd_b_col, w.subrange(i + 1, j)));
        } else {
            // pw[i] stable but not Gen(p) ⟹ Inv(p); second disjunct.
            assert(pw[i] == Symbol::Inv(p));
            assert(pw[j] == Symbol::Gen(p));
            assert(w[i] == Symbol::Inv(st));
            assert(w[j] == Symbol::Gen(st));
            assert(in_generated_subgroup(rd.base, rd_a_col, pw.subrange(i + 1, j)));
            assert(in_generated_subgroup(h1_base(mm, n), rd_a_col,
                apply_embedding(a_words_F(mm, n), mid_w)));
            lemma_middle_descent_a(mm, n, m, alphas, mid_w);
            assert(w.subrange(i + 1, j) == mid_w);
            assert(in_generated_subgroup(pd.base, pd_a_col, w.subrange(i + 1, j)));
        }
    }
    assert(has_pinch(pd, w)) by { assert(has_pinch_at(pd, w, i, j)); }
}

// ----------------------------------------------------------------------------
// The generic pinch-out (t^{±1}·g·t^{∓1} ≡ φ(g), a stable-free product) + stable-count drop.
// ----------------------------------------------------------------------------

/// Assemble the pinch-out: given the pinched middle `mid = w[i..j+1]` reduces (in the HNN) to a
/// stable-free base word `phi_g`, splice it back — `w ≡ pre·phi_g·suf` with strictly fewer stable
/// letters (the two `t`'s at `i,j` are gone; `phi_g` and `g` are both stable-free).
proof fn lemma_pinch_assemble(data: HNNData, w: Word, i: int, j: int, phi_g: Word) -> (wshort: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        has_adjacent_opposite_at(data, w, i, j),
        word_valid(phi_g, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w.subrange(i, j + 1), phi_g),
    ensures
        equiv_in_presentation(hnn_presentation(data), w, wshort),
        word_valid(wshort, hnn_presentation(data).num_generators),
        stable_count(data, wshort) < stable_count(data, w),
        wshort == w.subrange(0, i) + phi_g + w.subrange(j + 1, w.len() as int),
{
    let hp = hnn_presentation(data);
    let png = hp.num_generators;
    let ng = data.base.num_generators;
    let pre = w.subrange(0, i);
    let suf = w.subrange(j + 1, w.len() as int);
    let mid = w.subrange(i, j + 1);
    let g = w.subrange(i + 1, j);
    let wshort = pre + phi_g + suf;
    lemma_hnn_presentation_valid(data);
    assert(png == ng + 1);

    // validities (subranges of w; phi_g over ng ≤ png).
    assert(word_valid(pre, png)) by {
        assert forall|t: int| 0 <= t < pre.len() implies symbol_valid(#[trigger] pre[t], png)
        by { assert(pre[t] == w[t]); }
    }
    assert(word_valid(suf, png)) by {
        assert forall|t: int| 0 <= t < suf.len() implies symbol_valid(#[trigger] suf[t], png)
        by { assert(suf[t] == w[j + 1 + t]); }
    }
    assert(word_valid(g, png)) by {
        assert forall|t: int| 0 <= t < g.len() implies symbol_valid(#[trigger] g[t], png)
        by { assert(g[t] == w[i + 1 + t]); }
    }
    assert(word_valid(phi_g, png)) by {
        assert forall|t: int| 0 <= t < phi_g.len() implies symbol_valid(#[trigger] phi_g[t], png)
        by { assert(symbol_valid(phi_g[t], ng)); }
    }
    lemma_concat_word_valid(pre, phi_g, png);
    lemma_concat_word_valid(pre + phi_g, suf, png);

    // w =~= (pre + mid) + suf.
    assert(w =~= (pre + mid) + suf) by {
        assert forall|t: int| 0 <= t < w.len() implies ((pre + mid) + suf)[t] == w[t] by {
            if t < i {
            } else if t < j + 1 {
                assert(mid[t - i] == w[t]);
            } else {
                assert(suf[t - (j + 1)] == w[t]);
            }
        }
    }
    // w ≡ wshort:  mid ≡ phi_g ⟹ pre·mid ≡ pre·phi_g ⟹ (pre·mid)·suf ≡ (pre·phi_g)·suf.
    lemma_equiv_concat_right(hp, pre, mid, phi_g);
    assert(concat(pre, mid) == pre + mid);
    assert(concat(pre, phi_g) == pre + phi_g);
    lemma_equiv_concat_left(hp, pre + mid, pre + phi_g, suf);
    assert(concat(pre + mid, suf) == (pre + mid) + suf);
    assert(concat(pre + phi_g, suf) == wshort);
    assert(equiv_in_presentation(hp, w, wshort));

    // stable-count drop.
    // mid =~= ([w[i]] + g) + [w[j]] ;  stable_count(mid) = 1 + 0 + 1 = 2.
    assert(mid =~= (seq![w[i]] + g) + seq![w[j]]) by {
        assert forall|t: int| 0 <= t < mid.len() implies ((seq![w[i]] + g) + seq![w[j]])[t] == mid[t] by {
            assert(mid[t] == w[i + t]);
            if t == 0 {
            } else if t < mid.len() - 1 {
                assert(g[t - 1] == w[i + t]);
            } else {
            }
        }
    }
    assert(stable_count(data, g) == 0) by {
        assert forall|t: int| 0 <= t < g.len() implies !is_stable(data, #[trigger] g[t]) by {
            assert(g[t] == w[i + 1 + t]);
            assert(i < i + 1 + t < j);
        }
        lemma_stable_count_no_stable(data, g);
    }
    assert(stable_count(data, seq![w[i]]) == 1) by {
        reveal_with_fuel(stable_count, 2);
        assert(seq![w[i]].last() == w[i]);
        assert(seq![w[i]].drop_last() =~= Seq::<Symbol>::empty());
        assert(is_stable(data, w[i]));
    }
    assert(stable_count(data, seq![w[j]]) == 1) by {
        reveal_with_fuel(stable_count, 2);
        assert(seq![w[j]].last() == w[j]);
        assert(seq![w[j]].drop_last() =~= Seq::<Symbol>::empty());
        assert(is_stable(data, w[j]));
    }
    lemma_stable_count_concat(data, seq![w[i]], g);
    assert(concat(seq![w[i]], g) == seq![w[i]] + g);
    lemma_stable_count_concat(data, seq![w[i]] + g, seq![w[j]]);
    assert(concat(seq![w[i]] + g, seq![w[j]]) == (seq![w[i]] + g) + seq![w[j]]);
    assert(stable_count(data, mid) == 2);
    // stable_count(phi_g) == 0 (stable-free).
    assert(stable_count(data, phi_g) == 0) by {
        assert forall|t: int| 0 <= t < phi_g.len() implies !is_stable(data, #[trigger] phi_g[t])
        by { assert(symbol_valid(phi_g[t], ng)); }
        lemma_stable_count_no_stable(data, phi_g);
    }
    // stable_count(w) = sc(pre)+2+sc(suf);  stable_count(wshort) = sc(pre)+0+sc(suf).
    lemma_stable_count_concat(data, pre, mid);
    lemma_stable_count_concat(data, pre + mid, suf);
    assert(stable_count(data, w) == stable_count(data, pre) + 2 + stable_count(data, suf)) by {
        assert(w =~= (pre + mid) + suf);
        assert(concat(pre, mid) == pre + mid);
        assert(concat(pre + mid, suf) == (pre + mid) + suf);
    }
    lemma_stable_count_concat(data, pre, phi_g);
    lemma_stable_count_concat(data, pre + phi_g, suf);
    assert(concat(pre, phi_g) == pre + phi_g);
    assert(concat(pre + phi_g, suf) == wshort);
    wshort
}

/// **Generic pinch-out**: a pinched word reduces (in the HNN) to a strictly stable-count-smaller
/// word.  Both orientations use the conjugation factorization (`lemma_stable_conj_factorization`
/// / `_rev`): the middle `g ∈ ⟨a-gens⟩` (resp. `⟨b-gens⟩`) has a preimage `u`
/// (`lemma_subgroup_to_k_word`), so `t⁻¹·g·t ≡ ψ(b-gens, u)` (resp. `t·g·t⁻¹ ≡ ψ(a-gens, u)`), a
/// stable-free base word, spliced back by `lemma_pinch_assemble`.
pub proof fn lemma_pd_pinch_out(data: HNNData, w: Word, i: int, j: int) -> (wshort: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        has_pinch_at(data, w, i, j),
    ensures
        equiv_in_presentation(hnn_presentation(data), w, wshort),
        word_valid(wshort, hnn_presentation(data).num_generators),
        stable_count(data, wshort) < stable_count(data, w),
{
    let hp = hnn_presentation(data);
    let png = hp.num_generators;
    let ng = data.base.num_generators;
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    let g = w.subrange(i + 1, j);
    let ag = hnn_a_gens(data);
    let bg = hnn_b_gens(data);
    let k = data.associations.len();
    lemma_hnn_presentation_valid(data);
    assert(png == ng + 1);
    assert(st == Symbol::Gen(ng) && si == Symbol::Inv(ng));
    // a/b-gens valid over ng.
    assert forall|t: int| 0 <= t < ag.len() implies word_valid(#[trigger] ag[t], ng) by {
        assert(ag[t] == data.associations[t].0);
    }
    assert forall|t: int| 0 <= t < bg.len() implies word_valid(#[trigger] bg[t], ng) by {
        assert(bg[t] == data.associations[t].1);
    }
    // mid =~= [w[i]] + g + [w[j]].
    assert(w.subrange(i, j + 1) =~= (seq![w[i]] + g) + seq![w[j]]) by {
        assert forall|t: int| 0 <= t < w.subrange(i, j + 1).len()
            implies ((seq![w[i]] + g) + seq![w[j]])[t] == w.subrange(i, j + 1)[t] by {
            assert(w.subrange(i, j + 1)[t] == w[i + t]);
            if t != 0 && t < w.subrange(i, j + 1).len() - 1 { assert(g[t - 1] == w[i + t]); }
        }
    }
    if w[i] == si {
        // t⁻¹·g·t:  g ∈ ⟨a-gens⟩.
        assert(w[j] == st);
        assert(in_generated_subgroup(data.base, ag, g));
        lemma_subgroup_to_k_word(data.base, ag, g);
        let u = choose|u: Word| word_valid(u, ag.len())
            && equiv_in_presentation(data.base, apply_embedding(ag, u), g);
        assert(word_valid(u, ag.len()) && equiv_in_presentation(data.base, apply_embedding(ag, u), g));
        assert(ag.len() == k);
        let phi_g = apply_embedding(bg, u);
        lemma_apply_embedding_valid(bg, u, ng);                  // phi_g valid over ng
        lemma_apply_embedding_valid(ag, u, ng);
        lemma_word_valid_mono(apply_embedding(ag, u), ng, png);
        // [si]·g·[st] ≡ [si]·ψ(ag,u)·[st] ≡ ψ(bg,u) = phi_g.
        lemma_base_embeds_in_hnn(data, apply_embedding(ag, u), g);      // ψ(ag,u) ≡_HNN g
        lemma_equiv_symmetric(hp, apply_embedding(ag, u), g);          // g ≡_HNN ψ(ag,u)
        lemma_equiv_concat_right(hp, seq![si], g, apply_embedding(ag, u));
        assert(concat(seq![si], g) == seq![si] + g);
        assert(concat(seq![si], apply_embedding(ag, u)) == seq![si] + apply_embedding(ag, u));
        lemma_equiv_concat_left(hp, seq![si] + g, seq![si] + apply_embedding(ag, u), seq![st]);
        assert(concat(seq![si] + g, seq![st]) == (seq![si] + g) + seq![st]);
        assert(concat(seq![si] + apply_embedding(ag, u), seq![st])
            == (seq![si] + apply_embedding(ag, u)) + seq![st]);
        lemma_stable_conj_factorization(data, u);                // [si]·ψ(ag,u)·[st] ≡ ψ(bg,u)
        assert(seq![si] + apply_embedding(ag, u) + seq![st]
            == (seq![si] + apply_embedding(ag, u)) + seq![st]);
        lemma_equiv_transitive(hp, (seq![si] + g) + seq![st],
            (seq![si] + apply_embedding(ag, u)) + seq![st], phi_g);
        assert(w.subrange(i, j + 1) == (seq![w[i]] + g) + seq![w[j]]);
        assert((seq![w[i]] + g) + seq![w[j]] == (seq![si] + g) + seq![st]);
        assert(equiv_in_presentation(hp, w.subrange(i, j + 1), phi_g));
        lemma_pinch_assemble(data, w, i, j, phi_g)
    } else {
        // t·g·t⁻¹:  w[i]==st, w[j]==si, g ∈ ⟨b-gens⟩.
        assert(w[i] == st && w[j] == si);
        assert(in_generated_subgroup(data.base, bg, g));
        lemma_subgroup_to_k_word(data.base, bg, g);
        let u = choose|u: Word| word_valid(u, bg.len())
            && equiv_in_presentation(data.base, apply_embedding(bg, u), g);
        assert(word_valid(u, bg.len()) && equiv_in_presentation(data.base, apply_embedding(bg, u), g));
        assert(bg.len() == k);
        let psi_g = apply_embedding(ag, u);
        lemma_apply_embedding_valid(ag, u, ng);
        lemma_apply_embedding_valid(bg, u, ng);
        lemma_word_valid_mono(apply_embedding(bg, u), ng, png);
        lemma_base_embeds_in_hnn(data, apply_embedding(bg, u), g);
        lemma_equiv_symmetric(hp, apply_embedding(bg, u), g);
        lemma_equiv_concat_right(hp, seq![st], g, apply_embedding(bg, u));
        assert(concat(seq![st], g) == seq![st] + g);
        assert(concat(seq![st], apply_embedding(bg, u)) == seq![st] + apply_embedding(bg, u));
        lemma_equiv_concat_left(hp, seq![st] + g, seq![st] + apply_embedding(bg, u), seq![si]);
        assert(concat(seq![st] + g, seq![si]) == (seq![st] + g) + seq![si]);
        assert(concat(seq![st] + apply_embedding(bg, u), seq![si])
            == (seq![st] + apply_embedding(bg, u)) + seq![si]);
        lemma_stable_conj_factorization_rev(data, u);            // [st]·ψ(bg,u)·[si] ≡ ψ(ag,u)
        assert(seq![st] + apply_embedding(bg, u) + seq![si]
            == (seq![st] + apply_embedding(bg, u)) + seq![si]);
        lemma_equiv_transitive(hp, (seq![st] + g) + seq![si],
            (seq![st] + apply_embedding(bg, u)) + seq![si], psi_g);
        assert(w.subrange(i, j + 1) == (seq![w[i]] + g) + seq![w[j]]);
        assert((seq![w[i]] + g) + seq![w[j]] == (seq![st] + g) + seq![si]);
        assert(equiv_in_presentation(hp, w.subrange(i, j + 1), psi_g));
        lemma_pinch_assemble(data, w, i, j, psi_g)
    }
}

// ----------------------------------------------------------------------------
// The forward injectivity induction (map_a faithful).
// ----------------------------------------------------------------------------

/// Each `a_words[i]` (a single literal generator) is valid over `h2_II`'s generator count
/// `h2_num_gens = nk+2n+2` (the max image index is `p_idx = nk+2n+1`).
pub proof fn lemma_a_words_img_valid(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < n + 4,
    ensures
        word_valid(a_words(mm, n)[i], h2_num_gens(g_m(mm).num_generators, n)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    lemma_a_words_is_phi_col0(mm, n, 1, 1);
    lemma_phi_assoc_index(nk, n, 1, 1);
    let hg = h2_num_gens(nk, n);                            // nk + 2n + 2
    assert(a_words(mm, n)[i] == phi_assoc(nk, n, 1, 1)[i].0);
    let g: nat =
        if i == 0 { 0 } else if i == 1 { 1 } else if i == 2 { d_idx(nk, n) }
        else if i < n + 3 { b_idx(nk, n, (i - 2) as nat) } else { p_idx(nk, n) };
    if i >= 3 && i < n + 3 {
        assert((i - 2) as nat == ((i - 3) + 1) as nat);
        assert(b_idx(nk, n, ((i - 3) + 1) as nat) == nk + n + (i - 3));
    }
    assert(a_words(mm, n)[i] == seq![Symbol::Gen(g)]);
    assert(g < hg);
    assert forall|t: int| 0 <= t < 1 implies symbol_valid(#[trigger] seq![Symbol::Gen(g)][t], hg) by {}
}

/// `a_words` sends every `P_A` relator (the `p`-conjugations) to `ε` in `h2_II` — the von-Dyck
/// homomorphism condition, here reused by `lemma_emb_respects_source_equiv` in the forward peel.
proof fn lemma_a_words_relator_trivial(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, j: int)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        0 <= j < betas(alphas).len(),
    ensures
        equiv_in_presentation(h2_II(mm, n, m, alphas),
            apply_embedding(a_words(mm, n), hnn_relator(pa_data(n, m, betas(alphas)), j)),
            empty_word()),
{
    let gammas = betas(alphas);
    lemma_betas_index(alphas);
    assert(numbers_word(n, m, gammas[j])) by {
        if j == 0 { assert(gammas[0] == 0); } else { assert(gammas[j] == alphas[j - 1]); }
    }
    lemma_a_words_on_hnn_relator(mm, n, m, gammas, j);     // ae =~= family_II_relator(gammas[j])
    if j == 0 {
        assert(gammas[0] == 0);
        lemma_family_II_relator_head_in_h2_II(mm, n, m, alphas);
    } else {
        assert(gammas[j] == alphas[j - 1]);
        lemma_family_II_relator_in_h2_II(mm, n, m, alphas, j - 1);
    }
}

/// **`map_a` FORWARD (faithful)**: `apply_embedding(a_words, w) ≡_{h2_II} ε ⟹ w ≡_{P_A} ε` — the
/// Britton-peel injectivity (`decreases stable_count`).  Base case (`stable_count == 0`, w an
/// F-word): descend `h2_II → h1_base` (B4) → `free(n+3)` (`a_words_F` free) → `P_A` (base embeds).
/// Step case: `britton_lemma_full` over `recog_data` (A1) gives a pinch of `pw`; descend it to a
/// pinch of `w` (`lemma_map_a_pinch_descends`); pinch out (`lemma_pd_pinch_out`, strictly fewer
/// stable letters); `a_words` respects `P_A`'s relators so `pw ≡ emb(a_words, wshort)`; recurse.
pub proof fn lemma_map_a_forward(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(w, (n + 4) as nat),
        equiv_in_presentation(h2_II(mm, n, m, alphas), apply_embedding(a_words(mm, n), w),
            empty_word()),
    ensures
        equiv_in_presentation(hnn_presentation(pa_data(n, m, betas(alphas))), w, empty_word()),
    decreases stable_count(pa_data(n, m, betas(alphas)), w),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bet = betas(alphas);
    let rd = recog_data(mm, n, m, alphas);
    let pd = pa_data(n, m, bet);
    let src = hnn_presentation(pd);
    let aw = a_words(mm, n);
    let pw = apply_embedding(aw, w);
    let h2ii = h2_II(mm, n, m, alphas);
    let awf = a_words_F(mm, n);

    lemma_betas_index(alphas);
    assert forall|i: int| 0 <= i < bet.len() implies numbers_word(n, m, #[trigger] bet[i]) by {
        if i == 0 { assert(bet[0] == 0); } else { assert(bet[i] == alphas[i - 1]); }
    }
    lemma_pa_data_shape(n, m, bet);
    assert(pd.base.num_generators == n + 3);
    assert(pd.base == free_group((n + 3) as nat));
    lemma_pa_data_valid(n, m, bet);
    lemma_hnn_presentation_valid(pd);
    assert(src.num_generators == n + 4);

    if stable_count(pd, w) == 0 {
        // --- base case: w is an F-word over n+3 ---
        lemma_stable_count_zero_no_stable(pd, w);
        assert(word_valid(w, (n + 3) as nat)) by {
            assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], (n + 3) as nat)
            by {
                assert(!is_stable(pd, w[k]));
                assert(symbol_valid(w[k], (n + 4) as nat));
                assert(generator_index(w[k]) != n + 3) by {
                    if generator_index(w[k]) == n + 3 {
                        match w[k] {
                            Symbol::Gen(gg) => { assert(w[k] == Symbol::Gen((n + 3) as nat)); },
                            Symbol::Inv(gg) => { assert(w[k] == Symbol::Inv((n + 3) as nat)); },
                        }
                    }
                }
            }
        }
        // emb(aw, w) = emb(awf, w), valid over h1_base's gens.
        lemma_a_words_eq_a_words_F(mm, n, w);
        assert(pw == apply_embedding(awf, w));
        lemma_h1_base_valid(mm, n);
        lemma_h1_base_num_generators(mm, n);
        let h1ng = h1_base(mm, n).num_generators;
        lemma_map_a_faithful(mm, n);                       // is_free_family(h1_base, awf)
        assert(awf.len() == n + 3);
        assert(word_valid(w, awf.len()));
        lemma_apply_embedding_valid(awf, w, h1ng);
        // B4: emb(awf, w) ≡_{h1_base} ε.
        lemma_h1_faithful_in_h2_II(mm, n, m, alphas, apply_embedding(awf, w));
        assert(equiv_in_presentation(h1_base(mm, n), apply_embedding(awf, w), empty_word()));
        // freeness ⟹ w ≡_{free(n+3)} ε.
        assert(equiv_in_presentation(free_group((n + 3) as nat), w, empty_word()));
        // base embeds ⟹ w ≡_{P_A} ε.
        lemma_base_embeds_in_hnn(pd, w, empty_word());
    } else {
        // --- step case: pw has a pinch over recog_data ---
        lemma_recog_data_valid(mm, n, m, alphas);
        lemma_recog_associations_isomorphic(mm, n, m, alphas);    // A1
        lemma_recog_presentation(mm, n, m, alphas);               // h2ii == hnn_presentation(rd)
        assert(hnn_presentation(rd) == h2ii);
        lemma_a_words_single_gen(mm, n);
        assert(word_valid(pw, hnn_presentation(rd).num_generators)) by {
            lemma_h1_base_num_generators(mm, n);
            assert(rd.base == h1_base(mm, n));
            assert(hnn_presentation(rd).num_generators == h2_num_gens(nk, n));
            assert(aw.len() == n + 4);
            assert forall|i: int| 0 <= i < aw.len()
                implies word_valid(#[trigger] aw[i], h2_num_gens(nk, n)) by {
                lemma_a_words_img_valid(mm, n, i);
            }
            lemma_apply_embedding_valid(aw, w, h2_num_gens(nk, n));
        }
        // has_stable_letter(rd, pw): w has a pd-stable letter, which relabels to a recog-stable one.
        lemma_single_gen_relabel(aw, w);
        lemma_stable_count_pos_has_stable(pd, w);
        let ks = choose|ks: int| 0 <= ks < w.len() && is_stable(pd, w[ks]);
        assert(0 <= ks < w.len() && is_stable(pd, w[ks]));
        assert(pw[ks] == relabel_symbol(aw, w[ks]));
        lemma_a_words_relabel_sym(mm, n, w[ks]);
        assert(is_stable(rd, pw[ks])) by {
            assert(rd.base.num_generators == p_idx(nk, n));
            lemma_h1_base_num_generators(mm, n);
        }
        assert(has_stable_letter(rd, pw)) by { assert(is_stable(rd, pw[ks])); }

        britton_lemma_full(rd, pw);                              // has_pinch(rd, pw)
        lemma_map_a_pinch_descends(mm, n, m, alphas, w);        // has_pinch(pd, w)
        let ij = choose|i: int, j: int| has_pinch_at(pd, w, i, j);
        assert(has_pinch_at(pd, w, ij.0, ij.1));

        // pinch out: w ≡_{P_A} wshort, strictly fewer stable letters.
        let wshort = lemma_pd_pinch_out(pd, w, ij.0, ij.1);
        assert(equiv_in_presentation(src, w, wshort));
        assert(word_valid(wshort, src.num_generators));
        assert(stable_count(pd, wshort) < stable_count(pd, w));

        // a_words respects P_A's relators ⟹ emb(aw, w) ≡_{h2_II} emb(aw, wshort).
        assert(src.relators =~= hnn_relators(pd)) by {
            assert(pd.base.relators == Seq::<Word>::empty());
        }
        lemma_recog_presentation(mm, n, m, alphas);
        assert(presentation_valid(h2ii)) by { lemma_hnn_presentation_valid(rd); }
        assert forall|i: int| 0 <= i < aw.len() implies
            word_valid(#[trigger] aw[i], h2ii.num_generators) by {
            // a_words images valid over h2_II gens.
            lemma_a_words_img_valid(mm, n, i);
        }
        assert forall|jj: int| 0 <= jj < src.relators.len() implies
            equiv_in_presentation(h2ii, apply_embedding(aw, src.relators[jj]), empty_word()) by {
            assert(src.relators[jj] == hnn_relators(pd)[jj]);
            assert(hnn_relators(pd)[jj] == hnn_relator(pd, jj));
            lemma_a_words_relator_trivial(mm, n, m, alphas, jj);
        }
        lemma_emb_respects_source_equiv(src, h2ii, aw, w, wshort);
        // pw ≡ emb(aw, wshort) ≡... combine with pw ≡ ε.
        lemma_equiv_symmetric(h2ii, pw, apply_embedding(aw, wshort));
        lemma_equiv_transitive(h2ii, apply_embedding(aw, wshort), pw, empty_word());

        // recurse.
        lemma_map_a_forward(mm, n, m, alphas, wshort);
        // w ≡_{src} wshort ≡_{src} ε.
        lemma_equiv_transitive(src, w, wshort, empty_word());
    }
}

} // verus!
