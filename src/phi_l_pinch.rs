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
use crate::layout::{d_idx, b_base, p_idx};
use crate::benign::{apply_embedding, in_generated_subgroup};
use crate::britton_via_tower::{has_pinch, has_pinch_at, has_adjacent_opposite_at, is_stable};
use crate::phi_l_forward::{relabel_symbol, lemma_a_words_single_gen, lemma_single_gen_relabel,
    lemma_single_gen_relabel_subrange, lemma_a_words_relabel_sym};
use crate::h1::lemma_h1_base_num_generators;
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
use crate::hnn::hnn_data_valid;
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

} // verus!
