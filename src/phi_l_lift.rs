// Layer 2 — Brick 5, C3.2c / the C-arc: the von-Dyck-backward halves (+ later the forward
// unified HNN lifting lemma).
//
// The crux `lemma_phi_l_iso_at_h2II` routes both directions through `w ≡_{P_A} ε` via two faithful
// embeddings `P_A ↪ h2_II` (`map_a` = inclusion, `map_b` = φ_l).  Each faithfulness is a
// biconditional `emb(map,w) ≡_{h2_II} ε ⟺ w ≡_{P_A} ε`.  THIS module builds the EASY `⟸` (von
// Dyck) half — generic over `map` — via `lemma_emb_respects_source_equiv`: since `P_A`'s base is
// FREE, its relators ARE the `p`-conjugation `hnn_relator`s, so a map preserves `≡_{P_A}` exactly
// when it sends each `hnn_relator(P_A,j)` to `ε` in `h2_II`.  The map-specific column translations
// (`phi_l_maps` for `map_a`) discharge that hypothesis.  See `docs/brick5-c3.2c-plan.md` §5.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::equiv_in_presentation;
use crate::presentation_lemmas::lemma_relator_is_identity;
use crate::hnn::{hnn_relator, hnn_relators, hnn_presentation, stable_letter, stable_letter_inv};
use crate::machine_group::{ModMachine, g_m, config_word, lemma_g_m_num_generators,
    lemma_config_word_zero, lemma_emb_respects_source_equiv};
use crate::layout::{p_idx, d_idx, b_base, b_idx, h2_num_gens, h1_num_gens};
use crate::benign::{apply_embedding, lemma_apply_embedding_concat, lemma_apply_embedding_inverse};
use crate::word_numbering::{w_b, w_c, numbers_word};
use crate::h1::{h1_base, lemma_h1_base_num_generators};
use crate::h2::{h2_pres, h2_data, td_word, lemma_h2_num_generators};
use crate::h3_ii::{family_II_lhs, family_II_rhs, family_II_relator, family_II, h2_II, h3_II_upto,
    lemma_h3_II_upto_valid};
use crate::base_swap::lemma_add_relators_relators;
use crate::amalgamated_free_product::lemma_add_relators_num_generators;
use crate::britton_infra::lemma_hnn_presentation_valid;
use crate::pa_data::{pa_data, pa_rhs, lemma_pa_data_shape, lemma_pa_data_valid};
use crate::phi_l_maps::{a_words, a_words_F, lemma_a_words_fixes_config, lemma_a_words_on_pa_rhs};
use crate::phi_l_iso::lemma_family_II_relator_in_h2_II;
use crate::f_free_a1::{betas, lemma_betas_index};

verus! {

// ----------------------------------------------------------------------------
// Goal (ii): the `γ=0` head case — `family_II_relator(0) ≡_{h2_II} ε`.
// ----------------------------------------------------------------------------

/// **The `γ=0` head case**: `family_II_relator(0) ≡_{h2_II} ε`.  `family_II_relator(0) =~=
/// hnn_relator(h2_data, 0)` — the `h2_pres` p-relator `p⁻¹ t p (td)⁻¹` (`config(0,0) = t`,
/// `w_0(b) = ε` ⟹ rhs `= td`), which sits in `h2_pres`'s relator block (a prefix of `h2_II`'s
/// relators), so it is a literal relator of `h2_II`.  This is the `β=0` case the `pa_data` head
/// (`p_assoc` `p⁻¹ t p = td`) needs for the von-Dyck-backward relator-preservation over `betas`.
pub proof fn lemma_family_II_relator_head_in_h2_II(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    ensures
        equiv_in_presentation(h2_II(mm, n, m, alphas), family_II_relator(mm, n, m, 0), empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    lemma_h1_base_num_generators(mm, n);                 // h1_base.num == nk+2n+1 = p_idx
    let h2ii = h2_II(mm, n, m, alphas);
    let h2p = h2_pres(mm, n);
    let h2d = h2_data(mm, n);
    let fam = family_II(mm, n, m, alphas);
    let p = p_idx(nk, n);
    let bb = b_base(nk, n);
    let d = d_idx(nk, n);

    // --- hnn_relator(h2_data, 0) structure ---
    assert(h2d.base.num_generators == h1_num_gens(nk, n));
    assert(h1_num_gens(nk, n) == p);
    assert(stable_letter(h2d) == Symbol::Gen(p));
    assert(stable_letter_inv(h2d) == Symbol::Inv(p));
    assert(h2d.associations[0] == (seq![Symbol::Gen(0)], td_word(nk, n)));
    let hr0 = hnn_relator(h2d, 0);
    assert(Seq::new(1, |_q: int| stable_letter_inv(h2d)) =~= seq![Symbol::Inv(p)]);
    assert(Seq::new(1, |_q: int| stable_letter(h2d)) =~= seq![Symbol::Gen(p)]);
    assert(hr0 =~= ((seq![Symbol::Inv(p)] + seq![Symbol::Gen(0)]) + seq![Symbol::Gen(p)])
        + inverse_word(td_word(nk, n)));

    // --- family_II_relator(0) =~= hr0 ---
    lemma_config_word_zero();                            // config(0,0) =~= [Gen0]
    assert(config_word(0, 0) =~= seq![Symbol::Gen(0)]);
    assert(w_c(bb, n, m, 0) =~= empty_word());           // w_c base case alpha==0
    assert(w_b(bb, n, m, 0) =~= empty_word());           // w_b := w_c
    // family_II_lhs(0) = [Inv(p)] + config(0,0) + [Gen(p)] =~= [Inv(p)]+[Gen0]+[Gen(p)].
    assert(family_II_lhs(mm, n, 0)
        =~= (seq![Symbol::Inv(p)] + seq![Symbol::Gen(0)]) + seq![Symbol::Gen(p)]);
    // family_II_rhs(0) = config(0,0) + w_b(bb,0) + [Gen(d)] =~= [Gen0]+[Gen(d)] = td.
    assert(family_II_rhs(mm, n, m, 0) =~= (seq![Symbol::Gen(0)] + empty_word()) + seq![Symbol::Gen(d)]);
    assert(td_word(nk, n) == seq![Symbol::Gen(0), Symbol::Gen(d)]);
    assert(family_II_rhs(mm, n, m, 0) =~= td_word(nk, n));
    assert(inverse_word(family_II_rhs(mm, n, m, 0)) =~= inverse_word(td_word(nk, n)));
    assert(family_II_relator(mm, n, m, 0)
        == family_II_lhs(mm, n, 0) + inverse_word(family_II_rhs(mm, n, m, 0)));
    assert(family_II_relator(mm, n, m, 0) =~= hr0);

    // --- hr0 is a literal relator of h2_II ---
    let base_len = h1_base(mm, n).relators.len() as int;
    // h2_pres.relators = h1_base.relators + hnn_relators(h2_data); index base_len = the p-relator.
    assert(h2p.relators == h1_base(mm, n).relators + hnn_relators(h2d));
    assert(hnn_relators(h2d).len() == 1);
    assert(h2p.relators.len() == base_len + 1);
    assert(h2p.relators[base_len] == hnn_relators(h2d)[0]);
    assert(hnn_relators(h2d)[0] == hnn_relator(h2d, 0));
    assert(h2p.relators[base_len] == hr0);
    // h2_II.relators = h2_pres.relators + fam.
    lemma_add_relators_relators(h2p, fam);
    assert(h2ii.relators == h2p.relators + fam);
    assert(0 <= base_len < h2ii.relators.len());
    assert(h2ii.relators[base_len] == h2p.relators[base_len]);
    assert(h2ii.relators[base_len] == family_II_relator(mm, n, m, 0));
    lemma_relator_is_identity(h2ii, base_len);
}

// ----------------------------------------------------------------------------
// Goal (i): `a_words` carries `P_A`'s j-th p-conjugation relator onto `h2_II`'s family-(II) one.
// ----------------------------------------------------------------------------

/// **Goal (i)**: `apply_embedding(a_words, hnn_relator(pa_data(n,m,gammas), j)) =~=
/// family_II_relator(γ_j)`.  `hnn_relator = p⁻¹ · config(γ,0) · p · pa_rhs(γ)⁻¹`; `a_words` fixes
/// the config (a-column), relabels `pa_rhs` onto `family_II_rhs` (b-column), and maps the stable
/// letter `p ↦ Gen(p_idx)`.  So `P_A`'s j-th relator maps to `h2_II`'s `family_II_relator(γ_j)`.
pub proof fn lemma_a_words_on_hnn_relator(mm: ModMachine, n: nat, m: nat, gammas: Seq<nat>, j: int)
    requires
        2 * n < m,
        0 <= j < gammas.len(),
        numbers_word(n, m, gammas[j]),
    ensures
        apply_embedding(a_words(mm, n), hnn_relator(pa_data(n, m, gammas), j))
            =~= family_II_relator(mm, n, m, gammas[j]),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let aw = a_words(mm, n);
    let data = pa_data(n, m, gammas);
    let gamma = gammas[j];
    let cfg = config_word(gamma, 0);
    let rhs = pa_rhs(n, m, gamma);
    let p = p_idx(nk, n);
    let st = (n + 3) as nat;                             // P_A stable-letter index

    lemma_pa_data_shape(n, m, gammas);                  // data.base.num_generators == n+3
    assert(stable_letter(data) == Symbol::Gen(st));
    assert(stable_letter_inv(data) == Symbol::Inv(st));
    assert(data.associations[j] == (config_word(gamma, 0), pa_rhs(n, m, gamma)));

    // aw[st] = [Gen(p)] (the push, since a_words_F has length n+3).
    let head: Seq<Word> = seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(d_idx(nk, n))]];
    let tail: Seq<Word> = Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))]);
    assert(a_words_F(mm, n) == head + tail);
    assert(a_words_F(mm, n).len() == n + 3);
    assert(aw == a_words_F(mm, n).push(seq![Symbol::Gen(p)]));
    assert(aw[st as int] == seq![Symbol::Gen(p)]);

    // hnn_relator(data, j) = ((A + cfg) + C) + inverse(rhs), A=[Inv(st)], C=[Gen(st)].
    let av: Word = Seq::new(1, |_q: int| stable_letter_inv(data));
    let cv: Word = Seq::new(1, |_q: int| stable_letter(data));
    assert(av =~= seq![Symbol::Inv(st)]);
    assert(cv =~= seq![Symbol::Gen(st)]);
    let hr = hnn_relator(data, j);
    assert(hr == ((av + cfg) + cv) + inverse_word(rhs));

    // distribute apply_embedding over the three outer concats.
    lemma_apply_embedding_concat(aw, (av + cfg) + cv, inverse_word(rhs));
    lemma_apply_embedding_concat(aw, av + cfg, cv);
    lemma_apply_embedding_concat(aw, av, cfg);

    // ae(av) = inverse_word(aw[st]) = [Inv(p)].
    reveal_with_fuel(apply_embedding, 2);
    lemma_concat_empty_right(inverse_word(aw[st as int]));
    assert(apply_embedding(aw, av) =~= inverse_word(aw[st as int]));
    reveal_with_fuel(inverse_word, 2);
    assert(inverse_word(aw[st as int]) =~= seq![Symbol::Inv(p)]);
    // ae(cfg) =~= cfg.
    lemma_a_words_fixes_config(mm, n, gamma);
    // ae(cv) = aw[st] = [Gen(p)].
    lemma_concat_empty_right(aw[st as int]);
    assert(apply_embedding(aw, cv) =~= aw[st as int]);
    // ae(inverse(rhs)) = inverse(ae(rhs)) = inverse(family_II_rhs(γ)).
    lemma_apply_embedding_inverse(aw, rhs);
    lemma_a_words_on_pa_rhs(mm, n, m, gamma);
    assert(apply_embedding(aw, inverse_word(rhs)) =~= inverse_word(family_II_rhs(mm, n, m, gamma)));

    // assemble.
    assert(apply_embedding(aw, hr)
        =~= ((seq![Symbol::Inv(p)] + cfg) + seq![Symbol::Gen(p)])
            + inverse_word(family_II_rhs(mm, n, m, gamma)));
    assert(family_II_lhs(mm, n, gamma) =~= (seq![Symbol::Inv(p)] + cfg) + seq![Symbol::Gen(p)]);
    assert(family_II_relator(mm, n, m, gamma)
        == family_II_lhs(mm, n, gamma) + inverse_word(family_II_rhs(mm, n, m, gamma)));
}

// ----------------------------------------------------------------------------
// The generic von-Dyck-backward lemma (over an abstract `map` + relator-preservation hypothesis).
// ----------------------------------------------------------------------------

/// **Generic von-Dyck backward (`⟸`)**: if `map` (the `n+4`-entry image list, valid over `h2_II`'s
/// generators) sends every `P_A` relator `hnn_relator(pa_data(gammas), j)` to `ε` in `h2_II`, then
/// `w ≡_{P_A} ε ⟹ apply_embedding(map, w) ≡_{h2_II} ε`.  Since `P_A = HNN(free, p | …)` has a FREE
/// base, `src.relators` IS the `hnn_relators` list, so the relator-preservation hypothesis is
/// exactly `lemma_emb_respects_source_equiv`'s "respects every relator" precondition.
pub proof fn lemma_pa_von_dyck_backward(
    mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, gammas: Seq<nat>, map: Seq<Word>, w: Word)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < gammas.len() ==> numbers_word(n, m, #[trigger] gammas[i]),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        map.len() == n + 4,
        forall|i: int| 0 <= i < map.len() ==>
            word_valid(#[trigger] map[i], h2_num_gens(g_m(mm).num_generators, n)),
        word_valid(w, (n + 4) as nat),
        forall|j: int| 0 <= j < gammas.len() ==>
            equiv_in_presentation(h2_II(mm, n, m, alphas),
                apply_embedding(map, hnn_relator(pa_data(n, m, gammas), j)), empty_word()),
        equiv_in_presentation(hnn_presentation(pa_data(n, m, gammas)), w, empty_word()),
    ensures
        equiv_in_presentation(h2_II(mm, n, m, alphas), apply_embedding(map, w), empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let pd = pa_data(n, m, gammas);
    let src = hnn_presentation(pd);
    let tgt = h2_II(mm, n, m, alphas);

    // --- src structure: free base ⟹ src.relators IS hnn_relators(pd) ---
    lemma_pa_data_shape(n, m, gammas);                  // base.num == n+3, assoc.len == gammas.len
    assert(src.num_generators == n + 4);
    assert(pd.base.relators == Seq::<Word>::empty());   // free_group has no relators
    assert(src.relators == pd.base.relators + hnn_relators(pd));
    assert(src.relators =~= hnn_relators(pd));
    assert(src.relators.len() == gammas.len());

    // --- src valid ---
    lemma_pa_data_valid(n, m, gammas);
    lemma_hnn_presentation_valid(pd);

    // --- tgt valid + gen-count ---
    lemma_h3_II_upto_valid(mm, n, m, alphas, 0);
    assert(h3_II_upto(mm, n, m, alphas, 0) == tgt);
    lemma_add_relators_num_generators(h2_pres(mm, n), family_II(mm, n, m, alphas));
    lemma_h2_num_generators(mm, n);
    assert(tgt.num_generators == h2_num_gens(nk, n));

    // --- map images valid over tgt.num_generators ---
    assert forall|i: int| 0 <= i < map.len() implies
        word_valid(#[trigger] map[i], tgt.num_generators) by {}

    // --- relator-preservation: forall j over src.relators (== hnn_relators(pd)) ---
    assert forall|jj: int| 0 <= jj < src.relators.len() implies
        equiv_in_presentation(tgt, apply_embedding(map, src.relators[jj]), empty_word()) by {
        assert(src.relators[jj] == hnn_relators(pd)[jj]);
        assert(hnn_relators(pd)[jj] == hnn_relator(pd, jj));
    }

    lemma_emb_respects_source_equiv(src, tgt, map, w, empty_word());
    assert(apply_embedding(map, empty_word()) =~= empty_word());
}

// ----------------------------------------------------------------------------
// map_a's instantiation: discharge the relator-preservation over `betas = [0] ++ alphas`.
// ----------------------------------------------------------------------------

/// **`map_a` von-Dyck backward (`⟸`)**: `w ≡_{P_A} ε ⟹ apply_embedding(a_words, w) ≡_{h2_II} ε`,
/// where `P_A = pa_data(betas(alphas))`.  Discharges the generic lemma's relator-preservation: for
/// each `j`, `apply_embedding(a_words, hnn_relator(P_A, j)) =~= family_II_relator(βⱼ)` (goal i),
/// and that relator is `≡_{h2_II} ε` — the `β=0` head case (`lemma_..._head_in_h2_II`) and, for
/// `j ≥ 1` (`βⱼ = alphas[j-1] ∈ alphas`), the literal-augmentation case (`lemma_..._in_h2_II`).
pub proof fn lemma_map_a_von_dyck_backward(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        forall|i: int| 0 <= i < a_words(mm, n).len() ==>
            word_valid(#[trigger] a_words(mm, n)[i], h2_num_gens(g_m(mm).num_generators, n)),
        a_words(mm, n).len() == n + 4,
        word_valid(w, (n + 4) as nat),
        equiv_in_presentation(hnn_presentation(pa_data(n, m, betas(alphas))), w, empty_word()),
    ensures
        equiv_in_presentation(h2_II(mm, n, m, alphas), apply_embedding(a_words(mm, n), w),
            empty_word()),
{
    let nk = g_m(mm).num_generators;
    let gammas = betas(alphas);
    lemma_betas_index(alphas);

    // gammas all number words (betas: 0 ++ alphas; numbers_word(n,m,0) == true).
    assert forall|i: int| 0 <= i < gammas.len() implies numbers_word(n, m, #[trigger] gammas[i]) by {
        if i == 0 {
            assert(gammas[0] == 0);
        } else {
            assert(gammas[i] == alphas[i - 1]);
        }
    }

    // discharge the relator-preservation forall.
    assert forall|j: int| 0 <= j < gammas.len() implies
        equiv_in_presentation(h2_II(mm, n, m, alphas),
            apply_embedding(a_words(mm, n), hnn_relator(pa_data(n, m, gammas), j)),
            empty_word()) by {
        assert(numbers_word(n, m, gammas[j])) by {
            if j == 0 { assert(gammas[0] == 0); } else { assert(gammas[j] == alphas[j - 1]); }
        }
        lemma_a_words_on_hnn_relator(mm, n, m, gammas, j);   // ae = family_II_relator(γ_j)
        if j == 0 {
            assert(gammas[0] == 0);
            lemma_family_II_relator_head_in_h2_II(mm, n, m, alphas);
        } else {
            assert(gammas[j] == alphas[j - 1]);
            lemma_family_II_relator_in_h2_II(mm, n, m, alphas, j - 1);
        }
    }

    lemma_pa_von_dyck_backward(mm, n, m, alphas, gammas, a_words(mm, n), w);
}

} // verus!
