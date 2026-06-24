// Layer 2 — Brick 5, C3.2c / map_b forward — M2: `φ_l_src` injective on `P_A` (the Britton peel),
// then the map_b forward assembly.
//
// `map_b forward` = M1 (factoring, DONE) + map_a forward (DONE) + **M2** (`φ_l_src` injective on
// `P_A`).  M2 is a Britton peel over `pa_data` (decreasing `stable_count`), mirroring
// `lemma_map_a_forward`; the one new piece vs map_a is the SPANNING pinch-descent — `φ_l_src` is a
// scaling map (`x↦xᵐ`), not a relabeling, so the pinch middle is `emb(φ_F, mid)` and descends to
// `mid` via the (R) reflections (a-column `lemma_config_reflect_full`, b-column
// `lemma_pa_rhs_reflect_full`).  Since `φ_l_src = stable_emb(free(n+3), φ_F_family)`, the position
// correspondence reuses `f_free`'s `lemma_extend_spanning`.  See docs/brick5-c3.2c-plan.md §6.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{ModMachine, mod_machine_wf, config_word, lemma_strip_prefix_preserves_pinch,
    lemma_prepend_preserves_pinch, lemma_word_valid_mono, lemma_g_m_num_generators, g_m};
use crate::benign::{apply_embedding, apply_embedding_symbol, in_generated_subgroup,
    lemma_apply_embedding_concat, lemma_apply_embedding_inverse, lemma_apply_embedding_valid};
use crate::britton_via_tower::{has_pinch, has_pinch_at, has_adjacent_opposite_at, is_stable,
    has_stable_letter, stable_count, britton_lemma_full};
use crate::hnn::{HNNData, hnn_relator, hnn_relators, hnn_presentation, stable_letter, stable_letter_inv,
    hnn_associations_isomorphic, hnn_data_valid, lemma_base_embeds_in_hnn};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::f_free::{stable_emb, free_stable_data, is_free_family, lemma_extend_spanning,
    lemma_apply_embedding_agree_prefix, lemma_word_valid_no_inner_stable, lemma_extend_stable_count_eq};
use crate::machine_group::lemma_single_hnn_base_faithful;
use crate::pa_data::{pa_data, pa_rhs, pa_assoc, pa_b_base, lemma_pa_data_shape, lemma_pa_data_valid};
use crate::phi_l_mapb::{phi_l_src, phi_F_family, sigma_betas, lemma_phi_F_family_free,
    lemma_phi_l_src_len, lemma_phi_l_src_valid, lemma_phi_F_on_config, lemma_mapb_factor_source,
    lemma_pa_data_isomorphic};
use crate::phi_l_pinch::{lemma_map_a_forward, lemma_map_a_pinch_descends, lemma_a_words_eq_a_words_F,
    lemma_a_words_img_valid};
use crate::phi_l_lift::{b_words, lemma_map_a_von_dyck_backward, lemma_map_b_von_dyck_backward,
    lemma_b_words_relator_trivial};
use crate::phi_l_maps::{a_words, a_words_F, lemma_a_words_is_phi_col0, lemma_map_a_faithful};
use crate::h3_ii::{h2_II, lemma_phi_assoc_len, compose_embeddings, recog_data, lemma_recog_data_valid,
    lemma_recog_presentation};
use crate::h3::{phi_assoc, lemma_phi_assoc_valid};
use crate::layout::{h2_num_gens, p_idx};
use crate::f_free_a1::{betas, lemma_betas_index, lemma_h1_faithful_in_h2_II,
    lemma_recog_associations_isomorphic};
use crate::h1::{h1_base, lemma_h1_base_num_generators};
use crate::phi_l_forward::{relabel_symbol, lemma_a_words_single_gen, lemma_single_gen_relabel,
    lemma_a_words_relabel_sym};
use crate::r_prime::{sigma_backsat, lemma_config_reflect_full, lemma_config_word_valid2};
use crate::r_prime_b::{pa_rhs_emb, sigma_fwdsat, lemma_pa_rhs_reflect_full, lemma_phi_F_on_pa_rhs,
    lemma_compose_phi_F_pa_rhs_emb, lemma_pa_rhs_valid_n3};
use crate::phi_l_mapb::lemma_compose_phi_F_config_emb;
use crate::phi_l_forward::lemma_intersection_property;
use crate::free_basis::config_emb;
use crate::word_numbering::{numbers_word, lemma_div_mod_step};
use crate::presentation::{equiv_in_presentation, presentation_valid, lemma_equiv_transitive,
    lemma_equiv_symmetric};
use crate::presentation_lemmas::lemma_relator_is_identity;
use crate::britton_infra::lemma_hnn_presentation_valid;
use crate::machine_group::{lemma_emb_respects_source_equiv, lemma_stable_count_pos_has_stable,
    lemma_stable_count_zero_no_stable};
use crate::phi_l_pinch::lemma_pd_pinch_out;
use crate::cohen_cs4d::{bet_of, lemma_bet_of_number_words, lemma_bet_of_no_dup};
use crate::cohen_cs4d_recog::lemma_phi_image_config_support;
use crate::r_prime_b::lemma_phi_image_pa_rhs_support;

verus! {

// ----------------------------------------------------------------------------
// φ_l_src = stable_emb(free(n+3), φ_F_family) — the bridge to the f_free spanning machinery.
// ----------------------------------------------------------------------------

/// **`φ_l_src = stable_emb(free(n+3), φ_F_family)`.**  `φ_l_src` is `φ_F_family` (the `n+3` F-images)
/// with the stable letter `p ↦ [Gen(n+3)]` appended — exactly `stable_emb`'s shape (the family plus
/// the new generator).  Lets the M2 pinch-descent reuse `f_free`'s `lemma_extend_spanning`.
pub proof fn lemma_phi_l_src_eq_stable_emb(n: nat, m: nat, l: nat)
    requires
        1 <= l <= 2 * n,
    ensures
        phi_l_src(n, m, l) =~= stable_emb(free_group((n + 3) as nat), phi_F_family(n, m, l)),
{
    let src = phi_l_src(n, m, l);
    let pf = phi_F_family(n, m, l);
    let se = stable_emb(free_group((n + 3) as nat), pf);
    assert(se == pf.push(seq![Symbol::Gen((n + 3) as nat)]));
    assert(src.len() == n + 4 && se.len() == n + 4 && pf.len() == n + 3);
    let tail = Seq::new(n, |j: int| seq![Symbol::Gen((3 + j) as nat)]);
    assert forall|i: int| 0 <= i < n + 4 implies src[i] =~= se[i] by {
        if i < n + 3 {
            assert(se[i] == pf[i]);
            if i == 0 || i == 1 || i == 2 {
            } else {
                // i ∈ [3, n+3): src[i] = [Gen(i)]; pf[i] = tail[i-3] = [Gen(3+(i-3))] = [Gen(i)].
                assert(pf[i] == tail[i - 3]) by { assert(i >= 3); }
                assert(tail[i - 3] == seq![Symbol::Gen((3 + (i - 3)) as nat)]);
                assert(src[i] == seq![Symbol::Gen(i as nat)]);
            }
        } else {
            assert(i == n + 3);
            assert(se[i] == seq![Symbol::Gen((n + 3) as nat)]);
            assert(src[i] == seq![Symbol::Gen((n + 3) as nat)]);
        }
    }
}

// ----------------------------------------------------------------------------
// The spanning pinch-descent — a pinch in `emb(φ_l_src, w)` descends to a pinch in `w` over `pa_data`.
// ----------------------------------------------------------------------------

/// **M2 pinch-descent**: a pinch of `emb(φ_l_src, w)` over `pa_data` descends to a pinch of `w`.
/// Head-peel induction (port of `lemma_extend_pinch_descends`): strip a non-stable run / single stable
/// prefix and recurse, OR (spanning, the head IS the left endpoint) reconstruct the pinch — the middle
/// `emb(φ_F, mid)` lies in the association column, so (R) (`lemma_config_reflect_full` a-side /
/// `lemma_pa_rhs_reflect_full` b-side) descends it to `mid` in the matching `pa_data` column.
pub proof fn lemma_mapb_pinch_descends(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        sigma_backsat(bet, m, l),
        word_valid(w, (n + 4) as nat),
        has_pinch(pa_data(n, m, bet), apply_embedding(phi_l_src(n, m, l), w)),
    ensures
        has_pinch(pa_data(n, m, bet), w),
    decreases w.len(),
{
    let pd = pa_data(n, m, bet);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let se = stable_emb(fg, pf);
    let st = (n + 3) as nat;
    lemma_phi_l_src_eq_stable_emb(n, m, l);
    assert(phi_l_src(n, m, l) == se);
    let pw = apply_embedding(se, w);

    lemma_free_group_valid((n + 3) as nat);
    lemma_pa_data_shape(n, m, bet);                    // pd.base.num == n+3
    assert(pd.base.num_generators == st);
    lemma_phi_F_family_free(n, m, l);                  // is_free_family(fg, pf) ⟹ images valid over n+3
    assert(pf.len() == n + 3);
    assert(se == pf.push(seq![Symbol::Gen(st)]));

    let ij: (int, int) = choose|i: int, j: int| has_pinch_at(pd, pw, i, j);
    let bi = ij.0;
    let bj = ij.1;
    assert(has_pinch_at(pd, pw, bi, bj));
    assert(has_adjacent_opposite_at(pd, pw, bi, bj));

    assert(w.len() > 0) by { if w.len() == 0 { assert(pw =~= Seq::<Symbol>::empty()); } }
    let c = w[0];
    let w2 = w.drop_first();
    assert(w =~= seq![c] + w2);
    assert(word_valid(w2, (n + 4) as nat)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], (n + 4) as nat)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(se, seq![c], w2);
    let ec = apply_embedding(se, seq![c]);
    let pw2 = apply_embedding(se, w2);
    assert(ec =~= apply_embedding_symbol(se, c)) by { reveal_with_fuel(apply_embedding, 2); }
    assert(pw =~= ec + pw2);
    assert(symbol_valid(c, (n + 4) as nat)) by { assert(c == w[0]); }

    if is_stable(pd, c) {
        // c is the stable letter ⟹ ec = [c], length 1.
        assert(c == Symbol::Gen(st) || c == Symbol::Inv(st));
        if c == Symbol::Gen(st) {
            assert(ec =~= seq![Symbol::Gen(st)]) by { assert(se[st as int] == seq![Symbol::Gen(st)]); }
        } else {
            assert(se[st as int] == seq![Symbol::Gen(st)]);
            assert(ec =~= inverse_word(seq![Symbol::Gen(st)]));
            assert(ec =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
        }
        assert(ec.len() == 1 && ec[0] == c);
        assert(pw[0] == ec[0] && pw[0] == c);
        if bi == 0 {
            lemma_mapb_pinch_spanning(mm, n, m, l, bet, w, w2, bi, bj);
        } else {
            // strip the single stable prefix [c], recurse on w2, re-prepend.
            assert(pw =~= ec + pw2);
            lemma_strip_prefix_preserves_pinch(pd, ec, pw2, bi, bj);
            assert(apply_embedding(phi_l_src(n, m, l), w2) == pw2);
            lemma_mapb_pinch_descends(mm, n, m, l, bet, w2);
            lemma_prepend_preserves_pinch(pd, c, w2);
            assert(seq![c] + w2 =~= w);
        }
    } else {
        // c is non-stable ⟹ ec is a stable-free run; the pinch lies past it; strip + recurse.
        assert(generator_index(c) < st) by {
            assert(symbol_valid(c, (n + 4) as nat));
            assert(generator_index(c) != st);             // not stable
        }
        // ec is stable-free (a base word over n+3).
        assert(generator_index(c) < pf.len());
        let gi = generator_index(c) as int;
        if c == Symbol::Gen(generator_index(c)) {
            assert(ec =~= se[gi]) by { reveal_with_fuel(apply_embedding, 2); lemma_concat_empty_right(se[gi]); }
            assert(se[gi] == pf[gi]);
            lemma_word_valid_no_inner_stable(fg, pf[gi]);
        } else {
            assert(c == Symbol::Inv(generator_index(c)));
            assert(ec =~= inverse_word(se[gi])) by {
                reveal_with_fuel(apply_embedding, 2); lemma_concat_empty_right(inverse_word(se[gi]));
            }
            assert(se[gi] == pf[gi]);
            crate::word::lemma_inverse_word_valid(pf[gi], (n + 3) as nat);
            lemma_word_valid_no_inner_stable(fg, inverse_word(pf[gi]));
        }
        let elen = ec.len() as int;
        assert(forall|k: int| 0 <= k < elen ==> !is_stable_at(pd, ec, k, st));
        assert(forall|k: int| 0 <= k < elen ==> #[trigger] pw[k] == ec[k]);
        assert(is_stable(pd, pw[bi]));
        assert(bi >= elen) by {
            if bi < elen {
                assert(pw[bi] == ec[bi]);
                assert(!is_stable(pd, ec[bi])) by { assert(0 <= bi < elen); }
            }
        }
        lemma_strip_prefix_preserves_pinch(pd, ec, pw2, bi, bj);
        assert(apply_embedding(phi_l_src(n, m, l), w2) == pw2);
        lemma_mapb_pinch_descends(mm, n, m, l, bet, w2);
        lemma_prepend_preserves_pinch(pd, c, w2);
        assert(seq![c] + w2 =~= w);
    }
}

/// Spelling of "`ec[k]` is not the stable letter" (used to avoid an `is_stable` trigger tangle in the
/// non-stable-head branch).
spec fn is_stable_at(pd: crate::hnn::HNNData, ec: Word, k: int, st: nat) -> bool {
    is_stable(pd, ec[k])
}

// ----------------------------------------------------------------------------
// The spanning case — the head IS the left endpoint; (R) descends the middle.
// ----------------------------------------------------------------------------

/// The `bi == 0` spanning case of `lemma_mapb_pinch_descends`, factored out for a clean context.
/// `pw[0]` is the pinch's left endpoint; `lemma_extend_spanning` locates the matching right endpoint
/// `w[l]`, the middle `emb(φ_F, mid)` is the pinch middle (in the association column), and (R)
/// reflects it to `mid` over `pa_data`, assembling `has_pinch_at(pd, w, 0, l)`.
proof fn lemma_mapb_pinch_spanning(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>,
    w: Word, w2: Word, bi: int, bj: int)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        sigma_backsat(bet, m, l),
        word_valid(w, (n + 4) as nat),
        w.len() > 0,
        w2 == w.drop_first(),
        bi == 0,
        has_pinch_at(pa_data(n, m, bet),
            apply_embedding(phi_l_src(n, m, l), w), bi, bj),
        is_stable(pa_data(n, m, bet), w[0]),
        // pw[0] is the head (the stable image of w[0]).
        apply_embedding(phi_l_src(n, m, l), w)[0] == w[0],
    ensures
        has_pinch(pa_data(n, m, bet), w),
{
    let pd = pa_data(n, m, bet);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let se = stable_emb(fg, pf);
    let st = (n + 3) as nat;
    lemma_phi_l_src_eq_stable_emb(n, m, l);
    assert(phi_l_src(n, m, l) == se);
    let pw = apply_embedding(se, w);
    lemma_free_group_valid((n + 3) as nat);
    lemma_pa_data_shape(n, m, bet);
    assert(pd.base.num_generators == st);
    lemma_phi_F_family_free(n, m, l);
    assert(pf.len() == n + 3);
    assert(se == pf.push(seq![Symbol::Gen(st)]));

    let c = w[0];
    assert(word_valid(w2, (n + 4) as nat)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], (n + 4) as nat)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(se, seq![c], w2);
    let ec = apply_embedding(se, seq![c]);
    let pw2 = apply_embedding(se, w2);
    assert(ec =~= apply_embedding_symbol(se, c)) by { reveal_with_fuel(apply_embedding, 2); }
    assert(pw =~= ec + pw2);
    // ec = [c], pw[0] = c (the head is the stable letter).
    assert(c == Symbol::Gen(st) || c == Symbol::Inv(st));
    if c == Symbol::Gen(st) {
        assert(ec =~= seq![Symbol::Gen(st)]) by { assert(se[st as int] == seq![Symbol::Gen(st)]); }
    } else {
        assert(se[st as int] == seq![Symbol::Gen(st)]);
        assert(ec =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
    }
    assert(ec.len() == 1 && ec[0] == c && pw[0] == c);

    // --- locate the right endpoint via the spanning correspondence ---
    assert(forall|t: int| 0 <= t < pw2.len() ==> #[trigger] pw[1 + t] == pw2[t]);
    assert(has_adjacent_opposite_at(pd, pw, 0, bj));
    assert(0 <= bj - 1 < pw2.len()) by { assert(0 < bj < pw.len()); }
    assert(pw2[bj - 1] == pw[bj]);
    assert(is_stable(pd, pw2[bj - 1]));
    assert forall|k: int| 0 <= k < bj - 1 implies !is_stable(pd, #[trigger] pw2[k]) by {
        assert(pw2[k] == pw[k + 1]);
    }
    // φ_F_family images valid over n+3 (from is_free_family) — the spanning lemma's precondition.
    assert forall|i: int| 0 <= i < pf.len() implies word_valid(#[trigger] pf[i], (n + 3) as nat) by {}
    let lv = lemma_extend_spanning(fg, pf, w2, bj - 1);
    let lo = lv + 1;
    assert(0 <= lv < w2.len());
    assert(is_stable(pd, w2[lv]));                          // is_stable(fsd) == is_stable(pd) (same n+3)
    assert(w[lo] == w2[lv]);
    assert(forall|k: int| 0 <= k < lv ==> !is_stable(pd, #[trigger] w2[k]));
    // s_emb-symbol of the endpoints.
    assert(apply_embedding_symbol(se, c) =~= seq![pw[0]]) by { assert(ec[0] == pw[0]); }
    assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj - 1]]);
    assert(pw2[bj - 1] == pw[bj]);
    assert(pw[0] != pw[bj]);

    // --- endpoints are opposite stable letters of w ---
    assert(0 <= lo < w.len()) by { assert(lv < w2.len()); }
    assert(w[lo] == w2[lv]);
    assert(is_stable(pd, w[lo]));
    assert(w[0] != w[lo]) by {
        if w[0] == w[lo] {
            assert(apply_embedding_symbol(se, c) =~= apply_embedding_symbol(se, w2[lv]));
            assert(seq![pw[0]] =~= seq![pw[bj]]);
            assert(pw[0] == pw[bj]);
        }
    }
    assert forall|k: int| 0 < k < lo implies !is_stable(pd, #[trigger] w[k]) by {
        assert(w[k] == w2[k - 1]);
    }

    // --- the middle, as emb(φ_F, mid) ---
    let mid = w.subrange(1, lo);
    assert(mid =~= w2.subrange(0, lv)) by {
        assert(mid.len() == lv);
        assert forall|k: int| 0 <= k < lv implies mid[k] == w2.subrange(0, lv)[k] by {
            assert(mid[k] == w[k + 1]);
            assert(w[k + 1] == w2[k]);
        }
    }
    assert(word_valid(mid, (n + 3) as nat)) by {
        assert forall|k: int| 0 <= k < mid.len() implies symbol_valid(#[trigger] mid[k], (n + 3) as nat)
        by {
            assert(mid[k] == w2[k]);
            assert(!is_stable(pd, w2[k]));
            assert(symbol_valid(w2[k], (n + 4) as nat));
            assert(generator_index(w2[k]) != st);
        }
    }
    lemma_apply_embedding_agree_prefix(se, pf, mid, (n + 3) as nat);
    assert(apply_embedding(se, mid) =~= apply_embedding(pf, mid));
    assert(apply_embedding(se, mid) =~= pw2.subrange(0, bj - 1)) by {
        // emb(se, w2.subrange(0,lv)) == pw2.subrange(0, bj-1) (spanning prefix correspondence).
        assert(mid =~= w2.subrange(0, lv));
    }
    let pinch_mid = pw.subrange(1, bj);
    assert(pinch_mid =~= pw2.subrange(0, bj - 1)) by {
        assert(pinch_mid.len() == bj - 1);
        assert forall|k: int| 0 <= k < bj - 1 implies pinch_mid[k] == pw2.subrange(0, bj - 1)[k] by {
            assert(pinch_mid[k] == pw[k + 1]);
            assert(pw[k + 1] == pw2[k]);
        }
    }
    assert(pinch_mid =~= apply_embedding(pf, mid));

    // --- the column subgroups (pd cols == config_emb / pa_rhs_emb over bet) ---
    let a_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].0);
    let b_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].1);
    assert(pd.associations =~= pa_assoc(n, m, bet));
    assert(pd.associations.len() == bet.len());
    assert(a_col =~= config_emb(bet)) by {
        assert(config_emb(bet).len() == bet.len());
        assert forall|k: int| 0 <= k < bet.len() implies a_col[k] == config_emb(bet)[k] by {
            assert(pd.associations[k] == (crate::machine_group::config_word(bet[k], 0), pa_rhs(n, m, bet[k])));
        }
    }
    assert(b_col =~= pa_rhs_emb(n, m, bet)) by {
        assert(pa_rhs_emb(n, m, bet).len() == bet.len());
        assert forall|k: int| 0 <= k < bet.len() implies b_col[k] == pa_rhs_emb(n, m, bet)[k] by {
            assert(pd.associations[k] == (crate::machine_group::config_word(bet[k], 0), pa_rhs(n, m, bet[k])));
        }
    }

    // --- (R) reflects the middle; assemble has_pinch_at(pd, w, 0, lo) ---
    assert(has_adjacent_opposite_at(pd, w, 0, lo)) by {
        assert(is_stable(pd, w[0]) && is_stable(pd, w[lo]) && w[0] != w[lo]);
    }
    if pw[0] == Symbol::Gen(st) {
        // first disjunct: pw[bj] = Inv(st), middle ∈ ⟨b_col⟩.
        assert(pw[bj] == Symbol::Inv(st)) by { assert(pw[0] != pw[bj]); assert(is_stable(pd, pw[bj])); }
        assert(w[0] == Symbol::Gen(st) && w[lo] == Symbol::Inv(st)) by {
            assert(w[0] == pw[0]);
            assert(seq![w[lo]] =~= seq![pw[bj]]) by { assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj-1]]); }
        }
        assert(in_generated_subgroup(pd.base, b_col, pinch_mid));
        assert(in_generated_subgroup(fg, pa_rhs_emb(n, m, bet), apply_embedding(pf, mid)));
        lemma_pa_rhs_reflect_full(mm, n, m, l, mid, bet);
        assert(in_generated_subgroup(fg, pa_rhs_emb(n, m, bet), mid));
        assert(in_generated_subgroup(pd.base, b_col, w.subrange(1, lo)));
        assert(has_pinch_at(pd, w, 0, lo));
    } else {
        // second disjunct: pw[0] = Inv(st), pw[bj] = Gen(st), middle ∈ ⟨a_col⟩.
        assert(pw[0] == Symbol::Inv(st));
        assert(pw[bj] == Symbol::Gen(st)) by { assert(pw[0] != pw[bj]); assert(is_stable(pd, pw[bj])); }
        assert(w[0] == Symbol::Inv(st) && w[lo] == Symbol::Gen(st)) by {
            assert(w[0] == pw[0]);
            assert(seq![w[lo]] =~= seq![pw[bj]]) by { assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj-1]]); }
        }
        assert(in_generated_subgroup(pd.base, a_col, pinch_mid));
        assert(in_generated_subgroup(fg, config_emb(bet), apply_embedding(pf, mid)));
        lemma_config_reflect_full(mm, n, m, l, mid, bet);
        assert(in_generated_subgroup(fg, config_emb(bet), mid));
        assert(in_generated_subgroup(pd.base, a_col, w.subrange(1, lo)));
        assert(has_pinch_at(pd, w, 0, lo));
    }
    assert(has_pinch(pd, w)) by { assert(has_pinch_at(pd, w, 0, lo)); }
}

// ----------------------------------------------------------------------------
// von Dyck — `φ_l_src` sends each `P_A` relator to (the σ-shifted) `P_A` relator (≡ ε).
// ----------------------------------------------------------------------------

/// **`φ_l_src` respects `P_A`'s relators**: `emb(φ_l_src, hnn_relator(pd, j)) ≡_{P_A} ε`.  The
/// `j`-th `p`-conjugation relator `p⁻¹·config(γ,0)·p·pa_rhs(γ)⁻¹` maps (digit-scaling + the F-level
/// family-(II) payoff `φ_F(pa_rhs(γ))=pa_rhs(σγ)`) to the σ(γ)-relator, which is a literal `P_A`
/// relator since `σγ ∈ bet` (forward-saturation) — hence trivial.  This is φ_l_src's homomorphism
/// condition `P_A → P_A`, consumed by the M2 Britton-peel recursion.
pub proof fn lemma_phi_l_src_on_pa_relator(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>,
    j: int)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        sigma_fwdsat(bet, m, l),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        0 <= j < bet.len(),
    ensures
        equiv_in_presentation(hnn_presentation(pa_data(n, m, bet)),
            apply_embedding(phi_l_src(n, m, l), hnn_relator(pa_data(n, m, bet), j)), empty_word()),
{
    let pd = pa_data(n, m, bet);
    let src = phi_l_src(n, m, l);
    let pf = phi_F_family(n, m, l);
    let st = (n + 3) as nat;
    let gamma = bet[j];
    let sgamma = (m * gamma + l) as nat;
    let cfg = config_word(gamma, 0);
    let rhs = pa_rhs(n, m, gamma);

    lemma_pa_data_shape(n, m, bet);
    lemma_pa_data_valid(n, m, bet);
    lemma_hnn_presentation_valid(pd);
    lemma_phi_l_src_len(n, m, l);
    assert(stable_letter(pd) == Symbol::Gen(st) && stable_letter_inv(pd) == Symbol::Inv(st));
    assert(pd.associations[j] == (cfg, rhs));
    assert(word_valid(rhs, st));                              // hnn_data_valid: column valid over n+3

    // hnn_relator(pd, j) = ((av + cfg) + cv) + inverse(rhs).
    let av: Word = Seq::new(1, |_q: int| stable_letter_inv(pd));
    let cv: Word = Seq::new(1, |_q: int| stable_letter(pd));
    assert(av =~= seq![Symbol::Inv(st)] && cv =~= seq![Symbol::Gen(st)]);
    let hr = hnn_relator(pd, j);
    assert(hr == ((av + cfg) + cv) + inverse_word(rhs));
    lemma_apply_embedding_concat(src, (av + cfg) + cv, inverse_word(rhs));
    lemma_apply_embedding_concat(src, av + cfg, cv);
    lemma_apply_embedding_concat(src, av, cfg);

    // φ_l_src fixes p: emb(src, [Inv(st)]) = [Inv(st)], emb(src, [Gen(st)]) = [Gen(st)].
    reveal_with_fuel(apply_embedding, 2);
    assert(src[st as int] == seq![Symbol::Gen(st)]);
    lemma_concat_empty_right(inverse_word(src[st as int]));
    assert(apply_embedding(src, av) =~= inverse_word(src[st as int]));
    assert(inverse_word(src[st as int]) =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
    lemma_concat_empty_right(src[st as int]);
    assert(apply_embedding(src, cv) =~= src[st as int]);

    // emb(src, cfg) = emb(pf, cfg) = config(σγ, 0).
    lemma_config_word_valid2(gamma);
    lemma_word_valid_mono(cfg, 2, st);
    assert(pf.len() == n + 3 && src.len() == n + 4);
    assert forall|i: int| 0 <= i < st implies src[i] == pf[i] by {}
    lemma_apply_embedding_agree_prefix(src, pf, cfg, st);
    lemma_phi_F_on_config(mm, n, m, l, gamma);
    assert(apply_embedding(src, cfg) =~= config_word(sgamma, 0));

    // emb(src, inverse(rhs)) = inverse(emb(pf, rhs)) = inverse(pa_rhs(σγ)).
    lemma_apply_embedding_inverse(src, rhs);
    lemma_apply_embedding_agree_prefix(src, pf, rhs, st);
    lemma_phi_F_on_pa_rhs(mm, n, m, l, gamma);
    assert(apply_embedding(src, rhs) =~= pa_rhs(n, m, sgamma));
    assert(apply_embedding(src, inverse_word(rhs)) =~= inverse_word(pa_rhs(n, m, sgamma)));

    // assemble: emb(src, hr) =~= the σγ-relator form.
    assert(apply_embedding(src, hr)
        =~= ((seq![Symbol::Inv(st)] + config_word(sgamma, 0)) + seq![Symbol::Gen(st)])
            + inverse_word(pa_rhs(n, m, sgamma)));

    // σγ ∈ bet (forward-saturation) ⟹ the σγ-relator IS hnn_relator(pd, k), a P_A relator.
    assert(bet.contains(sgamma)) by { assert(sigma_betas(bet, m, l)[j] == sgamma); }
    let k = choose|k: int| 0 <= k < bet.len() && bet[k] == sgamma;
    assert(0 <= k < bet.len() && bet[k] == sgamma);
    assert(pd.associations[k] == (config_word(sgamma, 0), pa_rhs(n, m, sgamma)));
    let avk: Word = Seq::new(1, |_q: int| stable_letter_inv(pd));
    let cvk: Word = Seq::new(1, |_q: int| stable_letter(pd));
    assert(hnn_relator(pd, k)
        == ((avk + config_word(sgamma, 0)) + cvk) + inverse_word(pa_rhs(n, m, sgamma)));
    assert(apply_embedding(src, hr) =~= hnn_relator(pd, k));

    // hnn_relator(pd, k) is relator k of hnn_presentation(pd) ⟹ ≡ ε.
    assert(hnn_presentation(pd).relators =~= hnn_relators(pd)) by {
        assert(pd.base.relators == Seq::<Word>::empty());
    }
    assert(hnn_presentation(pd).relators[k] == hnn_relators(pd)[k]);
    assert(hnn_relators(pd)[k] == hnn_relator(pd, k));
    lemma_relator_is_identity(hnn_presentation(pd), k);
}

// ----------------------------------------------------------------------------
// R1 (C4 retargeting, docs/brick5-c4-plan.md §4) — the von-Dyck WITHOUT forward-saturation.
//
// The self-endo `lemma_phi_l_src_on_pa_relator` (above) needs `σγ ∈ bet` (forward-saturation,
// unsatisfiable for finite `bet`).  The fix is to RETARGET: `φ_l_src` maps the j-th `pa_data(bet)`
// relator to the j-th `pa_data(σbet)` relator (σbet = sigma_betas(bet,m,l)), which is `≡ ε` in
// `P_A(σbet)` AUTOMATICALLY — `σbet[j] = m·bet[j]+l` is in `σbet` by construction, no saturation.
// ----------------------------------------------------------------------------

/// `σ_l(β) = m·β + l` (append base-m digit `l ∈ [1,2n]`) preserves number-word-ness.
pub proof fn lemma_sigma_numbers_word(n: nat, m: nat, l: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        1 <= l <= 2 * n,
        2 * n < m,
    ensures
        numbers_word(n, m, (m * beta + l) as nat),
{
    let sg = (m * beta + l) as nat;
    assert(m * beta == beta * m) by (nonlinear_arith);
    assert(sg == (beta * m + l) as nat);
    lemma_div_mod_step(beta, m, l);                 // (beta*m+l)/m == beta, %m == l
    assert(m > 1);
    assert(sg >= l && sg != 0);
    assert(sg % m == l && sg / m == beta);
    assert(1 <= (sg % m) <= 2 * n);
    assert(numbers_word(n, m, sg));                 // unfold one step (open spec fn)
}

/// **`sigma_betas(bet,m,l)` entries are number words** (each `σ(bet[i]) = m·bet[i]+l`).
pub proof fn lemma_sigma_betas_numbers_word(n: nat, m: nat, l: nat, bet: Seq<nat>)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
    ensures
        forall|i: int| 0 <= i < sigma_betas(bet, m, l).len()
            ==> numbers_word(n, m, #[trigger] sigma_betas(bet, m, l)[i]),
{
    let sbet = sigma_betas(bet, m, l);
    assert forall|i: int| 0 <= i < sbet.len() implies numbers_word(n, m, #[trigger] sbet[i]) by {
        assert(sbet[i] == (m * bet[i] + l) as nat);
        lemma_sigma_numbers_word(n, m, l, bet[i]);
    }
}

/// **R1 — retargeted von-Dyck (no forward-saturation)**: `φ_l_src(j-th pa_data(bet) relator) ≡ ε` in
/// `P_A(σbet)`.  Mirrors `lemma_phi_l_src_on_pa_relator`'s computation `emb(src, hr) = σγ-relator form`,
/// then identifies it as the j-th `pa_data(σbet)` relator (`σbet[j] = σγ`) — a LITERAL relator of the
/// target, ≡ ε by `lemma_relator_is_identity`.
pub proof fn lemma_phi_l_src_on_pa_relator_retarget(mm: ModMachine, n: nat, m: nat, l: nat,
    bet: Seq<nat>, j: int)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        0 <= j < bet.len(),
    ensures
        equiv_in_presentation(hnn_presentation(pa_data(n, m, sigma_betas(bet, m, l))),
            apply_embedding(phi_l_src(n, m, l), hnn_relator(pa_data(n, m, bet), j)), empty_word()),
{
    let sbet = sigma_betas(bet, m, l);
    let pd = pa_data(n, m, bet);
    let pdt = pa_data(n, m, sbet);
    let src = phi_l_src(n, m, l);
    let pf = phi_F_family(n, m, l);
    let st = (n + 3) as nat;
    let gamma = bet[j];
    let sgamma = (m * gamma + l) as nat;
    let cfg = config_word(gamma, 0);
    let rhs = pa_rhs(n, m, gamma);

    lemma_pa_data_shape(n, m, bet);
    lemma_pa_data_valid(n, m, bet);
    lemma_phi_l_src_len(n, m, l);
    assert(pd.associations[j] == (cfg, rhs));
    assert(word_valid(rhs, st));

    // ---- compute emb(src, hnn_relator(pd, j)) = the σγ-relator form (mirror of the self-endo). ----
    let av: Word = Seq::new(1, |_q: int| stable_letter_inv(pd));
    let cv: Word = Seq::new(1, |_q: int| stable_letter(pd));
    assert(av =~= seq![Symbol::Inv(st)] && cv =~= seq![Symbol::Gen(st)]);
    let hr = hnn_relator(pd, j);
    assert(hr == ((av + cfg) + cv) + inverse_word(rhs));
    lemma_apply_embedding_concat(src, (av + cfg) + cv, inverse_word(rhs));
    lemma_apply_embedding_concat(src, av + cfg, cv);
    lemma_apply_embedding_concat(src, av, cfg);
    reveal_with_fuel(apply_embedding, 2);
    assert(src[st as int] == seq![Symbol::Gen(st)]);
    lemma_concat_empty_right(inverse_word(src[st as int]));
    assert(apply_embedding(src, av) =~= inverse_word(src[st as int]));
    assert(inverse_word(src[st as int]) =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
    lemma_concat_empty_right(src[st as int]);
    assert(apply_embedding(src, cv) =~= src[st as int]);
    lemma_config_word_valid2(gamma);
    lemma_word_valid_mono(cfg, 2, st);
    assert(pf.len() == n + 3 && src.len() == n + 4);
    assert forall|i: int| 0 <= i < st implies src[i] == pf[i] by {}
    lemma_apply_embedding_agree_prefix(src, pf, cfg, st);
    lemma_phi_F_on_config(mm, n, m, l, gamma);
    assert(apply_embedding(src, cfg) =~= config_word(sgamma, 0));
    lemma_apply_embedding_inverse(src, rhs);
    lemma_apply_embedding_agree_prefix(src, pf, rhs, st);
    lemma_phi_F_on_pa_rhs(mm, n, m, l, gamma);
    assert(apply_embedding(src, rhs) =~= pa_rhs(n, m, sgamma));
    assert(apply_embedding(src, inverse_word(rhs)) =~= inverse_word(pa_rhs(n, m, sgamma)));
    assert(apply_embedding(src, hr)
        =~= ((seq![Symbol::Inv(st)] + config_word(sgamma, 0)) + seq![Symbol::Gen(st)])
            + inverse_word(pa_rhs(n, m, sgamma)));

    // ---- identify the σγ-relator as the j-th relator of the TARGET pa_data(σbet). ----
    lemma_sigma_betas_numbers_word(n, m, l, bet);
    lemma_pa_data_shape(n, m, sbet);
    lemma_pa_data_valid(n, m, sbet);
    lemma_hnn_presentation_valid(pdt);
    assert(sbet[j] == sgamma) by { assert(sbet[j] == (m * bet[j] + l) as nat); }
    assert(pdt.associations[j] == (config_word(sgamma, 0), pa_rhs(n, m, sgamma)));
    assert(stable_letter(pdt) == Symbol::Gen(st) && stable_letter_inv(pdt) == Symbol::Inv(st));
    let avk: Word = Seq::new(1, |_q: int| stable_letter_inv(pdt));
    let cvk: Word = Seq::new(1, |_q: int| stable_letter(pdt));
    assert(avk =~= seq![Symbol::Inv(st)] && cvk =~= seq![Symbol::Gen(st)]);
    assert(hnn_relator(pdt, j)
        == ((avk + config_word(sgamma, 0)) + cvk) + inverse_word(pa_rhs(n, m, sgamma)));
    assert(apply_embedding(src, hr) =~= hnn_relator(pdt, j));

    // hnn_relator(pdt, j) is relator j of hnn_presentation(pdt) ⟹ ≡ ε.
    assert(hnn_presentation(pdt).relators =~= hnn_relators(pdt)) by {
        assert(pdt.base.relators == Seq::<Word>::empty());
    }
    assert(hnn_presentation(pdt).relators[j] == hnn_relators(pdt)[j]);
    assert(hnn_relators(pdt)[j] == hnn_relator(pdt, j));
    lemma_relator_is_identity(hnn_presentation(pdt), j);
}

// ----------------------------------------------------------------------------
// R2 reflection cores — the σbet→bet reflection via the INTERSECTION PROPERTY (no saturation).
//
// In the retargeted pinch-descent the pinch is over `pa_data(σbet)`, so the spanning middle
// `emb(φ_F,mid)` is NATIVELY in `⟨col(σbet)⟩` (= `⟨compose(φ_F, col(bet))⟩`), and the intersection
// property reflects it straight to `mid ∈ ⟨col(bet)⟩`.  This REPLACES the (R)/(R)_b reflections (which
// needed σ-saturation to lift `bet → σbet`) — here the element is already at `σbet`, so only the
// saturation-free intersection property is needed.  See docs/brick5-c4-plan.md §4 R2.
// ----------------------------------------------------------------------------

/// **b-column R2 reflection**: `emb(φ_F,mid) ∈ ⟨pa_rhs_emb(σbet)⟩ ⟹ mid ∈ ⟨pa_rhs_emb(bet)⟩` (no σ-sat).
pub proof fn lemma_pa_rhs_reflect_intersection(mm: ModMachine, n: nat, m: nat, l: nat, mid: Word,
    bet: Seq<nat>)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        word_valid(mid, (n + 3) as nat),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        in_generated_subgroup(free_group((n + 3) as nat), pa_rhs_emb(n, m, sigma_betas(bet, m, l)),
            apply_embedding(phi_F_family(n, m, l), mid)),
    ensures
        in_generated_subgroup(free_group((n + 3) as nat), pa_rhs_emb(n, m, bet), mid),
{
    let fg = free_group((n + 3) as nat);
    let pf = phi_F_family(n, m, l);
    let pr = pa_rhs_emb(n, m, bet);
    lemma_free_group_valid((n + 3) as nat);
    lemma_phi_F_family_free(n, m, l);                      // is_free_family(fg, pf)
    assert(pf.len() == n + 3);
    assert(word_valid(mid, pf.len()));
    assert forall|k: int| 0 <= k < pr.len() implies word_valid(#[trigger] pr[k], pf.len()) by {
        assert(pr[k] == pa_rhs(n, m, bet[k]));
        lemma_pa_rhs_valid_n3(n, m, bet[k]);
    }
    lemma_compose_phi_F_pa_rhs_emb(mm, n, m, l, bet);     // compose(pf, pr) = pa_rhs_emb(σbet)
    assert(compose_embeddings(pf, pr) == pa_rhs_emb(n, m, sigma_betas(bet, m, l)));
    lemma_intersection_property(fg, pf, pr, mid);
}

/// **a-column R2 reflection**: `emb(φ_F,mid) ∈ ⟨config_emb(σbet)⟩ ⟹ mid ∈ ⟨config_emb(bet)⟩` (no σ-sat).
pub proof fn lemma_config_reflect_intersection(mm: ModMachine, n: nat, m: nat, l: nat, mid: Word,
    bet: Seq<nat>)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        word_valid(mid, (n + 3) as nat),
        in_generated_subgroup(free_group((n + 3) as nat), config_emb(sigma_betas(bet, m, l)),
            apply_embedding(phi_F_family(n, m, l), mid)),
    ensures
        in_generated_subgroup(free_group((n + 3) as nat), config_emb(bet), mid),
{
    let fg = free_group((n + 3) as nat);
    let pf = phi_F_family(n, m, l);
    let ce = config_emb(bet);
    lemma_free_group_valid((n + 3) as nat);
    lemma_phi_F_family_free(n, m, l);                      // is_free_family(fg, pf)
    assert(pf.len() == n + 3);
    assert(word_valid(mid, pf.len()));
    assert forall|k: int| 0 <= k < ce.len() implies word_valid(#[trigger] ce[k], pf.len()) by {
        assert(ce[k] == config_word(bet[k], 0));
        lemma_config_word_valid2(bet[k]);
        lemma_word_valid_mono(config_word(bet[k], 0), 2, (n + 3) as nat);
    }
    lemma_compose_phi_F_config_emb(mm, n, m, l, bet);     // compose(pf, ce) = config_emb(σbet)
    assert(compose_embeddings(pf, ce) == config_emb(sigma_betas(bet, m, l)));
    lemma_intersection_property(fg, pf, ce, mid);
}

/// **R2 — the retargeted cross-index pinch-descent**: a pinch of `pw = emb(φ_l_src, w)` over
/// `pa_data(σbet)` descends to a pinch of `w` over `pa_data(bet)`.  Both bases are `free(n+3)` (common),
/// so `is_stable` agrees and the generic strip/prepend helpers apply; the head-peel induction
/// (`decreases w.len()`) threads BOTH datas (pinch ops over `pdt = pa_data(σbet)`, the assembled
/// `w`-pinch over `pd = pa_data(bet)`).  The spanning case delegates to `lemma_mapb_pinch_spanning_rt`.
/// **No σ-saturation** (the reflection is the saturation-free intersection property).
pub proof fn lemma_mapb_pinch_descends_rt(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>,
    w: Word)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        word_valid(w, (n + 4) as nat),
        has_pinch(pa_data(n, m, sigma_betas(bet, m, l)), apply_embedding(phi_l_src(n, m, l), w)),
    ensures
        has_pinch(pa_data(n, m, bet), w),
    decreases w.len(),
{
    let sbet = sigma_betas(bet, m, l);
    let pd = pa_data(n, m, bet);
    let pdt = pa_data(n, m, sbet);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let se = stable_emb(fg, pf);
    let st = (n + 3) as nat;
    lemma_phi_l_src_eq_stable_emb(n, m, l);
    assert(phi_l_src(n, m, l) == se);
    let pw = apply_embedding(se, w);

    lemma_free_group_valid((n + 3) as nat);
    lemma_pa_data_shape(n, m, bet);
    lemma_sigma_betas_numbers_word(n, m, l, bet);
    lemma_pa_data_shape(n, m, sbet);
    assert(pd.base.num_generators == st && pdt.base.num_generators == st);
    lemma_phi_F_family_free(n, m, l);
    assert(pf.len() == n + 3);
    assert(se == pf.push(seq![Symbol::Gen(st)]));
    // is_stable agrees across pd / pdt (same base.num_generators).
    assert forall|x: Symbol| is_stable(pdt, x) == is_stable(pd, x) by {}

    let ij: (int, int) = choose|i: int, j: int| has_pinch_at(pdt, pw, i, j);
    let bi = ij.0;
    let bj = ij.1;
    assert(has_pinch_at(pdt, pw, bi, bj));
    assert(has_adjacent_opposite_at(pdt, pw, bi, bj));

    assert(w.len() > 0) by { if w.len() == 0 { assert(pw =~= Seq::<Symbol>::empty()); } }
    let c = w[0];
    let w2 = w.drop_first();
    assert(w =~= seq![c] + w2);
    assert(word_valid(w2, (n + 4) as nat)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], (n + 4) as nat)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(se, seq![c], w2);
    let ec = apply_embedding(se, seq![c]);
    let pw2 = apply_embedding(se, w2);
    assert(ec =~= apply_embedding_symbol(se, c)) by { reveal_with_fuel(apply_embedding, 2); }
    assert(pw =~= ec + pw2);
    assert(symbol_valid(c, (n + 4) as nat)) by { assert(c == w[0]); }

    if is_stable(pdt, c) {
        assert(c == Symbol::Gen(st) || c == Symbol::Inv(st));
        if c == Symbol::Gen(st) {
            assert(ec =~= seq![Symbol::Gen(st)]) by { assert(se[st as int] == seq![Symbol::Gen(st)]); }
        } else {
            assert(se[st as int] == seq![Symbol::Gen(st)]);
            assert(ec =~= inverse_word(seq![Symbol::Gen(st)]));
            assert(ec =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
        }
        assert(ec.len() == 1 && ec[0] == c);
        assert(pw[0] == ec[0] && pw[0] == c);
        if bi == 0 {
            lemma_mapb_pinch_spanning_rt(mm, n, m, l, bet, w, w2, bi, bj);
        } else {
            assert(pw =~= ec + pw2);
            lemma_strip_prefix_preserves_pinch(pdt, ec, pw2, bi, bj);
            assert(apply_embedding(phi_l_src(n, m, l), w2) == pw2);
            lemma_mapb_pinch_descends_rt(mm, n, m, l, bet, w2);
            lemma_prepend_preserves_pinch(pd, c, w2);
            assert(seq![c] + w2 =~= w);
        }
    } else {
        assert(generator_index(c) < st) by {
            assert(symbol_valid(c, (n + 4) as nat));
            assert(generator_index(c) != st);
        }
        assert(generator_index(c) < pf.len());
        let gi = generator_index(c) as int;
        if c == Symbol::Gen(generator_index(c)) {
            assert(ec =~= se[gi]) by { reveal_with_fuel(apply_embedding, 2); lemma_concat_empty_right(se[gi]); }
            assert(se[gi] == pf[gi]);
            lemma_word_valid_no_inner_stable(fg, pf[gi]);
        } else {
            assert(c == Symbol::Inv(generator_index(c)));
            assert(ec =~= inverse_word(se[gi])) by {
                reveal_with_fuel(apply_embedding, 2); lemma_concat_empty_right(inverse_word(se[gi]));
            }
            assert(se[gi] == pf[gi]);
            crate::word::lemma_inverse_word_valid(pf[gi], (n + 3) as nat);
            lemma_word_valid_no_inner_stable(fg, inverse_word(pf[gi]));
        }
        let elen = ec.len() as int;
        assert(forall|k: int| 0 <= k < elen ==> !is_stable_at(pdt, ec, k, st));
        assert(forall|k: int| 0 <= k < elen ==> #[trigger] pw[k] == ec[k]);
        assert(is_stable(pdt, pw[bi]));
        assert(bi >= elen) by {
            if bi < elen {
                assert(pw[bi] == ec[bi]);
                assert(!is_stable(pdt, ec[bi])) by { assert(0 <= bi < elen); }
            }
        }
        lemma_strip_prefix_preserves_pinch(pdt, ec, pw2, bi, bj);
        assert(apply_embedding(phi_l_src(n, m, l), w2) == pw2);
        lemma_mapb_pinch_descends_rt(mm, n, m, l, bet, w2);
        lemma_prepend_preserves_pinch(pd, c, w2);
        assert(seq![c] + w2 =~= w);
    }
}

// ----------------------------------------------------------------------------
// R2 spanning (retargeted) — the head IS the left endpoint; the INTERSECTION property descends the
// middle.  The pinch of `pw = emb(φ_l_src, w)` is over `pa_data(σbet)` (the retargeted image); the
// middle `emb(φ_F, mid)` sits in `⟨col(σbet)⟩`, reflected to `mid ∈ ⟨col(bet)⟩` by the R2 cores; we
// assemble `has_pinch_at(pa_data(bet), w, 0, lo)`.  Mirror of `lemma_mapb_pinch_spanning` with the
// (R)/(R)_b reflections replaced by the saturation-free intersection property.
// ----------------------------------------------------------------------------

/// The `bi == 0` spanning case of the retargeted pinch-descent (`lemma_mapb_pinch_descends_rt`).
proof fn lemma_mapb_pinch_spanning_rt(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>,
    w: Word, w2: Word, bi: int, bj: int)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        word_valid(w, (n + 4) as nat),
        w.len() > 0,
        w2 == w.drop_first(),
        bi == 0,
        has_pinch_at(pa_data(n, m, sigma_betas(bet, m, l)),
            apply_embedding(phi_l_src(n, m, l), w), bi, bj),
        is_stable(pa_data(n, m, sigma_betas(bet, m, l)),
            apply_embedding(phi_l_src(n, m, l), w)[0]),
        apply_embedding(phi_l_src(n, m, l), w)[0] == w[0],
    ensures
        has_pinch(pa_data(n, m, bet), w),
{
    let sbet = sigma_betas(bet, m, l);
    let pd = pa_data(n, m, bet);
    let pdt = pa_data(n, m, sbet);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let se = stable_emb(fg, pf);
    let st = (n + 3) as nat;
    lemma_phi_l_src_eq_stable_emb(n, m, l);
    assert(phi_l_src(n, m, l) == se);
    let pw = apply_embedding(se, w);
    lemma_free_group_valid((n + 3) as nat);
    lemma_pa_data_shape(n, m, bet);
    lemma_sigma_betas_numbers_word(n, m, l, bet);
    lemma_pa_data_shape(n, m, sbet);
    assert(pd.base.num_generators == st && pdt.base.num_generators == st);
    assert(pd.base == fg && pdt.base == fg);
    lemma_phi_F_family_free(n, m, l);
    assert(pf.len() == n + 3);
    assert(se == pf.push(seq![Symbol::Gen(st)]));
    // is_stable / has_adjacent_opposite agree across pd / pdt (same base.num_generators).
    assert forall|x: Symbol| is_stable(pdt, x) == is_stable(pd, x) by {}

    let c = w[0];
    assert(word_valid(w2, (n + 4) as nat)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], (n + 4) as nat)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(se, seq![c], w2);
    let ec = apply_embedding(se, seq![c]);
    let pw2 = apply_embedding(se, w2);
    assert(ec =~= apply_embedding_symbol(se, c)) by { reveal_with_fuel(apply_embedding, 2); }
    assert(pw =~= ec + pw2);
    assert(c == Symbol::Gen(st) || c == Symbol::Inv(st));
    if c == Symbol::Gen(st) {
        assert(ec =~= seq![Symbol::Gen(st)]) by { assert(se[st as int] == seq![Symbol::Gen(st)]); }
    } else {
        assert(se[st as int] == seq![Symbol::Gen(st)]);
        assert(ec =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
    }
    assert(ec.len() == 1 && ec[0] == c && pw[0] == c);

    // --- locate the right endpoint via the spanning correspondence (over pdt; same is_stable) ---
    assert(forall|t: int| 0 <= t < pw2.len() ==> #[trigger] pw[1 + t] == pw2[t]);
    assert(has_adjacent_opposite_at(pdt, pw, 0, bj));
    assert(0 <= bj - 1 < pw2.len()) by { assert(0 < bj < pw.len()); }
    assert(pw2[bj - 1] == pw[bj]);
    assert(is_stable(pd, pw2[bj - 1]));
    assert forall|k: int| 0 <= k < bj - 1 implies !is_stable(pd, #[trigger] pw2[k]) by {
        assert(pw2[k] == pw[k + 1]);
    }
    assert forall|i: int| 0 <= i < pf.len() implies word_valid(#[trigger] pf[i], (n + 3) as nat) by {}
    let lv = lemma_extend_spanning(fg, pf, w2, bj - 1);
    let lo = lv + 1;
    assert(0 <= lv < w2.len());
    assert(is_stable(pd, w2[lv]));
    assert(w[lo] == w2[lv]);
    assert(forall|k: int| 0 <= k < lv ==> !is_stable(pd, #[trigger] w2[k]));
    assert(apply_embedding_symbol(se, c) =~= seq![pw[0]]) by { assert(ec[0] == pw[0]); }
    assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj - 1]]);
    assert(pw2[bj - 1] == pw[bj]);
    assert(pw[0] != pw[bj]);

    assert(0 <= lo < w.len()) by { assert(lv < w2.len()); }
    assert(w[lo] == w2[lv]);
    assert(is_stable(pd, w[lo]));
    assert(w[0] != w[lo]) by {
        if w[0] == w[lo] {
            assert(apply_embedding_symbol(se, c) =~= apply_embedding_symbol(se, w2[lv]));
            assert(seq![pw[0]] =~= seq![pw[bj]]);
            assert(pw[0] == pw[bj]);
        }
    }
    assert forall|k: int| 0 < k < lo implies !is_stable(pd, #[trigger] w[k]) by {
        assert(w[k] == w2[k - 1]);
    }

    // --- the middle, as emb(φ_F, mid) ---
    let mid = w.subrange(1, lo);
    assert(mid =~= w2.subrange(0, lv)) by {
        assert(mid.len() == lv);
        assert forall|k: int| 0 <= k < lv implies mid[k] == w2.subrange(0, lv)[k] by {
            assert(mid[k] == w[k + 1]);
            assert(w[k + 1] == w2[k]);
        }
    }
    assert(word_valid(mid, (n + 3) as nat)) by {
        assert forall|k: int| 0 <= k < mid.len() implies symbol_valid(#[trigger] mid[k], (n + 3) as nat)
        by {
            assert(mid[k] == w2[k]);
            assert(!is_stable(pd, w2[k]));
            assert(symbol_valid(w2[k], (n + 4) as nat));
            assert(generator_index(w2[k]) != st);
        }
    }
    lemma_apply_embedding_agree_prefix(se, pf, mid, (n + 3) as nat);
    assert(apply_embedding(se, mid) =~= apply_embedding(pf, mid));
    assert(apply_embedding(se, mid) =~= pw2.subrange(0, bj - 1)) by {
        assert(mid =~= w2.subrange(0, lv));
    }
    let pinch_mid = pw.subrange(1, bj);
    assert(pinch_mid =~= pw2.subrange(0, bj - 1)) by {
        assert(pinch_mid.len() == bj - 1);
        assert forall|k: int| 0 <= k < bj - 1 implies pinch_mid[k] == pw2.subrange(0, bj - 1)[k] by {
            assert(pinch_mid[k] == pw[k + 1]);
            assert(pw[k + 1] == pw2[k]);
        }
    }
    assert(pinch_mid =~= apply_embedding(pf, mid));

    // --- columns: pdt columns (σbet) for the middle, pd columns (bet) for the assembly ---
    let a_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].0);
    let b_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].1);
    let a_col_t = Seq::new(pdt.associations.len(), |k: int| pdt.associations[k].0);
    let b_col_t = Seq::new(pdt.associations.len(), |k: int| pdt.associations[k].1);
    assert(pd.associations =~= pa_assoc(n, m, bet) && pd.associations.len() == bet.len());
    assert(pdt.associations =~= pa_assoc(n, m, sbet) && pdt.associations.len() == sbet.len());
    assert(a_col =~= config_emb(bet)) by {
        assert(config_emb(bet).len() == bet.len());
        assert forall|k: int| 0 <= k < bet.len() implies a_col[k] == config_emb(bet)[k] by {
            assert(pd.associations[k] == (crate::machine_group::config_word(bet[k], 0), pa_rhs(n, m, bet[k])));
        }
    }
    assert(b_col =~= pa_rhs_emb(n, m, bet)) by {
        assert(pa_rhs_emb(n, m, bet).len() == bet.len());
        assert forall|k: int| 0 <= k < bet.len() implies b_col[k] == pa_rhs_emb(n, m, bet)[k] by {
            assert(pd.associations[k] == (crate::machine_group::config_word(bet[k], 0), pa_rhs(n, m, bet[k])));
        }
    }
    assert(a_col_t =~= config_emb(sbet)) by {
        assert(config_emb(sbet).len() == sbet.len());
        assert forall|k: int| 0 <= k < sbet.len() implies a_col_t[k] == config_emb(sbet)[k] by {
            assert(pdt.associations[k] == (crate::machine_group::config_word(sbet[k], 0), pa_rhs(n, m, sbet[k])));
        }
    }
    assert(b_col_t =~= pa_rhs_emb(n, m, sbet)) by {
        assert(pa_rhs_emb(n, m, sbet).len() == sbet.len());
        assert forall|k: int| 0 <= k < sbet.len() implies b_col_t[k] == pa_rhs_emb(n, m, sbet)[k] by {
            assert(pdt.associations[k] == (crate::machine_group::config_word(sbet[k], 0), pa_rhs(n, m, sbet[k])));
        }
    }

    // --- the middle (over pdt = σbet) reflected to mid (over pd = bet), then assemble ---
    assert(has_adjacent_opposite_at(pd, w, 0, lo)) by {
        assert(is_stable(pd, w[0]) && is_stable(pd, w[lo]) && w[0] != w[lo]);
    }
    if pw[0] == Symbol::Gen(st) {
        assert(pw[bj] == Symbol::Inv(st)) by { assert(pw[0] != pw[bj]); assert(is_stable(pd, pw[bj])); }
        assert(w[0] == Symbol::Gen(st) && w[lo] == Symbol::Inv(st)) by {
            assert(w[0] == pw[0]);
            assert(seq![w[lo]] =~= seq![pw[bj]]) by { assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj-1]]); }
        }
        // middle ∈ ⟨b_col_t = pa_rhs_emb(σbet)⟩  (from has_pinch_at(pdt, pw, 0, bj)).
        assert(in_generated_subgroup(pdt.base, b_col_t, pinch_mid));
        assert(in_generated_subgroup(fg, pa_rhs_emb(n, m, sbet), apply_embedding(pf, mid)));
        lemma_pa_rhs_reflect_intersection(mm, n, m, l, mid, bet);
        assert(in_generated_subgroup(fg, pa_rhs_emb(n, m, bet), mid));
        assert(in_generated_subgroup(pd.base, b_col, w.subrange(1, lo)));
        assert(has_pinch_at(pd, w, 0, lo));
    } else {
        assert(pw[0] == Symbol::Inv(st));
        assert(pw[bj] == Symbol::Gen(st)) by { assert(pw[0] != pw[bj]); assert(is_stable(pd, pw[bj])); }
        assert(w[0] == Symbol::Inv(st) && w[lo] == Symbol::Gen(st)) by {
            assert(w[0] == pw[0]);
            assert(seq![w[lo]] =~= seq![pw[bj]]) by { assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj-1]]); }
        }
        // middle ∈ ⟨a_col_t = config_emb(σbet)⟩.
        assert(in_generated_subgroup(pdt.base, a_col_t, pinch_mid));
        assert(in_generated_subgroup(fg, config_emb(sbet), apply_embedding(pf, mid)));
        lemma_config_reflect_intersection(mm, n, m, l, mid, bet);
        assert(in_generated_subgroup(fg, config_emb(bet), mid));
        assert(in_generated_subgroup(pd.base, a_col, w.subrange(1, lo)));
        assert(has_pinch_at(pd, w, 0, lo));
    }
    assert(has_pinch(pd, w)) by { assert(has_pinch_at(pd, w, 0, lo)); }
}

// ----------------------------------------------------------------------------
// CS-4d — the SUPERSET-SLICE pinch-descent (S → bet = bet_of(S)).  Additive copy of
// `lemma_mapb_pinch_descends_rt` / `lemma_mapb_pinch_spanning_rt` whose Britton peel runs over the
// SUPERSET slice `S` (so the pinch-middle lands in `⟨·_emb(S)⟩`); the §4.2 recognition cores
// (`lemma_phi_image_config_support` / `lemma_phi_image_pa_rhs_support`) RECOGNIZE that the `φ_F`-image
// middle actually sits in `⟨·_emb(σbet)⟩` (σbet = sigma_betas(bet_of(S)) = the ≡l elements of S),
// after which the EXISTING saturation-free reflections (`lemma_config_reflect_intersection` /
// `lemma_pa_rhs_reflect_intersection`, σbet → bet) descend it to `mid ∈ ⟨·_emb(bet)⟩`.  This is the
// only place CS-4d's recognition enters; everything upstream/downstream reuses the proven `_rt`
// machinery (the strip/prepend/spanning helpers are slice-generic).  See cohen-cs4d-blueprint.md §3.
// ----------------------------------------------------------------------------

/// The `bi == 0` spanning case of the superset-slice pinch-descent (mirror of
/// `lemma_mapb_pinch_spanning_rt`, with the §4.2 recognition inserted before the reflection).
proof fn lemma_mapb_pinch_spanning_S(mm: ModMachine, n: nat, m: nat, l: nat, s_slice: Seq<nat>,
    w: Word, w2: Word, bi: int, bj: int)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        s_slice.no_duplicates(),
        forall|i: int| 0 <= i < s_slice.len() ==> numbers_word(n, m, #[trigger] s_slice[i]),
        word_valid(w, (n + 4) as nat),
        w.len() > 0,
        w2 == w.drop_first(),
        bi == 0,
        has_pinch_at(pa_data(n, m, s_slice), apply_embedding(phi_l_src(n, m, l), w), bi, bj),
        is_stable(pa_data(n, m, s_slice), apply_embedding(phi_l_src(n, m, l), w)[0]),
        apply_embedding(phi_l_src(n, m, l), w)[0] == w[0],
    ensures
        has_pinch(pa_data(n, m, bet_of(s_slice, m, l)), w),
{
    let bet = bet_of(s_slice, m, l);
    let sbet = sigma_betas(bet, m, l);
    let pd = pa_data(n, m, bet);
    let pdS = pa_data(n, m, s_slice);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let se = stable_emb(fg, pf);
    let st = (n + 3) as nat;
    lemma_phi_l_src_eq_stable_emb(n, m, l);
    assert(phi_l_src(n, m, l) == se);
    let pw = apply_embedding(se, w);
    lemma_free_group_valid((n + 3) as nat);
    lemma_bet_of_no_dup(s_slice, m, l);
    lemma_bet_of_number_words(s_slice, n, m, l);
    lemma_pa_data_shape(n, m, bet);
    lemma_pa_data_shape(n, m, s_slice);
    assert(pd.base.num_generators == st && pdS.base.num_generators == st);
    assert(pd.base == fg && pdS.base == fg);
    lemma_phi_F_family_free(n, m, l);
    assert(pf.len() == n + 3);
    assert(se == pf.push(seq![Symbol::Gen(st)]));
    assert forall|x: Symbol| is_stable(pdS, x) == is_stable(pd, x) by {}

    let c = w[0];
    assert(word_valid(w2, (n + 4) as nat)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], (n + 4) as nat)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(se, seq![c], w2);
    let ec = apply_embedding(se, seq![c]);
    let pw2 = apply_embedding(se, w2);
    assert(ec =~= apply_embedding_symbol(se, c)) by { reveal_with_fuel(apply_embedding, 2); }
    assert(pw =~= ec + pw2);
    assert(c == Symbol::Gen(st) || c == Symbol::Inv(st));
    if c == Symbol::Gen(st) {
        assert(ec =~= seq![Symbol::Gen(st)]) by { assert(se[st as int] == seq![Symbol::Gen(st)]); }
    } else {
        assert(se[st as int] == seq![Symbol::Gen(st)]);
        assert(ec =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
    }
    assert(ec.len() == 1 && ec[0] == c && pw[0] == c);

    // --- locate the right endpoint via the spanning correspondence (over pdS; same is_stable) ---
    assert(forall|t: int| 0 <= t < pw2.len() ==> #[trigger] pw[1 + t] == pw2[t]);
    assert(has_adjacent_opposite_at(pdS, pw, 0, bj));
    assert(0 <= bj - 1 < pw2.len()) by { assert(0 < bj < pw.len()); }
    assert(pw2[bj - 1] == pw[bj]);
    assert(is_stable(pd, pw2[bj - 1]));
    assert forall|k: int| 0 <= k < bj - 1 implies !is_stable(pd, #[trigger] pw2[k]) by {
        assert(pw2[k] == pw[k + 1]);
    }
    assert forall|i: int| 0 <= i < pf.len() implies word_valid(#[trigger] pf[i], (n + 3) as nat) by {}
    let lv = lemma_extend_spanning(fg, pf, w2, bj - 1);
    let lo = lv + 1;
    assert(0 <= lv < w2.len());
    assert(is_stable(pd, w2[lv]));
    assert(w[lo] == w2[lv]);
    assert(forall|k: int| 0 <= k < lv ==> !is_stable(pd, #[trigger] w2[k]));
    assert(apply_embedding_symbol(se, c) =~= seq![pw[0]]) by { assert(ec[0] == pw[0]); }
    assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj - 1]]);
    assert(pw2[bj - 1] == pw[bj]);
    assert(pw[0] != pw[bj]);

    assert(0 <= lo < w.len()) by { assert(lv < w2.len()); }
    assert(w[lo] == w2[lv]);
    assert(is_stable(pd, w[lo]));
    assert(w[0] != w[lo]) by {
        if w[0] == w[lo] {
            assert(apply_embedding_symbol(se, c) =~= apply_embedding_symbol(se, w2[lv]));
            assert(seq![pw[0]] =~= seq![pw[bj]]);
            assert(pw[0] == pw[bj]);
        }
    }
    assert forall|k: int| 0 < k < lo implies !is_stable(pd, #[trigger] w[k]) by {
        assert(w[k] == w2[k - 1]);
    }

    // --- the middle, as emb(φ_F, mid) ---
    let mid = w.subrange(1, lo);
    assert(mid =~= w2.subrange(0, lv)) by {
        assert(mid.len() == lv);
        assert forall|k: int| 0 <= k < lv implies mid[k] == w2.subrange(0, lv)[k] by {
            assert(mid[k] == w[k + 1]);
            assert(w[k + 1] == w2[k]);
        }
    }
    assert(word_valid(mid, (n + 3) as nat)) by {
        assert forall|k: int| 0 <= k < mid.len() implies symbol_valid(#[trigger] mid[k], (n + 3) as nat)
        by {
            assert(mid[k] == w2[k]);
            assert(!is_stable(pd, w2[k]));
            assert(symbol_valid(w2[k], (n + 4) as nat));
            assert(generator_index(w2[k]) != st);
        }
    }
    lemma_apply_embedding_agree_prefix(se, pf, mid, (n + 3) as nat);
    assert(apply_embedding(se, mid) =~= apply_embedding(pf, mid));
    assert(apply_embedding(se, mid) =~= pw2.subrange(0, bj - 1)) by {
        assert(mid =~= w2.subrange(0, lv));
    }
    let pinch_mid = pw.subrange(1, bj);
    assert(pinch_mid =~= pw2.subrange(0, bj - 1)) by {
        assert(pinch_mid.len() == bj - 1);
        assert forall|k: int| 0 <= k < bj - 1 implies pinch_mid[k] == pw2.subrange(0, bj - 1)[k] by {
            assert(pinch_mid[k] == pw[k + 1]);
            assert(pw[k + 1] == pw2[k]);
        }
    }
    assert(pinch_mid =~= apply_embedding(pf, mid));

    // --- columns: pdS columns (S) for the middle, pd columns (bet) for the assembly ---
    let a_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].0);
    let b_col = Seq::new(pd.associations.len(), |k: int| pd.associations[k].1);
    let a_col_S = Seq::new(pdS.associations.len(), |k: int| pdS.associations[k].0);
    let b_col_S = Seq::new(pdS.associations.len(), |k: int| pdS.associations[k].1);
    assert(pd.associations =~= pa_assoc(n, m, bet) && pd.associations.len() == bet.len());
    assert(pdS.associations =~= pa_assoc(n, m, s_slice) && pdS.associations.len() == s_slice.len());
    assert(a_col =~= config_emb(bet)) by {
        assert(config_emb(bet).len() == bet.len());
        assert forall|k: int| 0 <= k < bet.len() implies a_col[k] == config_emb(bet)[k] by {
            assert(pd.associations[k] == (crate::machine_group::config_word(bet[k], 0), pa_rhs(n, m, bet[k])));
        }
    }
    assert(b_col =~= pa_rhs_emb(n, m, bet)) by {
        assert(pa_rhs_emb(n, m, bet).len() == bet.len());
        assert forall|k: int| 0 <= k < bet.len() implies b_col[k] == pa_rhs_emb(n, m, bet)[k] by {
            assert(pd.associations[k] == (crate::machine_group::config_word(bet[k], 0), pa_rhs(n, m, bet[k])));
        }
    }
    assert(a_col_S =~= config_emb(s_slice)) by {
        assert(config_emb(s_slice).len() == s_slice.len());
        assert forall|k: int| 0 <= k < s_slice.len() implies a_col_S[k] == config_emb(s_slice)[k] by {
            assert(pdS.associations[k] == (crate::machine_group::config_word(s_slice[k], 0), pa_rhs(n, m, s_slice[k])));
        }
    }
    assert(b_col_S =~= pa_rhs_emb(n, m, s_slice)) by {
        assert(pa_rhs_emb(n, m, s_slice).len() == s_slice.len());
        assert forall|k: int| 0 <= k < s_slice.len() implies b_col_S[k] == pa_rhs_emb(n, m, s_slice)[k] by {
            assert(pdS.associations[k] == (crate::machine_group::config_word(s_slice[k], 0), pa_rhs(n, m, s_slice[k])));
        }
    }

    // --- middle (over pdS = S) recognized in σbet, reflected to mid (over pd = bet), then assemble ---
    assert(has_adjacent_opposite_at(pd, w, 0, lo)) by {
        assert(is_stable(pd, w[0]) && is_stable(pd, w[lo]) && w[0] != w[lo]);
    }
    if pw[0] == Symbol::Gen(st) {
        assert(pw[bj] == Symbol::Inv(st)) by { assert(pw[0] != pw[bj]); assert(is_stable(pd, pw[bj])); }
        assert(w[0] == Symbol::Gen(st) && w[lo] == Symbol::Inv(st)) by {
            assert(w[0] == pw[0]);
            assert(seq![w[lo]] =~= seq![pw[bj]]) by { assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj-1]]); }
        }
        // middle ∈ ⟨b_col_S = pa_rhs_emb(S)⟩  (from has_pinch_at(pdS, pw, 0, bj)).
        assert(in_generated_subgroup(pdS.base, b_col_S, pinch_mid));
        assert(in_generated_subgroup(fg, pa_rhs_emb(n, m, s_slice), apply_embedding(pf, mid)));
        // §4.2 b-side recognition: ⟨pa_rhs_emb(S)⟩ ⟹ ⟨pa_rhs_emb(σbet)⟩.
        lemma_phi_image_pa_rhs_support(mm, n, m, l, mid, s_slice);
        assert(in_generated_subgroup(fg, pa_rhs_emb(n, m, sbet), apply_embedding(pf, mid)));
        lemma_pa_rhs_reflect_intersection(mm, n, m, l, mid, bet);
        assert(in_generated_subgroup(fg, pa_rhs_emb(n, m, bet), mid));
        assert(in_generated_subgroup(pd.base, b_col, w.subrange(1, lo)));
        assert(has_pinch_at(pd, w, 0, lo));
    } else {
        assert(pw[0] == Symbol::Inv(st));
        assert(pw[bj] == Symbol::Gen(st)) by { assert(pw[0] != pw[bj]); assert(is_stable(pd, pw[bj])); }
        assert(w[0] == Symbol::Inv(st) && w[lo] == Symbol::Gen(st)) by {
            assert(w[0] == pw[0]);
            assert(seq![w[lo]] =~= seq![pw[bj]]) by { assert(apply_embedding_symbol(se, w2[lv]) =~= seq![pw2[bj-1]]); }
        }
        // middle ∈ ⟨a_col_S = config_emb(S)⟩.
        assert(in_generated_subgroup(pdS.base, a_col_S, pinch_mid));
        assert(in_generated_subgroup(fg, config_emb(s_slice), apply_embedding(pf, mid)));
        // §4.2 a-side recognition: ⟨config_emb(S)⟩ ⟹ ⟨config_emb(σbet)⟩.
        lemma_phi_image_config_support(n, m, l, mid, s_slice);
        assert(in_generated_subgroup(fg, config_emb(sbet), apply_embedding(pf, mid)));
        lemma_config_reflect_intersection(mm, n, m, l, mid, bet);
        assert(in_generated_subgroup(fg, config_emb(bet), mid));
        assert(in_generated_subgroup(pd.base, a_col, w.subrange(1, lo)));
        assert(has_pinch_at(pd, w, 0, lo));
    }
    assert(has_pinch(pd, w)) by { assert(has_pinch_at(pd, w, 0, lo)); }
}

/// **CS-4d superset-slice pinch-descent**: a pinch of `pw = emb(φ_l_src, w)` over `pa_data(S)`
/// descends to a pinch of `w` over `pa_data(bet_of(S))`.  Mirror of `lemma_mapb_pinch_descends_rt`
/// with the peel running over `S` and the spanning case delegating to `lemma_mapb_pinch_spanning_S`.
pub proof fn lemma_mapb_pinch_descends_S(mm: ModMachine, n: nat, m: nat, l: nat, s_slice: Seq<nat>,
    w: Word)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        s_slice.no_duplicates(),
        forall|i: int| 0 <= i < s_slice.len() ==> numbers_word(n, m, #[trigger] s_slice[i]),
        word_valid(w, (n + 4) as nat),
        has_pinch(pa_data(n, m, s_slice), apply_embedding(phi_l_src(n, m, l), w)),
    ensures
        has_pinch(pa_data(n, m, bet_of(s_slice, m, l)), w),
    decreases w.len(),
{
    let bet = bet_of(s_slice, m, l);
    let pd = pa_data(n, m, bet);
    let pdS = pa_data(n, m, s_slice);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let se = stable_emb(fg, pf);
    let st = (n + 3) as nat;
    lemma_phi_l_src_eq_stable_emb(n, m, l);
    assert(phi_l_src(n, m, l) == se);
    let pw = apply_embedding(se, w);

    lemma_free_group_valid((n + 3) as nat);
    lemma_bet_of_no_dup(s_slice, m, l);
    lemma_bet_of_number_words(s_slice, n, m, l);
    lemma_pa_data_shape(n, m, bet);
    lemma_pa_data_shape(n, m, s_slice);
    assert(pd.base.num_generators == st && pdS.base.num_generators == st);
    lemma_phi_F_family_free(n, m, l);
    assert(pf.len() == n + 3);
    assert(se == pf.push(seq![Symbol::Gen(st)]));
    assert forall|x: Symbol| is_stable(pdS, x) == is_stable(pd, x) by {}

    let ij: (int, int) = choose|i: int, j: int| has_pinch_at(pdS, pw, i, j);
    let bi = ij.0;
    let bj = ij.1;
    assert(has_pinch_at(pdS, pw, bi, bj));
    assert(has_adjacent_opposite_at(pdS, pw, bi, bj));

    assert(w.len() > 0) by { if w.len() == 0 { assert(pw =~= Seq::<Symbol>::empty()); } }
    let c = w[0];
    let w2 = w.drop_first();
    assert(w =~= seq![c] + w2);
    assert(word_valid(w2, (n + 4) as nat)) by {
        assert forall|k: int| 0 <= k < w2.len() implies symbol_valid(#[trigger] w2[k], (n + 4) as nat)
        by { assert(w2[k] == w[k + 1]); }
    }
    lemma_apply_embedding_concat(se, seq![c], w2);
    let ec = apply_embedding(se, seq![c]);
    let pw2 = apply_embedding(se, w2);
    assert(ec =~= apply_embedding_symbol(se, c)) by { reveal_with_fuel(apply_embedding, 2); }
    assert(pw =~= ec + pw2);
    assert(symbol_valid(c, (n + 4) as nat)) by { assert(c == w[0]); }

    if is_stable(pdS, c) {
        assert(c == Symbol::Gen(st) || c == Symbol::Inv(st));
        if c == Symbol::Gen(st) {
            assert(ec =~= seq![Symbol::Gen(st)]) by { assert(se[st as int] == seq![Symbol::Gen(st)]); }
        } else {
            assert(se[st as int] == seq![Symbol::Gen(st)]);
            assert(ec =~= inverse_word(seq![Symbol::Gen(st)]));
            assert(ec =~= seq![Symbol::Inv(st)]) by { reveal_with_fuel(inverse_word, 2); }
        }
        assert(ec.len() == 1 && ec[0] == c);
        assert(pw[0] == ec[0] && pw[0] == c);
        if bi == 0 {
            lemma_mapb_pinch_spanning_S(mm, n, m, l, s_slice, w, w2, bi, bj);
        } else {
            assert(pw =~= ec + pw2);
            lemma_strip_prefix_preserves_pinch(pdS, ec, pw2, bi, bj);
            assert(apply_embedding(phi_l_src(n, m, l), w2) == pw2);
            lemma_mapb_pinch_descends_S(mm, n, m, l, s_slice, w2);
            lemma_prepend_preserves_pinch(pd, c, w2);
            assert(seq![c] + w2 =~= w);
        }
    } else {
        assert(generator_index(c) < st) by {
            assert(symbol_valid(c, (n + 4) as nat));
            assert(generator_index(c) != st);
        }
        assert(generator_index(c) < pf.len());
        let gi = generator_index(c) as int;
        if c == Symbol::Gen(generator_index(c)) {
            assert(ec =~= se[gi]) by { reveal_with_fuel(apply_embedding, 2); lemma_concat_empty_right(se[gi]); }
            assert(se[gi] == pf[gi]);
            lemma_word_valid_no_inner_stable(fg, pf[gi]);
        } else {
            assert(c == Symbol::Inv(generator_index(c)));
            assert(ec =~= inverse_word(se[gi])) by {
                reveal_with_fuel(apply_embedding, 2); lemma_concat_empty_right(inverse_word(se[gi]));
            }
            assert(se[gi] == pf[gi]);
            crate::word::lemma_inverse_word_valid(pf[gi], (n + 3) as nat);
            lemma_word_valid_no_inner_stable(fg, inverse_word(pf[gi]));
        }
        let elen = ec.len() as int;
        assert(forall|k: int| 0 <= k < elen ==> !is_stable_at(pdS, ec, k, st));
        assert(forall|k: int| 0 <= k < elen ==> #[trigger] pw[k] == ec[k]);
        assert(is_stable(pdS, pw[bi]));
        assert(bi >= elen) by {
            if bi < elen {
                assert(pw[bi] == ec[bi]);
                assert(!is_stable(pdS, ec[bi])) by { assert(0 <= bi < elen); }
            }
        }
        lemma_strip_prefix_preserves_pinch(pdS, ec, pw2, bi, bj);
        assert(apply_embedding(phi_l_src(n, m, l), w2) == pw2);
        lemma_mapb_pinch_descends_S(mm, n, m, l, s_slice, w2);
        lemma_prepend_preserves_pinch(pd, c, w2);
        assert(seq![c] + w2 =~= w);
    }
}

// ----------------------------------------------------------------------------
// M2 — `φ_l_src` injective on `P_A` (the Britton peel, mirror of `lemma_map_a_forward`).
// ----------------------------------------------------------------------------

/// `stable_count` depends only on `base.num_generators` (`is_stable`), so it transfers between two
/// HNN data with the same base generator count.
proof fn lemma_stable_count_same_base(d1: HNNData, d2: HNNData, w: Word)
    requires
        d1.base.num_generators == d2.base.num_generators,
    ensures
        stable_count(d1, w) == stable_count(d2, w),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        assert(is_stable(d1, w.last()) == is_stable(d2, w.last()));
        lemma_stable_count_same_base(d1, d2, w.drop_last());
    }
}

/// **M2 — `φ_l_src` is injective on `P_A`**: `emb(φ_l_src, w) ≡_{P_A} ε ⟹ w ≡_{P_A} ε`.  A Britton
/// peel over `pa_data` (`decreases stable_count`).  Base case (no stable letter): `emb(φ_l_src, w) =
/// emb(φ_F, w)` descends `P_A → free(n+3)` (`lemma_single_hnn_base_faithful` + the pa iso), then
/// `φ_F` free gives `w ≡_{free} ε`, then base-embeds.  Step case: `britton_lemma_full` (pa iso) gives
/// a pinch of `emb(φ_l_src, w)`; descend it to a pinch of `w` (the spanning descent); pinch out
/// (`lemma_pd_pinch_out`); `φ_l_src` respects `P_A`'s relators so `emb(φ_l_src, w) ≡ emb(φ_l_src,
/// wshort)`; recurse.
pub proof fn lemma_mapb_M2(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        sigma_backsat(bet, m, l),
        sigma_fwdsat(bet, m, l),
        hnn_associations_isomorphic(pa_data(n, m, bet)),
        word_valid(w, (n + 4) as nat),
        equiv_in_presentation(hnn_presentation(pa_data(n, m, bet)),
            apply_embedding(phi_l_src(n, m, l), w), empty_word()),
    ensures
        equiv_in_presentation(hnn_presentation(pa_data(n, m, bet)), w, empty_word()),
    decreases stable_count(pa_data(n, m, bet), w),
{
    let pd = pa_data(n, m, bet);
    let src = hnn_presentation(pd);
    let phi = phi_l_src(n, m, l);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let pw = apply_embedding(phi, w);

    lemma_free_group_valid((n + 3) as nat);
    lemma_pa_data_shape(n, m, bet);
    assert(pd.base.num_generators == n + 3);
    assert(pd.base == fg);
    lemma_pa_data_valid(n, m, bet);
    lemma_hnn_presentation_valid(pd);
    assert(src.num_generators == n + 4);
    lemma_phi_F_family_free(n, m, l);                          // is_free_family(fg, pf)
    assert(pf.len() == n + 3);
    lemma_phi_l_src_valid(n, m, l);
    lemma_phi_l_src_len(n, m, l);

    if stable_count(pd, w) == 0 {
        // --- base case: w is an F-word over n+3 ---
        lemma_stable_count_zero_no_stable(pd, w);
        assert(word_valid(w, (n + 3) as nat)) by {
            assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], (n + 3) as nat)
            by {
                assert(!is_stable(pd, w[k]));
                assert(symbol_valid(w[k], (n + 4) as nat));
                assert(generator_index(w[k]) != n + 3);
                match w[k] {
                    Symbol::Gen(gg) => { },
                    Symbol::Inv(gg) => { },
                }
            }
        }
        // emb(φ_l_src, w) = emb(φ_F, w) (agree on first n+3), a base word over n+3.
        assert forall|i: int| 0 <= i < n + 3 implies phi[i] == pf[i] by {}
        lemma_apply_embedding_agree_prefix(phi, pf, w, (n + 3) as nat);
        assert(pw == apply_embedding(pf, w));
        lemma_apply_embedding_valid(pf, w, (n + 3) as nat);
        // P_A → free(n+3): emb(φ_F, w) ≡_{free} ε.
        lemma_single_hnn_base_faithful(pd, pw);
        assert(equiv_in_presentation(fg, pw, empty_word()));
        // φ_F free ⟹ w ≡_{free} ε.
        assert(word_valid(w, pf.len()));
        assert(equiv_in_presentation(free_group(pf.len()), w, empty_word()));
        // base embeds ⟹ w ≡_{P_A} ε.
        lemma_base_embeds_in_hnn(pd, w, empty_word());
    } else {
        // --- step case ---
        // stable_count(pd, pw) == stable_count(pd, w) > 0.
        lemma_extend_stable_count_eq(fg, pf, w);
        assert(stable_emb(fg, pf) == phi) by { lemma_phi_l_src_eq_stable_emb(n, m, l); }
        assert(stable_count(free_stable_data(fg), pw)
            == stable_count(free_stable_data(free_group(pf.len())), w));
        lemma_stable_count_same_base(pd, free_stable_data(fg), pw);
        lemma_stable_count_same_base(pd, free_stable_data(free_group(pf.len())), w);
        assert(stable_count(pd, pw) == stable_count(pd, w));
        lemma_stable_count_pos_has_stable(pd, pw);
        assert(has_stable_letter(pd, pw));

        // pw valid over src.num_generators = n+4.
        assert forall|i: int| 0 <= i < phi.len() implies word_valid(#[trigger] phi[i], (n + 4) as nat)
        by {}
        lemma_apply_embedding_valid(phi, w, (n + 4) as nat);

        britton_lemma_full(pd, pw);                            // has_pinch(pd, pw)
        lemma_mapb_pinch_descends(mm, n, m, l, bet, w);        // has_pinch(pd, w)
        let ij = choose|i: int, j: int| has_pinch_at(pd, w, i, j);
        assert(has_pinch_at(pd, w, ij.0, ij.1));

        // pinch out.
        let wshort = lemma_pd_pinch_out(pd, w, ij.0, ij.1);
        assert(equiv_in_presentation(src, w, wshort));
        assert(word_valid(wshort, src.num_generators));
        assert(stable_count(pd, wshort) < stable_count(pd, w));

        // φ_l_src respects P_A's relators ⟹ emb(φ_l_src, w) ≡_{P_A} emb(φ_l_src, wshort).
        assert(src.relators =~= hnn_relators(pd)) by {
            assert(pd.base.relators == Seq::<Word>::empty());
        }
        assert forall|jj: int| 0 <= jj < src.relators.len() implies
            equiv_in_presentation(src, apply_embedding(phi, src.relators[jj]), empty_word()) by {
            assert(src.relators[jj] == hnn_relators(pd)[jj]);
            assert(hnn_relators(pd)[jj] == hnn_relator(pd, jj));
            lemma_phi_l_src_on_pa_relator(mm, n, m, l, bet, jj);
        }
        lemma_emb_respects_source_equiv(src, src, phi, w, wshort);
        lemma_equiv_symmetric(src, pw, apply_embedding(phi, wshort));
        lemma_equiv_transitive(src, apply_embedding(phi, wshort), pw, empty_word());

        // recurse.
        lemma_mapb_M2(mm, n, m, l, bet, wshort);
        lemma_equiv_transitive(src, w, wshort, empty_word());
    }
}

/// **R3 — the retargeted cross-index M2**: `emb(φ_l_src, w) ≡_{P_A(σbet)} ε ⟹ w ≡_{P_A(bet)} ε`.
/// Britton peel over `pa_data(σbet)` for the IMAGE (taking its iso as a hypothesis — finite σbet, prove
/// via `lemma_pa_data_isomorphic`), `lemma_mapb_pinch_descends_rt` to descend the pinch to `w` over
/// `pa_data(bet)`, pinch-out over `pa_data(bet)`, and R1 (`lemma_phi_l_src_on_pa_relator_retarget`)
/// for the cross-presentation `lemma_emb_respects_source_equiv` (φ_l_src maps `pd`-relators to `≡ε` in
/// `pdt`).  `decreases stable_count(pd, w)`.  **No σ-saturation.**
pub proof fn lemma_mapb_M2_rt(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        hnn_associations_isomorphic(pa_data(n, m, sigma_betas(bet, m, l))),
        word_valid(w, (n + 4) as nat),
        equiv_in_presentation(hnn_presentation(pa_data(n, m, sigma_betas(bet, m, l))),
            apply_embedding(phi_l_src(n, m, l), w), empty_word()),
    ensures
        equiv_in_presentation(hnn_presentation(pa_data(n, m, bet)), w, empty_word()),
    decreases stable_count(pa_data(n, m, bet), w),
{
    let sbet = sigma_betas(bet, m, l);
    let pd = pa_data(n, m, bet);
    let pdt = pa_data(n, m, sbet);
    let src = hnn_presentation(pd);
    let srct = hnn_presentation(pdt);
    let phi = phi_l_src(n, m, l);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let pw = apply_embedding(phi, w);

    lemma_free_group_valid((n + 3) as nat);
    lemma_pa_data_shape(n, m, bet);
    lemma_sigma_betas_numbers_word(n, m, l, bet);
    lemma_pa_data_shape(n, m, sbet);
    assert(pd.base.num_generators == n + 3 && pdt.base.num_generators == n + 3);
    assert(pd.base == fg && pdt.base == fg);
    lemma_pa_data_valid(n, m, bet);
    lemma_pa_data_valid(n, m, sbet);
    lemma_hnn_presentation_valid(pd);
    lemma_hnn_presentation_valid(pdt);
    assert(src.num_generators == n + 4 && srct.num_generators == n + 4);
    lemma_phi_F_family_free(n, m, l);
    assert(pf.len() == n + 3);
    lemma_phi_l_src_valid(n, m, l);
    lemma_phi_l_src_len(n, m, l);
    // is_stable / stable_count agree across pd / pdt (same base.num).
    assert forall|x: Symbol| is_stable(pdt, x) == is_stable(pd, x) by {}
    lemma_stable_count_same_base(pdt, pd, w);
    lemma_stable_count_same_base(pdt, pd, pw);

    if stable_count(pd, w) == 0 {
        // --- base case: w is an F-word over n+3 ---
        lemma_stable_count_zero_no_stable(pd, w);
        assert(word_valid(w, (n + 3) as nat)) by {
            assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], (n + 3) as nat)
            by {
                assert(!is_stable(pd, w[k]));
                assert(symbol_valid(w[k], (n + 4) as nat));
                assert(generator_index(w[k]) != n + 3);
                match w[k] {
                    Symbol::Gen(gg) => { },
                    Symbol::Inv(gg) => { },
                }
            }
        }
        // emb(φ_l_src, w) = emb(φ_F, w), a base word over n+3, ≡ε in srct = P_A(σbet).
        assert forall|i: int| 0 <= i < n + 3 implies phi[i] == pf[i] by {}
        lemma_apply_embedding_agree_prefix(phi, pf, w, (n + 3) as nat);
        assert(pw == apply_embedding(pf, w));
        lemma_apply_embedding_valid(pf, w, (n + 3) as nat);
        // P_A(σbet) → free(n+3): emb(φ_F, w) ≡_{free} ε  (pdt iso).
        lemma_single_hnn_base_faithful(pdt, pw);
        assert(equiv_in_presentation(fg, pw, empty_word()));
        // φ_F free ⟹ w ≡_{free} ε.
        assert(word_valid(w, pf.len()));
        assert(equiv_in_presentation(free_group(pf.len()), w, empty_word()));
        // base embeds into pd ⟹ w ≡_{P_A(bet)} ε.
        lemma_base_embeds_in_hnn(pd, w, empty_word());
    } else {
        // --- step case ---
        lemma_extend_stable_count_eq(fg, pf, w);
        assert(stable_emb(fg, pf) == phi) by { lemma_phi_l_src_eq_stable_emb(n, m, l); }
        assert(stable_count(free_stable_data(fg), pw)
            == stable_count(free_stable_data(free_group(pf.len())), w));
        lemma_stable_count_same_base(pd, free_stable_data(fg), pw);
        lemma_stable_count_same_base(pd, free_stable_data(free_group(pf.len())), w);
        assert(stable_count(pdt, pw) == stable_count(pd, w));
        lemma_stable_count_pos_has_stable(pdt, pw);
        assert(has_stable_letter(pdt, pw));

        assert forall|i: int| 0 <= i < phi.len() implies word_valid(#[trigger] phi[i], (n + 4) as nat)
        by {}
        lemma_apply_embedding_valid(phi, w, (n + 4) as nat);

        britton_lemma_full(pdt, pw);                           // has_pinch(pdt, pw)  [pdt iso]
        lemma_mapb_pinch_descends_rt(mm, n, m, l, bet, w);     // has_pinch(pd, w)
        let ij = choose|i: int, j: int| has_pinch_at(pd, w, i, j);
        assert(has_pinch_at(pd, w, ij.0, ij.1));

        // pinch out over pd = P_A(bet).
        let wshort = lemma_pd_pinch_out(pd, w, ij.0, ij.1);
        assert(equiv_in_presentation(src, w, wshort));
        assert(word_valid(wshort, src.num_generators));
        assert(stable_count(pd, wshort) < stable_count(pd, w));

        // φ_l_src maps pd's relators to ≡ε in pdt (R1) ⟹ emb(φ, w) ≡_{pdt} emb(φ, wshort).
        assert(src.relators =~= hnn_relators(pd)) by {
            assert(pd.base.relators == Seq::<Word>::empty());
        }
        assert forall|jj: int| 0 <= jj < src.relators.len() implies
            equiv_in_presentation(srct, apply_embedding(phi, src.relators[jj]), empty_word()) by {
            assert(src.relators[jj] == hnn_relators(pd)[jj]);
            assert(hnn_relators(pd)[jj] == hnn_relator(pd, jj));
            lemma_phi_l_src_on_pa_relator_retarget(mm, n, m, l, bet, jj);
        }
        lemma_emb_respects_source_equiv(src, srct, phi, w, wshort);
        lemma_equiv_symmetric(srct, pw, apply_embedding(phi, wshort));
        lemma_equiv_transitive(srct, apply_embedding(phi, wshort), pw, empty_word());

        // recurse: emb(φ, wshort) ≡_{pdt} ε ⟹ wshort ≡_{pd} ε.
        lemma_mapb_M2_rt(mm, n, m, l, bet, wshort);
        lemma_equiv_transitive(src, w, wshort, empty_word());
    }
}

// ----------------------------------------------------------------------------
// map_b forward — the backward crux direction (Route II factoring assembled).
// ----------------------------------------------------------------------------

/// **`map_b` FORWARD (faithful)**: `emb(b_words, w) ≡_{h2_II} ε ⟹ w ≡_{P_A} ε`.  Route II
/// (factoring): `emb(b_words, w) = emb(a_words, emb(φ_l_src, w))` (M1) ⟹ (map_a forward)
/// `emb(φ_l_src, w) ≡_{P_A} ε` ⟹ (M2 = φ_l_src injective on P_A) `w ≡_{P_A} ε`.  With the
/// von-Dyck-backward half (DONE), this completes `map_b` as a FAITHFUL embedding `P_A ↪ h2_II`.
pub proof fn lemma_map_b_forward(mm: ModMachine, n: nat, m: nat, l: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        sigma_backsat(betas(alphas), m, l),
        sigma_fwdsat(betas(alphas), m, l),
        word_valid(w, (n + 4) as nat),
        equiv_in_presentation(h2_II(mm, n, m, alphas),
            apply_embedding(b_words(mm, n, m, l), w), empty_word()),
    ensures
        equiv_in_presentation(hnn_presentation(pa_data(n, m, betas(alphas))), w, empty_word()),
{
    let bet = betas(alphas);
    let phi = phi_l_src(n, m, l);
    let pw = apply_embedding(phi, w);
    let h2ii = h2_II(mm, n, m, alphas);
    lemma_betas_index(alphas);

    // M1: emb(b_words, w) = emb(a_words, pw) ⟹ emb(a_words, pw) ≡_{h2_II} ε.
    lemma_mapb_factor_source(mm, n, m, l, w);
    assert(apply_embedding(b_words(mm, n, m, l), w) =~= apply_embedding(a_words(mm, n), pw));
    assert(equiv_in_presentation(h2ii, apply_embedding(a_words(mm, n), pw), empty_word()));

    // pw valid over n+4.
    lemma_phi_l_src_valid(n, m, l);
    lemma_phi_l_src_len(n, m, l);
    lemma_apply_embedding_valid(phi, w, (n + 4) as nat);

    // map_a forward ⟹ pw ≡_{P_A} ε.
    lemma_map_a_forward(mm, n, m, alphas, pw);
    assert(equiv_in_presentation(hnn_presentation(pa_data(n, m, bet)), pw, empty_word()));

    // betas side conditions (no-duplicates, numbers_word) + pa iso.
    assert forall|i: int| 0 <= i < bet.len() implies numbers_word(n, m, #[trigger] bet[i]) by {
        if i == 0 { assert(bet[0] == 0); } else { assert(bet[i] == alphas[i - 1]); }
    }
    assert(bet.no_duplicates()) by {
        assert forall|i: int, j: int|
            0 <= i < bet.len() && 0 <= j < bet.len() && i != j implies bet[i] != bet[j] by {
            if i == 0 {
                assert(bet[j] == alphas[j - 1]);
                assert(alphas.contains(alphas[j - 1]));
            } else if j == 0 {
                assert(bet[i] == alphas[i - 1]);
                assert(alphas.contains(alphas[i - 1]));
            } else {
                assert(bet[i] == alphas[i - 1] && bet[j] == alphas[j - 1]);
            }
        }
    }
    lemma_pa_data_isomorphic(mm, n, m, alphas);                // hnn_associations_isomorphic(pa_data(bet))

    // M2 ⟹ w ≡_{P_A} ε.
    lemma_mapb_M2(mm, n, m, l, bet, w);
}

// ----------------------------------------------------------------------------
// map_b forward (RETARGETED, R4) — the direct b_words Britton peel over recog.
//
// The Route-II factoring (map_a fwd → M2_rt) is BLOCKED: map_a-fwd landing in σbet for an opaque
// word is FALSE (a `pa_data(betas)` relator over γ∈betas\σbet maps trivially into h2_II but is
// nontrivial in `P_A(σbet)`), and it's true only for φ_l_src-images — where pinch-out destroys the
// image structure so the recursion can't keep it as an invariant.  So peel `b_words` DIRECTLY over
// `recog_data` (= h2_II), recursing on the clean word `w`.  The pinch-descent COMPOSES two existing
// descents: `lemma_map_a_pinch_descends` (a_words relabel: recog → pa_data(betas)) ∘
// `lemma_mapb_pinch_descends` (φ_l_src self-endo spanning, backsat-only).  With the final target =
// betas(alphas), the OLD self-endo (R) reflections (`lemma_config_reflect_full`/
// `lemma_pa_rhs_reflect_full`) are EXACTLY right (bet→bet) and need `sigma_backsat` ONLY — NO fwdsat.
// ----------------------------------------------------------------------------

/// **R4 — the retargeted `map_b` forward**: `emb(b_words, w) ≡_{h2_II} ε ⟹ w ≡_{P_A(betas(alphas))} ε`,
/// the direct `b_words` Britton peel (`decreases stable_count(pa_data(betas(alphas)), w)`).  Base case
/// (`w` an F-word): `emb(b_words, w) = emb(a_words_F, emb(φ_F, w))` → B4 (`h1_faithful`) → `a_words_F`
/// free → `φ_F` free → base-embeds.  Step: `britton_lemma_full` over `recog` (A1) gives a pinch of
/// `emb(b_words, w) = emb(a_words, g)` (M1, `g = emb(φ_l_src, w)`); the COMPOSED descent
/// (`lemma_map_a_pinch_descends` then `lemma_mapb_pinch_descends`, backsat-only) lands a pinch of `w`
/// over `P_A`; pinch out (`lemma_pd_pinch_out`); `b_words` respects `P_A`'s relators in `h2_II`
/// (`lemma_b_words_relator_trivial`, finite-slice) so `emb(b_words, w) ≡ emb(b_words, wshort)`; recurse.
pub proof fn lemma_map_b_forward_rt(mm: ModMachine, n: nat, m: nat, l: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        sigma_backsat(betas(alphas), m, l),
        // finite-slice: for each γ ∈ betas, the image index m·γ+l lands in `alphas`.
        forall|jj: int| 0 <= jj < betas(alphas).len() ==>
            exists|k: int| 0 <= k < alphas.len() && alphas[k] == m * (#[trigger] betas(alphas)[jj]) + l,
        word_valid(w, (n + 4) as nat),
        equiv_in_presentation(h2_II(mm, n, m, alphas),
            apply_embedding(b_words(mm, n, m, l), w), empty_word()),
    ensures
        equiv_in_presentation(hnn_presentation(pa_data(n, m, betas(alphas))), w, empty_word()),
    decreases stable_count(pa_data(n, m, betas(alphas)), w),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bet = betas(alphas);
    let pd = pa_data(n, m, bet);
    let src = hnn_presentation(pd);
    let bw = b_words(mm, n, m, l);
    let aw = a_words(mm, n);
    let awf = a_words_F(mm, n);
    let phi = phi_l_src(n, m, l);
    let pf = phi_F_family(n, m, l);
    let fg = free_group((n + 3) as nat);
    let h2ii = h2_II(mm, n, m, alphas);
    let rd = recog_data(mm, n, m, alphas);
    let g = apply_embedding(phi, w);

    lemma_betas_index(alphas);
    assert forall|i: int| 0 <= i < bet.len() implies numbers_word(n, m, #[trigger] bet[i]) by {
        if i == 0 { assert(bet[0] == 0); } else { assert(bet[i] == alphas[i - 1]); }
    }
    assert(bet.no_duplicates()) by {
        assert forall|i: int, j: int|
            0 <= i < bet.len() && 0 <= j < bet.len() && i != j implies bet[i] != bet[j] by {
            if i == 0 {
                assert(bet[j] == alphas[j - 1]); assert(alphas.contains(alphas[j - 1]));
            } else if j == 0 {
                assert(bet[i] == alphas[i - 1]); assert(alphas.contains(alphas[i - 1]));
            } else {
                assert(bet[i] == alphas[i - 1] && bet[j] == alphas[j - 1]);
            }
        }
    }
    lemma_free_group_valid((n + 3) as nat);
    lemma_pa_data_shape(n, m, bet);
    assert(pd.base.num_generators == n + 3 && pd.base == fg);
    lemma_pa_data_valid(n, m, bet);
    lemma_hnn_presentation_valid(pd);
    assert(src.num_generators == n + 4);
    lemma_phi_F_family_free(n, m, l);
    assert(pf.len() == n + 3);
    lemma_phi_l_src_valid(n, m, l);
    lemma_phi_l_src_len(n, m, l);
    lemma_apply_embedding_valid(phi, w, (n + 4) as nat);     // g valid over n+4

    // M1: emb(b_words, w) = emb(a_words, g),  g = emb(φ_l_src, w).
    lemma_mapb_factor_source(mm, n, m, l, w);
    assert(apply_embedding(bw, w) =~= apply_embedding(aw, g));
    assert(equiv_in_presentation(h2ii, apply_embedding(aw, g), empty_word()));

    if stable_count(pd, w) == 0 {
        // --- base case: w an F-word over n+3 ---
        lemma_stable_count_zero_no_stable(pd, w);
        assert(word_valid(w, (n + 3) as nat)) by {
            assert forall|k: int| 0 <= k < w.len() implies symbol_valid(#[trigger] w[k], (n + 3) as nat)
            by {
                assert(!is_stable(pd, w[k]));
                assert(symbol_valid(w[k], (n + 4) as nat));
                assert(generator_index(w[k]) != n + 3);
                match w[k] { Symbol::Gen(gg) => {}, Symbol::Inv(gg) => {} }
            }
        }
        // g = emb(φ_F, w) (φ_l_src agrees with φ_F on n+3).
        assert forall|i: int| 0 <= i < n + 3 implies phi[i] == pf[i] by {}
        lemma_apply_embedding_agree_prefix(phi, pf, w, (n + 3) as nat);
        assert(g == apply_embedding(pf, w));
        lemma_apply_embedding_valid(pf, w, (n + 3) as nat);    // g valid over n+3
        // emb(aw, g) = emb(awf, g) (g over n+3).
        lemma_a_words_eq_a_words_F(mm, n, g);
        assert(apply_embedding(aw, g) == apply_embedding(awf, g));
        assert(equiv_in_presentation(h2ii, apply_embedding(awf, g), empty_word()));
        // B4: emb(awf, g) ≡_{h1_base} ε.
        lemma_h1_base_num_generators(mm, n);
        let h1ng = h1_base(mm, n).num_generators;
        lemma_map_a_faithful(mm, n);                           // is_free_family(h1_base, awf)
        assert(awf.len() == n + 3);
        lemma_apply_embedding_valid(awf, g, h1ng);
        lemma_h1_faithful_in_h2_II(mm, n, m, alphas, apply_embedding(awf, g));
        assert(equiv_in_presentation(h1_base(mm, n), apply_embedding(awf, g), empty_word()));
        // awf free ⟹ g ≡_{free(n+3)} ε.
        assert(word_valid(g, awf.len()));
        assert(equiv_in_presentation(free_group((n + 3) as nat), g, empty_word()));
        // φ_F free ⟹ w ≡_{free(n+3)} ε.
        assert(word_valid(w, pf.len()));
        assert(equiv_in_presentation(free_group(pf.len()), w, empty_word()));
        // base embeds ⟹ w ≡_{P_A} ε.
        lemma_base_embeds_in_hnn(pd, w, empty_word());
    } else {
        // --- step case ---
        // stable_count(pd, g) == stable_count(pd, w) > 0  (φ_l_src = stable_emb(fg, pf)).
        lemma_extend_stable_count_eq(fg, pf, w);
        assert(stable_emb(fg, pf) == phi) by { lemma_phi_l_src_eq_stable_emb(n, m, l); }
        assert(stable_count(free_stable_data(fg), g)
            == stable_count(free_stable_data(free_group(pf.len())), w));
        lemma_stable_count_same_base(pd, free_stable_data(fg), g);
        lemma_stable_count_same_base(pd, free_stable_data(free_group(pf.len())), w);
        assert(stable_count(pd, g) == stable_count(pd, w));
        lemma_stable_count_pos_has_stable(pd, g);
        let ks = choose|ks: int| 0 <= ks < g.len() && is_stable(pd, g[ks]);
        assert(0 <= ks < g.len() && is_stable(pd, g[ks]));

        // recog valid + iso + presentation.
        lemma_recog_data_valid(mm, n, m, alphas);
        lemma_recog_associations_isomorphic(mm, n, m, alphas);  // A1
        lemma_recog_presentation(mm, n, m, alphas);             // h2ii == hnn_presentation(rd)
        assert(hnn_presentation(rd) == h2ii);
        lemma_hnn_presentation_valid(rd);
        lemma_h1_base_num_generators(mm, n);
        assert(rd.base == h1_base(mm, n));
        assert(rd.base.num_generators == p_idx(nk, n));
        assert(hnn_presentation(rd).num_generators == h2_num_gens(nk, n));

        // has_stable_letter(rd, emb(aw, g)) via the a_words relabeling (same-index).
        lemma_a_words_single_gen(mm, n);
        lemma_single_gen_relabel(aw, g);
        assert(apply_embedding(aw, g).len() == g.len());
        assert(apply_embedding(aw, g)[ks] == relabel_symbol(aw, g[ks]));
        assert(symbol_valid(g[ks], (n + 4) as nat));
        lemma_a_words_relabel_sym(mm, n, g[ks]);
        assert(is_stable(rd, apply_embedding(aw, g)[ks])) by {
            assert(rd.base.num_generators == p_idx(nk, n));
        }
        assert(has_stable_letter(rd, apply_embedding(aw, g))) by {
            assert(is_stable(rd, apply_embedding(aw, g)[ks]));
        }
        // emb(aw, g) valid over recog.num = h2_num_gens.
        assert(word_valid(apply_embedding(aw, g), hnn_presentation(rd).num_generators)) by {
            assert(aw.len() == n + 4);
            assert forall|i: int| 0 <= i < aw.len()
                implies word_valid(#[trigger] aw[i], h2_num_gens(nk, n)) by {
                lemma_a_words_img_valid(mm, n, i);
            }
            lemma_apply_embedding_valid(aw, g, h2_num_gens(nk, n));
        }
        // britton over recog (= h2ii) ⟹ pinch.
        britton_lemma_full(rd, apply_embedding(aw, g));         // has_pinch(rd, emb(aw, g))
        // composed pinch descent: recog → pa_data(bet) (a_words), then φ_l_src self-endo.
        lemma_map_a_pinch_descends(mm, n, m, alphas, g);        // has_pinch(pd, g)
        lemma_mapb_pinch_descends(mm, n, m, l, bet, w);         // has_pinch(pd, w)  [backsat-only]
        let ij = choose|i: int, j: int| has_pinch_at(pd, w, i, j);
        assert(has_pinch_at(pd, w, ij.0, ij.1));

        // pinch out: w ≡_{P_A} wshort, strictly fewer stable letters.
        let wshort = lemma_pd_pinch_out(pd, w, ij.0, ij.1);
        assert(equiv_in_presentation(src, w, wshort));
        assert(word_valid(wshort, src.num_generators));
        assert(stable_count(pd, wshort) < stable_count(pd, w));

        // von-Dyck: b_words respects P_A's relators ⟹ emb(bw, w) ≡_{h2_II} emb(bw, wshort).
        assert(src.relators =~= hnn_relators(pd)) by {
            assert(pd.base.relators == Seq::<Word>::empty());
        }
        lemma_phi_assoc_valid(nk, n, m, l, h2_num_gens(nk, n));
        assert(bw.len() == n + 4);
        assert forall|i: int| 0 <= i < bw.len() implies
            word_valid(#[trigger] bw[i], h2ii.num_generators) by {
            assert(bw[i] == phi_assoc(nk, n, m, l)[i].1);
            assert(h2ii.num_generators == h2_num_gens(nk, n));
        }
        assert forall|jj: int| 0 <= jj < src.relators.len() implies
            equiv_in_presentation(h2ii, apply_embedding(bw, src.relators[jj]), empty_word()) by {
            assert(src.relators[jj] == hnn_relators(pd)[jj]);
            assert(hnn_relators(pd)[jj] == hnn_relator(pd, jj));
            lemma_b_words_relator_trivial(mm, n, m, l, alphas, jj);
        }
        assert(presentation_valid(h2ii)) by { lemma_hnn_presentation_valid(rd); }
        lemma_emb_respects_source_equiv(src, h2ii, bw, w, wshort);
        // emb(bw, w) ≡ emb(bw, wshort) ≡... combine with emb(bw, w) ≡ ε.
        lemma_equiv_symmetric(h2ii, apply_embedding(bw, w), apply_embedding(bw, wshort));
        lemma_equiv_transitive(h2ii, apply_embedding(bw, wshort), apply_embedding(bw, w),
            empty_word());

        // recurse.
        lemma_map_b_forward_rt(mm, n, m, l, alphas, wshort);
        lemma_equiv_transitive(src, w, wshort, empty_word());
    }
}

// ----------------------------------------------------------------------------
// C-asm — the crux biconditional `lemma_phi_l_iso_at_h2II` (the bottom crux at base `h2_II`).
// ----------------------------------------------------------------------------

/// **C-asm — the per-level φ_l iso crux at `h2_II`** (`docs/brick5-c3.2c-plan.md` §5).  For every
/// `w` over the `k = n+4` association slots,
///   `emb(a_words, w) ≡_{h2_II} ε  ⟺  emb(b_words, w) ≡_{h2_II} ε`,
/// both directions chained through `w ≡_{P_A} ε` via the two FAITHFUL embeddings `P_A ↪ h2_II`
/// (`map_a` = inclusion, `map_b` = φ_l), each a biconditional `emb(map, w) ≡_{h2_II} ε ⟺ w ≡_{P_A} ε`
/// (forward = Britton-peel injectivity, backward = von Dyck).  This is the bottom of the a-tower that
/// C3.2d's `decreases l` induction descends to.
pub proof fn lemma_phi_l_iso_at_h2II(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        sigma_backsat(betas(alphas), m, l),
        // finite-slice: for each γ ∈ betas, the image index m·γ+l lands in `alphas` (replaces the
        // unsatisfiable σ-forward-saturation; satisfiable by a bounded σ-orbit `alphas`).
        forall|jj: int| 0 <= jj < betas(alphas).len() ==>
            exists|k: int| 0 <= k < alphas.len() && alphas[k] == m * (#[trigger] betas(alphas)[jj]) + l,
    ensures
        hnn_associations_isomorphic(HNNData {
            base: h2_II(mm, n, m, alphas),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        }),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let data = HNNData { base: h2_II(mm, n, m, alphas), associations: phi_assoc(nk, n, m, l) };
    let k = data.associations.len();
    lemma_phi_assoc_len(nk, n, m, l);
    assert(k == n + 4);
    let a_col = Seq::new(k, |i: int| data.associations[i].0);
    let b_col = Seq::new(k, |i: int| data.associations[i].1);

    // a_col == a_words, b_col == b_words (the literal crux lists).
    lemma_a_words_is_phi_col0(mm, n, m, l);
    assert(a_col =~= a_words(mm, n));
    assert(b_col =~= b_words(mm, n, m, l));

    // a_words images valid over h2_num_gens (= the von-Dyck-backward precondition).
    lemma_phi_assoc_valid(nk, n, m, l, h2_num_gens(nk, n));
    assert(a_words(mm, n).len() == n + 4) by { assert(a_col =~= a_words(mm, n)); }
    assert forall|i: int| 0 <= i < a_words(mm, n).len() implies
        word_valid(#[trigger] a_words(mm, n)[i], h2_num_gens(nk, n)) by {
        assert(a_words(mm, n)[i] == a_col[i]);
        assert(a_col[i] == data.associations[i].0);
    }

    // finite-slice for map_b (forward + backward) is now a direct hypothesis (no σ-fwd-sat needed).

    // the biconditional, chained through w ≡_{P_A} ε.
    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(data.base, apply_embedding(a_col, w), empty_word())
        <==>
        equiv_in_presentation(data.base, apply_embedding(b_col, w), empty_word())
    ) by {
        assert(apply_embedding(a_col, w) == apply_embedding(a_words(mm, n), w));
        assert(apply_embedding(b_col, w) == apply_embedding(b_words(mm, n, m, l), w));
        if equiv_in_presentation(h2_II(mm, n, m, alphas), apply_embedding(a_words(mm, n), w),
            empty_word()) {
            lemma_map_a_forward(mm, n, m, alphas, w);                   // w ≡_{P_A} ε
            lemma_map_b_von_dyck_backward(mm, n, m, l, alphas, w);      // emb(b_words, w) ≡ ε
        }
        if equiv_in_presentation(h2_II(mm, n, m, alphas), apply_embedding(b_words(mm, n, m, l), w),
            empty_word()) {
            lemma_map_b_forward_rt(mm, n, m, l, alphas, w);             // w ≡_{P_A} ε (direct peel)
            lemma_map_a_von_dyck_backward(mm, n, m, alphas, w);         // emb(a_words, w) ≡ ε
        }
    }
}

} // verus!
