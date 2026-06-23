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
use crate::phi_l_pinch::lemma_map_a_forward;
use crate::phi_l_lift::{b_words, lemma_map_a_von_dyck_backward, lemma_map_b_von_dyck_backward};
use crate::phi_l_maps::{a_words, lemma_a_words_is_phi_col0};
use crate::h3_ii::{h2_II, lemma_phi_assoc_len};
use crate::h3::{phi_assoc, lemma_phi_assoc_valid};
use crate::layout::h2_num_gens;
use crate::f_free_a1::{betas, lemma_betas_index};
use crate::r_prime::{sigma_backsat, lemma_config_reflect_full, lemma_config_word_valid2};
use crate::r_prime_b::{pa_rhs_emb, sigma_fwdsat, lemma_pa_rhs_reflect_full, lemma_phi_F_on_pa_rhs};
use crate::free_basis::config_emb;
use crate::word_numbering::numbers_word;
use crate::presentation::{equiv_in_presentation, presentation_valid, lemma_equiv_transitive,
    lemma_equiv_symmetric};
use crate::presentation_lemmas::lemma_relator_is_identity;
use crate::britton_infra::lemma_hnn_presentation_valid;
use crate::machine_group::{lemma_emb_respects_source_equiv, lemma_stable_count_pos_has_stable,
    lemma_stable_count_zero_no_stable};
use crate::phi_l_pinch::lemma_pd_pinch_out;

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
        sigma_fwdsat(bet, m, l),
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
        sigma_fwdsat(bet, m, l),
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
        sigma_fwdsat(betas(alphas), m, l),
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

    // finite-slice for map_b backward: m·γ+l ∈ alphas for each γ ∈ betas (from σ-fwd-sat + l ≥ 1).
    let bet = betas(alphas);
    lemma_betas_index(alphas);
    assert forall|j: int| 0 <= j < bet.len() implies
        exists|kk: int| 0 <= kk < alphas.len() && alphas[kk] == m * (#[trigger] bet[j]) + l by {
        assert(sigma_betas(bet, m, l)[j] == (m * bet[j] + l) as nat);
        assert(bet.contains((m * bet[j] + l) as nat));                  // σ-fwd-sat
        let kk0 = choose|kk0: int| 0 <= kk0 < bet.len() && bet[kk0] == (m * bet[j] + l) as nat;
        assert(0 <= kk0 < bet.len() && bet[kk0] == (m * bet[j] + l) as nat);
        assert(m * bet[j] + l >= 1);                                    // l ≥ 1
        assert(kk0 != 0) by { assert(bet[0] == 0); }
        assert(bet[kk0] == alphas[kk0 - 1]);
    }

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
            lemma_map_b_forward(mm, n, m, l, alphas, w);                // w ≡_{P_A} ε
            lemma_map_a_von_dyck_backward(mm, n, m, alphas, w);         // emb(a_words, w) ≡ ε
        }
    }
}

} // verus!
