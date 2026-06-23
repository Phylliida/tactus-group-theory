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
use crate::machine_group::{ModMachine, mod_machine_wf, lemma_strip_prefix_preserves_pinch,
    lemma_prepend_preserves_pinch};
use crate::benign::{apply_embedding, apply_embedding_symbol, in_generated_subgroup,
    lemma_apply_embedding_concat};
use crate::britton_via_tower::{has_pinch, has_pinch_at, has_adjacent_opposite_at, is_stable};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::f_free::{stable_emb, free_stable_data, is_free_family, lemma_extend_spanning,
    lemma_apply_embedding_agree_prefix, lemma_word_valid_no_inner_stable};
use crate::pa_data::{pa_data, pa_rhs, pa_assoc, pa_b_base, lemma_pa_data_shape};
use crate::phi_l_mapb::{phi_l_src, phi_F_family, lemma_phi_F_family_free, lemma_phi_l_src_len};
use crate::r_prime::{sigma_backsat, lemma_config_reflect_full};
use crate::r_prime_b::{pa_rhs_emb, sigma_fwdsat, lemma_pa_rhs_reflect_full};
use crate::free_basis::config_emb;
use crate::word_numbering::numbers_word;

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

} // verus!
