// Layer 2 — Cohen §1 assembly, brick CS-4d (the σ-recognition cores). `docs/cohen-cs4d-blueprint.md` §4.2.
//
// The recognition crux of CS-4d (`map_b` faithful, backward `b ⟹ a`): the M2_general Britton peel
// runs over a SUPERSET slice `S = betas(norm)` (a no-dup number-word slice carrying a forced 0-head
// and arbitrary non-σ junk indices), so its pinch-middle lands in `⟨config_emb(S)⟩` (a-side) or
// `⟨pa_rhs_emb(S)⟩` (b-side).  To feed the EXISTING `lemma_config_reflect_intersection` /
// `lemma_pa_rhs_reflect_intersection` (which consume `⟨·_emb(σbet)⟩`), the middle — a `φ_F`-image —
// must first be RECOGNIZED to sit in the smaller `⟨·_emb(σbet)⟩`, where `σbet = sigma_betas(bet_of(S))`
// = the `≡ l (mod m)` elements of `S`.
//
// This is a SIBLING of `lemma_r_prime` (`r_prime.rs`): same `phi_canon_invariant` / `cong_l`
// coordinate-tracking, but the coordinate-restriction step lands DIRECTLY in `σbet` (a coord that is
// in `S` and `≡ l` is — by the very definition of `σbet` — a `σbet`-coordinate, via the round-trip
// `lemma_bet_of_all_preimages`), so NO `sigma_backsat` SHIFT (`lemma_sat_bridge`) is needed.  That is
// the only change from `lemma_r_prime`'s step 5.
//
// This module holds the a-side config core; the b-side `pa_rhs` core lives in `r_prime_b.rs` (it
// needs that module's private coord-selector machinery).  Additive (new module + one lib.rs line).

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::{equiv_in_presentation, lemma_equiv_symmetric, lemma_equiv_transitive};
use crate::machine_group::{CanonLetter, canw_eval, base_A, signed_power, gexp,
    lemma_in_subgroup_respects_equiv, lemma_word_valid_mono, lemma_gexp_concat,
    lemma_gexp_signed_power, lemma_equiv_preserves_gexp};
use crate::config_reduce::{cw_reduce, coord_in, lemma_cw_reduce_coords, lemma_tfree_coord_restrict};
use crate::r_prime::{cong_l, lemma_retraction, lemma_phi_canon_invariant, lemma_membership_to_canon,
    lemma_gexp1_config_factors, lemma_gexp1_canw_zero, lemma_phi_canon_acc_coords, lemma_free_to_base_A,
    lemma_free_cw_reduce_eval, lemma_canw_in_config_subgroup, lemma_phi_prime_emb_valid,
    lemma_phi_F_emb_valid, lemma_canw_eval_valid2, phi_canon_acc, phi_prime};
use crate::phi_l_mapb::{sigma_betas, phi_F_family};
use crate::benign::{apply_embedding, in_generated_subgroup, factors_from_generators, concat_all};
use crate::free_basis::config_emb;
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::word_numbering::lemma_div_mod_step;
use crate::cohen_cs4d::{bet_of, is_sigma_image, lemma_bet_of_all_preimages};

verus! {

// ============================================================================
// Step-5 swap: direct-membership coordinate restriction (NO sat_bridge shift).
// ============================================================================

/// **Coordinate restriction into `σbet` (direct membership)** — the `lemma_coords_in_sigma` analog
/// for CS-4d.  If `canw_eval(cu) ≡_A canw_eval(cs)` with `cu`'s coords `≡ l (mod m)` (`cong_l`) and
/// `cs`'s coords ⊆ a no-dup number-word slice `S`, then under the "all preimages" condition (every
/// `≡ l` element `g ∈ S` has its preimage `g/m ∈ bet`), every coordinate of `cw_reduce(cu)` is a
/// `sigma_betas(bet)`-coordinate.  Unlike `lemma_coords_in_sigma`, the conclusion is reached WITHOUT
/// `sigma_backsat`: a coord `r` that is in `S` and `≡ l` is already a `σbet`-value by construction
/// (`σbet = sigma_betas(bet)` = the `≡ l` elements of `S`).
pub proof fn lemma_coords_in_sigbet(s_slice: Seq<nat>, bet: Seq<nat>, m: nat, l: nat,
    cu: Seq<CanonLetter>, cs: Seq<CanonLetter>)
    requires
        m >= 1,
        l < m,
        equiv_in_presentation(base_A(), canw_eval(cu), canw_eval(cs)),
        forall|i: int| 0 <= i < cu.len() ==> (#[trigger] cu[i]).s == 0 && cong_l(cu[i].r, m, l),
        forall|i: int| 0 <= i < cs.len()
            ==> exists|j: int| 0 <= j < s_slice.len() && s_slice[j] as int == (#[trigger] cs[i]).r,
        forall|g: nat| s_slice.contains(g) && g % m == l ==> bet.contains((g / m)),
    ensures
        forall|idx: int| 0 <= idx < cw_reduce(cu).len() ==> {
            &&& (#[trigger] cw_reduce(cu)[idx]).s == 0
            &&& exists|k: int| 0 <= k < sigma_betas(bet, m, l).len()
                    && sigma_betas(bet, m, l)[k] as int == cw_reduce(cu)[idx].r
        },
{
    let red = cw_reduce(cu);
    lemma_cw_reduce_coords(cu);   // ∀idx. coord_in(cu, red[idx].r, red[idx].s)
    assert forall|idx: int| 0 <= idx < red.len() implies {
        &&& (#[trigger] red[idx]).s == 0
        &&& exists|k: int| 0 <= k < sigma_betas(bet, m, l).len()
                && sigma_betas(bet, m, l)[k] as int == red[idx].r
    } by {
        let r = red[idx].r;
        let st = red[idx].s;
        assert(coord_in(red, r, st)) by { assert(red[idx].r == r && red[idx].s == st); }
        assert(coord_in(cu, r, st));   // from lemma_cw_reduce_coords[idx]
        let i2 = choose|i2: int| 0 <= i2 < cu.len() && cu[i2].r == r && cu[i2].s == st;
        assert(0 <= i2 < cu.len() && cu[i2].r == r && cu[i2].s == st);
        assert(cu[i2].s == 0 && cong_l(cu[i2].r, m, l));
        assert(st == 0 && cong_l(r, m, l));
        // restrict the coord into cs ⊆ S.
        lemma_tfree_coord_restrict(cu, cs, r, st);
        assert(coord_in(cs, r, st));
        let i3 = choose|i3: int| 0 <= i3 < cs.len() && cs[i3].r == r && cs[i3].s == st;
        assert(0 <= i3 < cs.len() && cs[i3].r == r && cs[i3].s == st);
        // r is an S-element (nat).
        let jS = choose|j: int| 0 <= j < s_slice.len() && s_slice[j] as int == cs[i3].r;
        assert(0 <= jS < s_slice.len() && s_slice[jS] as int == r);
        assert(r >= 0);                              // r == s_slice[jS] : nat
        let rn = r as nat;
        assert(rn == s_slice[jS] && s_slice.contains(rn));
        assert((rn as int) == r);
        // cong_l ⟹ r = m·b + l with b ≥ 0; then (b·m + l)/m = b, %m = l.
        let b = choose|b: int| r == #[trigger] ((m as int) * b) + (l as int);
        assert(r == (m as int) * b + (l as int));
        assert(b >= 0) by(nonlinear_arith)
            requires r == (m as int) * b + (l as int), r >= 0, (l as int) < (m as int), m >= 1;
        let bn = b as nat;
        assert((bn as int) == b);
        assert((rn as int) == (bn as int) * (m as int) + (l as int)) by(nonlinear_arith)
            requires (rn as int) == r, r == (m as int) * b + (l as int), (bn as int) == b;
        assert(rn == bn * m + l) by(nonlinear_arith)
            requires (rn as int) == (bn as int) * (m as int) + (l as int);
        lemma_div_mod_step(bn, m, l);                // (bn·m+l)/m == bn, (bn·m+l)%m == l
        assert(rn % m == l && rn / m == bn);
        // all-preimages ⟹ bet contains rn/m = bn.
        assert(bet.contains(bn));                    // hypothesis with g = rn (rn ∈ S, rn%m==l, rn/m==bn)
        let k = choose|k: int| 0 <= k < bet.len() && bet[k] == bn;
        assert(0 <= k < bet.len() && bet[k] == bn);
        // sigma_betas(bet)[k] = m·bet[k] + l = m·bn + l = rn = r.
        assert(sigma_betas(bet, m, l)[k] == (m * bet[k] + l) as nat);
        assert(sigma_betas(bet, m, l)[k] as int == r) by {
            assert(bet[k] == bn);
            assert((m * bn + l) as int == r) by(nonlinear_arith)
                requires (rn as int) == (bn as int) * (m as int) + (l as int), (rn as int) == r;
        }
    }
}

// ============================================================================
// §4.2 a-side core — the recognition crux (config column).
// ============================================================================

/// **a-side recognition crux** — a `φ_F`-image lying in `⟨config_emb(S)⟩` over a no-dup number-word
/// slice `S` actually lies in the σ-restricted `⟨config_emb(σbet)⟩`, where `σbet =
/// sigma_betas(bet_of(S))` = the `≡ l (mod m)` elements of `S`.  Sibling of `lemma_r_prime`: identical
/// `phi_canon_invariant` / `cong_l` coordinate-tracking, but step 5 is `lemma_coords_in_sigbet`
/// (direct membership) instead of `lemma_coords_in_sigma` (`sat_bridge` shift).  No `sigma_backsat`.
pub proof fn lemma_phi_image_config_support(n: nat, m: nat, l: nat, u: Word, s_slice: Seq<nat>)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        word_valid(u, (n + 3) as nat),
        in_generated_subgroup(free_group((n + 3) as nat), config_emb(s_slice),
            apply_embedding(phi_F_family(n, m, l), u)),
    ensures
        in_generated_subgroup(free_group((n + 3) as nat),
            config_emb(sigma_betas(bet_of(s_slice, m, l), m, l)),
            apply_embedding(phi_F_family(n, m, l), u)),
{
    let fg = free_group((n + 3) as nat);
    let g_word = apply_embedding(phi_F_family(n, m, l), u);
    let pp_u = apply_embedding(phi_prime(n, m, l), u);
    let cu = phi_canon_acc(l, m, u, 0);
    let mm = m as int;
    let gx = gexp(1, u);
    let bet = bet_of(s_slice, m, l);
    let sbet = sigma_betas(bet, m, l);
    lemma_free_group_valid((n + 3) as nat);
    lemma_phi_prime_emb_valid(n, m, l, u);   // word_valid(pp_u, n+3)
    lemma_phi_F_emb_valid(n, m, l, u);       // word_valid(g_word, n+3)

    // ---- Step 1: retraction.  pp_u ≡_fg g_word. ----
    lemma_retraction(n, m, l, u, s_slice);
    assert(equiv_in_presentation(fg, pp_u, g_word));

    // ---- Step 2: coordinate-tracking at xe=0.  pp_u ≡_fg canw_eval(cu) + x^{mm·gx}. ----
    lemma_phi_canon_invariant(fg, n, m, l, u, 0);
    let rhs2 = canw_eval(cu) + signed_power(1, mm * gx);
    assert(mm * 0 == 0 && signed_power(1, mm * 0) =~= empty_word());
    lemma_concat_empty_left(pp_u);
    assert(signed_power(1, mm * 0) + pp_u =~= pp_u);
    assert(mm * (0 + gx) == mm * gx);
    assert(equiv_in_presentation(fg, pp_u, rhs2));

    // ---- the config_emb(S) witness + its canon (coords ⊆ S) ----
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(config_emb(s_slice), f)
        && equiv_in_presentation(fg, concat_all(f), g_word);
    assert(factors_from_generators(config_emb(s_slice), factors)
        && equiv_in_presentation(fg, concat_all(factors), g_word));
    let cs = lemma_membership_to_canon(s_slice, factors);
    assert(concat_all(factors) =~= canw_eval(cs));
    assert(equiv_in_presentation(fg, canw_eval(cs), g_word));

    // ---- Step 3: xexp(u) = 0  (gexp(1) of both sides). ----
    lemma_gexp1_config_factors(s_slice, factors);              // gexp(1, concat_all(factors)) = 0
    lemma_equiv_preserves_gexp(fg, concat_all(factors), g_word, 1);   // gexp(1, g_word) = 0
    assert(gexp(1, g_word) == 0);
    lemma_gexp1_canw_zero(cu);
    lemma_gexp_concat(1, canw_eval(cu), signed_power(1, mm * gx));
    lemma_gexp_signed_power(1, 1, mm * gx);
    lemma_equiv_symmetric(fg, pp_u, g_word);                   // equiv(fg, g_word, pp_u)
    lemma_equiv_transitive(fg, g_word, pp_u, rhs2);            // equiv(fg, g_word, rhs2)
    lemma_equiv_preserves_gexp(fg, g_word, rhs2, 1);
    assert(mm * gx == 0);
    assert(gx == 0) by(nonlinear_arith) requires mm * gx == 0, mm >= 1;
    assert(mm * gx == 0 && signed_power(1, mm * gx) =~= empty_word());
    lemma_concat_empty_right(canw_eval(cu));
    assert(rhs2 =~= canw_eval(cu));
    assert(equiv_in_presentation(fg, canw_eval(cu), g_word)) by {
        assert(equiv_in_presentation(fg, g_word, rhs2));
        assert(rhs2 =~= canw_eval(cu));
        lemma_equiv_symmetric(fg, g_word, rhs2);
    }

    // ---- Step 4: free→base_A.  canw_eval(cu) ≡_base_A canw_eval(cs). ----
    lemma_phi_canon_acc_coords(l, m, u, 0);                    // cu: s=0, cong_l
    lemma_canw_eval_valid2(cu);
    lemma_canw_eval_valid2(cs);
    lemma_word_valid_mono(canw_eval(cu), 2, 3);
    lemma_word_valid_mono(canw_eval(cs), 2, 3);
    lemma_equiv_symmetric(fg, canw_eval(cs), g_word);          // equiv(fg, g_word, canw_eval(cs))
    lemma_word_valid_mono(canw_eval(cs), 2, (n + 3) as nat);
    lemma_equiv_transitive(fg, canw_eval(cu), g_word, canw_eval(cs));
    lemma_free_to_base_A((n + 3) as nat, canw_eval(cu), canw_eval(cs));

    // ---- Step 5: coordinate restriction (DIRECT membership, no sat_bridge). ----
    assert(l < m);
    assert forall|gg: nat| s_slice.contains(gg) && gg % m == l implies bet.contains(gg / m) by {
        assert(is_sigma_image(gg, m, l));                      // gg % m == l
        lemma_bet_of_all_preimages(s_slice, m, l, gg);         // bet_of(S).contains(gg/m)
    }
    lemma_coords_in_sigbet(s_slice, bet, m, l, cu, cs);

    // ---- Step 6: free cw_reduce.  canw_eval(cw_reduce(cu)) ≡_fg g_word. ----
    lemma_free_cw_reduce_eval(n, cu);
    lemma_equiv_transitive(fg, canw_eval(cw_reduce(cu)), canw_eval(cu), g_word);

    // ---- Step 7: reconstruction into ⟨config_emb(σbet)⟩ + respects_equiv. ----
    lemma_canw_in_config_subgroup(sbet, n, cw_reduce(cu));
    lemma_in_subgroup_respects_equiv(fg, config_emb(sbet), canw_eval(cw_reduce(cu)), g_word);
}

} // verus!
