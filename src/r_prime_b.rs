// Layer 2 — Brick 5, C3.2c / map_b forward — the b-side (R') config-reflection over `pa_rhs`.
//
// The M2 pinch-descent's middle membership comes in BOTH Britton orientations: the a-column
// (`config_emb(betas)`) handled by (R) = `lemma_config_reflect_full` (`r_prime.rs`), and the
// b-column (`pa_rhs_emb(betas)`) handled HERE.  Per Danielle's route: project through `kill_db`
// (kills d,b, fixes t,x), reuse the a-side coordinate core on `emb(φ', u)`, then transfer the
// resulting σ-restriction from the `config_emb` basis back to the `pa_rhs_emb` basis (both free
// families over the same index set `betas`).  See docs/brick5-c3.2c-plan.md §6.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::{presentation_valid, equiv_in_presentation, lemma_equiv_refl,
    lemma_equiv_symmetric, lemma_equiv_transitive};
use crate::machine_group::{ModMachine, g_m, mod_machine_wf, config_word, symbol_power, signed_power,
    CanonLetter, canw_eval, gexp, lemma_signed_power_valid, lemma_gexp_concat, lemma_gexp_signed_power,
    lemma_word_valid_mono, lemma_product_in_subgroup, lemma_in_subgroup_respects_equiv,
    lemma_equiv_preserves_gexp, lemma_config_word_valid, lemma_emb_respects_source_equiv,
    lemma_apply_embedding_in_subgroup, lemma_g_m_num_generators, lemma_g_m_valid,
    lemma_no_relator_equiv_implies_freely_equivalent};
use crate::presentation_lemmas::lemma_freely_equivalent_implies_equiv;
use crate::f_free::is_free_family;
use crate::phi_l_forward::lemma_intersection_property;
use crate::h3_ii::{compose_embeddings, lemma_apply_embedding_compose};
use crate::free_basis::lemma_config_emb_free;
use crate::r_prime::{lemma_kill_db_on_phi_F, lemma_phi_F_emb_valid};
use crate::h3::lemma_single_gen_valid;
use crate::config_reduce::cw_reduce;
use crate::benign::{apply_embedding, apply_embedding_symbol, in_generated_subgroup,
    factors_from_generators, concat_all, lemma_apply_embedding_concat, lemma_apply_embedding_valid};
use crate::homomorphism::{apply_hom, apply_hom_symbol, lemma_hom_preserves_equiv};
use crate::free_basis::{comp_images, lemma_apply_hom_embedding_compose, lemma_apply_hom_eq_embedding,
    config_emb};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::word_numbering::{w_c, w_b, numbers_word, lemma_w_c_valid, lemma_w_c_gens_in_block,
    lemma_w_b_snoc, alphabet_letter};
use crate::pa_data::{pa_b_base, pa_rhs};
use crate::phi_l_mapb::lemma_phi_F_on_config;
use crate::phi_l_iso::lemma_apply_embedding_fixes;
use crate::phi_l_mapb::{sigma_betas, phi_F_family};
use crate::r_prime::{phi_prime, phi_canon_acc, kill_db, sigma_backsat,
    lemma_phi_prime_emb_valid, lemma_membership_to_canon, lemma_phi_canon_invariant,
    lemma_gexp1_config_factors, lemma_gexp1_canw_zero, lemma_phi_canon_acc_coords,
    lemma_canw_eval_valid2, lemma_free_to_base_A, lemma_coords_in_sigma, lemma_free_cw_reduce_eval,
    lemma_canw_in_config_subgroup, lemma_kill_db_valid, lemma_kill_db_fixes_low,
    lemma_config_word_valid2};
use crate::normal_form_afp_textbook::lemma_subgroup_to_k_word;

verus! {

// ----------------------------------------------------------------------------
// The extracted a-side coordinate core — `emb(φ',u) ∈ ⟨config(bet)⟩ ⟹ ∈ ⟨config(σbet)⟩`.
// (= `lemma_r_prime` minus the retraction step 1, so it applies to ANY `emb(φ',u)` membership,
// not only those arising as the `kill_db` retraction of an `emb(φ_F,u) ∈ ⟨t,x⟩`.)
// ----------------------------------------------------------------------------

/// **The σ-restriction coordinate core**: a `φ'`-image `emb(φ', u)` lying in `⟨config_emb(bet)⟩`
/// actually lies in the σ-shifted sub-subgroup `⟨config_emb(σbet)⟩`, under σ-backward-saturation.
/// Re-derives `lemma_r_prime`'s steps 2–7 with subject `pp_u = emb(φ', u)` (no retraction needed).
pub proof fn lemma_phi_prime_in_sigma_config(n: nat, m: nat, l: nat, u: Word, bet: Seq<nat>)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        word_valid(u, (n + 3) as nat),
        in_generated_subgroup(free_group((n + 3) as nat), config_emb(bet),
            apply_embedding(phi_prime(n, m, l), u)),
        sigma_backsat(bet, m, l),
    ensures
        in_generated_subgroup(free_group((n + 3) as nat), config_emb(sigma_betas(bet, m, l)),
            apply_embedding(phi_prime(n, m, l), u)),
{
    let fg = free_group((n + 3) as nat);
    let pp_u = apply_embedding(phi_prime(n, m, l), u);
    let cu = phi_canon_acc(l, m, u, 0);
    let mm = m as int;
    let gx = gexp(1, u);
    let sbet = sigma_betas(bet, m, l);
    lemma_free_group_valid((n + 3) as nat);
    lemma_phi_prime_emb_valid(n, m, l, u);    // word_valid(pp_u, n+3)

    // ---- config witness for pp_u + its canon (coords ⊆ bet) ----
    let factors = choose|f: Seq<Word>| #[trigger] factors_from_generators(config_emb(bet), f)
        && equiv_in_presentation(fg, concat_all(f), pp_u);
    assert(factors_from_generators(config_emb(bet), factors)
        && equiv_in_presentation(fg, concat_all(factors), pp_u));
    let cbet = lemma_membership_to_canon(bet, factors);
    assert(concat_all(factors) =~= canw_eval(cbet));
    // pp_u ≡_fg canw_eval(cbet).
    assert(equiv_in_presentation(fg, canw_eval(cbet), pp_u));

    // ---- Step 2: coordinate-tracking at xe=0.  pp_u ≡_fg canw_eval(cu) + x^{mm·gx}. ----
    lemma_phi_canon_invariant(fg, n, m, l, u, 0);
    let rhs2 = canw_eval(cu) + signed_power(1, mm * gx);
    assert(mm * 0 == 0 && signed_power(1, mm * 0) =~= empty_word());
    lemma_concat_empty_left(pp_u);
    assert(signed_power(1, mm * 0) + pp_u =~= pp_u);
    assert(mm * (0 + gx) == mm * gx);
    assert(equiv_in_presentation(fg, pp_u, rhs2));

    // ---- Step 3: xexp(u) = 0  (gexp(1) of both sides; config products have gexp(1)=0). ----
    lemma_gexp1_config_factors(bet, factors);                  // gexp(1, concat_all(factors)) = 0
    lemma_equiv_preserves_gexp(fg, concat_all(factors), pp_u, 1);   // gexp(1, pp_u) = 0
    assert(gexp(1, pp_u) == 0);
    lemma_gexp1_canw_zero(cu);
    lemma_gexp_concat(1, canw_eval(cu), signed_power(1, mm * gx));
    lemma_gexp_signed_power(1, 1, mm * gx);
    lemma_equiv_preserves_gexp(fg, pp_u, rhs2, 1);
    assert(mm * gx == 0);
    assert(gx == 0) by(nonlinear_arith) requires mm * gx == 0, mm >= 1;
    assert(mm * gx == 0 && signed_power(1, mm * gx) =~= empty_word());
    lemma_concat_empty_right(canw_eval(cu));
    assert(rhs2 =~= canw_eval(cu));
    assert(equiv_in_presentation(fg, canw_eval(cu), pp_u)) by {
        assert(equiv_in_presentation(fg, pp_u, rhs2));
        assert(rhs2 =~= canw_eval(cu));
        lemma_equiv_symmetric(fg, pp_u, rhs2);
    }

    // ---- Step 4: free→base_A.  canw_eval(cu) ≡_base_A canw_eval(cbet). ----
    lemma_phi_canon_acc_coords(l, m, u, 0);                    // cu: s=0, cong_l
    lemma_canw_eval_valid2(cu);
    lemma_canw_eval_valid2(cbet);
    lemma_word_valid_mono(canw_eval(cu), 2, 3);
    lemma_word_valid_mono(canw_eval(cbet), 2, 3);
    lemma_equiv_symmetric(fg, canw_eval(cbet), pp_u);          // pp_u ≡ canw_eval(cbet)
    lemma_word_valid_mono(canw_eval(cbet), 2, (n + 3) as nat);
    lemma_equiv_transitive(fg, canw_eval(cu), pp_u, canw_eval(cbet));
    lemma_free_to_base_A((n + 3) as nat, canw_eval(cu), canw_eval(cbet));

    // ---- Step 5: coordinate restriction.  cw_reduce(cu) coords ⊆ σ(bet). ----
    assert(l < m);
    lemma_coords_in_sigma(bet, m, l, cu, cbet);

    // ---- Step 6: free cw_reduce.  canw_eval(cw_reduce(cu)) ≡_fg pp_u. ----
    lemma_free_cw_reduce_eval(n, cu);
    lemma_equiv_transitive(fg, canw_eval(cw_reduce(cu)), canw_eval(cu), pp_u);

    // ---- Step 7: reconstruction into ⟨config_emb(σbet)⟩ + respects_equiv. ----
    lemma_canw_in_config_subgroup(sbet, n, cw_reduce(cu));
    lemma_in_subgroup_respects_equiv(fg, config_emb(sbet), canw_eval(cw_reduce(cu)), pp_u);
}

// ----------------------------------------------------------------------------
// The b-side `pa_rhs` family + the `kill_db` projection `pa_rhs ↦ config`.
// ----------------------------------------------------------------------------

/// **`pa_rhs_emb`** — the b-column family `[pa_rhs(β) : β ∈ bet]` (`pa_rhs(β) = config(β,0)·w_c(β)·d`),
/// the `pa_data` association b-column the M2 pinch-descent reflects through.
pub open spec fn pa_rhs_emb(n: nat, m: nat, bet: Seq<nat>) -> Seq<Word> {
    Seq::new(bet.len(), |i: int| pa_rhs(n, m, bet[i]))
}

/// `kill_db` (gens ≥ 2 ↦ ε) kills any word whose symbols all have generator index ≥ 2.
proof fn lemma_kill_db_emb_kills_high(n: nat, w: Word)
    requires
        word_valid(w, (n + 3) as nat),
        forall|j: int| 0 <= j < w.len() ==> generator_index(#[trigger] w[j]) >= 2,
    ensures
        apply_embedding(kill_db(n).generator_images, w) =~= empty_word(),
    decreases w.len(),
{
    let gi = kill_db(n).generator_images;
    reveal_with_fuel(apply_embedding, 2);
    if w.len() == 0 {
        assert(apply_embedding(gi, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(generator_index(s) >= 2 && symbol_valid(s, (n + 3) as nat)) by { assert(w[0] == s); }
        assert(word_valid(rest, (n + 3) as nat)
            && (forall|j: int| 0 <= j < rest.len() ==> generator_index(#[trigger] rest[j]) >= 2)) by {
            assert forall|k: int| 0 <= k < rest.len() implies
                (symbol_valid(#[trigger] rest[k], (n + 3) as nat) && generator_index(rest[k]) >= 2)
            by { assert(rest[k] == w[k + 1]); }
        }
        let gidx = generator_index(s);
        assert(gi[gidx as int] == empty_word()) by { assert(2 <= gidx < n + 3); }
        assert(apply_embedding_symbol(gi, s) =~= empty_word()) by {
            match s {
                Symbol::Gen(i) => { assert(i == gidx); },
                Symbol::Inv(i) => { assert(i == gidx); crate::word::lemma_inverse_empty(); },
            }
        }
        lemma_kill_db_emb_kills_high(n, rest);
        assert(apply_embedding(gi, w)
            =~= concat(apply_embedding_symbol(gi, s), apply_embedding(gi, rest)));
    }
}

/// **`kill_db(pa_rhs(β)) = config(β,0)`**: the config part (over `{t,x}`) survives, the `w_c(β)·d`
/// part (b/d-block, gens ≥ 2) is killed to `ε`.
pub proof fn lemma_kill_db_on_pa_rhs(n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
    ensures
        apply_hom(kill_db(n), pa_rhs(n, m, beta)) =~= config_word(beta, 0),
{
    let h = kill_db(n);
    let gi = h.generator_images;
    let cfg = config_word(beta, 0);
    let wc = w_c(pa_b_base(), n, m, beta);
    let g2: Word = seq![Symbol::Gen(2)];
    assert(pa_rhs(n, m, beta) == (cfg + wc) + g2);
    lemma_apply_hom_eq_embedding(h, pa_rhs(n, m, beta));        // apply_hom = apply_embedding(gi, ·)
    lemma_apply_embedding_concat(gi, cfg + wc, g2);
    lemma_apply_embedding_concat(gi, cfg, wc);

    // apply_embedding(gi, cfg) =~= cfg.
    lemma_apply_hom_eq_embedding(h, cfg);
    lemma_config_word_valid2(beta);
    lemma_kill_db_fixes_low(n, cfg);
    assert(apply_embedding(gi, cfg) =~= cfg);

    // apply_embedding(gi, wc) =~= ε  (wc gens in [3, n+3) ⊆ [2, n+3)).
    lemma_w_c_gens_in_block(pa_b_base(), n, m, beta);
    lemma_w_c_valid(pa_b_base(), n, m, beta, (n + 3) as nat);   // 3 + n ≤ n + 3
    assert forall|j: int| 0 <= j < wc.len() implies generator_index(#[trigger] wc[j]) >= 2 by {
        assert(pa_b_base() <= generator_index(wc[j]) < pa_b_base() + n);
    }
    lemma_kill_db_emb_kills_high(n, wc);

    // apply_embedding(gi, g2) = gi[2] = ε.
    reveal_with_fuel(apply_embedding, 2);
    lemma_concat_empty_right(gi[2]);
    assert(apply_embedding(gi, g2) =~= gi[2]);
    assert(gi[2] == empty_word());

    // assemble: (cfg + ε) + ε =~= cfg.
    lemma_concat_empty_right(cfg);
    assert(apply_embedding(gi, cfg + wc) =~= cfg);
    lemma_concat_empty_right(apply_embedding(gi, cfg + wc));
}

/// **`kill_db ∘ pa_rhs_emb = config_emb`** — column-wise.  So `apply_hom(kill_db, emb(pa_rhs_emb, v))
/// = emb(config_emb(bet), v)`: the `kill_db` projection sends the b-column embedding to the a-column.
pub proof fn lemma_kill_db_on_pa_rhs_emb(n: nat, m: nat, bet: Seq<nat>)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
    ensures
        comp_images(kill_db(n), pa_rhs_emb(n, m, bet)) =~= config_emb(bet),
{
    let h = kill_db(n);
    let pre = pa_rhs_emb(n, m, bet);
    assert(comp_images(h, pre).len() == pre.len());
    assert(pre.len() == bet.len());
    assert(config_emb(bet).len() == bet.len());
    assert forall|i: int| 0 <= i < bet.len() implies comp_images(h, pre)[i] =~= config_emb(bet)[i] by {
        assert(comp_images(h, pre)[i] == apply_hom(h, pre[i]));
        assert(pre[i] == pa_rhs(n, m, bet[i]));
        lemma_kill_db_on_pa_rhs(n, m, bet[i]);
        assert(config_emb(bet)[i] == config_word(bet[i], 0));
    }
}

// ----------------------------------------------------------------------------
// The generic free-family subgroup transfer (config basis → pa_rhs basis on the same indices).
// ----------------------------------------------------------------------------

/// **Free-family subgroup transfer**: if `fam1` is a free family and a `fam1`-product
/// `emb(fam1, v)` lies in the sub-subgroup `⟨compose(fam1, sel)⟩`, then the corresponding
/// `fam2`-product lies in `⟨compose(fam2, sel)⟩` — for ANY (valid-image) `fam2` of the same length.
/// `fam1` free ⟹ (intersection property) `v ∈ ⟨sel⟩` in the abstract free group ⟹ push `v` forward
/// under `fam2` (relator-free source ⟹ embedding respects `≡`).  Used to carry the σ-restriction
/// proven on the `config_emb` basis over to the `pa_rhs_emb` basis (same index set).
pub proof fn lemma_free_family_subgroup_transfer(
    gp: crate::presentation::Presentation, fam1: Seq<Word>, fam2: Seq<Word>, sel: Seq<Word>, v: Word)
    requires
        presentation_valid(gp),
        is_free_family(gp, fam1),
        fam1.len() == fam2.len(),
        forall|i: int| 0 <= i < fam2.len() ==> word_valid(#[trigger] fam2[i], gp.num_generators),
        word_valid(v, fam1.len()),
        forall|k: int| 0 <= k < sel.len() ==> word_valid(#[trigger] sel[k], fam1.len()),
        in_generated_subgroup(gp, compose_embeddings(fam1, sel), apply_embedding(fam1, v)),
    ensures
        in_generated_subgroup(gp, compose_embeddings(fam2, sel), apply_embedding(fam2, v)),
{
    let k = fam1.len();
    let fgK = free_group(k);
    lemma_free_group_valid(k);
    // (1) v ∈ ⟨sel⟩ in free(K).
    lemma_intersection_property(gp, fam1, sel, v);
    assert(in_generated_subgroup(fgK, sel, v));
    // (2) z over sel.len() with emb(sel, z) ≡_{free(K)} v.
    lemma_subgroup_to_k_word(fgK, sel, v);
    let z = choose|z: Word| word_valid(z, sel.len())
        && equiv_in_presentation(fgK, apply_embedding(sel, z), v);
    assert(word_valid(z, sel.len())
        && equiv_in_presentation(fgK, apply_embedding(sel, z), v));
    // (3) emb(fam2, emb(sel,z)) ≡_gp emb(fam2, v)  (free(K) relator-free ⟹ embedding respects ≡).
    assert(fgK.num_generators == k);
    assert(word_valid(apply_embedding(sel, z), k)) by {
        lemma_apply_embedding_valid(sel, z, k);
    }
    assert(fgK.relators.len() == 0);
    lemma_emb_respects_source_equiv(fgK, gp, fam2, apply_embedding(sel, z), v);
    // (4) emb(fam2, emb(sel,z)) = emb(compose(fam2,sel), z) ∈ ⟨compose(fam2,sel)⟩.
    lemma_apply_embedding_compose(fam2, sel, z);
    assert(apply_embedding(fam2, apply_embedding(sel, z))
        =~= apply_embedding(compose_embeddings(fam2, sel), z));
    assert(compose_embeddings(fam2, sel).len() == sel.len());
    lemma_apply_embedding_in_subgroup(gp, compose_embeddings(fam2, sel), z);
    // (5) respects_equiv pulls emb(fam2, v) into the subgroup.
    lemma_in_subgroup_respects_equiv(gp, compose_embeddings(fam2, sel),
        apply_embedding(compose_embeddings(fam2, sel), z), apply_embedding(fam2, v));
}

// ----------------------------------------------------------------------------
// `config_emb` is a free family in the FREE group `free(n+3)` (= the `g_m` freeness lifted: a
// `free(n+3)`-equivalence is freely-equivalent, hence holds in `g_m`, where config freeness closes).
// ----------------------------------------------------------------------------

/// **`config_emb(bet)` is free in `free(n+3)`** (for distinct `bet`).  A `free(n+3)`-trivial
/// config-product is freely-equivalent to `ε` (free base, no relators), hence trivial in `g_m` (the
/// config words are valid over `g_m`'s generators), where `lemma_config_emb_free` closes it.
pub proof fn lemma_config_emb_free_in_free(mm: ModMachine, n: nat, bet: Seq<nat>)
    requires
        mod_machine_wf(mm),
        bet.no_duplicates(),
    ensures
        is_free_family(free_group((n + 3) as nat), config_emb(bet)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                 // nk ≥ 4
    lemma_g_m_valid(mm);
    let fg = free_group((n + 3) as nat);
    let ce = config_emb(bet);
    lemma_free_group_valid((n + 3) as nat);
    assert(nk >= 3);
    // images valid over n+3.
    assert forall|i: int| 0 <= i < ce.len() implies word_valid(#[trigger] ce[i], (n + 3) as nat) by {
        assert(ce[i] == config_word(bet[i], 0));
        lemma_config_word_valid(bet[i], 0);
        lemma_word_valid_mono(config_word(bet[i], 0), 3, (n + 3) as nat);
    }
    // freeness implication.
    assert forall|w: Word| (#[trigger] word_valid(w, ce.len())
        && equiv_in_presentation(fg, apply_embedding(ce, w), empty_word()))
        implies equiv_in_presentation(free_group(ce.len()), w, empty_word()) by {
        lemma_no_relator_equiv_implies_freely_equivalent(fg, apply_embedding(ce, w), empty_word());
        assert forall|i: int| 0 <= i < ce.len() implies word_valid(#[trigger] ce[i], nk) by {
            assert(ce[i] == config_word(bet[i], 0));
            lemma_config_word_valid(bet[i], 0);
            lemma_word_valid_mono(config_word(bet[i], 0), 3, nk);
        }
        lemma_apply_embedding_valid(ce, w, nk);
        lemma_freely_equivalent_implies_equiv(g_m(mm), apply_embedding(ce, w), empty_word());
        assert(ce.len() == bet.len());
        lemma_config_emb_free(mm, bet, w);
    }
}

// ----------------------------------------------------------------------------
// The σ-selector — `sel[k] = [Gen(p_k)]` with `bet[p_k] = σbet[k]` (forward-saturation).
// ----------------------------------------------------------------------------

/// **σ-forward-saturation**: every `σ(β) = m·β+l` for `β ∈ bet` is itself in `bet` (the dual of
/// `sigma_backsat`; makes the σ-shifted index set a sub-index-set of `bet`).
pub open spec fn sigma_fwdsat(bet: Seq<nat>, m: nat, l: nat) -> bool {
    forall|k: int| 0 <= k < bet.len() ==> bet.contains(#[trigger] sigma_betas(bet, m, l)[k])
}

/// A `bet`-position whose value is `val` (when one exists).
spec fn bet_pos(bet: Seq<nat>, val: nat) -> int {
    choose|p: int| 0 <= p < bet.len() && bet[p] == val
}

/// The selector `sel[k] = [Gen(p_k)]`, `bet[p_k] = σbet[k]` — picks, for each σ-shifted index, a
/// `bet`-position holding that value.  `compose(fam, sel)` is then `fam` restricted to those positions.
spec fn sigma_selector(bet: Seq<nat>, m: nat, l: nat) -> Seq<Word> {
    Seq::new(bet.len(), |k: int| seq![Symbol::Gen(bet_pos(bet, sigma_betas(bet, m, l)[k]) as nat)])
}

/// Under forward-saturation, `bet_pos(bet, σbet[k])` is a valid position holding value `σbet[k]`.
proof fn lemma_bet_pos(bet: Seq<nat>, m: nat, l: nat, k: int)
    requires
        0 <= k < bet.len(),
        bet.contains(sigma_betas(bet, m, l)[k]),
    ensures
        0 <= bet_pos(bet, sigma_betas(bet, m, l)[k]) < bet.len(),
        bet[bet_pos(bet, sigma_betas(bet, m, l)[k])] == sigma_betas(bet, m, l)[k],
{
    let val = sigma_betas(bet, m, l)[k];
    assert(exists|p: int| 0 <= p < bet.len() && bet[p] == val) by {
        assert(bet.contains(val));
    }
}

/// `compose(config_emb(bet), σ-selector) = config_emb(σbet)` — selecting the `σbet[k]`-valued
/// config generator from `config_emb(bet)`.
proof fn lemma_compose_config_sigma_selector(bet: Seq<nat>, m: nat, l: nat)
    requires
        sigma_fwdsat(bet, m, l),
    ensures
        compose_embeddings(config_emb(bet), sigma_selector(bet, m, l))
            =~= config_emb(sigma_betas(bet, m, l)),
{
    let sel = sigma_selector(bet, m, l);
    let sbet = sigma_betas(bet, m, l);
    let ce = config_emb(bet);
    let comp = compose_embeddings(ce, sel);
    assert(comp.len() == bet.len() && config_emb(sbet).len() == bet.len());
    assert forall|k: int| 0 <= k < bet.len() implies comp[k] =~= config_emb(sbet)[k] by {
        lemma_bet_pos(bet, m, l, k);
        let p = bet_pos(bet, sbet[k]);
        assert(sel[k] == seq![Symbol::Gen(p as nat)]);
        assert(comp[k] == apply_embedding(ce, sel[k]));
        reveal_with_fuel(apply_embedding, 2);
        lemma_concat_empty_right(ce[p]);
        assert(apply_embedding(ce, seq![Symbol::Gen(p as nat)]) =~= ce[p]);
        assert(ce[p] == config_word(bet[p], 0));
        assert(bet[p] == sbet[k]);
        assert(config_emb(sbet)[k] == config_word(sbet[k], 0));
    }
}

/// `compose(pa_rhs_emb(bet), σ-selector) = pa_rhs_emb(σbet)` — the b-column mirror.
proof fn lemma_compose_pa_rhs_sigma_selector(n: nat, m: nat, l: nat, bet: Seq<nat>)
    requires
        sigma_fwdsat(bet, m, l),
    ensures
        compose_embeddings(pa_rhs_emb(n, m, bet), sigma_selector(bet, m, l))
            =~= pa_rhs_emb(n, m, sigma_betas(bet, m, l)),
{
    let sel = sigma_selector(bet, m, l);
    let sbet = sigma_betas(bet, m, l);
    let pr = pa_rhs_emb(n, m, bet);
    let comp = compose_embeddings(pr, sel);
    assert(comp.len() == bet.len() && pa_rhs_emb(n, m, sbet).len() == bet.len());
    assert forall|k: int| 0 <= k < bet.len() implies comp[k] =~= pa_rhs_emb(n, m, sbet)[k] by {
        lemma_bet_pos(bet, m, l, k);
        let p = bet_pos(bet, sbet[k]);
        assert(sel[k] == seq![Symbol::Gen(p as nat)]);
        assert(comp[k] == apply_embedding(pr, sel[k]));
        reveal_with_fuel(apply_embedding, 2);
        lemma_concat_empty_right(pr[p]);
        assert(apply_embedding(pr, seq![Symbol::Gen(p as nat)]) =~= pr[p]);
        assert(pr[p] == pa_rhs(n, m, bet[p]));
        assert(bet[p] == sbet[k]);
        assert(pa_rhs_emb(n, m, sbet)[k] == pa_rhs(n, m, sbet[k]));
    }
}

/// `pa_rhs(β)` is valid over `n+3` (config over `{0,1}`, `w_c` over `[3,n+3)`, `d = Gen2 < n+3`).
proof fn lemma_pa_rhs_valid_n3(n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
    ensures
        word_valid(pa_rhs(n, m, beta), (n + 3) as nat),
{
    let ng = (n + 3) as nat;
    lemma_config_word_valid(beta, 0);
    lemma_word_valid_mono(config_word(beta, 0), 3, ng);
    lemma_w_c_valid(pa_b_base(), n, m, beta, ng);
    lemma_single_gen_valid(2, ng);
    lemma_concat_word_valid(config_word(beta, 0), w_c(pa_b_base(), n, m, beta), ng);
    lemma_concat_word_valid(config_word(beta, 0) + w_c(pa_b_base(), n, m, beta),
        seq![Symbol::Gen(2)], ng);
    assert(pa_rhs(n, m, beta) =~= (config_word(beta, 0) + w_c(pa_b_base(), n, m, beta))
        + seq![Symbol::Gen(2)]);
}

// ----------------------------------------------------------------------------
// (R')_b — the b-side config-reflection.
// ----------------------------------------------------------------------------

/// **(R')_b — the b-side (R')**: under σ-saturation (both directions), a `φ_F`-image in the b-column
/// subgroup `⟨pa_rhs_emb(bet)⟩` actually lies in the σ-shifted `⟨pa_rhs_emb(σbet)⟩`.  Route: project
/// through `kill_db` (`pa_rhs ↦ config`) to land an `emb(φ',u) ∈ ⟨config_emb(bet)⟩`, apply the a-side
/// coordinate core (`lemma_phi_prime_in_sigma_config`), then transfer the σ-restriction from the
/// `config_emb` basis to the `pa_rhs_emb` basis (`lemma_free_family_subgroup_transfer`, both free
/// over `bet`).
pub proof fn lemma_r_prime_b(mm: ModMachine, n: nat, m: nat, l: nat, u: Word, bet: Seq<nat>)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        word_valid(u, (n + 3) as nat),
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        in_generated_subgroup(free_group((n + 3) as nat), pa_rhs_emb(n, m, bet),
            apply_embedding(phi_F_family(n, m, l), u)),
        sigma_backsat(bet, m, l),
        sigma_fwdsat(bet, m, l),
    ensures
        in_generated_subgroup(free_group((n + 3) as nat),
            pa_rhs_emb(n, m, sigma_betas(bet, m, l)), apply_embedding(phi_F_family(n, m, l), u)),
{
    let fg = free_group((n + 3) as nat);
    let g = apply_embedding(phi_F_family(n, m, l), u);
    let pp_u = apply_embedding(phi_prime(n, m, l), u);
    let pr = pa_rhs_emb(n, m, bet);
    let ce = config_emb(bet);
    let sel = sigma_selector(bet, m, l);
    let sbet = sigma_betas(bet, m, l);
    let h = kill_db(n);
    lemma_free_group_valid((n + 3) as nat);
    lemma_kill_db_valid(n);
    lemma_phi_F_emb_valid(n, m, l, u);                     // word_valid(g, n+3)

    // pa_rhs / config columns valid over n+3; pp_u valid over n+3.
    assert forall|i: int| 0 <= i < pr.len() implies word_valid(#[trigger] pr[i], (n + 3) as nat) by {
        assert(pr[i] == pa_rhs(n, m, bet[i]));
        lemma_pa_rhs_valid_n3(n, m, bet[i]);
    }
    assert forall|i: int| 0 <= i < ce.len() implies word_valid(#[trigger] ce[i], (n + 3) as nat) by {
        assert(ce[i] == config_word(bet[i], 0));
        lemma_config_word_valid(bet[i], 0);
        lemma_word_valid_mono(config_word(bet[i], 0), 3, (n + 3) as nat);
    }
    crate::r_prime::lemma_phi_prime_emb_valid(n, m, l, u);   // word_valid(pp_u, n+3)

    // (1) v over bet.len() with emb(pr, v) ≡_fg g.
    lemma_subgroup_to_k_word(fg, pr, g);
    let v = choose|v: Word| word_valid(v, pr.len())
        && equiv_in_presentation(fg, apply_embedding(pr, v), g);
    assert(word_valid(v, pr.len()) && equiv_in_presentation(fg, apply_embedding(pr, v), g));
    assert(pr.len() == bet.len());
    assert(word_valid(v, ce.len()));
    lemma_apply_embedding_valid(ce, v, (n + 3) as nat);     // word_valid(emb(ce,v), n+3)

    // (2) kill_db:  emb(config_emb(bet), v) ≡_fg emb(φ', u).
    lemma_apply_hom_embedding_compose(h, pr, v);           // apply_hom(h, emb(pr,v)) = emb(comp,v)
    lemma_kill_db_on_pa_rhs_emb(n, m, bet);                // comp_images(h, pr) =~= config_emb(bet)
    assert(apply_hom(h, apply_embedding(pr, v)) =~= apply_embedding(ce, v));
    lemma_kill_db_on_phi_F(n, m, l, u);                    // apply_hom(h, g) =~= pp_u
    lemma_hom_preserves_equiv(h, apply_embedding(pr, v), g);
    assert(equiv_in_presentation(fg, apply_embedding(ce, v), pp_u));

    // (3) emb(φ', u) ∈ ⟨config_emb(bet)⟩.
    lemma_apply_embedding_in_subgroup(fg, ce, v);
    lemma_in_subgroup_respects_equiv(fg, ce, apply_embedding(ce, v), pp_u);

    // (4) a-side coordinate core ⟹ emb(φ', u) ∈ ⟨config_emb(σbet)⟩.
    lemma_phi_prime_in_sigma_config(n, m, l, u, bet);
    // ⟹ emb(config_emb(bet), v) ∈ ⟨config_emb(σbet)⟩.
    lemma_equiv_symmetric(fg, apply_embedding(ce, v), pp_u);
    lemma_in_subgroup_respects_equiv(fg, config_emb(sbet), pp_u, apply_embedding(ce, v));
    lemma_compose_config_sigma_selector(bet, m, l);        // compose(ce, sel) = config_emb(σbet)
    assert(compose_embeddings(ce, sel) == config_emb(sbet));
    assert(in_generated_subgroup(fg, compose_embeddings(ce, sel), apply_embedding(ce, v)));

    // (5) free-family transfer ⟹ emb(pa_rhs_emb(bet), v) ∈ ⟨compose(pr, sel)⟩ = ⟨pa_rhs_emb(σbet)⟩.
    lemma_config_emb_free_in_free(mm, n, bet);             // is_free_family(fg, ce)
    assert(ce.len() == pr.len());
    assert forall|k: int| 0 <= k < sel.len() implies word_valid(#[trigger] sel[k], ce.len()) by {
        assert(bet.contains(sbet[k]));                     // from sigma_fwdsat
        lemma_bet_pos(bet, m, l, k);
        assert(sel[k] == seq![Symbol::Gen(bet_pos(bet, sbet[k]) as nat)]);
        assert(bet_pos(bet, sbet[k]) < bet.len());
    }
    lemma_free_family_subgroup_transfer(fg, ce, pr, sel, v);
    lemma_compose_pa_rhs_sigma_selector(n, m, l, bet);     // compose(pr, sel) = pa_rhs_emb(σbet)
    assert(compose_embeddings(pr, sel) == pa_rhs_emb(n, m, sbet));

    // (6) g ≡ emb(pr, v) ⟹ g ∈ ⟨pa_rhs_emb(σbet)⟩.
    lemma_in_subgroup_respects_equiv(fg, pa_rhs_emb(n, m, sbet), apply_embedding(pr, v), g);
}

// ----------------------------------------------------------------------------
// (R)_b — the b-side reflection (R)⟸(R')_b via the generic intersection property.
// ----------------------------------------------------------------------------

/// **`φ_F` fixes `w_c(3,n,m,β)`** — its symbols all live in the F-b-block `[3, n+3)`, where
/// `phi_F_family` maps every generator to itself (the identity tail `[Gen(g)]`).
proof fn lemma_phi_F_fixes_w_c(n: nat, m: nat, l: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
        1 <= l <= 2 * n,
    ensures
        apply_embedding(phi_F_family(n, m, l), w_c(pa_b_base(), n, m, beta))
            =~= w_c(pa_b_base(), n, m, beta),
{
    let pf = phi_F_family(n, m, l);
    let wc = w_c(pa_b_base(), n, m, beta);
    assert(pf.len() == n + 3);
    let tail = Seq::new(n, |j: int| seq![Symbol::Gen((3 + j) as nat)]);
    lemma_w_c_gens_in_block(pa_b_base(), n, m, beta);
    assert forall|i: int| 0 <= i < wc.len()
        implies apply_embedding_symbol(pf, #[trigger] wc[i]) =~= seq![wc[i]] by {
        let g = generator_index(wc[i]);
        assert(pa_b_base() <= g < pa_b_base() + n);                 // 3 ≤ g < n+3
        // pf[g] = tail[g-3] = [Gen(g)].
        assert(pf[g as int] == tail[g - 3]) by { assert(g >= 3); }
        assert(tail[g - 3] == seq![Symbol::Gen((3 + (g - 3)) as nat)]);
        assert(pf[g as int] == seq![Symbol::Gen(g)]);
        match wc[i] {
            Symbol::Gen(gg) => { assert(gg == g); },
            Symbol::Inv(gg) => { assert(gg == g); reveal_with_fuel(inverse_word, 2); },
        }
    }
    lemma_apply_embedding_fixes(pf, wc);
}

/// **`φ_F(pa_rhs(β)) = pa_rhs(σβ)`** — the F-level family-(II) payoff (= `lemma_phi_l_on_family_II_rhs`
/// at the `P_A`/`F` level).  `φ_F` scales the config part (`config(β,0)↦config(σβ,0)`), fixes
/// `w_β(b)` (b-block), and `d↦b_l·d`; the numbering snoc `w_{σβ}(b) = w_β(b)·b_l` then aligns the
/// image with `pa_rhs(σβ)`.
pub proof fn lemma_phi_F_on_pa_rhs(mm: ModMachine, n: nat, m: nat, l: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
        1 <= l <= 2 * n,
    ensures
        apply_embedding(phi_F_family(n, m, l), pa_rhs(n, m, beta))
            =~= pa_rhs(n, m, (m * beta + l) as nat),
{
    let pf = phi_F_family(n, m, l);
    let bb = pa_b_base();                                  // 3
    let cfg = config_word(beta, 0);
    let wc = w_c(bb, n, m, beta);
    let dw: Word = seq![Symbol::Gen(2)];
    let bl = alphabet_letter(bb, n, l);

    // pa_rhs(β) = (cfg + wc) + [Gen2]; distribute.
    assert(pa_rhs(n, m, beta) == (cfg + wc) + dw);
    lemma_apply_embedding_concat(pf, cfg + wc, dw);
    lemma_apply_embedding_concat(pf, cfg, wc);

    // The three φ_F images.
    lemma_phi_F_on_config(mm, n, m, l, beta);             // φ_F(cfg) =~= config(mβ+l, 0)
    lemma_phi_F_fixes_w_c(n, m, l, beta);                 // φ_F(wc) =~= wc
    reveal_with_fuel(apply_embedding, 2);
    lemma_concat_empty_right(pf[2]);
    assert(apply_embedding(pf, dw) =~= pf[2]);            // φ_F(d) = pf[2] = [bl, Gen2]
    assert(pf[2] == seq![bl, Symbol::Gen(2)]);

    let cfg2 = config_word((m * beta + l) as nat, 0);
    assert(apply_embedding(pf, pa_rhs(n, m, beta)) =~= (cfg2 + wc) + seq![bl, Symbol::Gen(2)]);

    // Target side: w_{σβ}(b) = w_β(b)·b_l  (numbering snoc).  snoc yields β·m+l; bridge to m·β+l.
    lemma_w_b_snoc(bb, n, m, beta, l);
    assert(beta * m + l == m * beta + l) by (nonlinear_arith);
    let bl_seq = Seq::new(1, |_k: int| alphabet_letter(bb, n, l));
    assert(w_b(bb, n, m, (m * beta + l) as nat) =~= wc + bl_seq) by {
        assert(w_b(bb, n, m, beta) == wc);                // w_b := w_c
    }
    assert(bl_seq =~= seq![bl]);
    assert(pa_rhs(n, m, (m * beta + l) as nat)
        == (cfg2 + w_c(bb, n, m, (m * beta + l) as nat)) + dw);
    assert(w_c(bb, n, m, (m * beta + l) as nat) == w_b(bb, n, m, (m * beta + l) as nat));
    assert(seq![bl, Symbol::Gen(2)] =~= seq![bl] + dw);
}

/// `compose(φ_F, pa_rhs_emb(bet)) = pa_rhs_emb(σbet)` — the b-column σ-shift (mirror of
/// `lemma_compose_phi_F_config_emb`).  The recog-vs-pa relation `ψ = φ_F` at the b-column.
pub proof fn lemma_compose_phi_F_pa_rhs_emb(mm: ModMachine, n: nat, m: nat, l: nat, bet: Seq<nat>)
    requires
        2 * n < m,
        1 <= l <= 2 * n,
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
    ensures
        compose_embeddings(phi_F_family(n, m, l), pa_rhs_emb(n, m, bet))
            =~= pa_rhs_emb(n, m, sigma_betas(bet, m, l)),
{
    let pf = phi_F_family(n, m, l);
    let pr = pa_rhs_emb(n, m, bet);
    let sb = sigma_betas(bet, m, l);
    let comp = compose_embeddings(pf, pr);
    assert(comp.len() == bet.len() && pa_rhs_emb(n, m, sb).len() == bet.len());
    assert forall|i: int| 0 <= i < bet.len() implies comp[i] =~= pa_rhs_emb(n, m, sb)[i] by {
        assert(comp[i] == apply_embedding(pf, pr[i]));
        assert(pr[i] == pa_rhs(n, m, bet[i]));
        lemma_phi_F_on_pa_rhs(mm, n, m, l, bet[i]);
        assert(sb[i] == m * bet[i] + l);
        assert(pa_rhs_emb(n, m, sb)[i] == pa_rhs(n, m, sb[i]));
    }
}

/// **(R)_b — the b-side reflection**: `emb(φ_F, u) ∈ ⟨pa_rhs_emb(bet)⟩ ⟹ u ∈ ⟨pa_rhs_emb(bet)⟩`,
/// under σ-saturation (both directions).  (R')_b lifts the membership into `⟨pa_rhs_emb(σbet)⟩`, then
/// the generic intersection property (`ψ = φ_F` free, b-column `compose = pa_rhs_emb(σbet)`) reflects
/// it to `u`.  This is the b-column M2 pinch-middle consumable (mirror of `lemma_config_reflect_full`).
pub proof fn lemma_pa_rhs_reflect_full(mm: ModMachine, n: nat, m: nat, l: nat, u: Word, bet: Seq<nat>)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        word_valid(u, (n + 3) as nat),
        bet.no_duplicates(),
        forall|i: int| 0 <= i < bet.len() ==> numbers_word(n, m, #[trigger] bet[i]),
        in_generated_subgroup(free_group((n + 3) as nat), pa_rhs_emb(n, m, bet),
            apply_embedding(phi_F_family(n, m, l), u)),
        sigma_backsat(bet, m, l),
        sigma_fwdsat(bet, m, l),
    ensures
        in_generated_subgroup(free_group((n + 3) as nat), pa_rhs_emb(n, m, bet), u),
{
    let fg = free_group((n + 3) as nat);
    let pf = phi_F_family(n, m, l);
    let pr = pa_rhs_emb(n, m, bet);
    let sb = sigma_betas(bet, m, l);
    lemma_free_group_valid((n + 3) as nat);
    crate::phi_l_mapb::lemma_phi_F_family_free(n, m, l);   // is_free_family(fg, pf)
    assert(pf.len() == n + 3);

    // (R')_b: emb(φ_F, u) ∈ ⟨pa_rhs_emb(σbet)⟩.
    lemma_r_prime_b(mm, n, m, l, u, bet);

    // pa_rhs_emb(bet) columns valid over pf.len() = n+3.
    assert forall|k: int| 0 <= k < pr.len() implies word_valid(#[trigger] pr[k], pf.len()) by {
        assert(pr[k] == pa_rhs(n, m, bet[k]));
        lemma_pa_rhs_valid_n3(n, m, bet[k]);
    }
    // compose(φ_F, pa_rhs_emb(bet)) = pa_rhs_emb(σbet), so (R')_b IS the intersection hypothesis.
    lemma_compose_phi_F_pa_rhs_emb(mm, n, m, l, bet);
    assert(compose_embeddings(pf, pr) == pa_rhs_emb(n, m, sb));
    lemma_intersection_property(fg, pf, pr, u);
}

} // verus!
