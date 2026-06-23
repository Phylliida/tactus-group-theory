// Layer 2 — Brick 5, C3.2c / C3.2d: the a-tower lift of the bottom crux.
//
// The bottom crux `lemma_phi_l_iso_at_h2II` (`phi_l_mapb_fwd.rs`) gives the per-level φ_l iso at the
// BOTTOM base `h2_II`.  C3.2d lifts it up the augmented a-tower `h3_II_upto(l)`: a `decreases l`
// faithfulness induction (mirror of `lemma_b_m_upto_faithful`, `machine_group.rs`) that inline-builds
// the per-step iso at each level from the bottom crux + the IH (lower-tower faithfulness) +
// `lemma_h2II_equiv_lifts_to_tower`.  The standalone `lemma_phi_l_iso` then exposes
// `hnn_associations_isomorphic(phi_l_data(l))` at every level — the C3.2 goal.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, lemma_g_m_num_generators,
    lemma_word_valid_mono, lemma_single_hnn_base_faithful};
use crate::benign::apply_embedding;
use crate::hnn::{HNNData, hnn_presentation, hnn_associations_isomorphic, hnn_data_valid};
use crate::presentation::equiv_in_presentation;
use crate::layout::h2_num_gens;
use crate::h3::phi_assoc;
use crate::h3_ii::{h2_II, h3_II_upto, phi_l_data, lemma_phi_l_emb_h2_valid,
    lemma_h2II_equiv_lifts_to_tower, lemma_phi_l_data_valid, lemma_h3_II_upto_num_generators,
    lemma_phi_assoc_len};
use crate::phi_l_mapb_fwd::lemma_phi_l_iso_at_h2II;
use crate::r_prime::sigma_backsat;
use crate::f_free_a1::betas;
use crate::word_numbering::numbers_word;

verus! {

/// The per-level side-condition bundle for the a-tower iso: for every tower level `j ∈ [1, l]`,
/// `betas(alphas)` is σ-BACKWARD-saturated at digit `j`, AND the **finite-slice** holds — each
/// shifted index `m·γ+j` (`γ ∈ betas`) lands in `alphas`.
///
/// **⚠ VACUOUS — UNSATISFIABLE for any finite `alphas` (found 2026-06-22, confirmed w/ Danielle).**
/// The finite-slice was claimed finite-satisfiable by a "bounded σ-orbit", but it is NOT: with
/// `γ = betas[0] = 0, j = 1` it forces `1 ∈ alphas`, then `γ = 1` forces `m+1 ∈ alphas`, then
/// `m²+m+1`, … — a strictly increasing infinite chain into a finite `Seq` (proof:
/// `lemma_sigma_sat_upto_unsatisfiable`).  It is the SAME failure as the old σ-forward-saturation,
/// merely relocated.  ROOT CAUSE: the von-Dyck-backward direction needs `family_II_relator(m·β+l) ≡ ε`
/// in the base, which a finite base only has when `m·β+l ∈ alphas`; so the UNIVERSAL iso
/// (`hnn_associations_isomorphic`, ∀ww) requires σ-forward-closure of `alphas` ⟹ infinite.  A finite
/// presentation simply cannot carry the full (infinite) family (II), so the a-level associations are
/// NOT genuine universal isos over the base — only **virtual** isos (true in the group `h3_pres`,
/// false in the base presentation).  This is the SAME situation already flagged for the k-level
/// (`brick5-completeness-plan.md` §2.3, Fork B).  **C3.2 is therefore NOT done** — it must be reframed
/// to a WORD-RESTRICTED virtual iso (the R1–R4 directional machinery is reusable; only this universal
/// packaging + the `britton_lemma_full` tower lift are wrong).  See `docs/brick5-c4-plan.md` §7.
pub open spec fn sigma_sat_upto(alphas: Seq<nat>, m: nat, l: nat) -> bool {
    forall|j: nat| #![trigger sigma_backsat(betas(alphas), m, j)] 1 <= j <= l ==>
        sigma_backsat(betas(alphas), m, j)
        && (forall|jj: int| 0 <= jj < betas(alphas).len() ==>
              exists|kk: int| 0 <= kk < alphas.len()
                  && alphas[kk] == m * (#[trigger] betas(alphas)[jj]) + j)
}

/// **C3.2d — the a-tower faithfulness** (mirror of `lemma_b_m_upto_faithful`).  An `h2`-word `w`
/// (valid over `h2_num_gens`, so touching no `a_i`/`k` letter) that is trivial in the augmented
/// a-tower `h3_II_upto(l)` is trivial in the bottom `h2_II`.  `decreases l`: at level `l` build the
/// per-step iso INLINE (the embedded a/b column words are `h2`-words, descend to `h2_II` by the IH,
/// the bottom crux `lemma_phi_l_iso_at_h2II` flips a-side↔b-side, then `lemma_h2II_equiv_lifts_to_tower`
/// lifts back), discharge `hnn_data_valid`, descend one level (`lemma_single_hnn_base_faithful`), recurse.
pub proof fn lemma_h3_II_upto_faithful(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat,
    w: Word)
    requires
        mod_machine_wf(mm),
        l <= 2 * n,
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        sigma_sat_upto(alphas, m, l),
        word_valid(w, h2_num_gens(g_m(mm).num_generators, n)),
        equiv_in_presentation(h3_II_upto(mm, n, m, alphas, l), w, empty_word()),
    ensures
        equiv_in_presentation(h2_II(mm, n, m, alphas), w, empty_word()),
    decreases l,
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let hg = h2_num_gens(nk, n);
    if l == 0 {
        assert(h3_II_upto(mm, n, m, alphas, 0) == h2_II(mm, n, m, alphas));
    } else {
        let base = h3_II_upto(mm, n, m, alphas, (l - 1) as nat);
        let assoc = phi_assoc(nk, n, m, l);
        let step = HNNData { base, associations: assoc };
        assert(h3_II_upto(mm, n, m, alphas, l) == hnn_presentation(step));
        lemma_phi_assoc_len(nk, n, m, l);
        let k = assoc.len();
        assert(k == n + 4);

        // --- the per-step iso, inline, from the IH + bottom crux + lift ---
        let a_words = Seq::new(k, |idx: int| step.associations[idx].0);
        let b_words = Seq::new(k, |idx: int| step.associations[idx].1);
        assert(hnn_associations_isomorphic(step)) by {
            assert(sigma_backsat(betas(alphas), m, l));       // trigger sigma_sat_upto at j=l (backsat + finite-slice)
            lemma_phi_l_iso_at_h2II(mm, n, m, alphas, l);     // bottom crux: iso at h2_II
            let cr = HNNData { base: h2_II(mm, n, m, alphas), associations: phi_assoc(nk, n, m, l) };
            let cr_a = Seq::new(k, |idx: int| cr.associations[idx].0);
            let cr_b = Seq::new(k, |idx: int| cr.associations[idx].1);
            assert(cr_a == a_words && cr_b == b_words);
            assert forall|ww: Word| word_valid(ww, k as nat) implies (
                equiv_in_presentation(base, apply_embedding(a_words, ww), empty_word())
                <==> equiv_in_presentation(base, apply_embedding(b_words, ww), empty_word())
            ) by {
                lemma_phi_l_emb_h2_valid(nk, n, m, l, ww);     // ea, eb are h2-words
                let ea = apply_embedding(a_words, ww);
                let eb = apply_embedding(b_words, ww);
                if equiv_in_presentation(base, ea, empty_word()) {
                    lemma_h3_II_upto_faithful(mm, n, m, alphas, (l - 1) as nat, ea);  // ea ≡_{h2_II} ε
                    // bottom crux at ww: ea ≡_{h2_II} ε ⟹ eb ≡_{h2_II} ε.
                    assert(equiv_in_presentation(h2_II(mm, n, m, alphas), eb, empty_word()));
                    lemma_h2II_equiv_lifts_to_tower(mm, n, m, alphas, (l - 1) as nat, eb,
                        empty_word());
                }
                if equiv_in_presentation(base, eb, empty_word()) {
                    lemma_h3_II_upto_faithful(mm, n, m, alphas, (l - 1) as nat, eb);  // eb ≡_{h2_II} ε
                    assert(equiv_in_presentation(h2_II(mm, n, m, alphas), ea, empty_word()));
                    lemma_h2II_equiv_lifts_to_tower(mm, n, m, alphas, (l - 1) as nat, ea,
                        empty_word());
                }
            }
        }

        // --- hnn_data_valid(step) ---
        lemma_phi_l_data_valid(mm, n, m, alphas, l);          // = hnn_data_valid(phi_l_data(l)) = step
        assert(phi_l_data(mm, n, m, alphas, l) == step);
        assert(hnn_data_valid(step));

        // --- descend one level + recurse ---
        lemma_h3_II_upto_num_generators(mm, n, m, alphas, (l - 1) as nat);   // base.num = hg + (l-1)
        assert(base.num_generators == hg + (l - 1));
        lemma_word_valid_mono(w, hg, base.num_generators);
        lemma_single_hnn_base_faithful(step, w);             // w ≡_{base} ε
        lemma_h3_II_upto_faithful(mm, n, m, alphas, (l - 1) as nat, w);
    }
}

/// **C3.2d goal — the full a-level φ_l iso** `hnn_associations_isomorphic(phi_l_data(l))` at every
/// tower level `l` (base `h3_II_upto(l-1)`).  Built from the bottom crux at `h2_II` + the a-tower
/// faithfulness IH (`lemma_h3_II_upto_faithful` at `l-1`) + the lift — exactly the inline step iso of
/// the faithfulness induction, exposed standalone for the C2/C4/C5 Higman-completeness consumers.
pub proof fn lemma_phi_l_iso(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat)
    requires
        mod_machine_wf(mm),
        1 <= l <= 2 * n,
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        sigma_sat_upto(alphas, m, l),
    ensures
        hnn_associations_isomorphic(phi_l_data(mm, n, m, alphas, l)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let base = h3_II_upto(mm, n, m, alphas, (l - 1) as nat);
    let data = phi_l_data(mm, n, m, alphas, l);
    assert(data == HNNData { base, associations: phi_assoc(nk, n, m, l) });
    lemma_phi_assoc_len(nk, n, m, l);
    let k = data.associations.len();
    assert(k == n + 4);
    let a_words = Seq::new(k, |idx: int| data.associations[idx].0);
    let b_words = Seq::new(k, |idx: int| data.associations[idx].1);

    assert(sigma_backsat(betas(alphas), m, l));               // trigger sigma_sat_upto at j=l (backsat + finite-slice)
    lemma_phi_l_iso_at_h2II(mm, n, m, alphas, l);             // bottom crux: iso at h2_II
    let cr = HNNData { base: h2_II(mm, n, m, alphas), associations: phi_assoc(nk, n, m, l) };
    let cr_a = Seq::new(k, |idx: int| cr.associations[idx].0);
    let cr_b = Seq::new(k, |idx: int| cr.associations[idx].1);
    assert(cr_a == a_words && cr_b == b_words);
    assert forall|ww: Word| word_valid(ww, k as nat) implies (
        equiv_in_presentation(base, apply_embedding(a_words, ww), empty_word())
        <==> equiv_in_presentation(base, apply_embedding(b_words, ww), empty_word())
    ) by {
        lemma_phi_l_emb_h2_valid(nk, n, m, l, ww);
        let ea = apply_embedding(a_words, ww);
        let eb = apply_embedding(b_words, ww);
        if equiv_in_presentation(base, ea, empty_word()) {
            lemma_h3_II_upto_faithful(mm, n, m, alphas, (l - 1) as nat, ea);   // ea ≡_{h2_II} ε
            assert(equiv_in_presentation(h2_II(mm, n, m, alphas), eb, empty_word()));
            lemma_h2II_equiv_lifts_to_tower(mm, n, m, alphas, (l - 1) as nat, eb, empty_word());
        }
        if equiv_in_presentation(base, eb, empty_word()) {
            lemma_h3_II_upto_faithful(mm, n, m, alphas, (l - 1) as nat, eb);   // eb ≡_{h2_II} ε
            assert(equiv_in_presentation(h2_II(mm, n, m, alphas), ea, empty_word()));
            lemma_h2II_equiv_lifts_to_tower(mm, n, m, alphas, (l - 1) as nat, ea, empty_word());
        }
    }
}

} // verus!
