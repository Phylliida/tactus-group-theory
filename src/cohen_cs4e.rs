// Layer 2 — Cohen §1 assembly, brick CS-4e: the a_i association iso up the predicate H₃ tower.
//
// `docs/cohen-cs4-architecture.md` §4 (CS-4e). CS-4c/CS-4d proved the a_i iso `(★)` over the BASE
// `h2_pred`:  `emb(a_col, w) ≡_{h2_pred} ε  ⟺  emb(b_col, w) ≡_{h2_pred} ε`.  The actual CS-4 target
// is the iso of each tower level `l`:
//
//   hnn_pred_associations_isomorphic(PredHNNData{ base: h3_pred_upto(l-1), associations: phi_assoc(l) })
//   = ∀w. emb(a_col, w) ≡_{h3_pred_upto(l-1)} ε  ⟺  emb(b_col, w) ≡_{h3_pred_upto(l-1)} ε
//
// `a_col`/`b_col` are words over the h2-generators (the stated gens `t,x,d,b_j,p` and their φ_l
// images), so they are BASE WORDS of the tower.  By BASE-FAITHFULNESS — a word over the h2-gens is
// trivial in `h3_pred_upto(k)` iff in `h2_pred` — the level-`l` iso reduces to `(★)` over `h2_pred`.
// Base-faithfulness is a downward induction on the tower:
//   * ⟸ (base ⟹ tower):  `lemma_base_embeds_in_pred_hnn` — UNCONDITIONAL (base derivation lifts);
//   * ⟹ (tower ⟹ base):  `britton_lemma_unconditional` — needs the level iso (the IH).
// So the isos and base-faithfulness close together by induction on `l`: assuming isos at levels
// `< l`, base-faithfulness peels levels `l-1 … 1` down to `h2_pred`, where `(★)` decides the iff,
// giving the level-`l` iso.  Additive (new module + one lib.rs line); no regression.

use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::pred_presentation::{equiv_in_pred_presentation, pred_presentation_valid};
use crate::pred_hnn::{PredHNNData, hnn_pred_presentation, hnn_pred_associations_isomorphic,
    hnn_pred_data_valid, lemma_base_embeds_in_pred_hnn};
use crate::pred_britton_via_tower::britton_lemma_unconditional;
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, lemma_g_m_num_generators};
use crate::layout::h2_num_gens;
use crate::h3::{phi_assoc, lemma_phi_assoc_valid};
use crate::cohen_h2::{h2_pred, s_relators_valid};
use crate::cohen_h3::{h3_pred_upto, lemma_h3_pred_upto_num_generators, lemma_h3_pred_upto_valid,
    lemma_h3_pred_level_data_valid};
use crate::benign::{apply_embedding, lemma_apply_embedding_valid};
use crate::phi_l_maps::{a_words, lemma_a_words_is_phi_col0};
use crate::phi_l_lift::b_words;
use crate::phi_l_pinch::lemma_a_words_img_valid;
use crate::h3_ii::lemma_phi_assoc_len;
use crate::cohen_cs4c::{lemma_cs4c_forward, lemma_cs4d_backward};

verus! {

/// The single-letter a_i HNN datum at level `l` (base `h3_pred_upto(l-1)`, associations `phi_assoc(l)`).
pub open spec fn cs4_data(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat)
    -> PredHNNData
{
    PredHNNData {
        base: h3_pred_upto(mm, n, m, is_S, (l - 1) as nat),
        associations: phi_assoc(g_m(mm).num_generators, n, m, l),
    }
}

/// `cs4_levels_iso(mm,n,m,is_S,k)` — the a_i iso holds at every tower level `1 ≤ l ≤ k`.
pub open spec fn cs4_levels_iso(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, k: nat)
    -> bool
{
    forall|l: nat| 1 <= l <= k ==> hnn_pred_associations_isomorphic(cs4_data(mm, n, m, is_S, l))
}

// ============================================================================
// Base-faithfulness: a word over the h2-gens is trivial in `h3_pred_upto(k)` iff in `h2_pred`.
// ============================================================================

/// **Base-faithfulness up the a_i tower.** Given the a_i isos at levels `1 ≤ l ≤ k`, a word `u` over
/// the h2-generators is trivial in `h3_pred_upto(k)` iff in `h2_pred`.  Downward induction: the ⟸
/// half lifts a base derivation (`lemma_base_embeds_in_pred_hnn`, unconditional); the ⟹ half peels the
/// top a_k via `britton_lemma_unconditional` (needs the level-`k` iso) and recurses.
pub proof fn lemma_h3_pred_upto_base_faithful(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, k: nat, u: Word,
)
    requires
        2 * n < m,
        k <= 2 * n,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        word_valid(u, h2_num_gens(g_m(mm).num_generators, n)),
        cs4_levels_iso(mm, n, m, is_S, k),
    ensures
        equiv_in_pred_presentation(h3_pred_upto(mm, n, m, is_S, k), u, empty_word())
            <==> equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), u, empty_word()),
    decreases k,
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    if k == 0 {
        // h3_pred_upto(0) == h2_pred — the iff is reflexive.
        assert(h3_pred_upto(mm, n, m, is_S, 0) == h2_pred(mm, n, m, is_S));
    } else {
        let base = h3_pred_upto(mm, n, m, is_S, (k - 1) as nat);
        let data = cs4_data(mm, n, m, is_S, k);
        assert(data.base == base);
        assert(h3_pred_upto(mm, n, m, is_S, k) == hnn_pred_presentation(data));

        // u valid over base.num_generators (≥ h2_num_gens).
        lemma_h3_pred_upto_num_generators(mm, n, m, is_S, (k - 1) as nat);
        assert(base.num_generators == h2_num_gens(nk, n) + (k - 1));
        assert(word_valid(u, base.num_generators)) by {
            assert forall|t: int| 0 <= t < u.len()
                implies symbol_valid(#[trigger] u[t], base.num_generators) by {
                assert(symbol_valid(u[t], h2_num_gens(nk, n)));
            }
        }

        // IH base-faithfulness at k-1.
        lemma_h3_pred_upto_base_faithful(mm, n, m, is_S, (k - 1) as nat, u);

        // ⟸ : trivial in h2_pred ⟹ trivial in h3_pred_upto(k).
        assert(equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), u, empty_word())
            ==> equiv_in_pred_presentation(h3_pred_upto(mm, n, m, is_S, k), u, empty_word())) by {
            if equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), u, empty_word()) {
                assert(equiv_in_pred_presentation(base, u, empty_word()));   // IH
                lemma_base_embeds_in_pred_hnn(data, u, empty_word());
            }
        }

        // ⟹ : trivial in h3_pred_upto(k) ⟹ trivial in h2_pred (peel a_k via britton, then IH).
        assert(equiv_in_pred_presentation(h3_pred_upto(mm, n, m, is_S, k), u, empty_word())
            ==> equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), u, empty_word())) by {
            if equiv_in_pred_presentation(h3_pred_upto(mm, n, m, is_S, k), u, empty_word()) {
                assert(equiv_in_pred_presentation(hnn_pred_presentation(data), u, empty_word()));
                lemma_h3_pred_upto_valid(mm, n, m, is_S, (k - 1) as nat);    // pred_presentation_valid(base)
                lemma_h3_pred_level_data_valid(mm, n, m, is_S, k);          // hnn_pred_data_valid(data)
                assert(hnn_pred_associations_isomorphic(data));             // cs4_levels_iso at l=k
                britton_lemma_unconditional(data, u);
                assert(equiv_in_pred_presentation(base, u, empty_word()));  // IH
            }
        }
    }
}

// ============================================================================
// The a_i iso at level `L`, then the induction closing all levels.
// ============================================================================

/// The level-`L` iff for a single `w`: `emb(a_col, w) ≡_{h3_pred_upto(L-1)} ε ⟺ emb(b_col, w) ≡ ε`,
/// via base-faithfulness (`h3_pred_upto(L-1) ⟺ h2_pred`, needs the isos at levels `< L`) sandwiching
/// the `(★)` decision over `h2_pred` (CS-4c forward + CS-4d backward).
proof fn lemma_cs4e_level_iff(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, big_l: nat, w: Word,
)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        1 <= big_l <= 2 * n,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        word_valid(w, (n + 4) as nat),
        cs4_levels_iso(mm, n, m, is_S, (big_l - 1) as nat),
    ensures
        equiv_in_pred_presentation(h3_pred_upto(mm, n, m, is_S, (big_l - 1) as nat),
            apply_embedding(a_words(mm, n), w), empty_word())
        <==> equiv_in_pred_presentation(h3_pred_upto(mm, n, m, is_S, (big_l - 1) as nat),
            apply_embedding(b_words(mm, n, m, big_l), w), empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let base = h3_pred_upto(mm, n, m, is_S, (big_l - 1) as nat);
    let aw = a_words(mm, n);
    let bw = b_words(mm, n, m, big_l);
    let ea = apply_embedding(aw, w);
    let eb = apply_embedding(bw, w);
    let hp = h2_pred(mm, n, m, is_S);

    // aw / bw images valid over h2_num_gens ⟹ ea, eb valid over h2_num_gens.
    lemma_a_words_is_phi_col0(mm, n, m, big_l);                // aw.len() == n+4
    assert(aw.len() == n + 4);
    assert forall|i: int| 0 <= i < aw.len()
        implies word_valid(#[trigger] aw[i], h2_num_gens(nk, n)) by {
        lemma_a_words_img_valid(mm, n, i);
    }
    lemma_phi_assoc_len(nk, n, m, big_l);
    lemma_phi_assoc_valid(nk, n, m, big_l, h2_num_gens(nk, n));
    assert(bw.len() == n + 4);
    assert forall|i: int| 0 <= i < bw.len()
        implies word_valid(#[trigger] bw[i], h2_num_gens(nk, n)) by {
        assert(bw[i] == phi_assoc(nk, n, m, big_l)[i].1);     // fires assocs_valid
    }
    assert(word_valid(w, aw.len()) && word_valid(w, bw.len()));
    lemma_apply_embedding_valid(aw, w, h2_num_gens(nk, n));    // word_valid(ea, h2_num_gens)
    lemma_apply_embedding_valid(bw, w, h2_num_gens(nk, n));    // word_valid(eb, h2_num_gens)

    // base-faithfulness on ea and eb: base ⟺ h2_pred.
    lemma_h3_pred_upto_base_faithful(mm, n, m, is_S, (big_l - 1) as nat, ea);
    lemma_h3_pred_upto_base_faithful(mm, n, m, is_S, (big_l - 1) as nat, eb);

    // (★) over h2_pred: equiv(h2_pred, ea, ε) ⟺ equiv(h2_pred, eb, ε).
    assert(equiv_in_pred_presentation(hp, ea, empty_word())
        ==> equiv_in_pred_presentation(hp, eb, empty_word())) by {
        if equiv_in_pred_presentation(hp, ea, empty_word()) {
            lemma_cs4c_forward(mm, n, m, is_S, big_l, w);     // a ⟹ b
        }
    }
    assert(equiv_in_pred_presentation(hp, eb, empty_word())
        ==> equiv_in_pred_presentation(hp, ea, empty_word())) by {
        if equiv_in_pred_presentation(hp, eb, empty_word()) {
            lemma_cs4d_backward(mm, n, m, is_S, big_l, w);    // b ⟹ a
        }
    }
    // chain: equiv(base, ea, ε) ⟺ equiv(hp, ea, ε) ⟺ equiv(hp, eb, ε) ⟺ equiv(base, eb, ε).
}

/// **CS-4e — the a_i association iso at every tower level `1 ≤ l ≤ L`.**  Induction on `L`: the IH
/// gives the isos at levels `< L`, which power base-faithfulness `h3_pred_upto(L-1) ⟺ h2_pred`; the
/// level-`L` iff then follows from `(★)` over `h2_pred` (`lemma_cs4e_level_iff`).
pub proof fn lemma_cs4e_iso_upto(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, big_l: nat,
)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        big_l <= 2 * n,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        cs4_levels_iso(mm, n, m, is_S, big_l),
    decreases big_l,
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    if big_l >= 1 {
        lemma_cs4e_iso_upto(mm, n, m, is_S, (big_l - 1) as nat);     // isos 1..L-1
        let data = cs4_data(mm, n, m, is_S, big_l);
        let base = h3_pred_upto(mm, n, m, is_S, (big_l - 1) as nat);
        assert(data.base == base);
        lemma_phi_assoc_len(nk, n, m, big_l);
        let kk = data.associations.len();
        assert(kk == n + 4);
        let aiso = Seq::new(kk, |i: int| data.associations[i].0);
        let biso = Seq::new(kk, |i: int| data.associations[i].1);

        // aiso =~= a_words, biso =~= b_words.
        lemma_a_words_is_phi_col0(mm, n, m, big_l);
        assert(aiso =~= a_words(mm, n)) by {
            assert(data.associations == phi_assoc(nk, n, m, big_l));
        }
        assert(biso =~= b_words(mm, n, m, big_l)) by {
            assert(b_words(mm, n, m, big_l)
                == Seq::new((n + 4) as nat, |i: int| phi_assoc(nk, n, m, big_l)[i].1));
            assert(data.associations == phi_assoc(nk, n, m, big_l));
        }

        // the iso at level L: ∀w valid over kk. equiv(base, emb(aiso,w), ε) ⟺ equiv(base, emb(biso,w), ε).
        assert(hnn_pred_associations_isomorphic(data)) by {
            assert forall|w: Word| #![trigger word_valid(w, kk as nat)] word_valid(w, kk as nat) implies
                (equiv_in_pred_presentation(base, apply_embedding(aiso, w), empty_word())
                 <==> equiv_in_pred_presentation(base, apply_embedding(biso, w), empty_word())) by {
                assert(word_valid(w, (n + 4) as nat));
                lemma_cs4e_level_iff(mm, n, m, is_S, big_l, w);
                // emb(aiso,w) == emb(a_words,w), emb(biso,w) == emb(b_words,w).
                assert(apply_embedding(aiso, w) == apply_embedding(a_words(mm, n), w));
                assert(apply_embedding(biso, w) == apply_embedding(b_words(mm, n, m, big_l), w));
            }
        }

        // combine level L with levels 1..L-1 (recursive ensures).
        assert forall|l: nat| 1 <= l <= big_l
            implies hnn_pred_associations_isomorphic(cs4_data(mm, n, m, is_S, l)) by {
            if l < big_l {
                assert(cs4_levels_iso(mm, n, m, is_S, (big_l - 1) as nat));   // recursive ensures
            } else {
                assert(l == big_l);
            }
        }
    }
}

} // verus!
