// Layer 2 — Brick 5 COMPLETENESS, C3.1 (`h3_ii.rs`): the finite family-(II) augmentation.
//
// The a-level associations `φ_l` are NON-iso over the literal `h3_upto(l-1)` because the
// base lacks Cohen's family (II) `p⁻¹ t_β p = t_β w_β(b) d` (Approach-(b) keeps only the
// finite set (I); II is merely *derivable* via the `a_i`, `lemma_II`). The reroute
// (`docs/brick5-completeness-plan.md` §2.2ter) augments the a-tower BASE with a finite list
// of family-(II) relators — the bottom-augmented tower `h3_II` — making the a-levels literal
// isos again and re-isolating the "virtual" content to the single k-level (C4, Fork B).
//
// This module builds:
//   * `family_II_relator` / `family_II` — the augmenting relator words.  Each is
//     `(p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹`, i.e. lemma_II's two sides in relator form.  They are
//     valid over `h2_pres`'s generators (config uses gens 0–2; p,d,b all sit `< nk+2n+2`),
//     so they can be spliced into the `h2_pres` base.
//   * `lemma_family_II_relator_equiv_empty` — each relator is `≡_{h3_pres} ε` (lemma_II →
//     relator form).  This is the group-preservation key consumed by C3.1c via
//     `lemma_same_group_iff` (base_swap).
//
// C3.1c (the `h3_II` tower itself + the group-preservation iff) is added below in a later step.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::word_numbering::*;
use crate::layout::*;
use crate::hnn::*;
use crate::quotient::*;
use crate::h2::*;
use crate::h3::*;
use crate::base_swap::*;
use crate::benign::{apply_embedding, lemma_apply_embedding_valid};
use crate::britton_infra::lemma_hnn_presentation_valid;
use crate::higman_consequences::lemma_II;

verus! {

// ----------------------------------------------------------------------------
// A generic equiv → relator-form helper (pure presentation theory).
// ----------------------------------------------------------------------------

/// From `a ≡_p b`, the relator `a·b⁻¹` is `≡_p ε`. (No word-validity needed.)
pub proof fn lemma_equiv_to_relator(p: Presentation, a: Word, b: Word)
    requires
        equiv_in_presentation(p, a, b),
    ensures
        equiv_in_presentation(p, a + inverse_word(b), empty_word()),
{
    lemma_equiv_concat_left(p, a, b, inverse_word(b));     // a·b⁻¹ ≡ b·b⁻¹
    lemma_word_inverse_right(p, b);                        // b·b⁻¹ ≡ ε
    assert(concat(a, inverse_word(b)) == a + inverse_word(b));
    assert(concat(b, inverse_word(b)) == b + inverse_word(b));
    lemma_equiv_transitive(p, a + inverse_word(b), b + inverse_word(b), empty_word());
}

// ----------------------------------------------------------------------------
// The family-(II) relator words.
// ----------------------------------------------------------------------------

/// `p⁻¹ t_β p`, the LHS of family (II) (`t_β = config_word(β,0)`).
pub open spec fn family_II_lhs(mm: ModMachine, n: nat, beta: nat) -> Word {
    let nk = g_m(mm).num_generators;
    seq![Symbol::Inv(p_idx(nk, n))] + config_word(beta, 0) + seq![Symbol::Gen(p_idx(nk, n))]
}

/// `t_β w_β(b) d`, the RHS of family (II).
pub open spec fn family_II_rhs(mm: ModMachine, n: nat, m: nat, beta: nat) -> Word {
    let nk = g_m(mm).num_generators;
    config_word(beta, 0) + w_b(b_base(nk, n), n, m, beta) + seq![Symbol::Gen(d_idx(nk, n))]
}

/// The family-(II) relator `r_β = (p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹` — `≡ ε` exactly when
/// `p⁻¹ t_β p ≡ t_β w_β(b) d`, which `lemma_II` proves in `h3_pres`.
pub open spec fn family_II_relator(mm: ModMachine, n: nat, m: nat, beta: nat) -> Word {
    family_II_lhs(mm, n, beta) + inverse_word(family_II_rhs(mm, n, m, beta))
}

/// A finite family-(II) augmentation list, one relator per index in `alphas`.
pub open spec fn family_II(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>) -> Seq<Word> {
    Seq::new(alphas.len(), |i: int| family_II_relator(mm, n, m, alphas[i]))
}

// ----------------------------------------------------------------------------
// Validity: each relator is a valid word over any `ng ≥ nk + 2n + 2` (so over both
// `h2_pres` and `h3_pres`).
// ----------------------------------------------------------------------------

/// A single-symbol word `[s]` is valid when the symbol's index `< ng`.
proof fn lemma_sym_word_valid(s: Symbol, g: nat, ng: nat)
    requires
        g < ng,
        s == Symbol::Gen(g) || s == Symbol::Inv(g),
    ensures
        word_valid(seq![s], ng),
{
    let w: Word = seq![s];
    assert forall|j: int| 0 <= j < w.len() implies symbol_valid(#[trigger] w[j], ng) by {
        assert(w[0] == s);
    }
}

/// Both sides of family (II) — and hence the relator — are valid over `ng ≥ nk + 2n + 2`.
pub proof fn lemma_family_II_relator_valid(mm: ModMachine, n: nat, m: nat, beta: nat, ng: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
        (g_m(mm).num_generators + 2 * n + 2) as nat <= ng,
    ensures
        word_valid(family_II_lhs(mm, n, beta), ng),
        word_valid(family_II_rhs(mm, n, m, beta), ng),
        word_valid(family_II_relator(mm, n, m, beta), ng),
{
    let nk = g_m(mm).num_generators;
    let p = p_idx(nk, n);            // nk + 2n + 1
    let d = d_idx(nk, n);           // nk + 2n
    let bb = b_base(nk, n);         // nk + n
    let cfg = config_word(beta, 0);
    let wb = w_b(bb, n, m, beta);

    // atoms
    lemma_config_word_valid(beta, 0);                 // word_valid(cfg, 3)
    lemma_word_valid_mono(cfg, 3, ng);                // 3 ≤ ng
    lemma_sym_word_valid(Symbol::Inv(p), p, ng);      // [p⁻¹]
    lemma_sym_word_valid(Symbol::Gen(p), p, ng);      // [p]
    lemma_sym_word_valid(Symbol::Gen(d), d, ng);      // [d]
    lemma_w_c_valid(bb, n, m, beta, ng);              // word_valid(w_b, ng)  (bb + n = nk+2n ≤ ng)

    // LHS = [p⁻¹]·cfg·[p]
    lemma_concat_word_valid(seq![Symbol::Inv(p)], cfg, ng);
    lemma_concat_word_valid(seq![Symbol::Inv(p)] + cfg, seq![Symbol::Gen(p)], ng);
    assert(family_II_lhs(mm, n, beta) =~= (seq![Symbol::Inv(p)] + cfg) + seq![Symbol::Gen(p)]);

    // RHS = cfg·w_b·[d]
    lemma_concat_word_valid(cfg, wb, ng);
    lemma_concat_word_valid(cfg + wb, seq![Symbol::Gen(d)], ng);
    assert(family_II_rhs(mm, n, m, beta) =~= (cfg + wb) + seq![Symbol::Gen(d)]);

    // relator = LHS · RHS⁻¹
    lemma_inverse_word_valid(family_II_rhs(mm, n, m, beta), ng);
    lemma_concat_word_valid(family_II_lhs(mm, n, beta),
        inverse_word(family_II_rhs(mm, n, m, beta)), ng);
}

// ----------------------------------------------------------------------------
// Group-preservation key: each relator is `≡_{h3_pres} ε` (lemma_II → relator form).
// ----------------------------------------------------------------------------

/// **Each family-(II) relator is a consequence of `h3_pres`.** `lemma_II` gives
/// `p⁻¹ t_β p ≡ t_β w_β(b) d`; the relator form `(p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹ ≡ ε` follows.
pub proof fn lemma_family_II_relator_equiv_empty(mm: ModMachine, n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), family_II_relator(mm, n, m, beta), empty_word()),
{
    let h3 = h3_pres(mm, n, m);
    lemma_II(mm, n, m, beta);     // h3 ⊢ family_II_lhs ≡ family_II_rhs
    assert(equiv_in_presentation(h3, family_II_lhs(mm, n, beta), family_II_rhs(mm, n, m, beta)));
    lemma_equiv_to_relator(h3, family_II_lhs(mm, n, beta), family_II_rhs(mm, n, m, beta));
}

// ============================================================================
// C3.1c — the bottom-augmented tower `h3_II` and the group-preservation iff.
// ============================================================================
//
// Structure (the splice).  Both towers share the `h2_pres` relator prefix `H` and the SAME
// a-relator/k-relator blocks (same stable-letter indices — the num_gen counts agree because
// `add_relators` preserves the generator count).  `h3_II` just SPLICES `family_II` in right
// after `H`:
//     h3_pres.relators  ≃  H +              phi_blocks(2n) + Krel
//     h3_II.relators    ≃  H + family_II +  phi_blocks(2n) + Krel
// The compositional route (level-by-level base swap) is IMPOSSIBLE — `h2_II ≠ h2_pres` as
// groups (family (II) is not derivable in `h2_pres` alone; it needs the `a_i`).  So the
// group-equality is a genuinely TOP-LEVEL fact, discharged by `lemma_same_group_iff`
// (base_swap) against the flat splice.

// ----------------------------------------------------------------------------
// `hnn_relators` depends on the base only through `base.num_generators`.
// ----------------------------------------------------------------------------

/// Two HNN data with the same base generator-count and the same associations have the same
/// relators (the stable letter `Gen(base.num_generators)` and the association words agree).
pub proof fn lemma_hnn_relators_eq(d1: HNNData, d2: HNNData)
    requires
        d1.base.num_generators == d2.base.num_generators,
        d1.associations == d2.associations,
    ensures
        hnn_relators(d1) =~~= hnn_relators(d2),
{
    assert(stable_letter(d1) == stable_letter(d2));
    assert(stable_letter_inv(d1) == stable_letter_inv(d2));
    assert(hnn_relators(d1).len() == hnn_relators(d2).len());
    assert forall|i: int| 0 <= i < hnn_relators(d1).len()
        implies hnn_relators(d1)[i] =~~= hnn_relators(d2)[i] by {
        assert(d1.associations[i] == d2.associations[i]);
    }
}

// ----------------------------------------------------------------------------
// The a-relator blocks `phi_blocks(l) = Φ₁ + … + Φ_l`, and the explicit relator list of
// the canonical (non-augmented) tower `h3_upto`.
// ----------------------------------------------------------------------------

/// `Φ₁ + … + Φ_l` — the accumulated a-level HNN relators of the canonical tower.
pub open spec fn phi_blocks(mm: ModMachine, n: nat, m: nat, l: nat) -> Seq<Word>
    decreases l,
{
    if l == 0 {
        Seq::<Word>::empty()
    } else {
        phi_blocks(mm, n, m, (l - 1) as nat)
        + hnn_relators(HNNData {
            base: h3_upto(mm, n, m, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        })
    }
}

/// `h3_upto(l).relators ≃ h2_pres.relators + phi_blocks(l)`.
pub proof fn lemma_h3_upto_relators(mm: ModMachine, n: nat, m: nat, l: nat)
    ensures
        h3_upto(mm, n, m, l).relators =~= h2_pres(mm, n).relators + phi_blocks(mm, n, m, l),
    decreases l,
{
    if l == 0 {
        assert(phi_blocks(mm, n, m, 0) =~= Seq::<Word>::empty());
        assert(h2_pres(mm, n).relators + phi_blocks(mm, n, m, 0) =~= h2_pres(mm, n).relators);
    } else {
        lemma_h3_upto_relators(mm, n, m, (l - 1) as nat);
        let data = HNNData {
            base: h3_upto(mm, n, m, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        };
        // h3_upto(l).relators = h3_upto(l-1).relators + hnn_relators(data)
        assert(h3_upto(mm, n, m, l).relators
            =~= h3_upto(mm, n, m, (l - 1) as nat).relators + hnn_relators(data));
        assert(phi_blocks(mm, n, m, l) =~= phi_blocks(mm, n, m, (l - 1) as nat) + hnn_relators(data));
    }
}

// ----------------------------------------------------------------------------
// The bottom-augmented tower `h3_II`.  Family (II) is spliced into the a-tower BASE (at
// `h2_II`), so each a-level's base carries it (what C3.2 needs); the k-level on top is `h3_II`.
// ----------------------------------------------------------------------------

/// `h2_II = h2_pres + family (II)` — the augmented bottom of the tower.
pub open spec fn h2_II(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>) -> Presentation {
    add_relators(h2_pres(mm, n), family_II(mm, n, m, alphas))
}

/// The augmented a-tower: `h2_II` with `a_1,…,a_l` added (same `φ_l` associations as `h3_upto`).
pub open spec fn h3_II_upto(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat) -> Presentation
    decreases l,
{
    if l == 0 {
        h2_II(mm, n, m, alphas)
    } else {
        hnn_presentation(HNNData {
            base: h3_II_upto(mm, n, m, alphas, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        })
    }
}

/// `h3_II = HNN(h3_II_upto(2n); k ∣ ψ)` — the augmented Higman group (same `ψ` as `h3_pres`).
pub open spec fn h3_II(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>) -> Presentation {
    hnn_presentation(HNNData {
        base: h3_II_upto(mm, n, m, alphas, (2 * n) as nat),
        associations: psi_assoc(mm, n),
    })
}

/// `h3_II_upto(l)` has the SAME generator count as `h3_upto(l)` (`add_relators` preserves it).
pub proof fn lemma_h3_II_upto_num_generators(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat)
    ensures
        h3_II_upto(mm, n, m, alphas, l).num_generators
            == h2_num_gens((4 + mm.quads.len()) as nat, n) + l,
    decreases l,
{
    if l == 0 {
        lemma_add_relators_relators(h2_pres(mm, n), family_II(mm, n, m, alphas));  // num_gen preserved
        lemma_h2_num_generators(mm, n);
    } else {
        lemma_h3_II_upto_num_generators(mm, n, m, alphas, (l - 1) as nat);
    }
}

/// `h3_II_upto(l)` is a valid presentation (mirror of `lemma_h3_upto_valid`).
pub proof fn lemma_h3_II_upto_valid(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat)
    requires
        l <= 2 * n,
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        presentation_valid(h3_II_upto(mm, n, m, alphas, l)),
    decreases l,
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                                  // nk = 4+|quads|
    if l == 0 {
        // h2_II = add_relators(h2_pres, family_II): valid since each relator word_valid over h2 gens.
        lemma_h2_pres_valid(mm, n);
        lemma_h2_num_generators(mm, n);                            // h2_pres.num = nk+2n+2
        assert forall|i: int| 0 <= i < family_II(mm, n, m, alphas).len()
            implies word_valid(#[trigger] family_II(mm, n, m, alphas)[i], h2_pres(mm, n).num_generators) by {
            assert(family_II(mm, n, m, alphas)[i] == family_II_relator(mm, n, m, alphas[i]));
            lemma_family_II_relator_valid(mm, n, m, alphas[i], h2_pres(mm, n).num_generators);
        }
        lemma_add_relators_valid(h2_pres(mm, n), family_II(mm, n, m, alphas));
    } else {
        let base = h3_II_upto(mm, n, m, alphas, (l - 1) as nat);
        let data = HNNData { base, associations: phi_assoc(nk, n, m, l) };
        lemma_h3_II_upto_valid(mm, n, m, alphas, (l - 1) as nat);          // presentation_valid(base)
        lemma_h3_II_upto_num_generators(mm, n, m, alphas, (l - 1) as nat); // base.num = nk+2n+2+(l-1)
        lemma_phi_assoc_valid(nk, n, m, l, base.num_generators);
        lemma_hnn_data_valid_from(data, base.num_generators);
        lemma_hnn_presentation_valid(data);
    }
}

/// `h3_II_upto(l).relators ≃ h2_pres.relators + family_II + phi_blocks(l)` — the SPLICE: the
/// augmented tower equals the canonical one with `family_II` inserted right after `h2_pres`.
pub proof fn lemma_h3_II_upto_relators(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat)
    ensures
        h3_II_upto(mm, n, m, alphas, l).relators
            =~= h2_pres(mm, n).relators + family_II(mm, n, m, alphas) + phi_blocks(mm, n, m, l),
    decreases l,
{
    if l == 0 {
        lemma_add_relators_relators(h2_pres(mm, n), family_II(mm, n, m, alphas));  // .relators = h2 + fii
        assert(phi_blocks(mm, n, m, 0) =~= Seq::<Word>::empty());
        assert(h2_pres(mm, n).relators + family_II(mm, n, m, alphas) + phi_blocks(mm, n, m, 0)
            =~= h2_pres(mm, n).relators + family_II(mm, n, m, alphas));
    } else {
        lemma_h3_II_upto_relators(mm, n, m, alphas, (l - 1) as nat);
        let nk = g_m(mm).num_generators;
        let data_ii = HNNData {
            base: h3_II_upto(mm, n, m, alphas, (l - 1) as nat),
            associations: phi_assoc(nk, n, m, l),
        };
        let data = HNNData {
            base: h3_upto(mm, n, m, (l - 1) as nat),
            associations: phi_assoc(nk, n, m, l),
        };
        // Φ_l^II == Φ_l: same associations, and same base generator-count.
        lemma_h3_II_upto_num_generators(mm, n, m, alphas, (l - 1) as nat);
        lemma_h3_upto_num_generators(mm, n, m, (l - 1) as nat);
        lemma_hnn_relators_eq(data_ii, data);
        assert(hnn_relators(data_ii) == hnn_relators(data));
        // unfold both sides
        assert(h3_II_upto(mm, n, m, alphas, l).relators
            =~= h3_II_upto(mm, n, m, alphas, (l - 1) as nat).relators + hnn_relators(data_ii));
        assert(phi_blocks(mm, n, m, l) =~= phi_blocks(mm, n, m, (l - 1) as nat) + hnn_relators(data));
        // (H + fii + pb(l-1)) + Φ_l = H + fii + (pb(l-1) + Φ_l)
        assert(h2_pres(mm, n).relators + family_II(mm, n, m, alphas) + phi_blocks(mm, n, m, l)
            =~= (h2_pres(mm, n).relators + family_II(mm, n, m, alphas) + phi_blocks(mm, n, m, (l - 1) as nat))
                + hnn_relators(data));
    }
}

// ----------------------------------------------------------------------------
// Top-level facts about `h3_II` and the group-preservation iff (the C3.1 headline).
// ----------------------------------------------------------------------------

/// `h3_II` and `h3_pres` have the same generator count.
pub proof fn lemma_h3_II_num_generators(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    ensures
        h3_II(mm, n, m, alphas).num_generators == h3_pres(mm, n, m).num_generators,
        h3_II(mm, n, m, alphas).num_generators == h3_num_gens((4 + mm.quads.len()) as nat, n),
{
    lemma_h3_II_upto_num_generators(mm, n, m, alphas, (2 * n) as nat);  // = h2_num_gens + 2n
    lemma_h3_num_generators(mm, n, m);                                  // h3_pres = h3_num_gens
}

/// `h3_II` is a valid presentation.
pub proof fn lemma_h3_II_valid(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        presentation_valid(h3_II(mm, n, m, alphas)),
{
    let base = h3_II_upto(mm, n, m, alphas, (2 * n) as nat);
    let data = HNNData { base, associations: psi_assoc(mm, n) };
    lemma_h3_II_upto_valid(mm, n, m, alphas, (2 * n) as nat);
    lemma_h3_II_upto_num_generators(mm, n, m, alphas, (2 * n) as nat);  // base.num = nk+4n+2
    lemma_g_m_num_generators(mm);
    lemma_psi_assoc_valid(mm, n, base.num_generators);                 // needs nk+2n+2 ≤ nk+4n+2
    lemma_hnn_data_valid_from(data, base.num_generators);
    lemma_hnn_presentation_valid(data);
}

/// **The group-preservation iff (C3.1 headline).** `h3_II` (family (II) spliced into the
/// a-tower base) presents the SAME group as `h3_pres`: `equiv_in(h3_pres,·,·) ⟺
/// equiv_in(h3_II,·,·)`. Discharged by `lemma_same_group_iff` (base_swap) against the flat
/// splice `h3_pres ≃ H+M`, `h3_II ≃ H+family_II+M` — each augmenting relator is `≡_{h3_pres} ε`
/// (lemma_II), and the shared relators are relators of both.
pub proof fn lemma_h3_II_group_preserving(
    mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w1: Word, w2: Word,
)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2)
            <==> equiv_in_presentation(h3_II(mm, n, m, alphas), w1, w2),
{
    let p = h3_pres(mm, n, m);
    let q = h3_II(mm, n, m, alphas);
    let hh = h2_pres(mm, n).relators;
    let ff = family_II(mm, n, m, alphas);
    let pb = phi_blocks(mm, n, m, (2 * n) as nat);
    let psi_data = HNNData { base: h3_upto(mm, n, m, (2 * n) as nat), associations: psi_assoc(mm, n) };
    let psi_data_ii =
        HNNData { base: h3_II_upto(mm, n, m, alphas, (2 * n) as nat), associations: psi_assoc(mm, n) };
    let krel = hnn_relators(psi_data);
    let mm_blk = pb + krel;       // M = phi_blocks(2n) + Krel

    // validity + num_gens
    lemma_h3_pres_valid(mm, n, m);
    lemma_h3_II_valid(mm, n, m, alphas);
    lemma_h3_II_num_generators(mm, n, m, alphas);     // q.num == p.num
    assert(q.num_generators == p.num_generators);

    // K-relators agree (same num_gens, same ψ).
    lemma_h3_II_upto_num_generators(mm, n, m, alphas, (2 * n) as nat);
    lemma_h3_upto_num_generators(mm, n, m, (2 * n) as nat);
    lemma_hnn_relators_eq(psi_data_ii, psi_data);
    assert(hnn_relators(psi_data_ii) == krel);

    // p.relators ≃ H + M
    lemma_h3_upto_relators(mm, n, m, (2 * n) as nat);          // h3_upto(2n).relators ≃ H + pb
    assert(p.relators =~= h3_upto(mm, n, m, (2 * n) as nat).relators + krel);
    assert(p.relators =~= hh + mm_blk) by {
        assert(p.relators =~= (hh + pb) + krel);
        assert((hh + pb) + krel =~= hh + (pb + krel));
    }
    // q.relators ≃ H + F + M
    lemma_h3_II_upto_relators(mm, n, m, alphas, (2 * n) as nat);   // ≃ H + F + pb
    assert(q.relators =~= h3_II_upto(mm, n, m, alphas, (2 * n) as nat).relators + hnn_relators(psi_data_ii));
    assert(q.relators =~= hh + ff + mm_blk) by {
        assert(q.relators =~= (hh + ff + pb) + krel);
        assert((hh + ff + pb) + krel =~= (hh + ff) + (pb + krel));
        assert(hh + ff + mm_blk =~= (hh + ff) + mm_blk);
    }

    reveal(presentation_valid);     // unfold word_valid-of-relators below
    let hl = hh.len() as int;
    let fl = ff.len() as int;
    let ml = mm_blk.len() as int;
    // length facts from the seq equalities (=~= gives ==)
    assert(p.relators.len() == hl + ml);
    assert(q.relators.len() == hl + fl + ml);
    assert((hh + ff).len() == hl + fl);

    // (A) every q-relator is ≡_p ε.
    assert forall|i: int| 0 <= i < q.relators.len()
        implies word_valid(#[trigger] q.relators[i], p.num_generators)
            && equiv_in_presentation(p, q.relators[i], empty_word()) by {
        // word_valid from presentation_valid(q) (num_gens agree)
        assert(word_valid(q.relators[i], q.num_generators));
        // q.relators ≃ (hh+ff) + mm_blk
        assert(q.relators[i] == ((hh + ff) + mm_blk)[i]);
        if i < hl {
            // H-block: a relator of p (p.relators ≃ hh + mm_blk, prefix hh)
            assert(q.relators[i] == hh[i]);
            assert(p.relators[i] == hh[i]);
            lemma_relator_is_identity(p, i);
        } else if i < hl + fl {
            // family-II block
            assert(q.relators[i] == ff[i - hl]);
            assert(ff[i - hl] == family_II_relator(mm, n, m, alphas[i - hl]));
            lemma_family_II_relator_equiv_empty(mm, n, m, alphas[i - hl]);
        } else {
            // M-block (shifted by fl): q.relators[i] == p.relators[i - fl]
            assert(((hh + ff) + mm_blk)[i] == mm_blk[i - (hl + fl)]);   // i ≥ (hh+ff).len()
            assert(p.relators[i - fl] == (hh + mm_blk)[i - fl]);
            assert((hh + mm_blk)[i - fl] == mm_blk[(i - fl) - hl]);     // hl ≤ i-fl < hl+ml
            assert((i - fl) - hl == i - (hl + fl));
            assert(q.relators[i] == p.relators[i - fl]);
            lemma_relator_is_identity(p, i - fl);
        }
    }

    // (B) every p-relator is ≡_q ε.
    assert forall|j: int| 0 <= j < p.relators.len()
        implies word_valid(#[trigger] p.relators[j], q.num_generators)
            && equiv_in_presentation(q, p.relators[j], empty_word()) by {
        assert(word_valid(p.relators[j], p.num_generators));
        assert(p.relators[j] == (hh + mm_blk)[j]);
        if j < hl {
            assert(p.relators[j] == hh[j]);
            assert(q.relators[j] == hh[j]);
            lemma_relator_is_identity(q, j);
        } else {
            // M-block: p.relators[j] == q.relators[j + fl]
            assert((hh + mm_blk)[j] == mm_blk[j - hl]);                 // hl ≤ j < hl+ml
            assert(q.relators[j + fl] == ((hh + ff) + mm_blk)[j + fl]);
            assert(((hh + ff) + mm_blk)[j + fl] == mm_blk[(j + fl) - (hl + fl)]);  // j+fl ≥ hl+fl
            assert((j + fl) - (hl + fl) == j - hl);
            assert(p.relators[j] == q.relators[j + fl]);
            lemma_relator_is_identity(q, j + fl);
        }
    }

    lemma_same_group_iff(p, q, w1, w2);
}

// ============================================================================
// C3.2 — structural seeds (the b-augmented a-level recognition; see docs/brick5-c3.2-plan.md).
// ============================================================================

/// `phi_assoc` has `n + 4` association pairs — the stated gens `t, x, d, b_1..b_n, p`. The `k`
/// of `hnn_associations_isomorphic` for the a-level iso (C3.2).
pub proof fn lemma_phi_assoc_len(nk: nat, n: nat, m: nat, l: nat)
    ensures
        phi_assoc(nk, n, m, l).len() == n + 4,
{
    // phi_assoc = [t↦t_l, x↦xᵐ, d↦b_l d] (3) + phi_bblock (n) + [p↦p] (1)
    assert(phi_bblock(nk, n).len() == n);
}

/// **The explicit a_words/b_words of `φ_l`, by position** — the structural backbone of the
/// a-level iso (C3.2). `phi_assoc = head(3) + phi_bblock(n) + tail(1)`, so the `i`-th stated
/// gen ↦ image pair is:
///   `0 ↦ (t, t_l = config(l,0))`,  `1 ↦ (x, xᵐ)`,  `2 ↦ (d, b_l·d)`,
///   `3+j ↦ (b_{j+1}, b_{j+1})` for `0 ≤ j < n`,  `n+3 ↦ (p, p)`.
/// The crux (C3.2c) states the per-`w` biconditional against exactly these forms.
pub proof fn lemma_phi_assoc_index(nk: nat, n: nat, m: nat, l: nat)
    ensures
        phi_assoc(nk, n, m, l).len() == n + 4,
        phi_assoc(nk, n, m, l)[0] == (seq![Symbol::Gen(0)], config_word(l, 0)),
        phi_assoc(nk, n, m, l)[1] == (seq![Symbol::Gen(1)], symbol_power(Symbol::Gen(1), m)),
        phi_assoc(nk, n, m, l)[2]
            == (seq![Symbol::Gen(d_idx(nk, n))],
                seq![alphabet_letter(b_base(nk, n), n, l), Symbol::Gen(d_idx(nk, n))]),
        forall|j: int| 0 <= j < n ==> #[trigger] phi_assoc(nk, n, m, l)[3 + j]
            == (seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))],
                seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]),
        phi_assoc(nk, n, m, l)[(n + 3) as int]
            == (seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))]),
{
    let d = d_idx(nk, n);
    let p = p_idx(nk, n);
    let bb = b_base(nk, n);
    let head: Seq<(Word, Word)> = seq![
        (seq![Symbol::Gen(0)], config_word(l, 0)),
        (seq![Symbol::Gen(1)], symbol_power(Symbol::Gen(1), m)),
        (seq![Symbol::Gen(d)], seq![alphabet_letter(bb, n, l), Symbol::Gen(d)]),
    ];
    let bblk = phi_bblock(nk, n);
    let tail: Seq<(Word, Word)> = seq![ (seq![Symbol::Gen(p)], seq![Symbol::Gen(p)]) ];
    // phi_assoc is definitionally head + phi_bblock + tail.
    assert(phi_assoc(nk, n, m, l) == (head + bblk) + tail);
    assert(head.len() == 3);
    assert(bblk.len() == n);
    assert(tail.len() == 1);
    lemma_phi_assoc_len(nk, n, m, l);

    // head indices 0,1,2  (i < 3 ≤ 3 + n = (head+bblk).len())
    assert(((head + bblk) + tail)[0] == (head + bblk)[0]);
    assert((head + bblk)[0] == head[0]);
    assert(((head + bblk) + tail)[1] == (head + bblk)[1]);
    assert((head + bblk)[1] == head[1]);
    assert(((head + bblk) + tail)[2] == (head + bblk)[2]);
    assert((head + bblk)[2] == head[2]);

    // b-block indices 3+j  (3 ≤ 3+j < 3+n)
    assert forall|j: int| 0 <= j < n implies #[trigger] phi_assoc(nk, n, m, l)[3 + j]
        == (seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))],
            seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]) by {
        assert(((head + bblk) + tail)[3 + j] == (head + bblk)[3 + j]);
        assert((head + bblk)[3 + j] == bblk[j]);
        assert(bblk[j] == (seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))],
            seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]));
    }

    // tail index n+3  (= (head+bblk).len())
    assert(((head + bblk) + tail)[(n + 3) as int] == tail[0]);
}

// ----------------------------------------------------------------------------
// The a-level HNN data `phi_l_data` and its basic structural facts.
// ----------------------------------------------------------------------------

/// The HNN data for the a-level association `φ_l` over the family-(II)-augmented base
/// `h3_II_upto(l-1)`. `hnn_associations_isomorphic(phi_l_data(..))` is the C3.2 goal
/// (`lemma_phi_l_iso`); C3.2b/c/d discharge it.
pub open spec fn phi_l_data(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat) -> HNNData {
    HNNData {
        base: h3_II_upto(mm, n, m, alphas, (l - 1) as nat),
        associations: phi_assoc(g_m(mm).num_generators, n, m, l),
    }
}

/// The base generator-count of `phi_l_data` is `h2_num_gens + (l-1)` (so `≥ nk + 2n + 2` for
/// `l ≥ 1`), and there are `k = n + 4` associations.
pub proof fn lemma_phi_l_data_base(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat)
    requires
        1 <= l <= 2 * n,
    ensures
        phi_l_data(mm, n, m, alphas, l).base.num_generators
            == h2_num_gens((4 + mm.quads.len()) as nat, n) + (l - 1),
        phi_l_data(mm, n, m, alphas, l).associations.len() == n + 4,
{
    lemma_h3_II_upto_num_generators(mm, n, m, alphas, (l - 1) as nat);
    lemma_phi_assoc_len(g_m(mm).num_generators, n, m, l);
}

/// **`phi_l_data` is a valid HNN datum** — base valid (`lemma_h3_II_upto_valid`) and every
/// association word valid over `base.num_generators` (`lemma_phi_assoc_valid`, since
/// `base.num_generators = nk + 2n + 2 + (l-1) ≥ nk + 2n + 2`). This is what C3.2b (von Dyck)
/// and the eventual Britton instantiation consume.
pub proof fn lemma_phi_l_data_valid(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat)
    requires
        1 <= l <= 2 * n,
        2 * n < m,
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        hnn_data_valid(phi_l_data(mm, n, m, alphas, l)),
{
    let nk = g_m(mm).num_generators;
    let data = phi_l_data(mm, n, m, alphas, l);
    let base = data.base;
    lemma_g_m_num_generators(mm);                                   // nk = 4 + |quads|
    // base valid + num_gens
    lemma_h3_II_upto_valid(mm, n, m, alphas, (l - 1) as nat);
    lemma_h3_II_upto_num_generators(mm, n, m, alphas, (l - 1) as nat);
    assert(base.num_generators == h2_num_gens(nk, n) + (l - 1));    // = nk + 2n + 2 + (l-1)
    // associations valid over base.num_generators (≥ nk + 2n + 2)
    lemma_phi_assoc_valid(nk, n, m, l, base.num_generators);
    lemma_hnn_data_valid_from(data, base.num_generators);
}

// ============================================================================
// C3.2d infrastructure — the base-swap collapse prerequisites (no dependence on
// the deep bottom crux). See docs/brick5-c3.2-plan.md §2.2bis / §4 C3.2d.
//
// The full a-level iso `lemma_phi_l_iso` mirrors `lemma_b_m_upto_faithful` (machine_group.rs):
// a `decreases l` induction building each φ-step iso inline from the IH (lower-tower
// faithfulness) + the bottom crux (b-augmented `conj_scaling_trivial_iff` over `h2_II` = C3.2c),
// then `lemma_single_hnn_base_faithful` descends one level.  The two facts below are the
// crux-INDEPENDENT halves: (1) both embeddings are `h2`-words (so they CAN descend the a-tower);
// (2) the EASY collapse direction — `h2_II`-triviality lifts to every a-tower level.
// ============================================================================

/// **Both `φ_l` embeddings are `h2`-words.** For any `w` valid over the `k = n+4` association
/// slots, `emb(a_words, w)` and `emb(b_words, w)` are valid over `h2_num_gens(nk, n) = nk+2n+2`
/// — i.e. they touch only `t, x, d, b_j, p` and NEVER an `a_i`/`k` stable letter (those sit at
/// indices `≥ h2_num_gens`).  This is what lets the collapse descend them down the a-tower
/// (`lemma_single_hnn_base_faithful` needs the word valid over the base's generators).
pub proof fn lemma_phi_l_emb_h2_valid(nk: nat, n: nat, m: nat, l: nat, w: Word)
    requires
        1 <= l <= 2 * n,
        word_valid(w, (n + 4) as nat),
    ensures
        word_valid(
            apply_embedding(Seq::new((n + 4) as nat, |i: int| phi_assoc(nk, n, m, l)[i].0), w),
            h2_num_gens(nk, n)),
        word_valid(
            apply_embedding(Seq::new((n + 4) as nat, |i: int| phi_assoc(nk, n, m, l)[i].1), w),
            h2_num_gens(nk, n)),
{
    let ng = h2_num_gens(nk, n);                            // = nk + 2n + 2
    let a_words = Seq::new((n + 4) as nat, |i: int| phi_assoc(nk, n, m, l)[i].0);
    let b_words = Seq::new((n + 4) as nat, |i: int| phi_assoc(nk, n, m, l)[i].1);
    lemma_phi_assoc_len(nk, n, m, l);                       // phi_assoc.len() == n + 4
    lemma_phi_assoc_valid(nk, n, m, l, ng);                 // assocs_valid(phi_assoc, ng), since ng = nk+2n+2
    assert(a_words.len() == n + 4);
    assert(b_words.len() == n + 4);
    assert forall|i: int| 0 <= i < a_words.len() implies word_valid(#[trigger] a_words[i], ng) by {
        assert(a_words[i] == phi_assoc(nk, n, m, l)[i].0);  // fires assocs_valid trigger on phi_assoc[i]
    }
    assert forall|i: int| 0 <= i < b_words.len() implies word_valid(#[trigger] b_words[i], ng) by {
        assert(b_words[i] == phi_assoc(nk, n, m, l)[i].1);
    }
    lemma_apply_embedding_valid(a_words, w, ng);
    lemma_apply_embedding_valid(b_words, w, ng);
}

/// **The EASY collapse direction (bottom → top).** Anything trivial in the augmented bottom
/// `h2_II` stays trivial all the way up the a-tower `h3_II_upto(l)`.  Pure HNN base-embedding
/// (`lemma_base_embeds_in_hnn`) iterated up the tower — no faithfulness / iso needed.  The HARD
/// direction (top → bottom) is the crux-gated half threaded through C3.2c/d.
pub proof fn lemma_h2II_equiv_lifts_to_tower(
    mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, l: nat, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(h2_II(mm, n, m, alphas), w1, w2),
    ensures
        equiv_in_presentation(h3_II_upto(mm, n, m, alphas, l), w1, w2),
    decreases l,
{
    if l == 0 {
        assert(h3_II_upto(mm, n, m, alphas, 0) == h2_II(mm, n, m, alphas));
    } else {
        lemma_h2II_equiv_lifts_to_tower(mm, n, m, alphas, (l - 1) as nat, w1, w2);
        let data = HNNData {
            base: h3_II_upto(mm, n, m, alphas, (l - 1) as nat),
            associations: phi_assoc(g_m(mm).num_generators, n, m, l),
        };
        // h3_II_upto(l) == hnn_presentation(data); IH gives equiv in data.base.
        lemma_base_embeds_in_hnn(data, w1, w2);
    }
}

} // verus!
