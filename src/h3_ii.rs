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
use crate::h3::*;
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

} // verus!
