// Layer 2 — Brick 5, C3.2c: the per-level iso crux `lemma_phi_l_iso_at_h2II`.
//
// This module builds the C-arc: the biconditional `emb(a_words,w) ≡_{h2_II} ε ⟺
// emb(b_words,w) ≡_{h2_II} ε`, where `a_words = [t,x,d,b_j,p]` (literal generators) and
// `b_words = φ_l(a_words) = [t_l, xᵐ, b_l·d, b_j, p]`.  Per Danielle's design review
// (2026-06-22), both directions route through a UNIFIED "HNN lifting lemma" (faithfulness
// lifts base→HNN under an embedding that preserves associations), instantiated for `map_a`
// (the inclusion `F ↪ h1_base`) and `map_b` (the `φ_l`-restriction).  The von Dyck halves
// reduce to `lemma_emb_respects_source_equiv` over the abstract `P_A = HNN(F, p | family II)`.
//
// This first brick is the DIGIT-SCALING identity at the heart of the von-Dyck-`b` direction:
// `φ_l(config(β,0)) = config(mβ+l, 0)` — the reason `φ_l` carries the family-(II) relation
// for `β` onto the one for `mβ+l` (combined with the numbering identity `w_{mβ+l}(b)=w_β(b)·b_l`).
// See `docs/brick5-c3.2c-plan.md` §5.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{ModMachine, g_m, config_word, symbol_power, lemma_g_m_num_generators,
    lemma_inverse_word_sympower, lemma_symbol_power_merge, lemma_apply_embedding_sympower,
    word_power, lemma_word_power_symbol};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat};
use crate::word_numbering::{w_b, w_c, alphabet_letter, numbers_word, lemma_w_b_snoc,
    lemma_w_c_gens_in_block};
use crate::layout::{b_base, d_idx, h2_num_gens};
use crate::h1::h_w_b;
use crate::h3_ii::{phi_l_subst, family_II_rhs};

verus! {

/// `config_word(r,0) =~= x⁻ʳ · t · xʳ` — the `s=0` config word, with the empty `y`-powers
/// (`symbol_power(Inv(2),0)`, `symbol_power(Gen(2),0)`) dropped.
pub proof fn lemma_config_zero_form(r: nat)
    ensures
        config_word(r, 0) =~= symbol_power(Symbol::Inv(1), r) + seq![Symbol::Gen(0)]
            + symbol_power(Symbol::Gen(1), r),
{
    assert(symbol_power(Symbol::Inv(2), 0) =~= empty_word());
    assert(symbol_power(Symbol::Gen(2), 0) =~= empty_word());
}

/// **Digit-scaling under `φ_l`**: `φ_l(config(β,0)) =~= config(mβ+l, 0)`.
///
/// `config(β,0) = x⁻ᵝ t xᵝ` (gens `t=0`, `x=1`; the `y`-powers vanish at `s=0`), and `φ_l`
/// (= `phi_l_subst`) sends `t ↦ config(l,0)` and `x ↦ xᵐ` (it never touches `y`/`d`/`b`/`p`
/// here).  So the embedding is `x⁻ᵐᵝ · (x⁻ˡ t xˡ) · xᵐᵝ`, which merges to `x⁻⁽ᵐᵝ⁺ˡ⁾ t x⁽ᵐᵝ⁺ˡ⁾
/// = config(mβ+l, 0)`.  A pure word identity (no preconditions): the algebraic core of why
/// `φ_l` carries family (II) for `β` onto the relation for `mβ+l`.
pub proof fn lemma_phi_l_on_config_zero(mm: ModMachine, n: nat, m: nat, l: nat, beta: nat)
    ensures
        apply_embedding(phi_l_subst(g_m(mm).num_generators, n, m, l), config_word(beta, 0))
            =~= config_word(m * beta + l, 0),
{
    let nk = g_m(mm).num_generators;
    let subst = phi_l_subst(nk, n, m, l);
    let i2z = symbol_power(Symbol::Inv(2), 0);
    let i1 = symbol_power(Symbol::Inv(1), beta);
    let t0: Word = seq![Symbol::Gen(0)];
    let g1 = symbol_power(Symbol::Gen(1), beta);
    let g2z = symbol_power(Symbol::Gen(2), 0);

    // subst entries we touch (the t- and x-images; y/d/b/p never appear at s=0).
    assert(subst[0] == config_word(l, 0));
    assert(subst[1] == symbol_power(Symbol::Gen(1), m));

    // config_word(beta,0) is the 5-fold concat ((((i2z + i1) + t0) + g1) + g2z).
    assert(config_word(beta, 0) == (((i2z + i1) + t0) + g1) + g2z);

    // Distribute apply_embedding over the four concatenations.
    lemma_apply_embedding_concat(subst, ((i2z + i1) + t0) + g1, g2z);
    lemma_apply_embedding_concat(subst, (i2z + i1) + t0, g1);
    lemma_apply_embedding_concat(subst, i2z + i1, t0);
    lemma_apply_embedding_concat(subst, i2z, i1);

    let e_i2z = apply_embedding(subst, i2z);
    let e_i1 = apply_embedding(subst, i1);
    let e_t0 = apply_embedding(subst, t0);
    let e_g1 = apply_embedding(subst, g1);
    let e_g2z = apply_embedding(subst, g2z);

    assert(apply_embedding(subst, config_word(beta, 0))
        =~= (((e_i2z + e_i1) + e_t0) + e_g1) + e_g2z);

    // --- the two empty y-powers map to ε ---
    assert(i2z =~= empty_word());
    assert(g2z =~= empty_word());
    assert(apply_embedding(subst, empty_word()) =~= empty_word());
    assert(e_i2z =~= empty_word());
    assert(e_g2z =~= empty_word());

    // --- e_i1 =~= x⁻ᵐᵝ ---
    lemma_apply_embedding_sympower(subst, Symbol::Inv(1), beta);
    assert(apply_embedding_symbol(subst, Symbol::Inv(1)) =~= inverse_word(subst[1]));
    lemma_inverse_word_sympower(Symbol::Gen(1), m);          // inv(xᵐ) =~= Inv(1)ᵐ
    assert(inverse_symbol(Symbol::Gen(1)) == Symbol::Inv(1));
    assert(apply_embedding_symbol(subst, Symbol::Inv(1)) =~= symbol_power(Symbol::Inv(1), m));
    lemma_word_power_symbol(Symbol::Inv(1), m, beta);
    assert(e_i1 =~= symbol_power(Symbol::Inv(1), m * beta));

    // --- e_g1 =~= xᵐᵝ ---
    lemma_apply_embedding_sympower(subst, Symbol::Gen(1), beta);
    assert(apply_embedding_symbol(subst, Symbol::Gen(1)) == subst[1]);
    lemma_word_power_symbol(Symbol::Gen(1), m, beta);
    assert(e_g1 =~= symbol_power(Symbol::Gen(1), m * beta));

    // --- e_t0 =~= subst[0] = config(l,0) ---
    reveal_with_fuel(apply_embedding, 2);
    lemma_concat_empty_right(subst[0]);
    assert(e_t0 =~= subst[0]);
    assert(e_t0 =~= config_word(l, 0));

    // Collapse the empties: the embedded word reduces to x⁻ᵐᵝ · config(l,0) · xᵐᵝ.
    let imb = symbol_power(Symbol::Inv(1), m * beta);
    let gmb = symbol_power(Symbol::Gen(1), m * beta);
    assert(apply_embedding(subst, config_word(beta, 0)) =~= (imb + config_word(l, 0)) + gmb);

    // Expand config(l,0) and config(mβ+l,0).
    lemma_config_zero_form(l);
    lemma_config_zero_form((m * beta + l) as nat);

    // Merge the x-powers: x⁻ᵐᵝ·x⁻ˡ = x⁻⁽ᵐᵝ⁺ˡ⁾  and  xˡ·xᵐᵝ = x⁽ˡ⁺ᵐᵝ⁾ = x⁽ᵐᵝ⁺ˡ⁾.
    lemma_symbol_power_merge(Symbol::Inv(1), m * beta, l);
    lemma_symbol_power_merge(Symbol::Gen(1), l, m * beta);
    assert(l + m * beta == m * beta + l);

    assert(apply_embedding(subst, config_word(beta, 0))
        =~= symbol_power(Symbol::Inv(1), m * beta + l) + seq![Symbol::Gen(0)]
            + symbol_power(Symbol::Gen(1), m * beta + l));
}

/// **A substitution that fixes every symbol of `w` leaves `w` unchanged.** If
/// `apply_embedding_symbol(imgs, s) =~= [s]` for each symbol `s` of `w`, then
/// `apply_embedding(imgs, w) =~= w`.  (Induction on `w`, port of `lemma_apply_embedding_identity2`.)
pub proof fn lemma_apply_embedding_fixes(imgs: Seq<Word>, w: Word)
    requires
        forall|i: int| 0 <= i < w.len()
            ==> apply_embedding_symbol(imgs, #[trigger] w[i]) =~= seq![w[i]],
    ensures
        apply_embedding(imgs, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_embedding(imgs, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(w =~= seq![s] + rest);
        assert forall|i: int| 0 <= i < rest.len()
            implies apply_embedding_symbol(imgs, #[trigger] rest[i]) =~= seq![rest[i]] by {
            assert(rest[i] == w[i + 1]);
        }
        lemma_apply_embedding_fixes(imgs, rest);
        assert(apply_embedding_symbol(imgs, s) =~= seq![s]) by { assert(w[0] == s); }
        assert(apply_embedding(imgs, w)
            =~= concat(apply_embedding_symbol(imgs, s), apply_embedding(imgs, rest)));
    }
}

/// **`φ_l` fixes `w_β(b)`.** Its symbols all live in the b-block `[b_base, b_base+n)`
/// (`lemma_w_c_gens_in_block`, since `w_b := w_c` at `b_base`), and `phi_l_subst` maps every
/// b-block generator to itself (the identity branch — the b-block avoids `0`, `1`, `d_idx`).
pub proof fn lemma_phi_l_fixes_w_b(mm: ModMachine, n: nat, m: nat, l: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
        1 <= n,
    ensures
        apply_embedding(phi_l_subst(g_m(mm).num_generators, n, m, l),
            w_b(b_base(g_m(mm).num_generators, n), n, m, beta))
            =~= w_b(b_base(g_m(mm).num_generators, n), n, m, beta),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                       // nk == 4 + |quads| ≥ 4
    let subst = phi_l_subst(nk, n, m, l);
    let bb = b_base(nk, n);                             // = nk + n
    let wb = w_b(bb, n, m, beta);
    assert(wb == w_c(bb, n, m, beta));                  // w_b := w_c (open spec)
    lemma_w_c_gens_in_block(bb, n, m, beta);            // each symbol's index ∈ [bb, bb+n)
    assert forall|i: int| 0 <= i < wb.len()
        implies apply_embedding_symbol(subst, #[trigger] wb[i]) =~= seq![wb[i]] by {
        let g = generator_index(wb[i]);
        assert(bb <= g < bb + n);                       // gens_in_block on w_c
        assert(g != 0 && g != 1 && g != d_idx(nk, n));  // bb=nk+n≥5; bb+n-1<nk+2n=d_idx
        assert(g < h2_num_gens(nk, n));                 // g < nk+2n < nk+2n+2
        assert(subst[g as int] == seq![Symbol::Gen(g)]);
        match wb[i] {
            Symbol::Gen(gg) => {
                assert(gg == g);
                assert(apply_embedding_symbol(subst, wb[i]) == subst[gg as int]);
            },
            Symbol::Inv(gg) => {
                assert(gg == g);
                assert(apply_embedding_symbol(subst, wb[i]) =~= inverse_word(subst[gg as int]));
                reveal_with_fuel(inverse_word, 2);
            },
        }
    }
    lemma_apply_embedding_fixes(subst, wb);
}

/// **The family-(II) RHS payoff**: `φ_l(t_β · w_β(b) · d) =~= t_{mβ+l} · w_{mβ+l}(b) · d`,
/// i.e. `apply_embedding(φ_l, family_II_rhs(β)) =~= family_II_rhs(mβ+l)`.  Combines the
/// digit-scaling identity (`φ_l(t_β)=t_{mβ+l}`), the b-block fixing (`φ_l` fixes `w_β(b)`),
/// `φ_l(d) = b_l·d`, and the numbering snoc (`w_{mβ+l}(b) = w_β(b)·b_l`).  This is exactly why
/// `φ_l` carries the family-(II) relation for `β` onto the one for `mβ+l` (von-Dyck-`b`).
pub proof fn lemma_phi_l_on_family_II_rhs(mm: ModMachine, n: nat, m: nat, l: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
        2 * n < m,
        1 <= l <= 2 * n,
    ensures
        apply_embedding(phi_l_subst(g_m(mm).num_generators, n, m, l),
            family_II_rhs(mm, n, m, beta))
            =~= family_II_rhs(mm, n, m, m * beta + l),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let subst = phi_l_subst(nk, n, m, l);
    let bb = b_base(nk, n);
    let d = d_idx(nk, n);
    let cfg = config_word(beta, 0);
    let wb = w_b(bb, n, m, beta);
    let dw: Word = seq![Symbol::Gen(d)];

    // family_II_rhs(β) = (cfg + wb) + [d]; distribute apply_embedding.
    assert(family_II_rhs(mm, n, m, beta) == (cfg + wb) + dw);
    lemma_apply_embedding_concat(subst, cfg + wb, dw);
    lemma_apply_embedding_concat(subst, cfg, wb);

    // The three φ_l images.
    lemma_phi_l_on_config_zero(mm, n, m, l, beta);      // φ_l(cfg) =~= config(mβ+l,0)
    lemma_phi_l_fixes_w_b(mm, n, m, l, beta);           // φ_l(wb) =~= wb
    reveal_with_fuel(apply_embedding, 2);
    lemma_concat_empty_right(subst[d as int]);
    assert(apply_embedding(subst, dw) =~= subst[d as int]);   // φ_l(d) = subst[d] = b_l·d
    let bl = alphabet_letter(bb, n, l);
    assert(subst[d as int] == seq![bl, Symbol::Gen(d)]);

    let cfg2 = config_word(m * beta + l, 0);
    assert(apply_embedding(subst, family_II_rhs(mm, n, m, beta))
        =~= (cfg2 + wb) + seq![bl, Symbol::Gen(d)]);

    // Target side: w_{mβ+l}(b) = w_β(b) · b_l  (numbering snoc).  snoc yields `β·m+l`; bridge to `m·β+l`.
    lemma_w_b_snoc(bb, n, m, beta, l);
    assert(beta * m + l == m * beta + l) by (nonlinear_arith);
    let bl_seq = Seq::new(1, |_k: int| alphabet_letter(bb, n, l));
    assert(w_b(bb, n, m, m * beta + l) =~= wb + bl_seq);
    assert(bl_seq =~= seq![bl]);
    assert(family_II_rhs(mm, n, m, m * beta + l) == (cfg2 + w_b(bb, n, m, m * beta + l)) + dw);
    assert(seq![bl, Symbol::Gen(d)] =~= seq![bl] + dw);
}

} // verus!
