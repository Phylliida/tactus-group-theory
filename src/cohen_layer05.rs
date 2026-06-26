//! # Layer 0.5 — the A/B-column free families in `L = C₀ ⋆ F₂` (Miller Thm 4.1).
//!
//! The compactness probe (`cohen_layer05_probe.rs`, §D) showed Miller's HNN faithfulness
//! `C₀ ↪ L ↪ G` localizes to finite slices, leaving ONE genuinely-new math obligation: the two
//! association columns of the finite Miller slice are **free families** in `L = C₀ ⋆ F₂`.
//!
//! This module discharges both, with Miller's **`i ≥ 1`** convention (every `c`-term carries a
//! *nonempty* `a`-spacer — the design-doc §D nuance: the probe's 0-indexed `c₀·b` had an empty
//! spacer that collides with the separate `b` generator under the retraction). Concretely, for `n`
//! c-generators we use exponent `j+1` on the `j`-th c-term:
//!   * **A-column** `{ b } ∪ { cⱼ·a⁻⁽ʲ⁺¹⁾·b·a⁽ʲ⁺¹⁾ : 0 ≤ j < n }`  (length `n+1`)
//!   * **B-column** `{ a } ∪ { b⁻⁽ʲ⁺¹⁾·a·b⁽ʲ⁺¹⁾ : 0 ≤ j < n }`      (length `n+1`)
//! In `L`'s alphabet: `cⱼ = Gen(j)` (`j<n`), `a = Gen(n)`, `b = Gen(n+1)`.
//!
//! ## The proof — the retraction ρ killing `C₀` (companion-validated, Miller-faithful)
//!
//! `ρ : L = C₀ ⋆ F₂ → F₂` sends every `cⱼ ↦ ε`, `a ↦ a`, `b ↦ b`. It is a valid homomorphism
//! (it kills all of `decls`, which are words over the `cⱼ` only). Under ρ:
//!   * the **A-column** maps **exactly** onto `conj_family(n+1) = { a⁻ⁱ·b·aⁱ : 0 ≤ i ≤ n }`
//!     (the `b` is `i=0`; the `j`-th c-term is `i=j+1`) — banked free in F₂ (`lemma_conj_family_free`);
//!   * the **B-column** maps **exactly** onto `conj_family_b(n+1) = { b⁻ⁱ·a·bⁱ : 0 ≤ i ≤ n }`
//!     (pure-F₂, no `c`'s) — banked free in F₂ (`lemma_conj_family_b_free`).
//! Then the Layer-1 pullback engine `lemma_pullback_free` gives: a relation among the column words
//! that is trivial in `L` pushes through ρ to a relation among the (free) `conj_family` words in F₂,
//! hence is trivial in the abstract free group. That is exactly `is_free_family(L, col)`.
//!
//! This follows Miller §4.1 literally (his "A and B are free with free bases the listed generators
//! by our previous discussion"): the kill-`C₀` retraction is the standard, lightweight realization
//! of that freeness, and — crucially — does NOT use the §B.4 "C₀ is free" shortcut (a dragon: `∼` is
//! only c.e.). `decls` are carried opaquely throughout.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::benign::{apply_embedding, apply_embedding_symbol};
use crate::homomorphism::{HomomorphismData, apply_hom, apply_hom_symbol, is_valid_homomorphism,
    lemma_hom_singleton, lemma_hom_respects_concat};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::machine_group::{symbol_power, lemma_symbol_power_valid, lemma_symbol_power_merge,
    lemma_symbol_power_one, lemma_word_valid_mono};
use crate::f_free::is_free_family;
use crate::free_basis::{comp_images, lemma_pullback_free};
use crate::free_product::shift_relators;
use crate::conj_free::{conj_family, conj_word};
use crate::conj_free_core::lemma_conj_family_free;
use crate::conj_free_b::{conj_family_b, conj_word_b, lemma_conj_family_b_free};
use crate::cohen_layer05_probe::{c0_slice, l_slice};

verus! {

// ===========================================================================
// 0. The Miller `i ≥ 1` columns of `L = C₀ ⋆ F₂`.
//   Alphabet:  cⱼ = Gen(j) (j<n),  a = Gen(n),  b = Gen(n+1).   num_generators = n+2.
// ===========================================================================

/// A-basis element `cⱼ · a⁻⁽ʲ⁺¹⁾ · b · a⁽ʲ⁺¹⁾` (exponent `j+1` ⟹ nonempty `a`-spacer).
pub open spec fn acol_elt(n: nat, j: nat) -> Word {
    seq![Symbol::Gen(j)]
        + symbol_power(Symbol::Inv(n), j + 1)
        + seq![Symbol::Gen(n + 1)]
        + symbol_power(Symbol::Gen(n), j + 1)
}

/// B-basis element `b⁻⁽ʲ⁺¹⁾ · a · b⁽ʲ⁺¹⁾` (pure-F₂, exponent `j+1`).
pub open spec fn bcol_elt(n: nat, j: nat) -> Word {
    symbol_power(Symbol::Inv(n + 1), j + 1)
        + seq![Symbol::Gen(n)]
        + symbol_power(Symbol::Gen(n + 1), j + 1)
}

/// The A-column `{ b } ∪ { cⱼa⁻⁽ʲ⁺¹⁾ba⁽ʲ⁺¹⁾ : j<n }` — length `n+1`.
pub open spec fn a_col(n: nat) -> Seq<Word> {
    seq![seq![Symbol::Gen(n + 1)]] + Seq::new(n, |j: int| acol_elt(n, j as nat))
}

/// The B-column `{ a } ∪ { b⁻⁽ʲ⁺¹⁾ab⁽ʲ⁺¹⁾ : j<n }` — length `n+1`.
pub open spec fn b_col(n: nat) -> Seq<Word> {
    seq![seq![Symbol::Gen(n)]] + Seq::new(n, |j: int| bcol_elt(n, j as nat))
}

// ===========================================================================
// 1. The retraction ρ : L = C₀ ⋆ F₂ → F₂ killing the `cⱼ`.
//   images:  cⱼ ↦ ε (j<n),  a=Gen(n) ↦ [Gen(0)],  b=Gen(n+1) ↦ [Gen(1)].
// ===========================================================================

/// ρ's generator images (length `n+2`): first `n` are `ε`, then `[Gen(0)]`, `[Gen(1)]`.
pub open spec fn rho_imgs(n: nat) -> Seq<Word> {
    Seq::new(n, |_i: int| empty_word()) + seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)]]
}

/// The retraction homomorphism `L → F₂`.
pub open spec fn rho(n: nat, decls: Seq<Word>) -> HomomorphismData {
    HomomorphismData {
        source: l_slice(n, decls),
        target: free_group(2),
        generator_images: rho_imgs(n),
    }
}

// --- rho_imgs index facts ---

proof fn lemma_rho_imgs_len(n: nat)
    ensures rho_imgs(n).len() == n + 2,
{
}

proof fn lemma_rho_imgs_c(n: nat, j: nat)
    requires j < n,
    ensures rho_imgs(n)[j as int] == empty_word(),
{
    let pre = Seq::new(n, |_i: int| empty_word());
    assert(rho_imgs(n)[j as int] == pre[j as int]);
}

proof fn lemma_rho_imgs_a(n: nat)
    ensures rho_imgs(n)[n as int] == seq![Symbol::Gen(0)],
{
    let pre = Seq::new(n, |_i: int| empty_word());
    let suf = seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)]];
    assert(rho_imgs(n)[n as int] == suf[0]);
}

proof fn lemma_rho_imgs_b(n: nat)
    ensures rho_imgs(n)[(n + 1) as int] == seq![Symbol::Gen(1)],
{
    let pre = Seq::new(n, |_i: int| empty_word());
    let suf = seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)]];
    assert(rho_imgs(n)[(n + 1) as int] == suf[1]);
}

// ===========================================================================
// 2. apply_hom of a power block under ρ.
//   c-symbol ↦ ε;  Gen(n) ↦ Gen(0),  Inv(n) ↦ Inv(0)  (single-symbol images),
//   so apply_hom(ρ, sᵐ) = (image)ᵐ.
// ===========================================================================

/// If `apply_hom_symbol(h, s)` is a single symbol `[t]`, then `apply_hom(h, sᵐ) = tᵐ`.
proof fn lemma_apply_hom_symbol_power_single(h: HomomorphismData, s: Symbol, t: Symbol, m: nat)
    requires apply_hom_symbol(h, s) =~= seq![t],
    ensures apply_hom(h, symbol_power(s, m)) =~= symbol_power(t, m),
    decreases m,
{
    if m == 0 {
        assert(symbol_power(s, 0).len() == 0);
        assert(apply_hom(h, symbol_power(s, 0)) =~= empty_word());
        assert(symbol_power(t, 0) =~= empty_word());
    } else {
        let k = (m - 1) as nat;
        // sᵐ = [s] · s^{m-1}
        lemma_symbol_power_one(s);
        lemma_symbol_power_merge(s, 1, k);
        assert(symbol_power(s, m) =~= seq![s] + symbol_power(s, k));
        lemma_hom_respects_concat(h, seq![s], symbol_power(s, k));
        // apply_hom(h, [s]) = apply_hom_symbol(h, s) = [t]
        lemma_hom_singleton(h, s);
        assert(seq![s] =~= Seq::new(1, |_i: int| s));
        assert(apply_hom(h, seq![s]) =~= seq![t]);
        // IH
        lemma_apply_hom_symbol_power_single(h, s, t, k);
        // tᵐ = [t] · t^{m-1}
        lemma_symbol_power_one(t);
        lemma_symbol_power_merge(t, 1, k);
        assert(symbol_power(t, m) =~= seq![t] + symbol_power(t, k));
    }
}

/// `apply_hom_symbol(ρ, Gen(n)) = [Gen(0)]`.
proof fn lemma_rho_sym_a_pos(n: nat, decls: Seq<Word>)
    ensures apply_hom_symbol(rho(n, decls), Symbol::Gen(n)) =~= seq![Symbol::Gen(0)],
{
    lemma_rho_imgs_a(n);
    assert(apply_hom_symbol(rho(n, decls), Symbol::Gen(n)) == rho_imgs(n)[n as int]);
}

/// `apply_hom_symbol(ρ, Inv(n)) = [Inv(0)]` (inverse of the single-symbol image `[Gen(0)]`).
proof fn lemma_rho_sym_a_neg(n: nat, decls: Seq<Word>)
    ensures apply_hom_symbol(rho(n, decls), Symbol::Inv(n)) =~= seq![Symbol::Inv(0)],
{
    lemma_rho_imgs_a(n);
    // apply_hom_symbol(ρ, Inv(n)) = inverse_word(images[n]) = inverse_word([Gen(0)]) = [Inv(0)]
    assert(apply_hom_symbol(rho(n, decls), Symbol::Inv(n)) == inverse_word(rho_imgs(n)[n as int]));
    assert(inverse_word(seq![Symbol::Gen(0)]) =~= seq![Symbol::Inv(0)]) by {
        assert(seq![Symbol::Gen(0)].drop_first().len() == 0);
        assert(inverse_word(seq![Symbol::Gen(0)].drop_first()) =~= empty_word());
        assert(inverse_symbol(Symbol::Gen(0)) == Symbol::Inv(0));
    }
}

/// `apply_hom_symbol(ρ, Gen(n+1)) = [Gen(1)]`  (the image of `b`).
proof fn lemma_rho_sym_b(n: nat, decls: Seq<Word>)
    ensures apply_hom_symbol(rho(n, decls), Symbol::Gen(n + 1)) =~= seq![Symbol::Gen(1)],
{
    lemma_rho_imgs_b(n);
    assert(apply_hom_symbol(rho(n, decls), Symbol::Gen(n + 1)) == rho_imgs(n)[(n + 1) as int]);
}

/// `apply_hom_symbol(ρ, Gen(n)) = [Gen(0)]`  (the image of `a`).
proof fn lemma_rho_sym_a(n: nat, decls: Seq<Word>)
    ensures apply_hom_symbol(rho(n, decls), Symbol::Gen(n)) =~= seq![Symbol::Gen(0)],
{
    lemma_rho_sym_a_pos(n, decls);
}

// ===========================================================================
// 3. ρ maps the columns exactly onto conj_family / conj_family_b.
// ===========================================================================

/// `apply_hom(ρ, acol_elt(n,j)) = conj_word(j+1)`  (for `j < n`).
proof fn lemma_rho_acol_elt(n: nat, decls: Seq<Word>, j: nat)
    requires j < n,
    ensures apply_hom(rho(n, decls), acol_elt(n, j)) =~= conj_word((j + 1) as nat),
{
    let h = rho(n, decls);
    let cw = seq![Symbol::Gen(j)];
    let p = symbol_power(Symbol::Inv(n), j + 1);
    let bw = seq![Symbol::Gen(n + 1)];
    let q = symbol_power(Symbol::Gen(n), j + 1);
    // distribute apply_hom over the three concatenations
    lemma_hom_respects_concat(h, cw + p + bw, q);
    lemma_hom_respects_concat(h, cw + p, bw);
    lemma_hom_respects_concat(h, cw, p);
    // c-letter ↦ ε
    lemma_hom_singleton(h, Symbol::Gen(j));
    assert(seq![Symbol::Gen(j)] =~= Seq::new(1, |_i: int| Symbol::Gen(j)));
    lemma_rho_imgs_c(n, j);
    assert(apply_hom(h, cw) =~= empty_word());
    // a⁻⁽ʲ⁺¹⁾ ↦ Inv(0)⁽ʲ⁺¹⁾
    lemma_rho_sym_a_neg(n, decls);
    lemma_apply_hom_symbol_power_single(h, Symbol::Inv(n), Symbol::Inv(0), (j + 1) as nat);
    // b ↦ [Gen(1)]
    lemma_rho_sym_b(n, decls);
    lemma_hom_singleton(h, Symbol::Gen(n + 1));
    assert(seq![Symbol::Gen(n + 1)] =~= Seq::new(1, |_i: int| Symbol::Gen(n + 1)));
    assert(apply_hom(h, bw) =~= seq![Symbol::Gen(1)]);
    // a⁽ʲ⁺¹⁾ ↦ Gen(0)⁽ʲ⁺¹⁾
    lemma_rho_sym_a(n, decls);
    lemma_apply_hom_symbol_power_single(h, Symbol::Gen(n), Symbol::Gen(0), (j + 1) as nat);
    // assemble:  ε · Inv(0)^{j+1} · [Gen(1)] · Gen(0)^{j+1}  =  conj_word(j+1)
    assert(conj_word((j + 1) as nat)
        =~= symbol_power(Symbol::Inv(0), (j + 1) as nat)
            + seq![Symbol::Gen(1)]
            + symbol_power(Symbol::Gen(0), (j + 1) as nat));
}

/// `comp_images(ρ, a_col(n)) = conj_family(n+1)`.
proof fn lemma_rho_acol_is_conj_family(n: nat, decls: Seq<Word>)
    ensures comp_images(rho(n, decls), a_col(n)) =~= conj_family((n + 1) as nat),
{
    let h = rho(n, decls);
    let comp = comp_images(h, a_col(n));
    assert(a_col(n).len() == n + 1);
    assert(comp.len() == n + 1);
    assert(conj_family((n + 1) as nat).len() == n + 1);
    assert forall|i: int| 0 <= i < n + 1 implies
        #[trigger] comp[i] =~= conj_family((n + 1) as nat)[i] by {
        if i == 0 {
            // a_col[0] = [Gen(n+1)] ↦ [Gen(1)] = conj_word(0)
            assert(a_col(n)[0] == seq![Symbol::Gen(n + 1)]);
            lemma_rho_sym_b(n, decls);
            lemma_hom_singleton(h, Symbol::Gen(n + 1));
            assert(seq![Symbol::Gen(n + 1)] =~= Seq::new(1, |_i: int| Symbol::Gen(n + 1)));
            assert(comp[0] =~= seq![Symbol::Gen(1)]);
            assert(conj_word(0) =~= seq![Symbol::Gen(1)]) by {
                assert(symbol_power(Symbol::Inv(0), 0) =~= empty_word());
                assert(symbol_power(Symbol::Gen(0), 0) =~= empty_word());
            }
            assert(conj_family((n + 1) as nat)[0] == conj_word(0));
        } else {
            let j = (i - 1) as nat;
            assert(j < n);
            assert(a_col(n)[i] == acol_elt(n, j));
            lemma_rho_acol_elt(n, decls, j);
            assert(comp[i] == apply_hom(h, acol_elt(n, j)));
            assert(conj_family((n + 1) as nat)[i] == conj_word(i as nat));
            assert(i as nat == (j + 1) as nat);
        }
    }
}

/// `apply_hom(ρ, bcol_elt(n,j)) = conj_word_b(j+1)`  (for `j < n`).
proof fn lemma_rho_bcol_elt(n: nat, decls: Seq<Word>, j: nat)
    requires j < n,
    ensures apply_hom(rho(n, decls), bcol_elt(n, j)) =~= conj_word_b((j + 1) as nat),
{
    let h = rho(n, decls);
    let p = symbol_power(Symbol::Inv(n + 1), j + 1);
    let aw = seq![Symbol::Gen(n)];
    let q = symbol_power(Symbol::Gen(n + 1), j + 1);
    lemma_hom_respects_concat(h, p + aw, q);
    lemma_hom_respects_concat(h, p, aw);
    // b⁻⁽ʲ⁺¹⁾ ↦ Inv(1)⁽ʲ⁺¹⁾
    lemma_rho_sym_b_neg(n, decls);
    lemma_apply_hom_symbol_power_single(h, Symbol::Inv(n + 1), Symbol::Inv(1), (j + 1) as nat);
    // a ↦ [Gen(0)]
    lemma_rho_sym_a(n, decls);
    lemma_hom_singleton(h, Symbol::Gen(n));
    assert(seq![Symbol::Gen(n)] =~= Seq::new(1, |_i: int| Symbol::Gen(n)));
    assert(apply_hom(h, aw) =~= seq![Symbol::Gen(0)]);
    // b⁽ʲ⁺¹⁾ ↦ Gen(1)⁽ʲ⁺¹⁾
    lemma_rho_sym_b(n, decls);
    lemma_apply_hom_symbol_power_single(h, Symbol::Gen(n + 1), Symbol::Gen(1), (j + 1) as nat);
    assert(conj_word_b((j + 1) as nat)
        =~= symbol_power(Symbol::Inv(1), (j + 1) as nat)
            + seq![Symbol::Gen(0)]
            + symbol_power(Symbol::Gen(1), (j + 1) as nat));
}

/// `apply_hom_symbol(ρ, Inv(n+1)) = [Inv(1)]`  (inverse of the image of `b`).
proof fn lemma_rho_sym_b_neg(n: nat, decls: Seq<Word>)
    ensures apply_hom_symbol(rho(n, decls), Symbol::Inv(n + 1)) =~= seq![Symbol::Inv(1)],
{
    lemma_rho_imgs_b(n);
    assert(apply_hom_symbol(rho(n, decls), Symbol::Inv(n + 1))
        == inverse_word(rho_imgs(n)[(n + 1) as int]));
    assert(inverse_word(seq![Symbol::Gen(1)]) =~= seq![Symbol::Inv(1)]) by {
        assert(seq![Symbol::Gen(1)].drop_first().len() == 0);
        assert(inverse_word(seq![Symbol::Gen(1)].drop_first()) =~= empty_word());
        assert(inverse_symbol(Symbol::Gen(1)) == Symbol::Inv(1));
    }
}

/// `comp_images(ρ, b_col(n)) = conj_family_b(n+1)`.
proof fn lemma_rho_bcol_is_conj_family_b(n: nat, decls: Seq<Word>)
    ensures comp_images(rho(n, decls), b_col(n)) =~= conj_family_b((n + 1) as nat),
{
    let h = rho(n, decls);
    let comp = comp_images(h, b_col(n));
    assert(b_col(n).len() == n + 1);
    assert(comp.len() == n + 1);
    assert(conj_family_b((n + 1) as nat).len() == n + 1);
    assert forall|i: int| 0 <= i < n + 1 implies
        #[trigger] comp[i] =~= conj_family_b((n + 1) as nat)[i] by {
        if i == 0 {
            assert(b_col(n)[0] == seq![Symbol::Gen(n)]);
            lemma_rho_sym_a(n, decls);
            lemma_hom_singleton(h, Symbol::Gen(n));
            assert(seq![Symbol::Gen(n)] =~= Seq::new(1, |_i: int| Symbol::Gen(n)));
            assert(comp[0] =~= seq![Symbol::Gen(0)]);
            assert(conj_word_b(0) =~= seq![Symbol::Gen(0)]) by {
                assert(symbol_power(Symbol::Inv(1), 0) =~= empty_word());
                assert(symbol_power(Symbol::Gen(1), 0) =~= empty_word());
            }
            assert(conj_family_b((n + 1) as nat)[0] == conj_word_b(0));
        } else {
            let j = (i - 1) as nat;
            assert(j < n);
            assert(b_col(n)[i] == bcol_elt(n, j));
            lemma_rho_bcol_elt(n, decls, j);
            assert(comp[i] == apply_hom(h, bcol_elt(n, j)));
            assert(conj_family_b((n + 1) as nat)[i] == conj_word_b(i as nat));
            assert(i as nat == (j + 1) as nat);
        }
    }
}

// ===========================================================================
// 4. ρ is a valid homomorphism (it kills `decls`).
// ===========================================================================

/// ρ kills any word over the `n` c-generators: `apply_hom(ρ, w) = ε` when `word_valid(w, n)`.
proof fn lemma_rho_kills_c_word(n: nat, decls: Seq<Word>, w: Word)
    requires word_valid(w, n),
    ensures apply_hom(rho(n, decls), w) =~= empty_word(),
    decreases w.len(),
{
    let h = rho(n, decls);
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, n)) by { assert(w[0] == s); }
        assert(word_valid(rest, n)) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], n) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_rho_kills_c_word(n, decls, rest);
        // head symbol image is ε (Gen(j)↦ε, Inv(j)↦inverse_word(ε)=ε for j<n)
        match s {
            Symbol::Gen(j) => {
                assert(j < n);
                lemma_rho_imgs_c(n, j);
                assert(apply_hom_symbol(h, s) == rho_imgs(n)[j as int]);
            },
            Symbol::Inv(j) => {
                assert(j < n);
                lemma_rho_imgs_c(n, j);
                assert(apply_hom_symbol(h, s) == inverse_word(rho_imgs(n)[j as int]));
                assert(inverse_word(empty_word()) =~= empty_word());
            },
        }
        assert(apply_hom_symbol(h, s) =~= empty_word());
        assert(apply_hom(h, w) =~= concat(apply_hom_symbol(h, s), apply_hom(h, rest)));
    }
}

/// `l_slice(n, decls)` is a valid presentation with `n+2` generators (given `decls` valid over `n`).
proof fn lemma_l_slice_valid(n: nat, decls: Seq<Word>)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
    ensures
        presentation_valid(l_slice(n, decls)),
        l_slice(n, decls).num_generators == n + 2,
        l_slice(n, decls).relators =~= decls,
{
    reveal(presentation_valid);
    let p = l_slice(n, decls);
    assert(p.num_generators == n + 2);
    assert(free_group(2).relators.len() == 0);
    assert(shift_relators(free_group(2).relators, n).len() == 0);
    assert(p.relators =~= decls);
    assert forall|j: int| 0 <= j < p.relators.len()
        implies word_valid(#[trigger] p.relators[j], p.num_generators) by {
        assert(p.relators[j] == decls[j]);
        lemma_word_valid_mono(decls[j], n, (n + 2) as nat);
    }
}

/// ρ is a valid homomorphism `L → F₂`.
proof fn lemma_rho_valid(n: nat, decls: Seq<Word>)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
    ensures
        is_valid_homomorphism(rho(n, decls)),
{
    let h = rho(n, decls);
    lemma_l_slice_valid(n, decls);
    lemma_free_group_valid(2);
    lemma_rho_imgs_len(n);
    assert(h.generator_images.len() == h.source.num_generators);
    // images valid over the 2 target generators
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], 2) by {
        if i < n {
            lemma_rho_imgs_c(n, i as nat);
        } else if i == n {
            lemma_rho_imgs_a(n);
        } else {
            lemma_rho_imgs_b(n);
        }
    }
    // relator images ≡ ε: each relator is a decls word over the n c-gens ⟹ killed by ρ
    assert forall|i: int| #![trigger h.source.relators[i]] 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(h.target, apply_hom(h, h.source.relators[i]), empty_word()) by {
        assert(h.source.relators[i] == decls[i]);
        lemma_rho_kills_c_word(n, decls, decls[i]);
        lemma_equiv_refl(free_group(2), empty_word());
    }
}

// ===========================================================================
// 5. Column word-validity in `L^(N)`.
// ===========================================================================

proof fn lemma_single_gen_valid(g: nat, nn: nat)
    requires g < nn,
    ensures word_valid(seq![Symbol::Gen(g)], nn),
{
    assert forall|k: int| 0 <= k < seq![Symbol::Gen(g)].len()
        implies symbol_valid(#[trigger] seq![Symbol::Gen(g)][k], nn) by {
        assert(seq![Symbol::Gen(g)][k] == Symbol::Gen(g));
    }
}

proof fn lemma_acol_elt_valid(n: nat, j: nat)
    requires j < n,
    ensures word_valid(acol_elt(n, j), (n + 2) as nat),
{
    let nn = (n + 2) as nat;
    let cw = seq![Symbol::Gen(j)];
    let p = symbol_power(Symbol::Inv(n), j + 1);
    let bw = seq![Symbol::Gen(n + 1)];
    let q = symbol_power(Symbol::Gen(n), j + 1);
    lemma_single_gen_valid(j, nn);
    lemma_symbol_power_valid(Symbol::Inv(n), j + 1, nn);
    lemma_single_gen_valid((n + 1) as nat, nn);
    lemma_symbol_power_valid(Symbol::Gen(n), j + 1, nn);
    lemma_concat_word_valid(cw, p, nn);
    lemma_concat_word_valid(cw + p, bw, nn);
    lemma_concat_word_valid(cw + p + bw, q, nn);
    assert(acol_elt(n, j) =~= cw + p + bw + q);
}

proof fn lemma_bcol_elt_valid(n: nat, j: nat)
    ensures word_valid(bcol_elt(n, j), (n + 2) as nat),
{
    let nn = (n + 2) as nat;
    let p = symbol_power(Symbol::Inv(n + 1), j + 1);
    let aw = seq![Symbol::Gen(n)];
    let q = symbol_power(Symbol::Gen(n + 1), j + 1);
    lemma_symbol_power_valid(Symbol::Inv(n + 1), j + 1, nn);
    lemma_single_gen_valid(n, nn);
    lemma_symbol_power_valid(Symbol::Gen(n + 1), j + 1, nn);
    lemma_concat_word_valid(p, aw, nn);
    lemma_concat_word_valid(p + aw, q, nn);
    assert(bcol_elt(n, j) =~= p + aw + q);
}

proof fn lemma_acol_valid(n: nat)
    ensures forall|i: int| 0 <= i < a_col(n).len()
        ==> word_valid(#[trigger] a_col(n)[i], (n + 2) as nat),
{
    assert(a_col(n).len() == n + 1);
    assert forall|i: int| 0 <= i < a_col(n).len()
        implies word_valid(#[trigger] a_col(n)[i], (n + 2) as nat) by {
        if i == 0 {
            assert(a_col(n)[i] == seq![Symbol::Gen(n + 1)]);
            lemma_single_gen_valid((n + 1) as nat, (n + 2) as nat);
        } else {
            assert(a_col(n)[i] == acol_elt(n, (i - 1) as nat));
            lemma_acol_elt_valid(n, (i - 1) as nat);
        }
    }
}

proof fn lemma_bcol_valid(n: nat)
    ensures forall|i: int| 0 <= i < b_col(n).len()
        ==> word_valid(#[trigger] b_col(n)[i], (n + 2) as nat),
{
    assert(b_col(n).len() == n + 1);
    assert forall|i: int| 0 <= i < b_col(n).len()
        implies word_valid(#[trigger] b_col(n)[i], (n + 2) as nat) by {
        if i == 0 {
            assert(b_col(n)[i] == seq![Symbol::Gen(n)]);
            lemma_single_gen_valid(n, (n + 2) as nat);
        } else {
            assert(b_col(n)[i] == bcol_elt(n, (i - 1) as nat));
            lemma_bcol_elt_valid(n, (i - 1) as nat);
        }
    }
}

// ===========================================================================
// 6. THE PAYOFF — the two columns are free families in `L = C₀ ⋆ F₂`.
// ===========================================================================

/// **A-column free.** `{ b } ∪ { cⱼa⁻⁽ʲ⁺¹⁾ba⁽ʲ⁺¹⁾ : j<n }` is a free family in `L^(N)`.
pub proof fn lemma_acol_free(n: nat, decls: Seq<Word>)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
    ensures
        is_free_family(l_slice(n, decls), a_col(n)),
{
    let gp = l_slice(n, decls);
    lemma_l_slice_valid(n, decls);
    assert(gp.num_generators == n + 2);
    lemma_acol_valid(n);
    // clause 1: images valid
    assert(forall|i: int| 0 <= i < a_col(n).len()
        ==> word_valid(#[trigger] a_col(n)[i], gp.num_generators));
    // clause 2: a relation trivial in L pushes (via ρ) to a relation among the free conj_family
    assert forall|w: Word| (#[trigger] word_valid(w, a_col(n).len())
        && equiv_in_presentation(gp, apply_embedding(a_col(n), w), empty_word()))
        implies equiv_in_presentation(free_group(a_col(n).len()), w, empty_word()) by {
        let h = rho(n, decls);
        lemma_rho_valid(n, decls);
        // pullback: trivial in L ⟹ apply_embedding(comp_images(ρ, a_col), w) trivial in F₂
        lemma_pullback_free(h, a_col(n), w);
        lemma_rho_acol_is_conj_family(n, decls);
        // comp_images(ρ, a_col) = conj_family(n+1), so the relation is among conj_family
        assert(apply_embedding(comp_images(h, a_col(n)), w)
            == apply_embedding(conj_family((n + 1) as nat), w));
        assert(equiv_in_presentation(free_group(2),
            apply_embedding(conj_family((n + 1) as nat), w), empty_word()));
        // conj_family(n+1) is free ⟹ w trivial in the abstract free group
        lemma_conj_family_free((n + 1) as nat);
        assert(conj_family((n + 1) as nat).len() == n + 1);
        assert(a_col(n).len() == n + 1);
        // fire conj_family's free-family clause-2 at w
        assert(word_valid(w, conj_family((n + 1) as nat).len()));
    }
}

/// **B-column free.** `{ a } ∪ { b⁻⁽ʲ⁺¹⁾ab⁽ʲ⁺¹⁾ : j<n }` is a free family in `L^(N)`.
pub proof fn lemma_bcol_free(n: nat, decls: Seq<Word>)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
    ensures
        is_free_family(l_slice(n, decls), b_col(n)),
{
    let gp = l_slice(n, decls);
    lemma_l_slice_valid(n, decls);
    assert(gp.num_generators == n + 2);
    lemma_bcol_valid(n);
    assert(forall|i: int| 0 <= i < b_col(n).len()
        ==> word_valid(#[trigger] b_col(n)[i], gp.num_generators));
    assert forall|w: Word| (#[trigger] word_valid(w, b_col(n).len())
        && equiv_in_presentation(gp, apply_embedding(b_col(n), w), empty_word()))
        implies equiv_in_presentation(free_group(b_col(n).len()), w, empty_word()) by {
        let h = rho(n, decls);
        lemma_rho_valid(n, decls);
        lemma_pullback_free(h, b_col(n), w);
        lemma_rho_bcol_is_conj_family_b(n, decls);
        assert(apply_embedding(comp_images(h, b_col(n)), w)
            == apply_embedding(conj_family_b((n + 1) as nat), w));
        assert(equiv_in_presentation(free_group(2),
            apply_embedding(conj_family_b((n + 1) as nat), w), empty_word()));
        lemma_conj_family_b_free((n + 1) as nat);
        assert(conj_family_b((n + 1) as nat).len() == n + 1);
        assert(b_col(n).len() == n + 1);
        assert(word_valid(w, conj_family_b((n + 1) as nat).len()));
    }
}

} // verus!
