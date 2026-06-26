// Layer 2 — Cohen §1 assembly, brick CS-4b: the COMPACTNESS BRIDGE.
//
// `docs/cohen-cs4-architecture.md` §4 (CS-4b). The forward/backward faithfulness halves of the
// a_i iso (CS-4c/d) reuse the REAL finite directional lemmas `lemma_map_a_forward` /
// `lemma_mapb_M2_rt`, which live over a FINITE family-(II) slice `h2_II(alphas)`. CS-4b is the
// reduction that lets us hand them a finite slice: a word `u` (c-free, over `a_col`/`b_col`
// generators) trivial in the infinite predicate base `h2_pred` is trivial in SOME finite slice
// `h2_II(alphas)`.
//
// Two stages (`docs/cohen-cs4-architecture.md` §4 CS-4b (1)(2)(3)):
//
//   Part 1 — STRIP `S`.  A finite predicate derivation `u →* ε` in `h2_pred` may use the abstract
//     c-block relators `S` of `C = ⟨c;S⟩`.  The homomorphism `s_strip` (kill every c generator,
//     fix every non-c generator) maps `h2_pred → h2_noS_pred` (the predicate base WITHOUT `S`):
//     each K_M / family-(II) relator (c-free) maps to itself, each comm relator `b_i c_j b_i⁻¹
//     c_j⁻¹` maps to `b_i b_i⁻¹ ≡ ε`, each `S` relator (pure-c) maps to `ε`.  Since `u` is c-free,
//     `s_strip` FIXES it, so `u ≡_{h2_noS_pred} ε`.  This is the dual of CS-2's c-retraction.
//
//   Part 2 — COMPACTNESS.  A finite predicate derivation `u →* ε` in `h2_noS_pred` uses finitely
//     many relators, each a K_M relator, a comm relator, or a family-(II) relator
//     `family_II_relator(β)` (β a number word).  Threading the derivation, we accumulate the used
//     `β`'s into `alphas` and replay each step over the finite `h2_II(alphas)`: K_M/comm relators
//     are present in `h2_II(alphas)` for every `alphas` (they sit in `h2_pres`), and each used
//     family-(II) relator is added to `alphas` exactly when first encountered (lifting the tail's
//     equivalence over the larger slice by `add_relator` monotonicity).
//
// Additive/reversible (new module + one lib.rs line); no regression.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::pred_presentation::*;
use crate::presentation_lemmas::{extends_presentation, lemma_quotient_preserves_equiv};
use crate::quotient::{add_relator, lemma_add_relator_extends};
use crate::base_swap::lemma_add_relators_relators;
use crate::pred_homomorphism::*;
use crate::pred_presentation_lemmas::{lemma_pred_relator_is_identity, lemma_pred_word_inverse_right};
use crate::machine_group::*;
use crate::layout::*;
use crate::word_numbering::numbers_word;
use crate::h1::{h1_base, comm_relators, comm_relator, lemma_comm_relators_valid};
use crate::h2::{h2_pres, h2_data};
use crate::hnn::{hnn_relators};
use crate::h3_ii::{h2_II, family_II, family_II_relator, lemma_family_II_relator_valid};
use crate::cohen_h2::{h2_pred, h2_pred_relator, is_family_ii, s_relators_valid,
    is_c_word, c_symbol, lemma_c_word_valid};
use crate::cohen_retraction::{no_c_word, lemma_low_word_no_c, lemma_family_ii_no_c};

verus! {

// ============================================================================
// PART 1 — the S-stripping homomorphism `s_strip : h2_pred → h2_noS_pred`
// ============================================================================

// ----------------------------------------------------------------------------
// `h2_noS_pred` — the predicate base WITHOUT the abstract relator set `S`
// ----------------------------------------------------------------------------

/// `h2_pred` with the `is_S` clause removed: a K_M relator, OR a `b_i c_j = c_j b_i`
/// commutator, OR a family-(II) relator. The target of `s_strip` (the relator classes
/// that survive killing the c-block).
pub open spec fn h2_noS_pred_relator(mm: ModMachine, n: nat, m: nat, w: Word) -> bool {
    let nk = g_m(mm).num_generators;
    g_m(mm).relators.contains(w)
    || comm_relators(nk, n).contains(w)
    || is_family_ii(mm, n, m, w)
}

/// `H₂ without S` as a `PredPresentation` — same generators as `h2_pred`, relators =
/// `h2_noS_pred_relator`. The compactness target (Part 2) is a finite slice of this.
pub open spec fn h2_noS_pred(mm: ModMachine, n: nat, m: nat) -> PredPresentation {
    PredPresentation {
        num_generators: h2_num_gens(g_m(mm).num_generators, n),
        relators: |w: Word| h2_noS_pred_relator(mm, n, m, w),
    }
}

// ----------------------------------------------------------------------------
// The homomorphism and its symbol/word action
// ----------------------------------------------------------------------------

/// `s_strip : h2_pred → h2_noS_pred`: `c_j ↦ ε`, every non-c generator `↦ itself`. The dual
/// of CS-2's `c_retraction` (which keeps c, kills the rest).
pub open spec fn s_strip(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool,
) -> PredHomomorphismData {
    let nk = g_m(mm).num_generators;
    PredHomomorphismData {
        source: h2_pred(mm, n, m, is_S),
        target: h2_noS_pred(mm, n, m),
        generator_images: Seq::new(h2_num_gens(nk, n), |g: int| {
            if c_base(nk) <= g < c_base(nk) + n {
                empty_word()
            } else {
                Seq::new(1, |_j: int| Symbol::Gen(g as nat))
            }
        }),
    }
}

/// `s_strip` kills a c-block symbol: `apply_hom_symbol_pred(s_strip, s) = ε`.
pub proof fn lemma_strip_symbol_c(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, s: Symbol)
    requires
        c_symbol(g_m(mm).num_generators, n, s),
    ensures
        apply_hom_symbol_pred(s_strip(mm, n, m, is_S), s) =~= empty_word(),
{
    let nk = g_m(mm).num_generators;
    let h = s_strip(mm, n, m, is_S);
    let g = generator_index(s);
    assert(c_base(nk) <= g < c_base(nk) + n);
    assert(g < h2_num_gens(nk, n));
    assert(h.generator_images[g as int] =~= empty_word());
    match s {
        Symbol::Gen(gg) => {
            assert(apply_hom_symbol_pred(h, s) == h.generator_images[gg as int]);
        }
        Symbol::Inv(gg) => {
            assert(apply_hom_symbol_pred(h, s) == inverse_word(h.generator_images[gg as int]));
            assert(inverse_word(empty_word()) =~= empty_word());
        }
    }
}

/// `s_strip` fixes a non-c symbol: `apply_hom_symbol_pred(s_strip, s) = [s]`.
pub proof fn lemma_strip_symbol_noc(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, s: Symbol)
    requires
        !c_symbol(g_m(mm).num_generators, n, s),
        symbol_valid(s, h2_num_gens(g_m(mm).num_generators, n)),
    ensures
        apply_hom_symbol_pred(s_strip(mm, n, m, is_S), s) =~= Seq::new(1, |_j: int| s),
{
    let nk = g_m(mm).num_generators;
    let h = s_strip(mm, n, m, is_S);
    let g = generator_index(s);
    assert(g < h2_num_gens(nk, n));
    assert(!(c_base(nk) <= g < c_base(nk) + n));
    assert(h.generator_images[g as int] =~= Seq::new(1, |_j: int| Symbol::Gen(g)));
    match s {
        Symbol::Gen(gg) => {
            assert(gg == g);
            assert(apply_hom_symbol_pred(h, s) == h.generator_images[gg as int]);
            assert(Seq::new(1, |_j: int| s) =~= Seq::new(1, |_j: int| Symbol::Gen(g)));
        }
        Symbol::Inv(gg) => {
            assert(gg == g);
            assert(apply_hom_symbol_pred(h, s) == inverse_word(h.generator_images[gg as int]));
            lemma_inverse_singleton(Symbol::Gen(g));
            assert(inverse_symbol(Symbol::Gen(g)) == Symbol::Inv(g));
            assert(inverse_word(Seq::new(1, |_j: int| Symbol::Gen(g)))
                =~= Seq::new(1, |_j: int| Symbol::Inv(g)));
            assert(Seq::new(1, |_j: int| s) =~= Seq::new(1, |_j: int| Symbol::Inv(g)));
        }
    }
}

/// `s_strip` fixes any c-symbol-free word.
pub proof fn lemma_strip_fixes_noc_word(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word)
    requires
        word_valid(w, h2_num_gens(g_m(mm).num_generators, n)),
        no_c_word(g_m(mm).num_generators, n, w),
    ensures
        apply_hom_pred(s_strip(mm, n, m, is_S), w) =~= w,
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let h = s_strip(mm, n, m, is_S);
    if w.len() == 0 {
        assert(w =~= empty_word());
    } else {
        let rest = w.drop_first();
        assert(!c_symbol(nk, n, w.first())) by { assert(w[0] == w.first()); }
        assert(symbol_valid(w.first(), h2_num_gens(nk, n))) by { assert(w[0] == w.first()); }
        lemma_strip_symbol_noc(mm, n, m, is_S, w.first());
        assert(word_valid(rest, h2_num_gens(nk, n))) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(#[trigger] rest[i], h2_num_gens(nk, n)) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        assert(no_c_word(nk, n, rest)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies !c_symbol(nk, n, #[trigger] rest[i]) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_strip_fixes_noc_word(mm, n, m, is_S, rest);
        assert(apply_hom_pred(h, w)
            =~= concat(apply_hom_symbol_pred(h, w.first()), apply_hom_pred(h, rest)));
        assert(concat(Seq::new(1, |_j: int| w.first()), rest) =~= w);
    }
}

/// `s_strip` kills any pure-c word.
pub proof fn lemma_strip_kills_c_word(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word)
    requires
        is_c_word(g_m(mm).num_generators, n, w),
    ensures
        apply_hom_pred(s_strip(mm, n, m, is_S), w) =~= empty_word(),
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let h = s_strip(mm, n, m, is_S);
    if w.len() == 0 {
    } else {
        let rest = w.drop_first();
        assert(c_symbol(nk, n, w.first())) by { assert(w[0] == w.first()); }
        lemma_strip_symbol_c(mm, n, m, is_S, w.first());
        assert(is_c_word(nk, n, rest)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies c_symbol(nk, n, #[trigger] rest[i]) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_strip_kills_c_word(mm, n, m, is_S, rest);
        assert(apply_hom_pred(h, w)
            =~= concat(apply_hom_symbol_pred(h, w.first()), apply_hom_pred(h, rest)));
    }
}

// ----------------------------------------------------------------------------
// `s_strip` validity (every relator class ↦ identity of `h2_noS_pred`)
// ----------------------------------------------------------------------------

/// `h2_noS_pred` is a valid presentation (each surviving relator class is `word_valid`).
pub proof fn lemma_h2_noS_pred_valid(mm: ModMachine, n: nat, m: nat)
    requires
        2 * n < m,
    ensures
        pred_presentation_valid(h2_noS_pred(mm, n, m)),
{
    reveal(pred_presentation_valid);
    let nk = g_m(mm).num_generators;
    let ng = h2_num_gens(nk, n);
    let p = h2_noS_pred(mm, n, m);
    assert(p.num_generators == ng);
    assert forall|w: Word| #![trigger (p.relators)(w)] (p.relators)(w) implies word_valid(w, ng) by {
        assert((p.relators)(w) == h2_noS_pred_relator(mm, n, m, w));
        assert(h2_noS_pred_relator(mm, n, m, w));
        if g_m(mm).relators.contains(w) {
            reveal(presentation_valid);
            lemma_g_m_valid(mm);
            let i = choose|i: int| 0 <= i < g_m(mm).relators.len() && g_m(mm).relators[i] == w;
            assert(word_valid(g_m(mm).relators[i], nk));
            lemma_word_valid_mono(w, nk, ng);
        } else if comm_relators(nk, n).contains(w) {
            lemma_comm_relators_valid(nk, n, ng);
            let i = choose|i: int| 0 <= i < comm_relators(nk, n).len() && comm_relators(nk, n)[i] == w;
            assert(word_valid(comm_relators(nk, n)[i], ng));
        } else {
            assert(is_family_ii(mm, n, m, w));
            let beta = choose|beta: nat| numbers_word(n, m, beta) && w == family_II_relator(mm, n, m, beta);
            lemma_family_II_relator_valid(mm, n, m, beta, ng);
        }
    }
}

/// The image of the comm relator `b_i c_j b_i⁻¹ c_j⁻¹` under `s_strip` is `b_i b_i⁻¹ ≡ ε`.
pub proof fn lemma_comm_relator_image_strip(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, i: nat, j: nat,
)
    requires
        1 <= i <= n, 1 <= j <= n,
    ensures
        equiv_in_pred_presentation(h2_noS_pred(mm, n, m),
            apply_hom_pred(s_strip(mm, n, m, is_S), comm_relator(g_m(mm).num_generators, n, i, j)),
            empty_word()),
{
    let nk = g_m(mm).num_generators;
    let h = s_strip(mm, n, m, is_S);
    let tp = h2_noS_pred(mm, n, m);
    let bg = b_idx(nk, n, i);                // non-c
    let cg = c_idx(nk, j);                   // c-block
    let sb = Seq::new(1, |_k: int| Symbol::Gen(bg));
    let sc = Seq::new(1, |_k: int| Symbol::Gen(cg));
    let sbi = Seq::new(1, |_k: int| Symbol::Inv(bg));
    let sci = Seq::new(1, |_k: int| Symbol::Inv(cg));
    let comm = comm_relator(nk, n, i, j);
    assert(comm =~= sb + sc + sbi + sci);

    // index facts
    assert(bg == nk + n + (i - 1));
    assert(cg == nk + (j - 1));
    assert(!c_symbol(nk, n, Symbol::Gen(bg)));
    assert(!c_symbol(nk, n, Symbol::Inv(bg)));
    assert(c_symbol(nk, n, Symbol::Gen(cg)));
    assert(c_symbol(nk, n, Symbol::Inv(cg)));
    assert(symbol_valid(Symbol::Gen(bg), h2_num_gens(nk, n)));
    assert(symbol_valid(Symbol::Inv(bg), h2_num_gens(nk, n)));

    // per-symbol images: b ↦ itself, c ↦ ε
    lemma_strip_symbol_noc(mm, n, m, is_S, Symbol::Gen(bg));   // [Gen(bg)]
    lemma_strip_symbol_noc(mm, n, m, is_S, Symbol::Inv(bg));   // [Inv(bg)]
    lemma_strip_symbol_c(mm, n, m, is_S, Symbol::Gen(cg));     // ε
    lemma_strip_symbol_c(mm, n, m, is_S, Symbol::Inv(cg));     // ε
    lemma_hom_pred_singleton(h, Symbol::Gen(bg));
    lemma_hom_pred_singleton(h, Symbol::Inv(bg));
    lemma_hom_pred_singleton(h, Symbol::Gen(cg));
    lemma_hom_pred_singleton(h, Symbol::Inv(cg));

    // apply over the concatenation: [Gen(bg)] + ε + [Inv(bg)] + ε = [Gen(bg), Inv(bg)]
    lemma_hom_pred_respects_concat(h, sb + sc + sbi, sci);
    lemma_hom_pred_respects_concat(h, sb + sc, sbi);
    lemma_hom_pred_respects_concat(h, sb, sc);
    assert(apply_hom_pred(h, comm) =~= concat(sb, sbi));

    // [Gen(bg), Inv(bg)] = sb + inverse_word(sb) ≡ ε
    assert(sbi =~= inverse_word(sb));
    lemma_pred_word_inverse_right(tp, sb);
    assert(concat(sb, inverse_word(sb)) =~= concat(sb, sbi));
}

/// `s_strip` is a valid homomorphism: every `h2_pred` relator maps to an identity of `h2_noS_pred`.
pub proof fn lemma_s_strip_valid(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        is_valid_pred_homomorphism(s_strip(mm, n, m, is_S)),
{
    let nk = g_m(mm).num_generators;
    let ng = h2_num_gens(nk, n);
    let h = s_strip(mm, n, m, is_S);
    let tp = h2_noS_pred(mm, n, m);
    crate::cohen_h2::lemma_h2_pred_valid(mm, n, m, is_S);
    lemma_h2_noS_pred_valid(mm, n, m);
    assert(h.generator_images.len() == ng);
    assert(h.source.num_generators == ng);

    // generator-image validity
    assert forall|g: int| 0 <= g < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[g], tp.num_generators) by {
        if c_base(nk) <= g < c_base(nk) + n {
            assert(h.generator_images[g] =~= empty_word());
        } else {
            assert(h.generator_images[g] =~= Seq::new(1, |_k: int| Symbol::Gen(g as nat)));
            assert(word_valid(h.generator_images[g], ng)) by {
                assert(h.generator_images[g][0] == Symbol::Gen(g as nat));
            }
        }
    }

    // relator-image clause
    assert forall|w: Word| #![trigger (h.source.relators)(w)] (h.source.relators)(w) implies
        equiv_in_pred_presentation(tp, apply_hom_pred(h, w), empty_word()) by {
        assert((h.source.relators)(w) == h2_pred_relator(mm, n, m, is_S, w));
        assert(h2_pred_relator(mm, n, m, is_S, w));
        if g_m(mm).relators.contains(w) {
            reveal(presentation_valid);
            lemma_g_m_valid(mm);
            let idx = choose|idx: int| 0 <= idx < g_m(mm).relators.len() && g_m(mm).relators[idx] == w;
            assert(word_valid(g_m(mm).relators[idx], nk));
            lemma_low_word_no_c(nk, n, w);
            lemma_word_valid_mono(w, nk, ng);
            lemma_strip_fixes_noc_word(mm, n, m, is_S, w);
            assert((tp.relators)(w));
            lemma_pred_relator_is_identity(tp, w);
        } else if comm_relators(nk, n).contains(w) {
            let idx = choose|idx: int|
                0 <= idx < comm_relators(nk, n).len() && comm_relators(nk, n)[idx] == w;
            assert(comm_relators(nk, n).len() == n * n);
            assert(n > 0) by { if n == 0 { assert(n * n == 0); } }
            vstd::arithmetic::div_mod::lemma_multiply_divide_lt(idx, n as int, n as int);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(idx, n as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(idx, n as int);
            let ii = (idx / (n as int) + 1) as nat;
            let jj = (idx % (n as int) + 1) as nat;
            assert(w == comm_relator(nk, n, ii, jj));
            lemma_comm_relator_image_strip(mm, n, m, is_S, ii, jj);
        } else if is_S(w) {
            assert(is_c_word(nk, n, w));
            lemma_strip_kills_c_word(mm, n, m, is_S, w);
            lemma_pred_equiv_refl(tp, empty_word());
        } else {
            assert(is_family_ii(mm, n, m, w));
            let beta = choose|beta: nat| numbers_word(n, m, beta) && w == family_II_relator(mm, n, m, beta);
            lemma_family_ii_no_c(mm, n, m, beta);
            lemma_family_II_relator_valid(mm, n, m, beta, ng);
            lemma_strip_fixes_noc_word(mm, n, m, is_S, w);
            assert((tp.relators)(w));
            lemma_pred_relator_is_identity(tp, w);
        }
    }
}

/// **Part 1 headline — the S-strip descent.** A c-free word `u` trivial in `h2_pred` is trivial
/// in `h2_noS_pred` (the predicate base without `S`).
pub proof fn lemma_s_strip_descends(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, u: Word,
)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        no_c_word(g_m(mm).num_generators, n, u),
        word_valid(u, h2_num_gens(g_m(mm).num_generators, n)),
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), u, empty_word()),
    ensures
        equiv_in_pred_presentation(h2_noS_pred(mm, n, m), u, empty_word()),
{
    let h = s_strip(mm, n, m, is_S);
    lemma_s_strip_valid(mm, n, m, is_S);
    assert(h.source == h2_pred(mm, n, m, is_S));
    lemma_hom_pred_preserves_equiv(h, u, empty_word());
    lemma_strip_fixes_noc_word(mm, n, m, is_S, u);
    assert(apply_hom_pred(h, empty_word()) =~= empty_word());
}

// ============================================================================
// PART 2 — compactness: a finite `h2_noS_pred` derivation lifts to a finite slice
// ============================================================================

// ----------------------------------------------------------------------------
// `Seq::contains` is preserved by concatenation (both sides)
// ----------------------------------------------------------------------------

proof fn lemma_concat_contains_left(a: Seq<Word>, c: Seq<Word>, x: Word)
    requires
        a.contains(x),
    ensures
        (a + c).contains(x),
{
    let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
    assert((a + c)[i] == a[i]);
    assert(0 <= i < (a + c).len());
}

proof fn lemma_concat_contains_right(a: Seq<Word>, c: Seq<Word>, x: Word)
    requires
        c.contains(x),
    ensures
        (a + c).contains(x),
{
    let i = choose|i: int| 0 <= i < c.len() && c[i] == x;
    assert((a + c)[a.len() + i] == c[i]);
    assert(0 <= a.len() + i < (a + c).len());
}

// ----------------------------------------------------------------------------
// The relator structure of `h2_II(alphas)` and the three membership facts
// ----------------------------------------------------------------------------

/// `h2_II(alphas).relators = ((g_m.relators + comm) + hnn_relators(h2_data)) + family_II(alphas)`.
/// Also: its generator count is exactly `h2_noS_pred`'s.
pub proof fn lemma_h2_II_relators_eq(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    ensures
        h2_II(mm, n, m, alphas).relators
            =~= ((g_m(mm).relators + comm_relators(g_m(mm).num_generators, n))
                + hnn_relators(h2_data(mm, n))) + family_II(mm, n, m, alphas),
        h2_II(mm, n, m, alphas).num_generators
            == h2_num_gens(g_m(mm).num_generators, n),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    // h2_II = add_relators(h2_pres, family_II): num/relators split.
    lemma_add_relators_relators(h2_pres(mm, n), family_II(mm, n, m, alphas));
    // h2_pres = hnn_presentation(h2_data): relators = h1_base.relators + hnn_relators(h2_data).
    assert(h2_pres(mm, n).relators =~= h1_base(mm, n).relators + hnn_relators(h2_data(mm, n)));
    // h1_base.relators = g_m.relators + comm_relators.
    assert(h1_base(mm, n).relators =~= g_m(mm).relators + comm_relators(nk, n));
    crate::h2::lemma_h2_num_generators(mm, n);
}

pub proof fn lemma_h2_II_contains_gm(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        g_m(mm).relators.contains(w),
    ensures
        h2_II(mm, n, m, alphas).relators.contains(w),
{
    let nk = g_m(mm).num_generators;
    lemma_h2_II_relators_eq(mm, n, m, alphas);
    let g = g_m(mm).relators;
    let c = comm_relators(nk, n);
    let h = hnn_relators(h2_data(mm, n));
    let f = family_II(mm, n, m, alphas);
    lemma_concat_contains_left(g, c, w);
    lemma_concat_contains_left(g + c, h, w);
    lemma_concat_contains_left((g + c) + h, f, w);
}

proof fn lemma_h2_II_contains_comm(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        comm_relators(g_m(mm).num_generators, n).contains(w),
    ensures
        h2_II(mm, n, m, alphas).relators.contains(w),
{
    let nk = g_m(mm).num_generators;
    lemma_h2_II_relators_eq(mm, n, m, alphas);
    let g = g_m(mm).relators;
    let c = comm_relators(nk, n);
    let h = hnn_relators(h2_data(mm, n));
    let f = family_II(mm, n, m, alphas);
    lemma_concat_contains_right(g, c, w);
    lemma_concat_contains_left(g + c, h, w);
    lemma_concat_contains_left((g + c) + h, f, w);
}

proof fn lemma_h2_II_contains_family(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        family_II(mm, n, m, alphas).contains(w),
    ensures
        h2_II(mm, n, m, alphas).relators.contains(w),
{
    let nk = g_m(mm).num_generators;
    lemma_h2_II_relators_eq(mm, n, m, alphas);
    let g = g_m(mm).relators;
    let c = comm_relators(nk, n);
    let h = hnn_relators(h2_data(mm, n));
    let f = family_II(mm, n, m, alphas);
    lemma_concat_contains_right((g + c) + h, f, w);
}

// ----------------------------------------------------------------------------
// Step classification helpers
// ----------------------------------------------------------------------------

/// The relator word carried by a step (sentinel `ε` for free steps — never read).
pub open spec fn step_relator(step: PredDerivationStep) -> Word {
    match step {
        PredDerivationStep::RelatorInsert { relator, .. } => relator,
        PredDerivationStep::RelatorDelete { relator, .. } => relator,
        _ => empty_word(),
    }
}

/// Whether a step is a relator insert/delete.
pub open spec fn is_relator_step(step: PredDerivationStep) -> bool {
    match step {
        PredDerivationStep::RelatorInsert { .. } => true,
        PredDerivationStep::RelatorDelete { .. } => true,
        _ => false,
    }
}

/// The replay condition: a relator step's word must be a relator of the finite target.
pub open spec fn step_relator_in(fp: Presentation, step: PredDerivationStep) -> bool {
    !is_relator_step(step) || fp.relators.contains(step_relator(step))
}

// ----------------------------------------------------------------------------
// The generic single-step lifter: a `pp` step replays as a finite `fp` derivation
// ----------------------------------------------------------------------------

/// If a predicate step takes `start → next` over `pp`, and (for relator steps) its relator word
/// is a relator of the finite `fp` (with matching generator count), then `start ≡_{fp} next`.
proof fn lemma_finite_step_from_pred(
    fp: Presentation, pp: PredPresentation, start: Word, step: PredDerivationStep, next: Word,
)
    requires
        fp.num_generators == pp.num_generators,
        apply_step_pred(pp, start, step) == Some(next),
        step_relator_in(fp, step),
    ensures
        equiv_in_presentation(fp, start, next),
{
    let fstep: DerivationStep = match step {
        PredDerivationStep::FreeReduce { position } =>
            DerivationStep::FreeReduce { position },
        PredDerivationStep::FreeExpand { position, symbol } =>
            DerivationStep::FreeExpand { position, symbol },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            let idx = choose|k: int| 0 <= k < fp.relators.len() && fp.relators[k] == relator;
            DerivationStep::RelatorInsert { position, relator_index: idx as nat, inverted }
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            let idx = choose|k: int| 0 <= k < fp.relators.len() && fp.relators[k] == relator;
            DerivationStep::RelatorDelete { position, relator_index: idx as nat, inverted }
        },
    };

    // Each branch: apply_step(fp, start, fstep) == Some(next).
    match step {
        PredDerivationStep::FreeReduce { position } => {
            assert(apply_step(fp, start, fstep) == Some(next));
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
            assert(apply_step(fp, start, fstep) == Some(next));
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            assert(is_relator_step(step) && step_relator(step) == relator);
            assert(fp.relators.contains(relator));
            let idx = choose|k: int| 0 <= k < fp.relators.len() && fp.relators[k] == relator;
            assert(fp.relators[idx] == relator);
            assert(get_relator(fp, idx as nat, inverted) == get_relator_pred(relator, inverted));
            assert(apply_step(fp, start, fstep) == Some(next));
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            assert(is_relator_step(step) && step_relator(step) == relator);
            assert(fp.relators.contains(relator));
            let idx = choose|k: int| 0 <= k < fp.relators.len() && fp.relators[k] == relator;
            assert(fp.relators[idx] == relator);
            assert(get_relator(fp, idx as nat, inverted) == get_relator_pred(relator, inverted));
            assert(apply_step(fp, start, fstep) == Some(next));
        },
    }

    let d = Derivation { steps: Seq::new(1, |_i: int| fstep) };
    assert(d.steps.len() == 1);
    assert(d.steps.first() == fstep);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(fp, d.steps.drop_first(), next) == Some(next));
    assert(derivation_produces(fp, d.steps, start) == Some(next));
    assert(derivation_valid(fp, d, start, next));
}

// ----------------------------------------------------------------------------
// Slice-extension monotonicity: `h2_II(alphas_rest) → h2_II(alphas_rest.push(β))`
// ----------------------------------------------------------------------------

/// `family_II(alphas.push(β)) = family_II(alphas).push(family_II_relator(β))`.
proof fn lemma_family_II_push(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, beta: nat)
    ensures
        family_II(mm, n, m, alphas.push(beta))
            =~= family_II(mm, n, m, alphas).push(family_II_relator(mm, n, m, beta)),
{
    let lhs = family_II(mm, n, m, alphas.push(beta));
    let rhs = family_II(mm, n, m, alphas).push(family_II_relator(mm, n, m, beta));
    assert(lhs.len() == rhs.len());
    assert forall|i: int| 0 <= i < lhs.len() implies lhs[i] == rhs[i] by {
        if i < alphas.len() {
            assert(alphas.push(beta)[i] == alphas[i]);
        } else {
            assert(alphas.push(beta)[i] == beta);
        }
    }
}

/// `h2_II(alphas.push(β))` is `add_relator(h2_II(alphas), family_II_relator(β))` (up to relators),
/// hence extends it — so any `h2_II(alphas)`-equivalence lifts to the larger slice.
proof fn lemma_h2_II_extends_push(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, beta: nat)
    ensures
        extends_presentation(h2_II(mm, n, m, alphas), h2_II(mm, n, m, alphas.push(beta))),
{
    let rel = family_II_relator(mm, n, m, beta);
    let small = h2_II(mm, n, m, alphas);
    let big = h2_II(mm, n, m, alphas.push(beta));
    lemma_add_relators_relators(h2_pres(mm, n), family_II(mm, n, m, alphas));
    lemma_add_relators_relators(h2_pres(mm, n), family_II(mm, n, m, alphas.push(beta)));
    lemma_family_II_push(mm, n, m, alphas, beta);
    // big.relators = h2_pres.relators + family_II(alphas).push(rel) = (h2_pres + family_II(alphas)).push(rel)
    assert(h2_pres(mm, n).relators + family_II(mm, n, m, alphas).push(rel)
        =~= (h2_pres(mm, n).relators + family_II(mm, n, m, alphas)).push(rel));
    assert(big.relators =~= small.relators.push(rel));
    assert(big == add_relator(small, rel));
    lemma_add_relator_extends(small, rel);
}

// ----------------------------------------------------------------------------
// The relator-step arm: extend `alphas` (only for family-II), lift the tail
// ----------------------------------------------------------------------------

proof fn lemma_relator_arm(
    mm: ModMachine, n: nat, m: nat,
    start: Word, step: PredDerivationStep, next: Word, end: Word,
    alphas_rest: Seq<nat>, relator: Word,
)
    requires
        is_relator_step(step),
        step_relator(step) == relator,
        apply_step_pred(h2_noS_pred(mm, n, m), start, step) == Some(next),
        (h2_noS_pred(mm, n, m).relators)(relator),
        forall|i: int| 0 <= i < alphas_rest.len() ==> numbers_word(n, m, #[trigger] alphas_rest[i]),
        equiv_in_presentation(h2_II(mm, n, m, alphas_rest), next, end),
    ensures
        exists|alphas: Seq<nat>|
            (forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(h2_II(mm, n, m, alphas), start, end),
{
    let nk = g_m(mm).num_generators;
    let pp = h2_noS_pred(mm, n, m);
    assert(h2_noS_pred_relator(mm, n, m, relator));

    if g_m(mm).relators.contains(relator) {
        let alphas = alphas_rest;
        let fp = h2_II(mm, n, m, alphas);
        lemma_h2_II_contains_gm(mm, n, m, alphas, relator);
        lemma_h2_II_relators_eq(mm, n, m, alphas);
        lemma_finite_step_from_pred(fp, pp, start, step, next);
        lemma_equiv_transitive(fp, start, next, end);
        assert((forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(fp, start, end));
    } else if comm_relators(nk, n).contains(relator) {
        let alphas = alphas_rest;
        let fp = h2_II(mm, n, m, alphas);
        lemma_h2_II_contains_comm(mm, n, m, alphas, relator);
        lemma_h2_II_relators_eq(mm, n, m, alphas);
        lemma_finite_step_from_pred(fp, pp, start, step, next);
        lemma_equiv_transitive(fp, start, next, end);
        assert((forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(fp, start, end));
    } else {
        assert(is_family_ii(mm, n, m, relator));
        let beta = choose|beta: nat| numbers_word(n, m, beta) && relator == family_II_relator(mm, n, m, beta);
        let alphas = alphas_rest.push(beta);
        let fp = h2_II(mm, n, m, alphas);

        // numbers_word for the extended slice
        assert forall|i: int| 0 <= i < alphas.len() implies numbers_word(n, m, #[trigger] alphas[i]) by {
            if i < alphas_rest.len() {
                assert(alphas[i] == alphas_rest[i]);
            } else {
                assert(alphas[i] == beta);
            }
        }

        // family_II(alphas) contains the relator (last position)
        assert(family_II(mm, n, m, alphas).contains(relator)) by {
            let k = alphas.len() - 1;
            assert(alphas[k] == beta);
            assert(family_II(mm, n, m, alphas)[k] == family_II_relator(mm, n, m, beta));
            assert(family_II(mm, n, m, alphas)[k] == relator);
        }
        lemma_h2_II_contains_family(mm, n, m, alphas, relator);
        lemma_h2_II_relators_eq(mm, n, m, alphas);

        // start ≡ next over the larger slice
        lemma_finite_step_from_pred(fp, pp, start, step, next);

        // lift the tail next ≡ end from alphas_rest up to alphas
        lemma_h2_II_extends_push(mm, n, m, alphas_rest, beta);
        lemma_quotient_preserves_equiv(h2_II(mm, n, m, alphas_rest), fp, next, end);

        lemma_equiv_transitive(fp, start, next, end);
        assert((forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(fp, start, end));
    }
}

// ----------------------------------------------------------------------------
// The compactness core: induction over the derivation
// ----------------------------------------------------------------------------

proof fn lemma_compactness_core(
    mm: ModMachine, n: nat, m: nat, steps: Seq<PredDerivationStep>, start: Word, end: Word,
)
    requires
        pred_derivation_produces(h2_noS_pred(mm, n, m), steps, start) == Some(end),
    ensures
        exists|alphas: Seq<nat>|
            (forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(h2_II(mm, n, m, alphas), start, end),
    decreases steps.len(),
{
    let pp = h2_noS_pred(mm, n, m);
    if steps.len() == 0 {
        assert(start == end);
        let alphas = Seq::<nat>::empty();
        lemma_equiv_refl(h2_II(mm, n, m, alphas), start);
        assert((forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(h2_II(mm, n, m, alphas), start, end));
    } else {
        let first = steps.first();
        assert(apply_step_pred(pp, start, first) is Some);
        let next = apply_step_pred(pp, start, first).unwrap();
        let rest = steps.drop_first();
        assert(pred_derivation_produces(pp, rest, next) == Some(end));
        lemma_compactness_core(mm, n, m, rest, next, end);
        let alphas_rest = choose|a: Seq<nat>|
            (forall|i: int| 0 <= i < a.len() ==> numbers_word(n, m, a[i]))
            && equiv_in_presentation(h2_II(mm, n, m, a), next, end);
        assert(forall|i: int| 0 <= i < alphas_rest.len() ==> numbers_word(n, m, #[trigger] alphas_rest[i]));
        assert(equiv_in_presentation(h2_II(mm, n, m, alphas_rest), next, end));

        match first {
            PredDerivationStep::FreeReduce { position } => {
                let fp = h2_II(mm, n, m, alphas_rest);
                lemma_h2_II_relators_eq(mm, n, m, alphas_rest);
                lemma_finite_step_from_pred(fp, pp, start, first, next);
                lemma_equiv_transitive(fp, start, next, end);
                assert((forall|i: int| 0 <= i < alphas_rest.len() ==> numbers_word(n, m, #[trigger] alphas_rest[i]))
                    && equiv_in_presentation(fp, start, end));
            },
            PredDerivationStep::FreeExpand { position, symbol } => {
                let fp = h2_II(mm, n, m, alphas_rest);
                lemma_h2_II_relators_eq(mm, n, m, alphas_rest);
                lemma_finite_step_from_pred(fp, pp, start, first, next);
                lemma_equiv_transitive(fp, start, next, end);
                assert((forall|i: int| 0 <= i < alphas_rest.len() ==> numbers_word(n, m, #[trigger] alphas_rest[i]))
                    && equiv_in_presentation(fp, start, end));
            },
            PredDerivationStep::RelatorInsert { position, relator, inverted } => {
                assert((pp.relators)(relator));
                assert(is_relator_step(first) && step_relator(first) == relator);
                lemma_relator_arm(mm, n, m, start, first, next, end, alphas_rest, relator);
            },
            PredDerivationStep::RelatorDelete { position, relator, inverted } => {
                assert((pp.relators)(relator));
                assert(is_relator_step(first) && step_relator(first) == relator);
                lemma_relator_arm(mm, n, m, start, first, next, end, alphas_rest, relator);
            },
        }
    }
}

// ----------------------------------------------------------------------------
// CS-4b headline — the compactness bridge
// ----------------------------------------------------------------------------

/// **CS-4b — the compactness bridge.** A c-free word `u` trivial in the infinite predicate base
/// `h2_pred` is trivial in SOME finite family-(II) slice `h2_II(alphas)`, with every `alpha` a
/// number word. Stage 1 strips `S` (`lemma_s_strip_descends`); stage 2 re-indexes the resulting
/// `h2_noS_pred` derivation onto a finite slice (`lemma_compactness_core`). This is the reduction
/// that lets CS-4c/d feed the REAL finite directional lemmas `lemma_map_a_forward` /
/// `lemma_mapb_M2_rt`.
pub proof fn lemma_cs4b_compactness(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, u: Word,
)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        no_c_word(g_m(mm).num_generators, n, u),
        word_valid(u, h2_num_gens(g_m(mm).num_generators, n)),
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), u, empty_word()),
    ensures
        exists|alphas: Seq<nat>|
            (forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]))
            && equiv_in_presentation(h2_II(mm, n, m, alphas), u, empty_word()),
{
    lemma_s_strip_descends(mm, n, m, is_S, u);
    let d = choose|d: PredDerivation| pred_derivation_valid(h2_noS_pred(mm, n, m), d, u, empty_word());
    assert(pred_derivation_produces(h2_noS_pred(mm, n, m), d.steps, u) == Some(empty_word()));
    lemma_compactness_core(mm, n, m, d.steps, u, empty_word());
}

} // verus!
