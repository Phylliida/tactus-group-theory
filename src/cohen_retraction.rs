// Layer 2 — Cohen §1 assembly, brick CS-2: the c-retraction descent `H₂ → C`.
//
// `docs/cohen-section1-assembly-plan.md` §3 step 2. The ISO-FREE back-half of the
// faithfulness chain: once Britton descends `w_α(c)=1 in H₃` to `=1 in h2_pred`
// (CS-3..CS-5), this brick descends `=1 in h2_pred` to `=1 in C` WITHOUT any HNN
// peel of `p` (which would need an infinite-association Britton — never paid).
//
// The tool is the retraction homomorphism `ρ : h2_pred → c_pred` fixing every `c_j`
// and killing (↦ε) every other generator. `ρ` is valid: each K_M / family-(II)
// relator is c-symbol-free ⟹ ρ-image ε; each comm relator `b_i c_j b_i⁻¹ c_j⁻¹`
// ↦ `c_j c_j⁻¹ ≡ ε`; each S relator is a pure-c word ↦ itself, `=1 in C` by
// definition. Since `ρ` fixes pure-c words, `w_α(c)=1 in h2_pred ⟹ =1 in c_pred`.
// (Soundness peer-checked 2026-06-23.)
//
// `c_pred = ⟨h2 gens; S⟩` (non-c gens present-but-free); on pure-c words it presents
// exactly `C = ⟨c;S⟩` (the non-c gens Tietze-remove — a deferred final-packaging step).
//
// Additive/reversible (new module + one lib.rs line); no regression.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::*;
use crate::pred_homomorphism::*;
use crate::machine_group::*;
use crate::layout::*;
use crate::word_numbering::*;
use crate::h1::*;
use crate::h3_ii::*;
use crate::cohen_h2::*;

verus! {

// ----------------------------------------------------------------------------
// `no_c_word`: a word with NO c-block symbol (the dual of `is_c_word`)
// ----------------------------------------------------------------------------

/// `w` has no c-block letter: every symbol's index is outside `[c_base, c_base+n)`.
pub open spec fn no_c_word(nk: nat, n: nat, w: Word) -> bool {
    forall|i: int| 0 <= i < w.len() ==> !c_symbol(nk, n, #[trigger] w[i])
}

/// `no_c_word` is preserved by concatenation.
pub proof fn lemma_no_c_concat(nk: nat, n: nat, a: Word, b: Word)
    requires
        no_c_word(nk, n, a),
        no_c_word(nk, n, b),
    ensures
        no_c_word(nk, n, concat(a, b)),
{
    let w = concat(a, b);
    assert forall|i: int| 0 <= i < w.len() implies !c_symbol(nk, n, #[trigger] w[i]) by {
        if i < a.len() {
            assert(w[i] == a[i]);
        } else {
            assert(w[i] == b[i - a.len()]);
        }
    }
}

/// `no_c_word` is preserved by `inverse_word` (inversion keeps generator indices).
pub proof fn lemma_no_c_inverse(nk: nat, n: nat, w: Word)
    requires
        no_c_word(nk, n, w),
    ensures
        no_c_word(nk, n, inverse_word(w)),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        let rest = w.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies !c_symbol(nk, n, #[trigger] rest[i]) by {
            assert(rest[i] == w[i + 1]);
        }
        lemma_no_c_inverse(nk, n, rest);
        let s_inv = Seq::new(1, |_i: int| inverse_symbol(w.first()));
        assert(inverse_word(w) =~= inverse_word(rest) + s_inv);
        // inverse_symbol keeps the generator index ⟹ keeps !c_symbol.
        assert(!c_symbol(nk, n, w.first())) by { assert(w[0] == w.first()); }
        assert(generator_index(inverse_symbol(w.first())) == generator_index(w.first()));
        assert(no_c_word(nk, n, s_inv)) by {
            assert(s_inv[0] == inverse_symbol(w.first()));
        }
        lemma_no_c_concat(nk, n, inverse_word(rest), s_inv);
    }
}

/// A c-block word (`is_c_word`) and a no-c word are disjoint notions; in particular
/// a c-symbol is never a no-c symbol (used to read off the four relator classes).
pub proof fn lemma_c_word_indices(nk: nat, n: nat, w: Word)
    requires
        is_c_word(nk, n, w),
    ensures
        forall|i: int| 0 <= i < w.len() ==> generator_index(#[trigger] w[i]) < h2_num_gens(nk, n),
{
    assert forall|i: int| 0 <= i < w.len()
        implies generator_index(#[trigger] w[i]) < h2_num_gens(nk, n) by {
        assert(c_symbol(nk, n, w[i]));
    }
}

// ----------------------------------------------------------------------------
// `w_c` lands in its own base block (the lower bound `lemma_w_c_valid` lacks)
// ----------------------------------------------------------------------------

/// Every letter of `w_c(base,n,m,α)` has index in `[base, base+n)` — the block the
/// numbering map writes into. (`lemma_w_c_valid` gives only the upper bound.)
pub proof fn lemma_w_c_in_block(base: nat, n: nat, m: nat, alpha: nat)
    requires
        numbers_word(n, m, alpha),     // digits in 1..=2n (else digit 0 ↦ Gen(base-1), off-block)
    ensures
        forall|i: int| 0 <= i < w_c(base, n, m, alpha).len() ==>
            base <= generator_index(#[trigger] w_c(base, n, m, alpha)[i]) < base + n,
    decreases alpha,
{
    if alpha == 0 || m <= 1 {
        assert(w_c(base, n, m, alpha) =~= empty_word());
    } else {
        // numbers_word(α) ⟹ 1 ≤ α%m ≤ 2n  ∧  numbers_word(α/m).
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
        lemma_w_c_in_block(base, n, m, alpha / m);
        let head = w_c(base, n, m, alpha / m);
        let tail = Seq::new(1, |_i: int| alphabet_letter(base, n, alpha % m));
        assert(w_c(base, n, m, alpha) =~= head + tail);
        let w = w_c(base, n, m, alpha);
        assert(1 <= (alpha % m) <= 2 * n);
        assert forall|i: int| 0 <= i < w.len()
            implies base <= generator_index(#[trigger] w[i]) < base + n by {
            if i < head.len() {
                assert(w[i] == head[i]);
            } else {
                assert(w[i] == tail[0]);
                // alphabet_letter(base,n,j), 1≤j≤2n: index = base + (j or j-n) - 1 ∈ [base, base+n).
            }
        }
    }
}

// ----------------------------------------------------------------------------
// The four relator classes are each c-symbol-free or pure-c
// ----------------------------------------------------------------------------

/// A K_M relator (valid over `nk = c_base` generators) has no c-block letter.
pub proof fn lemma_low_word_no_c(nk: nat, n: nat, w: Word)
    requires
        word_valid(w, nk),
    ensures
        no_c_word(nk, n, w),
{
    assert forall|i: int| 0 <= i < w.len() implies !c_symbol(nk, n, #[trigger] w[i]) by {
        assert(symbol_valid(w[i], nk));         // generator_index(w[i]) < nk = c_base(nk)
    }
}

/// `config_word(β,0)` (gens 0,1,2) has no c-block letter (`c_base = nk ≥ 4 > 2`).
pub proof fn lemma_config_word_no_c(mm: ModMachine, n: nat, beta: nat)
    ensures
        no_c_word(g_m(mm).num_generators, n, config_word(beta, 0)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);               // nk = 4 + |quads| ≥ 4 > 3
    lemma_config_word_valid(beta, 0);           // word_valid(config_word, 3)
    lemma_word_valid_mono(config_word(beta, 0), 3, nk);
    lemma_low_word_no_c(nk, n, config_word(beta, 0));
}

/// `w_b(b_base,n,m,β)` (b-block, indices `≥ b_base = c_base+n`) has no c-block letter.
pub proof fn lemma_w_b_no_c(mm: ModMachine, n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
    ensures
        no_c_word(g_m(mm).num_generators, n, w_b(b_base(g_m(mm).num_generators, n), n, m, beta)),
{
    let nk = g_m(mm).num_generators;
    let bb = b_base(nk, n);                      // = nk + n = c_base(nk) + n
    lemma_w_c_in_block(bb, n, m, beta);          // w_b = w_c(bb,..); indices in [bb, bb+n)
    let w = w_b(bb, n, m, beta);
    assert(w =~= w_c(bb, n, m, beta));
    assert forall|i: int| 0 <= i < w.len() implies !c_symbol(nk, n, #[trigger] w[i]) by {
        // index ≥ bb = c_base(nk)+n ⟹ NOT < c_base(nk)+n ⟹ !c_symbol.
        assert(bb <= generator_index(w[i]) < bb + n);
    }
}

/// The family-(II) relator `(p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹` has no c-block letter
/// (its symbols are `t,x` (config), `b` (b-block), `p`, `d` — all off the c-block).
pub proof fn lemma_family_ii_no_c(mm: ModMachine, n: nat, m: nat, beta: nat)
    requires
        numbers_word(n, m, beta),
    ensures
        no_c_word(g_m(mm).num_generators, n, family_II_relator(mm, n, m, beta)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let p = p_idx(nk, n);
    let d = d_idx(nk, n);
    let bb = b_base(nk, n);
    let cw = config_word(beta, 0);
    let wb = w_b(bb, n, m, beta);
    lemma_config_word_no_c(mm, n, beta);         // no_c(cw)
    lemma_w_b_no_c(mm, n, m, beta);              // no_c(wb)

    // p, d singletons are off the c-block:  p = nk+2n+1 ≥ nk+n,  d = nk+2n ≥ nk+n.
    let p_inv_s = seq![Symbol::Inv(p)];
    let p_s = seq![Symbol::Gen(p)];
    let d_s = seq![Symbol::Gen(d)];
    assert(no_c_word(nk, n, p_inv_s)) by { assert(p_inv_s[0] == Symbol::Inv(p)); }
    assert(no_c_word(nk, n, p_s)) by { assert(p_s[0] == Symbol::Gen(p)); }
    assert(no_c_word(nk, n, d_s)) by { assert(d_s[0] == Symbol::Gen(d)); }

    // lhs = [p⁻¹] + config + [p]
    lemma_no_c_concat(nk, n, p_inv_s, cw);
    lemma_no_c_concat(nk, n, p_inv_s + cw, p_s);
    assert(family_II_lhs(mm, n, beta) =~= p_inv_s + cw + p_s);
    // rhs = config + w_b + [d]
    lemma_no_c_concat(nk, n, cw, wb);
    lemma_no_c_concat(nk, n, cw + wb, d_s);
    assert(family_II_rhs(mm, n, m, beta) =~= cw + wb + d_s);
    lemma_no_c_inverse(nk, n, family_II_rhs(mm, n, m, beta));
    // relator = lhs + inverse(rhs)
    lemma_no_c_concat(nk, n, family_II_lhs(mm, n, beta),
        inverse_word(family_II_rhs(mm, n, m, beta)));
    assert(family_II_relator(mm, n, m, beta)
        =~= family_II_lhs(mm, n, beta) + inverse_word(family_II_rhs(mm, n, m, beta)));
}

// ----------------------------------------------------------------------------
// The retraction `ρ : h2_pred → c_pred` and the target `C = ⟨c;S⟩`
// ----------------------------------------------------------------------------

/// `C = ⟨c;S⟩` as a `PredPresentation`: the (unchanged) `h2_num_gens` generators with
/// ONLY the relator set `S`. The non-c generators are present-but-free; on a pure-c
/// word this presents exactly Cohen's `C` (the free non-c gens Tietze-remove — a
/// deferred final-packaging step, plan §3).
pub open spec fn c_pred(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool) -> PredPresentation {
    PredPresentation {
        num_generators: h2_num_gens(g_m(mm).num_generators, n),
        relators: |w: Word| is_S(w),
    }
}

/// The c-retraction `ρ : h2_pred → c_pred`: `c_j ↦ c_j`, every other generator `↦ ε`.
pub open spec fn c_retraction(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool,
) -> PredHomomorphismData {
    let nk = g_m(mm).num_generators;
    PredHomomorphismData {
        source: h2_pred(mm, n, m, is_S),
        target: c_pred(mm, n, m, is_S),
        generator_images: Seq::new(h2_num_gens(nk, n), |g: int| {
            if c_base(nk) <= g < c_base(nk) + n {
                Seq::new(1, |_j: int| Symbol::Gen(g as nat))
            } else {
                empty_word()
            }
        }),
    }
}

// ----------------------------------------------------------------------------
// Symbol- and word-level action of `ρ`
// ----------------------------------------------------------------------------

/// `ρ` fixes a c-block symbol: `apply_hom_symbol_pred(ρ, s) = [s]`.
pub proof fn lemma_rho_symbol_c(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, s: Symbol)
    requires
        c_symbol(g_m(mm).num_generators, n, s),
    ensures
        apply_hom_symbol_pred(c_retraction(mm, n, m, is_S), s) =~= Seq::new(1, |_j: int| s),
{
    let nk = g_m(mm).num_generators;
    let rho = c_retraction(mm, n, m, is_S);
    let g = generator_index(s);
    assert(c_base(nk) <= g < c_base(nk) + n);
    assert(g < h2_num_gens(nk, n));
    assert(rho.generator_images[g as int] =~= Seq::new(1, |_j: int| Symbol::Gen(g)));
    match s {
        Symbol::Gen(gg) => {
            assert(gg == g);
            assert(apply_hom_symbol_pred(rho, s) == rho.generator_images[gg as int]);
            assert(Seq::new(1, |_j: int| s) =~= Seq::new(1, |_j: int| Symbol::Gen(g)));
        }
        Symbol::Inv(gg) => {
            assert(gg == g);
            assert(apply_hom_symbol_pred(rho, s) == inverse_word(rho.generator_images[gg as int]));
            // inverse_word([Gen(g)]) = [Inv(g)] = [s]
            lemma_inverse_singleton(Symbol::Gen(g));
            assert(inverse_symbol(Symbol::Gen(g)) == Symbol::Inv(g));
            assert(inverse_word(Seq::new(1, |_j: int| Symbol::Gen(g)))
                =~= Seq::new(1, |_j: int| Symbol::Inv(g)));
            assert(Seq::new(1, |_j: int| s) =~= Seq::new(1, |_j: int| Symbol::Inv(g)));
        }
    }
}

/// `ρ` kills a non-c symbol (index in range): `apply_hom_symbol_pred(ρ, s) = ε`.
pub proof fn lemma_rho_symbol_noc(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, s: Symbol)
    requires
        !c_symbol(g_m(mm).num_generators, n, s),
        symbol_valid(s, h2_num_gens(g_m(mm).num_generators, n)),
    ensures
        apply_hom_symbol_pred(c_retraction(mm, n, m, is_S), s) =~= empty_word(),
{
    let nk = g_m(mm).num_generators;
    let rho = c_retraction(mm, n, m, is_S);
    let g = generator_index(s);
    assert(g < h2_num_gens(nk, n));
    assert(!(c_base(nk) <= g < c_base(nk) + n));
    assert(rho.generator_images[g as int] =~= empty_word());
    match s {
        Symbol::Gen(gg) => {
            assert(apply_hom_symbol_pred(rho, s) == rho.generator_images[gg as int]);
        }
        Symbol::Inv(gg) => {
            assert(apply_hom_symbol_pred(rho, s) == inverse_word(rho.generator_images[gg as int]));
            assert(inverse_word(empty_word()) =~= empty_word());
        }
    }
}

/// `ρ` kills any c-symbol-free word.
pub proof fn lemma_rho_kills_word(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word)
    requires
        word_valid(w, h2_num_gens(g_m(mm).num_generators, n)),
        no_c_word(g_m(mm).num_generators, n, w),
    ensures
        apply_hom_pred(c_retraction(mm, n, m, is_S), w) =~= empty_word(),
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let rho = c_retraction(mm, n, m, is_S);
    if w.len() == 0 {
    } else {
        let rest = w.drop_first();
        assert(!c_symbol(nk, n, w.first())) by { assert(w[0] == w.first()); }
        assert(symbol_valid(w.first(), h2_num_gens(nk, n))) by { assert(w[0] == w.first()); }
        lemma_rho_symbol_noc(mm, n, m, is_S, w.first());
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
        lemma_rho_kills_word(mm, n, m, is_S, rest);
        assert(apply_hom_pred(rho, w)
            =~= concat(apply_hom_symbol_pred(rho, w.first()), apply_hom_pred(rho, rest)));
    }
}

/// `ρ` fixes any pure-c word.
pub proof fn lemma_rho_fixes_c_word(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word)
    requires
        is_c_word(g_m(mm).num_generators, n, w),
    ensures
        apply_hom_pred(c_retraction(mm, n, m, is_S), w) =~= w,
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let rho = c_retraction(mm, n, m, is_S);
    if w.len() == 0 {
        assert(w =~= empty_word());
    } else {
        let rest = w.drop_first();
        assert(c_symbol(nk, n, w.first())) by { assert(w[0] == w.first()); }
        lemma_rho_symbol_c(mm, n, m, is_S, w.first());
        assert(is_c_word(nk, n, rest)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies c_symbol(nk, n, #[trigger] rest[i]) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_rho_fixes_c_word(mm, n, m, is_S, rest);
        assert(apply_hom_pred(rho, w)
            =~= concat(apply_hom_symbol_pred(rho, w.first()), apply_hom_pred(rho, rest)));
        assert(apply_hom_symbol_pred(rho, w.first()) =~= Seq::new(1, |_j: int| w.first()));
        assert(concat(Seq::new(1, |_j: int| w.first()), rest) =~= w);
    }
}

// ----------------------------------------------------------------------------
// `ρ`'s validity (every relator class ↦ identity) and the descent
// ----------------------------------------------------------------------------

/// `c_pred` is a valid presentation (`S ⊆ c-block words`).
pub proof fn lemma_c_pred_valid(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    requires
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        pred_presentation_valid(c_pred(mm, n, m, is_S)),
{
    reveal(pred_presentation_valid);
    let nk = g_m(mm).num_generators;
    let cp = c_pred(mm, n, m, is_S);
    assert forall|w: Word| #![trigger (cp.relators)(w)] (cp.relators)(w) implies
        word_valid(w, cp.num_generators) by {
        assert((cp.relators)(w) == is_S(w));
        assert(is_c_word(nk, n, w));
        lemma_c_word_valid(nk, n, w);
    }
}

/// The image of the commutator relator `b_i c_j b_i⁻¹ c_j⁻¹` is `c_j c_j⁻¹ ≡ ε`.
pub proof fn lemma_comm_relator_image(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, i: nat, j: nat)
    requires
        1 <= i <= n, 1 <= j <= n,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        equiv_in_pred_presentation(c_pred(mm, n, m, is_S),
            apply_hom_pred(c_retraction(mm, n, m, is_S), comm_relator(g_m(mm).num_generators, n, i, j)),
            empty_word()),
{
    let nk = g_m(mm).num_generators;
    let rho = c_retraction(mm, n, m, is_S);
    let cp = c_pred(mm, n, m, is_S);
    let bg = b_idx(nk, n, i);                // b_idx = nk+n+(i-1) ∈ [nk+n, nk+2n) — non-c
    let cg = c_idx(nk, j);                   // c_idx = nk+(j-1) ∈ [nk, nk+n) — c-block
    let sb = Seq::new(1, |_k: int| Symbol::Gen(bg));
    let sc = Seq::new(1, |_k: int| Symbol::Gen(cg));
    let sbi = Seq::new(1, |_k: int| Symbol::Inv(bg));
    let sci = Seq::new(1, |_k: int| Symbol::Inv(cg));
    let comm = comm_relator(nk, n, i, j);
    assert(comm =~= sb + sc + sbi + sci);

    // index facts
    assert(bg == nk + n + (i - 1));
    assert(cg == nk + (j - 1));
    assert(c_symbol(nk, n, Symbol::Gen(cg)));
    assert(c_symbol(nk, n, Symbol::Inv(cg)));
    assert(!c_symbol(nk, n, Symbol::Gen(bg)));
    assert(!c_symbol(nk, n, Symbol::Inv(bg)));
    assert(symbol_valid(Symbol::Gen(bg), h2_num_gens(nk, n)));
    assert(symbol_valid(Symbol::Inv(bg), h2_num_gens(nk, n)));

    // per-symbol images
    lemma_rho_symbol_noc(mm, n, m, is_S, Symbol::Gen(bg));    // ε
    lemma_rho_symbol_noc(mm, n, m, is_S, Symbol::Inv(bg));    // ε
    lemma_rho_symbol_c(mm, n, m, is_S, Symbol::Gen(cg));      // [Gen(cg)]
    lemma_rho_symbol_c(mm, n, m, is_S, Symbol::Inv(cg));      // [Inv(cg)]
    lemma_hom_pred_singleton(rho, Symbol::Gen(bg));
    lemma_hom_pred_singleton(rho, Symbol::Inv(bg));
    lemma_hom_pred_singleton(rho, Symbol::Gen(cg));
    lemma_hom_pred_singleton(rho, Symbol::Inv(cg));

    // apply over the concatenation: ε + [Gen(cg)] + ε + [Inv(cg)] = [Gen(cg), Inv(cg)]
    lemma_hom_pred_respects_concat(rho, sb + sc + sbi, sci);
    lemma_hom_pred_respects_concat(rho, sb + sc, sbi);
    lemma_hom_pred_respects_concat(rho, sb, sc);
    assert(apply_hom_pred(rho, comm) =~= concat(sc, sci));

    // [Gen(cg), Inv(cg)] = sc + inverse_word(sc) ≡ ε
    assert(sci =~= inverse_word(sc));
    lemma_c_pred_valid(mm, n, m, is_S);
    lemma_pred_word_inverse_right(cp, sc);
    assert(concat(sc, inverse_word(sc)) =~= concat(sc, sci));
}

/// `ρ` is a valid homomorphism: every `h2_pred` relator maps to an identity of `c_pred`.
pub proof fn lemma_c_retraction_valid(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        is_valid_pred_homomorphism(c_retraction(mm, n, m, is_S)),
{
    let nk = g_m(mm).num_generators;
    let ng = h2_num_gens(nk, n);
    let rho = c_retraction(mm, n, m, is_S);
    let cp = c_pred(mm, n, m, is_S);
    lemma_h2_pred_valid(mm, n, m, is_S);
    lemma_c_pred_valid(mm, n, m, is_S);
    assert(rho.source == h2_pred(mm, n, m, is_S));
    assert(rho.generator_images.len() == ng);
    assert(rho.source.num_generators == ng);

    // generator-image validity
    assert forall|g: int| 0 <= g < rho.generator_images.len()
        implies word_valid(#[trigger] rho.generator_images[g], cp.num_generators) by {
        if c_base(nk) <= g < c_base(nk) + n {
            assert(rho.generator_images[g] =~= Seq::new(1, |_k: int| Symbol::Gen(g as nat)));
            assert(word_valid(rho.generator_images[g], ng)) by {
                assert(rho.generator_images[g][0] == Symbol::Gen(g as nat));
            }
        } else {
            assert(rho.generator_images[g] =~= empty_word());
        }
    }

    // relator-image clause
    assert forall|w: Word| #![trigger (rho.source.relators)(w)] (rho.source.relators)(w) implies
        equiv_in_pred_presentation(cp, apply_hom_pred(rho, w), empty_word()) by {
        assert((rho.source.relators)(w) == h2_pred_relator(mm, n, m, is_S, w));
        assert(h2_pred_relator(mm, n, m, is_S, w));
        if g_m(mm).relators.contains(w) {
            reveal(presentation_valid);
            lemma_g_m_valid(mm);
            let idx = choose|idx: int| 0 <= idx < g_m(mm).relators.len() && g_m(mm).relators[idx] == w;
            assert(word_valid(g_m(mm).relators[idx], nk));
            lemma_low_word_no_c(nk, n, w);
            lemma_word_valid_mono(w, nk, ng);
            lemma_rho_kills_word(mm, n, m, is_S, w);
            lemma_pred_equiv_refl(cp, empty_word());
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
            lemma_comm_relator_image(mm, n, m, is_S, ii, jj);
        } else if is_S(w) {
            assert(is_c_word(nk, n, w));
            lemma_rho_fixes_c_word(mm, n, m, is_S, w);
            assert((cp.relators)(w));
            lemma_pred_relator_is_identity(cp, w);
        } else {
            assert(is_family_ii(mm, n, m, w));
            let beta = choose|beta: nat|
                numbers_word(n, m, beta) && w == family_II_relator(mm, n, m, beta);
            lemma_family_ii_no_c(mm, n, m, beta);
            lemma_family_II_relator_valid(mm, n, m, beta, ng);
            lemma_rho_kills_word(mm, n, m, is_S, w);
            lemma_pred_equiv_refl(cp, empty_word());
        }
    }
}

/// **CS-2 headline — the c-retraction descent.** A pure-c word trivial in the predicate
/// base `h2_pred` is trivial in `C = ⟨c;S⟩`. This is the iso-free back-half of the
/// faithfulness chain (`docs/cohen-section1-assembly-plan.md` §3 step 2): no `p`-peel,
/// no infinite-association Britton.
pub proof fn lemma_h2_pred_descends_to_c(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        is_c_word(g_m(mm).num_generators, n, w),
        equiv_in_pred_presentation(h2_pred(mm, n, m, is_S), w, empty_word()),
    ensures
        equiv_in_pred_presentation(c_pred(mm, n, m, is_S), w, empty_word()),
{
    let rho = c_retraction(mm, n, m, is_S);
    lemma_c_retraction_valid(mm, n, m, is_S);
    assert(rho.source == h2_pred(mm, n, m, is_S));
    lemma_hom_pred_preserves_equiv(rho, w, empty_word());
    // apply_hom_pred(ρ, w) = w (fixes c-words);  apply_hom_pred(ρ, ε) = ε.
    lemma_rho_fixes_c_word(mm, n, m, is_S, w);
    assert(apply_hom_pred(rho, empty_word()) =~= empty_word());
}

} // verus!
