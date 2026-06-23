// Layer 2 — Brick 5, C3.2c / the C-arc: `map_b`'s forward (faithful) direction.
//
// `map_b = φ_l` is a digit-SCALING embedding (`t↦t_l, x↦xᵐ, d↦b_l·d`), so its forward Britton-peel
// is NOT same-index like `map_a`'s (relabeling).  The clean route (docs/brick5-c3.2c-plan.md §5,
// the "map_b = ψ_a ∘ φ_l" factoring) reuses `map_a` forward (DONE) and isolates the scaling into a
// PURE free-group injectivity:
//
//   emb(b_words, w) ≡_{h2_II} ε
//     = emb(a_words, φ_l_src(w)) ≡_{h2_II} ε          (M1, this module: the SOURCE-level factoring)
//     ⟹ φ_l_src(w) ≡_{P_A} ε                          (map_a forward, DONE)
//     ⟹ w ≡_{P_A} ε                                   (M2: φ_l_src injective on P_A — the hard arc)
//
// where `φ_l_src` is the φ_l substitution at the P_A/F level: it maps each P_A generator to a P_A
// word (`t↦config(l,0)`, `x↦xᵐ`, `d↦b_l·d`, `b_j↦b_j`, `p↦p`), so that applying `a_words` (the
// literal inclusion) afterwards reproduces `b_words = φ_l(a_words)`.  THIS module delivers M1 (pure
// syntax, reusing `phi_l_maps`'s column translations + `lemma_apply_embedding_compose`).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{ModMachine, g_m, config_word, symbol_power, lemma_g_m_num_generators};
use crate::layout::{d_idx, b_base, b_idx, p_idx};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat,
    lemma_apply_embedding_valid};
use crate::word_numbering::alphabet_letter;
use crate::pa_data::pa_b_base;
use crate::phi_l_maps::{a_words, lemma_a_words_fixes_config, lemma_a_words_on_alpha_letter,
    lemma_a_words_head, lemma_a_words_bblock};
use crate::phi_l_iso::lemma_apply_embedding_fixes;
use crate::phi_l_lift::b_words;
use crate::h3::phi_assoc;
use crate::h3_ii::{compose_embeddings, lemma_apply_embedding_compose, lemma_phi_assoc_index};

verus! {

// ----------------------------------------------------------------------------
// φ_l_src — the P_A-level φ_l substitution (each P_A gen ↦ a P_A word).
// ----------------------------------------------------------------------------

/// **`φ_l_src`** — the φ_l endomorphism at the source (`P_A`/`F`) level, a length-`n+4` image list
/// over `P_A`'s generators `[t=0, x=1, d=2, b_j=2+j, p=n+3]`:
///   `t ↦ config(l,0)` (`= x⁻ˡtxˡ`, over gens 0,1),  `x ↦ xᵐ`,  `d ↦ b_l·d`
///   (`= [alphabet_letter(3,n,l), Gen(2)]`, the F-b-block letter for digit `l` then `d=Gen2`),
///   and every other gen (`b_j`, `p`) ↦ itself.
/// Applying `a_words` (the literal inclusion) after `φ_l_src` reproduces `b_words = φ_l(a_words)`.
pub open spec fn phi_l_src(n: nat, m: nat, l: nat) -> Seq<Word> {
    Seq::new((n + 4) as nat, |g: int| {
        if g == 0 {
            config_word(l, 0)                                          // t ↦ config(l,0)
        } else if g == 1 {
            symbol_power(Symbol::Gen(1), m)                            // x ↦ xᵐ
        } else if g == 2 {
            seq![alphabet_letter(pa_b_base(), n, l), Symbol::Gen(2)]   // d ↦ b_l·d
        } else {
            seq![Symbol::Gen(g as nat)]                                // b_j, p ↦ themselves
        }
    })
}

/// `φ_l_src` has length `n+4`.
pub proof fn lemma_phi_l_src_len(n: nat, m: nat, l: nat)
    ensures
        phi_l_src(n, m, l).len() == n + 4,
{
}

/// **`φ_l_src` images are valid over `n+4`** (so `emb(φ_l_src, w)` is a `P_A` word for `w` over
/// `n+4`).  `config(l,0)` uses `{0,1}`; `xᵐ` uses `{1}`; `d↦b_l·d` uses the F-b-block letter
/// (index `≤ n+2`) and `d=Gen2`; the identity images `Gen(g)` have `g ≤ n+3`.
pub proof fn lemma_phi_l_src_valid(n: nat, m: nat, l: nat)
    requires
        1 <= l <= 2 * n,
    ensures
        forall|g: int| 0 <= g < n + 4 ==> word_valid(#[trigger] phi_l_src(n, m, l)[g], (n + 4) as nat),
{
    let ng = (n + 4) as nat;
    let s = phi_l_src(n, m, l);
    assert forall|g: int| 0 <= g < n + 4 implies word_valid(#[trigger] s[g], ng) by {
        if g == 0 {
            // config(l,0) = x⁻ˡtxˡ over {0,1} ⊂ [0,n+4).
            assert(s[0] == config_word(l, 0));
            crate::machine_group::lemma_config_word_valid(l, 0);             // word_valid(·, 3)
            crate::machine_group::lemma_word_valid_mono(config_word(l, 0), 3, ng);
        } else if g == 1 {
            assert(s[1] == symbol_power(Symbol::Gen(1), m));
            crate::machine_group::lemma_symbol_power_valid(Symbol::Gen(1), 1, ng);
        } else if g == 2 {
            // [alphabet_letter(3,n,l), Gen(2)]: alphabet_letter index ≤ n+2 < n+4, and 2 < n+4.
            assert(s[2] == seq![alphabet_letter(pa_b_base(), n, l), Symbol::Gen(2)]);
            assert(symbol_valid(alphabet_letter(pa_b_base(), n, l), ng)) by {
                if l <= n {
                    assert(alphabet_letter(pa_b_base(), n, l) == Symbol::Gen((3 + l - 1) as nat));
                } else {
                    assert(alphabet_letter(pa_b_base(), n, l) == Symbol::Inv((3 + (l - n) - 1) as nat));
                }
            }
            assert(symbol_valid(Symbol::Gen(2), ng));
            assert forall|t: int| 0 <= t < s[2].len() implies symbol_valid(#[trigger] s[2][t], ng) by {}
        } else {
            // identity image Gen(g), g ∈ [3, n+3].
            assert(s[g] == seq![Symbol::Gen(g as nat)]);
            assert(symbol_valid(Symbol::Gen(g as nat), ng));
            assert forall|t: int| 0 <= t < s[g].len() implies symbol_valid(#[trigger] s[g][t], ng) by {}
        }
    }
}

// ----------------------------------------------------------------------------
// M1-core — `a_words` post-composed with `φ_l_src` IS `b_words`.
// ----------------------------------------------------------------------------

/// **`a_words` fixes an x-power**: `emb(a_words, xᵏ) =~= xᵏ` (every symbol is `Gen(1)`, fixed by
/// `a_words[1] = [Gen(1)]`).
proof fn lemma_a_words_fixes_x_power(mm: ModMachine, n: nat, k: nat)
    ensures
        apply_embedding(a_words(mm, n), symbol_power(Symbol::Gen(1), k))
            =~= symbol_power(Symbol::Gen(1), k),
{
    let aw = a_words(mm, n);
    let sp = symbol_power(Symbol::Gen(1), k);
    lemma_a_words_head(mm, n);                                          // aw[1] = [Gen(1)]
    assert forall|i: int| 0 <= i < sp.len()
        implies apply_embedding_symbol(aw, #[trigger] sp[i]) =~= seq![sp[i]] by {
        assert(sp[i] == Symbol::Gen(1));
        assert(apply_embedding_symbol(aw, Symbol::Gen(1)) == aw[1]);
        assert(aw[1] == seq![Symbol::Gen(1)]);
    }
    lemma_apply_embedding_fixes(aw, sp);
}

/// **M1-core**: `compose_embeddings(a_words, φ_l_src) =~= b_words` — applying `a_words` (the literal
/// inclusion) to each `φ_l_src` image reproduces the corresponding `b_words` entry (`= φ_l(a_words)`).
/// Per-gen: `t↦config(l,0)` (a_words fixes config), `x↦xᵐ` (a_words fixes x-power), `d↦b_l·d`
/// (digit relabel + `d=Gen2↦Gen(d_idx)`), `b_j/p ↦` the literal h2-gen.
pub proof fn lemma_compose_a_words_phi_l_src(mm: ModMachine, n: nat, m: nat, l: nat)
    requires
        1 <= l <= 2 * n,
    ensures
        compose_embeddings(a_words(mm, n), phi_l_src(n, m, l)) =~= b_words(mm, n, m, l),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let aw = a_words(mm, n);
    let src = phi_l_src(n, m, l);
    let comp = compose_embeddings(aw, src);
    let bw = b_words(mm, n, m, l);
    let bb = b_base(nk, n);
    let d = d_idx(nk, n);
    let p = p_idx(nk, n);

    lemma_phi_assoc_index(nk, n, m, l);
    lemma_a_words_head(mm, n);                                          // aw[0],aw[1],aw[2], len n+4
    assert(comp.len() == src.len() == n + 4);
    assert(bw.len() == n + 4);

    assert forall|i: int| 0 <= i < n + 4 implies comp[i] =~= bw[i] by {
        assert(comp[i] == apply_embedding(aw, src[i]));
        assert(bw[i] == phi_assoc(nk, n, m, l)[i].1);
        if i == 0 {
            // t ↦ config(l,0); a_words fixes it; b_words[0] = config(l,0).
            assert(src[0] == config_word(l, 0));
            lemma_a_words_fixes_config(mm, n, l);
            assert(bw[0] == config_word(l, 0));
        } else if i == 1 {
            // x ↦ xᵐ; a_words fixes x-power; b_words[1] = xᵐ.
            assert(src[1] == symbol_power(Symbol::Gen(1), m));
            lemma_a_words_fixes_x_power(mm, n, m);
            assert(bw[1] == symbol_power(Symbol::Gen(1), m));
        } else if i == 2 {
            // d ↦ b_l·d = [alphabet_letter(3,n,l)] + [Gen2].
            let al3 = seq![alphabet_letter(pa_b_base(), n, l)];
            let g2: Word = seq![Symbol::Gen(2)];
            assert(src[2] == al3 + g2);
            lemma_apply_embedding_concat(aw, al3, g2);
            // emb(aw, [alphabet_letter(3,n,l)]) =~= [alphabet_letter(bb,n,l)].
            lemma_a_words_on_alpha_letter(mm, n, l);
            // emb(aw, [Gen2]) = aw[2] = [Gen(d)].
            reveal_with_fuel(apply_embedding, 2);
            lemma_concat_empty_right(aw[2]);
            assert(apply_embedding(aw, g2) =~= aw[2]);
            assert(aw[2] == seq![Symbol::Gen(d)]);
            assert(comp[2] =~= seq![alphabet_letter(bb, n, l)] + seq![Symbol::Gen(d)]);
            assert(bw[2] == seq![alphabet_letter(bb, n, l), Symbol::Gen(d)]);
        } else if i < n + 3 {
            // b-block: src[i] = [Gen(i)] (identity); emb = aw[i] = [Gen(nk+n+(i-3))].
            assert(src[i] == seq![Symbol::Gen(i as nat)]);
            reveal_with_fuel(apply_embedding, 2);
            lemma_concat_empty_right(aw[i]);
            assert(apply_embedding(aw, seq![Symbol::Gen(i as nat)]) =~= aw[i]);
            lemma_a_words_bblock(mm, n, i);                             // aw[i] = [Gen(nk+n+(i-3))]
            let j = i - 3;
            assert(bw[i] == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
            assert(b_idx(nk, n, (j + 1) as nat) == nk + n + (i - 3));
        } else {
            // p-tail: i = n+3, src[i] = [Gen(n+3)]; emb = aw[n+3] = [Gen(p_idx)].
            assert(i == n + 3);
            assert(src[i] == seq![Symbol::Gen((n + 3) as nat)]);
            reveal_with_fuel(apply_embedding, 2);
            lemma_concat_empty_right(aw[i]);
            assert(apply_embedding(aw, seq![Symbol::Gen((n + 3) as nat)]) =~= aw[i]);
            // aw[n+3] = [Gen(p_idx)] (the push entry of a_words = a_words_F.push([p])).
            assert(aw[(n + 3) as int] == seq![Symbol::Gen(p)]) by {
                lemma_a_words_is_phi_col0_local(mm, n, m, l);
            }
            assert(bw[(n + 3) as int] == seq![Symbol::Gen(p)]);
        }
    }
}

/// Local bridge: `a_words[n+3] = [Gen(p_idx)]` (the `p`-push entry).  Re-derives via the `.0` column.
proof fn lemma_a_words_is_phi_col0_local(mm: ModMachine, n: nat, m: nat, l: nat)
    ensures
        a_words(mm, n)[(n + 3) as int] == seq![Symbol::Gen(p_idx(g_m(mm).num_generators, n))],
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    crate::phi_l_maps::lemma_a_words_is_phi_col0(mm, n, m, l);
    lemma_phi_assoc_index(nk, n, m, l);
    let col0 = Seq::new((n + 4) as nat, |i: int| phi_assoc(nk, n, m, l)[i].0);
    assert(a_words(mm, n) == col0);
    assert(col0[(n + 3) as int] == phi_assoc(nk, n, m, l)[(n + 3) as int].0);
    assert(phi_assoc(nk, n, m, l)[(n + 3) as int].0 == seq![Symbol::Gen(p_idx(nk, n))]);
}

// ----------------------------------------------------------------------------
// M1 — the source-level factoring `emb(b_words, w) = emb(a_words, emb(φ_l_src, w))`.
// ----------------------------------------------------------------------------

/// **M1 — the source-level factoring**: `emb(b_words, w) =~= emb(a_words, emb(φ_l_src, w))`.
/// `b_words = compose(a_words, φ_l_src)` (M1-core), so by `lemma_apply_embedding_compose`,
/// `emb(b_words, w) = emb(compose(a_words, φ_l_src), w) = emb(a_words, emb(φ_l_src, w))`.  This lets
/// `map_b` forward reuse `map_a` forward on `emb(φ_l_src, w)` and reduce to `φ_l_src` injectivity.
pub proof fn lemma_mapb_factor_source(mm: ModMachine, n: nat, m: nat, l: nat, w: Word)
    requires
        1 <= l <= 2 * n,
        word_valid(w, (n + 4) as nat),
    ensures
        apply_embedding(b_words(mm, n, m, l), w)
            =~= apply_embedding(a_words(mm, n), apply_embedding(phi_l_src(n, m, l), w)),
{
    let aw = a_words(mm, n);
    let src = phi_l_src(n, m, l);
    let bw = b_words(mm, n, m, l);
    lemma_phi_l_src_len(n, m, l);
    assert(word_valid(w, src.len()));                                  // src.len() == n+4
    // f(g(w)) = (f∘g)(w),  f = a_words, g = φ_l_src.
    lemma_apply_embedding_compose(aw, src, w);
    assert(apply_embedding(aw, apply_embedding(src, w))
        =~= apply_embedding(compose_embeddings(aw, src), w));
    // compose(a_words, φ_l_src) =~= b_words.
    lemma_compose_a_words_phi_l_src(mm, n, m, l);
    assert(compose_embeddings(aw, src) =~= bw);
    // so emb(compose, w) = emb(b_words, w).
    lemma_apply_embedding_compose_eq(aw, src, bw, w);
}

/// If `compose(f,g) =~= bw` then `emb(compose(f,g), w) =~= emb(bw, w)` (embedding respects the
/// image-list equality).  A tiny congruence helper for M1's final step.
proof fn lemma_apply_embedding_compose_eq(f: Seq<Word>, g: Seq<Word>, bw: Seq<Word>, w: Word)
    requires
        compose_embeddings(f, g) =~= bw,
    ensures
        apply_embedding(compose_embeddings(f, g), w) =~= apply_embedding(bw, w),
{
    assert(compose_embeddings(f, g) == bw);
}

} // verus!
