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
use crate::h3_ii::{compose_embeddings, lemma_apply_embedding_compose, lemma_phi_assoc_index,
    recog_data};
use crate::pa_data::{pa_data, lemma_pa_data_valid, lemma_pa_data_shape};
use crate::phi_l_maps::{a_words_F, lemma_map_a_faithful};
use crate::phi_l_pinch::{lemma_a_col_correspondence, lemma_b_col_correspondence};
use crate::f_free_a1::{betas, lemma_betas_index, lemma_recog_associations_isomorphic};
use crate::phi_l_forward::lemma_free_family_injective;
use crate::free_basis::lemma_free_to_embedding;
use crate::h1::{h1_base, lemma_h1_base_valid, lemma_h1_base_num_generators};
use crate::higman_operations::free_group;
use crate::hnn::hnn_associations_isomorphic;
use crate::presentation::{equiv_in_presentation, presentation_valid, lemma_equiv_refl,
    lemma_equiv_symmetric, lemma_equiv_transitive};
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_word_inverse_left};
use crate::word_numbering::numbers_word;
use crate::machine_group::{mod_machine_wf, pres_tx, psi_F_images, lemma_psi_F_injective,
    lemma_config_word_valid, lemma_symbol_power_merge, lemma_inverse_word_sympower,
    lemma_symbol_power_valid};
use crate::phi_l_iso::lemma_config_zero_form;
use crate::free_family_perm::{conjugate_family, lemma_free_family_conjugate,
    lemma_free_family_respects_equiv};
use crate::f_free::is_free_family;
use crate::f_free_tower::{free_stable_tower, free_stable_family, free_stable_letter,
    lemma_free_stable_tower_extends, lemma_free_stable_tower_closed, lemma_free_stable_family_closed};

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

// ----------------------------------------------------------------------------
// pa_data iso — `hnn_associations_isomorphic(pa_data(betas))` over the FREE base.
// ----------------------------------------------------------------------------

/// **pa_data iso** — `hnn_associations_isomorphic(pa_data(n,m,betas(alphas)))`: for `w` over
/// `k = |betas|` letters, `emb(pa a-col, w) ≡_{free(n+3)} ε ⟺ emb(pa b-col, w) ≡_{free(n+3)} ε`.
///
/// **Clean assembly — NO fresh free-group machinery.**  The column correspondences (`phi_l_pinch`)
/// give `recog col = compose(a_words_F, pa col)`, `a_words_F` is free in `h1_base` (`map_a` faithful),
/// and A1 (`lemma_recog_associations_isomorphic`) is the `recog`-iso.  Chain (a-side ⟹ b-side):
///   `emb(pa a, w) ≡_free ε`
///     ⟹ (F3 `lemma_free_to_embedding`) `emb(a_words_F, emb(pa a, w)) ≡_{h1} ε`
///     = (compose) `emb(recog a, w) ≡_{h1} ε`
///     ⟹ (A1) `emb(recog b, w) ≡_{h1} ε` = `emb(a_words_F, emb(pa b, w)) ≡_{h1} ε`
///     ⟹ (a_words_F free ⟹ injective, `lemma_free_family_injective`) `emb(pa b, w) ≡_free ε`,
/// and symmetric.  Needed for the M2 Britton peel (`britton_lemma_full` over `pa_data`).
pub proof fn lemma_pa_data_isomorphic(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        hnn_associations_isomorphic(pa_data(n, m, betas(alphas))),
{
    let bet = betas(alphas);
    let pd = pa_data(n, m, bet);
    let rd = recog_data(mm, n, m, alphas);
    let awf = a_words_F(mm, n);
    let h1 = h1_base(mm, n);
    let k = pd.associations.len();

    let pa_a = Seq::new(k, |i: int| pd.associations[i].0);
    let pa_b = Seq::new(k, |i: int| pd.associations[i].1);
    let rd_a = Seq::new(rd.associations.len(), |i: int| rd.associations[i].0);
    let rd_b = Seq::new(rd.associations.len(), |i: int| rd.associations[i].1);

    lemma_betas_index(alphas);
    lemma_pa_data_shape(n, m, bet);                            // pd.base.num == n+3, assoc.len == |bet|
    assert forall|i: int| 0 <= i < bet.len() implies numbers_word(n, m, #[trigger] bet[i]) by {
        if i == 0 { assert(bet[0] == 0); } else { assert(bet[i] == alphas[i - 1]); }
    }
    lemma_pa_data_valid(n, m, bet);
    assert(pd.base == free_group((n + 3) as nat));
    assert(k == bet.len());
    assert(rd.associations.len() == bet.len());

    lemma_h1_base_valid(mm, n);
    lemma_h1_base_num_generators(mm, n);
    lemma_map_a_faithful(mm, n);                               // is_free_family(h1, awf)
    assert(awf.len() == n + 3);
    lemma_recog_associations_isomorphic(mm, n, m, alphas);     // A1
    lemma_a_col_correspondence(mm, n, m, alphas);              // rd_a =~= compose(awf, pa_a)
    lemma_b_col_correspondence(mm, n, m, alphas);              // rd_b =~= compose(awf, pa_b)
    assert(rd_a =~= compose_embeddings(awf, pa_a));
    assert(rd_b =~= compose_embeddings(awf, pa_b));

    // awf images valid over h1's generators (first conjunct of is_free_family).
    assert forall|i: int| 0 <= i < awf.len() implies word_valid(#[trigger] awf[i], h1.num_generators)
        by {}
    // pa columns valid over n+3 (= awf.len()), from pd validity.
    assert forall|i: int| 0 <= i < k implies (word_valid(#[trigger] pa_a[i], (n + 3) as nat)
        && word_valid(pa_b[i], (n + 3) as nat)) by {
        assert(pa_a[i] == pd.associations[i].0);
        assert(pa_b[i] == pd.associations[i].1);
    }

    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(pd.base, apply_embedding(pa_a, w), empty_word())
        <==>
        equiv_in_presentation(pd.base, apply_embedding(pa_b, w), empty_word())
    ) by {
        if equiv_in_presentation(pd.base, apply_embedding(pa_a, w), empty_word()) {
            lemma_pa_iso_one_dir(mm, n, m, alphas, w, true);
        }
        if equiv_in_presentation(pd.base, apply_embedding(pa_b, w), empty_word()) {
            lemma_pa_iso_one_dir(mm, n, m, alphas, w, false);
        }
    }
}

// ----------------------------------------------------------------------------
// (A) φ_F injective on free F — rung (i): [config(l,0), xᵐ] free in pres_tx = free(2).
// ----------------------------------------------------------------------------

/// **Rung (i)** — `[config(l,0), xᵐ]` is a FREE family in `pres_tx = free(2)`.  This is `φ_F`
/// restricted to the `⟨t,x⟩` factor (the scaling-plus-conjugate base map `t↦config(l,0)=x⁻ˡtxˡ,
/// x↦xᵐ`).  Route: `psi_F_images(m) = [t, xᵐ]` is free (`lemma_psi_F_injective`); conjugating by
/// `c = x⁻ˡ` gives `[x⁻ˡtxˡ, x⁻ˡxᵐxˡ]` free (`lemma_free_family_conjugate`); and that family is
/// per-generator equivalent to `[config(l,0), xᵐ]` (`config(l,0) =~= x⁻ˡtxˡ` syntactically; `xᵐ ≡
/// x⁻ˡxᵐxˡ` since x-powers commute), so freeness transfers (`lemma_free_family_respects_equiv`).
pub proof fn lemma_tx_image_free(l: nat, m: nat)
    requires
        m >= 1,
    ensures
        is_free_family(pres_tx(), seq![config_word(l, 0), symbol_power(Symbol::Gen(1), m)]),
{
    let g0: Word = seq![Symbol::Gen(0)];
    let xm = symbol_power(Symbol::Gen(1), m);
    let xl = symbol_power(Symbol::Gen(1), l);
    let xinvl = symbol_power(Symbol::Inv(1), l);                 // c = x⁻ˡ
    let pf = psi_F_images(m);                                    // [t, xᵐ]
    let fam = conjugate_family(pf, xinvl);
    let target = seq![config_word(l, 0), xm];

    assert(presentation_valid(pres_tx())) by { reveal(presentation_valid); }
    assert(pres_tx() == free_group(2));                         // {2, empty relators}
    assert(pf == seq![g0, xm]);
    assert(pf.len() == 2);

    // --- step 1: psi_F_images(m) is free in pres_tx ---
    assert(is_free_family(pres_tx(), pf)) by {
        lemma_symbol_power_valid(Symbol::Gen(1), 1, 2);         // xᵐ valid over 2
        assert forall|i: int| 0 <= i < pf.len() implies word_valid(#[trigger] pf[i], 2) by {
            if i == 0 { assert(pf[0] == g0); } else { assert(pf[1] == xm); }
        }
        assert forall|w: Word| (#[trigger] word_valid(w, pf.len())
            && equiv_in_presentation(pres_tx(), apply_embedding(pf, w), empty_word()))
            implies equiv_in_presentation(free_group(pf.len()), w, empty_word()) by {
            assert(word_valid(w, 2));
            lemma_psi_F_injective(m, w);                        // w ≡_{pres_tx} ε
            assert(pf.len() == 2);
        }
    }

    // --- step 2: conjugate by c = x⁻ˡ ---
    assert(word_valid(xinvl, 2)) by { lemma_symbol_power_valid(Symbol::Inv(1), 1, 2); }
    lemma_free_family_conjugate(pres_tx(), pf, xinvl);          // is_free_family(pres_tx, fam)

    // --- step 3: per-generator equivalence fam[i] ≡ target[i] (target[i] ≡ fam[i]) ---
    lemma_inverse_word_sympower(Symbol::Inv(1), l);             // inverse_word(x⁻ˡ) =~= xˡ
    assert(inverse_word(xinvl) =~= xl);
    assert(fam.len() == 2);
    // fam[0] = (x⁻ˡ + [t]) + xˡ =~= config(l,0).
    assert(fam[0] == (xinvl + g0) + inverse_word(xinvl));
    lemma_config_zero_form(l);                                  // config(l,0) =~= x⁻ˡ + [t] + xˡ
    assert(config_word(l, 0) =~= (xinvl + g0) + xl);
    assert(fam[0] =~= config_word(l, 0));
    // fam[1] = (x⁻ˡ + xᵐ) + xˡ ≡ xᵐ.
    assert(fam[1] == (xinvl + xm) + inverse_word(xinvl));
    assert(fam[1] =~= (xinvl + xm) + xl);
    // xᵐ + xˡ =~= x^{m+l} =~= xˡ + xᵐ.
    lemma_symbol_power_merge(Symbol::Gen(1), m, l);
    lemma_symbol_power_merge(Symbol::Gen(1), l, m);
    assert(xm + xl =~= xl + xm);
    // (x⁻ˡ + xᵐ) + xˡ =~= x⁻ˡ + (xˡ + xᵐ) =~= (x⁻ˡ + xˡ) + xᵐ.
    assert((xinvl + xm) + xl =~= (xinvl + xl) + xm) by {
        assert((xinvl + xm) + xl =~= xinvl + (xm + xl));
        assert(xinvl + (xl + xm) =~= (xinvl + xl) + xm);
    }
    // x⁻ˡ + xˡ ≡ ε  (x⁻ˡ = inverse_word(xˡ)).
    lemma_inverse_word_sympower(Symbol::Gen(1), l);             // inverse_word(xˡ) =~= x⁻ˡ
    assert(inverse_word(xl) =~= xinvl);
    lemma_symbol_power_valid(Symbol::Gen(1), 1, 2);             // xˡ, xᵐ valid over 2
    lemma_symbol_power_valid(Symbol::Inv(1), 1, 2);
    lemma_word_inverse_left(pres_tx(), xl);                     // inverse_word(xˡ) + xˡ ≡ ε
    assert(xinvl + xl =~= inverse_word(xl) + xl);
    // (x⁻ˡ + xˡ) + xᵐ ≡ ε + xᵐ =~= xᵐ.
    lemma_concat_word_valid(xinvl, xl, 2);
    lemma_equiv_concat_left(pres_tx(), xinvl + xl, empty_word(), xm);
    assert(concat(xinvl + xl, xm) == (xinvl + xl) + xm);
    assert(concat(empty_word(), xm) =~= xm);
    assert(equiv_in_presentation(pres_tx(), (xinvl + xl) + xm, xm));
    // fam[1] =~= (x⁻ˡ+xˡ)+xᵐ ≡ xᵐ ⟹ fam[1] ≡ xᵐ ⟹ xᵐ ≡ fam[1].
    assert(fam[1] =~= (xinvl + xl) + xm);
    assert(equiv_in_presentation(pres_tx(), fam[1], xm));
    lemma_equiv_symmetric(pres_tx(), fam[1], xm);

    // target[i] ≡ fam[i].
    assert(target.len() == 2);
    assert forall|i: int| 0 <= i < 2 implies equiv_in_presentation(pres_tx(), target[i], fam[i]) by {
        if i == 0 {
            assert(target[0] == config_word(l, 0));
            assert(config_word(l, 0) =~= fam[0]);
            lemma_equiv_refl(pres_tx(), config_word(l, 0));
        } else {
            assert(target[1] == xm);
            assert(equiv_in_presentation(pres_tx(), xm, fam[1]));
        }
    }
    // target entries valid over 2.
    assert forall|i: int| 0 <= i < 2 implies word_valid(#[trigger] target[i], 2) by {
        if i == 0 {
            assert(target[0] == config_word(l, 0));
            // config(l,0) =~= (x⁻ˡ+[t])+xˡ, all over gens {0,1}.
            lemma_concat_word_valid(xinvl, g0, 2);
            lemma_concat_word_valid(xinvl + g0, xl, 2);
            assert(config_word(l, 0) =~= (xinvl + g0) + xl);
        } else {
            assert(target[1] == xm);
        }
    }

    // --- step 4: transfer freeness to target ---
    lemma_free_family_respects_equiv(pres_tx(), fam, target);
}

/// The pre-transvection F-family `[config(l,0), xᵐ, d, b_1, …, b_n]` (`d = Gen2`, `b_j = Gen(2+j)`):
/// `[config(l,0), xᵐ]` followed by the `n+1` free stable letters `Gen2, …, Gen(n+2)`.
pub open spec fn txd_b_family(l: nat, m: nat, n: nat) -> Seq<Word> {
    seq![config_word(l, 0), symbol_power(Symbol::Gen(1), m)]
        + Seq::new((n + 1) as nat, |i: int| seq![Symbol::Gen((2 + i) as nat)])
}

/// **Rungs (ii)/(iii)** — `[config(l,0), xᵐ, d, b_1, …, b_n]` is FREE in `free(n+3)`.  Iterate the
/// generic free-stable-letter tower (`f_free_tower`) `n+1` times over the rung-(i) seed
/// `[config(l,0), xᵐ]` free in `pres_tx = free(2)`: each adjoined `Gen2, …, Gen(n+2)` is a free
/// stable letter, and the tower closed form gives `free_stable_tower(pres_tx, n+1) == free(n+3)` (same
/// `n+3` generators, no relators).  The natural tower order puts `d=Gen2` at index 2 then `b_1..b_n` —
/// exactly φ_F's order modulo `d ↦ b_l·d` (handled by the transvection (iv)).
pub proof fn lemma_txd_b_free(l: nat, m: nat, n: nat)
    requires
        m >= 1,
    ensures
        is_free_family(free_group((n + 3) as nat), txd_b_family(l, m, n)),
{
    let seed = seq![config_word(l, 0), symbol_power(Symbol::Gen(1), m)];
    assert(presentation_valid(pres_tx())) by { reveal(presentation_valid); }
    lemma_tx_image_free(l, m);                                   // is_free_family(pres_tx, seed)
    // iterate the tower n+1 times.
    lemma_free_stable_tower_extends(pres_tx(), seed, (n + 1) as nat);
    // tower == free_group(n+3): num_gens 2+(n+1)=n+3, relators empty.
    lemma_free_stable_tower_closed(pres_tx(), (n + 1) as nat);
    assert(free_stable_tower(pres_tx(), (n + 1) as nat) == free_group((n + 3) as nat)) by {
        assert(free_stable_tower(pres_tx(), (n + 1) as nat).num_generators == 2 + (n + 1));
        assert(free_stable_tower(pres_tx(), (n + 1) as nat).relators == pres_tx().relators);
        assert(pres_tx().relators =~= Seq::<Word>::empty());
        assert(free_group((n + 3) as nat).relators =~= Seq::<Word>::empty());
    }
    // family closed form: seed ++ [Gen2, …, Gen(n+2)] == txd_b_family.
    lemma_free_stable_family_closed(pres_tx(), seed, (n + 1) as nat);
    assert(free_stable_family(pres_tx(), seed, (n + 1) as nat) =~= txd_b_family(l, m, n)) by {
        // free_stable_letter(pres_tx.num_generators=2, i) = [Gen(2+i)].
        assert(Seq::new((n + 1) as nat, |i: int| free_stable_letter(2, i))
            =~= Seq::new((n + 1) as nat, |i: int| seq![Symbol::Gen((2 + i) as nat)]));
    }
}

/// One direction of `lemma_pa_data_isomorphic` (a-side⟹b-side when `fwd`, else b-side⟹a-side).
/// Factored out so each direction's chain (F3 → compose → A1 → free-family-injective) gets a clean
/// context.
proof fn lemma_pa_iso_one_dir(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word, fwd: bool)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(w, pa_data(n, m, betas(alphas)).associations.len() as nat),
        fwd ==> equiv_in_presentation(pa_data(n, m, betas(alphas)).base,
            apply_embedding(Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                |i: int| pa_data(n, m, betas(alphas)).associations[i].0), w), empty_word()),
        !fwd ==> equiv_in_presentation(pa_data(n, m, betas(alphas)).base,
            apply_embedding(Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                |i: int| pa_data(n, m, betas(alphas)).associations[i].1), w), empty_word()),
    ensures
        fwd ==> equiv_in_presentation(pa_data(n, m, betas(alphas)).base,
            apply_embedding(Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                |i: int| pa_data(n, m, betas(alphas)).associations[i].1), w), empty_word()),
        !fwd ==> equiv_in_presentation(pa_data(n, m, betas(alphas)).base,
            apply_embedding(Seq::new(pa_data(n, m, betas(alphas)).associations.len(),
                |i: int| pa_data(n, m, betas(alphas)).associations[i].0), w), empty_word()),
{
    let bet = betas(alphas);
    let pd = pa_data(n, m, bet);
    let rd = recog_data(mm, n, m, alphas);
    let awf = a_words_F(mm, n);
    let h1 = h1_base(mm, n);
    let k = pd.associations.len();
    let pa_a = Seq::new(k, |i: int| pd.associations[i].0);
    let pa_b = Seq::new(k, |i: int| pd.associations[i].1);
    let rd_a = Seq::new(rd.associations.len(), |i: int| rd.associations[i].0);
    let rd_b = Seq::new(rd.associations.len(), |i: int| rd.associations[i].1);

    lemma_betas_index(alphas);
    lemma_pa_data_shape(n, m, bet);
    assert forall|i: int| 0 <= i < bet.len() implies numbers_word(n, m, #[trigger] bet[i]) by {
        if i == 0 { assert(bet[0] == 0); } else { assert(bet[i] == alphas[i - 1]); }
    }
    lemma_pa_data_valid(n, m, bet);
    lemma_h1_base_valid(mm, n);
    lemma_h1_base_num_generators(mm, n);
    lemma_map_a_faithful(mm, n);
    lemma_recog_associations_isomorphic(mm, n, m, alphas);
    lemma_a_col_correspondence(mm, n, m, alphas);
    lemma_b_col_correspondence(mm, n, m, alphas);
    assert(rd_a == compose_embeddings(awf, pa_a));
    assert(rd_b == compose_embeddings(awf, pa_b));
    assert(awf.len() == n + 3);
    assert(rd.associations.len() == bet.len() == k);
    assert(rd.base == h1);

    // awf images valid over h1, pa columns valid over n+3.
    assert forall|i: int| 0 <= i < awf.len() implies word_valid(#[trigger] awf[i], h1.num_generators)
        by {}
    assert forall|i: int| 0 <= i < k implies (word_valid(#[trigger] pa_a[i], awf.len())
        && word_valid(pa_b[i], awf.len())) by {
        assert(pa_a[i] == pd.associations[i].0);
        assert(pa_b[i] == pd.associations[i].1);
    }
    // the two embedded products valid over n+3 = awf.len().
    lemma_apply_embedding_valid(pa_a, w, awf.len());
    lemma_apply_embedding_valid(pa_b, w, awf.len());
    assert(pd.base == free_group(awf.len()));                 // free_group(n+3)

    // A1's iff is stated for words over rd.associations.len() == k.
    assert(word_valid(w, rd.associations.len() as nat));

    if fwd {
        // emb(pa_a, w) ≡_free ε ⟹ F3 ⟹ emb(awf, emb(pa_a,w)) = emb(rd_a, w) ≡_{h1} ε.
        lemma_free_to_embedding(awf, h1, apply_embedding(pa_a, w));
        lemma_apply_embedding_compose(awf, pa_a, w);
        assert(apply_embedding(awf, apply_embedding(pa_a, w))
            == apply_embedding(compose_embeddings(awf, pa_a), w));
        assert(apply_embedding(compose_embeddings(awf, pa_a), w) == apply_embedding(rd_a, w));
        // A1: emb(rd_a, w) ≡ ε ⟺ emb(rd_b, w) ≡ ε.
        assert(equiv_in_presentation(h1, apply_embedding(rd_b, w), empty_word()));
        // emb(rd_b, w) = emb(awf, emb(pa_b, w)).
        lemma_apply_embedding_compose(awf, pa_b, w);
        assert(apply_embedding(rd_b, w) == apply_embedding(awf, apply_embedding(pa_b, w)));
        // injectivity ⟹ emb(pa_b, w) ≡_free ε.
        lemma_free_family_injective(h1, awf, apply_embedding(pa_b, w), empty_word());
        assert(apply_embedding(awf, empty_word()) =~= empty_word());
    } else {
        // mirror: b-side ⟹ a-side.
        lemma_free_to_embedding(awf, h1, apply_embedding(pa_b, w));
        lemma_apply_embedding_compose(awf, pa_b, w);
        assert(apply_embedding(awf, apply_embedding(pa_b, w))
            == apply_embedding(compose_embeddings(awf, pa_b), w));
        assert(apply_embedding(compose_embeddings(awf, pa_b), w) == apply_embedding(rd_b, w));
        assert(equiv_in_presentation(h1, apply_embedding(rd_a, w), empty_word()));
        lemma_apply_embedding_compose(awf, pa_a, w);
        assert(apply_embedding(rd_a, w) == apply_embedding(awf, apply_embedding(pa_a, w)));
        lemma_free_family_injective(h1, awf, apply_embedding(pa_a, w), empty_word());
        assert(apply_embedding(awf, empty_word()) =~= empty_word());
    }
}

} // verus!
