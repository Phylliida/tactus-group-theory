// Layer 2 — Brick 5, C3.2c / the C-arc: the FORWARD (faithful) direction of the unified HNN
// lifting lemma — `emb(map,w) ≡_{h2_II} ε ⟹ w ≡_{P_A} ε`.
//
// The deep Britton-peel (the BOTTLENECK).  KEY SIMPLIFICATION for `map_a`: it maps every `P_A`
// generator to a SINGLE `h2_II` generator (`t↦t, x↦x, d↦d, b_j↦b_j, p↦p`, just relabeling the
// scattered layout indices), so `a_words` is a LENGTH-PRESERVING injective relabeling — the
// pinch-descent is at the SAME indices, and the only real content is the MIDDLE membership
// ("intersection property").  This avoids the template's spanning/run-length case analysis (which
// only arises because the scaling map `x↦xᵖ` changes length).  See `docs/brick5-c3.2c-plan.md` §5.
//
// This module begins with the GENERIC leaves (reused by both the relabel facts and the intersection
// property): free-family injectivity-on-equiv, `apply_embedding` over `concat_all`, and a
// right-cancellation helper.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::{Presentation, equiv_in_presentation, presentation_valid,
    lemma_equiv_transitive, lemma_equiv_symmetric};
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_equiv_concat_right,
    lemma_word_inverse_right, lemma_word_inverse_left};
use crate::benign::{apply_embedding, apply_embedding_symbol, concat_all, in_generated_subgroup,
    lemma_apply_embedding_concat, lemma_apply_embedding_inverse, lemma_apply_embedding_valid};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::f_free::is_free_family;
use crate::machine_group::{ModMachine, g_m, lemma_g_m_num_generators,
    lemma_apply_embedding_in_subgroup, lemma_in_subgroup_respects_equiv};
use crate::layout::{p_idx, d_idx, b_idx};
use crate::h3::phi_assoc;
use crate::h3_ii::{lemma_phi_assoc_index, compose_embeddings, lemma_apply_embedding_compose};
use crate::phi_l_maps::{a_words, lemma_a_words_is_phi_col0};
use crate::normal_form_afp_textbook::lemma_subgroup_to_k_word;

verus! {

// ----------------------------------------------------------------------------
// F2 — the length-preserving relabel (single-generator images).
// ----------------------------------------------------------------------------

/// The relabel target of symbol `s` under a single-generator image list `imgs` (each `imgs[i] =
/// [Gen(gᵢ)]`): `Gen(i) ↦ imgs[i][0] = Gen(gᵢ)`, `Inv(i) ↦ inverse_symbol(imgs[i][0]) = Inv(gᵢ)`.
pub open spec fn relabel_symbol(imgs: Seq<Word>, s: Symbol) -> Symbol {
    match s {
        Symbol::Gen(i) => imgs[i as int][0],
        Symbol::Inv(i) => inverse_symbol(imgs[i as int][0]),
    }
}

/// **Single-gen images ⟹ length-preserving relabel**: if every `imgs[i] = [Gen(gᵢ)]`, then for a
/// valid `w`, `apply_embedding(imgs, w)` has the SAME length as `w` and is the per-symbol relabel
/// `apply_embedding(imgs, w)[k] = relabel_symbol(imgs, w[k])`.  This is why `map_a` (whose images
/// are all single generators) gives a same-index pinch descent — no run/spanning analysis.
pub proof fn lemma_single_gen_relabel(imgs: Seq<Word>, w: Word)
    requires
        word_valid(w, imgs.len()),
        forall|i: int| 0 <= i < imgs.len() ==>
            exists|g: nat| #[trigger] imgs[i] == seq![Symbol::Gen(g)],
    ensures
        apply_embedding(imgs, w).len() == w.len(),
        forall|k: int| 0 <= k < w.len() ==>
            #[trigger] apply_embedding(imgs, w)[k] == relabel_symbol(imgs, w[k]),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_embedding(imgs, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(w =~= seq![s] + rest);
        assert(word_valid(rest, imgs.len())) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(#[trigger] rest[k], imgs.len()) by { assert(rest[k] == w[k + 1]); }
        }
        lemma_single_gen_relabel(imgs, rest);
        reveal_with_fuel(apply_embedding, 2);
        let es = apply_embedding_symbol(imgs, s);
        assert(symbol_valid(s, imgs.len()));
        let g = generator_index(s);
        assert(0 <= g < imgs.len());
        let gg = choose|gg: nat| imgs[g as int] == seq![Symbol::Gen(gg)];
        assert(imgs[g as int] == seq![Symbol::Gen(gg)]);
        // es is the single relabeled symbol.
        assert(es =~= seq![relabel_symbol(imgs, s)]) by {
            match s {
                Symbol::Gen(i) => {
                    assert(i == g);
                    assert(es == imgs[i as int]);
                    assert(relabel_symbol(imgs, s) == imgs[i as int][0]);
                },
                Symbol::Inv(i) => {
                    assert(i == g);
                    assert(es =~= inverse_word(imgs[i as int]));
                    reveal_with_fuel(inverse_word, 2);
                    assert(imgs[i as int][0] == Symbol::Gen(gg));
                    assert(relabel_symbol(imgs, s) == inverse_symbol(Symbol::Gen(gg)));
                },
            }
        }
        assert(es.len() == 1);
        assert(apply_embedding(imgs, w) =~= es + apply_embedding(imgs, rest));
        // length and per-symbol.
        assert(apply_embedding(imgs, w).len() == w.len());
        assert forall|k: int| 0 <= k < w.len()
            implies #[trigger] apply_embedding(imgs, w)[k] == relabel_symbol(imgs, w[k]) by {
            if k == 0 {
                assert(apply_embedding(imgs, w)[0] == es[0]);
                assert(w[0] == s);
            } else {
                assert(apply_embedding(imgs, w)[k] == apply_embedding(imgs, rest)[k - 1]);
                assert(rest[k - 1] == w[k]);
            }
        }
    }
}

/// **Subrange commutes with single-gen relabel**: for single-gen `imgs`,
/// `apply_embedding(imgs, w).subrange(a,b) =~= apply_embedding(imgs, w.subrange(a,b))`.  The
/// pinch-descent uses it to identify the image pinch's middle with the relabel of `w`'s middle.
pub proof fn lemma_single_gen_relabel_subrange(imgs: Seq<Word>, w: Word, a: int, b: int)
    requires
        word_valid(w, imgs.len()),
        forall|i: int| 0 <= i < imgs.len() ==>
            exists|g: nat| #[trigger] imgs[i] == seq![Symbol::Gen(g)],
        0 <= a <= b <= w.len(),
    ensures
        apply_embedding(imgs, w).subrange(a, b) =~= apply_embedding(imgs, w.subrange(a, b)),
{
    let pw = apply_embedding(imgs, w);
    let sub = w.subrange(a, b);
    lemma_single_gen_relabel(imgs, w);
    assert(word_valid(sub, imgs.len())) by {
        assert forall|k: int| 0 <= k < sub.len() implies symbol_valid(#[trigger] sub[k], imgs.len())
        by { assert(sub[k] == w[a + k]); }
    }
    lemma_single_gen_relabel(imgs, sub);
    let lhs = pw.subrange(a, b);
    let rhs = apply_embedding(imgs, sub);
    assert(lhs.len() == b - a);
    assert(rhs.len() == b - a);
    assert forall|k: int| 0 <= k < b - a implies lhs[k] == rhs[k] by {
        assert(lhs[k] == pw[a + k]);
        assert(pw[a + k] == relabel_symbol(imgs, w[a + k]));
        assert(sub[k] == w[a + k]);
        assert(rhs[k] == relabel_symbol(imgs, sub[k]));
    }
}

// ----------------------------------------------------------------------------
// a_words-specific relabel facts (single-gen images, stable-letter correspondence).
// ----------------------------------------------------------------------------

/// Single-generator words are equal iff their indices are: `[Gen(a)] == [Gen(b)] ⟺ a == b`.
proof fn lemma_gen_word_inj(a: nat, b: nat)
    ensures
        (seq![Symbol::Gen(a)] == seq![Symbol::Gen(b)]) <==> (a == b),
{
    if seq![Symbol::Gen(a)] == seq![Symbol::Gen(b)] {
        assert(seq![Symbol::Gen(a)][0] == seq![Symbol::Gen(b)][0]);
    }
}

/// `a_words[i]` is a single generator `[Gen(gᵢ)]`, and `gᵢ == p_idx` (the recog/h2_II stable
/// letter) IFF `i == n+3` (the `P_A` stable letter index).  Via the `phi_assoc` `.0` column:
/// `gᵢ ∈ {0, 1, d_idx} ∪ [b_base, b_base+n)` for `i ≤ n+2`, all `< p_idx`.
pub proof fn lemma_a_words_entry(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < n + 4,
    ensures
        exists|g: nat| a_words(mm, n)[i] == seq![Symbol::Gen(g)],
        a_words(mm, n)[i] == seq![Symbol::Gen(p_idx(g_m(mm).num_generators, n))] <==> i == n + 3,
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                          // nk = 4 + |quads| ≥ 4
    lemma_a_words_is_phi_col0(mm, n, 1, 1);
    let col0 = Seq::new((n + 4) as nat, |k: int| phi_assoc(nk, n, 1, 1)[k].0);
    assert(a_words(mm, n) == col0);
    lemma_phi_assoc_index(nk, n, 1, 1);
    assert(a_words(mm, n)[i] == phi_assoc(nk, n, 1, 1)[i].0);
    let p = p_idx(nk, n);                                  // nk + 2n + 1 ≥ 5
    assert(nk >= 4);
    assert(p == nk + 2 * n + 1);
    // gᵢ — the generator index of a_words[i].
    let gi: nat =
        if i == 0 { 0 }
        else if i == 1 { 1 }
        else if i == 2 { d_idx(nk, n) }
        else if i < n + 3 { b_idx(nk, n, (i - 2) as nat) }
        else { p };
    if i == 0 {
        assert(a_words(mm, n)[i] == seq![Symbol::Gen(gi)]);
        assert(gi != p);
    } else if i == 1 {
        assert(a_words(mm, n)[i] == seq![Symbol::Gen(gi)]);
        assert(gi != p);
    } else if i == 2 {
        assert(a_words(mm, n)[i] == seq![Symbol::Gen(gi)]);
        assert(gi == d_idx(nk, n) && d_idx(nk, n) == nk + 2 * n);
        assert(gi != p);                                   // nk+2n != nk+2n+1
    } else if i < n + 3 {
        let j = i - 3;
        assert(0 <= j < n);
        assert(i == 3 + j);
        assert(phi_assoc(nk, n, 1, 1)[3 + j]
            == (seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))],
                seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]));
        assert((i - 2) as nat == (j + 1) as nat);
        assert(a_words(mm, n)[i] == seq![Symbol::Gen(gi)]);
        assert(gi == b_idx(nk, n, (j + 1) as nat) && b_idx(nk, n, (j + 1) as nat) == nk + n + j);
        assert(gi != p);                                   // nk+n+j ≤ nk+2n-1 < nk+2n+1
    } else {
        assert(i == n + 3);
        assert(a_words(mm, n)[i] == seq![Symbol::Gen(gi)]);
        assert(gi == p);
    }
    assert(gi == p <==> i == n + 3);
    lemma_gen_word_inj(gi, p);                              // [Gen(gi)]==[Gen(p)] ⟺ gi==p
}

/// `a_words` has length `n+4` and all single-generator images — the precondition of
/// `lemma_single_gen_relabel`/`_subrange` at `imgs = a_words`.
pub proof fn lemma_a_words_single_gen(mm: ModMachine, n: nat)
    ensures
        a_words(mm, n).len() == n + 4,
        forall|i: int| 0 <= i < a_words(mm, n).len() ==>
            exists|g: nat| #[trigger] a_words(mm, n)[i] == seq![Symbol::Gen(g)],
{
    lemma_g_m_num_generators(mm);
    lemma_a_words_is_phi_col0(mm, n, 1, 1);
    assert(a_words(mm, n).len() == n + 4);
    assert forall|i: int| 0 <= i < a_words(mm, n).len()
        implies exists|g: nat| #[trigger] a_words(mm, n)[i] == seq![Symbol::Gen(g)] by {
        lemma_a_words_entry(mm, n, i);
    }
}

/// **The relabel preserves the stable letter exactly**: under `ρ = relabel_symbol(a_words, ·)`, a
/// symbol relabels to the recog stable letter `Gen(p_idx)` / `Inv(p_idx)` IFF it IS the `P_A`
/// stable letter `Gen(n+3)` / `Inv(n+3)`.  (Gen/Inv orientation preserved; F-gens ↦ non-stable.)
/// This transfers `has_adjacent_opposite_at` between `recog_data` and `pa_data` at the same indices.
pub proof fn lemma_a_words_relabel_sym(mm: ModMachine, n: nat, s: Symbol)
    requires
        symbol_valid(s, (n + 4) as nat),
    ensures
        (relabel_symbol(a_words(mm, n), s) == Symbol::Gen(p_idx(g_m(mm).num_generators, n))
            <==> s == Symbol::Gen((n + 3) as nat)),
        (relabel_symbol(a_words(mm, n), s) == Symbol::Inv(p_idx(g_m(mm).num_generators, n))
            <==> s == Symbol::Inv((n + 3) as nat)),
{
    let nk = g_m(mm).num_generators;
    let p = p_idx(nk, n);
    let i = generator_index(s);
    assert(0 <= i < n + 4);
    lemma_a_words_entry(mm, n, i as int);
    let g = choose|g: nat| a_words(mm, n)[i as int] == seq![Symbol::Gen(g)];
    assert(a_words(mm, n)[i as int] == seq![Symbol::Gen(g)]);
    assert(a_words(mm, n)[i as int][0] == Symbol::Gen(g));
    // g == p  ⟺  i == n+3.
    assert(g == p <==> i == n + 3) by {
        if g == p {
            assert(a_words(mm, n)[i as int] == seq![Symbol::Gen(p)]);
        }
        if i == n + 3 {
            assert(a_words(mm, n)[i as int] == seq![Symbol::Gen(p)]);
            assert(seq![Symbol::Gen(g)] == seq![Symbol::Gen(p)]);
        }
    }
    match s {
        Symbol::Gen(ii) => {
            assert(ii == i);
            assert(relabel_symbol(a_words(mm, n), s) == a_words(mm, n)[i as int][0]);
            assert(relabel_symbol(a_words(mm, n), s) == Symbol::Gen(g));
        },
        Symbol::Inv(ii) => {
            assert(ii == i);
            assert(relabel_symbol(a_words(mm, n), s) == inverse_symbol(a_words(mm, n)[i as int][0]));
            assert(inverse_symbol(Symbol::Gen(g)) == Symbol::Inv(g));
            assert(relabel_symbol(a_words(mm, n), s) == Symbol::Inv(g));
        },
    }
}

/// **`apply_embedding` distributes over `concat_all`**: `apply_embedding(imgs, concat_all(fs)) =~=
/// concat_all(fs.map(apply_embedding(imgs, ·)))`.  (Induction on `fs`, mirror
/// `ii_subset::lemma_kill_t_concat_all_trivial`'s structure.)  The pullback engine of the
/// intersection property uses it to turn a `recog`-gen factorization into a `pa`-gen one.
pub proof fn lemma_apply_embedding_concat_all(imgs: Seq<Word>, factors: Seq<Word>)
    ensures
        apply_embedding(imgs, concat_all(factors))
            =~= concat_all(Seq::new(factors.len(), |k: int| apply_embedding(imgs, factors[k]))),
    decreases factors.len(),
{
    let mapped = Seq::new(factors.len(), |k: int| apply_embedding(imgs, factors[k]));
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
        reveal_with_fuel(apply_embedding, 2);
        assert(mapped.len() == 0);
        assert(concat_all(mapped) =~= empty_word());
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        lemma_apply_embedding_concat_all(imgs, rest);
        assert(concat_all(factors) =~= concat(first, concat_all(rest)));
        lemma_apply_embedding_concat(imgs, first, concat_all(rest));
        let restmapped = Seq::new(rest.len(), |k: int| apply_embedding(imgs, rest[k]));
        assert(mapped.first() == apply_embedding(imgs, first));
        assert(mapped.drop_first() =~= restmapped) by {
            assert forall|k: int| 0 <= k < restmapped.len() implies
                mapped.drop_first()[k] == restmapped[k] by {
                assert(mapped.drop_first()[k] == mapped[k + 1]);
                assert(rest[k] == factors[k + 1]);
            }
        }
        assert(concat_all(mapped) =~= concat(mapped.first(), concat_all(mapped.drop_first())));
    }
}

/// **Right-cancellation**: `u·v⁻¹ ≡_p ε ⟹ u ≡_p v`.  (`u ≡ u·(v⁻¹·v) = (u·v⁻¹)·v ≡ ε·v = v`.)
pub proof fn lemma_cancel_inverse_to_equiv(p: Presentation, u: Word, v: Word)
    requires
        presentation_valid(p),
        word_valid(u, p.num_generators),
        word_valid(v, p.num_generators),
        equiv_in_presentation(p, u + inverse_word(v), empty_word()),
    ensures
        equiv_in_presentation(p, u, v),
{
    let ng = p.num_generators;
    let uvi = u + inverse_word(v);
    lemma_inverse_word_valid(v, ng);
    lemma_concat_word_valid(u, inverse_word(v), ng);
    lemma_concat_word_valid(inverse_word(v), v, ng);

    // Fact A:  u·(v⁻¹·v) ≡ u   (since v⁻¹·v ≡ ε).
    lemma_word_inverse_left(p, v);                                  // v⁻¹·v ≡ ε
    lemma_equiv_concat_right(p, u, inverse_word(v) + v, empty_word());
    assert(concat(inverse_word(v), v) == inverse_word(v) + v);
    assert(concat(u, inverse_word(v) + v) == u + (inverse_word(v) + v));
    assert(concat(u, empty_word()) =~= u);
    assert(equiv_in_presentation(p, u + (inverse_word(v) + v), u));   // Fact A

    // Fact B:  u·(v⁻¹·v) =~= (u·v⁻¹)·v   (associativity).
    assert(u + (inverse_word(v) + v) =~= uvi + v);

    // Fact C:  (u·v⁻¹)·v ≡ v   (since u·v⁻¹ ≡ ε).
    lemma_equiv_concat_left(p, uvi, empty_word(), v);
    assert(concat(uvi, v) == uvi + v);
    assert(concat(empty_word(), v) =~= v);
    assert(equiv_in_presentation(p, uvi + v, v));                    // Fact C

    // chain:  u ≡ (u·v⁻¹)·v ≡ v.
    lemma_concat_word_valid(uvi, v, ng);
    lemma_equiv_symmetric(p, uvi + v, u);                            // u ≡ uvi+v   (from Fact A + B)
    lemma_equiv_transitive(p, u, uvi + v, v);                        // u ≡ v       (with Fact C)
}

/// **Free family ⟹ injective on equivalence**: for a free family `gens` in `gp`, words `u,v` over
/// `gens.len()` with `emb(gens,u) ≡_{gp} emb(gens,v)` satisfy `u ≡_{free} v`.  (Standard:
/// `emb(gens, u·v⁻¹) ≡ ε ⟹ (freeness) u·v⁻¹ ≡_free ε ⟹ (cancel) u ≡_free v`.)  This is the
/// `ψ`-injectivity the intersection property needs.
pub proof fn lemma_free_family_injective(gp: Presentation, gens: Seq<Word>, u: Word, v: Word)
    requires
        presentation_valid(gp),
        is_free_family(gp, gens),
        word_valid(u, gens.len()),
        word_valid(v, gens.len()),
        equiv_in_presentation(gp, apply_embedding(gens, u), apply_embedding(gens, v)),
    ensures
        equiv_in_presentation(free_group(gens.len()), u, v),
{
    let k = gens.len();
    let fg = free_group(k);
    lemma_free_group_valid(k);
    assert(fg.num_generators == k);
    let eu = apply_embedding(gens, u);
    let ev = apply_embedding(gens, v);

    // emb(gens,u·v⁻¹) =~= eu·ev⁻¹.
    let uv = u + inverse_word(v);
    lemma_inverse_word_valid(v, k);
    lemma_concat_word_valid(u, inverse_word(v), k);
    lemma_apply_embedding_concat(gens, u, inverse_word(v));
    lemma_apply_embedding_inverse(gens, v);
    assert(apply_embedding(gens, uv) =~= eu + inverse_word(ev));

    // eu, ev valid over gp.num_generators (gens are gp-words).
    lemma_apply_embedding_valid(gens, u, gp.num_generators);
    lemma_apply_embedding_valid(gens, v, gp.num_generators);
    lemma_inverse_word_valid(ev, gp.num_generators);
    lemma_concat_word_valid(ev, inverse_word(ev), gp.num_generators);

    // eu·ev⁻¹ ≡_{gp} ε  (eu ≡ ev).
    lemma_equiv_concat_left(gp, eu, ev, inverse_word(ev));          // eu·ev⁻¹ ≡ ev·ev⁻¹
    lemma_word_inverse_right(gp, ev);                              // ev·ev⁻¹ ≡ ε
    assert(concat(eu, inverse_word(ev)) == eu + inverse_word(ev));
    assert(concat(ev, inverse_word(ev)) == ev + inverse_word(ev));
    lemma_equiv_transitive(gp, eu + inverse_word(ev), ev + inverse_word(ev), empty_word());
    assert(equiv_in_presentation(gp, apply_embedding(gens, uv), empty_word()));

    // freeness ⟹ uv ≡_free ε.
    assert(word_valid(uv, gens.len()));
    assert(equiv_in_presentation(fg, uv, empty_word()));

    // cancellation ⟹ u ≡_free v.
    lemma_cancel_inverse_to_equiv(fg, u, v);
}

// ----------------------------------------------------------------------------
// F4 — the intersection property (the heart of the pinch descent).
// ----------------------------------------------------------------------------

/// **The intersection property (generic)**: if the recog gens are `ψ`-images of the `pa` gens
/// (`recog_gens = compose_embeddings(ψ, pa_gens)` = the column correspondence), `ψ` is a free family
/// in `gp`, and `ψ(u) ∈ ⟨recog_gens⟩` in `gp`, then `u ∈ ⟨pa_gens⟩` in the free group.  This is
/// `ψ(F) ∩ AssocSub(gp) = ψ(AssocSub(free))` — exactly the descent the spanning pinch case needs.
///
/// Route: pull `ψ(u)` back to a preimage word `h` over the recog gens (`lemma_subgroup_to_k_word`);
/// `apply_embedding(recog_gens, h) = ψ(apply_embedding(pa_gens, h))` (composition); injectivity of
/// `ψ` (`lemma_free_family_injective`) descends `apply_embedding(pa_gens, h) ≡_{free} u`; and that
/// embedded product is visibly a `⟨pa_gens⟩`-member, transported to `u` by equiv-respect.
pub proof fn lemma_intersection_property(
    gp: Presentation, psi: Seq<Word>, pa_gens: Seq<Word>, u: Word)
    requires
        presentation_valid(gp),
        is_free_family(gp, psi),
        word_valid(u, psi.len()),
        forall|k: int| 0 <= k < pa_gens.len() ==> word_valid(#[trigger] pa_gens[k], psi.len()),
        in_generated_subgroup(gp, compose_embeddings(psi, pa_gens), apply_embedding(psi, u)),
    ensures
        in_generated_subgroup(free_group(psi.len()), pa_gens, u),
{
    let k = psi.len();
    let fg = free_group(k);
    lemma_free_group_valid(k);
    let recog_gens = compose_embeddings(psi, pa_gens);
    let psi_u = apply_embedding(psi, u);
    assert(recog_gens.len() == pa_gens.len());

    // pull back ψ(u) to a preimage word over the recog gens.
    lemma_subgroup_to_k_word(gp, recog_gens, psi_u);
    let h = choose|h: Word| word_valid(h, recog_gens.len())
        && equiv_in_presentation(gp, apply_embedding(recog_gens, h), psi_u);
    assert(word_valid(h, recog_gens.len())
        && equiv_in_presentation(gp, apply_embedding(recog_gens, h), psi_u));
    assert(word_valid(h, pa_gens.len()));

    // apply_embedding(recog_gens, h) = ψ(apply_embedding(pa_gens, h)).
    lemma_apply_embedding_compose(psi, pa_gens, h);
    let ph = apply_embedding(pa_gens, h);
    assert(apply_embedding(recog_gens, h) =~= apply_embedding(psi, ph));

    // so ψ(ph) ≡_{gp} ψ(u);  injectivity ⟹ ph ≡_{free} u.
    lemma_apply_embedding_valid(pa_gens, h, k);                  // ph valid over k
    assert(equiv_in_presentation(gp, apply_embedding(psi, ph), apply_embedding(psi, u)));
    lemma_free_family_injective(gp, psi, ph, u);
    assert(equiv_in_presentation(fg, ph, u));

    // ph ∈ ⟨pa_gens⟩, and ph ≡_{free} u ⟹ u ∈ ⟨pa_gens⟩.
    lemma_apply_embedding_in_subgroup(fg, pa_gens, h);
    lemma_in_subgroup_respects_equiv(fg, pa_gens, ph, u);
}

} // verus!
