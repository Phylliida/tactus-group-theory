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
use crate::benign::{apply_embedding, concat_all, lemma_apply_embedding_concat,
    lemma_apply_embedding_inverse, lemma_apply_embedding_valid};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::f_free::is_free_family;

verus! {

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

} // verus!
