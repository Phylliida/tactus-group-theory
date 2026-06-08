use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::reduction::*;

verus! {

///  Data defining a group homomorphism via generator images.
pub struct HomomorphismData {
    pub source: Presentation,
    pub target: Presentation,
    pub generator_images: Seq<Word>,
}

///  Image of a single symbol under the homomorphism.
pub open spec fn apply_hom_symbol(h: HomomorphismData, s: Symbol) -> Word {
    match s {
        Symbol::Gen(i) => h.generator_images[i as int],
        Symbol::Inv(i) => inverse_word(h.generator_images[i as int]),
    }
}

///  Image of a word under the homomorphism.
pub open spec fn apply_hom(h: HomomorphismData, w: Word) -> Word
    decreases w.len(),
{
    if w.len() == 0 {
        empty_word()
    } else {
        concat(apply_hom_symbol(h, w.first()), apply_hom(h, w.drop_first()))
    }
}

///  A homomorphism is valid if images.len() == num_generators,
///  both presentations are valid, generator images are word_valid,
///  and each relator image ≡ ε.
pub open spec fn is_valid_homomorphism(h: HomomorphismData) -> bool {
    h.generator_images.len() == h.source.num_generators
    && presentation_valid(h.source)
    && presentation_valid(h.target)
    && (forall|i: int| 0 <= i < h.generator_images.len() ==>
        word_valid(h.generator_images[i], h.target.num_generators))
    && (forall|i: int| 0 <= i < h.source.relators.len() ==>
        equiv_in_presentation(h.target, apply_hom(h, h.source.relators[i]), empty_word()))
}

///  The identity homomorphism: Gen(i) → [Gen(i)].
pub open spec fn identity_hom(p: Presentation) -> HomomorphismData {
    HomomorphismData {
        source: p,
        target: p,
        generator_images: Seq::new(p.num_generators, |i: int| {
            Seq::new(1, |_j: int| Symbol::Gen(i as nat))
        }),
    }
}

///  Composition of homomorphisms.
pub open spec fn compose_hom(h1: HomomorphismData, h2: HomomorphismData) -> HomomorphismData {
    HomomorphismData {
        source: h1.source,
        target: h2.target,
        generator_images: Seq::new(h1.generator_images.len(), |i: int| {
            apply_hom(h2, h1.generator_images[i])
        }),
    }
}

//  --- Helpers ---

///  apply_hom of a singleton word.
pub proof fn lemma_hom_singleton(h: HomomorphismData, s: Symbol)
    ensures
        apply_hom(h, Seq::new(1, |_i: int| s)) =~= apply_hom_symbol(h, s),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.first() == s);
    let tail = w.drop_first();
    assert(tail.len() == 0);
    //  apply_hom(h, w) = concat(apply_hom_symbol(h, s), apply_hom(h, tail))
    //  apply_hom(h, tail) = empty_word() because tail.len() == 0
    assert(apply_hom(h, tail) =~= empty_word());
    //  concat(x, empty) =~= x
    assert(concat(apply_hom_symbol(h, s), empty_word()) =~= apply_hom_symbol(h, s));
}

///  Image of a single symbol is word_valid for target.
proof fn lemma_apply_hom_symbol_word_valid(h: HomomorphismData, s: Symbol)
    requires
        is_valid_homomorphism(h),
        symbol_valid(s, h.source.num_generators),
    ensures
        word_valid(apply_hom_symbol(h, s), h.target.num_generators),
{
    match s {
        Symbol::Gen(i) => {},
        Symbol::Inv(i) => {
            crate::word::lemma_inverse_word_valid(
                h.generator_images[i as int], h.target.num_generators);
        },
    }
}

///  Image of a word under a valid homomorphism is word_valid for target.
pub proof fn lemma_apply_hom_word_valid(h: HomomorphismData, w: Word)
    requires
        is_valid_homomorphism(h),
        word_valid(w, h.source.num_generators),
    ensures
        word_valid(apply_hom(h, w), h.target.num_generators),
    decreases w.len(),
{
    if w.len() > 0 {
        let s = w.first();
        let rest = w.drop_first();
        assert(word_valid(rest, h.source.num_generators)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(rest[i], h.source.num_generators)
            by { assert(rest[i] == w[i + 1]); }
        }
        lemma_apply_hom_symbol_word_valid(h, s);
        lemma_apply_hom_word_valid(h, rest);
        crate::word::lemma_concat_word_valid(
            apply_hom_symbol(h, s), apply_hom(h, rest), h.target.num_generators);
    }
}

///  concat(x, suffix) ≡ suffix when x ≡ ε.
pub proof fn lemma_identity_prefix_equiv(p: Presentation, x: Word, suffix: Word)
    requires
        equiv_in_presentation(p, x, empty_word()),
    ensures
        equiv_in_presentation(p, concat(x, suffix), suffix),
{
    lemma_equiv_concat_left(p, x, empty_word(), suffix);
    assert(concat(empty_word(), suffix) =~= suffix);
    lemma_equiv_refl(p, suffix);
    lemma_equiv_transitive(p, concat(x, suffix), concat(empty_word(), suffix), suffix);
}

///  hom(r) ≡ ε for an inverted relator.
proof fn lemma_inverted_relator_image_is_identity(h: HomomorphismData, relator_index: nat)
    requires
        is_valid_homomorphism(h),
        0 <= relator_index < h.source.relators.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, inverse_word(h.source.relators[relator_index as int])),
            empty_word(),
        ),
{
    reveal(presentation_valid);
    let orig_r = h.source.relators[relator_index as int];
    let hom_orig = apply_hom(h, orig_r);

    //  word_valid facts for lemma_equiv_symmetric calls
    assert(word_valid(orig_r, h.source.num_generators));
    lemma_apply_hom_word_valid(h, orig_r);
    let n = h.target.num_generators;
    crate::word::lemma_inverse_word_valid(hom_orig, n);
    crate::word::lemma_concat_word_valid(inverse_word(hom_orig), hom_orig, n);

    lemma_hom_respects_inverse(h, orig_r);

    lemma_word_inverse_left(h.target, hom_orig);
    lemma_equiv_symmetric(h.target, hom_orig, empty_word());
    lemma_equiv_concat_right(h.target, inverse_word(hom_orig), hom_orig, empty_word());
    assert(concat(inverse_word(hom_orig), empty_word()) =~= inverse_word(hom_orig));

    crate::word::lemma_concat_word_valid(inverse_word(hom_orig), empty_word(), n);
    lemma_equiv_symmetric(h.target,
        concat(inverse_word(hom_orig), hom_orig),
        concat(inverse_word(hom_orig), empty_word()),
    );
    lemma_equiv_transitive(h.target,
        inverse_word(hom_orig),
        concat(inverse_word(hom_orig), hom_orig),
        empty_word(),
    );

    assert(apply_hom(h, inverse_word(orig_r)) =~= inverse_word(hom_orig));
}

///  hom_r ≡ ε for either direct or inverted relator.
proof fn lemma_relator_image_is_identity(h: HomomorphismData, relator_index: nat, inverted: bool)
    requires
        is_valid_homomorphism(h),
        0 <= relator_index < h.source.relators.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, get_relator(h.source, relator_index, inverted)),
            empty_word(),
        ),
{
    if inverted {
        lemma_inverted_relator_image_is_identity(h, relator_index);
    }
}

//  --- Main Lemmas ---

///  Homomorphism of empty word is empty.
pub proof fn lemma_hom_empty(h: HomomorphismData)
    ensures
        apply_hom(h, empty_word()) =~= empty_word(),
{
}

///  Homomorphism respects concatenation.
pub proof fn lemma_hom_respects_concat(h: HomomorphismData, w1: Word, w2: Word)
    ensures
        apply_hom(h, concat(w1, w2)) =~= concat(apply_hom(h, w1), apply_hom(h, w2)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(apply_hom(h, w1) =~= empty_word());
    } else {
        let s = w1.first();
        let rest = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest, w2));
        lemma_hom_respects_concat(h, rest, w2);
        lemma_concat_assoc(apply_hom_symbol(h, s), apply_hom(h, rest), apply_hom(h, w2));
    }
}

///  Homomorphism respects word inverse.
pub proof fn lemma_hom_respects_inverse(h: HomomorphismData, w: Word)
    ensures
        apply_hom(h, inverse_word(w)) =~= inverse_word(apply_hom(h, w)),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();

        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        assert(inverse_word(w) =~= concat(inverse_word(rest), inv_s_word));
        lemma_hom_respects_concat(h, inverse_word(rest), inv_s_word);
        lemma_hom_respects_inverse(h, rest);
        lemma_hom_singleton(h, inverse_symbol(s));

        match s {
            Symbol::Gen(_idx) => {},
            Symbol::Inv(idx) => {
                crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
            },
        }

        lemma_inverse_concat(apply_hom_symbol(h, s), apply_hom(h, rest));
    }
}

///  Homomorphism preserves a single derivation step.
pub proof fn lemma_hom_preserves_single_step(
    h: HomomorphismData,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        is_valid_homomorphism(h),
        apply_step(h.source, w, step) == Some(w_prime),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, w_prime)),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            lemma_hom_preserves_free_reduce(h, w, position);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            lemma_hom_preserves_free_expand(h, w, position, symbol);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            lemma_hom_preserves_relator_insert(h, w, position, relator_index, inverted);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            lemma_hom_preserves_relator_delete(h, w, position, relator_index, inverted);
        },
    }
}

///  Helper: hom preserves FreeReduce step.
proof fn lemma_hom_preserves_free_reduce(
    h: HomomorphismData, w: Word, position: int,
)
    requires
        is_valid_homomorphism(h),
        has_cancellation_at(w, position),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, reduce_at(w, position))),
{
    let s1 = w[position];
    let s2 = w[position + 1];

    let prefix = w.subrange(0, position);
    let s1_word = Seq::new(1, |_i: int| s1);
    let s2_word = Seq::new(1, |_i: int| s2);
    let pair = s1_word + s2_word;
    let suffix = w.subrange(position + 2, w.len() as int);
    assert(w =~= (prefix + pair) + suffix);

    let reduced = reduce_at(w, position);
    assert(reduced =~= prefix + suffix);

    //  Decompose w = (prefix + pair) + suffix
    lemma_hom_respects_concat(h, prefix + pair, suffix);
    lemma_hom_respects_concat(h, prefix, pair);
    lemma_hom_respects_concat(h, s1_word, s2_word);
    lemma_hom_respects_concat(h, prefix, suffix);

    lemma_hom_singleton(h, s1);
    lemma_hom_singleton(h, s2);

    let img_s1 = apply_hom_symbol(h, s1);
    let img_s2 = apply_hom_symbol(h, s2);

    //  img_s2 = inverse_word(img_s1)
    match s1 {
        Symbol::Gen(_idx) => {},
        Symbol::Inv(idx) => {
            crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    lemma_word_inverse_right(h.target, img_s1);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let pair_img = concat(img_s1, img_s2);

    //  apply_hom(w) =~= concat(concat(hom_prefix, pair_img), hom_suffix)
    //  We need: concat(concat(hom_prefix, pair_img), hom_suffix)
    //        =~= concat(hom_prefix, concat(pair_img, hom_suffix))
    lemma_concat_assoc(hom_prefix, pair_img, hom_suffix);

    //  pair_img ≡ ε → concat(pair_img, hom_suffix) ≡ hom_suffix
    lemma_identity_prefix_equiv(h.target, pair_img, hom_suffix);
    //  concat(hom_prefix, concat(pair_img, hom_suffix)) ≡ concat(hom_prefix, hom_suffix)
    lemma_equiv_concat_right(h.target, hom_prefix, concat(pair_img, hom_suffix), hom_suffix);
}

///  Helper: hom preserves FreeExpand step.
proof fn lemma_hom_preserves_free_expand(
    h: HomomorphismData, w: Word, position: int, symbol: Symbol,
)
    requires
        is_valid_homomorphism(h),
        0 <= position <= w.len(),
        symbol_valid(symbol, h.source.num_generators),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w, DerivationStep::FreeExpand { position, symbol }).unwrap()),
        ),
{
    let s_word = Seq::new(1, |_i: int| symbol);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(symbol));
    let pair = s_word + inv_s_word;
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = (prefix + pair) + suffix;
    assert(w =~= prefix + suffix);

    lemma_hom_respects_concat(h, prefix, suffix);
    lemma_hom_respects_concat(h, prefix + pair, suffix);
    lemma_hom_respects_concat(h, prefix, pair);
    lemma_hom_respects_concat(h, s_word, inv_s_word);

    lemma_hom_singleton(h, symbol);
    lemma_hom_singleton(h, inverse_symbol(symbol));

    let img_s = apply_hom_symbol(h, symbol);
    let img_inv_s = apply_hom_symbol(h, inverse_symbol(symbol));

    match symbol {
        Symbol::Gen(_idx) => {},
        Symbol::Inv(idx) => {
            crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    lemma_word_inverse_right(h.target, img_s);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let pair_img = concat(img_s, img_inv_s);

    //  apply_hom(w_prime) =~= concat(concat(hom_prefix, pair_img), hom_suffix)
    //                     =~= concat(hom_prefix, concat(pair_img, hom_suffix))
    lemma_concat_assoc(hom_prefix, pair_img, hom_suffix);

    //  pair_img ≡ ε
    //  symmetric: ε ≡ pair_img (need word_valid(pair_img) — provable from symbol_valid)
    lemma_apply_hom_symbol_word_valid(h, symbol);
    crate::symbol::lemma_inverse_preserves_valid(symbol, h.source.num_generators);
    lemma_apply_hom_symbol_word_valid(h, inverse_symbol(symbol));
    crate::word::lemma_concat_word_valid(img_s, img_inv_s, h.target.num_generators);
    lemma_equiv_symmetric(h.target, pair_img, empty_word());

    //  ε ≡ pair_img → concat(ε, hom_suffix) ≡ concat(pair_img, hom_suffix)
    lemma_equiv_concat_left(h.target, empty_word(), pair_img, hom_suffix);
    //  concat(ε, hom_suffix) =~= hom_suffix
    //  concat(hom_prefix, concat(ε, hom_suffix)) ≡ concat(hom_prefix, concat(pair_img, hom_suffix))
    lemma_equiv_concat_right(h.target, hom_prefix,
        concat(empty_word(), hom_suffix), concat(pair_img, hom_suffix));

    //  apply_hom(w) =~= concat(hom_prefix, hom_suffix) =~= concat(hom_prefix, concat(ε, hom_suffix))
    //  apply_hom(w_prime) =~= concat(hom_prefix, concat(pair_img, hom_suffix))
}

///  Helper: hom preserves RelatorInsert step.
proof fn lemma_hom_preserves_relator_insert(
    h: HomomorphismData, w: Word,
    position: int, relator_index: nat, inverted: bool,
)
    requires
        is_valid_homomorphism(h),
        0 <= position <= w.len(),
        0 <= relator_index < h.source.relators.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w,
                DerivationStep::RelatorInsert { position, relator_index, inverted }).unwrap()),
        ),
{
    reveal(presentation_valid);
    let r = get_relator(h.source, relator_index, inverted);
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = (prefix + r) + suffix;
    assert(w =~= prefix + suffix);

    lemma_hom_respects_concat(h, prefix, suffix);
    lemma_hom_respects_concat(h, prefix + r, suffix);
    lemma_hom_respects_concat(h, prefix, r);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let hom_r = apply_hom(h, r);

    lemma_relator_image_is_identity(h, relator_index, inverted);

    //  apply_hom(w_prime) =~= concat(concat(hom_prefix, hom_r), hom_suffix)
    //                     =~= concat(hom_prefix, concat(hom_r, hom_suffix))
    lemma_concat_assoc(hom_prefix, hom_r, hom_suffix);

    //  hom_r ≡ ε → symmetric: ε ≡ hom_r
    //  Prove word_valid(hom_r) for symmetric call
    let rel = get_relator(h.source, relator_index, inverted);
    assert(word_valid(h.source.relators[relator_index as int], h.source.num_generators));
    if inverted {
        crate::word::lemma_inverse_word_valid(
            h.source.relators[relator_index as int], h.source.num_generators);
    }
    lemma_apply_hom_word_valid(h, rel);
    lemma_equiv_symmetric(h.target, hom_r, empty_word());

    //  ε ≡ hom_r → concat(ε, hom_suffix) ≡ concat(hom_r, hom_suffix)
    lemma_equiv_concat_left(h.target, empty_word(), hom_r, hom_suffix);
    //  concat(hom_prefix, concat(ε, hom_suffix)) ≡ concat(hom_prefix, concat(hom_r, hom_suffix))
    lemma_equiv_concat_right(h.target, hom_prefix,
        concat(empty_word(), hom_suffix), concat(hom_r, hom_suffix));
    //  apply_hom(w) =~= concat(hom_prefix, hom_suffix) =~= concat(hom_prefix, concat(ε, hom_suffix))
}

///  Helper: hom preserves RelatorDelete step.
proof fn lemma_hom_preserves_relator_delete(
    h: HomomorphismData, w: Word,
    position: int, relator_index: nat, inverted: bool,
)
    requires
        is_valid_homomorphism(h),
        0 <= relator_index < h.source.relators.len(),
        apply_step(h.source, w, DerivationStep::RelatorDelete { position, relator_index, inverted }) is Some,
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w,
                DerivationStep::RelatorDelete { position, relator_index, inverted }).unwrap()),
        ),
{
    let r = get_relator(h.source, relator_index, inverted);
    let rlen = r.len();
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position + rlen as int, w.len() as int);
    let w_prime = prefix + suffix;
    assert(w.subrange(position, position + rlen as int) == r);
    assert(w =~= (prefix + r) + suffix);

    lemma_hom_respects_concat(h, prefix + r, suffix);
    lemma_hom_respects_concat(h, prefix, r);
    lemma_hom_respects_concat(h, prefix, suffix);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let hom_r = apply_hom(h, r);

    lemma_relator_image_is_identity(h, relator_index, inverted);

    //  apply_hom(w) =~= concat(concat(hom_prefix, hom_r), hom_suffix)
    //               =~= concat(hom_prefix, concat(hom_r, hom_suffix))
    lemma_concat_assoc(hom_prefix, hom_r, hom_suffix);

    lemma_identity_prefix_equiv(h.target, hom_r, hom_suffix);
    lemma_equiv_concat_right(h.target, hom_prefix, concat(hom_r, hom_suffix), hom_suffix);
}

///  Homomorphism preserves a derivation (sequence of steps).
pub proof fn lemma_hom_preserves_derivation(
    h: HomomorphismData,
    steps: Seq<DerivationStep>, w: Word, w_prime: Word,
)
    requires
        is_valid_homomorphism(h),
        derivation_produces(h.source, steps, w) == Some(w_prime),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, w_prime)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        lemma_equiv_refl(h.target, apply_hom(h, w));
    } else {
        let step = steps.first();
        let rest = steps.drop_first();
        let w_mid = apply_step(h.source, w, step).unwrap();

        lemma_hom_preserves_single_step(h, w, step, w_mid);
        lemma_hom_preserves_derivation(h, rest, w_mid, w_prime);
        lemma_equiv_transitive(h.target,
            apply_hom(h, w), apply_hom(h, w_mid), apply_hom(h, w_prime));
    }
}

///  **Main theorem**: Homomorphisms preserve equivalence.
pub proof fn lemma_hom_preserves_equiv(
    h: HomomorphismData, w1: Word, w2: Word,
)
    requires
        is_valid_homomorphism(h),
        equiv_in_presentation(h.source, w1, w2),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w1), apply_hom(h, w2)),
{
    let d = choose|d: Derivation| derivation_valid(h.source, d, w1, w2);
    lemma_hom_preserves_derivation(h, d.steps, w1, w2);
}

///  The identity homomorphism is valid (for valid presentations).
pub proof fn lemma_identity_hom_valid(p: Presentation)
    requires
        presentation_valid(p),
    ensures
        is_valid_homomorphism(identity_hom(p)),
{
    reveal(presentation_valid);
    let h = identity_hom(p);
    assert(h.generator_images.len() == p.num_generators);

    assert forall|i: int| 0 <= i < p.relators.len() implies
        equiv_in_presentation(h.target, apply_hom(h, h.source.relators[i]), empty_word())
    by {
        let r = p.relators[i];
        assert(word_valid(r, p.num_generators));
        lemma_identity_hom_apply(h, r, p.num_generators);
        assert(apply_hom(h, r) =~= r);
        lemma_relator_is_identity(p, i);
    }
}

///  Helper: identity homomorphism preserves valid words.
proof fn lemma_identity_hom_apply(h: HomomorphismData, w: Word, n: nat)
    requires
        h.generator_images.len() == n,
        forall|i: int| 0 <= i < n ==>
            h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen(i as nat)),
        word_valid(w, n),
    ensures
        apply_hom(h, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, n));
        assert(word_valid(rest, n)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(rest[i], n) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_identity_hom_apply(h, rest, n);

        match s {
            Symbol::Gen(idx) => {
                assert(generator_index(s) == idx);
                assert((idx as int) < (n as int));
                assert(h.generator_images[idx as int] =~= Seq::new(1, |_j: int| Symbol::Gen(idx)));
            },
            Symbol::Inv(idx) => {
                assert(generator_index(s) == idx);
                assert((idx as int) < (n as int));
                assert(h.generator_images[idx as int] =~= Seq::new(1, |_j: int| Symbol::Gen(idx)));
                lemma_inverse_singleton(Symbol::Gen(idx));
            },
        }
        assert(concat(Seq::new(1, |_j: int| s), rest) =~= w);
    }
}

} //  verus!
