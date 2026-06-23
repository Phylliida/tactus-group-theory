use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::*;

verus! {

//  ============================================================
//  FORK-A brick FA-5 — predicate-base homomorphisms (2026-06-23).
//
//  Predicate-base analog of `homomorphism.rs`, over `PredPresentation`
//  (source/target relators carried as `spec_fn(Word) -> bool`).  This is the
//  BOTTOM brick of the AFP normal-form / Britton-tower port that Layer-2
//  faithfulness needs: free-product injectivity (`normal_form_free_product.rs`)
//  is proven via RETRACTION homomorphisms, and those route through
//  `lemma_hom_preserves_equiv` here.  Everything above it
//  (`normal_form_amalgamated` → `normal_form_afp_textbook` → `britton_via_tower`)
//  rests on this layer.
//
//  Per `docs/cohen-faithfulness-primary-source.md` §6a/§7c the change is local:
//    * `apply_hom`/`apply_hom_symbol`/`identity_hom`/`compose_hom` are
//      relator-set-agnostic ⟹ port VERBATIM (only the carried presentation
//      type changes).
//    * `is_valid_homomorphism`'s relator condition goes from indexed
//      (`source.relators[i]`) to predicate (`forall|w| (source.relators)(w) ==>
//      hom(w) ≡ ε`).
//    * the relator-step preservation lemmas carry the relator WORD gated by
//      `(source.relators)(relator)` instead of by index — §6a's "trivial" port.
//
//  Kept SEPARATE from the verified finite `homomorphism` module (zero
//  regression; reversible — delete the file + the `pub mod pred_homomorphism`
//  line).  Mirrors `homomorphism.rs` structure-for-structure.
//  ============================================================

///  Data defining a group homomorphism via generator images, predicate base.
pub struct PredHomomorphismData {
    pub source: PredPresentation,
    pub target: PredPresentation,
    pub generator_images: Seq<Word>,
}

///  Image of a single symbol under the homomorphism.  (Verbatim port.)
pub open spec fn apply_hom_symbol_pred(h: PredHomomorphismData, s: Symbol) -> Word {
    match s {
        Symbol::Gen(i) => h.generator_images[i as int],
        Symbol::Inv(i) => inverse_word(h.generator_images[i as int]),
    }
}

///  Image of a word under the homomorphism.  (Verbatim port.)
pub open spec fn apply_hom_pred(h: PredHomomorphismData, w: Word) -> Word
    decreases w.len(),
{
    if w.len() == 0 {
        empty_word()
    } else {
        concat(apply_hom_symbol_pred(h, w.first()), apply_hom_pred(h, w.drop_first()))
    }
}

///  A homomorphism is valid if images.len() == num_generators, both
///  presentations are valid, generator images are word_valid, and each accepted
///  relator's image ≡ ε.  The ONLY change vs `is_valid_homomorphism` is the
///  last clause: predicate quantification over accepted relator words instead of
///  indexing the finite relator list (§6a/§7c).
pub open spec fn is_valid_pred_homomorphism(h: PredHomomorphismData) -> bool {
    h.generator_images.len() == h.source.num_generators
    && pred_presentation_valid(h.source)
    && pred_presentation_valid(h.target)
    && (forall|i: int| 0 <= i < h.generator_images.len() ==>
        word_valid(#[trigger] h.generator_images[i], h.target.num_generators))
    && (forall|w: Word| #![trigger (h.source.relators)(w)] (h.source.relators)(w) ==>
        equiv_in_pred_presentation(h.target, apply_hom_pred(h, w), empty_word()))
}

///  The identity homomorphism: Gen(i) → [Gen(i)].  (Verbatim port.)
pub open spec fn identity_hom_pred(p: PredPresentation) -> PredHomomorphismData {
    PredHomomorphismData {
        source: p,
        target: p,
        generator_images: Seq::new(p.num_generators, |i: int| {
            Seq::new(1, |_j: int| Symbol::Gen(i as nat))
        }),
    }
}

///  Composition of homomorphisms.  (Verbatim port.)
pub open spec fn compose_hom_pred(h1: PredHomomorphismData, h2: PredHomomorphismData) -> PredHomomorphismData {
    PredHomomorphismData {
        source: h1.source,
        target: h2.target,
        generator_images: Seq::new(h1.generator_images.len(), |i: int| {
            apply_hom_pred(h2, h1.generator_images[i])
        }),
    }
}

//  --- Helpers ---

///  apply_hom of a singleton word.
pub proof fn lemma_hom_pred_singleton(h: PredHomomorphismData, s: Symbol)
    ensures
        apply_hom_pred(h, Seq::new(1, |_i: int| s)) =~= apply_hom_symbol_pred(h, s),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.first() == s);
    let tail = w.drop_first();
    assert(tail.len() == 0);
    assert(apply_hom_pred(h, tail) =~= empty_word());
    assert(concat(apply_hom_symbol_pred(h, s), empty_word()) =~= apply_hom_symbol_pred(h, s));
}

///  Image of a single symbol is word_valid for target.
proof fn lemma_apply_hom_pred_symbol_word_valid(h: PredHomomorphismData, s: Symbol)
    requires
        is_valid_pred_homomorphism(h),
        symbol_valid(s, h.source.num_generators),
    ensures
        word_valid(apply_hom_symbol_pred(h, s), h.target.num_generators),
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
pub proof fn lemma_apply_hom_pred_word_valid(h: PredHomomorphismData, w: Word)
    requires
        is_valid_pred_homomorphism(h),
        word_valid(w, h.source.num_generators),
    ensures
        word_valid(apply_hom_pred(h, w), h.target.num_generators),
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
        lemma_apply_hom_pred_symbol_word_valid(h, s);
        lemma_apply_hom_pred_word_valid(h, rest);
        crate::word::lemma_concat_word_valid(
            apply_hom_symbol_pred(h, s), apply_hom_pred(h, rest), h.target.num_generators);
    }
}

///  concat(x, suffix) ≡ suffix when x ≡ ε.
pub proof fn lemma_pred_identity_prefix_equiv(p: PredPresentation, x: Word, suffix: Word)
    requires
        equiv_in_pred_presentation(p, x, empty_word()),
    ensures
        equiv_in_pred_presentation(p, concat(x, suffix), suffix),
{
    lemma_pred_equiv_concat_left(p, x, empty_word(), suffix);
    assert(concat(empty_word(), suffix) =~= suffix);
    lemma_pred_equiv_refl(p, suffix);
    lemma_pred_equiv_transitive(p, concat(x, suffix), concat(empty_word(), suffix), suffix);
}

///  Homomorphism respects concatenation.
pub proof fn lemma_hom_pred_respects_concat(h: PredHomomorphismData, w1: Word, w2: Word)
    ensures
        apply_hom_pred(h, concat(w1, w2)) =~= concat(apply_hom_pred(h, w1), apply_hom_pred(h, w2)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(apply_hom_pred(h, w1) =~= empty_word());
    } else {
        let s = w1.first();
        let rest = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest, w2));
        lemma_hom_pred_respects_concat(h, rest, w2);
        lemma_concat_assoc(apply_hom_symbol_pred(h, s), apply_hom_pred(h, rest), apply_hom_pred(h, w2));
    }
}

///  Homomorphism respects word inverse.
pub proof fn lemma_hom_pred_respects_inverse(h: PredHomomorphismData, w: Word)
    ensures
        apply_hom_pred(h, inverse_word(w)) =~= inverse_word(apply_hom_pred(h, w)),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();

        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        assert(inverse_word(w) =~= concat(inverse_word(rest), inv_s_word));
        lemma_hom_pred_respects_concat(h, inverse_word(rest), inv_s_word);
        lemma_hom_pred_respects_inverse(h, rest);
        lemma_hom_pred_singleton(h, inverse_symbol(s));

        match s {
            Symbol::Gen(_idx) => {},
            Symbol::Inv(idx) => {
                crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
            },
        }

        lemma_inverse_concat(apply_hom_symbol_pred(h, s), apply_hom_pred(h, rest));
    }
}

///  hom(r) ≡ ε for an accepted relator word (and its inverse).
///  Predicate-base analog of `lemma_inverted_relator_image_is_identity`: the
///  relator is the carried word `r` gated by `(source.relators)(r)`.
proof fn lemma_pred_inverted_relator_image_is_identity(h: PredHomomorphismData, r: Word)
    requires
        is_valid_pred_homomorphism(h),
        (h.source.relators)(r),
    ensures
        equiv_in_pred_presentation(
            h.target,
            apply_hom_pred(h, inverse_word(r)),
            empty_word(),
        ),
{
    reveal(pred_presentation_valid);
    let hom_orig = apply_hom_pred(h, r);

    //  word_valid facts for lemma_pred_equiv_symmetric calls
    assert(word_valid(r, h.source.num_generators));
    lemma_apply_hom_pred_word_valid(h, r);
    let n = h.target.num_generators;
    crate::word::lemma_inverse_word_valid(hom_orig, n);
    crate::word::lemma_concat_word_valid(inverse_word(hom_orig), hom_orig, n);

    lemma_hom_pred_respects_inverse(h, r);

    //  hom_orig ≡ ε from is_valid (forall|w| (source.relators)(w) ==> hom(w) ≡ ε)
    assert((h.source.relators)(r));
    assert(equiv_in_pred_presentation(h.target, hom_orig, empty_word()));

    lemma_pred_word_inverse_left(h.target, hom_orig);
    lemma_pred_equiv_symmetric(h.target, hom_orig, empty_word());
    lemma_pred_equiv_concat_right(h.target, inverse_word(hom_orig), hom_orig, empty_word());
    assert(concat(inverse_word(hom_orig), empty_word()) =~= inverse_word(hom_orig));

    crate::word::lemma_concat_word_valid(inverse_word(hom_orig), empty_word(), n);
    lemma_pred_equiv_symmetric(h.target,
        concat(inverse_word(hom_orig), hom_orig),
        concat(inverse_word(hom_orig), empty_word()),
    );
    lemma_pred_equiv_transitive(h.target,
        inverse_word(hom_orig),
        concat(inverse_word(hom_orig), hom_orig),
        empty_word(),
    );

    assert(apply_hom_pred(h, inverse_word(r)) =~= inverse_word(hom_orig));
}

///  hom_r ≡ ε for the relator word, possibly inverted.
proof fn lemma_pred_relator_image_is_identity(h: PredHomomorphismData, r: Word, inverted: bool)
    requires
        is_valid_pred_homomorphism(h),
        (h.source.relators)(r),
    ensures
        equiv_in_pred_presentation(
            h.target,
            apply_hom_pred(h, get_relator_pred(r, inverted)),
            empty_word(),
        ),
{
    if inverted {
        lemma_pred_inverted_relator_image_is_identity(h, r);
    } else {
        assert(get_relator_pred(r, inverted) == r);
        assert((h.source.relators)(r));
        assert(equiv_in_pred_presentation(h.target, apply_hom_pred(h, r), empty_word()));
    }
}

//  --- Main Lemmas ---

///  Homomorphism of empty word is empty.
pub proof fn lemma_hom_pred_empty(h: PredHomomorphismData)
    ensures
        apply_hom_pred(h, empty_word()) =~= empty_word(),
{
}

///  Homomorphism preserves a single derivation step.
pub proof fn lemma_hom_pred_preserves_single_step(
    h: PredHomomorphismData,
    w: Word, step: PredDerivationStep, w_prime: Word,
)
    requires
        is_valid_pred_homomorphism(h),
        apply_step_pred(h.source, w, step) == Some(w_prime),
    ensures
        equiv_in_pred_presentation(h.target, apply_hom_pred(h, w), apply_hom_pred(h, w_prime)),
{
    match step {
        PredDerivationStep::FreeReduce { position } => {
            lemma_hom_pred_preserves_free_reduce(h, w, position);
        },
        PredDerivationStep::FreeExpand { position, symbol } => {
            lemma_hom_pred_preserves_free_expand(h, w, position, symbol);
        },
        PredDerivationStep::RelatorInsert { position, relator, inverted } => {
            lemma_hom_pred_preserves_relator_insert(h, w, position, relator, inverted);
        },
        PredDerivationStep::RelatorDelete { position, relator, inverted } => {
            lemma_hom_pred_preserves_relator_delete(h, w, position, relator, inverted);
        },
    }
}

///  Helper: hom preserves FreeReduce step.
proof fn lemma_hom_pred_preserves_free_reduce(
    h: PredHomomorphismData, w: Word, position: int,
)
    requires
        is_valid_pred_homomorphism(h),
        has_cancellation_at(w, position),
    ensures
        equiv_in_pred_presentation(h.target, apply_hom_pred(h, w), apply_hom_pred(h, reduce_at(w, position))),
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

    lemma_hom_pred_respects_concat(h, prefix + pair, suffix);
    lemma_hom_pred_respects_concat(h, prefix, pair);
    lemma_hom_pred_respects_concat(h, s1_word, s2_word);
    lemma_hom_pred_respects_concat(h, prefix, suffix);

    lemma_hom_pred_singleton(h, s1);
    lemma_hom_pred_singleton(h, s2);

    let img_s1 = apply_hom_symbol_pred(h, s1);
    let img_s2 = apply_hom_symbol_pred(h, s2);

    //  img_s2 = inverse_word(img_s1)
    match s1 {
        Symbol::Gen(_idx) => {},
        Symbol::Inv(idx) => {
            crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    lemma_pred_word_inverse_right(h.target, img_s1);

    let hom_prefix = apply_hom_pred(h, prefix);
    let hom_suffix = apply_hom_pred(h, suffix);
    let pair_img = concat(img_s1, img_s2);

    lemma_concat_assoc(hom_prefix, pair_img, hom_suffix);

    lemma_pred_identity_prefix_equiv(h.target, pair_img, hom_suffix);
    lemma_pred_equiv_concat_right(h.target, hom_prefix, concat(pair_img, hom_suffix), hom_suffix);
}

///  Helper: hom preserves FreeExpand step.
proof fn lemma_hom_pred_preserves_free_expand(
    h: PredHomomorphismData, w: Word, position: int, symbol: Symbol,
)
    requires
        is_valid_pred_homomorphism(h),
        0 <= position <= w.len(),
        symbol_valid(symbol, h.source.num_generators),
    ensures
        equiv_in_pred_presentation(
            h.target,
            apply_hom_pred(h, w),
            apply_hom_pred(h, apply_step_pred(h.source, w, PredDerivationStep::FreeExpand { position, symbol }).unwrap()),
        ),
{
    let s_word = Seq::new(1, |_i: int| symbol);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(symbol));
    let pair = s_word + inv_s_word;
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = (prefix + pair) + suffix;
    assert(w =~= prefix + suffix);

    lemma_hom_pred_respects_concat(h, prefix, suffix);
    lemma_hom_pred_respects_concat(h, prefix + pair, suffix);
    lemma_hom_pred_respects_concat(h, prefix, pair);
    lemma_hom_pred_respects_concat(h, s_word, inv_s_word);

    lemma_hom_pred_singleton(h, symbol);
    lemma_hom_pred_singleton(h, inverse_symbol(symbol));

    let img_s = apply_hom_symbol_pred(h, symbol);
    let img_inv_s = apply_hom_symbol_pred(h, inverse_symbol(symbol));

    match symbol {
        Symbol::Gen(_idx) => {},
        Symbol::Inv(idx) => {
            crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    lemma_pred_word_inverse_right(h.target, img_s);

    let hom_prefix = apply_hom_pred(h, prefix);
    let hom_suffix = apply_hom_pred(h, suffix);
    let pair_img = concat(img_s, img_inv_s);

    lemma_concat_assoc(hom_prefix, pair_img, hom_suffix);

    //  pair_img ≡ ε; symmetric needs word_valid(pair_img) + pred_presentation_valid(target)
    lemma_apply_hom_pred_symbol_word_valid(h, symbol);
    crate::symbol::lemma_inverse_preserves_valid(symbol, h.source.num_generators);
    lemma_apply_hom_pred_symbol_word_valid(h, inverse_symbol(symbol));
    crate::word::lemma_concat_word_valid(img_s, img_inv_s, h.target.num_generators);
    lemma_pred_equiv_symmetric(h.target, pair_img, empty_word());

    lemma_pred_equiv_concat_left(h.target, empty_word(), pair_img, hom_suffix);
    lemma_pred_equiv_concat_right(h.target, hom_prefix,
        concat(empty_word(), hom_suffix), concat(pair_img, hom_suffix));
}

///  Helper: hom preserves RelatorInsert step.
proof fn lemma_hom_pred_preserves_relator_insert(
    h: PredHomomorphismData, w: Word,
    position: int, relator: Word, inverted: bool,
)
    requires
        is_valid_pred_homomorphism(h),
        0 <= position <= w.len(),
        (h.source.relators)(relator),
    ensures
        equiv_in_pred_presentation(
            h.target,
            apply_hom_pred(h, w),
            apply_hom_pred(h, apply_step_pred(h.source, w,
                PredDerivationStep::RelatorInsert { position, relator, inverted }).unwrap()),
        ),
{
    reveal(pred_presentation_valid);
    let r = get_relator_pred(relator, inverted);
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = (prefix + r) + suffix;
    assert(w =~= prefix + suffix);

    lemma_hom_pred_respects_concat(h, prefix, suffix);
    lemma_hom_pred_respects_concat(h, prefix + r, suffix);
    lemma_hom_pred_respects_concat(h, prefix, r);

    let hom_prefix = apply_hom_pred(h, prefix);
    let hom_suffix = apply_hom_pred(h, suffix);
    let hom_r = apply_hom_pred(h, r);

    lemma_pred_relator_image_is_identity(h, relator, inverted);

    lemma_concat_assoc(hom_prefix, hom_r, hom_suffix);

    //  hom_r ≡ ε → symmetric: ε ≡ hom_r; need word_valid(hom_r) + pred_presentation_valid(target)
    assert(word_valid(relator, h.source.num_generators));
    if inverted {
        crate::word::lemma_inverse_word_valid(relator, h.source.num_generators);
    }
    lemma_apply_hom_pred_word_valid(h, r);
    lemma_pred_equiv_symmetric(h.target, hom_r, empty_word());

    lemma_pred_equiv_concat_left(h.target, empty_word(), hom_r, hom_suffix);
    lemma_pred_equiv_concat_right(h.target, hom_prefix,
        concat(empty_word(), hom_suffix), concat(hom_r, hom_suffix));
}

///  Helper: hom preserves RelatorDelete step.
proof fn lemma_hom_pred_preserves_relator_delete(
    h: PredHomomorphismData, w: Word,
    position: int, relator: Word, inverted: bool,
)
    requires
        is_valid_pred_homomorphism(h),
        (h.source.relators)(relator),
        apply_step_pred(h.source, w, PredDerivationStep::RelatorDelete { position, relator, inverted }) is Some,
    ensures
        equiv_in_pred_presentation(
            h.target,
            apply_hom_pred(h, w),
            apply_hom_pred(h, apply_step_pred(h.source, w,
                PredDerivationStep::RelatorDelete { position, relator, inverted }).unwrap()),
        ),
{
    let r = get_relator_pred(relator, inverted);
    let rlen = r.len();
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position + rlen as int, w.len() as int);
    let w_prime = prefix + suffix;
    assert(w.subrange(position, position + rlen as int) == r);
    assert(w =~= (prefix + r) + suffix);

    lemma_hom_pred_respects_concat(h, prefix + r, suffix);
    lemma_hom_pred_respects_concat(h, prefix, r);
    lemma_hom_pred_respects_concat(h, prefix, suffix);

    let hom_prefix = apply_hom_pred(h, prefix);
    let hom_suffix = apply_hom_pred(h, suffix);
    let hom_r = apply_hom_pred(h, r);

    lemma_pred_relator_image_is_identity(h, relator, inverted);

    lemma_concat_assoc(hom_prefix, hom_r, hom_suffix);

    lemma_pred_identity_prefix_equiv(h.target, hom_r, hom_suffix);
    lemma_pred_equiv_concat_right(h.target, hom_prefix, concat(hom_r, hom_suffix), hom_suffix);
}

///  Homomorphism preserves a derivation (sequence of steps).
pub proof fn lemma_hom_pred_preserves_derivation(
    h: PredHomomorphismData,
    steps: Seq<PredDerivationStep>, w: Word, w_prime: Word,
)
    requires
        is_valid_pred_homomorphism(h),
        pred_derivation_produces(h.source, steps, w) == Some(w_prime),
    ensures
        equiv_in_pred_presentation(h.target, apply_hom_pred(h, w), apply_hom_pred(h, w_prime)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        lemma_pred_equiv_refl(h.target, apply_hom_pred(h, w));
    } else {
        let step = steps.first();
        let rest = steps.drop_first();
        let w_mid = apply_step_pred(h.source, w, step).unwrap();

        lemma_hom_pred_preserves_single_step(h, w, step, w_mid);
        lemma_hom_pred_preserves_derivation(h, rest, w_mid, w_prime);
        lemma_pred_equiv_transitive(h.target,
            apply_hom_pred(h, w), apply_hom_pred(h, w_mid), apply_hom_pred(h, w_prime));
    }
}

///  **Main theorem**: Homomorphisms preserve equivalence.
pub proof fn lemma_hom_pred_preserves_equiv(
    h: PredHomomorphismData, w1: Word, w2: Word,
)
    requires
        is_valid_pred_homomorphism(h),
        equiv_in_pred_presentation(h.source, w1, w2),
    ensures
        equiv_in_pred_presentation(h.target, apply_hom_pred(h, w1), apply_hom_pred(h, w2)),
{
    let d = choose|d: PredDerivation| pred_derivation_valid(h.source, d, w1, w2);
    lemma_hom_pred_preserves_derivation(h, d.steps, w1, w2);
}

///  The identity homomorphism is valid (for valid presentations).
pub proof fn lemma_identity_hom_pred_valid(p: PredPresentation)
    requires
        pred_presentation_valid(p),
    ensures
        is_valid_pred_homomorphism(identity_hom_pred(p)),
{
    reveal(pred_presentation_valid);
    let h = identity_hom_pred(p);
    assert(h.generator_images.len() == p.num_generators);

    assert forall|w: Word| #![trigger (h.source.relators)(w)] (h.source.relators)(w) implies
        equiv_in_pred_presentation(h.target, apply_hom_pred(h, w), empty_word())
    by {
        assert((p.relators)(w));
        assert(word_valid(w, p.num_generators));
        lemma_identity_hom_pred_apply(h, w, p.num_generators);
        assert(apply_hom_pred(h, w) =~= w);
        lemma_pred_relator_is_identity(p, w);
    }
}

///  Helper: identity homomorphism preserves valid words.
proof fn lemma_identity_hom_pred_apply(h: PredHomomorphismData, w: Word, n: nat)
    requires
        h.generator_images.len() == n,
        forall|i: int| 0 <= i < n ==>
            #[trigger] h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen(i as nat)),
        word_valid(w, n),
    ensures
        apply_hom_pred(h, w) =~= w,
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
        lemma_identity_hom_pred_apply(h, rest, n);

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
