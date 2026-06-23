use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::*;
use crate::pred_free_product::*;
use crate::pred_homomorphism::*;
//  Word-level shift machinery is relator-agnostic ⟹ REUSED verbatim from finite
//  free_product (pure Word ops, take no Presentation).
use crate::free_product::{shift_symbol, shift_word};

verus! {

//  ============================================================
//  FORK-A brick FA-6 — predicate-base free-product injectivity (2026-06-23).
//
//  Predicate-base analog of `normal_form_free_product.rs`, over
//  `PredPresentation`.  Free-product injectivity via a RETRACTION homomorphism:
//
//     w a G₁-word, w ≡ ε in free_product_pred(p1,p2)  ⟹  w ≡ ε in p1.
//
//  Proof (verbatim from the finite version): the left retraction ρ: FP → P₁
//  (collapse G₂-generators to ε, fix G₁-generators) is a valid homomorphism;
//  ρ preserves equivalence (FA-5 `lemma_hom_pred_preserves_equiv`); ρ is the
//  identity on G₁-words; so ρ(w)=w ≡ ρ(ε)=ε in P₁.
//
//  Per `docs/cohen-faithfulness-primary-source.md` §7c the proof is a verbatim
//  type-swap EXCEPT the homomorphism-validity relator clause: it goes from
//  indexed (`fp.relators[i]`, split at `p1.relators.len()`) to the predicate
//  disjunction `(p1.relators)(w) || shifted_pred(p2.relators, n1, w)` (the
//  predicate `shift` from FA-3).  Kept separate (reversible, zero regression).
//  ============================================================

//  ============================================================
//  Left retraction: free_product_pred(p1, p2) → p1
//  ============================================================

///  The left retraction homomorphism.
///  Gen(i) for i < n₁ → [Gen(i)]; Gen(j) for j ≥ n₁ → ε.
pub open spec fn fp_left_retraction_pred(p1: PredPresentation, p2: PredPresentation) -> PredHomomorphismData {
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;
    PredHomomorphismData {
        source: free_product_pred(p1, p2),
        target: p1,
        generator_images: Seq::new(n1 + n2, |i: int|
            if i < n1 {
                Seq::new(1, |_j: int| Symbol::Gen(i as nat))
            } else {
                empty_word()
            }
        ),
    }
}

//  ============================================================
//  Helper: apply_hom collapses a word whose symbols all map to ε
//  ============================================================

///  If every symbol of w maps to ε under h, then apply_hom_pred(h, w) =~= ε.
pub proof fn lemma_hom_pred_collapses_word(h: PredHomomorphismData, w: Word)
    requires
        forall|k: int| 0 <= k < w.len() ==>
            apply_hom_symbol_pred(h, #[trigger] w[k]) =~= empty_word(),
    ensures
        apply_hom_pred(h, w) =~= empty_word(),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(w[0] == s);
        assert(apply_hom_symbol_pred(h, s) =~= empty_word());
        assert forall|k: int| 0 <= k < rest.len() implies
            apply_hom_symbol_pred(h, #[trigger] rest[k]) =~= empty_word()
        by {
            assert(rest[k] == w[k + 1]);
        }
        lemma_hom_pred_collapses_word(h, rest);
        assert(apply_hom_pred(h, rest) =~= empty_word());
        assert(apply_hom_pred(h, w) =~= concat(empty_word(), empty_word()));
        assert(concat(empty_word(), empty_word()) =~= empty_word());
    }
}

//  ============================================================
//  Helper: apply_hom is the identity on words with identity images
//  ============================================================

///  If images[i] =~= [Gen(i)] for all i < n, and word_valid(w, n),
///  then apply_hom_pred(h, w) =~= w.
pub proof fn lemma_hom_pred_identity_on_word(h: PredHomomorphismData, w: Word, n: nat)
    requires
        forall|i: int| 0 <= i < n ==>
            #[trigger] h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen(i as nat)),
        h.generator_images.len() >= n,
        word_valid(w, n),
    ensures
        apply_hom_pred(h, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_hom_pred(h, w) =~= empty_word());
        assert(w =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, n));

        assert(word_valid(rest, n)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], n)
            by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_hom_pred_identity_on_word(h, rest, n);
        assert(apply_hom_pred(h, rest) =~= rest);

        let idx = generator_index(s);
        assert(idx < n);
        match s {
            Symbol::Gen(i) => {
                assert(h.generator_images[i as int]
                    =~= Seq::new(1, |_j: int| Symbol::Gen(i)));
                assert(apply_hom_symbol_pred(h, s) =~= h.generator_images[i as int]);
                assert(apply_hom_symbol_pred(h, s)
                    =~= Seq::new(1, |_j: int| Symbol::Gen(i)));
            },
            Symbol::Inv(i) => {
                let img = Seq::new(1, |_j: int| Symbol::Gen(i));
                assert(h.generator_images[i as int] =~= img);
                assert(img.drop_first() =~= Seq::<Symbol>::empty());
                assert(inverse_word(img.drop_first()) =~= empty_word());
                assert(inverse_symbol(img.first()) == Symbol::Inv(i));
                let inv_img = inverse_word(img);
                assert(inv_img =~= empty_word() + Seq::new(1, |_j: int| Symbol::Inv(i)));
                assert(inv_img =~= Seq::new(1, |_j: int| Symbol::Inv(i)));
                assert(apply_hom_symbol_pred(h, s) =~= inv_img);
            },
        }

        assert(apply_hom_symbol_pred(h, s) =~= Seq::new(1, |_j: int| s));
        assert(apply_hom_pred(h, w) =~= concat(Seq::new(1, |_j: int| s), rest));
        assert(concat(Seq::new(1, |_j: int| s), rest) =~= w) by {
            let lhs = concat(Seq::new(1, |_j: int| s), rest);
            assert(lhs.len() == 1 + rest.len());
            assert(lhs.len() == w.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == w[k] by {
                if k == 0 {
                    assert(lhs[0] == s);
                    assert(w[0] == s);
                } else {
                    assert(lhs[k] == rest[k - 1]);
                    assert(rest[k - 1] == w[k]);
                }
            }
        }
    }
}

//  ============================================================
//  free_product_pred is a valid predicate presentation
//  ============================================================

///  The predicate free product is valid (every accepted relator word is
///  word_valid for n1+n2).  Predicate analog of the inline `presentation_valid`
///  block in `lemma_fp_left_retraction_valid`: case-split the disjunction
///  `(p1.relators)(w) || shifted_pred(p2.relators, n1, w)`.
pub proof fn lemma_free_product_pred_valid(p1: PredPresentation, p2: PredPresentation)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
    ensures
        pred_presentation_valid(free_product_pred(p1, p2)),
{
    reveal(pred_presentation_valid);
    let fp = free_product_pred(p1, p2);
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;
    assert(fp.num_generators == n1 + n2);

    assert forall|w: Word| #![trigger (fp.relators)(w)] (fp.relators)(w) implies
        word_valid(w, (n1 + n2) as nat)
    by {
        assert(free_product_pred_relators(p1, p2, w));
        if (p1.relators)(w) {
            //  p1-relator: word_valid(w, n1) → monotone to n1+n2
            assert(word_valid(w, n1));
            assert forall|m: int| 0 <= m < w.len()
                implies symbol_valid(w[m], (n1 + n2) as nat)
            by {
                assert(symbol_valid(w[m], n1));
            }
        } else {
            //  shifted p2-relator: w = shift_word(w0, n1), each symbol index ∈ [n1, n1+n2)
            assert(shifted_pred(p2.relators, n1, w));
            let w0 = choose|w0: Word| (p2.relators)(w0) && w == shift_word(w0, n1);
            assert((p2.relators)(w0));
            assert(word_valid(w0, n2));
            assert(w == shift_word(w0, n1));
            assert(w.len() == w0.len());
            assert forall|m: int| 0 <= m < w.len()
                implies symbol_valid(w[m], (n1 + n2) as nat)
            by {
                assert(w[m] == shift_symbol(w0[m], n1));
                assert(symbol_valid(w0[m], n2));
            }
        }
    }
}

//  ============================================================
//  Left retraction is a valid homomorphism
//  ============================================================

///  The left retraction is a valid homomorphism.
pub proof fn lemma_fp_left_retraction_pred_valid(p1: PredPresentation, p2: PredPresentation)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
    ensures
        is_valid_pred_homomorphism(fp_left_retraction_pred(p1, p2)),
{
    reveal(pred_presentation_valid);
    let rho = fp_left_retraction_pred(p1, p2);
    let fp = free_product_pred(p1, p2);
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;

    assert(rho.generator_images.len() == n1 + n2);
    assert(rho.source.num_generators == n1 + n2);

    //  source = free_product_pred(p1, p2) is valid
    lemma_free_product_pred_valid(p1, p2);

    //  Each image is word_valid for p1
    assert forall|i: int| 0 <= i < rho.generator_images.len()
        implies word_valid(#[trigger] rho.generator_images[i], n1)
    by {
        if i < n1 as int {
            assert(rho.generator_images[i] =~=
                Seq::new(1, |_j: int| Symbol::Gen(i as nat)));
            assert(symbol_valid(Symbol::Gen(i as nat), n1));
        } else {
            //  empty_word(), trivially valid
        }
    }

    //  Each accepted source relator maps to ≡ ε in p1
    assert forall|w: Word| #![trigger (rho.source.relators)(w)] (rho.source.relators)(w) implies
        equiv_in_pred_presentation(p1, apply_hom_pred(rho, w), empty_word())
    by {
        assert(free_product_pred_relators(p1, p2, w));
        if (p1.relators)(w) {
            //  G₁-relator: rho is the identity on it
            assert(word_valid(w, n1));
            lemma_hom_pred_identity_on_word(rho, w, n1);
            assert(apply_hom_pred(rho, w) =~= w);
            lemma_pred_relator_is_identity(p1, w);
        } else {
            //  shifted G₂-relator: all symbols index ≥ n1, collapse to ε
            assert(shifted_pred(p2.relators, n1, w));
            let w0 = choose|w0: Word| (p2.relators)(w0) && w == shift_word(w0, n1);
            assert((p2.relators)(w0));
            assert(word_valid(w0, n2));
            assert(w == shift_word(w0, n1));
            assert(w.len() == w0.len());
            assert forall|k: int| 0 <= k < w.len()
                implies apply_hom_symbol_pred(rho, #[trigger] w[k]) =~= empty_word()
            by {
                assert(w[k] == shift_symbol(w0[k], n1));
                assert(symbol_valid(w0[k], n2));
                let orig = w0[k];
                match orig {
                    Symbol::Gen(gi) => {
                        assert(w[k] == Symbol::Gen(gi + n1));
                        assert(generator_index(w[k]) == gi + n1);
                        assert(gi + n1 >= n1);
                        assert(gi + n1 < n1 + n2);
                        assert(rho.generator_images[(gi + n1) as int] =~= empty_word());
                    },
                    Symbol::Inv(gi) => {
                        assert(w[k] == Symbol::Inv(gi + n1));
                        assert(generator_index(w[k]) == gi + n1);
                        assert(gi + n1 >= n1);
                        assert(gi + n1 < n1 + n2);
                        assert(rho.generator_images[(gi + n1) as int] =~= empty_word());
                        assert(inverse_word(empty_word()) =~= empty_word());
                    },
                }
            }
            lemma_hom_pred_collapses_word(rho, w);
            assert(apply_hom_pred(rho, w) =~= empty_word());
            lemma_pred_equiv_refl(p1, empty_word());
        }
    }
}

//  ============================================================
//  Left retraction is the identity on G₁-words
//  ============================================================

///  For G₁-words: apply_hom_pred(ρ, w) =~= w.
pub proof fn lemma_fp_left_retraction_pred_identity(
    p1: PredPresentation, p2: PredPresentation, w: Word,
)
    requires
        word_valid(w, p1.num_generators),
    ensures
        apply_hom_pred(fp_left_retraction_pred(p1, p2), w) =~= w,
{
    let rho = fp_left_retraction_pred(p1, p2);
    let n1 = p1.num_generators;
    lemma_hom_pred_identity_on_word(rho, w, n1);
}

//  ============================================================
//  Main theorem: free product injectivity (left)
//  ============================================================

///  If w is a G₁-word and w ≡ ε in free_product_pred(p1,p2), then w ≡ ε in p1.
pub proof fn lemma_free_product_pred_injective_left(
    p1: PredPresentation, p2: PredPresentation, w: Word,
)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
        word_valid(w, p1.num_generators),
        equiv_in_pred_presentation(free_product_pred(p1, p2), w, empty_word()),
    ensures
        equiv_in_pred_presentation(p1, w, empty_word()),
{
    let rho = fp_left_retraction_pred(p1, p2);
    lemma_fp_left_retraction_pred_valid(p1, p2);
    lemma_hom_pred_preserves_equiv(rho, w, empty_word());
    lemma_fp_left_retraction_pred_identity(p1, p2, w);
    lemma_hom_pred_empty(rho);
}

//  ============================================================
//  Right retraction: free_product_pred(p1, p2) → p2
//  ============================================================

///  The right retraction homomorphism.
///  Gen(i) for i < n₁ → ε; Gen(n₁+j) for j < n₂ → [Gen(j)].
pub open spec fn fp_right_retraction_pred(p1: PredPresentation, p2: PredPresentation) -> PredHomomorphismData {
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;
    PredHomomorphismData {
        source: free_product_pred(p1, p2),
        target: p2,
        generator_images: Seq::new(n1 + n2, |i: int|
            if i < n1 {
                empty_word()
            } else {
                Seq::new(1, |_j: int| Symbol::Gen((i - n1) as nat))
            }
        ),
    }
}

///  The right retraction is a valid homomorphism.
pub proof fn lemma_fp_right_retraction_pred_valid(p1: PredPresentation, p2: PredPresentation)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
    ensures
        is_valid_pred_homomorphism(fp_right_retraction_pred(p1, p2)),
{
    reveal(pred_presentation_valid);
    let rho = fp_right_retraction_pred(p1, p2);
    let fp = free_product_pred(p1, p2);
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;

    assert(rho.generator_images.len() == n1 + n2);

    //  source valid
    lemma_free_product_pred_valid(p1, p2);

    //  Each image is word_valid for p2
    assert forall|i: int| 0 <= i < rho.generator_images.len()
        implies word_valid(#[trigger] rho.generator_images[i], n2)
    by {
        if i < n1 as int {
            //  empty_word(), trivially valid
        } else {
            let gi = (i - n1) as nat;
            assert(rho.generator_images[i] =~=
                Seq::new(1, |_j: int| Symbol::Gen(gi)));
            assert(gi < n2);
            assert(symbol_valid(Symbol::Gen(gi), n2));
        }
    }

    //  Each accepted source relator maps to ≡ ε in p2
    assert forall|w: Word| #![trigger (rho.source.relators)(w)] (rho.source.relators)(w) implies
        equiv_in_pred_presentation(p2, apply_hom_pred(rho, w), empty_word())
    by {
        assert(free_product_pred_relators(p1, p2, w));
        if (p1.relators)(w) {
            //  G₁-relator: all symbols index < n1, all map to ε
            assert(word_valid(w, n1));
            assert forall|k: int| 0 <= k < w.len()
                implies apply_hom_symbol_pred(rho, #[trigger] w[k]) =~= empty_word()
            by {
                assert(symbol_valid(w[k], n1));
                assert(generator_index(w[k]) < n1);
                match w[k] {
                    Symbol::Gen(gi) => {
                        assert(rho.generator_images[gi as int] =~= empty_word());
                    },
                    Symbol::Inv(gi) => {
                        assert(rho.generator_images[gi as int] =~= empty_word());
                        assert(inverse_word(empty_word()) =~= empty_word());
                    },
                }
            }
            lemma_hom_pred_collapses_word(rho, w);
            lemma_pred_equiv_refl(p2, empty_word());
        } else {
            //  shifted G₂-relator: rho unshifts shift(w0) back to w0
            assert(shifted_pred(p2.relators, n1, w));
            let w0 = choose|w0: Word| (p2.relators)(w0) && w == shift_word(w0, n1);
            assert((p2.relators)(w0));
            assert(word_valid(w0, n2));
            assert(w == shift_word(w0, n1));

            lemma_right_retraction_pred_unshifts(p1, p2, w0);
            assert(apply_hom_pred(rho, w) =~= w0);

            lemma_pred_relator_is_identity(p2, w0);
            lemma_pred_equiv_refl(p2, apply_hom_pred(rho, w));
        }
    }
}

///  Helper: the right retraction unshifts a shifted G₂-word back to the original.
///  apply_hom_pred(right_rho, shift_word(w, n1)) =~= w for G₂-words.
proof fn lemma_right_retraction_pred_unshifts(
    p1: PredPresentation, p2: PredPresentation, w: Word,
)
    requires
        word_valid(w, p2.num_generators),
    ensures
        apply_hom_pred(fp_right_retraction_pred(p1, p2), shift_word(w, p1.num_generators)) =~= w,
    decreases w.len(),
{
    let rho = fp_right_retraction_pred(p1, p2);
    let n1 = p1.num_generators;
    let sw = shift_word(w, n1);

    if w.len() == 0 {
        assert(sw =~= empty_word());
        assert(apply_hom_pred(rho, sw) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let ss = shift_symbol(s, n1);
        let srest = shift_word(rest, n1);

        assert(sw.first() == ss);
        assert(sw.drop_first() =~= srest);

        assert(word_valid(rest, p2.num_generators)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], p2.num_generators)
            by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_right_retraction_pred_unshifts(p1, p2, rest);
        assert(apply_hom_pred(rho, srest) =~= rest);

        assert(symbol_valid(s, p2.num_generators));
        match s {
            Symbol::Gen(gi) => {
                assert(ss == Symbol::Gen(gi + n1));
                assert((gi + n1) >= n1);
                assert(rho.generator_images[(gi + n1) as int]
                    =~= Seq::new(1, |_j: int| Symbol::Gen(gi)));
                assert(apply_hom_symbol_pred(rho, ss)
                    =~= Seq::new(1, |_j: int| Symbol::Gen(gi)));
                assert(Seq::new(1, |_j: int| Symbol::Gen(gi))
                    =~= Seq::new(1, |_j: int| s));
            },
            Symbol::Inv(gi) => {
                assert(ss == Symbol::Inv(gi + n1));
                assert((gi + n1) >= n1);
                let img = Seq::new(1, |_j: int| Symbol::Gen(gi));
                assert(rho.generator_images[(gi + n1) as int] =~= img);
                assert(img.drop_first() =~= Seq::<Symbol>::empty());
                assert(inverse_word(img.drop_first()) =~= empty_word());
                assert(inverse_symbol(img.first()) == Symbol::Inv(gi));
                let inv_img = inverse_word(img);
                assert(inv_img =~= empty_word() + Seq::new(1, |_j: int| Symbol::Inv(gi)));
                assert(inv_img =~= Seq::new(1, |_j: int| Symbol::Inv(gi)));
                assert(apply_hom_symbol_pred(rho, ss) =~= inv_img);
                assert(Seq::new(1, |_j: int| Symbol::Inv(gi))
                    =~= Seq::new(1, |_j: int| s));
            },
        }

        assert(apply_hom_symbol_pred(rho, ss) =~= Seq::new(1, |_j: int| s));
        assert(apply_hom_pred(rho, sw) =~= concat(Seq::new(1, |_j: int| s), rest));
        assert(concat(Seq::new(1, |_j: int| s), rest) =~= w) by {
            let lhs = concat(Seq::new(1, |_j: int| s), rest);
            assert(lhs.len() == w.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == w[k] by {
                if k == 0 {
                } else {
                    assert(lhs[k] == rest[k - 1]);
                    assert(rest[k - 1] == w[k]);
                }
            }
        }
    }
}

///  For shifted G₂-words: apply_hom_pred(right_rho, shift_word(w, n1)) =~= w.
pub proof fn lemma_fp_right_retraction_pred_identity(
    p1: PredPresentation, p2: PredPresentation, w: Word,
)
    requires
        word_valid(w, p2.num_generators),
    ensures
        apply_hom_pred(fp_right_retraction_pred(p1, p2), shift_word(w, p1.num_generators)) =~= w,
{
    lemma_right_retraction_pred_unshifts(p1, p2, w);
}

//  ============================================================
//  Main theorem: free product injectivity (right)
//  ============================================================

///  If w is a G₂-word and shift(w) ≡ ε in free_product_pred(p1,p2), then w ≡ ε in p2.
pub proof fn lemma_free_product_pred_injective_right(
    p1: PredPresentation, p2: PredPresentation, w: Word,
)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
        word_valid(w, p2.num_generators),
        equiv_in_pred_presentation(
            free_product_pred(p1, p2),
            shift_word(w, p1.num_generators),
            empty_word(),
        ),
    ensures
        equiv_in_pred_presentation(p2, w, empty_word()),
{
    let rho = fp_right_retraction_pred(p1, p2);
    lemma_fp_right_retraction_pred_valid(p1, p2);
    lemma_hom_pred_preserves_equiv(rho, shift_word(w, p1.num_generators), empty_word());
    lemma_fp_right_retraction_pred_identity(p1, p2, w);
    lemma_hom_pred_empty(rho);
}

//  ============================================================
//  General form: two G₁-words equivalent in FP are equivalent in P₁
//  ============================================================

///  If w₁, w₂ are G₁-words and w₁ ≡ w₂ in FP, then w₁ ≡ w₂ in P₁.
pub proof fn lemma_free_product_pred_reflects_left(
    p1: PredPresentation, p2: PredPresentation, w1: Word, w2: Word,
)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
        word_valid(w1, p1.num_generators),
        word_valid(w2, p1.num_generators),
        equiv_in_pred_presentation(free_product_pred(p1, p2), w1, w2),
    ensures
        equiv_in_pred_presentation(p1, w1, w2),
{
    let rho = fp_left_retraction_pred(p1, p2);
    lemma_fp_left_retraction_pred_valid(p1, p2);
    lemma_hom_pred_preserves_equiv(rho, w1, w2);
    lemma_fp_left_retraction_pred_identity(p1, p2, w1);
    lemma_fp_left_retraction_pred_identity(p1, p2, w2);
}

} //  verus!
