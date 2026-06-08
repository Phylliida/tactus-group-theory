use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::homomorphism::*;

verus! {

//  ============================================================
//  Free Product Injectivity via Retraction Homomorphism
//  ============================================================
//
//  Theorem: If w is a G₁-word and w ≡ ε in free_product(p1, p2),
//  then w ≡ ε in p1.
//
//  Proof: Define a retraction ρ: FP → P₁ that collapses G₂ generators
//  to ε and maps G₁ generators to themselves. Then:
//    w ≡ ε in FP  ⟹  ρ(w) ≡ ρ(ε) in P₁  ⟹  w ≡ ε in P₁.

//  ============================================================
//  Left retraction: FP(p1, p2) → p1
//  ============================================================

///  The left retraction homomorphism.
///  Gen(i) for i < n₁ → [Gen(i)]; Gen(j) for j ≥ n₁ → ε.
pub open spec fn fp_left_retraction(p1: Presentation, p2: Presentation) -> HomomorphismData {
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;
    HomomorphismData {
        source: free_product(p1, p2),
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

///  If every symbol of w maps to ε under h, then apply_hom(h, w) =~= ε.
pub proof fn lemma_hom_collapses_word(h: HomomorphismData, w: Word)
    requires
        forall|k: int| 0 <= k < w.len() ==>
            apply_hom_symbol(h, #[trigger] w[k]) =~= empty_word(),
    ensures
        apply_hom(h, w) =~= empty_word(),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(w[0] == s);
        assert(apply_hom_symbol(h, s) =~= empty_word());
        //  Recurse: rest also collapses
        assert forall|k: int| 0 <= k < rest.len() implies
            apply_hom_symbol(h, #[trigger] rest[k]) =~= empty_word()
        by {
            assert(rest[k] == w[k + 1]);
        }
        lemma_hom_collapses_word(h, rest);
        assert(apply_hom(h, rest) =~= empty_word());
        assert(apply_hom(h, w) =~= concat(empty_word(), empty_word()));
        assert(concat(empty_word(), empty_word()) =~= empty_word());
    }
}

//  ============================================================
//  Helper: apply_hom is the identity on words with identity images
//  ============================================================

///  If images[i] =~= [Gen(i)] for all i < n, and word_valid(w, n),
///  then apply_hom(h, w) =~= w.
pub proof fn lemma_hom_identity_on_word(h: HomomorphismData, w: Word, n: nat)
    requires
        forall|i: int| 0 <= i < n ==>
            h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen(i as nat)),
        h.generator_images.len() >= n,
        word_valid(w, n),
    ensures
        apply_hom(h, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_hom(h, w) =~= empty_word());
        assert(w =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, n));

        //  Recurse
        assert(word_valid(rest, n)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], n)
            by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_hom_identity_on_word(h, rest, n);
        assert(apply_hom(h, rest) =~= rest);

        //  Show apply_hom_symbol(h, s) =~= Seq::new(1, |_| s)
        let idx = generator_index(s);
        assert(idx < n);
        match s {
            Symbol::Gen(i) => {
                assert(h.generator_images[i as int]
                    =~= Seq::new(1, |_j: int| Symbol::Gen(i)));
                assert(apply_hom_symbol(h, s) =~= h.generator_images[i as int]);
                assert(apply_hom_symbol(h, s)
                    =~= Seq::new(1, |_j: int| Symbol::Gen(i)));
            },
            Symbol::Inv(i) => {
                let img = Seq::new(1, |_j: int| Symbol::Gen(i));
                assert(h.generator_images[i as int] =~= img);
                //  inverse_word([Gen(i)]) = inverse_word([].drop_first()) + [Inv(Gen(i).first())]
                //  = inverse_word(empty) + [Inv(i)] = empty + [Inv(i)] = [Inv(i)]
                assert(img.drop_first() =~= Seq::<Symbol>::empty());
                assert(inverse_word(img.drop_first()) =~= empty_word());
                assert(inverse_symbol(img.first()) == Symbol::Inv(i));
                let inv_img = inverse_word(img);
                assert(inv_img =~= empty_word() + Seq::new(1, |_j: int| Symbol::Inv(i)));
                assert(inv_img =~= Seq::new(1, |_j: int| Symbol::Inv(i)));
                assert(apply_hom_symbol(h, s) =~= inv_img);
            },
        }

        //  apply_hom(h, w) = concat(apply_hom_symbol(h, s), apply_hom(h, rest))
        //                  =~= concat([s], rest) =~= w
        assert(apply_hom_symbol(h, s) =~= Seq::new(1, |_j: int| s));
        assert(apply_hom(h, w) =~= concat(Seq::new(1, |_j: int| s), rest));
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
//  Left retraction is a valid homomorphism
//  ============================================================

///  The left retraction is a valid homomorphism.
pub proof fn lemma_fp_left_retraction_valid(p1: Presentation, p2: Presentation)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
    ensures
        is_valid_homomorphism(fp_left_retraction(p1, p2)),
{
    reveal(presentation_valid);
    let rho = fp_left_retraction(p1, p2);
    let fp = free_product(p1, p2);
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;

    //  generator_images.len() == n1 + n2 = fp.num_generators
    assert(rho.generator_images.len() == n1 + n2);
    assert(rho.source.num_generators == n1 + n2);

    //  source = free_product(p1, p2) is presentation_valid
    assert(presentation_valid(fp)) by {
        assert forall|k: int| 0 <= k < fp.relators.len()
            implies word_valid(fp.relators[k], fp.num_generators)
        by {
            if k < p1.relators.len() as int {
                assert(fp.relators[k] == p1.relators[k]);
                assert(word_valid(p1.relators[k], n1));
                assert forall|m: int| 0 <= m < fp.relators[k].len()
                    implies symbol_valid(fp.relators[k][m], n1 + n2) by {
                    assert(symbol_valid(fp.relators[k][m], n1));
                }
            } else {
                let j = k - p1.relators.len() as int;
                assert(fp.relators[k] == shift_word(p2.relators[j], n1));
                //  shift_word_valid: shifted word is valid for combined generator count
                let sw = shift_word(p2.relators[j], n1);
                assert forall|m: int| 0 <= m < sw.len()
                    implies symbol_valid(sw[m], n1 + n2)
                by {
                    assert(sw[m] == shift_symbol(p2.relators[j][m], n1));
                    assert(symbol_valid(p2.relators[j][m], n2));
                }
            }
        }
    }

    //  target = p1 is presentation_valid (given)

    //  Each image is word_valid for p1
    assert forall|i: int| 0 <= i < rho.generator_images.len()
        implies word_valid(rho.generator_images[i], n1)
    by {
        if i < n1 as int {
            //  Image is [Gen(i)], valid for n1
            assert(rho.generator_images[i] =~=
                Seq::new(1, |_j: int| Symbol::Gen(i as nat)));
            assert(symbol_valid(Symbol::Gen(i as nat), n1));
        } else {
            //  Image is empty_word(), trivially valid
        }
    }

    //  Each source relator maps to ≡ ε in p1
    assert forall|i: int| 0 <= i < fp.relators.len()
        implies equiv_in_presentation(p1, apply_hom(rho, fp.relators[i]), empty_word())
    by {
        if i < p1.relators.len() as int {
            //  G₁-relator: rho maps it to itself
            let r = fp.relators[i];
            assert(r == p1.relators[i]);
            assert(word_valid(r, n1));
            lemma_hom_identity_on_word(rho, r, n1);
            assert(apply_hom(rho, r) =~= r);
            //  r ≡ ε in p1 since it's a relator
            lemma_relator_is_identity(p1, i);
            //  Need: apply_hom(rho, r) ≡ ε. Since apply_hom(rho, r) =~= r and r ≡ ε:
            lemma_equiv_refl(p1, apply_hom(rho, r));
        } else {
            //  Shifted G₂-relator: all symbols have index ≥ n1, so all map to ε
            let j = i - p1.relators.len() as int;
            let r = fp.relators[i];
            assert(r == shift_word(p2.relators[j], n1));
            //  Every symbol in r has generator_index ≥ n1
            assert forall|k: int| 0 <= k < r.len()
                implies apply_hom_symbol(rho, #[trigger] r[k]) =~= empty_word()
            by {
                let s = r[k];
                assert(s == shift_symbol(p2.relators[j][k], n1));
                let orig = p2.relators[j][k];
                match orig {
                    Symbol::Gen(gi) => {
                        assert(s == Symbol::Gen(gi + n1));
                        assert(generator_index(s) == gi + n1);
                        assert(gi + n1 >= n1);
                        assert(rho.generator_images[(gi + n1) as int] =~= empty_word());
                    },
                    Symbol::Inv(gi) => {
                        assert(s == Symbol::Inv(gi + n1));
                        assert(generator_index(s) == gi + n1);
                        assert(gi + n1 >= n1);
                        assert(rho.generator_images[(gi + n1) as int] =~= empty_word());
                        assert(inverse_word(empty_word()) =~= empty_word());
                    },
                }
            }
            lemma_hom_collapses_word(rho, r);
            assert(apply_hom(rho, r) =~= empty_word());
            lemma_equiv_refl(p1, empty_word());
        }
    }
}

//  ============================================================
//  Left retraction is the identity on G₁-words
//  ============================================================

///  For G₁-words: apply_hom(ρ, w) =~= w.
pub proof fn lemma_fp_left_retraction_identity(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        word_valid(w, p1.num_generators),
    ensures
        apply_hom(fp_left_retraction(p1, p2), w) =~= w,
{
    let rho = fp_left_retraction(p1, p2);
    let n1 = p1.num_generators;
    lemma_hom_identity_on_word(rho, w, n1);
}

//  ============================================================
//  Main theorem: free product injectivity (left)
//  ============================================================

///  If w is a G₁-word and w ≡ ε in free_product(p1, p2), then w ≡ ε in p1.
pub proof fn lemma_free_product_injective_left(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
        word_valid(w, p1.num_generators),
        equiv_in_presentation(free_product(p1, p2), w, empty_word()),
    ensures
        equiv_in_presentation(p1, w, empty_word()),
{
    let rho = fp_left_retraction(p1, p2);

    //  rho is a valid homomorphism
    lemma_fp_left_retraction_valid(p1, p2);

    //  rho preserves equivalence: w ≡ ε in FP ⟹ rho(w) ≡ rho(ε) in P₁
    lemma_hom_preserves_equiv(rho, w, empty_word());

    //  rho(w) =~= w
    lemma_fp_left_retraction_identity(p1, p2, w);

    //  rho(ε) =~= ε
    lemma_hom_empty(rho);

    //  So w ≡ ε in P₁
}

//  ============================================================
//  Right retraction: FP(p1, p2) → p2
//  ============================================================

///  The right retraction homomorphism.
///  Gen(i) for i < n₁ → ε; Gen(n₁+j) for j < n₂ → [Gen(j)].
pub open spec fn fp_right_retraction(p1: Presentation, p2: Presentation) -> HomomorphismData {
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;
    HomomorphismData {
        source: free_product(p1, p2),
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
pub proof fn lemma_fp_right_retraction_valid(p1: Presentation, p2: Presentation)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
    ensures
        is_valid_homomorphism(fp_right_retraction(p1, p2)),
{
    reveal(presentation_valid);
    let rho = fp_right_retraction(p1, p2);
    let fp = free_product(p1, p2);
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;

    //  source = free_product(p1, p2) is presentation_valid
    assert(presentation_valid(fp)) by {
        assert forall|k: int| 0 <= k < fp.relators.len()
            implies word_valid(fp.relators[k], fp.num_generators)
        by {
            if k < p1.relators.len() as int {
                assert(fp.relators[k] == p1.relators[k]);
                assert(word_valid(p1.relators[k], n1));
                assert forall|m: int| 0 <= m < fp.relators[k].len()
                    implies symbol_valid(fp.relators[k][m], n1 + n2) by {
                    assert(symbol_valid(fp.relators[k][m], n1));
                }
            } else {
                let j = k - p1.relators.len() as int;
                assert(fp.relators[k] == shift_word(p2.relators[j], n1));
                //  shift_word_valid: shifted word is valid for combined generator count
                let sw = shift_word(p2.relators[j], n1);
                assert forall|m: int| 0 <= m < sw.len()
                    implies symbol_valid(sw[m], n1 + n2)
                by {
                    assert(sw[m] == shift_symbol(p2.relators[j][m], n1));
                    assert(symbol_valid(p2.relators[j][m], n2));
                }
            }
        }
    }

    //  Each image is word_valid for p2
    assert forall|i: int| 0 <= i < rho.generator_images.len()
        implies word_valid(rho.generator_images[i], n2)
    by {
        if i < n1 as int {
            //  empty_word() is trivially valid
        } else {
            let gi = (i - n1) as nat;
            assert(rho.generator_images[i] =~=
                Seq::new(1, |_j: int| Symbol::Gen(gi)));
            assert(gi < n2);
            assert(symbol_valid(Symbol::Gen(gi), n2));
        }
    }

    //  Each source relator maps to ≡ ε in p2
    assert forall|i: int| 0 <= i < fp.relators.len()
        implies equiv_in_presentation(p2, apply_hom(rho, fp.relators[i]), empty_word())
    by {
        if i < p1.relators.len() as int {
            //  G₁-relator: all symbols have index < n1, all map to ε
            let r = fp.relators[i];
            assert(r == p1.relators[i]);
            assert(word_valid(r, n1));
            assert forall|k: int| 0 <= k < r.len()
                implies apply_hom_symbol(rho, #[trigger] r[k]) =~= empty_word()
            by {
                let s = r[k];
                assert(symbol_valid(s, n1));
                assert(generator_index(s) < n1);
                match s {
                    Symbol::Gen(gi) => {
                        assert(rho.generator_images[gi as int] =~= empty_word());
                    },
                    Symbol::Inv(gi) => {
                        assert(rho.generator_images[gi as int] =~= empty_word());
                        assert(inverse_word(empty_word()) =~= empty_word());
                    },
                }
            }
            lemma_hom_collapses_word(rho, r);
            lemma_equiv_refl(p2, empty_word());
        } else {
            //  Shifted G₂-relator: rho maps shift(Gen(j)) = Gen(n1+j) → [Gen(j)]
            //  So rho(shift(r_j)) =~= r_j (the original G₂ relator)
            let j = i - p1.relators.len() as int;
            let sr = fp.relators[i];
            assert(sr == shift_word(p2.relators[j], n1));
            let r = p2.relators[j];

            //  Show apply_hom(rho, sr) =~= r by showing it's the identity on shifted words
            lemma_right_retraction_unshifts(p1, p2, r);
            assert(apply_hom(rho, sr) =~= r);

            //  r ≡ ε in p2 since it's a relator
            lemma_relator_is_identity(p2, j);
            lemma_equiv_refl(p2, apply_hom(rho, sr));
        }
    }
}

///  Helper: The right retraction unshifts a shifted G₂-word back to the original.
///  apply_hom(right_rho, shift_word(w, n1)) =~= w for G₂-words.
proof fn lemma_right_retraction_unshifts(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        word_valid(w, p2.num_generators),
    ensures
        apply_hom(fp_right_retraction(p1, p2), shift_word(w, p1.num_generators)) =~= w,
    decreases w.len(),
{
    let rho = fp_right_retraction(p1, p2);
    let n1 = p1.num_generators;
    let sw = shift_word(w, n1);

    if w.len() == 0 {
        assert(sw =~= empty_word());
        assert(apply_hom(rho, sw) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let ss = shift_symbol(s, n1);
        let srest = shift_word(rest, n1);

        assert(sw.first() == ss);
        assert(sw.drop_first() =~= srest);

        //  Recurse
        assert(word_valid(rest, p2.num_generators)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], p2.num_generators)
            by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_right_retraction_unshifts(p1, p2, rest);
        assert(apply_hom(rho, srest) =~= rest);

        //  Show apply_hom_symbol(rho, ss) =~= Seq::new(1, |_| s)
        assert(symbol_valid(s, p2.num_generators));
        match s {
            Symbol::Gen(gi) => {
                assert(ss == Symbol::Gen(gi + n1));
                assert((gi + n1) >= n1);
                assert(rho.generator_images[(gi + n1) as int]
                    =~= Seq::new(1, |_j: int| Symbol::Gen(gi)));
                assert(apply_hom_symbol(rho, ss)
                    =~= Seq::new(1, |_j: int| Symbol::Gen(gi)));
                assert(Seq::new(1, |_j: int| Symbol::Gen(gi))
                    =~= Seq::new(1, |_j: int| s));
            },
            Symbol::Inv(gi) => {
                assert(ss == Symbol::Inv(gi + n1));
                assert((gi + n1) >= n1);
                let img = Seq::new(1, |_j: int| Symbol::Gen(gi));
                assert(rho.generator_images[(gi + n1) as int] =~= img);
                //  Expand inverse_word on single-element seq
                assert(img.drop_first() =~= Seq::<Symbol>::empty());
                assert(inverse_word(img.drop_first()) =~= empty_word());
                assert(inverse_symbol(img.first()) == Symbol::Inv(gi));
                let inv_img = inverse_word(img);
                assert(inv_img =~= empty_word() + Seq::new(1, |_j: int| Symbol::Inv(gi)));
                assert(inv_img =~= Seq::new(1, |_j: int| Symbol::Inv(gi)));
                assert(apply_hom_symbol(rho, ss) =~= inv_img);
                assert(Seq::new(1, |_j: int| Symbol::Inv(gi))
                    =~= Seq::new(1, |_j: int| s));
            },
        }

        //  apply_hom(rho, sw) = concat(apply_hom_symbol(rho, ss), apply_hom(rho, srest))
        //                     =~= concat([s], rest) =~= w
        assert(apply_hom_symbol(rho, ss) =~= Seq::new(1, |_j: int| s));
        assert(apply_hom(rho, sw) =~= concat(Seq::new(1, |_j: int| s), rest));
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

///  For shifted G₂-words: apply_hom(right_rho, shift_word(w, n1)) =~= w.
pub proof fn lemma_fp_right_retraction_identity(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        word_valid(w, p2.num_generators),
    ensures
        apply_hom(fp_right_retraction(p1, p2), shift_word(w, p1.num_generators)) =~= w,
{
    lemma_right_retraction_unshifts(p1, p2, w);
}

//  ============================================================
//  Main theorem: free product injectivity (right)
//  ============================================================

///  If w is a G₂-word and shift(w) ≡ ε in free_product(p1, p2), then w ≡ ε in p2.
pub proof fn lemma_free_product_injective_right(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
        word_valid(w, p2.num_generators),
        equiv_in_presentation(
            free_product(p1, p2),
            shift_word(w, p1.num_generators),
            empty_word(),
        ),
    ensures
        equiv_in_presentation(p2, w, empty_word()),
{
    let rho = fp_right_retraction(p1, p2);

    //  rho is a valid homomorphism
    lemma_fp_right_retraction_valid(p1, p2);

    //  rho preserves equivalence
    lemma_hom_preserves_equiv(rho, shift_word(w, p1.num_generators), empty_word());

    //  rho(shift(w)) =~= w
    lemma_fp_right_retraction_identity(p1, p2, w);

    //  rho(ε) =~= ε
    lemma_hom_empty(rho);
}

//  ============================================================
//  General form: two G₁-words equivalent in FP are equivalent in P₁
//  ============================================================

///  If w₁, w₂ are G₁-words and w₁ ≡ w₂ in FP, then w₁ ≡ w₂ in P₁.
pub proof fn lemma_free_product_reflects_left(
    p1: Presentation, p2: Presentation, w1: Word, w2: Word,
)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
        word_valid(w1, p1.num_generators),
        word_valid(w2, p1.num_generators),
        equiv_in_presentation(free_product(p1, p2), w1, w2),
    ensures
        equiv_in_presentation(p1, w1, w2),
{
    let rho = fp_left_retraction(p1, p2);
    lemma_fp_left_retraction_valid(p1, p2);
    lemma_hom_preserves_equiv(rho, w1, w2);
    lemma_fp_left_retraction_identity(p1, p2, w1);
    lemma_fp_left_retraction_identity(p1, p2, w2);
}

} //  verus!
