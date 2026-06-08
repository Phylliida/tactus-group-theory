use vstd::prelude::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;

verus! {

///  Add a single relator to a presentation.
pub open spec fn add_relator(p: Presentation, r: Word) -> Presentation {
    Presentation {
        num_generators: p.num_generators,
        relators: p.relators.push(r),
    }
}

///  Add multiple relators to a presentation (recursive).
pub open spec fn add_relators(p: Presentation, rs: Seq<Word>) -> Presentation
    decreases rs.len(),
{
    if rs.len() == 0 {
        p
    } else {
        add_relators(add_relator(p, rs.first()), rs.drop_first())
    }
}

//  --- Lemmas ---

///  Adding a relator extends the presentation.
pub proof fn lemma_add_relator_extends(p: Presentation, r: Word)
    ensures
        extends_presentation(p, add_relator(p, r)),
{
    let p2 = add_relator(p, r);
    assert(p2.num_generators == p.num_generators);
    assert(p2.relators.len() == p.relators.len() + 1);
    assert(p2.relators.subrange(0, p.relators.len() as int) =~= p.relators);
}

///  Extension is transitive.
pub proof fn lemma_extends_transitive(p1: Presentation, p2: Presentation, p3: Presentation)
    requires
        extends_presentation(p1, p2),
        extends_presentation(p2, p3),
    ensures
        extends_presentation(p1, p3),
{
    assert(p3.num_generators == p1.num_generators);
    assert(p1.relators.len() <= p2.relators.len() <= p3.relators.len());
    //  p3.relators[0..p2.len] == p2.relators
    //  p2.relators[0..p1.len] == p1.relators
    //  So p3.relators[0..p1.len] == p1.relators
    assert(p3.relators.subrange(0, p1.relators.len() as int) =~= p1.relators);
}

///  Adding a relator preserves existing equivalences.
pub proof fn lemma_add_relator_preserves_equiv(
    p: Presentation, r: Word, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(add_relator(p, r), w1, w2),
{
    lemma_add_relator_extends(p, r);
    lemma_quotient_preserves_equiv(p, add_relator(p, r), w1, w2);
}

///  The newly added relator is the identity in the extended presentation.
pub proof fn lemma_added_relator_is_identity(p: Presentation, r: Word)
    ensures
        equiv_in_presentation(add_relator(p, r), r, empty_word()),
{
    let p2 = add_relator(p, r);
    let idx = p.relators.len();
    assert(p2.relators[idx as int] == r);
    lemma_relator_is_identity(p2, idx as int);
}

///  Conjugates of the added relator are also identity.
pub proof fn lemma_normal_closure_contains_conjugates(
    p: Presentation, r: Word, w: Word,
)
    ensures
        equiv_in_presentation(
            add_relator(p, r),
            concat(concat(w, r), inverse_word(w)),
            empty_word(),
        ),
{
    let p2 = add_relator(p, r);
    let idx = p.relators.len();
    assert(p2.relators[idx as int] == r);
    lemma_conjugate_relator_is_identity(p2, w, idx as int);
}

///  Adding multiple relators extends the original presentation.
pub proof fn lemma_add_relators_extends(p: Presentation, rs: Seq<Word>)
    ensures
        extends_presentation(p, add_relators(p, rs)),
    decreases rs.len(),
{
    if rs.len() == 0 {
        assert(p.relators.subrange(0, p.relators.len() as int) =~= p.relators);
    } else {
        let p1 = add_relator(p, rs.first());
        lemma_add_relator_extends(p, rs.first());
        lemma_add_relators_extends(p1, rs.drop_first());
        lemma_extends_transitive(p, p1, add_relators(p1, rs.drop_first()));
    }
}

///  Adding multiple relators preserves existing equivalences.
pub proof fn lemma_add_relators_preserves_equiv(
    p: Presentation, rs: Seq<Word>, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(add_relators(p, rs), w1, w2),
{
    lemma_add_relators_extends(p, rs);
    lemma_quotient_preserves_equiv(p, add_relators(p, rs), w1, w2);
}

///  Each added relator is the identity in the extended presentation.
pub proof fn lemma_each_added_relator_is_identity(
    p: Presentation, rs: Seq<Word>, i: int,
)
    requires
        0 <= i < rs.len(),
    ensures
        equiv_in_presentation(add_relators(p, rs), rs[i], empty_word()),
    decreases rs.len(),
{
    if rs.len() == 0 {
        //  impossible
    } else {
        let p1 = add_relator(p, rs.first());
        if i == 0 {
            //  rs[0] = rs.first() is the identity in p1
            lemma_added_relator_is_identity(p, rs.first());
            //  Lift to add_relators(p1, rs.drop_first())
            lemma_add_relators_extends(p1, rs.drop_first());
            lemma_quotient_preserves_equiv(
                p1,
                add_relators(p1, rs.drop_first()),
                rs.first(),
                empty_word(),
            );
            assert(rs[0] == rs.first());
        } else {
            //  rs[i] == rs.drop_first()[i-1]
            assert(rs[i] == rs.drop_first()[(i - 1) as int]);
            lemma_each_added_relator_is_identity(p1, rs.drop_first(), i - 1);
        }
    }
}

///  Adding relators preserves presentation_valid when all added words are word_valid.
pub proof fn lemma_add_relators_valid(p: Presentation, rs: Seq<Word>)
    requires
        presentation_valid(p),
        forall|i: int| 0 <= i < rs.len() ==> word_valid(rs[i], p.num_generators),
    ensures
        presentation_valid(add_relators(p, rs)),
    decreases rs.len(),
{
    reveal(presentation_valid);
    if rs.len() == 0 {
    } else {
        let p1 = add_relator(p, rs.first());
        assert(presentation_valid(p1)) by {
            assert forall|i: int| 0 <= i < p1.relators.len()
                implies word_valid(p1.relators[i], p1.num_generators)
            by {
                if i < p.relators.len() as int {
                    assert(p1.relators[i] == p.relators[i]);
                } else {
                    assert(p1.relators[i] == rs.first());
                    assert(rs[0] == rs.first());
                }
            }
        }
        assert forall|i: int| 0 <= i < rs.drop_first().len()
            implies word_valid(rs.drop_first()[i], p1.num_generators)
        by {
            assert(rs.drop_first()[i] == rs[i + 1]);
        }
        lemma_add_relators_valid(p1, rs.drop_first());
    }
}

} //  verus!
