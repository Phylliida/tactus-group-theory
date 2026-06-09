use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::quotient::*;

verus! {

///  Commutator [g, h] = g·h·g⁻¹·h⁻¹.
pub open spec fn commutator(g: Word, h: Word) -> Word {
    concat(concat(concat(g, h), inverse_word(g)), inverse_word(h))
}

///  Single-generator word [Gen(i)].
pub open spec fn gen_word(i: nat) -> Word {
    Seq::new(1, |_j: int| Symbol::Gen(i))
}

///  All generator commutators [g_i, g_j] for 0 <= i < j < n.
pub open spec fn generator_commutators(n: nat) -> Seq<Word>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        //  Commutators involving generators 0..n-2 with each other
        let prev = generator_commutators((n - 1) as nat);
        //  Plus: [g_i, g_{n-1}] for 0 <= i < n-1
        let new_commutators = Seq::new((n - 1) as nat, |i: int|
            commutator(gen_word(i as nat), gen_word((n - 1) as nat))
        );
        prev + new_commutators
    }
}

///  Abelianization: add all generator commutators as relators.
pub open spec fn abelianization(p: Presentation) -> Presentation {
    add_relators(p, generator_commutators(p.num_generators))
}

//  --- Lemmas ---

///  [g_i, g_j] appears in generator_commutators(n) for i < j < n.
pub proof fn lemma_commutator_in_list(n: nat, i: nat, j: nat)
    requires
        i < j,
        j < n,
    ensures
        ({
            let comms = generator_commutators(n);
            exists|k: int| 0 <= k < comms.len() && comms[k] == commutator(gen_word(i), gen_word(j))
        }),
    decreases n,
{
    if n == 0 {
        //  impossible
    } else if j == n - 1 {
        //  [g_i, g_{n-1}] is in the new_commutators batch
        let prev = generator_commutators((n - 1) as nat);
        let new_comms = Seq::new((n - 1) as nat, |k: int|
            commutator(gen_word(k as nat), gen_word((n - 1) as nat))
        );
        let comms = prev + new_comms;
        assert(comms == generator_commutators(n));
        let idx = (prev.len() + i) as int;
        assert(comms[idx] == new_comms[i as int]);
        assert(new_comms[i as int] == commutator(gen_word(i), gen_word((n - 1) as nat)));
    } else {
        //  j < n - 1, so the commutator is in the recursive part
        lemma_commutator_in_list((n - 1) as nat, i, j);
        let prev = generator_commutators((n - 1) as nat);
        let new_comms = Seq::new((n - 1) as nat, |k: int|
            commutator(gen_word(k as nat), gen_word((n - 1) as nat))
        );
        let comms = prev + new_comms;
        assert(comms == generator_commutators(n));
        //  The witness k from the recursive call also works in the larger sequence
        let k = choose|k: int| 0 <= k < prev.len() && prev[k] == commutator(gen_word(i), gen_word(j));
        assert(comms[k] == prev[k]);
    }
}

///  Single-generator words are word_valid.
proof fn lemma_gen_word_valid(i: nat, n: nat)
    requires i < n,
    ensures word_valid(gen_word(i), n),
{
    assert forall|k: int| 0 <= k < gen_word(i).len()
        implies symbol_valid(gen_word(i)[k], n) by {}
}

///  Commutator word is word_valid.
proof fn lemma_commutator_word_valid(i: nat, j: nat, n: nat)
    requires i < n, j < n,
    ensures word_valid(commutator(gen_word(i), gen_word(j)), n),
{
    lemma_gen_word_valid(i, n);
    lemma_gen_word_valid(j, n);
    crate::word::lemma_inverse_word_valid(gen_word(i), n);
    crate::word::lemma_inverse_word_valid(gen_word(j), n);
    crate::word::lemma_concat_word_valid(gen_word(i), gen_word(j), n);
    crate::word::lemma_concat_word_valid(concat(gen_word(i), gen_word(j)), inverse_word(gen_word(i)), n);
    crate::word::lemma_concat_word_valid(
        concat(concat(gen_word(i), gen_word(j)), inverse_word(gen_word(i))),
        inverse_word(gen_word(j)), n);
}

///  All generator commutators are word_valid.
proof fn lemma_commutators_word_valid(n: nat)
    ensures
        forall|k: int| 0 <= k < generator_commutators(n).len()
            ==> word_valid(generator_commutators(n)[k], n),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_commutators_word_valid((n - 1) as nat);
        let prev = generator_commutators((n - 1) as nat);
        let new_comms = Seq::new((n - 1) as nat, |i: int|
            commutator(gen_word(i as nat), gen_word((n - 1) as nat))
        );
        let comms = prev + new_comms;
        assert(comms == generator_commutators(n));
        assert forall|k: int| 0 <= k < comms.len()
            implies word_valid(comms[k], n)
        by {
            if k < prev.len() as int {
                assert(comms[k] == prev[k]);
                //  prev[k] is word_valid for (n-1) which is < n, so also for n
                assert(word_valid(prev[k], (n - 1) as nat));
                //  word_valid for (n-1) implies word_valid for n
                assert forall|m: int| 0 <= m < prev[k].len()
                    implies symbol_valid(prev[k][m], n)
                by {
                    assert(symbol_valid(prev[k][m], (n - 1) as nat));
                }
            } else {
                let i = (k - prev.len()) as int;
                assert(comms[k] == new_comms[i]);
                assert(new_comms[i] == commutator(gen_word(i as nat), gen_word((n - 1) as nat)));
                lemma_commutator_word_valid(i as nat, (n - 1) as nat, n);
            }
        }
    }
}

///  [g_i, g_j] ≡ ε in abelianization(p) when i < j < p.num_generators.
pub proof fn lemma_commutator_is_identity(p: Presentation, i: nat, j: nat)
    requires
        i < j,
        j < p.num_generators,
    ensures
        equiv_in_presentation(
            abelianization(p),
            commutator(gen_word(i), gen_word(j)),
            empty_word(),
        ),
{
    let n = p.num_generators;
    let comms = generator_commutators(n);
    lemma_commutator_in_list(n, i, j);
    let k = choose|k: int| 0 <= k < comms.len() && comms[k] == commutator(gen_word(i), gen_word(j));
    lemma_each_added_relator_is_identity(p, comms, k);
}

///  In abelianization(p), g_i·g_j ≡ g_j·g_i for i < j.
///
///  Proof: [g_i, g_j] = g_i·g_j·g_i⁻¹·g_j⁻¹ ≡ ε
///  So g_i·g_j·g_i⁻¹·g_j⁻¹ ≡ ε
///  Right-multiply both sides by g_j·g_i:
///  g_i·g_j·g_i⁻¹·g_j⁻¹·g_j·g_i ≡ g_j·g_i
///  Cancel g_j⁻¹·g_j and g_i⁻¹·g_i:
///  g_i·g_j ≡ g_j·g_i
pub proof fn lemma_abelianization_commutes(p: Presentation, i: nat, j: nat)
    requires
        i < j,
        j < p.num_generators,
        presentation_valid(p),
    ensures
        equiv_in_presentation(
            abelianization(p),
            concat(gen_word(i), gen_word(j)),
            concat(gen_word(j), gen_word(i)),
        ),
{
    let ap = abelianization(p);
    let gi = gen_word(i);
    let gj = gen_word(j);
    let gi_inv = inverse_word(gi);
    let gj_inv = inverse_word(gj);
    let gj_gi = concat(gj, gi);

    //  Step 1: [gi, gj] ≡ ε
    lemma_commutator_is_identity(p, i, j);
    //  commutator(gi, gj) = gi·gj·gi⁻¹·gj⁻¹

    //  Step 2: [gi, gj]·gj·gi ≡ ε·gj·gi = gj·gi
    //  commutator · gj_gi ≡ gj_gi
    lemma_equiv_concat_left(ap,
        commutator(gi, gj), empty_word(), gj_gi);
    assert(concat(empty_word(), gj_gi) =~= gj_gi);
    lemma_equiv_refl(ap, gj_gi);
    lemma_equiv_transitive(ap,
        concat(commutator(gi, gj), gj_gi),
        concat(empty_word(), gj_gi),
        gj_gi,
    );

    //  Step 3: Reassociate commutator · gj_gi
    //  = (gi·gj·gi⁻¹·gj⁻¹)·(gj·gi)
    //  = gi·gj·gi⁻¹·(gj⁻¹·gj)·gi   (by assoc)
    //  = gi·gj·(gi⁻¹·gi)             (after gj⁻¹·gj cancels)
    //  = gi·gj                         (after gi⁻¹·gi cancels)

    //  We need: gi·gj ≡ concat(commutator(gi,gj), gj_gi)
    //  Then by transitivity: gi·gj ≡ gj·gi

    //  Show gj⁻¹·gj ≡ ε
    lemma_word_inverse_left(ap, gj);
    //  Show gi⁻¹·gi ≡ ε
    lemma_word_inverse_left(ap, gi);

    //  gj⁻¹·gj·gi ≡ ε·gi = gi
    lemma_equiv_concat_left(ap, concat(gj_inv, gj), empty_word(), gi);
    assert(concat(empty_word(), gi) =~= gi);
    lemma_equiv_refl(ap, gi);
    lemma_equiv_transitive(ap,
        concat(concat(gj_inv, gj), gi),
        concat(empty_word(), gi),
        gi,
    );

    //  gi⁻¹·(gj⁻¹·gj·gi) ≡ gi⁻¹·gi ≡ ε
    lemma_equiv_concat_left(ap,
        concat(concat(gj_inv, gj), gi),
        gi,
        gi_inv,
    );
    //  Flip the order: put gi_inv on left
    //  Actually we need: gi_inv · gj_inv · gj · gi
    //  Let me reassociate: commutator(gi,gj) · gj · gi
    //  = gi · gj · gi_inv · gj_inv · gj · gi
    //  = gi · gj · gi_inv · (gj_inv · gj) · gi
    //  We need to show this extensionally equals gi · gj · gi_inv · gj_inv · gj · gi

    //  Let's just show the whole thing directly by Seq extensionality
    //  commutator(gi, gj) = concat(concat(concat(gi, gj), gi_inv), gj_inv)
    //  concat(commutator(gi,gj), gj_gi) by Seq assoc:
    //  = gi ++ gj ++ gi_inv ++ gj_inv ++ gj ++ gi

    //  gi ++ gj = concat(gi, gj)
    let gi_gj = concat(gi, gj);

    //  gi_inv ++ gj_inv ++ gj ++ gi
    let tail = concat(concat(concat(gi_inv, gj_inv), gj), gi);

    //  Show: concat(commutator(gi,gj), gj_gi) =~= concat(gi_gj, tail)
    assert(concat(commutator(gi, gj), gj_gi) =~= concat(gi_gj, tail)) by {
        //  Both sides are gi ++ gj ++ gi_inv ++ gj_inv ++ gj ++ gi
        //  commutator = ((gi ++ gj) ++ gi_inv) ++ gj_inv
        //  left side = (((gi ++ gj) ++ gi_inv) ++ gj_inv) ++ (gj ++ gi)
        //  right side = (gi ++ gj) ++ (((gi_inv ++ gj_inv) ++ gj) ++ gi)
        //  Both flatten to the same sequence
        lemma_inverse_singleton(Symbol::Gen(i));
        lemma_inverse_singleton(Symbol::Gen(j));
        assert(gi.len() == 1);
        assert(gj.len() == 1);
        assert(gi_inv.len() == 1);
        assert(gj_inv.len() == 1);
    }

    //  Now show tail ≡ ε in ap
    //  tail = gi_inv ++ gj_inv ++ gj ++ gi
    //       = gi_inv ++ (gj_inv ++ gj) ++ gi
    //  gj_inv ++ gj ≡ ε, so gj_inv ++ gj ++ gi ≡ gi
    //  gi_inv ++ gi ≡ ε
    //  So tail ≡ ε

    //  gj_inv ++ gj ++ gi ≡ gi  (since gj_inv·gj ≡ ε)
    let gj_inv_gj_gi = concat(concat(gj_inv, gj), gi);
    lemma_equiv_concat_left(ap, concat(gj_inv, gj), empty_word(), gi);
    assert(concat(empty_word(), gi) =~= gi);
    lemma_equiv_transitive(ap, gj_inv_gj_gi, concat(empty_word(), gi), gi);

    //  gi_inv ++ (gj_inv ++ gj ++ gi) ≡ gi_inv ++ gi ≡ ε
    lemma_equiv_concat_right(ap, gi_inv, gj_inv_gj_gi, gi);
    //  concat(gi_inv, gj_inv_gj_gi) ≡ concat(gi_inv, gi)
    lemma_equiv_transitive(ap,
        concat(gi_inv, gj_inv_gj_gi),
        concat(gi_inv, gi),
        empty_word(),
    );

    //  tail =~= concat(gi_inv, gj_inv_gj_gi) (by Seq assoc)
    assert(tail =~= concat(gi_inv, gj_inv_gj_gi));

    //  So tail ≡ ε
    //  concat(gi_gj, tail) ≡ concat(gi_gj, ε) = gi_gj
    lemma_equiv_concat_right(ap, gi_gj, tail, empty_word());
    assert(concat(gi_gj, empty_word()) =~= gi_gj);
    lemma_equiv_refl(ap, gi_gj);
    lemma_equiv_transitive(ap,
        concat(gi_gj, tail),
        concat(gi_gj, empty_word()),
        gi_gj,
    );

    //  gi_gj ≡ concat(gi_gj, tail) (symmetric)
    //  Prove word_valid(concat(gi_gj, tail)) and presentation_valid(ap) for symmetric
    lemma_abelianization_extends(p);
    assert(ap.num_generators == p.num_generators);
    lemma_gen_word_valid(i, ap.num_generators);
    lemma_gen_word_valid(j, ap.num_generators);
    crate::word::lemma_concat_word_valid(gi, gj, ap.num_generators);
    lemma_inverse_singleton(Symbol::Gen(i));
    lemma_inverse_singleton(Symbol::Gen(j));
    assert(word_valid(gi_inv, ap.num_generators)) by {
        crate::word::lemma_inverse_word_valid(gi, ap.num_generators);
    }
    assert(word_valid(gj_inv, ap.num_generators)) by {
        crate::word::lemma_inverse_word_valid(gj, ap.num_generators);
    }
    crate::word::lemma_concat_word_valid(gi_inv, gj_inv, ap.num_generators);
    crate::word::lemma_concat_word_valid(concat(gi_inv, gj_inv), gj, ap.num_generators);
    crate::word::lemma_concat_word_valid(concat(concat(gi_inv, gj_inv), gj), gi, ap.num_generators);
    crate::word::lemma_concat_word_valid(gi_gj, tail, ap.num_generators);
    //  Prove presentation_valid(ap)
    //  Commutators are word_valid since they use Gen(i)/Inv(i) with i < p.num_generators
    lemma_commutators_word_valid(p.num_generators);
    lemma_add_relators_valid(p, generator_commutators(p.num_generators));
    lemma_equiv_symmetric(ap, concat(gi_gj, tail), gi_gj);

    //  concat(gi_gj, tail) =~= concat(commutator(gi, gj), gj_gi)
    //  gi_gj ≡ concat(commutator, gj_gi) ≡ gj_gi
    lemma_equiv_transitive(ap, gi_gj, concat(commutator(gi, gj), gj_gi), gj_gi);
}

///  Abelianization extends the original presentation.
pub proof fn lemma_abelianization_extends(p: Presentation)
    ensures
        extends_presentation(p, abelianization(p)),
{
    lemma_add_relators_extends(p, generator_commutators(p.num_generators));
}

///  Equivalence in p is preserved in abelianization(p).
pub proof fn lemma_abelianization_preserves_equiv(p: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(abelianization(p), w1, w2),
{
    lemma_add_relators_preserves_equiv(p, generator_commutators(p.num_generators), w1, w2);
}

} //  verus!
