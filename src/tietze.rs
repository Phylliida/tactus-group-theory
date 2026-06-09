use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::quotient::*;

verus! {

///  Tietze transformation types.
pub enum TietzeStep {
    ///  T3: Add a relator that is derivable (equivalent to ε).
    AddRelator { relator: Word },
    ///  T4: Remove a relator at given index.
    RemoveRelator { relator_index: nat },
    ///  T1: Add a new generator with a defining relator Gen(n)·defining_word⁻¹.
    AddGenerator { defining_word: Word },
}

///  Remove the relator at a given index.
pub open spec fn remove_relator(p: Presentation, idx: nat) -> Presentation
    recommends idx < p.relators.len(),
{
    Presentation {
        num_generators: p.num_generators,
        relators: p.relators.subrange(0, idx as int) + p.relators.subrange(idx as int + 1, p.relators.len() as int),
    }
}

///  Add a new generator with a defining relator: Gen(n) · defining_word⁻¹.
///  The defining relator expresses that the new generator equals defining_word.
pub open spec fn add_generator_to_presentation(p: Presentation, defining_word: Word) -> Presentation {
    let new_gen = p.num_generators;
    let defining_relator = concat(
        Seq::new(1, |_i: int| Symbol::Gen(new_gen)),
        inverse_word(defining_word),
    );
    Presentation {
        num_generators: (new_gen + 1) as nat,
        relators: p.relators.push(defining_relator),
    }
}

//  --- Helpers ---

///  If w ≡ ε in p, then w⁻¹ ≡ ε in p.
pub proof fn lemma_inverse_of_identity(p: Presentation, w: Word)
    requires
        equiv_in_presentation(p, w, empty_word()),
        word_valid(w, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, inverse_word(w), empty_word()),
{
    //  inv(w) · w ≡ ε (left inverse)
    lemma_word_inverse_left(p, w);
    //  w ≡ ε, so inv(w) · w ≡ inv(w) · ε = inv(w)
    lemma_equiv_concat_right(p, inverse_word(w), w, empty_word());
    assert(concat(inverse_word(w), empty_word()) =~= inverse_word(w));
    lemma_equiv_refl(p, inverse_word(w));

    //  symmetric on concat(inv(w), w): need word_valid
    crate::word::lemma_inverse_word_valid(w, p.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(w), w, p.num_generators);
    lemma_equiv_symmetric(p,
        concat(inverse_word(w), w),
        concat(inverse_word(w), empty_word()),
    );
    lemma_equiv_transitive(p,
        inverse_word(w),
        concat(inverse_word(w), w),
        empty_word(),
    );
}

///  A single valid derivation step witnesses equivalence.
proof fn lemma_single_step_equiv(p: Presentation, w: Word, step: DerivationStep, w_prime: Word)
    requires
        apply_step(p, w, step) == Some(w_prime),
    ensures
        equiv_in_presentation(p, w, w_prime),
{
    let d = Derivation { steps: Seq::new(1, |_i: int| step) };
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(p, d.steps.drop_first(), w_prime) == Some(w_prime));
    assert(derivation_valid(p, d, w, w_prime));
}

//  --- Lemmas ---

///  T3 forward: adding a derivable relator preserves equivalence.
///  (Wrapper for lemma_add_relator_preserves_equiv.)
pub proof fn lemma_add_derivable_relator_forward(p: Presentation, r: Word, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(add_relator(p, r), w1, w2),
{
    lemma_add_relator_preserves_equiv(p, r, w1, w2);
}

///  T3 reverse: if r ≡ ε in p, then equivalence in add_relator(p, r) implies equivalence in p.
///
///  Proof sketch: Given a derivation in add_relator(p, r), every step using old relators
///  is valid in p. Steps using the new relator r can be replaced by the witness derivation
///  of r ≡ ε (or r⁻¹ ≡ ε) in p, conjugated appropriately.
pub proof fn lemma_add_derivable_relator_reverse(
    p: Presentation, r: Word, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
        equiv_in_presentation(add_relator(p, r), w1, w2),
        word_valid(r, p.num_generators),
        presentation_valid(p),
        word_valid(w1, p.num_generators),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let p2 = add_relator(p, r);
    let d = choose|d: Derivation| derivation_valid(p2, d, w1, w2);
    lemma_derivation_replace_new_relator(p, r, d.steps, w1, w2);
}

///  Core of T3 reverse: replace uses of the new relator in a derivation.
proof fn lemma_derivation_replace_new_relator(
    p: Presentation, r: Word,
    steps: Seq<DerivationStep>, w_start: Word, w_end: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
        derivation_produces(add_relator(p, r), steps, w_start) == Some(w_end),
        word_valid(r, p.num_generators),
        presentation_valid(p),
        word_valid(w_start, p.num_generators),
    ensures
        equiv_in_presentation(p, w_start, w_end),
    decreases steps.len(),
{
    reveal(presentation_valid);
    let p2 = add_relator(p, r);
    if steps.len() == 0 {
        assert(w_start == w_end);
        lemma_equiv_refl(p, w_start);
    } else {
        let step = steps.first();
        let w_mid = apply_step(p2, w_start, step).unwrap();
        let rest = steps.drop_first();

        //  Prove presentation_valid(p2) and word_valid(w_mid) for recursive call
        assert(presentation_valid(p2)) by {
            assert forall|i: int| 0 <= i < p2.relators.len()
                implies word_valid(p2.relators[i], p2.num_generators)
            by {
                if i < p.relators.len() as int {
                    assert(p2.relators[i] == p.relators[i]);
                } else {
                    assert(p2.relators[i] == r);
                }
            }
        }
        lemma_step_preserves_word_valid_pres(p2, w_start, step, w_mid);

        //  Recursion: w_mid → w_end is equivalent in p
        lemma_derivation_replace_new_relator(p, r, rest, w_mid, w_end);

        //  Now show w_start → w_mid is equivalent in p
        match step {
            DerivationStep::FreeReduce { position } => {
                assert(apply_step(p, w_start, step) == Some(w_mid));
                lemma_single_step_equiv(p, w_start, step, w_mid);
            },
            DerivationStep::FreeExpand { position, symbol } => {
                assert(apply_step(p, w_start, step) == Some(w_mid));
                lemma_single_step_equiv(p, w_start, step, w_mid);
            },
            DerivationStep::RelatorInsert { position, relator_index, inverted } => {
                if relator_index < p.relators.len() {
                    assert(p2.relators[relator_index as int] == p.relators[relator_index as int]);
                    assert(get_relator(p2, relator_index, inverted) == get_relator(p, relator_index, inverted));
                    assert(apply_step(p, w_start, step) == Some(w_mid));
                    lemma_single_step_equiv(p, w_start, step, w_mid);
                } else {
                    //  New relator: relator_index == p.relators.len()
                    let rel = get_relator(p2, relator_index, inverted);
                    assert(p2.relators[p.relators.len() as int] == r);

                    //  Show rel ≡ ε in p
                    if !inverted {
                        assert(rel == r);
                    } else {
                        assert(rel == inverse_word(r));
                        lemma_inverse_of_identity(p, r);
                    }

                    let prefix = w_start.subrange(0, position);
                    let suffix = w_start.subrange(position, w_start.len() as int);
                    assert(w_start =~= concat(prefix, suffix));
                    assert(w_mid =~= concat(concat(prefix, rel), suffix));

                    //  concat(prefix, rel) ≡ prefix
                    lemma_equiv_concat_right(p, prefix, rel, empty_word());
                    assert(concat(prefix, empty_word()) =~= prefix);
                    lemma_equiv_refl(p, prefix);
                    lemma_equiv_transitive(p,
                        concat(prefix, rel),
                        concat(prefix, empty_word()),
                        prefix,
                    );

                    //  w_mid ≡ w_start
                    lemma_equiv_concat_left(p,
                        concat(prefix, rel), prefix, suffix);
                    //  w_start ≡ w_mid (symmetric — w_mid is word_valid from step_preserves above)
                    lemma_equiv_symmetric(p, w_mid, w_start);
                }
            },
            DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                if relator_index < p.relators.len() {
                    assert(p2.relators[relator_index as int] == p.relators[relator_index as int]);
                    assert(get_relator(p2, relator_index, inverted) == get_relator(p, relator_index, inverted));
                    assert(apply_step(p, w_start, step) == Some(w_mid));
                    lemma_single_step_equiv(p, w_start, step, w_mid);
                } else {
                    //  Deleting the new relator: reverse of insert case
                    let rel = get_relator(p2, relator_index, inverted);
                    assert(p2.relators[p.relators.len() as int] == r);

                    let prefix = w_start.subrange(0, position);
                    let rlen = rel.len();
                    let suffix = w_start.subrange(position + rlen as int, w_start.len() as int);
                    assert(w_mid =~= concat(prefix, suffix));
                    assert(w_start.subrange(position, position + rlen as int) == rel);
                    assert(w_start =~= concat(concat(prefix, rel), suffix));

                    //  Show rel ≡ ε in p
                    if inverted {
                        assert(rel == inverse_word(r));
                        lemma_inverse_of_identity(p, r);
                    }

                    //  concat(prefix, rel) ≡ prefix
                    lemma_equiv_concat_right(p, prefix, rel, empty_word());
                    assert(concat(prefix, empty_word()) =~= prefix);
                    lemma_equiv_refl(p, prefix);
                    lemma_equiv_transitive(p,
                        concat(prefix, rel),
                        concat(prefix, empty_word()),
                        prefix,
                    );

                    //  w_start =~= concat(concat(prefix, rel), suffix) ≡ concat(prefix, suffix) = w_mid
                    lemma_equiv_concat_left(p,
                        concat(prefix, rel), prefix, suffix);
                }
            },
        }

        //  Chain: w_start ≡ w_mid ≡ w_end
        lemma_equiv_transitive(p, w_start, w_mid, w_end);
    }
}

///  T4: Removing a derivable relator preserves equivalence (forward direction).
///  If relators[idx] ≡ ε in remove_relator(p, idx), then equiv in p → equiv in remove_relator(p, idx).
pub proof fn lemma_remove_relator_forward(
    p: Presentation, idx: nat, w1: Word, w2: Word,
)
    requires
        idx < p.relators.len(),
        equiv_in_presentation(remove_relator(p, idx), p.relators[idx as int], empty_word()),
        equiv_in_presentation(p, w1, w2),
        presentation_valid(p),
        word_valid(w1, p.num_generators),
    ensures
        equiv_in_presentation(remove_relator(p, idx), w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_derivation_replace_removed_relator(p, idx, d.steps, w1, w2);
}

///  Helper: prove relator index correspondence for remove_relator.
///  For ri < idx: remove_relator(p, idx).relators[ri] == p.relators[ri].
///  For ri >= idx: remove_relator(p, idx).relators[ri] == p.relators[ri + 1].
proof fn lemma_remove_relator_index_map(p: Presentation, idx: nat, ri: nat)
    requires
        idx < p.relators.len(),
        ri < p.relators.len() - 1,
    ensures
        ri < idx ==> remove_relator(p, idx).relators[ri as int] == p.relators[ri as int],
        ri >= idx ==> remove_relator(p, idx).relators[ri as int] == p.relators[(ri + 1) as int],
{
    let rp = remove_relator(p, idx);
    let left = p.relators.subrange(0, idx as int);
    let right = p.relators.subrange(idx as int + 1, p.relators.len() as int);
    assert(rp.relators =~= left + right);
    if ri < idx {
        assert(rp.relators[ri as int] == left[ri as int]);
    } else {
        let offset = (ri - idx) as int;
        assert(rp.relators[ri as int] == right[offset]);
        assert(right[offset] == p.relators[idx as int + 1 + offset]);
    }
}

///  Core of T4 forward: replace uses of the removed relator in a derivation.
///  Mirrors lemma_derivation_replace_new_relator for the remove direction.
proof fn lemma_derivation_replace_removed_relator(
    p: Presentation, idx: nat,
    steps: Seq<DerivationStep>, w_start: Word, w_end: Word,
)
    requires
        idx < p.relators.len(),
        equiv_in_presentation(remove_relator(p, idx), p.relators[idx as int], empty_word()),
        derivation_produces(p, steps, w_start) == Some(w_end),
        presentation_valid(p),
        word_valid(w_start, p.num_generators),
    ensures
        equiv_in_presentation(remove_relator(p, idx), w_start, w_end),
    decreases steps.len(),
{
    reveal(presentation_valid);
    let p2 = remove_relator(p, idx);
    //  Prove presentation_valid(p2) — p2 has a subset of p's relators
    assert(presentation_valid(p2)) by {
        assert(p2.num_generators == p.num_generators);
        let left = p.relators.subrange(0, idx as int);
        let right = p.relators.subrange(idx as int + 1, p.relators.len() as int);
        assert(p2.relators =~= left + right);
        assert forall|i: int| 0 <= i < p2.relators.len()
            implies word_valid(p2.relators[i], p2.num_generators)
        by {
            if i < idx as int {
                assert(p2.relators[i] == p.relators[i]);
            } else {
                assert(p2.relators[i] == p.relators[i + 1]);
            }
        }
    }
    if steps.len() == 0 {
        assert(w_start == w_end);
        lemma_equiv_refl(p2, w_start);
    } else {
        let step = steps.first();
        let w_mid = apply_step(p, w_start, step).unwrap();
        let rest = steps.drop_first();

        //  Prove word_valid(w_mid) for recursive call and symmetric calls
        lemma_step_preserves_word_valid_pres(p, w_start, step, w_mid);

        //  Recursion: w_mid → w_end is equivalent in p2
        lemma_derivation_replace_removed_relator(p, idx, rest, w_mid, w_end);

        //  Now show w_start → w_mid is equivalent in p2
        match step {
            DerivationStep::FreeReduce { position } => {
                assert(apply_step(p2, w_start, step) == Some(w_mid));
                lemma_single_step_equiv(p2, w_start, step, w_mid);
            },
            DerivationStep::FreeExpand { position, symbol } => {
                assert(apply_step(p2, w_start, step) == Some(w_mid));
                lemma_single_step_equiv(p2, w_start, step, w_mid);
            },
            DerivationStep::RelatorInsert { position, relator_index, inverted } => {
                if relator_index < idx {
                    //  Relator at same index in p2
                    lemma_remove_relator_index_map(p, idx, relator_index);
                    let step2 = DerivationStep::RelatorInsert { position, relator_index, inverted };
                    assert(get_relator(p2, relator_index, inverted) == get_relator(p, relator_index, inverted));
                    assert(apply_step(p2, w_start, step2) == Some(w_mid));
                    lemma_single_step_equiv(p2, w_start, step2, w_mid);
                } else if relator_index > idx {
                    //  Relator shifted down by 1 in p2
                    let ri2 = (relator_index - 1) as nat;
                    lemma_remove_relator_index_map(p, idx, ri2);
                    assert(p2.relators[ri2 as int] == p.relators[relator_index as int]);
                    let step2 = DerivationStep::RelatorInsert { position, relator_index: ri2, inverted };
                    assert(get_relator(p2, ri2, inverted) == get_relator(p, relator_index, inverted));
                    assert(apply_step(p2, w_start, step2) == Some(w_mid));
                    lemma_single_step_equiv(p2, w_start, step2, w_mid);
                } else {
                    //  relator_index == idx: the removed relator
                    //  rel ≡ ε in p2 (from requires)
                    let rel = get_relator(p, relator_index, inverted);
                    assert(p.relators[idx as int] == p.relators[relator_index as int]);

                    //  Show rel ≡ ε in p2
                    if !inverted {
                        assert(rel == p.relators[idx as int]);
                    } else {
                        assert(rel == inverse_word(p.relators[idx as int]));
                        lemma_inverse_of_identity(p2, p.relators[idx as int]);
                    }

                    //  w_mid = prefix ++ rel ++ suffix, w_start = prefix ++ suffix
                    let prefix = w_start.subrange(0, position);
                    let suffix = w_start.subrange(position, w_start.len() as int);
                    assert(w_start =~= concat(prefix, suffix));
                    assert(w_mid =~= concat(concat(prefix, rel), suffix));

                    //  concat(prefix, rel) ≡ prefix
                    lemma_equiv_concat_right(p2, prefix, rel, empty_word());
                    assert(concat(prefix, empty_word()) =~= prefix);
                    lemma_equiv_refl(p2, prefix);
                    lemma_equiv_transitive(p2,
                        concat(prefix, rel),
                        concat(prefix, empty_word()),
                        prefix,
                    );

                    //  w_mid ≡ w_start
                    lemma_equiv_concat_left(p2,
                        concat(prefix, rel), prefix, suffix);
                    lemma_equiv_symmetric(p2, w_mid, w_start);
                }
            },
            DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                if relator_index < idx {
                    lemma_remove_relator_index_map(p, idx, relator_index);
                    let step2 = DerivationStep::RelatorDelete { position, relator_index, inverted };
                    assert(get_relator(p2, relator_index, inverted) == get_relator(p, relator_index, inverted));
                    assert(apply_step(p2, w_start, step2) == Some(w_mid));
                    lemma_single_step_equiv(p2, w_start, step2, w_mid);
                } else if relator_index > idx {
                    let ri2 = (relator_index - 1) as nat;
                    lemma_remove_relator_index_map(p, idx, ri2);
                    assert(p2.relators[ri2 as int] == p.relators[relator_index as int]);
                    let step2 = DerivationStep::RelatorDelete { position, relator_index: ri2, inverted };
                    assert(get_relator(p2, ri2, inverted) == get_relator(p, relator_index, inverted));
                    assert(apply_step(p2, w_start, step2) == Some(w_mid));
                    lemma_single_step_equiv(p2, w_start, step2, w_mid);
                } else {
                    //  relator_index == idx: deleting the removed relator
                    let rel = get_relator(p, relator_index, inverted);
                    assert(p.relators[idx as int] == p.relators[relator_index as int]);

                    let prefix = w_start.subrange(0, position);
                    let rlen = rel.len();
                    let suffix = w_start.subrange(position + rlen as int, w_start.len() as int);
                    assert(w_mid =~= concat(prefix, suffix));
                    assert(w_start.subrange(position, position + rlen as int) == rel);
                    assert(w_start =~= concat(concat(prefix, rel), suffix));

                    //  Show rel ≡ ε in p2
                    if inverted {
                        assert(rel == inverse_word(p.relators[idx as int]));
                        lemma_inverse_of_identity(p2, p.relators[idx as int]);
                    }

                    //  concat(prefix, rel) ≡ prefix
                    lemma_equiv_concat_right(p2, prefix, rel, empty_word());
                    assert(concat(prefix, empty_word()) =~= prefix);
                    lemma_equiv_refl(p2, prefix);
                    lemma_equiv_transitive(p2,
                        concat(prefix, rel),
                        concat(prefix, empty_word()),
                        prefix,
                    );

                    //  w_start ≡ w_mid
                    lemma_equiv_concat_left(p2,
                        concat(prefix, rel), prefix, suffix);
                }
            },
        }

        //  Chain: w_start ≡ w_mid ≡ w_end
        lemma_equiv_transitive(p2, w_start, w_mid, w_end);
    }
}

///  T1: Adding a generator preserves existing equivalences.
///  Old words (using generators 0..n-1) are still equivalent in the extended presentation.
pub proof fn lemma_add_generator_preserves(
    p: Presentation, defining_word: Word, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(add_generator_to_presentation(p, defining_word), w1, w2),
{
    let p2 = add_generator_to_presentation(p, defining_word);
    //  p2 has same relators as p (plus one more), and more generators
    //  A derivation in p uses relators 0..p.relators.len()-1
    //  These same relators exist in p2 at the same indices

    //  p2.relators.subrange(0, p.relators.len()) == p.relators
    assert(p2.relators.subrange(0, p.relators.len() as int) =~= p.relators);
    assert(p2.num_generators == p.num_generators + 1);
    //  extends_presentation requires same num_generators, but p2 has more
    //  So we can't use extends_presentation directly.
    //  Instead, prove step-by-step that derivation in p is valid in p2.
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_add_gen_derivation_valid(p, p2, defining_word, d.steps, w1, w2);
    let d2 = Derivation { steps: d.steps };
    assert(derivation_valid(p2, d2, w1, w2));
}

///  Helper: derivation steps valid in p are valid in add_generator(p, ...).
proof fn lemma_add_gen_derivation_valid(
    p: Presentation, p2: Presentation, defining_word: Word,
    steps: Seq<DerivationStep>, w_start: Word, w_end: Word,
)
    requires
        p2 == add_generator_to_presentation(p, defining_word),
        derivation_produces(p, steps, w_start) == Some(w_end),
    ensures
        derivation_produces(p2, steps, w_start) == Some(w_end),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let w_mid = apply_step(p, w_start, step).unwrap();

        //  Show this step is valid in p2
        match step {
            DerivationStep::FreeReduce { position } => {
                assert(apply_step(p2, w_start, step) == Some(w_mid));
            },
            DerivationStep::FreeExpand { position, symbol } => {
                assert(apply_step(p2, w_start, step) == Some(w_mid));
            },
            DerivationStep::RelatorInsert { position, relator_index, inverted } => {
                assert(relator_index < p.relators.len());
                assert(relator_index < p2.relators.len());
                assert(p2.relators[relator_index as int] == p.relators[relator_index as int]);
                assert(get_relator(p2, relator_index, inverted) == get_relator(p, relator_index, inverted));
                assert(apply_step(p2, w_start, step) == Some(w_mid));
            },
            DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                assert(relator_index < p.relators.len());
                assert(relator_index < p2.relators.len());
                assert(p2.relators[relator_index as int] == p.relators[relator_index as int]);
                assert(get_relator(p2, relator_index, inverted) == get_relator(p, relator_index, inverted));
                assert(apply_step(p2, w_start, step) == Some(w_mid));
            },
        }

        lemma_add_gen_derivation_valid(p, p2, defining_word, steps.drop_first(), w_mid, w_end);
    }
}

} //  verus!
