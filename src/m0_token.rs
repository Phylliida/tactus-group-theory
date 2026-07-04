// m0_token.rs — the M0 token layer, built on the crate's VERIFIED substrate.
//
// docs/m0-closure.md formalized by REUSE, not reinvention (Danielle's note 2026-07-04):
// the agent's thue.rs/m0.rs hand-rolled Word, free reduction, the Thue closure, and
// homomorphism transport — all of which are already verified here. Concretely:
//   * the Thue congruence of T̂ IS `equiv_in_presentation(token_pres, ·, ·)`
//     (a Thue rule lhs→rhs is the relator lhs·rhs⁻¹; RelatorInsert/Delete = subword replace);
//   * ψ IS a `HomomorphismData` into `free_group(4)`;
//   * M0-soundness (thue ⟹ ψ-equal) IS `lemma_hom_preserves_equiv` + the free-group bridge —
//     NO new closure/congruence lemmas needed (agent admits A3/A4/step_sound dissolve).
// This module lands the encoding + validity; soundness assembly is the immediate next step.
//
// Alphabet:  ⟨=Gen(0) ⟩=Gen(1) M=Gen(2) 1=Gen(3) X=Gen(4) 0=Gen(5)   (source, 6 gens)
// ψ target free_group(4):  ⟨=0 M=1 X=2 1=3   (⟩,0 are the two derived/eliminated letters)

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::{has_cancellation_at, reduce_at, reduces_one_step, reduces_in_steps,
    reduces_to, freely_equivalent, lemma_reduces_to_refl};
use crate::presentation::*;
use crate::presentation_lemmas::lemma_freely_equivalent_implies_equiv;
use crate::homomorphism::*;
use crate::higman_operations::{free_group, lemma_free_group_valid};

verus! {

// ── the nine T̂ relators (lhs·rhs⁻¹ over the 6-letter alphabet) ──────────────
// r1: X0 = M1     ⟹  X·0·1⁻¹·M⁻¹
// d1..d4: rotations of ⟨M1⟩ = ε      e1..e4: rotations of ⟨X0⟩ = ε   (rhs = ε)

pub open spec fn tok_relators() -> Seq<Word> {
    seq![
        // r1: X 0 1⁻¹ M⁻¹
        seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2)],
        // d1: ⟨ M 1 ⟩
        seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)],
        // d2: M 1 ⟩ ⟨
        seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0)],
        // d3: 1 ⟩ ⟨ M
        seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2)],
        // d4: ⟩ ⟨ M 1
        seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3)],
        // e1: ⟨ X 0 ⟩
        seq![Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1)],
        // e2: X 0 ⟩ ⟨
        seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0)],
        // e3: 0 ⟩ ⟨ X
        seq![Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4)],
        // e4: ⟩ ⟨ X 0
        seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5)],
    ]
}

pub open spec fn token_pres() -> Presentation {
    Presentation { num_generators: 6, relators: tok_relators() }
}

pub proof fn lemma_token_pres_valid()
    ensures presentation_valid(token_pres())
{
    reveal(presentation_valid);
    assert forall|i: int| 0 <= i < token_pres().relators.len()
        implies word_valid(#[trigger] token_pres().relators[i], 6) by {
        // each relator is a length-4 word over Gen/Inv with index < 6
        assert(word_valid(token_pres().relators[i], 6));
    }
}

// ── ψ : token_pres → free_group(4) ─────────────────────────────────────────
//  ⟨(0)↦⟨ ; ⟩(1)↦1⁻¹M⁻¹⟨⁻¹ ; M(2)↦M ; 1(3)↦1 ; X(4)↦X ; 0(5)↦X⁻¹M1
//  target indices: ⟨=0, M=1, X=2, 1=3

pub open spec fn psi_images() -> Seq<Word> {
    seq![
        seq![Symbol::Gen(0)],                                   // ⟨
        seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)],   // ⟩ ↦ 1⁻¹M⁻¹⟨⁻¹
        seq![Symbol::Gen(1)],                                   // M
        seq![Symbol::Gen(3)],                                   // 1
        seq![Symbol::Gen(2)],                                   // X
        seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3)],   // 0 ↦ X⁻¹M1
    ]
}

pub open spec fn psi_hom() -> HomomorphismData {
    HomomorphismData {
        source: token_pres(),
        target: free_group(4),
        generator_images: psi_images(),
    }
}

// Sanity: the two structural facts of is_valid_homomorphism that need no relator work,
// isolated so the shakeout localizes any encoding error before the 9 rule computations.
pub proof fn lemma_psi_shape()
    ensures
        psi_hom().generator_images.len() == psi_hom().source.num_generators,
        presentation_valid(psi_hom().source),
        presentation_valid(psi_hom().target),
        forall|i: int| 0 <= i < psi_hom().generator_images.len() ==>
            word_valid(#[trigger] psi_hom().generator_images[i], 4),
{
    lemma_token_pres_valid();
    lemma_free_group_valid(4);
    assert forall|i: int| 0 <= i < psi_hom().generator_images.len()
        implies word_valid(#[trigger] psi_hom().generator_images[i], 4) by {
        assert(word_valid(psi_hom().generator_images[i], 4));
    }
}

// ── rule-soundness: the path (SHAKEOUT FINDING 2026-07-04) ──────────────────
// Each of the 9 relators r: ψ(r) freely reduces to ε ⟹ equiv_in_presentation(
// free_group(4), apply_hom(psi_hom, r), ε), the relator condition of
// is_valid_homomorphism.  Reusable chain: `lemma_reduces_to_normal_form` +
// `lemma_freely_equivalent_implies_equiv` (both verified here).  BUT the
// `normal_form(ψ(r)) == ε` step must NOT go through `by (compute)`:
//   FINDING — `assert(normal_form(img) =~= empty_word()) by (compute)` fails with
//   "assert_by_compute exceeded maximum recursion depth" (symbol.rs:18) — the
//   `reduce_n_steps ∘ apply_hom` recursion is deeper than the compute engine's cap.
// Correct route (next session, compile-iterate): unfold `apply_hom` on each concrete
// relator to its 6-symbol image, then witness `reduces_to(img, ε)` by an EXPLICIT
// chain of `reduce_at` steps (the free cancellations, e.g. d1: Gen0 Gen1 Gen3 Inv3
// Inv1 Inv0 → reduce@2 → reduce@1 → reduce@0 → ε) via `lemma_reduces_one_step_equiv`
// / a hand `reduces_in_steps` witness — 3 cancellations per relator, mechanical.
// Then: `lemma_psi_valid` (is_valid_homomorphism) and `lemma_m0_soundness`
// (= `lemma_hom_preserves_equiv` + `lemma_free_group_equiv_freely_equivalent`).

// ── reduction-chain helper: 3 explicit cancellations w0→w1→w2→ε ────────────
proof fn reduces3(w0: Word, i0: int, w1: Word, i1: int, w2: Word, i2: int)
    requires
        has_cancellation_at(w0, i0), w1 == reduce_at(w0, i0),
        has_cancellation_at(w1, i1), w2 == reduce_at(w1, i1),
        has_cancellation_at(w2, i2), reduce_at(w2, i2) == empty_word(),
    ensures reduces_to(w0, empty_word())
{
    assert(reduces_one_step(w2, empty_word())) by {
        assert(has_cancellation_at(w2, i2) && empty_word() == reduce_at(w2, i2));
    }
    assert(reduces_in_steps(w2, empty_word(), 1)) by {
        assert(reduces_one_step(w2, empty_word())
            && reduces_in_steps(empty_word(), empty_word(), 0));
    }
    assert(reduces_one_step(w1, w2)) by {
        assert(has_cancellation_at(w1, i1) && w2 == reduce_at(w1, i1));
    }
    assert(reduces_in_steps(w1, empty_word(), 2)) by {
        assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, empty_word(), 1));
    }
    assert(reduces_one_step(w0, w1)) by {
        assert(has_cancellation_at(w0, i0) && w1 == reduce_at(w0, i0));
    }
    assert(reduces_in_steps(w0, empty_word(), 3)) by {
        assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, empty_word(), 2));
    }
    assert(reduces_to(w0, empty_word())) by {
        assert(reduces_in_steps(w0, empty_word(), 3));
    }
}

// 4-step variant for the e-family (length-8 images).
proof fn reduces4(w0: Word, i0: int, w1: Word, i1: int, w2: Word, i2: int, w3: Word, i3: int)
    requires
        has_cancellation_at(w0, i0), w1 == reduce_at(w0, i0),
        has_cancellation_at(w1, i1), w2 == reduce_at(w1, i1),
        has_cancellation_at(w2, i2), w3 == reduce_at(w2, i2),
        has_cancellation_at(w3, i3), reduce_at(w3, i3) == empty_word(),
    ensures reduces_to(w0, empty_word())
{
    assert(reduces_one_step(w3, empty_word())) by {
        assert(has_cancellation_at(w3, i3) && empty_word() == reduce_at(w3, i3));
    }
    assert(reduces_in_steps(w3, empty_word(), 1)) by {
        assert(reduces_one_step(w3, empty_word())
            && reduces_in_steps(empty_word(), empty_word(), 0));
    }
    assert(reduces_one_step(w2, w3)) by {
        assert(has_cancellation_at(w2, i2) && w3 == reduce_at(w2, i2));
    }
    assert(reduces_in_steps(w2, empty_word(), 2)) by {
        assert(reduces_one_step(w2, w3) && reduces_in_steps(w3, empty_word(), 1));
    }
    assert(reduces_one_step(w1, w2)) by {
        assert(has_cancellation_at(w1, i1) && w2 == reduce_at(w1, i1));
    }
    assert(reduces_in_steps(w1, empty_word(), 3)) by {
        assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, empty_word(), 2));
    }
    assert(reduces_one_step(w0, w1)) by {
        assert(has_cancellation_at(w0, i0) && w1 == reduce_at(w0, i0));
    }
    assert(reduces_in_steps(w0, empty_word(), 4)) by {
        assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, empty_word(), 3));
    }
    assert(reduces_to(w0, empty_word())) by {
        assert(reduces_in_steps(w0, empty_word(), 4));
    }
}

// close the relator condition once reduces_to(img, ε) is in hand.
proof fn relator_trivial_from_reduces(img: Word)
    requires reduces_to(img, empty_word()), word_valid(img, 4),
    ensures equiv_in_presentation(free_group(4), img, empty_word())
{
    lemma_reduces_to_refl(empty_word());
    assert(freely_equivalent(img, empty_word())) by {
        assert(reduces_to(img, empty_word()) && reduces_to(empty_word(), empty_word()));
    }
    lemma_free_group_valid(4);
    assert(word_valid(empty_word(), 4));
    lemma_freely_equivalent_implies_equiv(free_group(4), img, empty_word());
}

// ── d1 END-TO-END (template for the other length-6 relators) ────────────────
pub proof fn lemma_rel_d1()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(),
            seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)]),
        empty_word())
{
    let img = apply_hom(psi_hom(),
        seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)]);
    // ψ(⟨M1⟩) = ⟨ M 1 1⁻¹M⁻¹⟨⁻¹   (full literals — compute doesn't see through `let`)
    let w0: Word = seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Gen(3),
                        Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)];
    let w1: Word = seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(1), Symbol::Inv(0)];
    let w2: Word = seq![Symbol::Gen(0), Symbol::Inv(0)];
    assert(apply_hom(psi_hom(),
        seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)])
        =~= seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Gen(3),
                 Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 2));
    assert(w1 == reduce_at(w0, 2)) by { assert(w1 =~= reduce_at(w0, 2)); }
    assert(has_cancellation_at(w1, 1));
    assert(w2 == reduce_at(w1, 1)) by { assert(w2 =~= reduce_at(w1, 1)); }
    assert(has_cancellation_at(w2, 0));
    assert(reduce_at(w2, 0) == empty_word()) by { assert(reduce_at(w2, 0) =~= empty_word()); }
    reduces3(w0, 2, w1, 1, w2, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

// ── the other 8 relators (GENERATED from ψ by tools, no hand-transcription) ──
pub proof fn lemma_rel_r1()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2)]);
    let w0: Word = seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1)];
    let w1: Word = seq![Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1)];
    let w2: Word = seq![Symbol::Gen(1), Symbol::Inv(1)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2)]) =~= seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 0));
    assert(w1 == reduce_at(w0, 0)) by { assert(w1 =~= reduce_at(w0, 0)); }
    assert(has_cancellation_at(w1, 1));
    assert(w2 == reduce_at(w1, 1)) by { assert(w2 =~= reduce_at(w1, 1)); }
    assert(has_cancellation_at(w2, 0));
    assert(reduce_at(w2, 0) == empty_word()) by { assert(reduce_at(w2, 0) =~= empty_word()); }
    reduces3(w0, 0, w1, 1, w2, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

pub proof fn lemma_rel_d2()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0)]);
    let w0: Word = seq![Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0)];
    let w1: Word = seq![Symbol::Gen(1), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0)];
    let w2: Word = seq![Symbol::Inv(0), Symbol::Gen(0)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0)]) =~= seq![Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 1));
    assert(w1 == reduce_at(w0, 1)) by { assert(w1 =~= reduce_at(w0, 1)); }
    assert(has_cancellation_at(w1, 0));
    assert(w2 == reduce_at(w1, 0)) by { assert(w2 =~= reduce_at(w1, 0)); }
    assert(has_cancellation_at(w2, 0));
    assert(reduce_at(w2, 0) == empty_word()) by { assert(reduce_at(w2, 0) =~= empty_word()); }
    reduces3(w0, 1, w1, 0, w2, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

pub proof fn lemma_rel_d3()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2)]);
    let w0: Word = seq![Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(1)];
    let w1: Word = seq![Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(1)];
    let w2: Word = seq![Symbol::Inv(1), Symbol::Gen(1)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2)]) =~= seq![Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(1)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 0));
    assert(w1 == reduce_at(w0, 0)) by { assert(w1 =~= reduce_at(w0, 0)); }
    assert(has_cancellation_at(w1, 1));
    assert(w2 == reduce_at(w1, 1)) by { assert(w2 =~= reduce_at(w1, 1)); }
    assert(has_cancellation_at(w2, 0));
    assert(reduce_at(w2, 0) == empty_word()) by { assert(reduce_at(w2, 0) =~= empty_word()); }
    reduces3(w0, 0, w1, 1, w2, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

pub proof fn lemma_rel_d4()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3)]);
    let w0: Word = seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(1), Symbol::Gen(3)];
    let w1: Word = seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Gen(1), Symbol::Gen(3)];
    let w2: Word = seq![Symbol::Inv(3), Symbol::Gen(3)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3)]) =~= seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(1), Symbol::Gen(3)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 2));
    assert(w1 == reduce_at(w0, 2)) by { assert(w1 =~= reduce_at(w0, 2)); }
    assert(has_cancellation_at(w1, 1));
    assert(w2 == reduce_at(w1, 1)) by { assert(w2 =~= reduce_at(w1, 1)); }
    assert(has_cancellation_at(w2, 0));
    assert(reduce_at(w2, 0) == empty_word()) by { assert(reduce_at(w2, 0) =~= empty_word()); }
    reduces3(w0, 2, w1, 1, w2, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

pub proof fn lemma_rel_e1()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1)]);
    let w0: Word = seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)];
    let w1: Word = seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)];
    let w2: Word = seq![Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(1), Symbol::Inv(0)];
    let w3: Word = seq![Symbol::Gen(0), Symbol::Inv(0)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1)]) =~= seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 1));
    assert(w1 == reduce_at(w0, 1)) by { assert(w1 =~= reduce_at(w0, 1)); }
    assert(has_cancellation_at(w1, 2));
    assert(w2 == reduce_at(w1, 2)) by { assert(w2 =~= reduce_at(w1, 2)); }
    assert(has_cancellation_at(w2, 1));
    assert(w3 == reduce_at(w2, 1)) by { assert(w3 =~= reduce_at(w2, 1)); }
    assert(has_cancellation_at(w3, 0));
    assert(reduce_at(w3, 0) == empty_word()) by { assert(reduce_at(w3, 0) =~= empty_word()); }
    reduces4(w0, 1, w1, 2, w2, 1, w3, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

pub proof fn lemma_rel_e2()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0)]);
    let w0: Word = seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0)];
    let w1: Word = seq![Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0)];
    let w2: Word = seq![Symbol::Gen(1), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0)];
    let w3: Word = seq![Symbol::Inv(0), Symbol::Gen(0)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0)]) =~= seq![Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 0));
    assert(w1 == reduce_at(w0, 0)) by { assert(w1 =~= reduce_at(w0, 0)); }
    assert(has_cancellation_at(w1, 1));
    assert(w2 == reduce_at(w1, 1)) by { assert(w2 =~= reduce_at(w1, 1)); }
    assert(has_cancellation_at(w2, 0));
    assert(w3 == reduce_at(w2, 0)) by { assert(w3 =~= reduce_at(w2, 0)); }
    assert(has_cancellation_at(w3, 0));
    assert(reduce_at(w3, 0) == empty_word()) by { assert(reduce_at(w3, 0) =~= empty_word()); }
    reduces4(w0, 0, w1, 1, w2, 0, w3, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

pub proof fn lemma_rel_e3()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4)]);
    let w0: Word = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2)];
    let w1: Word = seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2)];
    let w2: Word = seq![Symbol::Inv(2), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2)];
    let w3: Word = seq![Symbol::Inv(2), Symbol::Gen(2)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4)]) =~= seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3), Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 2));
    assert(w1 == reduce_at(w0, 2)) by { assert(w1 =~= reduce_at(w0, 2)); }
    assert(has_cancellation_at(w1, 1));
    assert(w2 == reduce_at(w1, 1)) by { assert(w2 =~= reduce_at(w1, 1)); }
    assert(has_cancellation_at(w2, 1));
    assert(w3 == reduce_at(w2, 1)) by { assert(w3 =~= reduce_at(w2, 1)); }
    assert(has_cancellation_at(w3, 0));
    assert(reduce_at(w3, 0) == empty_word()) by { assert(reduce_at(w3, 0) =~= empty_word()); }
    reduces4(w0, 2, w1, 1, w2, 1, w3, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}

pub proof fn lemma_rel_e4()
    ensures equiv_in_presentation(free_group(4),
        apply_hom(psi_hom(), seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5)]), empty_word())
{
    let img = apply_hom(psi_hom(), seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5)]);
    let w0: Word = seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3)];
    let w1: Word = seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3)];
    let w2: Word = seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Gen(1), Symbol::Gen(3)];
    let w3: Word = seq![Symbol::Inv(3), Symbol::Gen(3)];
    assert(apply_hom(psi_hom(), seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5)]) =~= seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2), Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3)]) by (compute);
    assert(img =~= w0);
    assert(has_cancellation_at(w0, 2));
    assert(w1 == reduce_at(w0, 2)) by { assert(w1 =~= reduce_at(w0, 2)); }
    assert(has_cancellation_at(w1, 2));
    assert(w2 == reduce_at(w1, 2)) by { assert(w2 =~= reduce_at(w1, 2)); }
    assert(has_cancellation_at(w2, 1));
    assert(w3 == reduce_at(w2, 1)) by { assert(w3 =~= reduce_at(w2, 1)); }
    assert(has_cancellation_at(w3, 0));
    assert(reduce_at(w3, 0) == empty_word()) by { assert(reduce_at(w3, 0) =~= empty_word()); }
    reduces4(w0, 2, w1, 2, w2, 1, w3, 0);
    assert(word_valid(w0, 4));
    relator_trivial_from_reduces(w0);
    assert(img == w0);
}


} // verus!
