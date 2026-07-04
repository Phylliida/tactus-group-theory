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
use crate::presentation_lemmas::*;
use crate::homomorphism::*;
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::free_word_problem::lemma_free_group_equiv_freely_equivalent;

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


// ── is_valid_homomorphism: shape (lemma_psi_shape) + the 9 relator conditions ──
pub proof fn lemma_psi_valid()
    ensures is_valid_homomorphism(psi_hom())
{
    lemma_psi_shape();
    assert forall|i: int| 0 <= i < token_pres().relators.len() implies
        equiv_in_presentation(free_group(4),
            apply_hom(psi_hom(), #[trigger] token_pres().relators[i]), empty_word()) by {
        if i == 0 { assert(token_pres().relators[0] =~= seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2)]); lemma_rel_r1(); }
        if i == 1 { assert(token_pres().relators[1] =~= seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)]); lemma_rel_d1(); }
        if i == 2 { assert(token_pres().relators[2] =~= seq![Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0)]); lemma_rel_d2(); }
        if i == 3 { assert(token_pres().relators[3] =~= seq![Symbol::Gen(3), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2)]); lemma_rel_d3(); }
        if i == 4 { assert(token_pres().relators[4] =~= seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3)]); lemma_rel_d4(); }
        if i == 5 { assert(token_pres().relators[5] =~= seq![Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1)]); lemma_rel_e1(); }
        if i == 6 { assert(token_pres().relators[6] =~= seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0)]); lemma_rel_e2(); }
        if i == 7 { assert(token_pres().relators[7] =~= seq![Symbol::Gen(5), Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4)]); lemma_rel_e3(); }
        if i == 8 { assert(token_pres().relators[8] =~= seq![Symbol::Gen(1), Symbol::Gen(0), Symbol::Gen(4), Symbol::Gen(5)]); lemma_rel_e4(); }
    }
}

// ── M0-soundness: thue ⟹ ψ-equal, by REUSE (the agent's A3/A4/step_sound) ──
pub proof fn lemma_m0_soundness(u: Word, v: Word)
    requires equiv_in_presentation(token_pres(), u, v)
    ensures freely_equivalent(apply_hom(psi_hom(), u), apply_hom(psi_hom(), v))
{
    lemma_psi_valid();
    lemma_hom_preserves_equiv(psi_hom(), u, v);
    lemma_free_group_equiv_freely_equivalent(4,
        apply_hom(psi_hom(), u), apply_hom(psi_hom(), v));
}

// ═══════════════════════════════════════════════════════════════════════════
// COMPLETENESS (A5+A6 dissolve): ψ is FAITHFUL via a RETRACTION φ: free_group(4)
// → token_pres with φ∘ψ ≡ id.  Mirror of miller_collapse_inject's
// lemma_collapse_injective (§54 "mutually-inverse homs ⟹ iso, no Britton-peel").
// This gives  G_T ≅ free_group(4)  — the token quotient is FREE, the meaningful
// M0 content — WITHOUT confluence (A5) or the scar induction (A6): both were
// artifacts of the Thue-rewriting framing; the group-iso framing needs neither.
//   φ: free_group(4) gens (LAng=0,M=1,X=2,One=3) -> token_pres gens (LAng=0,M=2,X=4,One=3)
// ═══════════════════════════════════════════════════════════════════════════

pub open spec fn phi_images() -> Seq<Word> {
    seq![ seq![Symbol::Gen(0)],   // LAng -> LAng
          seq![Symbol::Gen(2)],   // M -> M
          seq![Symbol::Gen(4)],   // X -> X
          seq![Symbol::Gen(3)] ]  // One -> One
}

pub open spec fn phi_hom() -> HomomorphismData {
    HomomorphismData {
        source: free_group(4),
        target: token_pres(),
        generator_images: phi_images(),
    }
}

pub proof fn lemma_phi_valid()
    ensures is_valid_homomorphism(phi_hom())
{
    reveal(presentation_valid);
    lemma_free_group_valid(4);
    lemma_token_pres_valid();
    assert(free_group(4).relators.len() == 0);
    assert forall|i: int| 0 <= i < phi_hom().generator_images.len()
        implies word_valid(#[trigger] phi_hom().generator_images[i], 6) by {
        assert(word_valid(phi_hom().generator_images[i], 6));
    }
}


// reduces_to a NONEMPTY target via 3 explicit cancellations (for the per-gen identities).
proof fn reduces3_to(w0: Word, i0: int, w1: Word, i1: int, w2: Word, i2: int, w3: Word)
    requires
        has_cancellation_at(w0, i0), w1 == reduce_at(w0, i0),
        has_cancellation_at(w1, i1), w2 == reduce_at(w1, i1),
        has_cancellation_at(w2, i2), w3 == reduce_at(w2, i2),
    ensures reduces_to(w0, w3)
{
    assert(reduces_one_step(w2, w3)) by { assert(has_cancellation_at(w2, i2) && w3 == reduce_at(w2, i2)); }
    assert(reduces_in_steps(w2, w3, 1)) by { assert(reduces_one_step(w2, w3) && reduces_in_steps(w3, w3, 0)); }
    assert(reduces_one_step(w1, w2)) by { assert(has_cancellation_at(w1, i1) && w2 == reduce_at(w1, i1)); }
    assert(reduces_in_steps(w1, w3, 2)) by { assert(reduces_one_step(w1, w2) && reduces_in_steps(w2, w3, 1)); }
    assert(reduces_one_step(w0, w1)) by { assert(has_cancellation_at(w0, i0) && w1 == reduce_at(w0, i0)); }
    assert(reduces_in_steps(w0, w3, 3)) by { assert(reduces_one_step(w0, w1) && reduces_in_steps(w1, w3, 2)); }
    assert(reduces_to(w0, w3)) by { assert(reduces_in_steps(w0, w3, 3)); }
}

pub proof fn lemma_gen5_id()
    ensures equiv_in_presentation(token_pres(), seq![Symbol::Inv(4), Symbol::Gen(2), Symbol::Gen(3)], seq![Symbol::Gen(5)])
{
    let p = token_pres();
    let pre: Word = seq![Symbol::Inv(4)]; let suf: Word = seq![Symbol::Gen(2), Symbol::Gen(3)];
    let rr: Word = seq![Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2)]; let lhs: Word = seq![Symbol::Inv(4), Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2), Symbol::Gen(2), Symbol::Gen(3)];
    let prefsuf: Word = seq![Symbol::Inv(4), Symbol::Gen(2), Symbol::Gen(3)]; let tgt: Word = seq![Symbol::Gen(5)];
    lemma_token_pres_valid();
    assert(p.relators[0] =~= rr);
    lemma_relator_is_identity(p, 0);
    lemma_equiv_refl(p, pre); lemma_equiv_refl(p, suf);
    lemma_equiv_concat(p, pre, pre, rr, empty_word());
    assert(concat(pre, empty_word()) =~= pre);
    lemma_equiv_concat(p, concat(pre, rr), pre, suf, suf);
    assert(lhs =~= concat(concat(pre, rr), suf));
    assert(concat(pre, suf) =~= prefsuf);
    let w0: Word = seq![Symbol::Inv(4), Symbol::Gen(4), Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2), Symbol::Gen(2), Symbol::Gen(3)];
    let w1: Word = seq![Symbol::Gen(5), Symbol::Inv(3), Symbol::Inv(2), Symbol::Gen(2), Symbol::Gen(3)];
    let w2: Word = seq![Symbol::Gen(5), Symbol::Inv(3), Symbol::Gen(3)];
    assert(has_cancellation_at(w0, 0));
    assert(w1 == reduce_at(w0, 0)) by { assert(w1 =~= reduce_at(w0, 0)); }
    assert(has_cancellation_at(w1, 2));
    assert(w2 == reduce_at(w1, 2)) by { assert(w2 =~= reduce_at(w1, 2)); }
    assert(has_cancellation_at(w2, 1));
    assert(tgt == reduce_at(w2, 1)) by { assert(tgt =~= reduce_at(w2, 1)); }
    reduces3_to(w0, 0, w1, 2, w2, 1, tgt);
    assert(w0 =~= lhs);
    lemma_reduces_to_equiv(p, lhs, tgt);
    assert(word_valid(lhs, 6));
    lemma_equiv_symmetric(p, lhs, prefsuf);
    lemma_equiv_transitive(p, prefsuf, lhs, tgt);
}

pub proof fn lemma_gen1_id()
    ensures equiv_in_presentation(token_pres(), seq![Symbol::Inv(3), Symbol::Inv(2), Symbol::Inv(0)], seq![Symbol::Gen(1)])
{
    let p = token_pres();
    let pre: Word = seq![Symbol::Inv(3), Symbol::Inv(2), Symbol::Inv(0)]; let suf: Word = seq![];
    let rr: Word = seq![Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)]; let lhs: Word = seq![Symbol::Inv(3), Symbol::Inv(2), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)];
    let prefsuf: Word = seq![Symbol::Inv(3), Symbol::Inv(2), Symbol::Inv(0)]; let tgt: Word = seq![Symbol::Gen(1)];
    lemma_token_pres_valid();
    assert(p.relators[1] =~= rr);
    lemma_relator_is_identity(p, 1);
    lemma_equiv_refl(p, pre); lemma_equiv_refl(p, suf);
    lemma_equiv_concat(p, pre, pre, rr, empty_word());
    assert(concat(pre, empty_word()) =~= pre);
    lemma_equiv_concat(p, concat(pre, rr), pre, suf, suf);
    assert(lhs =~= concat(concat(pre, rr), suf));
    assert(concat(pre, suf) =~= prefsuf);
    let w0: Word = seq![Symbol::Inv(3), Symbol::Inv(2), Symbol::Inv(0), Symbol::Gen(0), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)];
    let w1: Word = seq![Symbol::Inv(3), Symbol::Inv(2), Symbol::Gen(2), Symbol::Gen(3), Symbol::Gen(1)];
    let w2: Word = seq![Symbol::Inv(3), Symbol::Gen(3), Symbol::Gen(1)];
    assert(has_cancellation_at(w0, 2));
    assert(w1 == reduce_at(w0, 2)) by { assert(w1 =~= reduce_at(w0, 2)); }
    assert(has_cancellation_at(w1, 1));
    assert(w2 == reduce_at(w1, 1)) by { assert(w2 =~= reduce_at(w1, 1)); }
    assert(has_cancellation_at(w2, 0));
    assert(tgt == reduce_at(w2, 0)) by { assert(tgt =~= reduce_at(w2, 0)); }
    reduces3_to(w0, 2, w1, 1, w2, 0, tgt);
    assert(w0 =~= lhs);
    lemma_reduces_to_equiv(p, lhs, tgt);
    assert(word_valid(lhs, 6));
    lemma_equiv_symmetric(p, lhs, prefsuf);
    lemma_equiv_transitive(p, prefsuf, lhs, tgt);
}


// ── wrap-identity building block: φ∘ψ ≡ id on each generator ──
pub proof fn lemma_gen_wrap(g: int)
    requires 0 <= g < 6
    ensures equiv_in_presentation(token_pres(),
        apply_hom(phi_hom(), psi_images()[g]), seq![Symbol::Gen(g as nat)])
{
    let p = token_pres(); lemma_token_pres_valid();
    if g == 0 {
        assert(psi_images()[0] =~= seq![Symbol::Gen(0)]);
        assert(apply_hom(phi_hom(), seq![Symbol::Gen(0)]) =~= seq![Symbol::Gen(0)]) by (compute);
        lemma_equiv_refl(p, seq![Symbol::Gen(0)]);
        assert(seq![Symbol::Gen(g as nat)] =~= seq![Symbol::Gen(0)]);
    }
    else if g == 1 {
        assert(psi_images()[1] =~= seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)]);
        assert(apply_hom(phi_hom(), seq![Symbol::Inv(3), Symbol::Inv(1), Symbol::Inv(0)]) =~= seq![Symbol::Inv(3), Symbol::Inv(2), Symbol::Inv(0)]) by (compute);
        lemma_gen1_id();
        assert(seq![Symbol::Gen(g as nat)] =~= seq![Symbol::Gen(1)]);
    }
    else if g == 2 {
        assert(psi_images()[2] =~= seq![Symbol::Gen(1)]);
        assert(apply_hom(phi_hom(), seq![Symbol::Gen(1)]) =~= seq![Symbol::Gen(2)]) by (compute);
        lemma_equiv_refl(p, seq![Symbol::Gen(2)]);
        assert(seq![Symbol::Gen(g as nat)] =~= seq![Symbol::Gen(2)]);
    }
    else if g == 3 {
        assert(psi_images()[3] =~= seq![Symbol::Gen(3)]);
        assert(apply_hom(phi_hom(), seq![Symbol::Gen(3)]) =~= seq![Symbol::Gen(3)]) by (compute);
        lemma_equiv_refl(p, seq![Symbol::Gen(3)]);
        assert(seq![Symbol::Gen(g as nat)] =~= seq![Symbol::Gen(3)]);
    }
    else if g == 4 {
        assert(psi_images()[4] =~= seq![Symbol::Gen(2)]);
        assert(apply_hom(phi_hom(), seq![Symbol::Gen(2)]) =~= seq![Symbol::Gen(4)]) by (compute);
        lemma_equiv_refl(p, seq![Symbol::Gen(4)]);
        assert(seq![Symbol::Gen(g as nat)] =~= seq![Symbol::Gen(4)]);
    }
    else {
        assert(psi_images()[5] =~= seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3)]);
        assert(apply_hom(phi_hom(), seq![Symbol::Inv(2), Symbol::Gen(1), Symbol::Gen(3)]) =~= seq![Symbol::Inv(4), Symbol::Gen(2), Symbol::Gen(3)]) by (compute);
        lemma_gen5_id();
        assert(seq![Symbol::Gen(g as nat)] =~= seq![Symbol::Gen(5)]);
    }
}


// ── per-symbol wrap: φ(ψ(s)) ≡ [s] (Gen via gen_wrap; Inv via inverse) ──
pub proof fn lemma_sym_wrap(s: Symbol)
    requires generator_index(s) < 6
    ensures equiv_in_presentation(token_pres(),
        apply_hom(phi_hom(), apply_hom_symbol(psi_hom(), s)), seq![s])
{
    let p = token_pres(); lemma_token_pres_valid(); lemma_phi_valid(); lemma_psi_shape();
    match s {
        Symbol::Gen(g) => {
            lemma_gen_wrap(g as int);
            assert(apply_hom_symbol(psi_hom(), Symbol::Gen(g)) == psi_images()[g as int]);
            assert(seq![s] =~= seq![Symbol::Gen(g)]);
        }
        Symbol::Inv(g) => {
            lemma_gen_wrap(g as int);
            assert(apply_hom_symbol(psi_hom(), Symbol::Inv(g)) == inverse_word(psi_images()[g as int]));
            lemma_hom_respects_inverse(phi_hom(), psi_images()[g as int]);
            lemma_apply_hom_word_valid(phi_hom(), psi_images()[g as int]);
            crate::higman_consequences::lemma_equiv_inverse(p, apply_hom(phi_hom(), psi_images()[g as int]), seq![Symbol::Gen(g)]);
            lemma_inverse_singleton(Symbol::Gen(g));
            assert(seq![Symbol::Gen(g)] =~= Seq::new(1, |_i: int| Symbol::Gen(g)));
            assert(Seq::new(1, |_i: int| inverse_symbol(Symbol::Gen(g))) =~= seq![Symbol::Inv(g)]);
            assert(inverse_word(seq![Symbol::Gen(g)]) =~= seq![Symbol::Inv(g)]);
            assert(seq![s] =~= seq![Symbol::Inv(g)]);
        }
    }
}

// ── wrap-identity: φ(ψ(w)) ≡ w for all valid w (induction) ──
pub proof fn lemma_wrap(w: Word)
    requires word_valid(w, 6)
    ensures equiv_in_presentation(token_pres(), apply_hom(phi_hom(), apply_hom(psi_hom(), w)), w)
    decreases w.len()
{
    let p = token_pres(); lemma_token_pres_valid(); lemma_phi_valid();
    if w.len() == 0 {
        assert(apply_hom(psi_hom(), w) =~= empty_word());
        assert(apply_hom(phi_hom(), apply_hom(psi_hom(), w)) =~= empty_word());
        assert(w =~= empty_word());
        lemma_equiv_refl(p, w);
    } else {
        let s = w.first(); let rest = w.drop_first();
        assert(symbol_valid(s, 6)) by { assert(w[0] == s); }
        assert(word_valid(rest, 6)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], 6) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        assert(apply_hom(psi_hom(), w)
            =~= concat(apply_hom_symbol(psi_hom(), s), apply_hom(psi_hom(), rest)));
        lemma_hom_respects_concat(phi_hom(), apply_hom_symbol(psi_hom(), s), apply_hom(psi_hom(), rest));
        lemma_sym_wrap(s);
        lemma_wrap(rest);
        lemma_equiv_concat(p, apply_hom(phi_hom(), apply_hom_symbol(psi_hom(), s)), seq![s],
                              apply_hom(phi_hom(), apply_hom(psi_hom(), rest)), rest);
        assert(concat(seq![s], rest) =~= w);
    }
}

// ── ψ FAITHFUL: freely_equivalent(ψu,ψv) ⟹ u ≡ v  (the completeness half) ──
pub proof fn lemma_psi_faithful(u: Word, v: Word)
    requires
        word_valid(u, 6), word_valid(v, 6),
        freely_equivalent(apply_hom(psi_hom(), u), apply_hom(psi_hom(), v)),
    ensures equiv_in_presentation(token_pres(), u, v)
{
    let p = token_pres(); lemma_token_pres_valid(); lemma_phi_valid(); lemma_psi_valid();
    lemma_free_group_valid(4); lemma_psi_shape();
    lemma_apply_hom_word_valid(psi_hom(), u);
    lemma_apply_hom_word_valid(psi_hom(), v);
    lemma_freely_equivalent_implies_equiv(free_group(4),
        apply_hom(psi_hom(), u), apply_hom(psi_hom(), v));
    lemma_hom_preserves_equiv(phi_hom(), apply_hom(psi_hom(), u), apply_hom(psi_hom(), v));
    lemma_wrap(u); lemma_wrap(v);
    lemma_apply_hom_word_valid(phi_hom(), apply_hom(psi_hom(), u));
    lemma_equiv_symmetric(p, apply_hom(phi_hom(), apply_hom(psi_hom(), u)), u);
    lemma_equiv_transitive(p, u, apply_hom(phi_hom(), apply_hom(psi_hom(), u)),
        apply_hom(phi_hom(), apply_hom(psi_hom(), v)));
    lemma_equiv_transitive(p, u, apply_hom(phi_hom(), apply_hom(psi_hom(), v)), v);
}

// ── M0 (the token quotient is FREE via ψ): the iff, both directions VERIFIED ──
pub proof fn lemma_m0(u: Word, v: Word)
    requires word_valid(u, 6), word_valid(v, 6)
    ensures equiv_in_presentation(token_pres(), u, v)
        <==> freely_equivalent(apply_hom(psi_hom(), u), apply_hom(psi_hom(), v))
{
    if equiv_in_presentation(token_pres(), u, v) { lemma_m0_soundness(u, v); }
    if freely_equivalent(apply_hom(psi_hom(), u), apply_hom(psi_hom(), v)) { lemma_psi_faithful(u, v); }
}

} // verus!