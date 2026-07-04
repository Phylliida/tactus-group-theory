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
use crate::presentation::*;
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

} // verus!
