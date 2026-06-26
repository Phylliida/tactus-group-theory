// GAP-1 item-3b, brick B3 — the generic pred→pred RELABEL-ISO lift (machine-free).
//
// `docs/final-gate-axiom-removal-plan.md` §3.4 / §14.4.  Co-designed with Danielle (port 8051,
// 2026-06-26): "build a generic lemma equiv_by_relabeling(p1,p2,ρ) where ρ is a generator relabeling
// such that r ∈ Rel(p1) ⟺ ρ(r) ∈ Rel(p2); it keeps B3 machine-agnostic and is reusable."
//
// ρ here is a block-SHIFT relabeling: Gen(i) ↦ Gen(off+i) (i < p1.num_generators), embedding p1's
// generators as the block `[off, off+p1.num_generators)` of p2.  The extra p2-generators are FREE
// (Cohen's c_pred carries free non-c generators — invisible to a word over the c-block).  The lift
// is built from the §54 "two mutually-inverse homomorphisms ⟹ iso" pattern (`miller_collapse_inject`):
// the forward relabel `relabel_hom` and the backward `relabel_hom_inv` (Gen(off+i) ↦ Gen(i), the free
// complement ↦ Gen(0)) compose to the identity on p1-words, so equivalence transports both ways.
//
//   lemma_equiv_by_relabel:  equiv(p1, v, ε)  ⟺  equiv(p2, ρ(v), ε)   (for v over p1's generators),
//   given the two-way relator correspondence  Rel(p1)(r) ⟺ Rel(p2)(ρ(r)).
//
// Machine-free / family-free: pure `pred_homomorphism` algebra.  Instantiated by item-3b's B2 (in the
// computability crate) with p1 = p_infty, p2 = c_pred, off = c_base.  Additive; reversible.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::{Word, empty_word, word_valid, inverse_word, lemma_inverse_singleton};
use crate::pred_presentation::*;
use crate::pred_presentation_lemmas::lemma_pred_relator_is_identity;
use crate::pred_homomorphism::*;

verus! {

// ----------------------------------------------------------------------------
// The forward / backward relabeling homomorphisms
// ----------------------------------------------------------------------------

/// Forward relabel `ρ : p1 → p2`, `Gen(i) ↦ Gen(off+i)` — embeds p1's generators as the block
/// `[off, off+p1.num_generators)` of p2.
pub open spec fn relabel_hom(p1: PredPresentation, p2: PredPresentation, off: nat) -> PredHomomorphismData {
    PredHomomorphismData {
        source: p1,
        target: p2,
        generator_images: Seq::new(p1.num_generators, |i: int| Seq::new(1, |_j: int| Symbol::Gen((off + i) as nat))),
    }
}

/// Backward relabel `ρ⁻¹ : p2 → p1`, `Gen(off+i) ↦ Gen(i)` on the image block; the free complement
/// `↦ Gen(0)` (junk — those generators never appear in p2's relators, so validity is unconstrained).
pub open spec fn relabel_hom_inv(p1: PredPresentation, p2: PredPresentation, off: nat) -> PredHomomorphismData {
    PredHomomorphismData {
        source: p2,
        target: p1,
        generator_images: Seq::new(p2.num_generators, |j: int|
            if off <= j < off + p1.num_generators {
                Seq::new(1, |_k: int| Symbol::Gen((j - off) as nat))
            } else {
                Seq::new(1, |_k: int| Symbol::Gen(0nat))
            }),
    }
}

// ----------------------------------------------------------------------------
// Round-trip: ρ⁻¹ ∘ ρ = id on p1-words
// ----------------------------------------------------------------------------

/// Single-letter round-trip: `ρ⁻¹(ρ(s)) = s` for a p1-symbol `s`.
pub proof fn lemma_relabel_sym_roundtrip(p1: PredPresentation, p2: PredPresentation, off: nat, s: Symbol)
    requires
        symbol_valid(s, p1.num_generators),
        off + p1.num_generators <= p2.num_generators,
    ensures
        apply_hom_pred(relabel_hom_inv(p1, p2, off), apply_hom_symbol_pred(relabel_hom(p1, p2, off), s))
            =~= Seq::new(1, |_i: int| s),
{
    let h = relabel_hom(p1, p2, off);
    let hinv = relabel_hom_inv(p1, p2, off);
    match s {
        Symbol::Gen(i) => {
            // i < p1.num_generators, so hsym(h, Gen(i)) = h.images[i] = [Gen(off+i)].
            assert(apply_hom_symbol_pred(h, s) == h.generator_images[i as int]);
            let mid = Seq::new(1, |_j: int| Symbol::Gen((off + i) as nat));
            assert(h.generator_images[i as int] =~= mid);
            lemma_hom_pred_singleton(hinv, Symbol::Gen((off + i) as nat));
            // hsym(hinv, Gen(off+i)) = hinv.images[off+i] = [Gen(i)]  (off ≤ off+i < off+p1.ng)
            assert(off <= (off + i) < off + p1.num_generators);
            assert(hinv.generator_images[(off + i) as int] =~= Seq::new(1, |_k: int| Symbol::Gen(i)));
            assert((((off + i) as nat) - off) as nat == i);
        },
        Symbol::Inv(i) => {
            // hsym(h, Inv(i)) = inverse_word([Gen(off+i)]) = [Inv(off+i)].
            assert(apply_hom_symbol_pred(h, s) == inverse_word(h.generator_images[i as int]));
            let gen_mid = Seq::new(1, |_j: int| Symbol::Gen((off + i) as nat));
            assert(h.generator_images[i as int] =~= gen_mid);
            lemma_inverse_singleton(Symbol::Gen((off + i) as nat));
            let inv_mid = Seq::new(1, |_j: int| Symbol::Inv((off + i) as nat));
            assert(inverse_word(gen_mid) =~= inv_mid);
            lemma_hom_pred_singleton(hinv, Symbol::Inv((off + i) as nat));
            // hsym(hinv, Inv(off+i)) = inverse_word(hinv.images[off+i]) = inverse_word([Gen(i)]) = [Inv(i)].
            assert(off <= (off + i) < off + p1.num_generators);
            assert(hinv.generator_images[(off + i) as int] =~= Seq::new(1, |_k: int| Symbol::Gen(i)));
            assert((((off + i) as nat) - off) as nat == i);
            lemma_inverse_singleton(Symbol::Gen(i));
        },
    }
}

/// Whole-word round-trip: `ρ⁻¹(ρ(v)) = v` for any p1-word `v`.
pub proof fn lemma_relabel_roundtrip(p1: PredPresentation, p2: PredPresentation, off: nat, v: Word)
    requires
        word_valid(v, p1.num_generators),
        off + p1.num_generators <= p2.num_generators,
    ensures
        apply_hom_pred(relabel_hom_inv(p1, p2, off), apply_hom_pred(relabel_hom(p1, p2, off), v)) =~= v,
    decreases v.len()
{
    let h = relabel_hom(p1, p2, off);
    let hinv = relabel_hom_inv(p1, p2, off);
    if v.len() == 0 {
        assert(apply_hom_pred(h, v) =~= empty_word());
        assert(apply_hom_pred(hinv, empty_word()) =~= empty_word());
        assert(v =~= empty_word());
    } else {
        let s = v.first();
        let rest = v.drop_first();
        assert(symbol_valid(s, p1.num_generators)) by { assert(s == v[0]); }
        assert(word_valid(rest, p1.num_generators)) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], p1.num_generators) by {
                assert(rest[k] == v[k + 1]);
            }
        }
        lemma_relabel_roundtrip(p1, p2, off, rest);                          // IH: ρ⁻¹(ρ(rest)) = rest
        // ρ(v) = concat(hsym(h,s), ρ(rest)).
        assert(apply_hom_pred(h, v) =~= crate::word::concat(apply_hom_symbol_pred(h, s), apply_hom_pred(h, rest)));
        lemma_hom_pred_respects_concat(hinv, apply_hom_symbol_pred(h, s), apply_hom_pred(h, rest));
        lemma_relabel_sym_roundtrip(p1, p2, off, s);                          // ρ⁻¹(hsym(h,s)) = [s]
        // ρ⁻¹(ρ(v)) = concat([s], rest) = v.
        assert(v =~= crate::word::concat(Seq::new(1, |_i: int| s), rest));
    }
}

// ----------------------------------------------------------------------------
// Generic 2-homomorphism iso on the word problem
// ----------------------------------------------------------------------------

/// Two mutually-inverse pred-homomorphisms transport triviality both ways (§54 pattern).
pub proof fn lemma_pred_hom_iso_equiv(h: PredHomomorphismData, hinv: PredHomomorphismData, v: Word)
    requires
        is_valid_pred_homomorphism(h),
        is_valid_pred_homomorphism(hinv),
        hinv.source == h.target,
        hinv.target == h.source,
        apply_hom_pred(hinv, apply_hom_pred(h, v)) =~= v,
    ensures
        equiv_in_pred_presentation(h.source, v, empty_word())
            <==> equiv_in_pred_presentation(h.target, apply_hom_pred(h, v), empty_word()),
{
    // forward: equiv(p1,v,ε) ⟹ equiv(p2, h(v), h(ε)=ε)
    assert(equiv_in_pred_presentation(h.source, v, empty_word())
        ==> equiv_in_pred_presentation(h.target, apply_hom_pred(h, v), empty_word())) by {
        if equiv_in_pred_presentation(h.source, v, empty_word()) {
            lemma_hom_pred_preserves_equiv(h, v, empty_word());
            lemma_hom_pred_empty(h);
        }
    }
    // backward: equiv(p2, h(v), ε) ⟹ equiv(p1, hinv(h(v))=v, hinv(ε)=ε)
    assert(equiv_in_pred_presentation(h.target, apply_hom_pred(h, v), empty_word())
        ==> equiv_in_pred_presentation(h.source, v, empty_word())) by {
        if equiv_in_pred_presentation(h.target, apply_hom_pred(h, v), empty_word()) {
            lemma_hom_pred_preserves_equiv(hinv, apply_hom_pred(h, v), empty_word());
            lemma_hom_pred_empty(hinv);
        }
    }
}

// ----------------------------------------------------------------------------
// Validity of the two relabel homomorphisms (from the relator correspondence)
// ----------------------------------------------------------------------------

/// `ρ` is a valid homomorphism, given the FORWARD relator correspondence.
pub proof fn lemma_relabel_hom_valid(p1: PredPresentation, p2: PredPresentation, off: nat)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
        off + p1.num_generators <= p2.num_generators,
        forall|r: Word| #![trigger (p1.relators)(r)]
            (p1.relators)(r) ==> (p2.relators)(apply_hom_pred(relabel_hom(p1, p2, off), r)),
    ensures
        is_valid_pred_homomorphism(relabel_hom(p1, p2, off)),
{
    let h = relabel_hom(p1, p2, off);
    assert(h.generator_images.len() == p1.num_generators);
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(#[trigger] h.generator_images[i], p2.num_generators) by {
        assert(h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen((off + i) as nat)));
        assert(symbol_valid(Symbol::Gen((off + i) as nat), p2.num_generators));
    }
    assert forall|r: Word| #![trigger (h.source.relators)(r)] (h.source.relators)(r)
        implies equiv_in_pred_presentation(h.target, apply_hom_pred(h, r), empty_word()) by {
        assert((p1.relators)(r));
        assert((p2.relators)(apply_hom_pred(h, r)));
        lemma_pred_relator_is_identity(p2, apply_hom_pred(h, r));
    }
}

/// `ρ⁻¹` is a valid homomorphism, given the BACKWARD relator correspondence.
pub proof fn lemma_relabel_hom_inv_valid(p1: PredPresentation, p2: PredPresentation, off: nat)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
        off + p1.num_generators <= p2.num_generators,
        p1.num_generators >= 1,
        forall|s: Word| #![trigger (p2.relators)(s)]
            (p2.relators)(s) ==> exists|r: Word|
                word_valid(r, p1.num_generators) && (p1.relators)(r)
                && s =~= apply_hom_pred(relabel_hom(p1, p2, off), r),
    ensures
        is_valid_pred_homomorphism(relabel_hom_inv(p1, p2, off)),
{
    let hinv = relabel_hom_inv(p1, p2, off);
    assert(hinv.generator_images.len() == p2.num_generators);
    assert forall|j: int| 0 <= j < hinv.generator_images.len()
        implies word_valid(#[trigger] hinv.generator_images[j], p1.num_generators) by {
        if off <= j < off + p1.num_generators {
            assert(hinv.generator_images[j] =~= Seq::new(1, |_k: int| Symbol::Gen((j - off) as nat)));
            assert(symbol_valid(Symbol::Gen((j - off) as nat), p1.num_generators));
        } else {
            assert(hinv.generator_images[j] =~= Seq::new(1, |_k: int| Symbol::Gen(0nat)));
            assert(symbol_valid(Symbol::Gen(0nat), p1.num_generators));
        }
    }
    assert forall|s: Word| #![trigger (hinv.source.relators)(s)] (hinv.source.relators)(s)
        implies equiv_in_pred_presentation(hinv.target, apply_hom_pred(hinv, s), empty_word()) by {
        assert((p2.relators)(s));
        let r = choose|r: Word|
            word_valid(r, p1.num_generators) && (p1.relators)(r)
            && s =~= apply_hom_pred(relabel_hom(p1, p2, off), r);
        // ρ⁻¹(s) = ρ⁻¹(ρ(r)) = r, and r ≡ ε in p1.
        lemma_relabel_roundtrip(p1, p2, off, r);
        assert(apply_hom_pred(hinv, s) =~= r);
        lemma_pred_relator_is_identity(p1, r);
    }
}

// ----------------------------------------------------------------------------
// The consumer-facing relabel-iso lift
// ----------------------------------------------------------------------------

/// **B3 — relabel-iso.**  If the block-shift relabeling `ρ : Gen(i) ↦ Gen(off+i)` matches p1's and
/// p2's relator sets BOTH WAYS, then the word problem transports: `v ≡ ε in p1 ⟺ ρ(v) ≡ ε in p2`.
pub proof fn lemma_equiv_by_relabel(p1: PredPresentation, p2: PredPresentation, off: nat, v: Word)
    requires
        pred_presentation_valid(p1),
        pred_presentation_valid(p2),
        off + p1.num_generators <= p2.num_generators,
        p1.num_generators >= 1,
        word_valid(v, p1.num_generators),
        forall|r: Word| #![trigger (p1.relators)(r)]
            (p1.relators)(r) ==> (p2.relators)(apply_hom_pred(relabel_hom(p1, p2, off), r)),
        forall|s: Word| #![trigger (p2.relators)(s)]
            (p2.relators)(s) ==> exists|r: Word|
                word_valid(r, p1.num_generators) && (p1.relators)(r)
                && s =~= apply_hom_pred(relabel_hom(p1, p2, off), r),
    ensures
        equiv_in_pred_presentation(p1, v, empty_word())
            <==> equiv_in_pred_presentation(p2, apply_hom_pred(relabel_hom(p1, p2, off), v), empty_word()),
{
    let h = relabel_hom(p1, p2, off);
    let hinv = relabel_hom_inv(p1, p2, off);
    lemma_relabel_hom_valid(p1, p2, off);
    lemma_relabel_hom_inv_valid(p1, p2, off);
    lemma_relabel_roundtrip(p1, p2, off, v);
    lemma_pred_hom_iso_equiv(h, hinv, v);
}

} // verus!
