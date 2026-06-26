use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::lemma_relator_is_identity;
use crate::benign::{apply_embedding, embedding_preserving, lemma_apply_embedding_valid};
use crate::homomorphism::{HomomorphismData, apply_hom, is_valid_homomorphism,
    lemma_hom_preserves_equiv};
use crate::free_basis::lemma_apply_hom_eq_embedding;
use crate::hnn::{hnn_presentation, hnn_relators, hnn_relator};
use crate::cohen_layer05::{miller_data, lemma_miller_data_valid};
use crate::cohen_layer05_probe::l_slice;
use crate::free_product::shift_relators;
use crate::higman_operations::free_group;
use crate::miller_collapse::{miller_collapse_emb, lemma_miller_collapse_emb_len,
    lemma_miller_collapse_emb_valid};
use crate::miller_collapse_reln::lemma_collapse_hnn_relator_trivial;
use crate::machine_group::lemma_word_valid_mono;
use crate::britton_infra::lemma_hnn_presentation_valid;

verus! {

// ===========================================================================
// GAP-1 §9.2-item-(2) — `embedding_preserving`:  the collapse `emb_M : G^(M) → K_M` is a well-defined
// homomorphism into the fresh `{a,t}`-presentation `K_M = ⟨a,t | D̄_M⟩` (Danielle-signed packaging (A)).
//
// `D̄_M = pushforward(decls)` (the base relators only) — the association relators discharge to ε
// (the well-definedness brick, `miller_collapse_reln`).  Assembled via the codebase's homomorphism
// machinery (`lemma_hom_preserves_equiv` + `lemma_apply_hom_eq_embedding`), which lifts per-relator
// triviality to `G-equiv ⟹ K_M-equiv`.  Fresh packaging fixes `a = Gen(0)`, `t = Gen(1)`.
// ===========================================================================

/// `D̄_M` — the collapse images of the c-block relators (and ONLY those).  `|D̄_M| = |decls|`.
pub open spec fn dbar(n: nat, decls: Seq<Word>) -> Seq<Word> {
    Seq::new(decls.len(), |k: int| apply_embedding(miller_collapse_emb(n, 0, 1), decls[k]))
}

/// The fresh collapsed presentation `K_M = ⟨a, t | D̄_M⟩`  (2 generators: `a = Gen(0)`, `t = Gen(1)`).
pub open spec fn k_m(n: nat, decls: Seq<Word>) -> Presentation {
    Presentation { num_generators: 2, relators: dbar(n, decls) }
}

/// The collapse homomorphism `G^(M) → K_M` carrying `emb_M`.
pub open spec fn collapse_hom(n: nat, decls: Seq<Word>) -> HomomorphismData {
    HomomorphismData {
        source: hnn_presentation(miller_data(n, decls)),
        target: k_m(n, decls),
        generator_images: miller_collapse_emb(n, 0, 1),
    }
}

/// Every `D̄_M` relator is a valid 2-generator word.
pub proof fn lemma_dbar_valid(n: nat, decls: Seq<Word>)
    requires
        forall|k: int| 0 <= k < decls.len() ==> word_valid(#[trigger] decls[k], n),
    ensures
        forall|k: int| 0 <= k < dbar(n, decls).len() ==> word_valid(#[trigger] dbar(n, decls)[k], 2),
{
    let emb = miller_collapse_emb(n, 0, 1);
    lemma_miller_collapse_emb_len(n, 0, 1);          // emb.len() == n+3
    lemma_miller_collapse_emb_valid(n, 0, 1, 2);     // every emb[i] valid in 2
    assert forall|k: int| 0 <= k < dbar(n, decls).len()
        implies word_valid(#[trigger] dbar(n, decls)[k], 2) by {
        assert(dbar(n, decls)[k] == apply_embedding(emb, decls[k]));
        lemma_word_valid_mono(decls[k], n, (n + 3) as nat);   // decls[k] valid in n ⟹ in n+3 = emb.len()
        lemma_apply_embedding_valid(emb, decls[k], 2);
    }
}

/// `K_M` is a valid presentation.
pub proof fn lemma_k_m_valid(n: nat, decls: Seq<Word>)
    requires
        forall|k: int| 0 <= k < decls.len() ==> word_valid(#[trigger] decls[k], n),
    ensures
        presentation_valid(k_m(n, decls)),
{
    reveal(presentation_valid);
    lemma_dbar_valid(n, decls);
}

/// Structure of the source relators:  `base.relators (= decls) + hnn_relators`.
proof fn lemma_source_relators_struct(n: nat, decls: Seq<Word>)
    requires
        forall|k: int| 0 <= k < decls.len() ==> word_valid(#[trigger] decls[k], n),
    ensures
        hnn_presentation(miller_data(n, decls)).relators
            =~= decls + hnn_relators(miller_data(n, decls)),
        hnn_relators(miller_data(n, decls)).len() == (n + 1) as nat,
        hnn_presentation(miller_data(n, decls)).num_generators == (n + 3) as nat,
{
    lemma_miller_data_valid(n, decls);   // associations.len() == n+1, base.num_generators == n+2
    // l_slice(n,decls).relators =~= decls  (free_product of c0_slice + free_group(2), no extra relators)
    assert(shift_relators(Seq::<Word>::empty(), n) =~= Seq::<Word>::empty());
    assert(l_slice(n, decls).relators =~= decls);
}

/// Each source relator pushes through `emb_M` to `ε` in `K_M`: base relators ARE `D̄_M` relators
/// (`lemma_relator_is_identity`); association relators discharge (the well-definedness brick).
proof fn lemma_source_relator_trivial(n: nat, decls: Seq<Word>, k: int)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
        0 <= k < hnn_presentation(miller_data(n, decls)).relators.len(),
    ensures
        equiv_in_presentation(k_m(n, decls),
            apply_hom(collapse_hom(n, decls),
                hnn_presentation(miller_data(n, decls)).relators[k]),
            empty_word()),
{
    let h = collapse_hom(n, decls);
    let emb = miller_collapse_emb(n, 0, 1);
    let src_rel = hnn_presentation(miller_data(n, decls)).relators;
    lemma_source_relators_struct(n, decls);
    lemma_k_m_valid(n, decls);
    // apply_hom(h, r) = apply_embedding(emb, r)
    lemma_apply_hom_eq_embedding(h, src_rel[k]);

    if k < decls.len() {
        // src_rel[k] = decls[k] ;  apply_embedding(emb, decls[k]) = dbar[k] = k_m.relators[k]
        assert(src_rel[k] == decls[k]);
        assert(apply_embedding(emb, decls[k]) == dbar(n, decls)[k]);
        assert(dbar(n, decls)[k] == k_m(n, decls).relators[k]);
        lemma_relator_is_identity(k_m(n, decls), k);
    } else {
        let i = (k - decls.len()) as nat;
        assert(i < (n + 1) as nat);
        assert(src_rel[k] == hnn_relators(miller_data(n, decls))[i as int]);
        assert(hnn_relators(miller_data(n, decls))[i as int]
            == hnn_relator(miller_data(n, decls), i as int));
        lemma_collapse_hnn_relator_trivial(k_m(n, decls), n, decls, 0, 1, i);
    }
}

/// `collapse_hom` is a valid homomorphism `G^(M) → K_M`.
pub proof fn lemma_collapse_hom_valid(n: nat, decls: Seq<Word>)
    requires
        forall|k: int| 0 <= k < decls.len() ==> word_valid(#[trigger] decls[k], n),
    ensures
        is_valid_homomorphism(collapse_hom(n, decls)),
{
    let h = collapse_hom(n, decls);
    lemma_miller_data_valid(n, decls);                 // hnn_data_valid + base.num_generators == n+2
    lemma_hnn_presentation_valid(miller_data(n, decls));  // presentation_valid(source)
    lemma_k_m_valid(n, decls);                          // presentation_valid(target)
    lemma_miller_collapse_emb_len(n, 0, 1);            // emb.len() == n+3 == source.num_generators
    lemma_miller_collapse_emb_valid(n, 0, 1, 2);       // images valid in target.num_generators == 2

    assert forall|k: int| 0 <= k < h.source.relators.len()
        implies equiv_in_presentation(h.target, apply_hom(h, h.source.relators[k]), empty_word()) by {
        lemma_source_relator_trivial(n, decls, k);
    }
}

/// **`embedding_preserving`.**  `G^(M)`-equivalence implies `K_M`-equivalence of `emb_M`-images —
/// i.e. `emb_M` is a well-defined homomorphism into the fresh collapsed presentation.
pub proof fn lemma_collapse_preserving(n: nat, decls: Seq<Word>)
    requires
        forall|k: int| 0 <= k < decls.len() ==> word_valid(#[trigger] decls[k], n),
    ensures
        embedding_preserving(hnn_presentation(miller_data(n, decls)), k_m(n, decls),
            miller_collapse_emb(n, 0, 1)),
{
    let h = collapse_hom(n, decls);
    let src = hnn_presentation(miller_data(n, decls));
    let emb = miller_collapse_emb(n, 0, 1);
    lemma_collapse_hom_valid(n, decls);
    lemma_source_relators_struct(n, decls);            // src.num_generators == n+3
    lemma_miller_collapse_emb_len(n, 0, 1);            // emb.len() == n+3

    assert forall|w1: Word, w2: Word|
        word_valid(w1, src.num_generators) && word_valid(w2, src.num_generators)
        && equiv_in_presentation(src, w1, w2)
        implies #[trigger] equiv_in_presentation(k_m(n, decls),
            apply_embedding(emb, w1), apply_embedding(emb, w2)) by {
        lemma_hom_preserves_equiv(h, w1, w2);
        lemma_apply_hom_eq_embedding(h, w1);
        lemma_apply_hom_eq_embedding(h, w2);
    }
}

} // verus!
