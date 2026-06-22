// Layer 2 — Brick 5 COMPLETENESS, C3.2c / F1: the free subgroup `F = ⟨t, x, d, b_j⟩` of `h2_II`.
//
// `F1` (the Route-B prerequisite, docs/brick5-c3.2c-plan.md §3b): the subgroup
// `F = ⟨t, x, d, b_1..b_n⟩` is FREE in `h1_base` (hence in `h2_II`, the p-HNN over it).
// This is what makes `A = ⟨t,x,d,b_j,p⟩ = HNN(F free, p | family II)` a legitimate
// presentation of the subgroup `A`, so `A`'s only relations are the p-conjugations and the
// von Dyck (backward) crux direction reduces to "`φ_l` respects the `p`-conjugations".
//
// Mathematics: `h1_base = K_M ∗ (F(c) × F(b)) ∗ ⟨d⟩` (a free product, since we DON'T carry `C`'s
// relator set `S`).  `F = ⟨t,x⟩ * ⟨b_j⟩ * ⟨d⟩`, where `⟨t,x⟩` is free in `K_M`, `⟨b_j⟩` free in
// the middle factor, `⟨d⟩` free.  Subgroups of distinct free factors generate their free product,
// hence `F` is free.
//
// NOTE on the obstruction: there is NO retraction `K_M → ⟨t,x⟩` (the machine relators are
// conjugacy relations among config words that cannot be killed while fixing `t, x`), so the
// pullback engine of `free_basis.rs` (which needs a valid homomorphism on the whole source) does
// NOT apply with `t, x` preserved.  `⟨t,x⟩` is free in `K_M` but is not a RETRACT of it — its
// freeness is established by the FAITHFUL base embedding `base_A ↪ K_M` (`lemma_g_m_base_faithful`)
// composed with `base_A = HNN(⟨t,x⟩ free, y)` (`a_as_hnn`), NOT by a homomorphism.
//
// This module builds the pieces bottom-up.  First brick (F1a): `⟨t,x⟩` is free in `K_M = g_m`.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::machine_group::*;
use crate::hnn::*;
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_valid};
use crate::free_product::free_product;
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::normal_form_free_product::lemma_free_product_injective_left;
use crate::free_basis::lemma_g_m_base_faithful;

verus! {

// ----------------------------------------------------------------------------
// apply_embedding only depends on the images at the indices a word actually uses.
// ----------------------------------------------------------------------------

/// If two image lists agree on the first `k` entries and `w` is valid over `k`, the embeddings
/// agree.  (Pure induction on `w`; each symbol uses an index `< k` where the lists coincide.)
pub proof fn lemma_apply_embedding_agree_prefix(imgs1: Seq<Word>, imgs2: Seq<Word>, w: Word, k: nat)
    requires
        word_valid(w, k),
        k <= imgs1.len(),
        k <= imgs2.len(),
        forall|i: int| 0 <= i < k ==> imgs1[i] == imgs2[i],
    ensures
        apply_embedding(imgs1, w) =~= apply_embedding(imgs2, w),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, k)) by { assert(w[0] == s); }
        assert(word_valid(rest, k)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], k) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        // head symbol agrees: its index < k where imgs1, imgs2 coincide.
        assert(apply_embedding_symbol(imgs1, s) == apply_embedding_symbol(imgs2, s)) by {
            match s {
                Symbol::Gen(i) => { assert(imgs1[i as int] == imgs2[i as int]); },
                Symbol::Inv(i) => { assert(imgs1[i as int] == imgs2[i as int]); },
            }
        }
        lemma_apply_embedding_agree_prefix(imgs1, imgs2, rest, k);
        assert(apply_embedding(imgs1, w)
            =~= concat(apply_embedding_symbol(imgs1, s), apply_embedding(imgs1, rest)));
        assert(apply_embedding(imgs2, w)
            =~= concat(apply_embedding_symbol(imgs2, s), apply_embedding(imgs2, rest)));
    }
}

// ----------------------------------------------------------------------------
// Free-group equivalence is monotone in the generator count.
// ----------------------------------------------------------------------------

/// A valid `free_group(k)` derivation is valid in `free_group(k2)` for `k ≤ k2`: free groups have
/// NO relators (so `RelatorInsert/Delete` never appear in a valid derivation), and the only
/// `num_generators` dependence is `FreeExpand`'s `symbol_valid(·, num_gens)`, which only WEAKENS as
/// the count grows.  So `apply_step` agrees on every step a valid `free_group(k)` derivation uses.
proof fn lemma_free_group_derivation_transfers(
    k: nat, k2: nat, steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        k <= k2,
        derivation_produces(free_group(k), steps, start) == Some(end),
    ensures
        derivation_produces(free_group(k2), steps, start) == Some(end),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let s = steps.first();
        let next = apply_step(free_group(k), start, s);
        assert(next is Some);             // else derivation_produces would be None
        let nw = next.unwrap();
        // apply_step agrees in free_group(k2): relators empty (no Relator steps survive), and
        // FreeExpand's symbol_valid(·, k) ⟹ symbol_valid(·, k2).
        assert(apply_step(free_group(k2), start, s) == Some(nw)) by {
            match s {
                DerivationStep::FreeReduce { position } => { },
                DerivationStep::FreeExpand { position, symbol } => {
                    // free_group(k) gave Some ⟹ symbol_valid(symbol, k) ⟹ symbol_valid(symbol, k2).
                    if 0 <= position <= start.len() && symbol_valid(symbol, k) {
                        assert(symbol_valid(symbol, k2));
                    }
                },
                DerivationStep::RelatorInsert { position, relator_index, inverted } => {
                    // free_group(k).relators is empty ⟹ relator_index < 0 is false ⟹ would be None.
                    assert(free_group(k).relators.len() == 0);
                },
                DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                    assert(free_group(k).relators.len() == 0);
                },
            }
        }
        lemma_free_group_derivation_transfers(k, k2, steps.drop_first(), nw, end);
    }
}

/// **Free-group equivalence is monotone in the generator count.** `k ≤ k2` and `w1 ≡ w2` in
/// `free_group(k)` ⟹ `w1 ≡ w2` in `free_group(k2)`.
pub proof fn lemma_free_group_equiv_mono(k: nat, k2: nat, w1: Word, w2: Word)
    requires
        k <= k2,
        equiv_in_presentation(free_group(k), w1, w2),
    ensures
        equiv_in_presentation(free_group(k2), w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(free_group(k), d, w1, w2);
    assert(derivation_produces(free_group(k), d.steps, w1) == Some(w2));
    lemma_free_group_derivation_transfers(k, k2, d.steps, w1, w2);
    assert(derivation_valid(free_group(k2), Derivation { steps: d.steps }, w1, w2));
}

// ----------------------------------------------------------------------------
// B1 — base case: a stable-letter-free word descends to free-group triviality.
// ----------------------------------------------------------------------------

/// **B1 base case.** Let `gens` be a FREE family in `gp` (the higher-order `free-family` hypothesis).
/// If `w` is valid over `gens.len()` (i.e. uses NO stable letter `s = Gen(gp.num_generators)`) and
/// the stable-extended embedding `apply_embedding(gens.push([s]), w)` is trivial in
/// `gp ∗ ⟨s⟩ = hnn_presentation(free_stable_data(gp))`, then `w ≡ ε` in `free_group(gens.len()+1)`.
///
/// Chain: the `s`-image is unused (prefix-invariance) so the embedded word is the `gp`-word
/// `apply_embedding(gens, w)`; descend `gp ∗ ⟨s⟩ → gp` (`lemma_free_product_injective_left` via the
/// `lemma_free_stable_is_free_product` bridge); the free-family hypothesis gives `w ≡ ε` over
/// `gens.len()`, lifted to `gens.len()+1` (free groups: more generators, same empty relators).
pub proof fn lemma_extend_free_no_stable(gp: Presentation, gens: Seq<Word>, w: Word)
    requires
        presentation_valid(gp),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], gp.num_generators),
        forall|u: Word| (#[trigger] word_valid(u, gens.len())
            && equiv_in_presentation(gp, apply_embedding(gens, u), empty_word()))
            ==> equiv_in_presentation(free_group(gens.len()), u, empty_word()),
        word_valid(w, gens.len()),
        equiv_in_presentation(hnn_presentation(free_stable_data(gp)),
            apply_embedding(gens.push(seq![Symbol::Gen(gp.num_generators)]), w), empty_word()),
    ensures
        equiv_in_presentation(free_group((gens.len() + 1) as nat), w, empty_word()),
{
    let s_emb = gens.push(seq![Symbol::Gen(gp.num_generators)]);
    let gw = apply_embedding(gens, w);
    // (1) the s-image is unused: apply_embedding(s_emb, w) =~= apply_embedding(gens, w).
    assert(s_emb.len() == gens.len() + 1);
    assert forall|i: int| 0 <= i < gens.len() implies s_emb[i] == gens[i] by { }
    lemma_apply_embedding_agree_prefix(s_emb, gens, w, gens.len());
    assert(equiv_in_presentation(hnn_presentation(free_stable_data(gp)), gw, empty_word()));
    // (2) hnn_presentation(free_stable_data(gp)) == free_product(gp, free_group(1)).
    lemma_free_stable_is_free_product(gp);
    assert(equiv_in_presentation(free_product(gp, free_group(1)), gw, empty_word()));
    // (3) gw is a gp-word; descend to gp via free-product left-injectivity.
    lemma_apply_embedding_valid(gens, w, gp.num_generators);
    assert(word_valid(gw, gp.num_generators));
    lemma_free_group_valid(1);
    lemma_free_product_injective_left(gp, free_group(1), gw);
    assert(equiv_in_presentation(gp, gw, empty_word()));
    // (4) free-family hypothesis on u = w.
    assert(equiv_in_presentation(free_group(gens.len()), w, empty_word()));
    // (5) lift free_group(k) → free_group(k+1) (empty relators; only num_generators grows).
    lemma_free_group_equiv_mono(gens.len(), (gens.len() + 1) as nat, w, empty_word());
}

// ----------------------------------------------------------------------------
// Adding a free generator = HNN with NO associations.
// ----------------------------------------------------------------------------

/// The HNN datum that adjoins a single FREE stable letter to `gp` (no associations).  Its pinches
/// are exactly adjacent `s … s⁻¹` pairs with a base-trivial middle (`in_generated_subgroup(gp, [], ·)`
/// = `· ≡_{gp} ε`), and `hnn_associations_isomorphic` holds vacuously — so `britton_lemma_full`
/// applies, the route by which "a free family extends by a free stable letter".
pub open spec fn free_stable_data(gp: Presentation) -> HNNData {
    HNNData { base: gp, associations: Seq::<(Word, Word)>::empty() }
}

/// **The bridge:** adjoining a free stable letter (the empty-association HNN) IS the free product
/// `gp ∗ ⟨s⟩ = gp ∗ free_group(1)`, on the nose.  Both are
/// `⟨gp.num_generators + 1 | gp.relators⟩` — the HNN side has no HNN relators (no associations) and
/// the free-product side adjoins `free_group(1)`'s (empty, shifted) relators.
pub proof fn lemma_free_stable_is_free_product(gp: Presentation)
    ensures
        hnn_presentation(free_stable_data(gp)) == free_product(gp, free_group(1)),
{
    let data = free_stable_data(gp);
    let lhs = hnn_presentation(data);
    let rhs = free_product(gp, free_group(1));
    // HNN side: no associations ⟹ no HNN relators.
    assert(data.associations.len() == 0);
    assert(hnn_relators(data) =~= Seq::<Word>::empty());
    assert(lhs.relators =~= gp.relators);
    // free-product side: free_group(1) has empty relators, so the shifted block is empty.
    assert(free_group(1).relators =~= Seq::<Word>::empty());
    assert(crate::free_product::shift_relators(free_group(1).relators, gp.num_generators)
        =~= Seq::<Word>::empty());
    assert(rhs.relators =~= gp.relators);
    // both: num_generators = gp.num_generators + 1, relators = gp.relators.
    assert(lhs.num_generators == rhs.num_generators);
    assert(lhs.relators =~= rhs.relators);
    assert(lhs == rhs);
}

// ----------------------------------------------------------------------------
// F1a — `⟨t,x⟩` is free in `K_M = g_m`.
// ----------------------------------------------------------------------------

/// **F1a.** A word over `{t = Gen(0), x = Gen(1)}` that is trivial in `K_M = g_m(mm)` is already
/// trivial in the free group `pres_tx = free⟨t,x⟩` — i.e. `⟨t,x⟩` is free in `K_M`.
///
/// Chain: lift `word_valid(·,2) → (·,3)`; descend `g_m → base_A` (`lemma_g_m_base_faithful`);
/// transport `base_A → A`'s HNN presentation (Tietze bridge `lemma_base_A_to_a_hnn`); then peel
/// the `y`-HNN layer `base_A = HNN(pres_tx, y | y⁻¹xy = x)` with `lemma_single_hnn_base_faithful`
/// (the `a_as_hnn` datum is valid + association-isomorphic).
pub proof fn lemma_tx_free_in_g_m(mm: ModMachine, w: Word)
    requires
        mod_machine_wf(mm),
        word_valid(w, 2),
        equiv_in_presentation(g_m(mm), w, empty_word()),
    ensures
        equiv_in_presentation(pres_tx(), w, empty_word()),
{
    // w is a base_A word (gens {0,1} ⊆ {0,1,2}).
    lemma_word_valid_mono(w, 2, 3);
    // g_m → base_A.
    lemma_g_m_base_faithful(mm, w);
    // base_A → pres_tx (Tietze bridge + peel the y-HNN layer): exactly `lemma_a_base_faithful`.
    lemma_a_base_faithful(w);
}

} // verus!
