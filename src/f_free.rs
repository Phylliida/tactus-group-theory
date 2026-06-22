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
use crate::britton_via_tower::{is_stable, has_stable_letter, has_pinch, has_pinch_at,
    has_adjacent_opposite_at, stable_count, lemma_stable_count_concat, lemma_stable_count_no_stable,
    lemma_has_stable_implies_count, lemma_delete_equiv_empty};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_valid,
    lemma_apply_embedding_concat, in_generated_subgroup};
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

// ----------------------------------------------------------------------------
// B1 — the inductive (pinch) case: `lemma_extend_free_by_stable`.
//
// Port of `machine_group::lemma_psi_F_injective` / `_pinch_descends` / `_spanning` into the
// cross-presentation setting.  The embedding `s_emb = gens.push([s])` differs from `ψ_F`:
//   • a NON-stable source gen `i < gens.len()` maps to `gens[i]` — a stable-FREE `gp`-word of
//     arbitrary length (vs `ψ_F`'s `t ↦ t`, length 1);
//   • the stable source gen `gens.len()` maps to `[s]` — exactly ONE stable letter (vs `ψ_F`'s
//     `x ↦ xᵖ`, a run of length `p`).
// So the "run" and "length-1" roles are swapped: the spanning case fires when the peeled symbol is
// the stable letter, and peeling a non-stable symbol strips a variable-length stable-free prefix.
// ----------------------------------------------------------------------------

/// The stable-extended embedding: each free-family generator keeps its image, the new (stable)
/// generator `Gen(gp.num_generators)` maps to the single stable letter `[Gen(gp.num_generators)]`.
pub open spec fn stable_emb(gp: Presentation, gens: Seq<Word>) -> Seq<Word> {
    gens.push(seq![Symbol::Gen(gp.num_generators)])
}

/// Index facts for `stable_emb` (Seq::push).
pub proof fn lemma_stable_emb_index(gp: Presentation, gens: Seq<Word>)
    ensures
        stable_emb(gp, gens).len() == gens.len() + 1,
        forall|i: int| 0 <= i < gens.len() ==> stable_emb(gp, gens)[i] == gens[i],
        stable_emb(gp, gens)[gens.len() as int] == seq![Symbol::Gen(gp.num_generators)],
{
}

/// The empty-association HNN is `hnn_data_valid` whenever the base is valid.
pub proof fn lemma_free_stable_data_valid(gp: Presentation)
    requires
        presentation_valid(gp),
    ensures
        hnn_data_valid(free_stable_data(gp)),
{
    assert(free_stable_data(gp).associations.len() == 0);
}

/// The empty-association HNN is (vacuously) association-isomorphic: only the empty word is valid
/// over `0` generators, and both embedded sides are then `ε`.
pub proof fn lemma_free_stable_data_isomorphic(gp: Presentation)
    ensures
        hnn_associations_isomorphic(free_stable_data(gp)),
{
    let data = free_stable_data(gp);
    let k = data.associations.len();
    assert(k == 0);
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word())
        <==>
        equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word())
    ) by {
        assert(w.len() == 0) by {
            if w.len() > 0 { assert(symbol_valid(w[0], 0)); }
        }
        assert(w =~= empty_word());
        assert(apply_embedding(a_words, w) =~= empty_word());
        assert(apply_embedding(b_words, w) =~= empty_word());
    }
}

/// A word valid over `gp.num_generators` has NO inner stable letter (its symbols all have index
/// `< gp.num_generators`, while the stable letter sits at index `gp.num_generators`).
pub proof fn lemma_word_valid_no_inner_stable(gp: Presentation, v: Word)
    requires
        word_valid(v, gp.num_generators),
    ensures
        forall|k: int| 0 <= k < v.len() ==> !is_stable(free_stable_data(gp), #[trigger] v[k]),
{
    assert forall|k: int| 0 <= k < v.len() implies !is_stable(free_stable_data(gp), v[k]) by {
        assert(symbol_valid(v[k], gp.num_generators));
    }
}

/// Reverse of `lemma_in_empty_subgroup_trivial`: a word `≡ ε` lies in the trivial subgroup.
pub proof fn lemma_trivial_in_empty_subgroup(p: Presentation, w: Word)
    requires
        presentation_valid(p),
        word_valid(w, p.num_generators),
        equiv_in_presentation(p, w, empty_word()),
    ensures
        in_generated_subgroup(p, Seq::<Word>::empty(), w),
{
    let factors = Seq::<Word>::empty();
    assert(crate::benign::factors_from_generators(Seq::<Word>::empty(), factors));
    assert(crate::benign::concat_all(factors) =~= empty_word());
    lemma_equiv_symmetric(p, w, empty_word());
    assert(equiv_in_presentation(p, crate::benign::concat_all(factors), w));
}

/// **Generic pinch-out** for the empty-association HNN: deleting a pinch `s·u·s⁻¹` (with `u ≡ ε` in
/// the base, since the associated subgroup is trivial) shrinks the word by an `≡`-step.  This is
/// `lemma_pinch_out` generalized from the fixed `pres_t`/`pres_tx` to an arbitrary base `gp`.
pub proof fn lemma_free_stable_pinch_out(gp: Presentation, w: Word, i: int, j: int)
    requires
        presentation_valid(gp),
        has_pinch_at(free_stable_data(gp), w, i, j),
    ensures
        equiv_in_presentation(hnn_presentation(free_stable_data(gp)),
            w, w.subrange(0, i) + w.subrange(j + 1, w.len() as int)),
{
    let data = free_stable_data(gp);
    let hp = hnn_presentation(data);
    let u = w.subrange(i + 1, j);
    let mid = w.subrange(i, j + 1);
    let si = w[i];
    let sj = w[j];
    // both associated-subgroup generator lists are empty
    assert(Seq::new(0, |k: int| data.associations[k].0) =~= Seq::<Word>::empty());
    assert(Seq::new(0, |k: int| data.associations[k].1) =~= Seq::<Word>::empty());
    // the pinch middle lies in the trivial subgroup ⟹ u ≡ ε
    assert(in_generated_subgroup(gp, Seq::<Word>::empty(), u));
    assert(is_inverse_pair(si, sj));
    lemma_in_empty_subgroup_trivial(gp, u);
    lemma_base_embeds_in_hnn(data, u, empty_word());     // u ≡ ε in hp
    // mid = [si] · (u · [sj]) ≡ [si] · [sj] ≡ ε
    assert(mid =~= concat(seq![si], concat(u, seq![sj])));
    lemma_delete_equiv_empty(hp, seq![si], u, seq![sj]);
    assert(concat(seq![si], seq![sj]) =~= seq![si, sj]);
    lemma_cancel_pair_equiv_empty(hp, si, sj);
    lemma_equiv_transitive(hp, mid, concat(seq![si], seq![sj]), empty_word());
    // w = w[0..i] · (mid · w[j+1..])  ⟹  w ≡ w[0..i] · w[j+1..]
    assert(w =~= concat(w.subrange(0, i), concat(mid, w.subrange(j + 1, w.len() as int))));
    lemma_delete_equiv_empty(hp,
        w.subrange(0, i), mid, w.subrange(j + 1, w.len() as int));
    assert(w.subrange(0, i) + w.subrange(j + 1, w.len() as int)
        =~= concat(w.subrange(0, i), w.subrange(j + 1, w.len() as int)));
}

/// Adjoining a free stable letter to a FREE group is again a free group: the empty-association HNN
/// over `free_group(k)` is exactly `free_group(k+1)`.  (Analog of `lemma_f_as_hnn_presentation`.)
pub proof fn lemma_free_stable_of_free_group(k: nat)
    ensures
        hnn_presentation(free_stable_data(free_group(k))) == free_group((k + 1) as nat),
{
    let data = free_stable_data(free_group(k));
    let lhs = hnn_presentation(data);
    let rhs = free_group((k + 1) as nat);
    assert(data.associations.len() == 0);
    assert(hnn_relators(data) =~= Seq::<Word>::empty());
    assert(free_group(k).relators =~= Seq::<Word>::empty());
    assert(lhs.relators =~= Seq::<Word>::empty());
    assert(rhs.relators =~= Seq::<Word>::empty());
    assert(lhs.num_generators == rhs.num_generators);
    assert(lhs.relators =~= rhs.relators);
    assert(lhs == rhs);
}

// ----------------------------------------------------------------------------
// Stable-count correspondence: W = apply_embedding(s_emb, w) has the same number of (inner) stable
// letters as w has (outer) stable letters — the stable gen maps to ONE stable letter, non-stable
// gens map to stable-free words.  (Analog of `lemma_psi_F_stable_count_scales`, factor 1.)
// ----------------------------------------------------------------------------

/// Per-symbol contribution: `s_emb` applied to a single symbol contributes 1 inner stable letter
/// iff the symbol was the outer stable letter, else 0.
pub proof fn lemma_extend_emb_symbol_stable_count(gp: Presentation, gens: Seq<Word>, s: Symbol)
    requires
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], gp.num_generators),
        symbol_valid(s, (gens.len() + 1) as nat),
    ensures
        stable_count(free_stable_data(gp), apply_embedding(stable_emb(gp, gens), seq![s]))
            == (if is_stable(free_stable_data(free_group(gens.len())), s) { 1nat } else { 0nat }),
{
    let inner = free_stable_data(gp);
    let outer = free_stable_data(free_group(gens.len()));
    let imgs = stable_emb(gp, gens);
    lemma_stable_emb_index(gp, gens);
    reveal_with_fuel(apply_embedding, 2);
    assert(apply_embedding(imgs, seq![s]) =~= apply_embedding_symbol(imgs, s));
    let g = gens.len() as int;
    // outer stable letter sits at index gens.len().
    assert(outer.base.num_generators == gens.len());
    match s {
        Symbol::Gen(idx) => {
            if idx == gens.len() {
                assert(is_stable(outer, s));
                assert(apply_embedding_symbol(imgs, s) =~= imgs[g]);
                assert(imgs[g] =~= seq![Symbol::Gen(gp.num_generators)]);
                assert(is_stable(inner, Symbol::Gen(gp.num_generators)));
                reveal_with_fuel(stable_count, 2);
            } else {
                assert(idx < gens.len());
                assert(!is_stable(outer, s));
                assert(apply_embedding_symbol(imgs, s) =~= imgs[idx as int]);
                assert(imgs[idx as int] == gens[idx as int]);
                lemma_word_valid_no_inner_stable(gp, gens[idx as int]);
                lemma_stable_count_no_stable(inner, gens[idx as int]);
            }
        }
        Symbol::Inv(idx) => {
            if idx == gens.len() {
                assert(is_stable(outer, s));
                assert(apply_embedding_symbol(imgs, s) =~= inverse_word(imgs[g]));
                assert(imgs[g] =~= seq![Symbol::Gen(gp.num_generators)]);
                assert(inverse_word(imgs[g]) =~= seq![Symbol::Inv(gp.num_generators)]) by {
                    reveal_with_fuel(inverse_word, 2);
                }
                assert(is_stable(inner, Symbol::Inv(gp.num_generators)));
                reveal_with_fuel(stable_count, 2);
            } else {
                assert(idx < gens.len());
                assert(!is_stable(outer, s));
                assert(apply_embedding_symbol(imgs, s) =~= inverse_word(imgs[idx as int]));
                assert(imgs[idx as int] == gens[idx as int]);
                crate::word::lemma_inverse_word_valid(gens[idx as int], gp.num_generators);
                lemma_word_valid_no_inner_stable(gp, inverse_word(gens[idx as int]));
                lemma_stable_count_no_stable(inner, inverse_word(gens[idx as int]));
            }
        }
    }
}

/// The inner stable count of `W = apply_embedding(s_emb, w)` equals the outer stable count of `w`.
pub proof fn lemma_extend_stable_count_eq(gp: Presentation, gens: Seq<Word>, w: Word)
    requires
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], gp.num_generators),
        word_valid(w, (gens.len() + 1) as nat),
    ensures
        stable_count(free_stable_data(gp), apply_embedding(stable_emb(gp, gens), w))
            == stable_count(free_stable_data(free_group(gens.len())), w),
    decreases w.len(),
{
    let inner = free_stable_data(gp);
    let outer = free_stable_data(free_group(gens.len()));
    let imgs = stable_emb(gp, gens);
    if w.len() == 0 {
        assert(apply_embedding(imgs, w) =~= Seq::<Symbol>::empty());
    } else {
        let last = w.last();
        let pre = w.drop_last();
        assert(w =~= pre + seq![last]);
        assert(word_valid(pre, (gens.len() + 1) as nat)) by {
            assert forall|k: int| 0 <= k < pre.len()
                implies symbol_valid(#[trigger] pre[k], (gens.len() + 1) as nat)
            by { assert(pre[k] == w[k]); }
        }
        assert(symbol_valid(last, (gens.len() + 1) as nat));
        lemma_apply_embedding_concat(imgs, pre, seq![last]);
        assert(apply_embedding(imgs, w)
            =~= apply_embedding(imgs, pre) + apply_embedding(imgs, seq![last]));
        lemma_stable_count_concat(inner,
            apply_embedding(imgs, pre), apply_embedding(imgs, seq![last]));
        lemma_extend_emb_symbol_stable_count(gp, gens, last);
        lemma_extend_stable_count_eq(gp, gens, pre);
        let inc: nat = if is_stable(outer, last) { 1nat } else { 0nat };
        assert(stable_count(outer, w) == stable_count(outer, pre) + inc) by {
            reveal_with_fuel(stable_count, 2);
        }
    }
}

} // verus!
