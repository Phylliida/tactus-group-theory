// Layer 2 — Brick 5 COMPLETENESS, C3.2c / F1, B2: the free-stable-letter TOWER.
//
// B1 (`f_free.rs`) proved the reusable step: a free family `gens` in `gp` extends by ONE free stable
// letter — `is_free_family(gp, gens) ⟹ is_free_family(gp ∗ ⟨s⟩, gens.push([s]))` (packaged as
// `lemma_free_family_extends`).  B2 iterates that step `j` times to build the whole H₁ free basis.
//
// Mathematics (docs/brick5-c3.2c-plan.md §4.1 "B2"): seed with F1a (`[t, x]` free in `K_M`,
// `lemma_tx_is_free_family`) and add the `b_1,…,b_n` then `d` as free stable letters.  Each addition
// is an empty-association HNN (adjoining a FREE generator), so the `j`-fold tower over `K_M` is just
// `K_M` with `j` more generators and the SAME relators — i.e. `K_M ∗ free_group(j)`.  At `j = n + 1`
// this is `K_M ∗ F(b) ∗ ⟨d⟩` (`free_group(n) ∗ free_group(1) = free_group(n+1)`), with free basis
// `[t, x, b_1, …, b_n, d]` at generator indices `0, 1, nk, nk+1, …, nk+n` (`nk = K_M`'s gen count).
//
// This module is self-contained on B1's `is_free_family` interface; it adds no new triggers to
// `f_free.rs` (separate module ⟹ separate Z3/Lean context, and a warm `f_free` cache survives).
// The h1_base connection (B3: kill the `c`'s + reindex) is the NEXT arc and lives elsewhere.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, lemma_g_m_valid,
    lemma_g_m_num_generators, lemma_hnn_presentation_valid};
use crate::hnn::{HNNData, hnn_presentation, hnn_relators};
use crate::higman_operations::free_group;
use crate::free_product::{free_product, shift_relators};
use crate::f_free::{free_stable_data, stable_emb, is_free_family,
    lemma_free_stable_data_valid, lemma_free_family_extends, lemma_tx_is_free_family,
    lemma_stable_emb_index};

verus! {

// ----------------------------------------------------------------------------
// The tower presentation and the tower family.
// ----------------------------------------------------------------------------

/// The `j`-fold empty-association HNN tower over `gp`: adjoin `j` free stable letters.
/// `free_stable_tower(gp, 0) = gp`; each step is `hnn_presentation(free_stable_data(·))`.
pub open spec fn free_stable_tower(gp: Presentation, j: nat) -> Presentation
    decreases j,
{
    if j == 0 {
        gp
    } else {
        hnn_presentation(free_stable_data(free_stable_tower(gp, (j - 1) as nat)))
    }
}

/// The family obtained from `gens` by adjoining `j` free stable letters (each `stable_emb` appends
/// the new top generator `Gen(tower.num_generators)`).
pub open spec fn free_stable_family(gp: Presentation, gens: Seq<Word>, j: nat) -> Seq<Word>
    decreases j,
{
    if j == 0 {
        gens
    } else {
        stable_emb(free_stable_tower(gp, (j - 1) as nat), free_stable_family(gp, gens, (j - 1) as nat))
    }
}

// ----------------------------------------------------------------------------
// Closed form of the tower presentation: `j` more generators, the SAME relators.
// ----------------------------------------------------------------------------

/// **Tower closed form.** Adjoining free stable letters never adds a relator (the empty-association
/// HNN has no HNN relators), so the tower is `gp` with `j` extra generators and `gp`'s relators.
pub proof fn lemma_free_stable_tower_closed(gp: Presentation, j: nat)
    ensures
        free_stable_tower(gp, j).num_generators == (gp.num_generators + j) as nat,
        free_stable_tower(gp, j).relators == gp.relators,
    decreases j,
{
    if j == 0 {
    } else {
        let jm = (j - 1) as nat;
        lemma_free_stable_tower_closed(gp, jm);
        let p = free_stable_tower(gp, jm);
        let data = free_stable_data(p);
        // num_generators: p.num_generators + 1 = (gp.num_generators + jm) + 1 = gp.num_generators + j.
        assert(free_stable_tower(gp, j).num_generators == p.num_generators + 1);
        // relators: p.relators + hnn_relators(data), and the HNN relator block is empty.
        assert(data.associations.len() == 0);
        assert(hnn_relators(data) =~= Seq::<Word>::empty());
        assert(free_stable_tower(gp, j).relators =~= p.relators);
    }
}

/// The tower is a valid presentation (each empty-association HNN over a valid base is valid).
pub proof fn lemma_free_stable_tower_valid(gp: Presentation, j: nat)
    requires
        presentation_valid(gp),
    ensures
        presentation_valid(free_stable_tower(gp, j)),
    decreases j,
{
    if j == 0 {
    } else {
        let jm = (j - 1) as nat;
        lemma_free_stable_tower_valid(gp, jm);
        let p = free_stable_tower(gp, jm);
        lemma_free_stable_data_valid(p);
        lemma_hnn_presentation_valid(free_stable_data(p));
    }
}

/// **Tower = free product with a free group.** `free_stable_tower(gp, j) == free_product(gp,
/// free_group(j))`: same generator count (`gp.num_generators + j`) and same relators (`gp`'s, since
/// `free_group(j)` has none, so the shifted block is empty).  Generalizes
/// `lemma_free_stable_is_free_product` (`j = 1`) and `lemma_free_stable_of_free_group`.
pub proof fn lemma_free_stable_tower_is_free_product(gp: Presentation, j: nat)
    ensures
        free_stable_tower(gp, j) == free_product(gp, free_group(j)),
{
    lemma_free_stable_tower_closed(gp, j);
    let lhs = free_stable_tower(gp, j);
    let rhs = free_product(gp, free_group(j));
    // num_generators: both gp.num_generators + j.
    assert(rhs.num_generators == gp.num_generators + j);
    // relators: free_group(j) has empty relators ⟹ the shifted block is empty.
    assert(free_group(j).relators =~= Seq::<Word>::empty());
    assert(shift_relators(free_group(j).relators, gp.num_generators) =~= Seq::<Word>::empty());
    assert(rhs.relators =~= gp.relators);
    assert(lhs.num_generators == rhs.num_generators);
    assert(lhs.relators == rhs.relators);
    assert(lhs == rhs);
}

// ----------------------------------------------------------------------------
// B2 — the tower induction: a free family extends by `j` free stable letters.
// ----------------------------------------------------------------------------

/// **B2 (the meat).** A free family `gens` in `gp` stays free after adjoining `j` free stable
/// letters: `free_stable_family(gp, gens, j)` is a free family in `free_stable_tower(gp, j)`.
/// Induction on `j`, each step the single-letter B1 step `lemma_free_family_extends`.
pub proof fn lemma_free_stable_tower_extends(gp: Presentation, gens: Seq<Word>, j: nat)
    requires
        presentation_valid(gp),
        is_free_family(gp, gens),
    ensures
        is_free_family(free_stable_tower(gp, j), free_stable_family(gp, gens, j)),
    decreases j,
{
    if j == 0 {
    } else {
        let jm = (j - 1) as nat;
        lemma_free_stable_tower_extends(gp, gens, jm);
        let p = free_stable_tower(gp, jm);
        let fam = free_stable_family(gp, gens, jm);
        // p is valid; the IH gives is_free_family(p, fam).
        lemma_free_stable_tower_valid(gp, jm);
        // single-letter step: is_free_family(hnn_presentation(free_stable_data(p)), stable_emb(p, fam)).
        lemma_free_family_extends(p, fam);
        // = is_free_family(free_stable_tower(gp, j), free_stable_family(gp, gens, j)).
    }
}

// ----------------------------------------------------------------------------
// Closed form of the tower family: `gens ++ [Gen(nk), Gen(nk+1), …, Gen(nk+j-1)]`.
// ----------------------------------------------------------------------------

/// The `i`-th adjoined free stable letter (0-indexed) is the singleton word `[Gen(gp.num_generators + i)]`.
pub open spec fn free_stable_letter(nk: nat, i: int) -> Word {
    seq![Symbol::Gen((nk + i) as nat)]
}

/// **Tower family closed form.** Each step appends the new top generator, and (by the tower closed
/// form) the `j`-th step's base has `gp.num_generators + (j-1)` generators, so the appended letters
/// are `Gen(gp.num_generators), …, Gen(gp.num_generators + j - 1)` in order.
pub proof fn lemma_free_stable_family_closed(gp: Presentation, gens: Seq<Word>, j: nat)
    ensures
        free_stable_family(gp, gens, j)
            =~= gens + Seq::new(j, |i: int| free_stable_letter(gp.num_generators, i)),
    decreases j,
{
    let nk = gp.num_generators;
    if j == 0 {
        assert(Seq::new(0nat, |i: int| free_stable_letter(nk, i)) =~= Seq::<Word>::empty());
    } else {
        let jm = (j - 1) as nat;
        lemma_free_stable_family_closed(gp, gens, jm);
        let p = free_stable_tower(gp, jm);
        let fam = free_stable_family(gp, gens, jm);
        lemma_stable_emb_index(p, fam);
        lemma_free_stable_tower_closed(gp, jm);
        // the new generator is Gen(p.num_generators) = Gen(nk + jm).
        assert(p.num_generators == nk + jm);
        let new_letter = seq![Symbol::Gen(p.num_generators)];
        assert(new_letter =~= free_stable_letter(nk, jm as int));
        // free_stable_family(gp,gens,j) = fam.push(new_letter); fam =~= gens + tail(jm).
        let tail_jm = Seq::new(jm, |i: int| free_stable_letter(nk, i));
        let tail_j = Seq::new(j, |i: int| free_stable_letter(nk, i));
        assert(fam =~= gens + tail_jm);
        // (gens + tail_jm).push(new_letter) = gens + (tail_jm.push(new_letter)) = gens + tail_j.
        assert(tail_jm.push(new_letter) =~= tail_j) by {
            assert(tail_jm.push(new_letter).len() == j);
            assert forall|i: int| #![trigger tail_j[i]] 0 <= i < j
                implies tail_jm.push(new_letter)[i] == tail_j[i]
            by {
                if i < jm {
                    assert(tail_jm.push(new_letter)[i] == tail_jm[i]);
                } else {
                    assert(i == jm);
                    assert(tail_jm.push(new_letter)[i] == new_letter);
                    assert(tail_j[i] == free_stable_letter(nk, i));
                }
            }
        }
        assert(free_stable_family(gp, gens, j) =~= (gens + tail_jm).push(new_letter));
        assert((gens + tail_jm).push(new_letter) =~= gens + tail_jm.push(new_letter));
    }
}

// ----------------------------------------------------------------------------
// B2 headline: `[t, x, b_1, …, b_n, d]` is free in `K_M ∗ F(b) ∗ ⟨d⟩`.
// ----------------------------------------------------------------------------

/// The seed family `[t = Gen(0), x = Gen(1)]`.
pub open spec fn tx_family() -> Seq<Word> {
    seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)]]
}

/// **B2 (headline).** `[t, x, b_1, …, b_n, d] = free_stable_family(g_m(mm), [t,x], n+1)` is a FREE
/// family in the tower `free_stable_tower(g_m(mm), n+1) == K_M ∗ free_group(n+1) = K_M ∗ F(b) ∗ ⟨d⟩`.
/// Seed = F1a (`lemma_tx_is_free_family`); iterate B2's `lemma_free_stable_tower_extends` `n+1` times.
pub proof fn lemma_txbd_free_in_tower(mm: ModMachine, n: nat)
    requires
        mod_machine_wf(mm),
    ensures
        is_free_family(
            free_stable_tower(g_m(mm), (n + 1) as nat),
            free_stable_family(g_m(mm), tx_family(), (n + 1) as nat),
        ),
        free_stable_tower(g_m(mm), (n + 1) as nat) == free_product(g_m(mm), free_group((n + 1) as nat)),
{
    lemma_g_m_valid(mm);
    lemma_tx_is_free_family(mm);
    assert(is_free_family(g_m(mm), tx_family()));
    lemma_free_stable_tower_extends(g_m(mm), tx_family(), (n + 1) as nat);
    lemma_free_stable_tower_is_free_product(g_m(mm), (n + 1) as nat);
}

/// **Generator layout of the B2 family.** The tower family at `j = n + 1` is
/// `[t, x] ++ [Gen(nk), Gen(nk+1), …, Gen(nk+n)]` (`nk = g_m(mm).num_generators = 4 + |quads|`),
/// i.e. `t, x` at `0, 1`, the `b_j` at `nk, …, nk+n-1`, and `d` at `nk + n`.  This pins the exact
/// indices the B3 (kill-`c` + reindex to `h1_base`) connection consumes.
pub proof fn lemma_txbd_family_layout(mm: ModMachine, n: nat)
    requires
        mod_machine_wf(mm),
    ensures
        free_stable_family(g_m(mm), tx_family(), (n + 1) as nat)
            =~= tx_family()
                + Seq::new((n + 1) as nat,
                    |i: int| free_stable_letter(g_m(mm).num_generators, i)),
{
    lemma_free_stable_family_closed(g_m(mm), tx_family(), (n + 1) as nat);
}

} // verus!
