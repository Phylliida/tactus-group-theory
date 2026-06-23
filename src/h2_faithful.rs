// Layer 2 — Brick 3 (`h2.rs`) payoff: `H₂ = HNN(H₁, p)` faithfully contains `H₁` (hence `C`).
//
// AGENDA §3.2, the H₂ item ("H₂ = HNN(H₁, p | p⁻¹ tα p = tα wα(b) d) — contains C").  Under Approach
// (b) the literal `h2_pres` carries only the single `α = 0` p-relation `p⁻¹ t p = t d`; the infinite
// family (II) is derived one level up.  The HNN-faithfulness we need here is therefore the iso of the
// SINGLE p-association `(t, t·d)`, and `H₁ ↪ H₂` is then `lemma_single_hnn_base_faithful`.
//
// Both fall out of the already-verified A1 machinery (`f_free_a1.rs`) at the EMPTY index set:
//   • `recog_data(mm, n, m, [])` = `HNN(h1_base, p | p_assoc ++ family_II_assoc([]))`
//     = `HNN(h1_base, p | p_assoc)` = `h2_data(mm, n)`   (`family_II_assoc([])` is empty), and
//   • `h2_II(mm, n, m, [])` = `add_relators(h2_pres, family_II([]))` = `h2_pres(mm, n)`.
// So `lemma_recog_associations_isomorphic` / `lemma_h1_faithful_in_h2_II` specialize to the plain
// `h2_data` / `h2_pres` with no new proof work — only the empty-index identification.  (`m` is free;
// pick `m = 2n+1` to satisfy the `2n < m` side condition, which family (II) never reads when empty.)

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::equiv_in_presentation;
use crate::hnn::{HNNData, hnn_associations_isomorphic};
use crate::quotient::add_relators;
use crate::machine_group::{ModMachine, mod_machine_wf, g_m};
use crate::h1::h1_base;
use crate::h2::{h2_data, h2_pres, p_assoc};
use crate::h3_ii::{recog_data, family_II_assoc, family_II, h2_II};
use crate::f_free_a1::{lemma_recog_associations_isomorphic, lemma_h1_faithful_in_h2_II};

verus! {

/// `recog_data(mm, n, m, [])` is literally `h2_data(mm, n)`: at the empty index set the family-(II)
/// association list is empty, so the recognition datum's associations collapse to `p_assoc` alone.
proof fn lemma_recog_data_empty(mm: ModMachine, n: nat, m: nat)
    ensures
        recog_data(mm, n, m, Seq::<nat>::empty()) == h2_data(mm, n),
{
    let nk = g_m(mm).num_generators;
    let e = Seq::<nat>::empty();
    // family_II_assoc([]) = Seq::new(0, …) — empty.
    assert(family_II_assoc(mm, n, m, e).len() == 0);
    // p_assoc ++ [] =~= p_assoc.
    assert(p_assoc(nk, n) + family_II_assoc(mm, n, m, e) =~= p_assoc(nk, n));
    // bases agree (both h1_base), associations agree ⟹ the HNNData agree.
    assert(recog_data(mm, n, m, e) == h2_data(mm, n));
}

/// `h2_II(mm, n, m, [])` is literally `h2_pres(mm, n)`: the empty family (II) adds no relators.
proof fn lemma_h2_II_empty(mm: ModMachine, n: nat, m: nat)
    ensures
        h2_II(mm, n, m, Seq::<nat>::empty()) == h2_pres(mm, n),
{
    let e = Seq::<nat>::empty();
    // family_II([]) = Seq::new(0, …) — empty ⟹ add_relators returns the base unchanged.
    assert(family_II(mm, n, m, e).len() == 0);
    assert(add_relators(h2_pres(mm, n), family_II(mm, n, m, e)) == h2_pres(mm, n));
}

/// **The single p-association `(t, t·d)` is a subgroup isomorphism** —
/// `hnn_associations_isomorphic(h2_data(mm, n))`.  This is exactly A1
/// (`lemma_recog_associations_isomorphic`) at the empty index set, where `recog_data = h2_data`.
/// The `m` parameter of A1 is unused when `alphas = []`, so any `m > 2n` works; we take `m = 2n+1`.
pub proof fn lemma_h2_associations_isomorphic(mm: ModMachine, n: nat)
    requires
        mod_machine_wf(mm),
    ensures
        hnn_associations_isomorphic(h2_data(mm, n)),
{
    let e = Seq::<nat>::empty();
    let m = (2 * n + 1) as nat;
    // side conditions of A1 hold vacuously / trivially for the empty index set.
    assert(!e.contains(0nat));
    assert(e.no_duplicates());
    lemma_recog_associations_isomorphic(mm, n, m, e);       // hnn_associations_isomorphic(recog_data(…,[]))
    lemma_recog_data_empty(mm, n, m);                       // recog_data(…,[]) == h2_data
}

/// **`H₁ ↪ H₂` is faithful** — an `h1_base`-word trivial in `H₂` is already trivial in `H₁`.  Since
/// `C ⊆ H₁` (the c-generators), this is the agenda's "`H₂` contains `C`" claim.  It is
/// `lemma_h1_faithful_in_h2_II` at the empty index set (`h2_II(…,[]) = h2_pres`).
pub proof fn lemma_h1_faithful_in_h2_pres(mm: ModMachine, n: nat, w: Word)
    requires
        mod_machine_wf(mm),
        word_valid(w, h1_base(mm, n).num_generators),
        equiv_in_presentation(h2_pres(mm, n), w, empty_word()),
    ensures
        equiv_in_presentation(h1_base(mm, n), w, empty_word()),
{
    let e = Seq::<nat>::empty();
    let m = (2 * n + 1) as nat;
    assert(!e.contains(0nat));
    assert(e.no_duplicates());
    lemma_h2_II_empty(mm, n, m);                            // h2_II(…,[]) == h2_pres
    lemma_h1_faithful_in_h2_II(mm, n, m, e, w);             // descends h2_II → h1_base
}

} // verus!
