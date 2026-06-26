// Layer 2 — Cohen §1 assembly, brick CS-7: transport the faithfulness to the printable group.
//
// `docs/cohen-section1-assembly-plan.md` §3/§5 (the second half of CS-6).  CS-6's `lemma_C_faithful`
// proves `C ↪ H₃` faithfulness over the PREDICATE base `h3_pred` (whose infinite relator families
// make the a_i/k associations genuine isos).  The actual deliverable group is the **printable finite**
// `h3_pres` (Cohen's finite set (I)).  This brick transports faithfulness to it:
//
//     equiv(h3_pres, w, ε)  ⟹  equiv(c_pred, w, ε)        (w a pure-c word)
//
// via the chain  `equiv(h3_pres, w) ⟹ equiv_pred(h3_pred, w) ⟹ equiv_pred(c_pred, w)`, where the
// first arrow is the **easy direction**: the finite `h3_pres` has FEWER relators than the predicate
// `h3_pred` (only the β=0 p-relation, vs the full family (II) for all β, plus S), so every finite
// relator is a predicate relator/consequence.  Concretely:
//
//   * the two towers are structurally aligned — `h3_upto(0) = h2_pres`, both use the SAME
//     `phi_assoc`/`psi_assoc`, and `hnn_relator` ≡ `hnn_relator_pred` once the generator counts match;
//   * the ONLY content is the base p-relator `hnn_relator(h2_data,0) = p⁻¹·t·p·(td)⁻¹` equalling
//     `family_II_relator(mm,n,m,0)` (config_word(0,0)=t, w_b(0)=ε), accepted by `is_family_ii`
//     (witness β=0, `numbers_word(n,m,0)`);
//   * the rest is a structural induction (relator inclusion up the tower) + the existing generic
//     finite→predicate lift `lemma_pred_equiv_from_finite`.
//
// NOTE this transport needs NEITHER `lemma_II` NOR S-soundness (those are the *other* direction —
// "predicate relators are consequences of finite (I)" = the groups-are-equal claim).  Additive (new
// module + one lib.rs line); no regression.

use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::presentation::equiv_in_presentation;
use crate::pred_presentation::equiv_in_pred_presentation;
use crate::hnn::{HNNData, hnn_relator, hnn_relators, stable_letter, stable_letter_inv};
use crate::pred_hnn::{PredHNNData, hnn_relator_pred, hnn_extra_relator_pred,
    stable_letter_pred, stable_letter_inv_pred};
use crate::machine_group::{ModMachine, mod_machine_wf, mm_terminal, g_m, lemma_g_m_num_generators,
    config_word, lemma_config_word_zero};
use crate::layout::{h2_num_gens, p_idx, d_idx, b_base};
use crate::word_numbering::{numbers_word, w_b};
use crate::h1::comm_relators;
use crate::h2::{h2_pres, h2_data, td_word, p_assoc, lemma_h2_stable_letter};
use crate::h3::{h3_pres, h3_upto, phi_assoc, psi_assoc, lemma_h3_upto_num_generators,
    lemma_h3_num_generators};
use crate::h3_ii::{family_II_relator, family_II_lhs, family_II_rhs};
use crate::cohen_h2::{h2_pred, s_relators_valid, s_realizes, is_c_word, lemma_c_word_valid};
use crate::cohen_h3::{h3_pred, h3_pred_upto, lemma_h3_pred_upto_num_generators,
    lemma_h3_pred_num_generators};
use crate::cohen_cs5::lemma_pred_equiv_from_finite;
use crate::cohen_cs6::lemma_C_faithful;
use crate::cohen_retraction::c_pred;

verus! {

// ============================================================================
// Generator counts of the finite and predicate towers agree at every level
// ============================================================================

/// `h3_upto(l)` (finite) and `h3_pred_upto(l)` (predicate) have the same generator count
/// (`h2_num_gens(nk,n) + l`, `nk = g_m.num = 4+|quads|`).  Needed so the HNN stable letters
/// `Gen(base.num_generators)` coincide between the two towers, making the relators identical.
pub proof fn lemma_h3_upto_gens_match(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat,
)
    ensures
        h3_upto(mm, n, m, l).num_generators == h3_pred_upto(mm, n, m, is_S, l).num_generators,
{
    lemma_g_m_num_generators(mm);                          // g_m.num == 4+|quads|
    lemma_h3_upto_num_generators(mm, n, m, l);             // h2_num_gens(4+|quads|,n) + l
    lemma_h3_pred_upto_num_generators(mm, n, m, is_S, l);  // h2_num_gens(g_m.num,n) + l
}

// ============================================================================
// A single HNN relator is identical between a finite and a predicate level
// ============================================================================

/// When a finite HNN datum and a predicate HNN datum share the same base generator count and the
/// same association list, their `j`-th HNN relators coincide (both = `t⁻¹·a_j·t·b_j⁻¹` with the
/// same stable letter `t = Gen(base.num_generators)`).
pub proof fn lemma_hnn_relator_match(dataf: HNNData, datap: PredHNNData, j: int)
    requires
        dataf.base.num_generators == datap.base.num_generators,
        dataf.associations == datap.associations,
        0 <= j < dataf.associations.len(),
    ensures
        hnn_relator(dataf, j) == hnn_relator_pred(datap, j),
{
    // stable letters agree: Gen/Inv(base.num_generators) on both sides.
    assert(stable_letter(dataf) == stable_letter_pred(datap));
    assert(stable_letter_inv(dataf) == stable_letter_inv_pred(datap));
    let (a_j, b_j) = dataf.associations[j];
    assert(datap.associations[j] == (a_j, b_j));
    assert(hnn_relator(dataf, j)
        =~= Seq::new(1, |_k: int| stable_letter_inv(dataf)) + a_j
            + Seq::new(1, |_k: int| stable_letter(dataf)) + inverse_word(b_j));
    assert(hnn_relator_pred(datap, j)
        =~= Seq::new(1, |_k: int| stable_letter_inv_pred(datap)) + a_j
            + Seq::new(1, |_k: int| stable_letter_pred(datap)) + inverse_word(b_j));
}

// ============================================================================
// The base p-relator of the finite tower is family-(II) at β=0
// ============================================================================

/// The single p-HNN relator of the finite `h2_pres` — `hnn_relator(h2_data,0) = p⁻¹·t·p·(td)⁻¹` —
/// is exactly `family_II_relator(mm,n,m,0)`: at β=0, `config_word(0,0) = t = Gen(0)` and `w_b(0)=ε`,
/// so the rhs `t·w_0(b)·d` collapses to `t·d = td_word`, the finite p-association's `b`-word.
pub proof fn lemma_p_relator_is_family_ii(mm: ModMachine, n: nat, m: nat)
    ensures
        hnn_relator(h2_data(mm, n), 0) == family_II_relator(mm, n, m, 0),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    lemma_h2_stable_letter(mm, n);                 // stable_letter(h2_data) == Gen(p_idx(nk,n))
    lemma_config_word_zero();                      // config_word(0,0) =~= [Gen(0)]

    // concretize the finite p-association: (a_0, b_0) = ([t], td_word).
    assert(h2_data(mm, n).associations == p_assoc(nk, n));
    assert(h2_data(mm, n).associations[0] == (seq![Symbol::Gen(0)], td_word(nk, n)));

    // the two zero-case collapses:  config_word(0,0) = [Gen(0)],  w_b(...,0) = ε.
    assert(config_word(0, 0) == seq![Symbol::Gen(0)]);            // from lemma_config_word_zero (=~= ⟹ ==)
    assert(w_b(b_base(nk, n), n, m, 0) == empty_word());          // w_c alpha==0 branch

    // rhs(0) = [Gen(0)] + ε + [Gen(d_idx)]  collapses to td_word = [Gen(0), Gen(d_idx)].
    assert(family_II_rhs(mm, n, m, 0) =~= td_word(nk, n));
    // lhs(0) = [Inv(p_idx)] + [Gen(0)] + [Gen(p_idx)].
    assert(family_II_lhs(mm, n, 0)
        =~= seq![Symbol::Inv(p_idx(nk, n))] + seq![Symbol::Gen(0)] + seq![Symbol::Gen(p_idx(nk, n))]);

    assert(hnn_relator(h2_data(mm, n), 0) =~= family_II_relator(mm, n, m, 0));
}

// ============================================================================
// Relator inclusion: h3_pred_upto(l) accepts every relator of h3_upto(l)
// ============================================================================

/// **Base case.**  `h2_pred` accepts every relator of the finite `h2_pres`
/// (`= h3_upto(0)`/`h3_pred_upto(0)`): the H₁ base relators (K_M ∪ comm) are directly h2_pred
/// relator classes, and the single p-relation is `family_II_relator(0)` (accepted by `is_family_ii`).
pub proof fn lemma_h2_pres_rel_incl(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, i: int,
)
    requires
        0 <= i < h2_pres(mm, n).relators.len(),
    ensures
        (h2_pred(mm, n, m, is_S).relators)(h2_pres(mm, n).relators[i]),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let gr = g_m(mm).relators;
    let cr = comm_relators(nk, n);
    let hr = hnn_relators(h2_data(mm, n));
    // h2_pres.relators = h1_base.relators ++ hnn_relators(h2_data) = (gr ++ cr) ++ hr.
    assert(h2_pres(mm, n).relators == (gr + cr) + hr);
    let r = h2_pres(mm, n).relators[i];
    if i < gr.len() {
        assert(r == gr[i]);
        assert(gr.contains(r));                    // witness i — K_M relator class
    } else if i < gr.len() + cr.len() {
        let jj = i - gr.len();
        assert(r == cr[jj]);
        assert(cr.contains(r));                    // witness jj — comm relator class
    } else {
        // i == gr.len()+cr.len(): the single p-relator = family_II_relator(0).
        assert(hr.len() == 1);
        assert(r == hr[0]);
        assert(r == hnn_relator(h2_data(mm, n), 0));
        lemma_p_relator_is_family_ii(mm, n, m);    // r == family_II_relator(mm,n,m,0)
        assert(numbers_word(n, m, 0));             // β=0 qualifies
        // is_family_ii(mm,n,m,r): exists β=0 with numbers_word ∧ r == family_II_relator(β).
    }
}

/// **Inductive relator inclusion up the a-tower.**  `h3_pred_upto(l)` accepts every relator of the
/// finite `h3_upto(l)` (0 ≤ l ≤ 2n).  Downward on `l`: the finite relator Seq is
/// `h3_upto(l-1).relators ++ hnn_relators(level l)`; a base-relator index recurses (IH ⟹ the first
/// disjunct of `hnn_all_relator_pred`), an HNN-relator index matches `hnn_relator_pred` (the second
/// disjunct, via `lemma_hnn_relator_match` + the gen-count agreement).
pub proof fn lemma_h3_upto_rel_incl(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, l: nat, i: int,
)
    requires
        l <= 2 * n,
        0 <= i < h3_upto(mm, n, m, l).relators.len(),
    ensures
        (h3_pred_upto(mm, n, m, is_S, l).relators)(h3_upto(mm, n, m, l).relators[i]),
    decreases l,
{
    if l == 0 {
        lemma_h2_pres_rel_incl(mm, n, m, is_S, i);
    } else {
        let nk = g_m(mm).num_generators;
        let prevf = h3_upto(mm, n, m, (l - 1) as nat);
        let prevp = h3_pred_upto(mm, n, m, is_S, (l - 1) as nat);
        let assoc = phi_assoc(nk, n, m, l);
        let dataf = HNNData { base: prevf, associations: assoc };
        let datap = PredHNNData { base: prevp, associations: assoc };
        let r = h3_upto(mm, n, m, l).relators[i];
        assert(h3_upto(mm, n, m, l).relators == prevf.relators + hnn_relators(dataf));
        if i < prevf.relators.len() {
            assert(r == prevf.relators[i]);
            lemma_h3_upto_rel_incl(mm, n, m, is_S, (l - 1) as nat, i);   // IH: prevp accepts r
            // ⟹ (datap.base.relators)(r) = first disjunct of hnn_all_relator_pred(datap, r).
        } else {
            let j = i - prevf.relators.len();
            assert(r == hnn_relators(dataf)[j]);
            assert(r == hnn_relator(dataf, j));
            lemma_h3_upto_gens_match(mm, n, m, is_S, (l - 1) as nat);    // prevf.num == prevp.num
            lemma_hnn_relator_match(dataf, datap, j);                    // r == hnn_relator_pred(datap, j)
            assert(hnn_extra_relator_pred(datap, r));                    // witness j — second disjunct
        }
    }
}

/// **Top level (+k).**  `h3_pred` accepts every relator of the finite `h3_pres`.  Same step argument
/// as `lemma_h3_upto_rel_incl`, with the base = `h3_upto(2n)`/`h3_pred_upto(2n)` and the k-association
/// `psi_assoc`.
pub proof fn lemma_h3_pres_rel_incl(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, i: int,
)
    requires
        0 <= i < h3_pres(mm, n, m).relators.len(),
    ensures
        (h3_pred(mm, n, m, is_S).relators)(h3_pres(mm, n, m).relators[i]),
{
    let nk = g_m(mm).num_generators;
    let prevf = h3_upto(mm, n, m, (2 * n) as nat);
    let prevp = h3_pred_upto(mm, n, m, is_S, (2 * n) as nat);
    let assoc = psi_assoc(mm, n);
    let dataf = HNNData { base: prevf, associations: assoc };
    let datap = PredHNNData { base: prevp, associations: assoc };
    let r = h3_pres(mm, n, m).relators[i];
    assert(h3_pres(mm, n, m).relators == prevf.relators + hnn_relators(dataf));
    if i < prevf.relators.len() {
        assert(r == prevf.relators[i]);
        lemma_h3_upto_rel_incl(mm, n, m, is_S, (2 * n) as nat, i);   // IH-analog: prevp accepts r
    } else {
        let j = i - prevf.relators.len();
        assert(r == hnn_relator(dataf, j));
        lemma_h3_upto_gens_match(mm, n, m, is_S, (2 * n) as nat);
        lemma_hnn_relator_match(dataf, datap, j);
        assert(hnn_extra_relator_pred(datap, r));
    }
}

// ============================================================================
// The transport, and the printable-group faithfulness headline
// ============================================================================

/// **The transport** (the easy direction).  A word trivial in the finite printable `h3_pres` is
/// trivial in the predicate `h3_pred` — every finite relator is a predicate relator (above), so the
/// generic finite→predicate lift `lemma_pred_equiv_from_finite` applies.
pub proof fn lemma_h3_pres_to_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
)
    requires
        equiv_in_presentation(h3_pres(mm, n, m), w, empty_word()),
    ensures
        equiv_in_pred_presentation(h3_pred(mm, n, m, is_S), w, empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    lemma_h3_num_generators(mm, n, m);                  // h3_pres.num == h3_num_gens(nk,n)
    lemma_h3_pred_num_generators(mm, n, m, is_S);       // h3_pred.num == h2_num_gens(nk,n)+2n+1
    // h3_num_gens(nk,n) = nk+4n+3 = (nk+2n+2)+2n+1 = h2_num_gens(nk,n)+2n+1 — gens agree.
    assert(h3_pres(mm, n, m).num_generators <= h3_pred(mm, n, m, is_S).num_generators);
    assert forall|i: int| 0 <= i < h3_pres(mm, n, m).relators.len()
        implies (h3_pred(mm, n, m, is_S).relators)(#[trigger] h3_pres(mm, n, m).relators[i]) by {
        lemma_h3_pres_rel_incl(mm, n, m, is_S, i);
    }
    lemma_pred_equiv_from_finite(h3_pres(mm, n, m), h3_pred(mm, n, m, is_S), w, empty_word());
}

/// **CS-7 — Layer-2 completeness for the PRINTABLE group `H₃ = h3_pres`.**  A pure-c word `w` trivial
/// in the finite, printable `h3_pres` (Cohen's finite set (I)) is trivial in `C = ⟨c;S⟩`.  This is
/// the faithfulness of the Higman embedding `C ↪ H₃` for the actual deliverable group: the transport
/// `lemma_h3_pres_to_pred` lands `w` in the predicate `h3_pred`, then CS-6's `lemma_C_faithful`
/// lands it in `C`.
pub proof fn lemma_C_faithful_printable(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
        s_realizes(is_S, mm, n, m),
        is_c_word(g_m(mm).num_generators, n, w),
        equiv_in_presentation(h3_pres(mm, n, m), w, empty_word()),
    ensures
        equiv_in_pred_presentation(c_pred(mm, n, m, is_S), w, empty_word()),
{
    let nk = g_m(mm).num_generators;
    lemma_c_word_valid(nk, n, w);
    lemma_h3_pres_to_pred(mm, n, m, is_S, w);       // equiv_pred(h3_pred, w, ε)
    lemma_C_faithful(mm, n, m, is_S, w);            // equiv_pred(c_pred, w, ε)
}

} // verus!
