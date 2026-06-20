// Layer 2 — Brick 5 (`higman_consequences.rs`): the Higman payoff.
//
// The BRIDGE THEOREM (soundness direction this session):
//
//     (α,0) ∈ H₀(M)   ⟹   h3_pres(mm,n,m) ⊢ w_α(c) = 1.
//
// This is Cohen's "(II),(III) are consequences of the finite set (I)" (book p.281): the
// recursively-presented relations of `C = ⟨c;S⟩` hold in the FINITE presentation `h3_pres` as
// derived theorems. Combined with Layer 1 (`lemma_theorem1`) it realizes the c.e. set
// `S = { w_α(c) : (α,0)∈H₀(M) }` as the word problem of `H₃` among the c-generators.
//
// See `docs/brick5-plan.md` for the full decomposition and the (deferred) completeness routing.
//
// Sub-brick 0 (this file, first): the LIFTING HELPERS. Every relation we use lives at some tower
// level (`h2_pres`, `h3_upto(l)`); we lift it up to `h3_pres` via repeated `lemma_base_embeds_in_hnn`
// (an HNN base embeds in its extension — no validity / iso hypothesis needed).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::machine_group::*;
use crate::word_numbering::*;
use crate::layout::*;
use crate::h1::*;
use crate::h2::*;
use crate::h3::*;

verus! {

// ----------------------------------------------------------------------------
// Generic commutation algebra.  `commutes(p, a, b)` := `a·b ≡ b·a` in `p`.
// Reused in the `w_bc` split (b-letters past c-words) and in (II) (p past w_α(a)).
// ----------------------------------------------------------------------------

/// `a` and `b` commute in presentation `p`.
pub open spec fn commutes(p: Presentation, a: Word, b: Word) -> bool {
    equiv_in_presentation(p, a + b, b + a)
}

/// Everything commutes with the empty word.
pub proof fn lemma_commutes_empty_right(p: Presentation, a: Word)
    ensures commutes(p, a, empty_word()),
{
    assert(a + empty_word() =~= a);
    assert(empty_word() + a =~= a);
    lemma_equiv_refl(p, a);
}

/// Commutation is symmetric (needs validity of `a·b` for the symmetry of `≡`).
pub proof fn lemma_commutes_sym(p: Presentation, a: Word, b: Word)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        commutes(p, a, b),
    ensures commutes(p, b, a),
{
    lemma_concat_word_valid(a, b, p.num_generators);
    lemma_equiv_symmetric(p, a + b, b + a);
}

/// `a` commutes with `b₁` and `b₂` ⟹ `a` commutes with `b₁·b₂`.
pub proof fn lemma_commutes_concat_right(p: Presentation, a: Word, b1: Word, b2: Word)
    requires
        commutes(p, a, b1),
        commutes(p, a, b2),
    ensures commutes(p, a, b1 + b2),
{
    // a·(b1·b2) = (a·b1)·b2 ≡ (b1·a)·b2 = b1·(a·b2) ≡ b1·(b2·a) = (b1·b2)·a.
    lemma_equiv_concat_left(p, a + b1, b1 + a, b2);     // (a·b1)·b2 ≡ (b1·a)·b2
    assert(concat(a + b1, b2) =~= a + (b1 + b2));
    assert(concat(b1 + a, b2) =~= b1 + (a + b2));
    lemma_equiv_concat_right(p, b1, a + b2, b2 + a);     // b1·(a·b2) ≡ b1·(b2·a)
    assert(concat(b1, a + b2) =~= b1 + (a + b2));
    assert(concat(b1, b2 + a) =~= (b1 + b2) + a);
    lemma_equiv_transitive(p, a + (b1 + b2), b1 + (a + b2), (b1 + b2) + a);
    assert(a + (b1 + b2) =~= a + (b1 + b2));
}

/// If `a` commutes with `b`, it commutes with `b⁻¹` (valid `a`,`b`; conjugate-and-cancel).
pub proof fn lemma_commutes_inv_right(p: Presentation, a: Word, b: Word)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        commutes(p, a, b),
    ensures commutes(p, a, inverse_word(b)),
{
    let ng = p.num_generators;
    let bi = inverse_word(b);
    lemma_inverse_word_valid(b, ng);
    // From a·b ≡ b·a, sandwich by b⁻¹ on both sides:  b⁻¹·(a·b)·b⁻¹ ≡ b⁻¹·(b·a)·b⁻¹.
    lemma_equiv_concat_left(p, a + b, b + a, bi);          // (a·b)·b⁻¹ ≡ (b·a)·b⁻¹
    lemma_equiv_concat_right(p, bi, (a + b) + bi, (b + a) + bi);  // E2: lhs ≡ rhs
    let lhs = bi + ((a + b) + bi);
    let rhs = bi + ((b + a) + bi);
    assert(equiv_in_presentation(p, lhs, rhs));

    // LHS = b⁻¹·a·(b·b⁻¹) ≡ b⁻¹·a  (b·b⁻¹ ≡ ε).
    lemma_word_inverse_right(p, b);                        // b·b⁻¹ ≡ ε
    lemma_equiv_concat_right(p, bi + a, b + bi, empty_word());  // (b⁻¹a)(b b⁻¹) ≡ (b⁻¹a)·ε
    assert(lhs =~= (bi + a) + (b + bi));
    assert((bi + a) + empty_word() =~= bi + a);
    assert(equiv_in_presentation(p, lhs, bi + a));         // E3 (terms collapsed by the =~= above)

    // RHS = (b⁻¹·b)·a·b⁻¹ ≡ a·b⁻¹  (b⁻¹·b ≡ ε).
    lemma_word_inverse_left(p, b);                         // b⁻¹·b ≡ ε
    lemma_equiv_concat_left(p, bi + b, empty_word(), a + bi);   // (b⁻¹b)(a b⁻¹) ≡ ε·(a b⁻¹)
    assert(rhs =~= (bi + b) + (a + bi));
    assert(empty_word() + (a + bi) =~= a + bi);
    assert(equiv_in_presentation(p, rhs, a + bi));         // E4

    // chain:  b⁻¹·a ≡ lhs ≡ rhs ≡ a·b⁻¹, then symmetry gives a·b⁻¹ ≡ b⁻¹·a.
    lemma_concat_word_valid(bi, a, ng);
    lemma_equiv_symmetric(p, lhs, bi + a);                 // b⁻¹·a ≡ lhs
    lemma_equiv_transitive(p, bi + a, lhs, rhs);           // b⁻¹·a ≡ rhs
    lemma_equiv_transitive(p, bi + a, rhs, a + bi);        // b⁻¹·a ≡ a·b⁻¹
    lemma_equiv_symmetric(p, bi + a, a + bi);              // a·b⁻¹ ≡ b⁻¹·a  = commutes(a, b⁻¹)
}

// ----------------------------------------------------------------------------
// Sub-brick 0 — lifting equivalences up the iterated HNN tower to h3_pres.
// ----------------------------------------------------------------------------

/// One rung: an equivalence in `h3_upto(l)` lifts to `h3_upto(l+1)` (the `a_{l+1}` HNN whose
/// base is exactly `h3_upto(l)`).
pub proof fn lemma_h3_upto_step_embeds(mm: ModMachine, n: nat, m: nat, l: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_upto(mm, n, m, (l + 1) as nat), w1, w2),
{
    let data = HNNData {
        base: h3_upto(mm, n, m, l),
        associations: phi_assoc(g_m(mm).num_generators, n, m, (l + 1) as nat),
    };
    // h3_upto(l+1) = hnn_presentation(data), and data.base = h3_upto(l).
    assert(h3_upto(mm, n, m, (l + 1) as nat) == hnn_presentation(data));
    lemma_base_embeds_in_hnn(data, w1, w2);
}

/// Climb from level `l` up to level `hi` (`l ≤ hi ≤ 2n`): equivalence is preserved up the tower.
pub proof fn lemma_h3_upto_climbs(mm: ModMachine, n: nat, m: nat, l: nat, hi: nat, w1: Word, w2: Word)
    requires
        l <= hi,
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_upto(mm, n, m, hi), w1, w2),
    decreases hi - l,
{
    if l == hi {
    } else {
        lemma_h3_upto_step_embeds(mm, n, m, l, w1, w2);
        lemma_h3_upto_climbs(mm, n, m, (l + 1) as nat, hi, w1, w2);
    }
}

/// Top rung: an equivalence in `h3_upto(2n)` lifts to `h3_pres` (the `k` HNN whose base is
/// `h3_upto(2n)`).
pub proof fn lemma_h3_upto_top_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h3_upto(mm, n, m, (2 * n) as nat), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    let data = HNNData {
        base: h3_upto(mm, n, m, (2 * n) as nat),
        associations: psi_assoc(mm, n),
    };
    assert(h3_pres(mm, n, m) == hnn_presentation(data));
    lemma_base_embeds_in_hnn(data, w1, w2);
}

/// **Lift from any tower level `l ≤ 2n` to `h3_pres`.**
pub proof fn lemma_h3_upto_in_h3(mm: ModMachine, n: nat, m: nat, l: nat, w1: Word, w2: Word)
    requires
        l <= 2 * n,
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    lemma_h3_upto_climbs(mm, n, m, l, (2 * n) as nat, w1, w2);
    lemma_h3_upto_top_in_h3(mm, n, m, w1, w2);
}

/// **Lift from `h2_pres` to `h3_pres`** (= the `l = 0` base of the tower).
pub proof fn lemma_h2_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h2_pres(mm, n), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    // h3_upto(0) == h2_pres.
    assert(h3_upto(mm, n, m, 0) == h2_pres(mm, n));
    lemma_h3_upto_in_h3(mm, n, m, 0, w1, w2);
}

/// **Lift from `h1_base` to `h3_pres`** (through the `p` HNN, then the tower). `h2_pres` is the
/// `p`-HNN over `h1_base`, so an `h1_base` equivalence first lifts to `h2_pres`.
pub proof fn lemma_h1_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h1_base(mm, n), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    // h2_pres = hnn_presentation(h2_data), h2_data.base = h1_base.
    let data = h2_data(mm, n);
    assert(h2_pres(mm, n) == hnn_presentation(data));
    assert(data.base == h1_base(mm, n));
    lemma_base_embeds_in_hnn(data, w1, w2);
    lemma_h2_in_h3(mm, n, m, w1, w2);
}

} // verus!
