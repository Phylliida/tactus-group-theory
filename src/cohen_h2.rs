// Layer 2 — Cohen §1 assembly, brick CS-1: the PREDICATE base `H₂`.
//
// `docs/cohen-section1-assembly-plan.md`. This is the textbook completeness route
// (`docs/cohen-faithfulness-primary-source.md` §1), built on the now-complete
// predicate-base substrate (`pred_britton_via_tower::britton_lemma_unconditional`).
//
// Cohen's `H₂ = HNN(H₁, p ∣ p⁻¹ t_α p = t_α w_α(b) d, all α∈I)` is the base of the
// finite-association top HNN `H₃`. Unlike the finite `h2_pres` (Approach (b): only the
// single α=0 relation), the predicate base carries the FULL infinite family (II) AND
// the relator set `S` of `C = ⟨c;S⟩` — the only thing that has to go predicate. Its
// generator set is unchanged (`h2_num_gens`, the global `layout.rs`).
//
// `S` is carried as an abstract predicate `is_S : spec_fn(Word)->bool` with two side
// conditions (plan §2): `s_relators_valid` (S is a set of c-block words) and, for the
// k-iso later, the realization hypothesis (§3.3 bridge) — not needed in this brick.
//
// Kept SEPARATE from the finite tower (zero regression; reversible — delete the file
// + the `pub mod cohen_h2` line).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::pred_presentation::*;
use crate::machine_group::*;
use crate::layout::*;
use crate::word_numbering::*;
use crate::h1::*;
use crate::h3_ii::*;

verus! {

// ----------------------------------------------------------------------------
// The infinite family (II) as a membership predicate
// ----------------------------------------------------------------------------

/// `is_family_ii(mm,n,m,w)` — `w` is the family-(II) relator
/// `(p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹` for some `β ∈ I` (`numbers_word`). The FULL
/// infinite family (II) of Cohen's `H₂`, all β∈I (incl. β=0, the schematic
/// `p⁻¹tp=td`, which subsumes the finite `p_assoc`).
pub open spec fn is_family_ii(mm: ModMachine, n: nat, m: nat, w: Word) -> bool {
    exists|beta: nat| numbers_word(n, m, beta) && w == family_II_relator(mm, n, m, beta)
}

// ----------------------------------------------------------------------------
// `S` as an abstract c-block relator predicate
// ----------------------------------------------------------------------------

/// `s` is a c-block symbol: `Gen/Inv(g)` with `c_base ≤ g < c_base+n` — a letter of
/// the 2n-letter c-alphabet (an element of the free group on c₁..cₙ).
pub open spec fn c_symbol(nk: nat, n: nat, s: Symbol) -> bool {
    c_base(nk) <= generator_index(s) < c_base(nk) + n
}

/// `w` is a word on the c-block alphabet (every letter a `c_symbol`).
pub open spec fn is_c_word(nk: nat, n: nat, w: Word) -> bool {
    forall|i: int| 0 <= i < w.len() ==> c_symbol(nk, n, #[trigger] w[i])
}

/// A c-block word is valid over `h2_num_gens` (the predicate base's generators):
/// every letter's index is `< nk+n ≤ nk+2n+2`.
pub proof fn lemma_c_word_valid(nk: nat, n: nat, w: Word)
    requires
        is_c_word(nk, n, w),
    ensures
        word_valid(w, h2_num_gens(nk, n)),
{
    assert forall|i: int| 0 <= i < w.len()
        implies symbol_valid(#[trigger] w[i], h2_num_gens(nk, n)) by {
        assert(c_symbol(nk, n, w[i]));
        // generator_index(w[i]) < c_base(nk)+n = nk+n < nk+2n+2 = h2_num_gens(nk,n).
    }
}

/// The side condition on the abstract relator set `S`: every accepted relator is a
/// c-block word (so `S ⊆ free group on c₁..cₙ`, Cohen's setting). Discharges
/// `pred_presentation_valid` for the S-clause and is reused by the retraction (CS-2).
pub open spec fn s_relators_valid(is_S: spec_fn(Word) -> bool, nk: nat, n: nat) -> bool {
    forall|w: Word| #[trigger] is_S(w) ==> is_c_word(nk, n, w)
}

/// The **realization hypothesis** (one direction of the §3.3 machine bridge, plan §2): the abstract
/// relator set `S` of `C = ⟨c;S⟩` contains every c-word `w_α(c)` for `(α,0) ∈ H₀(M)`. Consumed ONLY
/// by the CS-5 k-iso's von-Dyck-forward (`docs/cohen-cs5-blueprint.md` §1): there `w_α(c) ≡_{h2_pred}
/// ε` must hold in the base, which follows because `is_S(w_α(c))` ⟹ `w_α(c)` is an `h2_pred` relator.
/// The §3.3 instantiation (the machine side of the bridge) will discharge it.
pub open spec fn s_realizes(is_S: spec_fn(Word) -> bool, mm: ModMachine, n: nat, m: nat) -> bool {
    let nk = g_m(mm).num_generators;
    forall|alpha: nat|
        (numbers_word(n, m, alpha) && mm_in_H0(mm, alpha, 0))
        ==> #[trigger] is_S(w_c(c_base(nk), n, m, alpha))
}

// ----------------------------------------------------------------------------
// The predicate base presentation `H₂`
// ----------------------------------------------------------------------------

/// The H₂ relator predicate: a K_M relator, OR a `b_i c_j = c_j b_i` commutator, OR a
/// relator of `C = ⟨c;S⟩`, OR a family-(II) relator. The first two are finite (Seq
/// membership); the last two are infinite predicates. This is exactly Cohen's
/// `H₂ = HNN(H₁, p | family (II))` written as a single (predicate) presentation.
pub open spec fn h2_pred_relator(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool, w: Word,
) -> bool {
    let nk = g_m(mm).num_generators;
    g_m(mm).relators.contains(w)
    || comm_relators(nk, n).contains(w)
    || is_S(w)
    || is_family_ii(mm, n, m, w)
}

/// `H₂` as a `PredPresentation`: `h2_num_gens` generators (the unchanged layout),
/// relators = `h2_pred_relator`. The base of the top HNN `H₃` (CS-3).
pub open spec fn h2_pred(
    mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool,
) -> PredPresentation {
    PredPresentation {
        num_generators: h2_num_gens(g_m(mm).num_generators, n),
        relators: |w: Word| h2_pred_relator(mm, n, m, is_S, w),
    }
}

/// `h2_pred` has `h2_num_gens(4+|quads|, n)` generators.
pub proof fn lemma_h2_pred_num_generators(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    ensures
        h2_pred(mm, n, m, is_S).num_generators == h2_num_gens((4 + mm.quads.len()) as nat, n),
{
    lemma_g_m_num_generators(mm);
}

// ----------------------------------------------------------------------------
// Validity
// ----------------------------------------------------------------------------

/// `h2_pred` is a valid predicate presentation: every accepted relator is
/// `word_valid` over `h2_num_gens`. Each of the four clauses lands:
///   * K_M relators — `presentation_valid(g_m)` + monotone lift `nk → h2_num_gens`;
///   * comm relators — `lemma_comm_relators_valid` (over `nk+2n ≤ h2_num_gens`);
///   * S relators — `s_relators_valid` ⟹ c-block word ⟹ `lemma_c_word_valid`;
///   * family (II) — `lemma_family_II_relator_valid` (needs `2n<m`, `nk+2n+2 ≤ ng`).
pub proof fn lemma_h2_pred_valid(mm: ModMachine, n: nat, m: nat, is_S: spec_fn(Word) -> bool)
    requires
        2 * n < m,
        s_relators_valid(is_S, g_m(mm).num_generators, n),
    ensures
        pred_presentation_valid(h2_pred(mm, n, m, is_S)),
{
    reveal(pred_presentation_valid);
    let nk = g_m(mm).num_generators;
    let ng = h2_num_gens(nk, n);
    let p = h2_pred(mm, n, m, is_S);
    assert(p.num_generators == ng);

    assert forall|w: Word| #![trigger (p.relators)(w)] (p.relators)(w) implies word_valid(w, ng) by {
        // (p.relators)(w) beta-reduces to h2_pred_relator(..)(w) (the disjunction).
        assert((p.relators)(w) == h2_pred_relator(mm, n, m, is_S, w));
        assert(h2_pred_relator(mm, n, m, is_S, w));
        if g_m(mm).relators.contains(w) {
            reveal(presentation_valid);
            lemma_g_m_valid(mm);
            let i = choose|i: int|
                0 <= i < g_m(mm).relators.len() && g_m(mm).relators[i] == w;
            assert(word_valid(g_m(mm).relators[i], nk));
            lemma_word_valid_mono(w, nk, ng);
        } else if comm_relators(nk, n).contains(w) {
            lemma_comm_relators_valid(nk, n, ng);
            let i = choose|i: int|
                0 <= i < comm_relators(nk, n).len() && comm_relators(nk, n)[i] == w;
            assert(word_valid(comm_relators(nk, n)[i], ng));
        } else if is_S(w) {
            assert(is_c_word(nk, n, w));
            lemma_c_word_valid(nk, n, w);
        } else {
            assert(is_family_ii(mm, n, m, w));
            let beta = choose|beta: nat|
                numbers_word(n, m, beta) && w == family_II_relator(mm, n, m, beta);
            lemma_family_II_relator_valid(mm, n, m, beta, ng);
        }
    }
}

} // verus!
