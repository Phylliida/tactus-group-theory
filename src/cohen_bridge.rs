// Layer 2 — the machine bridge (§3.3a): the CONCRETE relator set `S`.
//
// `docs/machine-bridge-and-infinite-gen-plan.md` §A.  All of the Layer-2 assembly
// (CS-1..CS-7, `cohen_h2`..`cohen_cs7`) is parameterized over an ABSTRACT relator-set
// predicate `is_S : spec_fn(Word)->bool` carrying two side conditions:
//   * `s_relators_valid(is_S, nk, n)` — every `S`-relator is a pure-c word;
//   * `s_realizes(is_S, mm, n, m)`    — `(α,0)∈H₀(M) ∧ α∈I ⟹ is_S(w_α(c))`.
//
// This brick instantiates `is_S` to its CANONICAL value — the word-numbering image of the
// machine's c.e. set —
//
//     S = { w_α(c) : numbers_word(n,m,α) ∧ (α,0) ∈ H₀(M) },
//
// and discharges BOTH side conditions, turning Layer 2's abstract faithfulness into a CONCRETE
// statement about an explicit c.e. relator set (`lemma_C_faithful_printable_canonical`).  This is
// the *realization* (⟸) direction of Cohen's word-numbering bridge `w_α(c) ∈ S ⟺ (α,0) ∈ H₀(M)`
// (book p.279) made literal: with this `S`, the printable f.p. group `h3_pres` faithfully contains
// `C = ⟨c;S⟩` for the concrete machine set `H₀(M)`.
//
// What it does NOT do: close the headline machine-iff `w_α(c)=1 in H₃ ⟺ (α,0)∈H₀`.  The forward
// (`w_α(c)=1 in C ⟹ (α,0)∈H₀`) is the word problem of `C` deciding the c.e. set, which is the
// Layer-0.5 benign-embedding content — NOT derivable from the canonical `S` over a free group
// (`ncl(S)` collapses more than `S` itself).  See the plan doc §B.
//
// Additive (new module + one lib.rs line); reversible; no regression.

use vstd::prelude::*;
use crate::word::{Word, empty_word};
use crate::presentation::equiv_in_presentation;
use crate::pred_presentation::equiv_in_pred_presentation;
use crate::machine_group::{ModMachine, mod_machine_wf, mm_terminal, mm_in_H0, g_m};
use crate::layout::c_base;
use crate::word_numbering::{numbers_word, w_c};
use crate::h3::h3_pres;
use crate::cohen_h2::{s_relators_valid, s_realizes, is_c_word, c_symbol};
use crate::cohen_retraction::{c_pred, lemma_w_c_in_block};
use crate::cohen_cs7::lemma_C_faithful_printable;

verus! {

// ============================================================================
// The canonical relator set `S`
// ============================================================================

/// **The canonical `S`.**  `w ∈ S` iff `w = w_α(c)` for some `α` that numbers a word with
/// `(α,0) ∈ H₀(M)`.  This is Cohen's word-numbering bridge (book p.279): `S` is exactly the
/// word-numbering image of the machine's c.e. set `{α : (α,0)∈H₀(M)}`.  The `c`-block base is
/// `c_base(g_m(mm).num_generators)` — the same base every other Layer-2 module writes c-words at.
pub open spec fn is_S_canonical(mm: ModMachine, n: nat, m: nat) -> spec_fn(Word) -> bool {
    |w: Word|
        exists|alpha: nat|
            numbers_word(n, m, alpha)
            && mm_in_H0(mm, alpha, 0)
            && w == w_c(c_base(g_m(mm).num_generators), n, m, alpha)
}

// ============================================================================
// `w_α(c)` is a pure-c word
// ============================================================================

/// Every numbered word `w_α(c)` (`α∈I`) is a c-block word: a thin wrapper over
/// `lemma_w_c_in_block` (indices in `[c_base, c_base+n)` = exactly `c_symbol`).
pub proof fn lemma_w_c_is_c_word(nk: nat, n: nat, m: nat, alpha: nat)
    requires
        numbers_word(n, m, alpha),
    ensures
        is_c_word(nk, n, w_c(c_base(nk), n, m, alpha)),
{
    lemma_w_c_in_block(c_base(nk), n, m, alpha);
    let w = w_c(c_base(nk), n, m, alpha);
    assert forall|i: int| 0 <= i < w.len() implies c_symbol(nk, n, #[trigger] w[i]) by {
        // lemma_w_c_in_block: c_base(nk) ≤ generator_index(w[i]) < c_base(nk)+n = c_symbol.
    }
}

// ============================================================================
// The two side conditions, discharged for the canonical `S`
// ============================================================================

/// **Validity.**  The canonical `S` accepts only pure-c words (`s_relators_valid`): every accepted
/// word is some `w_α(c)`, which is a c-word by `lemma_w_c_is_c_word`.
pub proof fn lemma_is_S_canonical_relators_valid(mm: ModMachine, n: nat, m: nat)
    ensures
        s_relators_valid(is_S_canonical(mm, n, m), g_m(mm).num_generators, n),
{
    let nk = g_m(mm).num_generators;
    let is_S = is_S_canonical(mm, n, m);
    assert forall|w: Word| #[trigger] is_S(w) implies is_c_word(nk, n, w) by {
        let alpha = choose|alpha: nat|
            #![trigger w_c(c_base(nk), n, m, alpha)]
            numbers_word(n, m, alpha)
            && mm_in_H0(mm, alpha, 0)
            && w == w_c(c_base(nk), n, m, alpha);
        lemma_w_c_is_c_word(nk, n, m, alpha);
    }
}

/// **Realization (the bridge's ⟸).**  The canonical `S` contains every `w_α(c)` for `(α,0)∈H₀(M)`
/// (`s_realizes`): immediate from the definition with witness `β = α`.
pub proof fn lemma_is_S_canonical_realizes(mm: ModMachine, n: nat, m: nat)
    ensures
        s_realizes(is_S_canonical(mm, n, m), mm, n, m),
{
    let nk = g_m(mm).num_generators;
    let is_S = is_S_canonical(mm, n, m);
    assert forall|alpha: nat|
        (numbers_word(n, m, alpha) && mm_in_H0(mm, alpha, 0))
        implies #[trigger] is_S(w_c(c_base(nk), n, m, alpha)) by {
        // is_S(w_α(c)) holds with witness β = α.
        assert(numbers_word(n, m, alpha)
            && mm_in_H0(mm, alpha, 0)
            && w_c(c_base(nk), n, m, alpha) == w_c(c_base(nk), n, m, alpha));
    }
}

// ============================================================================
// The concrete faithfulness headline (CS-7 with the abstract `is_S` removed)
// ============================================================================

/// **§3.3a — concrete Higman-embedding faithfulness for the printable group.**  A pure-c word `w`
/// trivial in the printable finite `h3_pres` is trivial in `C = ⟨c;S⟩` for the CONCRETE relator
/// set `S = { w_α(c) : (α,0)∈H₀(M) }`.  This is `lemma_C_faithful_printable` with its two abstract
/// `is_S` hypotheses discharged by the canonical instantiation — the Higman embedding theorem
/// `C ↪ H₃` made fully explicit for the machine set `H₀(M)`.
pub proof fn lemma_C_faithful_printable_canonical(mm: ModMachine, n: nat, m: nat, w: Word)
    requires
        mod_machine_wf(mm),
        mm_terminal(mm, 0, 0),
        2 * n < m,
        is_c_word(g_m(mm).num_generators, n, w),
        equiv_in_presentation(h3_pres(mm, n, m), w, empty_word()),
    ensures
        equiv_in_pred_presentation(c_pred(mm, n, m, is_S_canonical(mm, n, m)), w, empty_word()),
{
    lemma_is_S_canonical_relators_valid(mm, n, m);
    lemma_is_S_canonical_realizes(mm, n, m);
    lemma_C_faithful_printable(mm, n, m, is_S_canonical(mm, n, m), w);
}

} // verus!
