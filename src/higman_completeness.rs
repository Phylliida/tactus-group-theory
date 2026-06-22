// Layer 2 — Brick 5 COMPLETENESS (`higman_completeness.rs`): the `C ↪ H₃` faithful
// direction. Companion to `higman_consequences.rs` (soundness, DONE: `lemma_III`).
//
// This module owns the **`in_C` predicate** (C1) and — eventually — the Fork-B
// virtual-iso k-level descent (C4) and assembly (C5). Kept in its own module so the
// completeness-specific quantifier triggers don't pollute the (already huge)
// soundness module. See `docs/brick5-completeness-plan.md`.
//
// ----------------------------------------------------------------------------
// C1 design (co-designed with C4, 2026-06-21; peer-reviewed)
// ----------------------------------------------------------------------------
// Target (faithfulness):  `h3_pres ⊢ w_α(c) = 1  ⟹  in_C(w_α(c))`, then C5 unfolds
// `in_C` to "= 1 in C = ⟨c;S⟩".  Here `w_α(c)` is a BASE word of the k-HNN (pure
// c-letters, no `k`; cf. `lemma_w_c_valid_h3_base`, C0).
//
// **`in_C` is the engine-facing predicate `w ∈ ncl(S)` taken over the k-HNN base
// `B = h3_upto(2n)`.** This is *exactly* what a virtual-iso `britton_lemma_unconditional`
// produces: the standard Britton descent lands a base-word-trivial-in-the-HNN at
// "trivial in the base", but over the free-c base `B` the literal "≡ ε in B" is FALSE
// (the c's are free); the honest output is "≡ ε in `B` MODULO ncl(S)", i.e. `in_C`.
//
// Two structural decisions, both peer-confirmed:
//   * **Direct virtual-iso descent, NOT `lemma_property_ii`.** In the faithfulness
//     instantiation the membership witness `in_kp_subgroup(data, in_C, w_α(c))` is the
//     EMPTY factor list (since `w_α(c) ≡ ε`), so the generic engine's `choose` over
//     witnesses is a liability (it may pick a non-empty `W`, reviving the pinch loop and
//     the false base-descent). C4 is a bespoke descent whose input is a base word by
//     construction. (`docs/brick5-completeness-plan.md` §2.3 / Fork B.)
//   * **One predicate.** `ncl_B(S) ∩ {pure c-words} = ncl_{F(c)}(S)` (the b's commute with
//     the c's so b-conjugators cancel; p/a/U don't enter pure c-words). So a single `in_C`
//     suffices and C5 is an unfolding, not a bridge between two predicates.
//
// Representation: the explicit conjugate-product form `∃ factors. (each factor a conjugate
// `g·r^{±1}·g⁻¹` of an S-relator `r = w_β(c)`, `(β,0)∈H₀`) ∧ `concat_all(factors) ≡_B w`.
// This makes the three subgroup-closure props (`in_C(ε)`, H_mul, H_resp) fall out of the
// existing `concat_all` / `equiv` infrastructure (chosen over the "finite-subset-of-S
// adjoined as relators" form, which has a relator-ordering wrinkle for H_mul). The
// conjugators `g` are arbitrary `B`-words — the *widest* (easiest-to-satisfy) predicate,
// which makes the C4 conclusion easiest to reach and keeps H_resp/H_mul cheap.

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::word_numbering::*;
use crate::h1::*;
use crate::h3::*;
use crate::benign::{concat_all, lemma_concat_all_empty};

verus! {

// ----------------------------------------------------------------------------
// The relator set S and its normal closure ncl(S) — as predicates
// ----------------------------------------------------------------------------

/// `r ∈ S`: `r = w_β(c)` (placed at the c-block) for some `β` that numbers a word with
/// `(β,0) ∈ H₀(M)`. `S` is c.e. (infinite), so it is carried as a predicate, not a `Seq`.
pub open spec fn is_S_relator(mm: ModMachine, n: nat, m: nat, r: Word) -> bool {
    exists|beta: nat| #![trigger h_w_c(g_m(mm).num_generators, n, m, beta)]
        numbers_word(n, m, beta)
        && mm_in_H0(mm, beta, 0)
        && r == h_w_c(g_m(mm).num_generators, n, m, beta)
}

/// A single normal-closure factor: a conjugate `g·r·g⁻¹` or `g·r⁻¹·g⁻¹` of an S-relator
/// `r`, with the conjugator `g` an arbitrary word. Products of these generate `ncl(S)`
/// (the inverse form is needed so the product set is closed under inverting a factor).
pub open spec fn is_conj_S_factor(mm: ModMachine, n: nat, m: nat, f: Word) -> bool {
    exists|g: Word, r: Word| #![trigger is_S_relator(mm, n, m, r), inverse_word(g)]
        is_S_relator(mm, n, m, r) && (
            f == g + r + inverse_word(g)
            || f == g + inverse_word(r) + inverse_word(g)
        )
}

/// Every entry of `factors` is a normal-closure factor.
pub open spec fn all_conj_S_factors(mm: ModMachine, n: nat, m: nat, factors: Seq<Word>) -> bool {
    forall|i: int| 0 <= i < factors.len() ==> is_conj_S_factor(mm, n, m, #[trigger] factors[i])
}

/// **`in_C(w)` — the engine-facing completeness predicate (C1).** `w ∈ ncl(S)` taken in the
/// k-HNN base `B = h3_upto(2n)`: a finite product of S-relator conjugates that is
/// `B`-equivalent to `w`. The exact output of a virtual-iso `britton_lemma_unconditional`
/// for the `k`-level (Fork B, C4). C5 unfolds this to `w = 1 in C = ⟨c;S⟩`.
pub open spec fn in_C(mm: ModMachine, n: nat, m: nat, w: Word) -> bool {
    exists|factors: Seq<Word>| #[trigger] all_conj_S_factors(mm, n, m, factors)
        && equiv_in_presentation(h3_upto(mm, n, m, (2 * n) as nat), concat_all(factors), w)
}

// ----------------------------------------------------------------------------
// C1 down-payment — the three subgroup-closure properties of `in_C`.
//
// These are what the Fork-B descent (C4) consumes as it accumulates a factor list:
//   * H_id   `in_C(ε)`                      — the empty product (base case of the peel)
//   * H_mul  `in_C(a) ∧ in_C(b) ⟹ in_C(ab)` — appending factor lists (each pinch step)
//   * H_resp `in_C(a) ∧ a ≡_B b ⟹ in_C(b)`  — closure under base-equivalence (re-association)
// They hold for any reasonable ncl predicate, so they do NOT by themselves validate the
// C1 design (that is C4's job); they are the safe, immediately-verifiable foundation.
// ----------------------------------------------------------------------------

/// **H_id.** `in_C(ε)` — the empty product of conjugates.
pub proof fn lemma_in_C_empty(mm: ModMachine, n: nat, m: nat)
    ensures in_C(mm, n, m, empty_word()),
{
    let base = h3_upto(mm, n, m, (2 * n) as nat);
    let factors: Seq<Word> = Seq::empty();
    lemma_concat_all_empty();                         // concat_all([]) == ε
    lemma_equiv_refl(base, empty_word());             // ε ≡ ε
    assert(all_conj_S_factors(mm, n, m, factors));    // vacuous (len 0)
    assert(concat_all(factors) =~= empty_word());
    // witness `factors` for the ∃ in `in_C`
    assert(all_conj_S_factors(mm, n, m, factors)
        && equiv_in_presentation(base, concat_all(factors), empty_word()));
}

/// **H_mul.** `in_C` is closed under product: `in_C(a) ∧ in_C(b) ⟹ in_C(a·b)`. Append the
/// two witness factor lists; `concat_all` distributes over `+`, and `equiv` respects concat.
pub proof fn lemma_in_C_mul(mm: ModMachine, n: nat, m: nat, a: Word, b: Word)
    requires
        in_C(mm, n, m, a),
        in_C(mm, n, m, b),
    ensures
        in_C(mm, n, m, a + b),
{
    let base = h3_upto(mm, n, m, (2 * n) as nat);
    let fa = choose|f: Seq<Word>| #![trigger all_conj_S_factors(mm, n, m, f)] all_conj_S_factors(mm, n, m, f)
        && equiv_in_presentation(base, concat_all(f), a);
    let fb = choose|f: Seq<Word>| #![trigger all_conj_S_factors(mm, n, m, f)] all_conj_S_factors(mm, n, m, f)
        && equiv_in_presentation(base, concat_all(f), b);
    assert(all_conj_S_factors(mm, n, m, fa) && equiv_in_presentation(base, concat_all(fa), a));
    assert(all_conj_S_factors(mm, n, m, fb) && equiv_in_presentation(base, concat_all(fb), b));

    let f = fa + fb;
    // (1) all factors of fa+fb are conjugate-S factors
    assert(all_conj_S_factors(mm, n, m, f)) by {
        assert forall|i: int| 0 <= i < f.len()
            implies is_conj_S_factor(mm, n, m, #[trigger] f[i]) by {
            if i < fa.len() {
                assert(f[i] == fa[i]);
            } else {
                assert(f[i] == fb[i - fa.len()]);
            }
        }
    }
    // (2) concat_all(fa+fb) = concat_all(fa) + concat_all(fb)  ≡  a + b
    lemma_concat_all_distributes(fa, fb);
    let ca = concat_all(fa);
    let cb = concat_all(fb);
    assert(concat_all(f) =~= ca + cb);
    lemma_equiv_concat_left(base, ca, a, cb);          // ca·cb ≡ a·cb
    lemma_equiv_concat_right(base, a, cb, b);          // a·cb  ≡ a·b
    assert(concat(ca, cb) == ca + cb);
    assert(concat(a, cb) == a + cb);
    assert(concat(a, b) == a + b);
    lemma_equiv_transitive(base, ca + cb, a + cb, a + b);
    assert(equiv_in_presentation(base, concat_all(f), a + b));
    // witness f
    assert(all_conj_S_factors(mm, n, m, f)
        && equiv_in_presentation(base, concat_all(f), a + b));
}

/// **H_resp.** `in_C` is closed under base-equivalence: `in_C(a) ∧ a ≡_B b ⟹ in_C(b)`. The
/// same witness factor list works — `concat_all(fa) ≡ a ≡ b`.
pub proof fn lemma_in_C_resp(mm: ModMachine, n: nat, m: nat, a: Word, b: Word)
    requires
        in_C(mm, n, m, a),
        equiv_in_presentation(h3_upto(mm, n, m, (2 * n) as nat), a, b),
    ensures
        in_C(mm, n, m, b),
{
    let base = h3_upto(mm, n, m, (2 * n) as nat);
    let fa = choose|f: Seq<Word>| #![trigger all_conj_S_factors(mm, n, m, f)] all_conj_S_factors(mm, n, m, f)
        && equiv_in_presentation(base, concat_all(f), a);
    assert(all_conj_S_factors(mm, n, m, fa) && equiv_in_presentation(base, concat_all(fa), a));
    lemma_equiv_transitive(base, concat_all(fa), a, b);   // concat_all(fa) ≡ a ≡ b
    // witness fa
    assert(all_conj_S_factors(mm, n, m, fa)
        && equiv_in_presentation(base, concat_all(fa), b));
}

// ----------------------------------------------------------------------------
// The faithfulness theorem — SIGNATURE (C4 + C5).
//
// Stated as a `spec` predicate so the target type-checks now (pinning `in_C`'s role and
// the precise hypotheses) without incurring a proof obligation. The actual
// `proof fn lemma_C_faithful` lands at the end of the Fork-B arc; until then it is NOT
// stated as a proof (respecting the standing no-shortcuts rule — no verifier bypasses).
//
//   FAITHFULNESS:  h3_pres ⊢ w_α(c) = 1  ⟹  in_C(w_α(c))
//
// The input `equiv_in_presentation(h3_pres, w_α(c), ε)` is consistent by soundness
// (`lemma_III` gives it for `(α,0)∈H₀`); in completeness it is the hypothesis, and the
// virtual-iso k-descent routes it to `in_C(w_α(c))`. The `mm_terminal` hypothesis feeds
// `lemma_theorem1` (the single circularity-breaker: `t_α∈⟨U⟩ ⟺ (α,0)∈H₀`), which
// discharges the ψ-well-definedness (virtual iso) inside C4.
// ----------------------------------------------------------------------------

/// The C4+C5 target, as a spec-level statement (signature pin; proof = the Fork-B arc).
pub open spec fn faithfulness_statement(mm: ModMachine, n: nat, m: nat, alpha: nat) -> bool {
    (
        mod_machine_wf(mm)
        && mm_terminal(mm, 0, 0)
        && numbers_word(n, m, alpha)
        && 2 * n < m
        && equiv_in_presentation(
            h3_pres(mm, n, m),
            h_w_c(g_m(mm).num_generators, n, m, alpha),
            empty_word())
    ) ==> in_C(mm, n, m, h_w_c(g_m(mm).num_generators, n, m, alpha))
}

} // verus!
