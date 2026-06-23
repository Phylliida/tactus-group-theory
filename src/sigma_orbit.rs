// Layer 2 — Brick 5, C3.2 REFRAME (step 2): the BOUNDED σ-ORBIT.
//
// THE PURPOSE — de-risk the C3.2 reframe.  Sessions 7 and 8 both crashed on the same rock: the
// a-level HNN association iso `hnn_associations_isomorphic(phi_l_data(l))` is UNIVERSAL (∀ word ww),
// and its von-Dyck-backward direction needs `family_II_relator(m·β+l) ≡_base ε` for *every* β the base
// covers, which forces `σ_l(alphas) ⊆ alphas` — σ-FORWARD-closure.  Since `σ_l(β) = m·β + l` appends a
// base-m digit (strictly grows), no FINITE `alphas` is forward-closed: `0 ↦ 1 ↦ m+1 ↦ m²+m+1 ↦ …` is
// an infinite ascending chain.  That unsatisfiability is machine-checked in
// `phi_l_iso_unsat.rs` (`lemma_sigma_sat_upto_unsatisfiable`).
//
// THE FIX (Danielle-confirmed, `docs/brick5-c4-plan.md` §7): drop the universal iso for a
// WORD-RESTRICTED one.  A fixed word `w` only triggers σ-shifts at BOUNDED DEPTH (its Britton-peel has
// a bounded stable-letter count, and the a-tower has fixed height `2n` — one σ per level).  So instead
// of closing `alphas` under σ *forever*, we only need `alphas` to contain the bounded forward σ-orbit
// of a SEED set up to a fixed depth.  That orbit is FINITE — hence satisfiable.
//
// This module is the clean, self-contained combinatorial brick: it builds the orbit as an explicit
// `Seq<nat>` (finite by construction), proves it preserves number-word-ness and is depth-stratified
// σ-closed (`orbit(d) → orbit(d+1)`, a DAG — the top layer's σ-shifts are NOT required, which is
// precisely why it dodges the unsat forward-closure), and pins the reframed word-restricted slice
// `sigma_slice_ok` together with a SATISFIABILITY WITNESS — the direct refutation of "even the
// depth-bounded slice is vacuous".  Its own module ⟹ no trigger pollution of the delicate isos.

use vstd::prelude::*;
use vstd::seq_lib::lemma_seq_concat_contains_all_elements;
use crate::word_numbering::numbers_word;
use crate::phi_l_mapb_fwd::lemma_sigma_numbers_word;

verus! {

// ----------------------------------------------------------------------------
// The orbit construction (all explicit `Seq<nat>` — finite by construction).
// ----------------------------------------------------------------------------

/// The σ digit-appends of one index `x`: the length-`2n` list `[m·x+1, …, m·x+2n]` — `x` with each
/// possible base-m digit `l ∈ [1,2n]` appended (`σ_l(x) = m·x + l`).
pub open spec fn digit_appends(x: nat, m: nat, n: nat) -> Seq<nat> {
    Seq::new(2 * n, |i: int| (m * x + (i + 1)) as nat)
}

/// One σ-expansion of a whole index list: concatenate the digit-appends of each element.
pub open spec fn sigma_expand(d: Seq<nat>, m: nat, n: nat) -> Seq<nat>
    decreases d.len(),
{
    if d.len() == 0 {
        Seq::<nat>::empty()
    } else {
        digit_appends(d.first(), m, n) + sigma_expand(d.drop_first(), m, n)
    }
}

/// The depth-`depth` bounded σ-orbit of seed list `d`: accumulate σ-expansions, keeping all layers.
/// `orbit(0) = d`; `orbit(k+1) = orbit(k) ++ σ-expand(orbit(k))`.  A FINITE `Seq` (hence satisfiable),
/// in contrast to the unsatisfiable forward-closure `σ(α) ⊆ α` of `phi_l_iso_unsat.rs`.
pub open spec fn sigma_orbit(d: Seq<nat>, m: nat, n: nat, depth: nat) -> Seq<nat>
    decreases depth,
{
    if depth == 0 {
        d
    } else {
        let prev = sigma_orbit(d, m, n, (depth - 1) as nat);
        prev + sigma_expand(prev, m, n)
    }
}

// ----------------------------------------------------------------------------
// `digit_appends` — contains + number-words.
// ----------------------------------------------------------------------------

/// `digit_appends(x,m,n)` contains `σ_l(x) = m·x+l` for every digit `l ∈ [1,2n]` (witness `i = l-1`).
pub proof fn lemma_digit_appends_contains(x: nat, m: nat, n: nat, l: nat)
    requires
        1 <= l <= 2 * n,
    ensures
        digit_appends(x, m, n).contains((m * x + l) as nat),
{
    let da = digit_appends(x, m, n);
    let i = (l - 1) as int;
    assert(0 <= i < da.len());
    assert(da[i] == (m * x + l) as nat);
    assert(da.contains((m * x + l) as nat));    // witness i
}

/// Every entry of `digit_appends(x,m,n)` numbers a word, when `x` does (`σ` preserves number-words).
pub proof fn lemma_digit_appends_numbers_word(x: nat, m: nat, n: nat)
    requires
        numbers_word(n, m, x),
        2 * n < m,
    ensures
        forall|y: nat| #[trigger] digit_appends(x, m, n).contains(y) ==> numbers_word(n, m, y),
{
    let da = digit_appends(x, m, n);
    assert forall|y: nat| #[trigger] da.contains(y) implies numbers_word(n, m, y) by {
        let i = choose|i: int| 0 <= i < da.len() && da[i] == y;
        assert(da[i] == (m * x + (i + 1)) as nat);
        lemma_sigma_numbers_word(n, m, (i + 1) as nat, x);     // 1 <= i+1 <= 2n
    }
}

// ----------------------------------------------------------------------------
// `sigma_expand` — contains + number-words (recursion on `d.len()`).
// ----------------------------------------------------------------------------

/// `d.contains(x)` with `d.first() != x` pushes the witness into `d.drop_first()`.
proof fn lemma_drop_first_contains(d: Seq<nat>, x: nat)
    requires
        d.contains(x),
        d.len() > 0,
        d.first() != x,
    ensures
        d.drop_first().contains(x),
{
    let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
    assert(d[i] == x);
    assert(i != 0);                              // d[0] = first != x
    assert(d.drop_first()[i - 1] == d[i]);       // drop_first = subrange(1,len)
    assert(d.drop_first().contains(x));          // witness i-1
}

/// `sigma_expand(d)` contains `σ_l(x) = m·x+l` whenever `x ∈ d` and `l ∈ [1,2n]`.
pub proof fn lemma_sigma_expand_contains(d: Seq<nat>, m: nat, n: nat, x: nat, l: nat)
    requires
        d.contains(x),
        1 <= l <= 2 * n,
    ensures
        sigma_expand(d, m, n).contains((m * x + l) as nat),
    decreases d.len(),
{
    let v = (m * x + l) as nat;
    assert(d.len() > 0);                         // from d.contains(x)
    let head = digit_appends(d.first(), m, n);
    let tail = sigma_expand(d.drop_first(), m, n);
    assert(sigma_expand(d, m, n) == head + tail);
    if d.first() == x {
        lemma_digit_appends_contains(x, m, n, l);
        assert(head.contains(v));
    } else {
        lemma_drop_first_contains(d, x);
        lemma_sigma_expand_contains(d.drop_first(), m, n, x, l);
        assert(tail.contains(v));
    }
    lemma_seq_concat_contains_all_elements(head, tail, v);
}

/// Every entry of `sigma_expand(d)` numbers a word, when every entry of `d` does.
pub proof fn lemma_sigma_expand_numbers_word(d: Seq<nat>, m: nat, n: nat)
    requires
        2 * n < m,
        forall|y: nat| #[trigger] d.contains(y) ==> numbers_word(n, m, y),
    ensures
        forall|y: nat| #[trigger] sigma_expand(d, m, n).contains(y) ==> numbers_word(n, m, y),
    decreases d.len(),
{
    if d.len() == 0 {
        assert(sigma_expand(d, m, n) == Seq::<nat>::empty());
    } else {
        let head = digit_appends(d.first(), m, n);
        let tail = sigma_expand(d.drop_first(), m, n);
        assert(sigma_expand(d, m, n) == head + tail);
        // head numbers words: d.first() does.
        assert(d.contains(d.first()));
        lemma_digit_appends_numbers_word(d.first(), m, n);
        // tail numbers words: each drop_first entry is a d entry.
        assert forall|y: nat| #[trigger] d.drop_first().contains(y) implies numbers_word(n, m, y) by {
            assert(d.contains(y));               // drop_first ⊆ d
        }
        lemma_sigma_expand_numbers_word(d.drop_first(), m, n);
        assert forall|y: nat| #[trigger] (head + tail).contains(y) implies numbers_word(n, m, y) by {
            lemma_seq_concat_contains_all_elements(head, tail, y);
        }
    }
}

// ----------------------------------------------------------------------------
// `sigma_orbit` — monotonicity, closure, number-words.
// ----------------------------------------------------------------------------

/// Single-step monotonicity: `orbit(d)` is a prefix of `orbit(d+1)`, so it preserves membership.
pub proof fn lemma_sigma_orbit_monotone_step(d: Seq<nat>, m: nat, n: nat, depth: nat, x: nat)
    requires
        sigma_orbit(d, m, n, depth).contains(x),
    ensures
        sigma_orbit(d, m, n, depth + 1).contains(x),
{
    let prev = sigma_orbit(d, m, n, depth);
    let ext = sigma_expand(prev, m, n);
    assert(sigma_orbit(d, m, n, depth + 1) == prev + ext);
    lemma_seq_concat_contains_all_elements(prev, ext, x);
}

/// Monotonicity: `orbit(d1) ⊆ orbit(d2)` for `d1 ≤ d2` (membership form).
pub proof fn lemma_sigma_orbit_monotone(d: Seq<nat>, m: nat, n: nat, d1: nat, d2: nat, x: nat)
    requires
        d1 <= d2,
        sigma_orbit(d, m, n, d1).contains(x),
    ensures
        sigma_orbit(d, m, n, d2).contains(x),
    decreases d2 - d1,
{
    if d1 < d2 {
        lemma_sigma_orbit_monotone_step(d, m, n, d1, x);
        lemma_sigma_orbit_monotone(d, m, n, d1 + 1, d2, x);
    }
}

/// **Depth-stratified σ-closure** — the DAG step.  An element at depth `d` has all its σ-shifts at
/// depth `d+1`.  Crucially the requirement runs `orbit(d) → orbit(d+1)` (NOT `orbit(d) → orbit(d)`),
/// so the *top* layer never needs its own shifts — that is what makes the orbit satisfiable where the
/// universal forward-closure is not.
pub proof fn lemma_sigma_orbit_closed_step(d: Seq<nat>, m: nat, n: nat, depth: nat, gamma: nat, l: nat)
    requires
        sigma_orbit(d, m, n, depth).contains(gamma),
        1 <= l <= 2 * n,
    ensures
        sigma_orbit(d, m, n, depth + 1).contains((m * gamma + l) as nat),
{
    let prev = sigma_orbit(d, m, n, depth);
    let ext = sigma_expand(prev, m, n);
    assert(sigma_orbit(d, m, n, depth + 1) == prev + ext);
    lemma_sigma_expand_contains(prev, m, n, gamma, l);
    assert(ext.contains((m * gamma + l) as nat));
    lemma_seq_concat_contains_all_elements(prev, ext, (m * gamma + l) as nat);
}

/// Every entry of `orbit(depth)` numbers a word, when every seed entry does (induction on `depth`).
pub proof fn lemma_sigma_orbit_numbers_word(d: Seq<nat>, m: nat, n: nat, depth: nat)
    requires
        2 * n < m,
        forall|y: nat| #[trigger] d.contains(y) ==> numbers_word(n, m, y),
    ensures
        forall|y: nat| #[trigger] sigma_orbit(d, m, n, depth).contains(y) ==> numbers_word(n, m, y),
    decreases depth,
{
    if depth == 0 {
        assert(sigma_orbit(d, m, n, 0) == d);
    } else {
        let prev = sigma_orbit(d, m, n, (depth - 1) as nat);
        let ext = sigma_expand(prev, m, n);
        assert(sigma_orbit(d, m, n, depth) == prev + ext);
        lemma_sigma_orbit_numbers_word(d, m, n, (depth - 1) as nat);    // prev numbers words
        lemma_sigma_expand_numbers_word(prev, m, n);                    // ext numbers words
        assert forall|y: nat| #[trigger] (prev + ext).contains(y) implies numbers_word(n, m, y) by {
            lemma_seq_concat_contains_all_elements(prev, ext, y);
        }
    }
}

// ----------------------------------------------------------------------------
// The reframed word-restricted slice + the SATISFIABILITY WITNESS.
// ----------------------------------------------------------------------------

/// **Word-restricted (seed-decoupled) σ-slice** — the SATISFIABLE replacement for the universal
/// `sigma_sat_upto` (`phi_l_iso_unsat.rs`).  It demands that every single-step σ-shift `σ_l(seed[k])`
/// (`l ∈ [1,2n]`) of the SEED list land in `alphas`.  The seed is the (finite) set of config-indices a
/// fixed word actually touches — DECOUPLED from `alphas`.  Because no `alphas`-element is forced to
/// contain its own σ-image, there is no infinite ascending chain: this slice is satisfiable (see
/// `lemma_sigma_slice_satisfiable`), unlike the universal `∀γ∈betas(alphas)` form.
pub open spec fn sigma_slice_ok(seed: Seq<nat>, alphas: Seq<nat>, m: nat, n: nat) -> bool {
    forall|k: int, l: nat| #![trigger alphas.contains((m * seed[k] + l) as nat)]
        (0 <= k < seed.len() && 1 <= l <= 2 * n) ==> alphas.contains((m * seed[k] + l) as nat)
}

/// **THE DE-RISKING WITNESS** — the direct refutation of "even the depth-bounded slice is vacuous".
/// For ANY `seed` of number-words, `alphas = sigma_expand(seed)` (one digit-append layer) is a FINITE
/// list of number-words that satisfies the word-restricted slice.  Contrast
/// `lemma_sigma_sat_upto_unsatisfiable`: the universal slice (`∀γ∈betas(alphas)`) is UNSAT because
/// `seed = betas(alphas)` is tied to `alphas`; here `seed` and `alphas` are different objects, so the
/// ascending-chain argument has no purchase.
pub proof fn lemma_sigma_slice_satisfiable(seed: Seq<nat>, m: nat, n: nat)
    requires
        2 * n < m,
        forall|i: int| 0 <= i < seed.len() ==> numbers_word(n, m, #[trigger] seed[i]),
    ensures
        sigma_slice_ok(seed, sigma_expand(seed, m, n), m, n),
        forall|y: nat| #[trigger] sigma_expand(seed, m, n).contains(y) ==> numbers_word(n, m, y),
{
    let alphas = sigma_expand(seed, m, n);
    // number-words: bridge the index-form hypothesis to the contains-form and expand.
    assert forall|y: nat| #[trigger] seed.contains(y) implies numbers_word(n, m, y) by {
        let i = choose|i: int| 0 <= i < seed.len() && seed[i] == y;
        assert(seed[i] == y);
    }
    lemma_sigma_expand_numbers_word(seed, m, n);
    // slice: each σ_l(seed[k]) is contained, since seed[k] ∈ seed.
    assert forall|k: int, l: nat| (0 <= k < seed.len() && 1 <= l <= 2 * n) implies
        alphas.contains(#[trigger] ((m * seed[k] + l) as nat)) by {
        assert(seed.contains(seed[k]));
        lemma_sigma_expand_contains(seed, m, n, seed[k], l);
    }
}

/// **Tower-depth satisfiability** — one finite `alphas = sigma_orbit(seed, depth)` covers ALL tower
/// levels.  Every σ-shift `σ_l(γ)` of an element `γ` reachable within depth `< depth` lands in
/// `alphas`.  Each a-tower level peels exactly one σ-step, so `depth = 2n` (the tower height) suffices;
/// the orbit stays finite because the requirement is depth-STRATIFIED (`orbit(d), d<depth → orbit(depth)`),
/// never forcing the maximal layer's shifts.  This is the satisfiable side condition the reframed
/// directional lemmas will carry (replacing the unsatisfiable `sigma_sat_upto`).
pub proof fn lemma_sigma_orbit_covers(seed: Seq<nat>, m: nat, n: nat, depth: nat, d: nat,
    gamma: nat, l: nat)
    requires
        d < depth,
        1 <= l <= 2 * n,
        sigma_orbit(seed, m, n, d).contains(gamma),
    ensures
        sigma_orbit(seed, m, n, depth).contains((m * gamma + l) as nat),
{
    lemma_sigma_orbit_closed_step(seed, m, n, d, gamma, l);          // ∈ orbit(d+1)
    lemma_sigma_orbit_monotone(seed, m, n, d + 1, depth, (m * gamma + l) as nat);  // ⟹ ∈ orbit(depth)
}

} // verus!
