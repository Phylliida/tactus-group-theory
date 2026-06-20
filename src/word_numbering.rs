// Layer 2 — Brick 1: word numbering (Cohen §9.6, book p.279).
//
// Pure word combinatorics: the α ↔ word numbering and the substitution maps
// w_α(c), w_α(b), w_α(bc). Self-contained on `word.rs` / `symbol.rs` — NO group
// theory. The generator layout is left ABSTRACT via base-offset parameters so
// this module commits to no absolute index convention (Brick 2 `h1.rs` pins the
// global layout table and instantiates these maps with concrete bases).
//
//   * `n`      — number of c-generators (= number of b-generators).
//   * `m`      — the modular-machine modulus; in practice m ≥ 2n+1 so the base-m
//                digits 1..=2n never collide (we carry `2*n < m` as a hypothesis
//                wherever the snoc/uniqueness facts need it).
//   * `c_base` — absolute index of c₁ (the c-block is c_base .. c_base+n).
//   * `b_base` — absolute index of b₁ (the b-block is b_base .. b_base+n).
//
// The "2n-letter alphabet" c₁,…,c_{2n} uses the convention c_{n+i} = c_i⁻¹, so a
// word in that alphabet is just a word in the free group on c₁,…,cₙ.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;

verus! {

// ----------------------------------------------------------------------------
// Per-digit letters
// ----------------------------------------------------------------------------

/// The symbol for digit `j` (1 ≤ j ≤ 2n) of the 2n-letter alphabet based at
/// `base`, under the convention `c_{n+i} = c_i⁻¹`:
///   j ∈ 1..=n      ↦ Gen(base + (j-1))      (the generator c_j)
///   j ∈ n+1..=2n   ↦ Inv(base + (j-n-1))    (the inverse c_{j-n}⁻¹)
pub open spec fn alphabet_letter(base: nat, n: nat, j: nat) -> Symbol {
    if j <= n {
        Symbol::Gen((base + j - 1) as nat)
    } else {
        Symbol::Inv((base + (j - n) - 1) as nat)
    }
}

/// The 2-letter contribution of digit `j` to `w_α(bc)`: `(b_j c_j)^{±1}`.
///   j ∈ 1..=n     ↦ b_j c_j        = [Gen b_j, Gen c_j]
///   j ∈ n+1..=2n  ↦ (b_i c_i)⁻¹    = c_i⁻¹ b_i⁻¹ = [Inv c_i, Inv b_i], i = j-n
pub open spec fn bc_letter(b_base: nat, c_base: nat, n: nat, j: nat) -> Word {
    if j <= n {
        seq![Symbol::Gen((b_base + j - 1) as nat), Symbol::Gen((c_base + j - 1) as nat)]
    } else {
        seq![
            Symbol::Inv((c_base + (j - n) - 1) as nat),
            Symbol::Inv((b_base + (j - n) - 1) as nat),
        ]
    }
}

// ----------------------------------------------------------------------------
// The numbering predicate I = { α : α numbers a word }
// ----------------------------------------------------------------------------

/// `α ∈ I`: every base-`m` digit of `α` lies in `1..=2n` (book p.279). Peels the
/// lowest digit `α % m` first; m ≤ 1 is treated as degenerate (only α = 0 ∈ I).
pub open spec fn numbers_word(n: nat, m: nat, alpha: nat) -> bool
    decreases alpha via numbers_word_decreases
{
    if alpha == 0 {
        true
    } else if m <= 1 {
        false
    } else {
        1 <= (alpha % m) <= 2 * n && numbers_word(n, m, alpha / m)
    }
}

// Termination witness for the `alpha / m` recursions below: under the Lean backend the
// fact `alpha / m < alpha` (for `m > 1`, `alpha > 0`) is not auto-discharged, so we
// supply it from vstd. The recursive branch is exactly `alpha != 0 && m > 1`.
#[via_fn]
proof fn numbers_word_decreases(n: nat, m: nat, alpha: nat) {
    if alpha != 0 && m > 1 {
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
    }
}

// ----------------------------------------------------------------------------
// The three substitution maps
// ----------------------------------------------------------------------------

/// `w_α(c)` — the α-th word on c₁,…,c_{2n}. The lowest base-m digit is the LAST
/// letter appended: `w_{αm+i}(c) = w_α(c) · c_i` (book's recursion).
pub open spec fn w_c(c_base: nat, n: nat, m: nat, alpha: nat) -> Word
    decreases alpha via w_c_decreases
{
    if alpha == 0 || m <= 1 {
        empty_word()
    } else {
        w_c(c_base, n, m, alpha / m)
            + Seq::new(1, |_i: int| alphabet_letter(c_base, n, alpha % m))
    }
}

#[via_fn]
proof fn w_c_decreases(c_base: nat, n: nat, m: nat, alpha: nat) {
    if alpha != 0 && m > 1 {
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
    }
}

/// `w_α(b)` — replace each `c_j^{±1}` by `b_j^{±1}`. Structurally identical to
/// `w_c` on the b-block, so we define it as exactly that.
pub open spec fn w_b(b_base: nat, n: nat, m: nat, alpha: nat) -> Word {
    w_c(b_base, n, m, alpha)
}

/// `w_α(bc)` — replace each `c_j^{±1}` by `(b_j c_j)^{±1}` (book p.279).
pub open spec fn w_bc(b_base: nat, c_base: nat, n: nat, m: nat, alpha: nat) -> Word
    decreases alpha via w_bc_decreases
{
    if alpha == 0 || m <= 1 {
        empty_word()
    } else {
        w_bc(b_base, c_base, n, m, alpha / m)
            + bc_letter(b_base, c_base, n, alpha % m)
    }
}

#[via_fn]
proof fn w_bc_decreases(b_base: nat, c_base: nat, n: nat, m: nat, alpha: nat) {
    if alpha != 0 && m > 1 {
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
    }
}

// ----------------------------------------------------------------------------
// div/mod helper: αm+i decomposition (1 ≤ i ≤ 2n < m)
// ----------------------------------------------------------------------------

/// For `0 ≤ i < m`, `(α·m + i) / m == α` and `(α·m + i) % m == i`.
///
/// Routes (resolve at verify time — nonlinear_arith won't handle a *variable*
/// divisor; use the Euclidean-uniqueness infra instead):
///   (a) `vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(r,m,q,a)`
///       with r=α·m+i, q=α, a=i  (cf. prop_v.rs:479) — needs r==q·m+a, 0≤a<m;
///       mind the int/nat cast (the maps use nat division).
///   (b) raw-Lean, mirroring `machine_group::lemma_div_mod_id` (Nat.div_add_mod +
///       omega): `Nat.add_mul_div_left`/`Nat.add_mul_mod_self_left` give
///       `(i + α·m)/m = i/m + α = α` since `i < m ⟹ i/m = 0`.
pub proof fn lemma_div_mod_step(alpha: nat, m: nat, i: nat)
    requires m > 0, i < m,
    ensures
        (alpha * m + i) / m == alpha,
        (alpha * m + i) % m == i,
{
    // r == q·m + a definitionally: alpha*m + i == alpha*m + i, with 0 ≤ i < m.
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (alpha * m + i) as int, m as int, alpha as int, i as int);
    // converse yields the int-division facts; nat division agrees for nonneg.
}

// ----------------------------------------------------------------------------
// Snoc recursion lemmas (the load-bearing facts of Brick 1)
// ----------------------------------------------------------------------------

/// `w_{αm+i}(c) = w_α(c) · c_i`  (book: `w_{αm+i}(c) = w_α(c) · c_i`).
pub proof fn lemma_w_c_snoc(c_base: nat, n: nat, m: nat, alpha: nat, i: nat)
    requires 1 <= i, 2 * n < m, i <= 2 * n,
    ensures
        w_c(c_base, n, m, alpha * m + i)
            =~= w_c(c_base, n, m, alpha)
                + Seq::new(1, |_k: int| alphabet_letter(c_base, n, i)),
{
    let beta = alpha * m + i;
    lemma_div_mod_step(alpha, m, i);
    // beta != 0 (since i ≥ 1) and m > 1 (since 2n < m and i ≤ 2n so m ≥ 2),
    // so w_c unfolds at beta.
    assert(beta % m == i);
    assert(beta / m == alpha);
    assert(beta >= 1);
    assert(m > 1);
}

/// `w_{αm+i}(b) = w_α(b) · b_i`  — immediate from `w_b := w_c` on the b-block.
pub proof fn lemma_w_b_snoc(b_base: nat, n: nat, m: nat, alpha: nat, i: nat)
    requires 1 <= i, 2 * n < m, i <= 2 * n,
    ensures
        w_b(b_base, n, m, alpha * m + i)
            =~= w_b(b_base, n, m, alpha)
                + Seq::new(1, |_k: int| alphabet_letter(b_base, n, i)),
{
    lemma_w_c_snoc(b_base, n, m, alpha, i);
}

/// `w_{αm+i}(bc) = w_α(bc) · (b_i c_i)`.
pub proof fn lemma_w_bc_snoc(b_base: nat, c_base: nat, n: nat, m: nat, alpha: nat, i: nat)
    requires 1 <= i, 2 * n < m, i <= 2 * n,
    ensures
        w_bc(b_base, c_base, n, m, alpha * m + i)
            =~= w_bc(b_base, c_base, n, m, alpha)
                + bc_letter(b_base, c_base, n, i),
{
    let beta = alpha * m + i;
    lemma_div_mod_step(alpha, m, i);
    assert(beta % m == i);
    assert(beta / m == alpha);
    assert(beta >= 1);
    assert(m > 1);
}

// ----------------------------------------------------------------------------
// Validity / length lemmas
// ----------------------------------------------------------------------------

/// Every digit-letter is a valid symbol for a presentation whose generator count
/// covers the c-block `base .. base+n`.
pub proof fn lemma_alphabet_letter_valid(base: nat, n: nat, j: nat, ng: nat)
    requires 1 <= j <= 2 * n, base + n <= ng,
    ensures symbol_valid(alphabet_letter(base, n, j), ng),
{
    if j <= n {
        assert(generator_index(alphabet_letter(base, n, j)) == (base + j - 1) as nat);
    } else {
        assert(generator_index(alphabet_letter(base, n, j)) == (base + (j - n) - 1) as nat);
    }
}

/// `w_c` only uses symbols in the c-block, hence is valid for any `ng ≥ c_base+n`,
/// PROVIDED `α ∈ I` (so every digit lies in 1..=2n).
pub proof fn lemma_w_c_valid(c_base: nat, n: nat, m: nat, alpha: nat, ng: nat)
    requires numbers_word(n, m, alpha), c_base + n <= ng, 2 * n < m,
    ensures word_valid(w_c(c_base, n, m, alpha), ng),
    decreases alpha,
{
    if alpha == 0 || m <= 1 {
        assert(w_c(c_base, n, m, alpha) =~= empty_word());
    } else {
        let d = alpha % m;
        // numbers_word ⟹ 1 ≤ d ≤ 2n
        // termination: alpha / m < alpha (m > 1, alpha > 0 hold in this branch).
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
        lemma_w_c_valid(c_base, n, m, alpha / m, ng);
        lemma_alphabet_letter_valid(c_base, n, d, ng);
        let pref = w_c(c_base, n, m, alpha / m);
        let last = Seq::new(1, |_i: int| alphabet_letter(c_base, n, d));
        assert(w_c(c_base, n, m, alpha) =~= pref + last);
        assert forall|k: int| #![trigger (pref + last)[k]] 0 <= k < (pref + last).len()
            implies symbol_valid((pref + last)[k], ng) by {
            if k < pref.len() {
                assert((pref + last)[k] == pref[k]);
            } else {
                assert((pref + last)[k] == last[0]);
            }
        }
    }
}

} // verus!
