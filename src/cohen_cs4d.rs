// Layer 2 — Cohen §1 assembly, brick CS-4d (slice arithmetic). `docs/cohen-cs4d-blueprint.md` §5.
//
// CS-4d backward (`b ⟹ a`) needs to convert `map_a_forward`'s output slice `S = betas(norm)`
// (a no-dup number-word slice carrying a forced 0-head and arbitrary non-σ junk indices) into the
// exact σ-image slice `sigma_betas(bet)` that `lemma_mapb_M2_rt` consumes. A number-word `γ` is a
// σ_l-image IFF `γ % m == l` (since `numbers_word` = every base-m digit ∈ [1,2n], and σ(β)=mβ+l
// appends the digit l). So the σ-preimage slice is exactly:
//
//   `bet_of(S, m, l)` = the preimages `γ/m` of the elements `γ ∈ S` with `γ % m == l`.
//
// This module is pure-Seq combinatorics (ZERO design risk): it pins `bet_of` and its four
// load-bearing properties for `M2_general` (blueprint §3/§4.2):
//   * `bet_of` is no-duplicates (σ is injective on the `%m==l` elements of a no-dup `S`);
//   * `bet_of` entries are number-words (one `numbers_word` unfold of the parent `γ`);
//   * every `sigma_betas(bet_of(S))` entry lands back in `S` (round-trip `σ(γ/m)=γ`);
//   * every `γ ∈ S` with `γ%m==l` has its preimage `γ/m ∈ bet_of(S)` (the "all preimages" fact the
//     recognition crux's `lemma_sat_bridge` consumes).
//
// Additive (new module + one lib.rs line); no regression.

use vstd::prelude::*;
use crate::word_numbering::numbers_word;
use crate::phi_l_mapb::sigma_betas;

verus! {

// ============================================================================
// `bet_of` — the σ-preimage slice
// ============================================================================

/// `γ` is a σ_l-image (its lowest base-`m` digit is `l`).
pub open spec fn is_sigma_image(gamma: nat, m: nat, l: nat) -> bool {
    gamma % m == l
}

/// Push index/length facts, packaged so the Lean backend fires them reliably (the bare `s.push(a)[i]`
/// axioms do not auto-instantiate when `s` is a recursive spec-fn application).
proof fn lemma_push_at<T>(s: Seq<T>, a: T, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s.push(a).len() == s.len() + 1,
        i < s.len() ==> s.push(a)[i] == s[i],
        i == s.len() ==> s.push(a)[i] == a,
{
}

/// The σ-preimages of the `%m==l` elements of `S`, in order (recursion on `drop_last`). No explicit
/// dedup is needed: on a no-dup `S`, distinct `%m==l` elements `γ` have distinct `γ/m` (since
/// `γ = m·(γ/m)+l`), so `bet_of` inherits no-duplicates for free.
/// One step: append `last/m` to `rest` iff `last` is a σ-image. Non-recursive, so it unfolds cleanly
/// (the Lean backend will not unfold a `.push` that directly wraps a recursive call — see `bet_of`).
pub open spec fn bet_of_step(last: nat, m: nat, l: nat, rest: Seq<nat>) -> Seq<nat> {
    if is_sigma_image(last, m, l) {
        rest.push(last / m)
    } else {
        rest
    }
}

/// The σ-preimages of the `%m==l` elements of `S`. The recursive call is an *argument* of the
/// non-recursive `bet_of_step` (NOT wrapped in `.push` directly) so the one-step unfold reveals under
/// the Lean backend.
pub open spec fn bet_of(s: Seq<nat>, m: nat, l: nat) -> Seq<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::<nat>::empty()
    } else {
        bet_of_step(s.last(), m, l, bet_of(s.drop_last(), m, l))
    }
}

/// One-step unfold of `bet_of` (isolated so the recursive `open spec fn` body reveals reliably under
/// the Lean backend, which does not unfold it in large proof contexts).
proof fn lemma_bet_of_step(s: Seq<nat>, m: nat, l: nat)
    requires
        s.len() > 0,
        m > 0,                          // nat division `s.last()/m` needs `m>0` to be well-defined
    ensures
        bet_of(s, m, l) == bet_of_step(s.last(), m, l, bet_of(s.drop_last(), m, l)),
        is_sigma_image(s.last(), m, l)
            ==> bet_of(s, m, l) == bet_of(s.drop_last(), m, l).push(s.last() / m),
        !is_sigma_image(s.last(), m, l) ==> bet_of(s, m, l) == bet_of(s.drop_last(), m, l),
{
    reveal_with_fuel(bet_of, 2);
}

// ----------------------------------------------------------------------------
// Modular round-trip atom: `γ % m == l` ⟹ `γ = m·(γ/m) + l` and `σ(γ/m) = γ`.
// ----------------------------------------------------------------------------

/// `γ % m == l` (with `l < m`) ⟹ `m·(γ/m) + l == γ`, i.e. `σ(γ/m) = γ`.
pub proof fn lemma_sigma_image_roundtrip(gamma: nat, m: nat, l: nat)
    requires
        m > 0,
        is_sigma_image(gamma, m, l),
    ensures
        (m * (gamma / m) + l) as nat == gamma,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(gamma as int, m as int);
    // γ == m·(γ/m) + γ%m  and  γ%m == l.
    assert(gamma % m == l);
}

// ----------------------------------------------------------------------------
// Membership: every element of `bet_of(S)` is `γ/m` for some `%m==l` element `γ ∈ S`.
// ----------------------------------------------------------------------------

/// `rest.push(z).contains(x)` splits into `rest.contains(x)` or `x == z` (index witness from push).
proof fn lemma_push_contains(rest: Seq<nat>, z: nat, x: nat)
    requires
        rest.push(z).contains(x),
    ensures
        rest.contains(x) || x == z,
{
    let i = choose|i: int| 0 <= i < rest.push(z).len() && rest.push(z)[i] == x;
    lemma_push_at(rest, z, i);
    if i < rest.len() {
        assert(rest[i] == x);              // rest.push(z)[i] == rest[i]
    }
}

/// **Contains-characterization of `bet_of`**: every member `x` of `bet_of(S)` is `γ/m` for some
/// `%m==l` element `γ ∈ S`. (Contains-based — discharges far more reliably than an index/exists
/// postcondition under the Lean backend.)
pub proof fn lemma_bet_of_elements(s: Seq<nat>, m: nat, l: nat, x: nat)
    requires
        m > 0,
        bet_of(s, m, l).contains(x),
    ensures
        exists|g: nat| s.contains(g) && is_sigma_image(g, m, l) && x == g / m,
    decreases s.len(),
{
    // s.len() == 0 ⟹ bet_of empty ⟹ contains(x) false (vacuous via the hypothesis).
    let rest = bet_of(s.drop_last(), m, l);
    let last = s.last();
    lemma_bet_of_step(s, m, l);                          // bet_of(s) == (σ? rest.push : rest)
    // every element of drop_last is an element of s
    assert forall|y: nat| s.drop_last().contains(y) implies s.contains(y) by {
        let k = choose|k: int| 0 <= k < s.drop_last().len() && s.drop_last()[k] == y;
        assert(s[k] == y);
    }
    if is_sigma_image(last, m, l) {
        // bet_of(s) == rest.push(last/m); contains(x) ⟹ rest.contains(x) ∨ x == last/m.
        lemma_push_contains(rest, last / m, x);
        if rest.contains(x) {
            lemma_bet_of_elements(s.drop_last(), m, l, x);   // IH ⟹ witness g ∈ drop_last
            let g = choose|g: nat| s.drop_last().contains(g) && is_sigma_image(g, m, l) && x == g / m;
            assert(s.contains(g) && is_sigma_image(g, m, l) && x == g / m);
        } else {
            // x == last/m; witness g = last (∈ s, σ-image).
            assert(s[s.len() - 1] == last && s.contains(last));
            assert(s.contains(last) && is_sigma_image(last, m, l) && x == last / m);
        }
    } else {
        // bet_of(s) == rest; contains(x) ⟹ IH on drop_last.
        lemma_bet_of_elements(s.drop_last(), m, l, x);
        let g = choose|g: nat| s.drop_last().contains(g) && is_sigma_image(g, m, l) && x == g / m;
        assert(s.contains(g) && is_sigma_image(g, m, l) && x == g / m);
    }
}

// ----------------------------------------------------------------------------
// Property 1 — `bet_of` entries are number words.
// ----------------------------------------------------------------------------

/// `bet_of(S)` entries are number words: each is `γ/m` for a `%m==l` (hence nonzero) number-word
/// `γ ∈ S`, and `numbers_word(n,m,γ)` unfolds to `numbers_word(n,m,γ/m)`.
pub proof fn lemma_bet_of_number_words(s: Seq<nat>, n: nat, m: nat, l: nat)
    requires
        m > 1,
        1 <= l,
        forall|i: int| 0 <= i < s.len() ==> numbers_word(n, m, #[trigger] s[i]),
    ensures
        forall|j: int| 0 <= j < bet_of(s, m, l).len()
            ==> numbers_word(n, m, #[trigger] bet_of(s, m, l)[j]),
{
    assert forall|j: int| 0 <= j < bet_of(s, m, l).len()
        implies numbers_word(n, m, #[trigger] bet_of(s, m, l)[j]) by {
        let x = bet_of(s, m, l)[j];
        assert(bet_of(s, m, l).contains(x));         // witness j
        lemma_bet_of_elements(s, m, l, x);           // exists g ∈ s: σ-image, x == g/m
        let g = choose|g: nat| s.contains(g) && is_sigma_image(g, m, l) && x == g / m;
        // g % m == l ≥ 1 ⟹ g = m·(g/m)+l ≥ l ≥ 1 ⟹ g ≠ 0 ⟹ numbers_word(g) unfolds to numbers_word(g/m).
        assert(g % m == l);
        lemma_sigma_image_roundtrip(g, m, l);        // m·(g/m)+l == g
        assert(g >= l && g != 0);                    // l ≥ 1
        let k = choose|k: int| 0 <= k < s.len() && s[k] == g;
        assert(numbers_word(n, m, s[k]));            // hypothesis at index k
        assert(numbers_word(n, m, g / m));           // unfold one step (m>1, g≠0); x == g/m
    }
}

// ----------------------------------------------------------------------------
// Property 2 — `sigma_betas(bet_of(S))` lands back in `S`.
// ----------------------------------------------------------------------------

/// Every `sigma_betas(bet_of(S))` entry is an element of `S` (round-trip `σ(γ/m)=γ`). This is the
/// `σbet ⊆ S` sub-slice fact the monotone relator step of `M2_general` consumes.
pub proof fn lemma_sigma_bet_of_in(s: Seq<nat>, m: nat, l: nat)
    requires
        m > 0,
        l < m,
    ensures
        forall|j: int| 0 <= j < sigma_betas(bet_of(s, m, l), m, l).len()
            ==> s.contains(#[trigger] sigma_betas(bet_of(s, m, l), m, l)[j]),
{
    let bet = bet_of(s, m, l);
    let sb = sigma_betas(bet, m, l);
    assert forall|j: int| 0 <= j < sb.len() implies s.contains(#[trigger] sb[j]) by {
        assert(sb[j] == (m * bet[j] + l) as nat);
        assert(bet.contains(bet[j]));                // witness j (bet[j] ∈ bet)
        lemma_bet_of_elements(s, m, l, bet[j]);      // exists g ∈ s: σ-image, bet[j] == g/m
        let g = choose|g: nat| s.contains(g) && is_sigma_image(g, m, l) && bet[j] == g / m;
        lemma_sigma_image_roundtrip(g, m, l);        // m·(g/m)+l == g, and bet[j] == g/m
        assert(sb[j] == g);                          // m·bet[j]+l == m·(g/m)+l == g
    }
}

// ----------------------------------------------------------------------------
// Property 3 — every `%m==l` element of `S` has its preimage in `bet_of(S)` ("all preimages").
// ----------------------------------------------------------------------------

/// If `γ ∈ S` and `γ % m == l`, then `γ/m ∈ bet_of(S)`. This is the saturation fact the recognition
/// crux's `lemma_sat_bridge` consumes (every `cong_l` coordinate of `S` has its preimage in `bet`).
pub proof fn lemma_bet_of_all_preimages(s: Seq<nat>, m: nat, l: nat, gamma: nat)
    requires
        m > 0,
        is_sigma_image(gamma, m, l),
        s.contains(gamma),
    ensures
        bet_of(s, m, l).contains(gamma / m),
    decreases s.len(),
{
    let rest = bet_of(s.drop_last(), m, l);
    let last = s.last();
    lemma_bet_of_step(s, m, l);                              // unfold bet_of(s) one step
    if s.drop_last().contains(gamma) {
        lemma_bet_of_all_preimages(s.drop_last(), m, l, gamma);
        assert(rest.contains(gamma / m));
        if is_sigma_image(last, m, l) {
            assert(bet_of(s, m, l) =~= rest.push(last / m));       // unfold one step
            let k = choose|k: int| 0 <= k < rest.len() && rest[k] == gamma / m;
            lemma_push_at(rest, last / m, k);
            assert(rest.push(last / m).contains(gamma / m));      // witness k
        } else {
            assert(bet_of(s, m, l) == rest);                      // unfold one step
        }
    } else {
        // γ must be the last element.
        let k = choose|k: int| 0 <= k < s.len() && s[k] == gamma;
        assert(k == s.len() - 1) by {
            if k < s.len() - 1 {
                assert(s.drop_last()[k] == gamma);
                assert(s.drop_last().contains(gamma));
            }
        }
        assert(last == gamma);
        assert(bet_of(s, m, l) =~= rest.push(last / m));           // is_sigma_image(last) holds
        lemma_push_at(rest, last / m, rest.len() as int);
        assert(rest.push(last / m)[rest.len() as int] == gamma / m);
        assert(rest.push(last / m).contains(gamma / m));
    }
}

// ----------------------------------------------------------------------------
// Property 4 — `bet_of` is duplicate-free (σ injective on the `%m==l` elements of a no-dup `S`).
// ----------------------------------------------------------------------------

/// `bet_of(S)` has no duplicates when `S` does. Distinct `%m==l` elements `γ₁ ≠ γ₂ ∈ S` have
/// `γ₁/m ≠ γ₂/m` (else `γᵢ = m·(γᵢ/m)+l` would coincide). Combined with `lemma_bet_of_elements`'s
/// witness-uniqueness, the pushed preimage is always fresh.
pub proof fn lemma_bet_of_no_dup(s: Seq<nat>, m: nat, l: nat)
    requires
        m > 0,
        l < m,
        s.no_duplicates(),
    ensures
        bet_of(s, m, l).no_duplicates(),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(bet_of(s, m, l) =~= Seq::<nat>::empty());     // no-dup vacuous
    } else {
        // drop_last of a no-dup seq is no-dup.
        assert(s.drop_last().no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < j < s.drop_last().len()
                implies s.drop_last()[i] != s.drop_last()[j] by {
                assert(s.drop_last()[i] == s[i] && s.drop_last()[j] == s[j]);
            }
        }
        lemma_bet_of_no_dup(s.drop_last(), m, l);             // rest no-dup (IH)
        let rest = bet_of(s.drop_last(), m, l);
        let last = s.last();
        lemma_bet_of_step(s, m, l);                          // bet_of(s) == (σ? rest.push : rest)
        if is_sigma_image(last, m, l) {
            // `last/m` is fresh: any rest member is γ/m for a %m==l element γ ∈ drop_last, and
            // γ ≠ last (no-dup) with both %m==l forces γ/m ≠ last/m.
            assert(!rest.contains(last / m)) by {
                if rest.contains(last / m) {
                    lemma_bet_of_elements(s.drop_last(), m, l, last / m);   // γ ∈ drop_last, σ, last/m==γ/m
                    let gamma = choose|g: nat|
                        s.drop_last().contains(g) && is_sigma_image(g, m, l) && last / m == g / m;
                    // γ ≠ last: γ ∈ drop_last but last = s.last() ∉ drop_last (s no-dup).
                    let k = choose|k: int| 0 <= k < s.drop_last().len() && s.drop_last()[k] == gamma;
                    assert(s[k] == gamma && s[s.len() - 1] == last && 0 <= k < s.len() - 1);
                    assert(gamma != last);                   // distinct indices into no-dup s
                    // both %m==l and γ/m == last/m ⟹ γ == last (roundtrip), contradiction.
                    lemma_sigma_image_roundtrip(gamma, m, l);
                    lemma_sigma_image_roundtrip(last, m, l);
                    assert(gamma == last);
                }
            }
            lemma_push_at(rest, last / m, rest.len() as int);     // big.len() == rest.len()+1
            let big = rest.push(last / m);
            assert forall|i: int, j: int| 0 <= i < big.len() && 0 <= j < big.len() && i != j
                implies big[i] != big[j] by {
                lemma_push_at(rest, last / m, i);
                lemma_push_at(rest, last / m, j);
                if i < rest.len() && j < rest.len() {
                } else if i == rest.len() {
                    assert(rest.contains(rest[j]));
                } else {
                    assert(rest.contains(rest[i]));
                }
            }
            assert(big.no_duplicates());                      // pairwise distinct == no_duplicates
        }
        // bet_of(s) is `big` (σ) or `rest` (¬σ), both no-dup (above / IH).
    }
}

} // verus!
