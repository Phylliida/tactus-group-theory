// Layer 2 — Brick 5, C3.2c / the C-arc: the F-part embeddings `map_a`, `map_b` of `P_A → h2_II`.
//
// The unified lifting lemma (docs/brick5-c3.2c-plan.md §5) needs faithful base embeddings
// `ψ: F → h1_base`.  This module builds `map_a`'s F-part (`a_words_F = [t,x,d,b_j]`, the literal
// inclusion) and proves it FREE in `h1_base` — i.e. `ψ_a` faithful — by the "permute once" route:
// B3 (`f_free_h1::lemma_f_free_in_h1`) gives `[t,x,b_j,d]` free, and `lemma_free_family_permute`
// reorders it into the `a_words` order `[t,x,d,b_j]` (d moved from last to index 2).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, lemma_g_m_num_generators};
use crate::layout::{b_base, b_idx, d_idx, p_idx};
use crate::h1::h1_base;
use crate::f_free::is_free_family;
use crate::f_free_h1::{f_h1_family, lemma_f_free_in_h1};
use crate::free_family_perm::{permute_family, lemma_free_family_permute};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat};
use crate::word_numbering::{w_c, alphabet_letter, numbers_word};
use crate::pa_data::pa_b_base;

verus! {

/// **`map_a`'s F-part** — the literal inclusion `F ↪ h1_base` in the `a_words` order
/// `[t, x, d, b_1, …, b_n]` (`t=Gen0`, `x=Gen1`, `d=Gen(d_idx)`, `b_j=Gen(b_idx(j))`).  This is the
/// first `n+3` entries of `a_words = phi_assoc.0`; the lifting lemma extends it with `p ↦ p`.
pub open spec fn a_words_F(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(d_idx(nk, n))]]
        + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))])
}

/// The reordering `σ` taking `f_h1_family = [t,x,b_1..b_n,d]` to `a_words_F = [t,x,d,b_1..b_n]`:
/// `t,x` fixed, index 2 (`d` in `a_words_F`) pulls from `f_h1`'s last slot `n+2`, and each `b`-slot
/// `3+j` pulls from `f_h1`'s `2+j`.
pub open spec fn pa_sigma(n: nat) -> Seq<nat> {
    Seq::new((n + 3) as nat, |i: int|
        if i < 2 { i as nat } else if i == 2 { (n + 2) as nat } else { (i - 1) as nat })
}

/// The left inverse of `pa_sigma`.
pub open spec fn pa_sigma_inv(n: nat) -> Seq<nat> {
    Seq::new((n + 3) as nat, |j: int|
        if j < 2 { j as nat } else if j == n + 2 { 2nat } else { (j + 1) as nat })
}

/// `pa_sigma` is a permutation of `0..n+3` with left inverse `pa_sigma_inv`.
proof fn lemma_pa_sigma_props(n: nat)
    ensures
        pa_sigma(n).len() == n + 3,
        pa_sigma_inv(n).len() == n + 3,
        forall|i: int| 0 <= i < n + 3 ==> #[trigger] pa_sigma(n)[i] < n + 3,
        forall|i: int| 0 <= i < n + 3 ==> #[trigger] pa_sigma_inv(n)[i] < n + 3,
        forall|i: int| 0 <= i < n + 3 ==> pa_sigma_inv(n)[#[trigger] pa_sigma(n)[i] as int] == i,
{
    let s = pa_sigma(n);
    let si = pa_sigma_inv(n);
    assert forall|i: int| 0 <= i < n + 3 implies #[trigger] s[i] < n + 3 by {}
    assert forall|i: int| 0 <= i < n + 3 implies #[trigger] si[i] < n + 3 by {}
    assert forall|i: int| 0 <= i < n + 3 implies si[#[trigger] s[i] as int] == i by {
        if i < 2 {
            assert(s[i] == i);
        } else if i == 2 {
            assert(s[i] == n + 2);
            assert(si[(n + 2) as int] == 2);
        } else {
            // 3 ≤ i ≤ n+2 ⟹ s[i] = i-1 ∈ [2, n+1], so si[i-1] = i.
            assert(s[i] == i - 1);
            assert(2 <= i - 1 < n + 2);
            assert(si[(i - 1) as int] == i);
        }
    }
}

/// `f_h1_family`'s entries by index: `[0]=t, [1]=x, [2+i]=Gen(nk+n+i)` (b-block then d).
proof fn lemma_f_h1_index(mm: ModMachine, n: nat)
    ensures
        f_h1_family(mm, n).len() == n + 3,
        f_h1_family(mm, n)[0] == seq![Symbol::Gen(0)],
        f_h1_family(mm, n)[1] == seq![Symbol::Gen(1)],
        forall|i: int| 0 <= i < n + 1 ==> #[trigger] f_h1_family(mm, n)[2 + i]
            == seq![Symbol::Gen((g_m(mm).num_generators + n + i) as nat)],
{
    let nk = g_m(mm).num_generators;
    let tower = Seq::new((n + 1) as nat, |i: int| seq![Symbol::Gen((nk + n + i) as nat)]);
    assert(f_h1_family(mm, n) =~= seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)]] + tower);
    let head = seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)]];
    assert(head.len() == 2);
    assert((head + tower)[0] == head[0]);
    assert((head + tower)[1] == head[1]);
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] (head + tower)[2 + i]
        == seq![Symbol::Gen((nk + n + i) as nat)] by {
        assert((head + tower)[2 + i] == tower[i]);
    }
}

/// `permute_family(f_h1_family, pa_sigma) =~= a_words_F` — the reordering realizes the `a_words` order.
proof fn lemma_permute_f_h1_is_a_words_F(mm: ModMachine, n: nat)
    ensures
        permute_family(f_h1_family(mm, n), pa_sigma(n)) =~= a_words_F(mm, n),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                          // nk = 4 + |quads| ≥ 4
    lemma_pa_sigma_props(n);
    lemma_f_h1_index(mm, n);
    let fam = f_h1_family(mm, n);
    let s = pa_sigma(n);
    let pf = permute_family(fam, s);
    let aw = a_words_F(mm, n);
    assert(pf.len() == n + 3);
    assert(aw.len() == n + 3) by {
        assert(aw == seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(d_idx(nk, n))]]
            + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]));
    }
    let awhead = seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(d_idx(nk, n))]];
    let awtail = Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
    assert(aw == awhead + awtail);
    assert forall|i: int| 0 <= i < n + 3 implies pf[i] =~= aw[i] by {
        assert(pf[i] == fam[s[i] as int]);
        if i == 0 {
            assert(s[0] == 0);
            assert(aw[0] == awhead[0]);
        } else if i == 1 {
            assert(s[1] == 1);
            assert(aw[1] == awhead[1]);
        } else if i == 2 {
            // d: f_h1[n+2] = Gen(nk+n+n) = Gen(nk+2n) = d_idx.
            assert(s[2] == n + 2);
            assert(fam[(n + 2) as int] == seq![Symbol::Gen((nk + n + n) as nat)]);  // i=n in lemma_f_h1_index
            assert((nk + n + n) as nat == d_idx(nk, n));
            assert(aw[2] == awhead[2]);
        } else {
            // 3 ≤ i ≤ n+2:  s[i]=i-1 ∈ [2, n+1];  fam[i-1] = Gen(nk+n+(i-3)) = b_{i-2}.
            let j = i - 3;
            assert(s[i] == i - 1);
            assert(fam[(i - 1) as int] == seq![Symbol::Gen((nk + n + (i - 1 - 2)) as nat)]);  // idx i-1-2 = i-3
            assert((nk + n + (i - 1 - 2)) as nat == b_idx(nk, n, (j + 1) as nat));
            assert(aw[i] == awtail[j]);
            assert(awtail[j] == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
        }
    }
}

/// **`map_a` faithful (`ψ_a` injective `F ↪ h1_base`)**: `a_words_F = [t,x,d,b_j]` is a FREE family
/// in `h1_base`.  Route A: B3 gives `[t,x,b_j,d]` free; `lemma_free_family_permute` reorders into the
/// `a_words` order.  This is the `map_a` hypothesis the unified lifting lemma consumes.
pub proof fn lemma_map_a_faithful(mm: ModMachine, n: nat)
    requires
        mod_machine_wf(mm),
    ensures
        is_free_family(h1_base(mm, n), a_words_F(mm, n)),
{
    lemma_f_free_in_h1(mm, n);                             // is_free_family(h1_base, f_h1_family)
    lemma_f_h1_index(mm, n);                               // f_h1_family.len() == n+3
    lemma_pa_sigma_props(n);
    // permute the free family by pa_sigma.
    lemma_free_family_permute(h1_base(mm, n), f_h1_family(mm, n), pa_sigma(n), pa_sigma_inv(n));
    // the permuted family IS a_words_F.
    lemma_permute_f_h1_is_a_words_F(mm, n);
    assert(permute_family(f_h1_family(mm, n), pa_sigma(n)) =~= a_words_F(mm, n));
}

// ----------------------------------------------------------------------------
// The full map `map_a = a_words` (ψ_a extended by `p ↦ p`) and the `w_c`-relabel.
// ----------------------------------------------------------------------------

/// **`map_a` (full)** — the inclusion `P_A ↪ h2_II`: `a_words_F` (the F-part) extended with the
/// stable letter `p ↦ Gen(p_idx)`.  This is `phi_assoc.0`, the crux's `a_words` list (`n+4` entries).
pub open spec fn a_words(mm: ModMachine, n: nat) -> Seq<Word> {
    a_words_F(mm, n).push(seq![Symbol::Gen(p_idx(g_m(mm).num_generators, n))])
}

/// `a_words` on a b-block index `[3, n+2]` is the literal `b`-generator (the F-b-gen `Gen(2+d)`
/// maps to the h2-b-gen `Gen(b_base+d-1) = Gen(nk+n+d-1)`).  A shift by `nk+n-3` on the b-block.
proof fn lemma_a_words_bblock(mm: ModMachine, n: nat, k: int)
    requires
        3 <= k < n + 3,
    ensures
        a_words(mm, n)[k] == seq![Symbol::Gen((g_m(mm).num_generators + n + (k - 3)) as nat)],
{
    let nk = g_m(mm).num_generators;
    let awf = a_words_F(mm, n);
    let head = seq![seq![Symbol::Gen(0)], seq![Symbol::Gen(1)], seq![Symbol::Gen(d_idx(nk, n))]];
    let tail = Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
    assert(awf == head + tail);
    assert(head.len() == 3);
    assert(awf.len() == n + 3);
    // a_words[k] = awf[k] for k < n+3 (push only adds index n+3).
    assert(a_words(mm, n)[k] == awf[k]);
    // awf[k] = tail[k-3] (k ≥ 3 = head.len()).
    assert(awf[k] == tail[k - 3]);
    assert(tail[k - 3] == seq![Symbol::Gen(b_idx(nk, n, ((k - 3) + 1) as nat))]);
    assert(b_idx(nk, n, ((k - 3) + 1) as nat) == nk + n + (k - 3));
}

/// **The digit relabel**: `apply_embedding(a_words, [alphabet_letter(3,n,d)]) =~=
/// [alphabet_letter(nk+n,n,d)]` for `1 ≤ d ≤ 2n`.  The F-b-block letter for digit `d` maps to the
/// h2-b-block letter for `d` (both `+` for `d≤n`, both `⁻¹` for `d>n`; the b-block shift `+nk+n-3`).
proof fn lemma_a_words_on_alpha_letter(mm: ModMachine, n: nat, d: nat)
    requires
        1 <= d <= 2 * n,
    ensures
        apply_embedding(a_words(mm, n), seq![alphabet_letter(pa_b_base(), n, d)])
            =~= seq![alphabet_letter(b_base(g_m(mm).num_generators, n), n, d)],
{
    let nk = g_m(mm).num_generators;
    let aw = a_words(mm, n);
    let bb = b_base(nk, n);                                  // nk + n
    reveal_with_fuel(apply_embedding, 2);
    if d <= n {
        // al(3,n,d) = Gen(3+d-1) = Gen(d+2);  k = d+2 ∈ [3, n+2].
        let k = (d + 2) as int;
        assert(alphabet_letter(pa_b_base(), n, d) == Symbol::Gen((pa_b_base() + d - 1) as nat));
        assert((pa_b_base() + d - 1) as nat == k as nat);   // 3 + d - 1 = d + 2
        assert(3 <= k < n + 3);
        lemma_a_words_bblock(mm, n, k);
        assert(aw[k] == seq![Symbol::Gen((nk + n + (k - 3)) as nat)]);
        assert((nk + n + (k - 3)) as nat == (bb + d - 1) as nat);   // k-3 = d-1
        lemma_concat_empty_right(aw[k]);
        assert(apply_embedding(aw, seq![Symbol::Gen((d + 2) as nat)]) =~= aw[k]);
        assert(alphabet_letter(bb, n, d) == Symbol::Gen((bb + d - 1) as nat));
    } else {
        // al(3,n,d) = Inv(3+(d-n)-1) = Inv(d-n+2);  k = d-n+2 ∈ [3, n+2].
        let e = (d - n) as nat;                             // 1 ≤ e ≤ n
        let k = (e + 2) as int;
        assert(alphabet_letter(pa_b_base(), n, d) == Symbol::Inv((pa_b_base() + e - 1) as nat));
        assert((pa_b_base() + e - 1) as nat == k as nat);
        assert(3 <= k < n + 3);
        lemma_a_words_bblock(mm, n, k);
        assert(aw[k] == seq![Symbol::Gen((nk + n + (k - 3)) as nat)]);
        assert((nk + n + (k - 3)) as nat == (bb + e - 1) as nat);   // k-3 = e-1
        assert(apply_embedding_symbol(aw, Symbol::Inv((e + 2) as nat)) =~= inverse_word(aw[k]));
        reveal_with_fuel(inverse_word, 2);
        lemma_concat_empty_right(inverse_word(aw[k]));
        assert(apply_embedding(aw, seq![Symbol::Inv((e + 2) as nat)]) =~= inverse_word(aw[k]));
        assert(inverse_word(aw[k]) =~= seq![Symbol::Inv((bb + e - 1) as nat)]);
        assert(alphabet_letter(bb, n, d) == Symbol::Inv((bb + (d - n) - 1) as nat));
    }
}

/// **The `w_c`-relabel (the key atom)**: `apply_embedding(a_words, w_c(3,n,m,γ)) =~= w_c(nk+n,n,m,γ)`.
/// The map `a_words` shifts the F-b-block `[3,n+2]` onto the h2-b-block `[nk+n, nk+2n-1]`, so it
/// carries the F-indexed b-substitution `w_γ(b)` onto the h2-indexed one.  Induction on `γ` over
/// `w_c`'s digit recursion (each digit `∈ [1,2n]` by `numbers_word`).
pub proof fn lemma_a_words_relabel_wc(mm: ModMachine, n: nat, m: nat, gamma: nat)
    requires
        numbers_word(n, m, gamma),
        2 * n < m,
    ensures
        apply_embedding(a_words(mm, n), w_c(pa_b_base(), n, m, gamma))
            =~= w_c(b_base(g_m(mm).num_generators, n), n, m, gamma),
    decreases gamma,
{
    let nk = g_m(mm).num_generators;
    let aw = a_words(mm, n);
    let bb = b_base(nk, n);
    if gamma == 0 || m <= 1 {
        assert(w_c(pa_b_base(), n, m, gamma) =~= empty_word());
        assert(w_c(bb, n, m, gamma) =~= empty_word());
        assert(apply_embedding(aw, empty_word()) =~= empty_word());
    } else {
        // numbers_word(γ): digit γ%m ∈ [1,2n], and γ/m numbers a word.
        let d = (gamma % m) as nat;
        assert(1 <= d <= 2 * n);
        assert(numbers_word(n, m, (gamma / m) as nat));
        // w_c(3,γ) = w_c(3,γ/m) + [al(3,n,d)]; distribute apply_embedding.
        let pre3 = w_c(pa_b_base(), n, m, (gamma / m) as nat);
        let letter3: Word = Seq::new(1, |_i: int| alphabet_letter(pa_b_base(), n, d));
        assert(w_c(pa_b_base(), n, m, gamma) =~= pre3 + letter3);
        lemma_apply_embedding_concat(aw, pre3, letter3);
        // IH on the prefix.
        lemma_a_words_relabel_wc(mm, n, m, (gamma / m) as nat);
        // digit relabel.
        assert(letter3 =~= seq![alphabet_letter(pa_b_base(), n, d)]);
        lemma_a_words_on_alpha_letter(mm, n, d);
        // target: w_c(nk+n,γ) = w_c(nk+n,γ/m) + [al(nk+n,n,d)].
        let preB = w_c(bb, n, m, (gamma / m) as nat);
        let letterB: Word = Seq::new(1, |_i: int| alphabet_letter(bb, n, d));
        assert(w_c(bb, n, m, gamma) =~= preB + letterB);
        assert(letterB =~= seq![alphabet_letter(bb, n, d)]);
    }
}

} // verus!
