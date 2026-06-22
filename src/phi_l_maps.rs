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
use crate::layout::{b_idx, d_idx};
use crate::h1::h1_base;
use crate::f_free::is_free_family;
use crate::f_free_h1::{f_h1_family, lemma_f_free_in_h1};
use crate::free_family_perm::{permute_family, lemma_free_family_permute};

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

} // verus!
