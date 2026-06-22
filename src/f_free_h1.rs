// Layer 2 — Brick 5 COMPLETENESS, C3.2c / F1, B3: lift the free family to `h1_base`.
//
// B2 (`f_free_tower.rs`) proved `[t, x, b_1..b_n, d]` is a FREE family in the empty-association tower
// `free_stable_tower(g_m(mm), n+1) == K_M ∗ F(b) ∗ ⟨d⟩` (no `c`-block, no commutators).  B3 lifts
// that to `h1_base`, which DOES carry the `c`-block and the `n²` commutators `b_i c_j = c_j b_i`.
//
// Strategy (docs/brick5-c3.2c-plan.md §4.1 "B3"): the homomorphism `kill_c : h1_base → K_M ∗ F(b) ∗
// ⟨d⟩` kills every `c_j` (↦ ε), fixes the K_M block, and shifts `b_j, d` DOWN by `n` (past the
// dropped `c`-block).  It is valid: the K_M relators are fixed and trivial in the target, and each
// commutator `b_i c_j b_i⁻¹ c_j⁻¹` maps to `b_i' b_i'⁻¹ ≡ ε`.  Then the pullback engine
// (`free_basis::lemma_pullback_free`): if `apply_embedding(F_h1, w) ≡ ε` in `h1_base`, then
// `apply_embedding(kill_c ∘ F_h1, w) ≡ ε` in the target — and `kill_c ∘ F_h1` is EXACTLY B2's family,
// so B2's freeness gives `w ≡_free ε`.  Hence `F_h1` is free in `h1_base`.
//
// `F_h1 = [t, x] ++ [Gen(nk+n), Gen(nk+n+1), …, Gen(nk+2n)]` (`nk = g_m`'s gen count): `t, x` at
// `0, 1`, the `b_j` at `nk+n .. nk+2n-1` and `d` at `nk+2n` — the literal `h1_base` layout
// (`layout.rs`).  Each appended index `nk+n+i` (`i = 0..n`) is in the b/d block, so `kill_c` shifts it
// to `nk+i` — matching B2's `free_stable_letter(nk, i) = [Gen(nk+i)]`.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::lemma_relator_is_identity;
use crate::homomorphism::{HomomorphismData, apply_hom, apply_hom_symbol, is_valid_homomorphism,
    lemma_hom_respects_concat};
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, lemma_g_m_valid,
    lemma_g_m_num_generators, lemma_cancel_pair_equiv_empty};
use crate::layout::{c_base, b_base, b_idx, d_idx, h1_num_gens};
use crate::h1::{h1_base, comm_relator, comm_relators, lemma_h1_base_valid, lemma_comm_relator_valid};
use crate::benign::apply_embedding;
use crate::free_basis::{comp_images, lemma_pullback_free};
use crate::higman_operations::free_group;
use crate::f_free::is_free_family;
use crate::f_free_tower::{free_stable_tower, free_stable_family, free_stable_letter, tx_family,
    lemma_free_stable_tower_closed, lemma_free_stable_tower_valid, lemma_txbd_free_in_tower,
    lemma_txbd_family_layout};

verus! {

// ----------------------------------------------------------------------------
// The c-killing / b,d-shifting homomorphism  h1_base → K_M ∗ F(b) ∗ ⟨d⟩.
// ----------------------------------------------------------------------------

/// `kill_c : h1_base(mm, n) → free_stable_tower(g_m(mm), n+1)`.  Identity on the K_M block
/// (`index < nk`), kills the `c`-block (`nk ≤ index < nk+n ↦ ε`), and shifts the b/d block down by
/// `n` (`nk+n ≤ index ↦ Gen(index − n)`), so `b_j, d` land at the target's b/d indices `nk .. nk+n`.
pub open spec fn kill_c(mm: ModMachine, n: nat) -> HomomorphismData {
    let nk = g_m(mm).num_generators;
    HomomorphismData {
        source: h1_base(mm, n),
        target: free_stable_tower(g_m(mm), (n + 1) as nat),
        generator_images: Seq::new(h1_num_gens(nk, n), |i: int|
            if i < nk {
                seq![Symbol::Gen(i as nat)]
            } else if i < nk + n {
                empty_word()
            } else {
                seq![Symbol::Gen((i - n) as nat)]
            }),
    }
}

/// The target has `nk + n + 1` generators.
pub proof fn lemma_kill_c_target_num_gens(mm: ModMachine, n: nat)
    ensures
        kill_c(mm, n).target.num_generators == g_m(mm).num_generators + n + 1,
{
    lemma_free_stable_tower_closed(g_m(mm), (n + 1) as nat);
}

// ----------------------------------------------------------------------------
// Per-symbol behaviour.
// ----------------------------------------------------------------------------

/// On a low symbol (`index < nk`), `kill_c` is the identity: `s ↦ [s]`.
pub proof fn lemma_kill_c_symbol_low(mm: ModMachine, n: nat, s: Symbol)
    requires generator_index(s) < g_m(mm).num_generators,
    ensures apply_hom_symbol(kill_c(mm, n), s) =~= seq![s],
{
    let h = kill_c(mm, n);
    let nk = g_m(mm).num_generators;
    let i = generator_index(s);
    assert(i < h1_num_gens(nk, n));
    assert(h.generator_images[i as int] == seq![Symbol::Gen(i)]);
    match s {
        Symbol::Gen(j) => { },
        Symbol::Inv(j) => {
            assert(seq![Symbol::Gen(j)] =~= Seq::new(1, |_k: int| Symbol::Gen(j)));
            crate::word::lemma_inverse_singleton(Symbol::Gen(j));
            assert(Seq::new(1, |_k: int| inverse_symbol(Symbol::Gen(j))) =~= seq![Symbol::Inv(j)]);
        },
    }
}

/// On a `c`-block symbol (`nk ≤ index < nk + n`), `kill_c` kills: `s ↦ ε`.
pub proof fn lemma_kill_c_symbol_c(mm: ModMachine, n: nat, s: Symbol)
    requires
        g_m(mm).num_generators <= generator_index(s),
        generator_index(s) < g_m(mm).num_generators + n,
    ensures apply_hom_symbol(kill_c(mm, n), s) =~= empty_word(),
{
    let h = kill_c(mm, n);
    let nk = g_m(mm).num_generators;
    let i = generator_index(s);
    assert(i < h1_num_gens(nk, n));
    assert(h.generator_images[i as int] == empty_word());
    match s {
        Symbol::Gen(j) => { },
        Symbol::Inv(j) => { crate::word::lemma_inverse_empty(); },
    }
}

/// On a b/d-block symbol (`nk + n ≤ index < h1_num_gens`), `kill_c` shifts the index down by `n`:
/// `Gen(idx) ↦ [Gen(idx−n)]`, `Inv(idx) ↦ [Inv(idx−n)]`.
pub proof fn lemma_kill_c_symbol_bd(mm: ModMachine, n: nat, s: Symbol)
    requires
        g_m(mm).num_generators + n <= generator_index(s),
        generator_index(s) < h1_num_gens(g_m(mm).num_generators, n),
    ensures
        apply_hom_symbol(kill_c(mm, n), s) =~= (match s {
            Symbol::Gen(idx) => seq![Symbol::Gen((idx - n) as nat)],
            Symbol::Inv(idx) => seq![Symbol::Inv((idx - n) as nat)],
        }),
{
    let h = kill_c(mm, n);
    let nk = g_m(mm).num_generators;
    let i = generator_index(s);
    assert(!(i < nk) && !(i < nk + n));
    assert(h.generator_images[i as int] == seq![Symbol::Gen((i - n) as nat)]);
    match s {
        Symbol::Gen(idx) => { },
        Symbol::Inv(idx) => {
            assert(seq![Symbol::Gen((idx - n) as nat)]
                =~= Seq::new(1, |_k: int| Symbol::Gen((idx - n) as nat)));
            crate::word::lemma_inverse_singleton(Symbol::Gen((idx - n) as nat));
            assert(Seq::new(1, |_k: int| inverse_symbol(Symbol::Gen((idx - n) as nat)))
                =~= seq![Symbol::Inv((idx - n) as nat)]);
        },
    }
}

/// `apply_hom` on a singleton word is the per-symbol image.
pub proof fn lemma_apply_hom_singleton(h: HomomorphismData, s: Symbol)
    ensures apply_hom(h, seq![s]) =~= apply_hom_symbol(h, s),
{
    reveal_with_fuel(apply_hom, 2);
    assert(seq![s].first() == s);
    assert(seq![s].drop_first() =~= empty_word());
    assert(apply_hom(h, empty_word()) =~= empty_word());
}

// ----------------------------------------------------------------------------
// `kill_c` fixes K_M words.
// ----------------------------------------------------------------------------

/// `kill_c` fixes any word using only K_M generators (`index < nk`).
pub proof fn lemma_kill_c_fixes_low(mm: ModMachine, n: nat, w: Word)
    requires word_valid(w, g_m(mm).num_generators),
    ensures apply_hom(kill_c(mm, n), w) =~= w,
    decreases w.len(),
{
    let h = kill_c(mm, n);
    let nk = g_m(mm).num_generators;
    if w.len() == 0 {
        assert(apply_hom(h, w) =~= empty_word());
        assert(w =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, nk)) by { assert(w[0] == s); }
        assert(word_valid(rest, nk)) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], nk) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_kill_c_symbol_low(mm, n, s);
        lemma_kill_c_fixes_low(mm, n, rest);
        assert(apply_hom(h, w) =~= concat(seq![s], rest));
        assert(w =~= seq![s] + rest);
    }
}

// ----------------------------------------------------------------------------
// Each commutator `b_i c_j b_i⁻¹ c_j⁻¹` maps to `b_i' b_i'⁻¹ ≡ ε`.
// ----------------------------------------------------------------------------

/// **The commutator case.** `kill_c(comm_relator(nk,n,i,j)) = [Gen(bi−n), Inv(bi−n)] ≡ ε` in the
/// target: the `c_j`'s vanish, leaving the cancelling pair `b_i' b_i'⁻¹` (`bi' = bi − n`).
pub proof fn lemma_kill_c_on_comm_relator(mm: ModMachine, n: nat, i: nat, j: nat)
    requires 1 <= i <= n, 1 <= j <= n,
    ensures
        equiv_in_presentation(kill_c(mm, n).target,
            apply_hom(kill_c(mm, n), comm_relator(g_m(mm).num_generators, n, i, j)), empty_word()),
{
    let h = kill_c(mm, n);
    let nk = g_m(mm).num_generators;
    let bi = b_idx(nk, n, i);
    let cj = crate::layout::c_idx(nk, j);
    let r = comm_relator(nk, n, i, j);
    // bi = nk + n + (i-1) ∈ [nk+n, nk+2n-1];  cj = nk + (j-1) ∈ [nk, nk+n-1].
    assert(bi == nk + n + (i - 1));
    assert(cj == nk + (j - 1));
    assert(nk + n <= bi < h1_num_gens(nk, n));
    assert(nk <= cj < nk + n);
    let bs = (bi - n) as nat;     // = nk + (i-1) < nk + n
    // per-symbol images.
    lemma_kill_c_symbol_bd(mm, n, Symbol::Gen(bi));
    lemma_kill_c_symbol_bd(mm, n, Symbol::Inv(bi));
    lemma_kill_c_symbol_c(mm, n, Symbol::Gen(cj));
    lemma_kill_c_symbol_c(mm, n, Symbol::Inv(cj));
    assert(apply_hom_symbol(h, Symbol::Gen(bi)) =~= seq![Symbol::Gen(bs)]);
    assert(apply_hom_symbol(h, Symbol::Inv(bi)) =~= seq![Symbol::Inv(bs)]);
    assert(apply_hom_symbol(h, Symbol::Gen(cj)) =~= empty_word());
    assert(apply_hom_symbol(h, Symbol::Inv(cj)) =~= empty_word());
    // split r into singletons; push apply_hom through the concats.
    let p1 = seq![Symbol::Gen(bi)];
    let p2 = seq![Symbol::Gen(cj)];
    let p3 = seq![Symbol::Inv(bi)];
    let p4 = seq![Symbol::Inv(cj)];
    assert(r =~= p1 + p2 + p3 + p4);
    lemma_hom_respects_concat(h, p1 + p2 + p3, p4);
    lemma_hom_respects_concat(h, p1 + p2, p3);
    lemma_hom_respects_concat(h, p1, p2);
    lemma_apply_hom_singleton(h, Symbol::Gen(bi));
    lemma_apply_hom_singleton(h, Symbol::Gen(cj));
    lemma_apply_hom_singleton(h, Symbol::Inv(bi));
    lemma_apply_hom_singleton(h, Symbol::Inv(cj));
    // apply_hom(h, r) =~= (([Gen bs] + ε) + [Inv bs]) + ε  =~= [Gen bs, Inv bs].
    assert(apply_hom(h, r) =~= seq![Symbol::Gen(bs), Symbol::Inv(bs)]);
    // cancelling pair ≡ ε.
    assert(is_inverse_pair(Symbol::Gen(bs), Symbol::Inv(bs)));
    lemma_cancel_pair_equiv_empty(h.target, Symbol::Gen(bs), Symbol::Inv(bs));
}

/// The commutator case keyed by the flat relator index `idx` (recovers `(i,j)` from `idx`).  Lives
/// in its own lemma so the nonlinear `n*n` index arithmetic gets a clean context, away from the
/// heavy `is_valid_homomorphism` forall body.
pub proof fn lemma_kill_c_on_comm_idx(mm: ModMachine, n: nat, idx: int)
    requires
        mod_machine_wf(mm),
        0 <= idx < comm_relators(g_m(mm).num_generators, n).len(),
    ensures
        equiv_in_presentation(kill_c(mm, n).target,
            apply_hom(kill_c(mm, n), comm_relators(g_m(mm).num_generators, n)[idx]), empty_word()),
{
    let nk = g_m(mm).num_generators;
    assert(comm_relators(nk, n).len() == (n * n) as nat);
    assert(n > 0) by { if n == 0 { assert((n * n) as nat == 0); } }
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(idx, n as int, n as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(idx, n as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(idx, n as int);
    let ci = (idx / (n as int) + 1) as nat;
    let cjj = (idx % (n as int) + 1) as nat;
    assert(1 <= ci <= n && 1 <= cjj <= n);
    assert(comm_relators(nk, n)[idx] == comm_relator(nk, n, ci, cjj));
    lemma_kill_c_on_comm_relator(mm, n, ci, cjj);
}

// ----------------------------------------------------------------------------
// `kill_c` is a valid homomorphism.
// ----------------------------------------------------------------------------

/// `kill_c` is a valid homomorphism `h1_base → K_M ∗ F(b) ∗ ⟨d⟩`: images valid, and every source
/// relator (K_M relators — fixed, trivial in the target; commutators — killed to a cancelling pair)
/// maps to `ε`.
pub proof fn lemma_kill_c_hom_valid(mm: ModMachine, n: nat)
    requires mod_machine_wf(mm),
    ensures is_valid_homomorphism(kill_c(mm, n)),
{
    reveal(presentation_valid);
    let h = kill_c(mm, n);
    let nk = g_m(mm).num_generators;
    let ng = h1_num_gens(nk, n);
    let src = h1_base(mm, n);
    let tgt = h.target;
    let grels = g_m(mm).relators;

    lemma_h1_base_valid(mm, n);                       // presentation_valid(src)
    lemma_g_m_valid(mm);                              // presentation_valid(g_m)
    lemma_free_stable_tower_valid(g_m(mm), (n + 1) as nat);  // presentation_valid(tgt)
    lemma_free_stable_tower_closed(g_m(mm), (n + 1) as nat); // tgt.num_gens, tgt.relators
    assert(h.source == src && tgt.num_generators == nk + n + 1);
    assert(tgt.relators == grels);
    assert(h.generator_images.len() == src.num_generators);   // = h1_num_gens(nk,n)

    // (a) each generator image is word_valid over the target's nk+n+1 generators.
    assert forall|i: int| #![trigger h.generator_images[i]] 0 <= i < h.generator_images.len()
        implies word_valid(h.generator_images[i], tgt.num_generators) by {
        let gi = h.generator_images[i];
        if i < nk {
            assert(gi == seq![Symbol::Gen(i as nat)]);
            assert(symbol_valid(gi[0], tgt.num_generators)) by { assert(gi[0] == Symbol::Gen(i as nat)); }
        } else if i < nk + n {
            assert(gi == empty_word());
        } else {
            assert(gi == seq![Symbol::Gen((i - n) as nat)]);
            assert(symbol_valid(gi[0], tgt.num_generators)) by {
                assert(gi[0] == Symbol::Gen((i - n) as nat));
                assert((i - n) as nat <= nk + n);     // i ≤ nk+2n ⟹ i-n ≤ nk+n < nk+n+1
            }
        }
    }

    // (b) each relator image ≡ ε in the target.
    assert(src.relators =~= grels + comm_relators(nk, n));
    assert forall|i: int| #![trigger src.relators[i]] 0 <= i < src.relators.len()
        implies equiv_in_presentation(tgt, apply_hom(h, src.relators[i]), empty_word()) by {
        if i < grels.len() {
            // K_M relator: over gens < nk, fixed by kill_c, trivial in the target (= g_m relator).
            assert(src.relators[i] == grels[i]);
            assert(word_valid(grels[i], nk));         // from presentation_valid(g_m)
            lemma_kill_c_fixes_low(mm, n, grels[i]);
            assert(tgt.relators[i] == grels[i]);      // tgt.relators == grels
            lemma_relator_is_identity(tgt, i);
            assert(apply_hom(h, src.relators[i]) =~= grels[i]);
        } else {
            // commutator: delegate to the index-keyed helper (fresh context for the nonlinear
            // `n*n` index recovery — keeps this heavy forall body lean).
            let idx = i - grels.len();
            assert(src.relators[i] == comm_relators(nk, n)[idx]);
            assert(0 <= idx < comm_relators(nk, n).len());
            lemma_kill_c_on_comm_idx(mm, n, idx);
        }
    }
}

// ----------------------------------------------------------------------------
// The F family at the literal `h1_base` layout, and the pullback assembly.
// ----------------------------------------------------------------------------

/// `F_h1 = [t, x] ++ [Gen(nk+n), …, Gen(nk+2n)]`: `t, x` at `0, 1`, the `b_j` at the `h1_base`
/// b-block `nk+n .. nk+2n-1`, and `d` at `nk+2n` (`= d_idx`).  The appended index `nk+n+i` (`i=0..n`)
/// is uniform across the `b_j` (`i<n`) and `d` (`i=n`).
pub open spec fn f_h1_family(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    tx_family() + Seq::new((n + 1) as nat, |i: int| seq![Symbol::Gen((nk + n + i) as nat)])
}

/// `kill_c ∘ F_h1` is EXACTLY B2's tower family: `kill_c` fixes `t, x` and shifts each `b/d` index
/// down by `n`, sending the appended `Gen(nk+n+i)` to `Gen(nk+i) = free_stable_letter(nk, i)`.
pub proof fn lemma_comp_is_b2_family(mm: ModMachine, n: nat)
    requires mod_machine_wf(mm),
    ensures
        comp_images(kill_c(mm, n), f_h1_family(mm, n))
            =~= free_stable_family(g_m(mm), tx_family(), (n + 1) as nat),
{
    let nk = g_m(mm).num_generators;
    let h = kill_c(mm, n);
    let fam = f_h1_family(mm, n);
    let comp = comp_images(h, fam);
    let b2 = free_stable_family(g_m(mm), tx_family(), (n + 1) as nat);
    let b2_closed = tx_family() + Seq::new((n + 1) as nat, |i: int| free_stable_letter(nk, i));
    lemma_g_m_num_generators(mm);                     // nk = 4 + |quads| ≥ 4 > 2
    lemma_txbd_family_layout(mm, n);
    assert(b2 =~= b2_closed);
    assert(fam.len() == 2 + (n + 1));
    assert(comp.len() == fam.len());
    assert(b2_closed.len() == 2 + (n + 1));
    assert forall|k: int| 0 <= k < comp.len() implies comp[k] =~= b2[k] by {
        assert(comp[k] == apply_hom(h, fam[k]));
        assert(b2[k] == b2_closed[k]);
        if k < 2 {
            // fam[k] = tx_family()[k] = [Gen(k)]; low ⟹ image [Gen(k)]; b2_closed[k] = [Gen(k)].
            assert(fam[k] == tx_family()[k]);
            if k == 0 {
                assert(tx_family()[k] =~= seq![Symbol::Gen(0)]);
            } else {
                assert(tx_family()[k] =~= seq![Symbol::Gen(1)]);
            }
            lemma_apply_hom_singleton(h, fam[k][0]);
            lemma_kill_c_symbol_low(mm, n, fam[k][0]);
            assert(fam[k] =~= seq![fam[k][0]]);
            assert(b2_closed[k] == tx_family()[k]);
        } else {
            let i = k - 2;                            // 0 ≤ i ≤ n
            // fam[k] = [Gen(nk+n+i)]; bd ⟹ image [Gen(nk+i)]; b2_closed[k] = free_stable_letter(nk,i).
            assert(fam[k] =~= seq![Symbol::Gen((nk + n + i) as nat)]);
            let s = Symbol::Gen((nk + n + i) as nat);
            assert(nk + n <= generator_index(s) < h1_num_gens(nk, n));
            lemma_apply_hom_singleton(h, s);
            lemma_kill_c_symbol_bd(mm, n, s);
            assert(apply_hom_symbol(h, s) =~= seq![Symbol::Gen((nk + i) as nat)]);
            assert(b2_closed[k] == free_stable_letter(nk, i));
            assert(free_stable_letter(nk, i) =~= seq![Symbol::Gen((nk + i) as nat)]);
        }
    }
}

/// **B3 (headline).** `F = [t, x, b_1..b_n, d]` is a FREE family in `h1_base`.  Pullback engine at
/// `kill_c`: a relation `apply_embedding(F_h1, w) ≡ ε` in `h1_base` maps to a relation of `kill_c∘F_h1`
/// (= B2's family) in the target, which B2 (`lemma_txbd_free_in_tower`) says is free — so `w ≡_free ε`.
pub proof fn lemma_f_free_in_h1(mm: ModMachine, n: nat)
    requires mod_machine_wf(mm),
    ensures is_free_family(h1_base(mm, n), f_h1_family(mm, n)),
{
    let nk = g_m(mm).num_generators;
    let src = h1_base(mm, n);
    let fam = f_h1_family(mm, n);
    let h = kill_c(mm, n);
    let tgt = h.target;
    let b2 = free_stable_family(g_m(mm), tx_family(), (n + 1) as nat);
    lemma_g_m_num_generators(mm);
    lemma_h1_base_valid(mm, n);
    assert(src.num_generators == h1_num_gens(nk, n));

    // (1) each F_h1 image is word_valid over src.num_generators = nk + 2n + 1.
    assert forall|i: int| 0 <= i < fam.len() implies word_valid(#[trigger] fam[i], src.num_generators) by {
        if i < 2 {
            assert(fam[i] == tx_family()[i]);
            if i == 0 { assert(tx_family()[i] =~= seq![Symbol::Gen(0)]); }
            else { assert(tx_family()[i] =~= seq![Symbol::Gen(1)]); }
            assert(symbol_valid(fam[i][0], src.num_generators)) by { assert(fam[i].len() == 1); }
        } else {
            let k = i - 2;
            assert(fam[i] =~= seq![Symbol::Gen((nk + n + k) as nat)]);
            assert(symbol_valid(fam[i][0], src.num_generators)) by {
                assert(fam[i][0] == Symbol::Gen((nk + n + k) as nat));
                assert(nk + n + k <= nk + 2 * n);     // k ≤ n
            }
        }
    }

    // (2) freeness via pullback + B2.
    lemma_kill_c_hom_valid(mm, n);
    lemma_comp_is_b2_family(mm, n);                   // comp_images(h, fam) =~= b2
    lemma_txbd_free_in_tower(mm, n);                  // is_free_family(tgt, b2)
    assert(comp_images(h, fam) =~= b2);
    assert(b2.len() == fam.len());                    // comp.len() = fam.len(), comp =~= b2
    assert forall|w: Word| (#[trigger] word_valid(w, fam.len())
        && equiv_in_presentation(src, apply_embedding(fam, w), empty_word()))
        implies equiv_in_presentation(free_group(fam.len()), w, empty_word()) by {
        lemma_pullback_free(h, fam, w);
        // apply_embedding(comp_images(h, fam), w) ≡ ε in tgt; comp_images =~= b2.
        assert(apply_embedding(comp_images(h, fam), w) =~= apply_embedding(b2, w));
        assert(equiv_in_presentation(tgt, apply_embedding(b2, w), empty_word()));
        // B2 freeness instantiated at w (lengths match).
        assert(word_valid(w, b2.len()));
        assert(equiv_in_presentation(free_group(b2.len()), w, empty_word()));
    }
}

} // verus!
