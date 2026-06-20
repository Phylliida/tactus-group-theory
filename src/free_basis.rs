// Layer 2 — Brick 2 (deep half): the kill homomorphism φ: H₁ → K_M.
//
// Toward the free-basis lemma "`{ t_α w_α(b) d : α∈I }` freely generate" (blueprint
// p.279, "Mapping H₁ → K_M … and Cor 1 to Prop 1.8"). The map is **at the H₁ level**:
// identity on the K_M block `0..nk`, killing `c/b/d`. (NOT an H₃ → K_M map — that would
// be invalid, since the φ_i relator `a_i⁻¹ t a_i t_i⁻¹` maps to `t·config(i,0)⁻¹` and
// `t ≢ config(i,0)` in K_M for `i≠0`.) `H₁`'s only relators are the K_M relators (fixed
// by φ, ≡ε as K_M relators) and the commutators (all gens killed, ≡ε), so φ is a valid
// homomorphism. This module builds φ and proves `is_valid_homomorphism`.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::homomorphism::*;
use crate::machine_group::*;
use crate::word_numbering::*;
use crate::layout::*;
use crate::h1::*;

verus! {

// ----------------------------------------------------------------------------
// The kill homomorphism
// ----------------------------------------------------------------------------

/// `φ: H₁ → K_M`: identity on the K_M generators `0..nk`, every other H₁ generator
/// (`c_j, b_j, d`) mapped to the empty word.
pub open spec fn kill_hom(mm: ModMachine, n: nat) -> HomomorphismData {
    let nk = g_m(mm).num_generators;
    HomomorphismData {
        source: h1_base(mm, n),
        target: g_m(mm),
        generator_images: Seq::new(h1_num_gens(nk, n), |i: int|
            if i < nk { seq![Symbol::Gen(i as nat)] } else { empty_word() }),
    }
}

// ----------------------------------------------------------------------------
// Per-symbol behaviour
// ----------------------------------------------------------------------------

/// On a low symbol (`index < nk`), φ acts as the identity: `s ↦ [s]`.
pub proof fn lemma_kill_symbol_low(mm: ModMachine, n: nat, s: Symbol)
    requires generator_index(s) < g_m(mm).num_generators,
    ensures apply_hom_symbol(kill_hom(mm, n), s) =~= seq![s],
{
    let h = kill_hom(mm, n);
    let nk = g_m(mm).num_generators;
    let i = generator_index(s);
    assert(i < h1_num_gens(nk, n));               // nk ≤ nk + 2n + 1
    assert(h.generator_images[i as int] == seq![Symbol::Gen(i)]);
    match s {
        Symbol::Gen(j) => {
            // apply_hom_symbol(h, Gen(j)) = images[j] = [Gen(j)] = [s].
        },
        Symbol::Inv(j) => {
            // apply_hom_symbol(h, Inv(j)) = inverse_word(images[j]) = inverse_word([Gen(j)]) = [Inv(j)].
            assert(seq![Symbol::Gen(j)] =~= Seq::new(1, |_k: int| Symbol::Gen(j)));
            lemma_inverse_singleton(Symbol::Gen(j));
            assert(Seq::new(1, |_k: int| inverse_symbol(Symbol::Gen(j))) =~= seq![Symbol::Inv(j)]);
        },
    }
}

/// On a high symbol (`nk ≤ index < h1_num_gens`), φ kills: `s ↦ ε`.
pub proof fn lemma_kill_symbol_high(mm: ModMachine, n: nat, s: Symbol)
    requires
        g_m(mm).num_generators <= generator_index(s),
        generator_index(s) < h1_num_gens(g_m(mm).num_generators, n),
    ensures apply_hom_symbol(kill_hom(mm, n), s) =~= empty_word(),
{
    let h = kill_hom(mm, n);
    let i = generator_index(s);
    assert(h.generator_images[i as int] == empty_word());
    match s {
        Symbol::Gen(j) => { },
        Symbol::Inv(j) => { lemma_inverse_empty(); },
    }
}

// ----------------------------------------------------------------------------
// Word-level transport
// ----------------------------------------------------------------------------

/// φ fixes any word using only K_M generators (`index < nk`).
pub proof fn lemma_kill_fixes_low(mm: ModMachine, n: nat, w: Word)
    requires word_valid(w, g_m(mm).num_generators),
    ensures apply_hom(kill_hom(mm, n), w) =~= w,
    decreases w.len(),
{
    let h = kill_hom(mm, n);
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
        lemma_kill_symbol_low(mm, n, s);
        lemma_kill_fixes_low(mm, n, rest);
        // apply_hom(h, w) = concat(apply_hom_symbol(h, s), apply_hom(h, rest)) =~= [s] + rest =~= w.
        assert(apply_hom(h, w) =~= concat(seq![s], rest));
        assert(w =~= seq![s] + rest);
    }
}

/// φ kills any word using only the c/b/d block (`nk ≤ index < h1_num_gens`).
pub proof fn lemma_kill_kills_high(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, h1_num_gens(g_m(mm).num_generators, n)),
        forall|k: int| 0 <= k < w.len() ==> g_m(mm).num_generators <= generator_index(#[trigger] w[k]),
    ensures apply_hom(kill_hom(mm, n), w) =~= empty_word(),
    decreases w.len(),
{
    let h = kill_hom(mm, n);
    let nk = g_m(mm).num_generators;
    let ng = h1_num_gens(nk, n);
    if w.len() == 0 {
        assert(apply_hom(h, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(w[0] == s);
        assert(nk <= generator_index(s));
        assert(symbol_valid(s, ng)) by { assert(w[0] == s); }
        assert(word_valid(rest, ng)) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], ng) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        assert forall|k: int| 0 <= k < rest.len() implies nk <= generator_index(#[trigger] rest[k]) by {
            assert(rest[k] == w[k + 1]);
        }
        lemma_kill_symbol_high(mm, n, s);
        lemma_kill_kills_high(mm, n, rest);
        // apply_hom(h, w) = concat(ε, ε) = ε.
        assert(apply_hom(h, w) =~= concat(empty_word(), empty_word()));
    }
}

// ----------------------------------------------------------------------------
// Each commutator relator lies entirely in the high (c/b) block
// ----------------------------------------------------------------------------

/// Every commutator `comm_relators(nk,n)[idx]` is valid over `h1_num_gens` and uses
/// only generators `≥ nk` (so φ kills it).
pub proof fn lemma_comm_relator_high(nk: nat, n: nat, idx: int)
    requires 0 <= idx < comm_relators(nk, n).len(),
    ensures
        word_valid(comm_relators(nk, n)[idx], h1_num_gens(nk, n)),
        forall|k: int| 0 <= k < comm_relators(nk, n)[idx].len()
            ==> nk <= generator_index(#[trigger] comm_relators(nk, n)[idx][k]),
{
    // recover (i,j) ∈ 1..=n × 1..=n from idx (as in lemma_comm_relators_valid).
    assert(n > 0) by { if n == 0 { assert(n * n == 0); } }
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(idx, n as int, n as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(idx, n as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(idx, n as int);
    let i = (idx / (n as int) + 1) as nat;
    let j = (idx % (n as int) + 1) as nat;
    assert(1 <= i <= n);
    assert(1 <= j <= n);
    let r = comm_relators(nk, n)[idx];
    assert(r == comm_relator(nk, n, i, j));
    let bi = b_idx(nk, n, i);
    let cj = c_idx(nk, j);
    // bi = nk + n + (i-1) ∈ [nk+n, nk+2n-1];  cj = nk + (j-1) ∈ [nk, nk+n-1].
    assert(bi == nk + n + (i - 1));
    assert(cj == nk + (j - 1));
    // comm_relator = [Gen(bi), Gen(cj), Inv(bi), Inv(cj)]; all indices in [nk, nk+2n).
    lemma_comm_relator_valid(nk, n, i, j, h1_num_gens(nk, n));   // valid: nk+2n ≤ nk+2n+1
    assert forall|k: int| 0 <= k < r.len() implies nk <= generator_index(#[trigger] r[k]) by {
        if k == 0 { assert(r[0] == Symbol::Gen(bi)); }
        else if k == 1 { assert(r[1] == Symbol::Gen(cj)); }
        else if k == 2 { assert(r[2] == Symbol::Inv(bi)); }
        else { assert(r[3] == Symbol::Inv(cj)); }
    }
}

// ----------------------------------------------------------------------------
// φ is a valid homomorphism
// ----------------------------------------------------------------------------

/// `kill_hom` is a valid homomorphism `H₁ → K_M`: images are valid, and every H₁
/// relator (K_M relators, fixed and ≡ε; commutators, killed to ε) maps to the identity.
pub proof fn lemma_kill_hom_valid(mm: ModMachine, n: nat)
    ensures is_valid_homomorphism(kill_hom(mm, n)),
{
    reveal(presentation_valid);
    let h = kill_hom(mm, n);
    let nk = g_m(mm).num_generators;
    let ng = h1_num_gens(nk, n);
    let src = h1_base(mm, n);
    let grels = g_m(mm).relators;

    lemma_h1_base_valid(mm, n);     // presentation_valid(src)
    lemma_g_m_valid(mm);            // presentation_valid(target = g_m)
    assert(h.source == src && h.target == g_m(mm));
    assert(h.generator_images.len() == src.num_generators);   // = h1_num_gens(nk,n)

    // (a) each generator image is word_valid over the target's nk generators.
    assert forall|i: int| #![trigger h.generator_images[i]] 0 <= i < h.generator_images.len()
        implies word_valid(h.generator_images[i], nk) by {
        if i < nk {
            let gi = h.generator_images[i];
            assert(gi == seq![Symbol::Gen(i as nat)]);
            assert forall|q: int| 0 <= q < gi.len() implies symbol_valid(#[trigger] gi[q], nk) by {
                assert(gi[0] == Symbol::Gen(i as nat));
            }
        } else {
            assert(h.generator_images[i] == empty_word());
        }
    }

    // (b) each relator image ≡ ε in K_M.
    assert(src.relators =~= grels + comm_relators(nk, n));
    assert forall|i: int| #![trigger src.relators[i]] 0 <= i < src.relators.len()
        implies equiv_in_presentation(g_m(mm), apply_hom(h, src.relators[i]), empty_word()) by {
        if i < grels.len() {
            // K_M relator: uses only gens < nk (presentation_valid), fixed by φ, ≡ ε in K_M.
            assert(src.relators[i] == grels[i]);
            assert(word_valid(grels[i], nk));      // from presentation_valid(g_m)
            lemma_kill_fixes_low(mm, n, grels[i]);
            lemma_relator_is_identity(g_m(mm), i);
            assert(apply_hom(h, src.relators[i]) =~= grels[i]);
        } else {
            // commutator: uses only gens ≥ nk, killed to ε.
            let idx = i - grels.len();
            assert(src.relators[i] == comm_relators(nk, n)[idx]);
            lemma_comm_relator_high(nk, n, idx);
            lemma_kill_kills_high(mm, n, src.relators[i]);
            lemma_equiv_refl(g_m(mm), empty_word());
        }
    }
}

// ----------------------------------------------------------------------------
// φ on the candidate basis element  t_α · w_α(b) · d  ↦  t_α
// ----------------------------------------------------------------------------

/// The candidate free-basis element `t_α · w_α(b) · d` of `H₁` (one per α∈I): the
/// config word `t_α = config(α,0)`, the b-substitution `w_α(b) = h_w_b`, and `d`.
pub open spec fn basis_elt(mm: ModMachine, n: nat, m: nat, alpha: nat) -> Word {
    let nk = g_m(mm).num_generators;
    config_word(alpha, 0) + h_w_b(nk, n, m, alpha) + seq![Symbol::Gen(d_idx(nk, n))]
}

/// `φ(t_α w_α(b) d) = t_α`: φ fixes `t_α` (K_M block) and kills `w_α(b)·d`
/// (b/d block). The image is the Layer-1 free family `{t_α}` — the setup for the
/// free-basis pullback (Cohen Prop-1.8-Cor-1).
pub proof fn lemma_kill_on_basis_elt(mm: ModMachine, n: nat, m: nat, alpha: nat)
    requires numbers_word(n, m, alpha), 2 * n < m,
    ensures apply_hom(kill_hom(mm, n), basis_elt(mm, n, m, alpha)) =~= config_word(alpha, 0),
{
    let h = kill_hom(mm, n);
    let nk = g_m(mm).num_generators;
    let ng = h1_num_gens(nk, n);
    lemma_g_m_num_generators(mm);                  // nk = 4 + |quads| ≥ 4
    let tw = config_word(alpha, 0);
    let wb = h_w_b(nk, n, m, alpha);
    let dw: Word = seq![Symbol::Gen(d_idx(nk, n))];

    // φ(t_α) = t_α  (config uses gens {0,1,2} < nk).
    lemma_config_word_valid(alpha, 0);
    lemma_word_valid_mono(tw, 3, nk);
    lemma_kill_fixes_low(mm, n, tw);

    // φ(w_α(b)) = ε  (wb = w_c at b_base; gens ∈ [nk+n, nk+2n) ≥ nk, < ng).
    lemma_h_w_b_valid(nk, n, m, alpha, ng);        // word_valid(wb, ng): b_base+n = nk+2n ≤ ng
    lemma_w_c_gens_in_block(b_base(nk, n), n, m, alpha);
    assert(wb == w_c(b_base(nk, n), n, m, alpha)); // h_w_b = w_b = w_c at b_base
    assert forall|k: int| 0 <= k < wb.len() implies nk <= generator_index(#[trigger] wb[k]) by {
        assert(wb[k] == w_c(b_base(nk, n), n, m, alpha)[k]);   // fires the gens-in-block fact
    }
    lemma_kill_kills_high(mm, n, wb);

    // φ(d) = ε  (d_idx = nk+2n ≥ nk, < ng).
    assert(word_valid(dw, ng)) by {
        assert forall|q: int| 0 <= q < dw.len() implies symbol_valid(#[trigger] dw[q], ng) by {
            assert(dw[0] == Symbol::Gen(d_idx(nk, n)));
        }
    }
    assert forall|k: int| 0 <= k < dw.len() implies nk <= generator_index(#[trigger] dw[k]) by {
        assert(dw[0] == Symbol::Gen(d_idx(nk, n)));
    }
    lemma_kill_kills_high(mm, n, dw);

    // combine over the two concatenations:  φ((t_α·w_b)·d) = (t_α·ε)·ε = t_α.
    lemma_hom_respects_concat(h, tw + wb, dw);
    lemma_hom_respects_concat(h, tw, wb);
    assert(basis_elt(mm, n, m, alpha) == tw + wb + dw);
    assert(apply_hom(h, tw + wb) =~= tw);
    assert(apply_hom(h, basis_elt(mm, n, m, alpha)) =~= tw);
}

} // verus!
