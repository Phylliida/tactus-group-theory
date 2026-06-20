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
use crate::benign::*;
use crate::higman_operations::*;
use crate::hnn::*;
use crate::config_reduce::*;

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

// ============================================================================
// PHASE 1 — The abstract free-basis pullback engine (Cohen, Cor 1 to Prop 1.8).
//
// φ: G → H a homomorphism; a family `{y_i} ⊆ G` whose images `{φ(y_i)}` form a
// FREE family in H ⟹ `{y_i}` is a free family in G, and φ restricts to an
// isomorphism of the generated subgroups. We work in the established
// `apply_embedding` / `free_group` vocabulary (benign.rs / higman_operations.rs)
// so the result feeds `hnn_associations_isomorphic` (hnn.rs) and the brick-5
// Britton argument directly.
//
// The engine is parameterised over a `HomomorphismData` h and an embedding
// `emb: Seq<Word>` of "basis" words into `h.source`. Its composite into the
// target is `comp_images(h, emb)` (index i ↦ φ(emb[i])). NONE of the engine
// depends on the deep Layer-1 freeness of the config words — that input (F2) is
// supplied separately and combined downstream.
// ============================================================================

/// The φ-images of an embedding: `comp_images(h, emb)[i] = φ(emb[i])`.
pub open spec fn comp_images(h: HomomorphismData, emb: Seq<Word>) -> Seq<Word> {
    Seq::new(emb.len(), |i: int| apply_hom(h, emb[i]))
}

/// `apply_hom` and `apply_embedding` are the same index-wise substitution: applying
/// the homomorphism `h` equals applying its `generator_images` as an embedding.
pub proof fn lemma_apply_hom_eq_embedding(h: HomomorphismData, w: Word)
    ensures apply_hom(h, w) =~= apply_embedding(h.generator_images, w),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        lemma_apply_hom_eq_embedding(h, rest);
        // apply_hom_symbol(h, s) == apply_embedding_symbol(h.generator_images, s) by the
        // identical match arms (Gen ↦ images[i], Inv ↦ inverse_word(images[i])).
        match s {
            Symbol::Gen(_i) => { },
            Symbol::Inv(_i) => { },
        }
        assert(apply_hom(h, w)
            =~= concat(apply_hom_symbol(h, s), apply_hom(h, rest)));
        assert(apply_embedding(h.generator_images, w)
            =~= concat(apply_embedding_symbol(h.generator_images, s),
                       apply_embedding(h.generator_images, rest)));
    }
}

/// φ commutes with `apply_embedding`: `φ(apply_embedding(emb, w)) = apply_embedding(φ∘emb, w)`.
/// (Composition of the homomorphism with an embedding is the embedding by the images.)
pub proof fn lemma_apply_hom_embedding_compose(h: HomomorphismData, emb: Seq<Word>, w: Word)
    requires word_valid(w, emb.len()),
    ensures
        apply_hom(h, apply_embedding(emb, w)) =~= apply_embedding(comp_images(h, emb), w),
    decreases w.len(),
{
    let comp = comp_images(h, emb);
    assert(comp.len() == emb.len());
    if w.len() == 0 {
        // both sides ε
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, emb.len())) by { assert(w[0] == s); }
        assert(word_valid(rest, emb.len())) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], emb.len()) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_apply_hom_embedding_compose(h, emb, rest);

        // head symbol: φ(apply_embedding_symbol(emb, s)) = apply_embedding_symbol(comp, s).
        match s {
            Symbol::Gen(i) => {
                assert(i < emb.len());
                // apply_embedding_symbol(emb, Gen(i)) = emb[i]; φ(emb[i]) = comp[i].
                assert(apply_embedding_symbol(emb, s) == emb[i as int]);
                assert(comp[i as int] == apply_hom(h, emb[i as int]));
                assert(apply_embedding_symbol(comp, s) == comp[i as int]);
            },
            Symbol::Inv(i) => {
                assert(i < emb.len());
                // apply_embedding_symbol(emb, Inv(i)) = inverse_word(emb[i]);
                // φ(inverse_word(emb[i])) = inverse_word(φ(emb[i])) = inverse_word(comp[i]).
                assert(apply_embedding_symbol(emb, s) == inverse_word(emb[i as int]));
                lemma_hom_respects_inverse(h, emb[i as int]);
                assert(comp[i as int] == apply_hom(h, emb[i as int]));
                assert(apply_embedding_symbol(comp, s) == inverse_word(comp[i as int]));
            },
        }
        // splice: φ(emb·w) = φ(headImg) · φ(emb·rest) = comp(headImg) · comp(rest).
        assert(apply_embedding(emb, w)
            =~= concat(apply_embedding_symbol(emb, s), apply_embedding(emb, rest)));
        lemma_hom_respects_concat(h, apply_embedding_symbol(emb, s), apply_embedding(emb, rest));
        assert(apply_embedding(comp, w)
            =~= concat(apply_embedding_symbol(comp, s), apply_embedding(comp, rest)));
    }
}

/// **F3 — free words map trivially.** A word `w` that is trivial in the free group on
/// `emb.len()` letters maps under ANY valid embedding to a word `≡ ε`. (The free group
/// has no relators, so any assignment of generators to valid target words is a valid
/// homomorphism; equivalence is then preserved.)
pub proof fn lemma_free_to_embedding(emb: Seq<Word>, target: Presentation, w: Word)
    requires
        presentation_valid(target),
        forall|i: int| 0 <= i < emb.len() ==> word_valid(#[trigger] emb[i], target.num_generators),
        word_valid(w, emb.len()),
        equiv_in_presentation(free_group(emb.len()), w, empty_word()),
    ensures
        equiv_in_presentation(target, apply_embedding(emb, w), empty_word()),
{
    let k = emb.len();
    let h = HomomorphismData { source: free_group(k), target, generator_images: emb };
    lemma_free_group_valid(k);
    // is_valid_homomorphism(h): images valid, both presentations valid, NO source relators.
    assert(is_valid_homomorphism(h)) by {
        reveal(presentation_valid);
        assert(h.generator_images.len() == h.source.num_generators);
        assert(h.source.relators.len() == 0);   // free_group has empty relators
    }
    lemma_hom_preserves_equiv(h, w, empty_word());
    // apply_hom(h, w) = apply_embedding(emb, w);  apply_hom(h, ε) = ε.
    lemma_apply_hom_eq_embedding(h, w);
    assert(apply_hom(h, empty_word()) =~= empty_word());
}

/// **The pullback engine (Cohen Cor 1 to Prop 1.8).** If a basis embedding `emb` of words
/// into `h.source` satisfies a relation `apply_embedding(emb, w) ≡ ε` in the source, then the
/// φ-image relation `apply_embedding(φ∘emb, w) ≡ ε` holds in the target. (Just: φ preserves
/// equivalence, and φ commutes with `apply_embedding`.) Combined with target-side FREENESS of
/// `φ∘emb` this yields `w ≡_free ε`, i.e. `emb` is itself a free family.
pub proof fn lemma_pullback_free(h: HomomorphismData, emb: Seq<Word>, w: Word)
    requires
        is_valid_homomorphism(h),
        forall|i: int| 0 <= i < emb.len() ==> word_valid(#[trigger] emb[i], h.source.num_generators),
        word_valid(w, emb.len()),
        equiv_in_presentation(h.source, apply_embedding(emb, w), empty_word()),
    ensures
        equiv_in_presentation(h.target, apply_embedding(comp_images(h, emb), w), empty_word()),
{
    let big = apply_embedding(emb, w);
    lemma_hom_preserves_equiv(h, big, empty_word());
    // φ(big) ≡_target φ(ε) = ε.
    assert(apply_hom(h, empty_word()) =~= empty_word());
    // φ(big) = apply_embedding(comp_images, w).
    lemma_apply_hom_embedding_compose(h, emb, w);
}

// ============================================================================
// F2a — Base faithfulness `base_A ↪ K_M = g_m`.
//
// The kill homomorphism legitimately targets `g_m` (it is the identity on the
// K_M block), so the config-word relations produced by the pullback engine land
// at `g_m` level. Config words live in `base_A` (gens {t,x,y}), at the bottom of
// the `g_m` HNN tower. The reduced-CanonLetter nontriviality result
// (`lemma_canw_eval_nontrivial`) is stated at `base_A` level. So we need: a base
// word `≡ ε` in `g_m` is already `≡ ε` in `base_A`.
//
// `lemma_b_m_equiv_faithful` already gives `b_m → base_A`. We add the single top
// HNN layer `g_m = HNN(b_m, k)`, whose associations `g_m_associations` are all
// DIAGONAL `(w,w)` (k commutes with `t` and each stable letter), making its
// association-isomorphism trivial. Peel it with `lemma_single_hnn_base_faithful`.
// ============================================================================

/// `g_m`'s top HNN layer (`k`) has DIAGONAL associations: `assoc[i].0 == assoc[i].1`.
pub proof fn lemma_g_m_assoc_diagonal(mm: ModMachine)
    ensures
        forall|i: int| 0 <= i < g_m_associations(mm).len()
            ==> #[trigger] g_m_associations(mm)[i].0 == g_m_associations(mm)[i].1,
{
    let assocs = g_m_associations(mm);
    assert forall|i: int| 0 <= i < assocs.len() implies
        #[trigger] assocs[i].0 == assocs[i].1 by {
        if i == 0 {
            // (seq![Gen 0], seq![Gen 0])
        } else {
            let g = Symbol::Gen((3 + (i - 1)) as nat);
            assert(assocs[i].0 == seq![g] && assocs[i].1 == seq![g]);
        }
    }
}

/// `g_m`'s top HNN datum has isomorphic associated subgroups — trivially, since the
/// associations are diagonal (`a_words == b_words`).
pub proof fn lemma_g_m_data_isomorphic(mm: ModMachine)
    ensures
        hnn_associations_isomorphic(HNNData { base: b_m(mm), associations: g_m_associations(mm) }),
{
    let data = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    let k = data.associations.len();
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    lemma_g_m_assoc_diagonal(mm);
    assert(a_words =~= b_words) by {
        assert forall|i: int| 0 <= i < k implies a_words[i] == b_words[i] by {
            // a_words[i] = assoc[i].0 == assoc[i].1 = b_words[i] by diagonal
        }
    }
    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word())
    ) by {
        assert(apply_embedding(a_words, w) =~= apply_embedding(b_words, w));
    }
}

/// **Base faithfulness `base_A ↪ g_m`.** A `base_A` word (`word_valid(·, 3)`) that is
/// `≡ ε` in `K_M = g_m` is already `≡ ε` in `base_A`. (Peel the top `k`-layer, then
/// descend the `b_m` tower with `lemma_b_m_equiv_faithful`.)
pub proof fn lemma_g_m_base_faithful(mm: ModMachine, w: Word)
    requires
        mod_machine_wf(mm),
        word_valid(w, 3),
        equiv_in_presentation(g_m(mm), w, empty_word()),
    ensures
        equiv_in_presentation(base_A(), w, empty_word()),
{
    let data = HNNData { base: b_m(mm), associations: g_m_associations(mm) };
    assert(g_m(mm) == hnn_presentation(data));

    lemma_b_m_valid(mm);
    lemma_b_m_upto_num_generators(mm, mm.quads.len());
    assert(b_m(mm) == b_m_upto(mm, mm.quads.len()));
    assert(data.base.num_generators == (3 + mm.quads.len()) as nat);
    lemma_g_m_associations_valid(mm);
    assert(hnn_data_valid(data));
    lemma_g_m_data_isomorphic(mm);

    lemma_word_valid_mono(w, 3, data.base.num_generators);
    // peel the k-layer: equiv at g_m ⟹ equiv at b_m.
    lemma_single_hnn_base_faithful(data, w);
    // descend the b_m tower: equiv at b_m ⟹ equiv at base_A.
    assert(word_valid(empty_word(), 3));
    lemma_b_m_equiv_faithful(mm, w, empty_word());
}

// ============================================================================
// F2b — The config-word product is a CanonLetter evaluation.
//
// `config_emb(alphas)[i] = t_{α_i} = config_word(alphas[i], 0)`. The word
// `apply_embedding(config_emb, w)` (a product of `t_α^{±1}` spelled by `w`) equals
// `canw_eval(canon)` where `canon` reads each `w`-symbol as a CanonLetter at
// coordinate `(α_i, 0)` with exponent `±1`. This routes the config-word algebra
// into the CanonLetter normal-form machinery (`cw_reduce`, the nontriviality of
// reduced sequences) that Layer 1 already developed.
// ============================================================================

/// The config-word embedding: index `i ↦ t_{α_i} = config_word(alphas[i], 0)`.
pub open spec fn config_emb(alphas: Seq<nat>) -> Seq<Word> {
    Seq::new(alphas.len(), |i: int| config_word(alphas[i], 0))
}

/// The CanonLetter for one source symbol: `Gen(i) ↦ {α_i, 0, +1}`, `Inv(i) ↦ {α_i, 0, -1}`.
pub open spec fn sym_to_canl(alphas: Seq<nat>, s: Symbol) -> CanonLetter {
    match s {
        Symbol::Gen(i) => CanonLetter { r: alphas[i as int] as int, s: 0, e: 1 },
        Symbol::Inv(i) => CanonLetter { r: alphas[i as int] as int, s: 0, e: -1 },
    }
}

/// The CanonLetter sequence reading each `w`-symbol via `sym_to_canl`.
pub open spec fn w_to_canon(alphas: Seq<nat>, w: Word) -> Seq<CanonLetter> {
    Seq::new(w.len(), |j: int| sym_to_canl(alphas, w[j]))
}

/// One symbol: `φ_config(s) = canl_eval(sym_to_canl(s))`.
pub proof fn lemma_config_symbol_to_canl(alphas: Seq<nat>, s: Symbol)
    requires symbol_valid(s, alphas.len()),
    ensures
        apply_embedding_symbol(config_emb(alphas), s) =~= canl_eval(sym_to_canl(alphas, s)),
{
    let emb = config_emb(alphas);
    match s {
        Symbol::Gen(i) => {
            assert(i < alphas.len());
            let a = alphas[i as int] as int;
            lemma_sconfig_nat(a, 0);             // sconfig(a,0) =~= config_word(a as nat, 0)
            lemma_sconfig_is_gsconfig1(a, 0);    // sconfig(a,0) =~= gsconfig(a,0,1)
            assert(apply_embedding_symbol(emb, s) == emb[i as int]);
            assert(emb[i as int] == config_word(alphas[i as int], 0));
            // config_word(a,0) =~= sconfig(a,0) =~= gsconfig(a,0,1) = canl_eval({a,0,1})
        },
        Symbol::Inv(i) => {
            assert(i < alphas.len());
            let a = alphas[i as int] as int;
            lemma_sconfig_nat(a, 0);
            lemma_sconfig_is_gsconfig1(a, 0);
            lemma_gsconfig_inverse(a, 0, 1);     // inverse_word(gsconfig(a,0,1)) =~= gsconfig(a,0,-1)
            assert(apply_embedding_symbol(emb, s) == inverse_word(emb[i as int]));
            assert(emb[i as int] == config_word(alphas[i as int], 0));
            // inverse_word(config_word(a,0)) =~= inverse_word(gsconfig(a,0,1)) =~= gsconfig(a,0,-1)
        },
    }
}

/// **F2b.** `apply_embedding(config_emb, w) = canw_eval(w_to_canon(alphas, w))`.
pub proof fn lemma_config_emb_eq_canw(alphas: Seq<nat>, w: Word)
    requires word_valid(w, alphas.len()),
    ensures
        apply_embedding(config_emb(alphas), w) =~= canw_eval(w_to_canon(alphas, w)),
    decreases w.len(),
{
    let emb = config_emb(alphas);
    let canon = w_to_canon(alphas, w);
    if w.len() == 0 {
        // both empty
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, alphas.len())) by { assert(w[0] == s); }
        assert(word_valid(rest, alphas.len())) by {
            assert forall|k: int| 0 <= k < rest.len() implies symbol_valid(#[trigger] rest[k], alphas.len()) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        assert(canon[0] == sym_to_canl(alphas, s)) by { assert(w[0] == s); }
        assert(canon.drop_first() =~= w_to_canon(alphas, rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies
                canon.drop_first()[j] == w_to_canon(alphas, rest)[j] by {
                assert(canon.drop_first()[j] == canon[j + 1]);
                assert(rest[j] == w[j + 1]);
            }
        }
        lemma_config_symbol_to_canl(alphas, s);
        lemma_config_emb_eq_canw(alphas, rest);
        // apply_embedding(emb,w) = φ(s) ++ apply_embedding(emb,rest)
        //                       =~= canl_eval(canon[0]) ++ canw_eval(canon.drop_first()) = canw_eval(canon)
        assert(apply_embedding(emb, w)
            =~= concat(apply_embedding_symbol(emb, s), apply_embedding(emb, rest)));
        assert(canw_eval(canon) =~= canl_eval(canon[0]) + canw_eval(canon.drop_first()));
    }
}

} // verus!
