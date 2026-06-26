use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::machine_group::{symbol_power, word_power, lemma_symbol_power_valid};

verus! {

// ===========================================================================
// GAP-1, §9.2-item-(1): the Miller §4.1 substitute-and-collapse images `uⱼ(a,t)`.
//
// `docs/final-gate-axiom-removal-plan.md` §3/§8.5/§9.2.  This module holds the
// **routing-invariant core** of the substitution that collapses the growing-generator Miller
// slice `G^(M)` to its genuine finite generating set `{a,t}` — i.e. the words `uⱼ` that the
// c-generators map to.  It is **definitions only** (plus pure-syntax well-formedness hygiene).
// The two faithfulness directions (§9.2-item-2, `embedding_injective`/`embedding_preserving`)
// and the direct-limit commutation glue (§9.2-item-3) are deliberately NOT here — they are the
// effort-gated build; this brick just pins the textbook object so that build starts from it.
//
// Index layout, read off `cohen_layer05.rs:60` (the alphabet of `miller_data(M)`):
//   c-block  cⱼ = Gen(j)   (j < M),     a = Gen(M),   b = Gen(M+1),   t = Gen(M+2) (HNN stable).
// So the repo's `cⱼ = Gen(j)` is Miller's `c_{j+1}` — the `i ≥ 1` family, repo-indexed from 0
// (the A-column `acol_elt(M,j)` uses exponent `j+1`).  Hence below the Miller exponent is `i = j+1`.
//
// Miller §4.1 collapse (the decisive lines, recorded in gate-doc §8.5), read off the
// `miller_data` HNN associations:
//   - col 0 association  `t⁻¹ b t = a`            ⟹  b = t a t⁻¹.
//   - col j+1 association `t⁻¹ (cⱼ a⁻ⁱ b aⁱ) t = b⁻ⁱ a bⁱ`  (i = j+1)  ⟹
//         cⱼ = t · b⁻ⁱ · a · bⁱ · t⁻¹ · a⁻ⁱ · b⁻¹ · aⁱ.
//   Substituting `b ↦ t a t⁻¹` (so `b⁻¹ ↦ t a⁻¹ t⁻¹`) gives `cⱼ = uⱼ(a,t)`.
//
// `uⱼ` is the **mechanical** word-substitution of Miller's word (NO algebraic reduction — that
// would be the "Literal Fallacy"): every `b` symbol becomes the 3-letter word `t a t⁻¹`, every
// `b⁻¹` becomes `t a⁻¹ t⁻¹`, leaving the result manifestly Miller's object.
//
// Everything is **parametrized over `(a_idx, t_idx)`** — the indices where `a` and `t` live in the
// chosen codomain — so the definition pre-commits NEITHER of §9.4's two reserved packaging choices:
//   - "wrap in place" (collapsed object as a subgroup of `G^(M)`):  a_idx = M,  t_idx = M+2;
//   - "fresh `{a,t}` presentation" (Cohen's literal n=2 input):     a_idx = 0,  t_idx = 1.
// Both instantiate the SAME parametrized words; the codomain choice stays with Danielle.
// ===========================================================================

/// The collapsed `b` as a word over `{a,t}`:  `b = t · a · t⁻¹`.
pub open spec fn b_sub(a_idx: nat, t_idx: nat) -> Word {
    seq![Symbol::Gen(t_idx), Symbol::Gen(a_idx), Symbol::Inv(t_idx)]
}

/// The collapsed `b⁻¹`:  `b⁻¹ = t · a⁻¹ · t⁻¹`  (= `inverse_word(b_sub)`).
pub open spec fn binv_sub(a_idx: nat, t_idx: nat) -> Word {
    seq![Symbol::Gen(t_idx), Symbol::Inv(a_idx), Symbol::Inv(t_idx)]
}

/// Miller's collapse image of the c-generator `cⱼ = Gen(j)` (Miller exponent `i = j+1`):
///   uⱼ = t · b⁻ⁱ · a · bⁱ · t⁻¹ · a⁻ⁱ · b⁻¹ · aⁱ ,   with  b ↦ t a t⁻¹  substituted mechanically.
/// Word over `{a_idx, t_idx}` only — codomain-neutral (see module header).
pub open spec fn miller_collapse_word(j: nat, a_idx: nat, t_idx: nat) -> Word {
    let i = (j + 1) as nat;
    seq![Symbol::Gen(t_idx)]                       // t
        + word_power(binv_sub(a_idx, t_idx), i)    // b⁻ⁱ  = (t a⁻¹ t⁻¹)ⁱ
        + seq![Symbol::Gen(a_idx)]                 // a
        + word_power(b_sub(a_idx, t_idx), i)       // bⁱ   = (t a t⁻¹)ⁱ
        + seq![Symbol::Inv(t_idx)]                 // t⁻¹
        + symbol_power(Symbol::Inv(a_idx), i)      // a⁻ⁱ
        + binv_sub(a_idx, t_idx)                   // b⁻¹  = t a⁻¹ t⁻¹
        + symbol_power(Symbol::Gen(a_idx), i)      // aⁱ
}

/// The full per-slice collapse substitution `emb_M` for `miller_data(M)`, as a `Seq<Word>` over the
/// slice generators (length `M+3`, matching `hnn_presentation(miller_data(M)).num_generators`):
///   c-block `Gen(j) ↦ uⱼ` (j<M),   `a = Gen(M) ↦ a`,   `b = Gen(M+1) ↦ t a t⁻¹`,   `t = Gen(M+2) ↦ t`.
/// Parametrized over `(a_idx, t_idx)` — codomain-neutral.  This is the literal `Seq<Word>` that
/// `apply_embedding`/`embedding_injective` (the gated item-2) will eventually consume; it is only
/// *defined* here, never reasoned about under equivalence.
pub open spec fn miller_collapse_emb(big_m: nat, a_idx: nat, t_idx: nat) -> Seq<Word> {
    Seq::new(big_m, |j: int| miller_collapse_word(j as nat, a_idx, t_idx))
        + seq![
            seq![Symbol::Gen(a_idx)],     // a  ↦ a
            b_sub(a_idx, t_idx),          // b  ↦ t a t⁻¹
            seq![Symbol::Gen(t_idx)]      // t  ↦ t
          ]
}

// ---------------------------------------------------------------------------
// Pure-syntax hygiene (no equivalence / no faithfulness — see header).
// ---------------------------------------------------------------------------

/// `b_sub`/`binv_sub` are valid words whenever `a` and `t` fit in the generator count.
pub proof fn lemma_bt_words_valid(a_idx: nat, t_idx: nat, g: nat)
    requires
        a_idx < g,
        t_idx < g,
    ensures
        word_valid(b_sub(a_idx, t_idx), g),
        word_valid(binv_sub(a_idx, t_idx), g),
{
    assert forall|k: int| 0 <= k < b_sub(a_idx, t_idx).len()
        implies symbol_valid(#[trigger] b_sub(a_idx, t_idx)[k], g) by {
        // entries are Gen(t), Gen(a), Inv(t)
    }
    assert forall|k: int| 0 <= k < binv_sub(a_idx, t_idx).len()
        implies symbol_valid(#[trigger] binv_sub(a_idx, t_idx)[k], g) by {
        // entries are Gen(t), Inv(a), Inv(t)
    }
}

/// `word_power(w, n)` is valid whenever `w` is — local induction (no `machine_group` analog).
pub proof fn lemma_word_power_valid(w: Word, n: nat, g: nat)
    requires
        word_valid(w, g),
    ensures
        word_valid(word_power(w, n), g),
    decreases n,
{
    if n == 0 {
        assert(word_power(w, 0) =~= empty_word());
    } else {
        let k = (n - 1) as nat;
        lemma_word_power_valid(w, k, g);
        // word_power(w, n) = w + word_power(w, k)
        lemma_concat_word_valid(w, word_power(w, k), g);
        assert(word_power(w, n) =~= concat(w, word_power(w, k)));
    }
}

/// The collapse image `uⱼ` is a valid word in any group whose generator count exceeds both indices.
pub proof fn lemma_miller_collapse_word_valid(j: nat, a_idx: nat, t_idx: nat, g: nat)
    requires
        a_idx < g,
        t_idx < g,
    ensures
        word_valid(miller_collapse_word(j, a_idx, t_idx), g),
{
    let i = (j + 1) as nat;
    let p0 = seq![Symbol::Gen(t_idx)];
    let p1 = word_power(binv_sub(a_idx, t_idx), i);
    let p2 = seq![Symbol::Gen(a_idx)];
    let p3 = word_power(b_sub(a_idx, t_idx), i);
    let p4 = seq![Symbol::Inv(t_idx)];
    let p5 = symbol_power(Symbol::Inv(a_idx), i);
    let p6 = binv_sub(a_idx, t_idx);
    let p7 = symbol_power(Symbol::Gen(a_idx), i);

    // each atomic piece is valid
    assert(word_valid(p0, g)) by {
        assert forall|k: int| 0 <= k < p0.len() implies symbol_valid(#[trigger] p0[k], g) by { }
    }
    assert(word_valid(p2, g)) by {
        assert forall|k: int| 0 <= k < p2.len() implies symbol_valid(#[trigger] p2[k], g) by { }
    }
    assert(word_valid(p4, g)) by {
        assert forall|k: int| 0 <= k < p4.len() implies symbol_valid(#[trigger] p4[k], g) by { }
    }
    lemma_bt_words_valid(a_idx, t_idx, g);                       // p6 (= binv_sub) and b_sub valid
    lemma_word_power_valid(binv_sub(a_idx, t_idx), i, g);        // p1
    lemma_word_power_valid(b_sub(a_idx, t_idx), i, g);           // p3
    lemma_symbol_power_valid(Symbol::Inv(a_idx), i, g);          // p5
    lemma_symbol_power_valid(Symbol::Gen(a_idx), i, g);          // p7

    // fold the left-associated concatenation `p0+p1+...+p7`
    lemma_concat_word_valid(p0, p1, g);
    lemma_concat_word_valid(p0 + p1, p2, g);
    lemma_concat_word_valid(p0 + p1 + p2, p3, g);
    lemma_concat_word_valid(p0 + p1 + p2 + p3, p4, g);
    lemma_concat_word_valid(p0 + p1 + p2 + p3 + p4, p5, g);
    lemma_concat_word_valid(p0 + p1 + p2 + p3 + p4 + p5, p6, g);
    lemma_concat_word_valid(p0 + p1 + p2 + p3 + p4 + p5 + p6, p7, g);
}

/// `emb_M` has exactly one image per slice generator (`M+3`).
pub proof fn lemma_miller_collapse_emb_len(big_m: nat, a_idx: nat, t_idx: nat)
    ensures
        miller_collapse_emb(big_m, a_idx, t_idx).len() == big_m + 3,
{
}

/// Every image word in `emb_M` is valid in a group with `>` both indices — i.e. `emb_M` is a
/// well-formed list of generator images into such a codomain.
pub proof fn lemma_miller_collapse_emb_valid(big_m: nat, a_idx: nat, t_idx: nat, g: nat)
    requires
        a_idx < g,
        t_idx < g,
    ensures
        forall|k: int| 0 <= k < miller_collapse_emb(big_m, a_idx, t_idx).len()
            ==> word_valid(#[trigger] miller_collapse_emb(big_m, a_idx, t_idx)[k], g),
{
    let emb = miller_collapse_emb(big_m, a_idx, t_idx);
    let pre = Seq::new(big_m, |j: int| miller_collapse_word(j as nat, a_idx, t_idx));
    let suf = seq![
        seq![Symbol::Gen(a_idx)],
        b_sub(a_idx, t_idx),
        seq![Symbol::Gen(t_idx)]
    ];
    assert(emb =~= pre + suf);
    lemma_bt_words_valid(a_idx, t_idx, g);
    assert forall|k: int| 0 <= k < emb.len()
        implies word_valid(#[trigger] emb[k], g) by {
        if k < big_m {
            assert(emb[k] == pre[k]);
            assert(pre[k] == miller_collapse_word(k as nat, a_idx, t_idx));
            lemma_miller_collapse_word_valid(k as nat, a_idx, t_idx, g);
        } else {
            // tail entries: a ↦ [Gen(a)], b ↦ b_sub, t ↦ [Gen(t)]
            assert(emb[k] == suf[k - big_m]);
            if k == big_m {
                assert forall|m: int| 0 <= m < emb[k].len()
                    implies symbol_valid(#[trigger] emb[k][m], g) by { }
            } else if k == big_m + 1 {
                // emb[k] == b_sub, already shown valid
            } else {
                assert forall|m: int| 0 <= m < emb[k].len()
                    implies symbol_valid(#[trigger] emb[k][m], g) by { }
            }
        }
    }
}

} // verus!
