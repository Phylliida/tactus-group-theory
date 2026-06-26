use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat};
use crate::machine_group::{symbol_power, word_power, lemma_symbol_power_one, lemma_symbol_power_merge,
    lemma_word_power_symbol};
use crate::miller_collapse::{b_sub, binv_sub, miller_collapse_word, miller_collapse_emb};

verus! {

// ===========================================================================
// GAP-1 §9.2-item-(2) — the `apply_embedding` evaluator for `miller_collapse_emb`.
//
// Pure-syntax plumbing under the well-definedness brick: how `emb_M = miller_collapse_emb(M,a,t)`
// maps the slice generators, and how `apply_embedding` interacts with singletons and symbol-powers.
// No equivalence reasoning here (that is `miller_collapse_assoc` + the association lemma).
// ===========================================================================

// --- generic apply_embedding helpers (any embedding) ---

/// `apply_embedding(emb, [s]) = apply_embedding_symbol(emb, s)`.
pub proof fn lemma_apply_embedding_singleton(emb: Seq<Word>, s: Symbol)
    ensures
        apply_embedding(emb, seq![s]) =~= apply_embedding_symbol(emb, s),
{
    reveal_with_fuel(apply_embedding, 2);
    assert(seq![s].len() == 1);
    assert(seq![s].first() == s);
    assert(seq![s].drop_first() =~= empty_word());
}

/// `apply_embedding(emb, sⁿ) = (apply_embedding_symbol(emb, s))ⁿ` — embedding a symbol-power.
pub proof fn lemma_apply_embedding_symbol_power(emb: Seq<Word>, s: Symbol, n: nat)
    ensures
        apply_embedding(emb, symbol_power(s, n))
            =~= word_power(apply_embedding_symbol(emb, s), n),
    decreases n,
{
    let img = apply_embedding_symbol(emb, s);
    if n == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
        assert(apply_embedding(emb, empty_word()) =~= empty_word());
        assert(word_power(img, 0) =~= empty_word());
    } else {
        let k = (n - 1) as nat;
        // symbol_power(s, n) = [s] + symbol_power(s, k)
        lemma_symbol_power_one(s);
        lemma_symbol_power_merge(s, 1, k);
        assert(symbol_power(s, n) =~= seq![s] + symbol_power(s, k));

        lemma_apply_embedding_concat(emb, seq![s], symbol_power(s, k));
        lemma_apply_embedding_singleton(emb, s);
        lemma_apply_embedding_symbol_power(emb, s, k);     // IH
        // apply_embedding(emb, sⁿ) = img + word_power(img, k) = word_power(img, n)
        assert(word_power(img, n) =~= img + word_power(img, k));
    }
}

/// `word_power([s], i) = sⁱ` — a singleton's word-power is the symbol-power.
pub proof fn lemma_word_power_singleton(s: Symbol, i: nat)
    ensures
        word_power(seq![s], i) =~= symbol_power(s, i),
{
    lemma_symbol_power_one(s);
    assert(seq![s] =~= symbol_power(s, 1));
    lemma_word_power_symbol(s, 1, i);   // word_power(symbol_power(s,1), i) =~= symbol_power(s, 1*i)
    assert((1 * i) as nat == i);
}

/// `apply_embedding(emb, Gen(k)ⁱ) = (emb[k])ⁱ` and the `Inv(k)` analog — embedding a generator-power.
pub proof fn lemma_emb_gen_power(emb: Seq<Word>, k: nat, i: nat)
    ensures
        apply_embedding(emb, symbol_power(Symbol::Gen(k), i)) =~= word_power(emb[k as int], i),
        apply_embedding(emb, symbol_power(Symbol::Inv(k), i)) =~= word_power(inverse_word(emb[k as int]), i),
{
    lemma_apply_embedding_symbol_power(emb, Symbol::Gen(k), i);
    assert(apply_embedding_symbol(emb, Symbol::Gen(k)) == emb[k as int]);
    lemma_apply_embedding_symbol_power(emb, Symbol::Inv(k), i);
    assert(apply_embedding_symbol(emb, Symbol::Inv(k)) == inverse_word(emb[k as int]));
}

// --- miller_collapse_emb index access (off the Seq::new + seq! structure) ---

/// `emb_M` splits as the `M`-length head of `uⱼ` images plus the 3-element `[a], b_sub, [t]` tail.
proof fn lemma_emb_split(big_m: nat, a_idx: nat, t_idx: nat)
    ensures
        miller_collapse_emb(big_m, a_idx, t_idx)
            =~= Seq::new(big_m, |j: int| miller_collapse_word(j as nat, a_idx, t_idx))
                + seq![seq![Symbol::Gen(a_idx)], b_sub(a_idx, t_idx), seq![Symbol::Gen(t_idx)]],
{
}

/// `emb_M[j] = uⱼ`  (the c-block image, `j < M`).
pub proof fn lemma_emb_head(big_m: nat, a_idx: nat, t_idx: nat, j: nat)
    requires
        j < big_m,
    ensures
        miller_collapse_emb(big_m, a_idx, t_idx)[j as int]
            == miller_collapse_word(j, a_idx, t_idx),
{
    let pre = Seq::new(big_m, |k: int| miller_collapse_word(k as nat, a_idx, t_idx));
    lemma_emb_split(big_m, a_idx, t_idx);
    assert(miller_collapse_emb(big_m, a_idx, t_idx)[j as int] == pre[j as int]);
}

/// `emb_M[M] = [a]`  (the `a ↦ a` image).
pub proof fn lemma_emb_a(big_m: nat, a_idx: nat, t_idx: nat)
    ensures
        miller_collapse_emb(big_m, a_idx, t_idx)[big_m as int] == seq![Symbol::Gen(a_idx)],
{
    let pre = Seq::new(big_m, |k: int| miller_collapse_word(k as nat, a_idx, t_idx));
    let suf = seq![seq![Symbol::Gen(a_idx)], b_sub(a_idx, t_idx), seq![Symbol::Gen(t_idx)]];
    lemma_emb_split(big_m, a_idx, t_idx);
    assert(miller_collapse_emb(big_m, a_idx, t_idx)[big_m as int] == suf[0]);
}

/// `emb_M[M+1] = b_sub = tat⁻¹`  (the `b ↦ tat⁻¹` image).
pub proof fn lemma_emb_b(big_m: nat, a_idx: nat, t_idx: nat)
    ensures
        miller_collapse_emb(big_m, a_idx, t_idx)[(big_m + 1) as int] == b_sub(a_idx, t_idx),
{
    let suf = seq![seq![Symbol::Gen(a_idx)], b_sub(a_idx, t_idx), seq![Symbol::Gen(t_idx)]];
    lemma_emb_split(big_m, a_idx, t_idx);
    assert(miller_collapse_emb(big_m, a_idx, t_idx)[(big_m + 1) as int] == suf[1]);
}

/// `emb_M[M+2] = [t]`  (the `t ↦ t` image).
pub proof fn lemma_emb_t(big_m: nat, a_idx: nat, t_idx: nat)
    ensures
        miller_collapse_emb(big_m, a_idx, t_idx)[(big_m + 2) as int] == seq![Symbol::Gen(t_idx)],
{
    let suf = seq![seq![Symbol::Gen(a_idx)], b_sub(a_idx, t_idx), seq![Symbol::Gen(t_idx)]];
    lemma_emb_split(big_m, a_idx, t_idx);
    assert(miller_collapse_emb(big_m, a_idx, t_idx)[(big_m + 2) as int] == suf[2]);
}

/// `inverse_word(b_sub) = binv_sub`  (so `b⁻¹ ↦ ta⁻¹t⁻¹`).
pub proof fn lemma_inverse_b_sub(a_idx: nat, t_idx: nat)
    ensures
        inverse_word(b_sub(a_idx, t_idx)) =~= binv_sub(a_idx, t_idx),
{
    reveal_with_fuel(inverse_word, 4);
}

} // verus!
