use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_equiv_concat_right,
    lemma_word_inverse_right, lemma_word_inverse_left};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat,
    lemma_apply_embedding_inverse};
use crate::hnn::{hnn_relator, stable_letter, stable_letter_inv};
use crate::cohen_layer05::{a_col, b_col, acol_elt, bcol_elt, miller_data};
use crate::miller_collapse::{b_sub, binv_sub, miller_collapse_word, miller_collapse_emb};
use crate::miller_collapse_eval::{lemma_apply_embedding_singleton, lemma_emb_a, lemma_emb_b,
    lemma_emb_t, lemma_emb_head, lemma_emb_gen_power, lemma_word_power_singleton, lemma_inverse_b_sub};
use crate::miller_collapse_assoc::{conj_t, lemma_deconj, lemma_symbol_power_inverse_cancel};
use crate::machine_group::{symbol_power, word_power};

verus! {

// ===========================================================================
// GAP-1 §9.2-item-(2) — the WELL-DEFINEDNESS brick: the HNN association relators of the Miller slice
// push through the collapse `emb_M` to FREELY-TRIVIAL words.
//
// This is what makes `D̄_M = pushforward(decls)` (Danielle-signed, 2026-06-26): the associations add
// ZERO relators because `apply_embedding(emb_M, hnn_relator(i)) ≡ ε`.  The structure (designed this
// session): the substituted association `image(a_col[i])` is the t-CONJUGATE of `image(b_col[i])`,
// so `t⁻¹ · image(a_col) · t ≡ image(b_col)` (deconjugation), and the full relator
// `t⁻¹·image(a_col)·t·image(b_col)⁻¹ ≡ image(b_col)·image(b_col)⁻¹ ≡ ε`.
//
// Codomain-generic over a valid `p` with `a_idx, t_idx < p.num_generators` (so it instantiates at
// `free_group(2)` and at `K_M = ⟨a,t|D̄_M⟩`).
// ===========================================================================

/// The collapse image of the i-th A-column / B-column word (`IA` / `IB` in the design notes).
pub open spec fn col_img_a(n: nat, a_idx: nat, t_idx: nat, i: nat) -> Word {
    apply_embedding(miller_collapse_emb(n, a_idx, t_idx), a_col(n)[i as int])
}
pub open spec fn col_img_b(n: nat, a_idx: nat, t_idx: nat, i: nat) -> Word {
    apply_embedding(miller_collapse_emb(n, a_idx, t_idx), b_col(n)[i as int])
}

/// The stable letter of the Miller slice sits at index `n+2` (c-block 0..n, then a,b at n,n+1).
proof fn lemma_slice_stable(n: nat, decls: Seq<Word>)
    ensures
        stable_letter(miller_data(n, decls)) == Symbol::Gen((n + 2) as nat),
        stable_letter_inv(miller_data(n, decls)) == Symbol::Inv((n + 2) as nat),
        miller_data(n, decls).base.num_generators == (n + 2) as nat,
{
}

/// `apply_embedding(emb, [Gen(k)]) = emb[k]` and `apply_embedding(emb, [Inv(k)]) = inverse_word(emb[k])`,
/// specialised to the two stable-letter singletons (mapping to `[Gen(t_idx)]`, `[Inv(t_idx)]`).
proof fn lemma_emb_stable_singletons(n: nat, a_idx: nat, t_idx: nat)
    ensures
        apply_embedding(miller_collapse_emb(n, a_idx, t_idx),
            Seq::new(1, |_j: int| Symbol::Gen((n + 2) as nat))) =~= seq![Symbol::Gen(t_idx)],
        apply_embedding(miller_collapse_emb(n, a_idx, t_idx),
            Seq::new(1, |_j: int| Symbol::Inv((n + 2) as nat))) =~= seq![Symbol::Inv(t_idx)],
{
    let emb = miller_collapse_emb(n, a_idx, t_idx);
    lemma_emb_t(n, a_idx, t_idx);   // emb[n+2] == [Gen(t_idx)]

    // Gen(n+2) singleton
    assert(Seq::new(1, |_j: int| Symbol::Gen((n + 2) as nat)) =~= seq![Symbol::Gen((n + 2) as nat)]);
    lemma_apply_embedding_singleton(emb, Symbol::Gen((n + 2) as nat));
    assert(apply_embedding_symbol(emb, Symbol::Gen((n + 2) as nat)) == emb[(n + 2) as int]);

    // Inv(n+2) singleton
    assert(Seq::new(1, |_j: int| Symbol::Inv((n + 2) as nat)) =~= seq![Symbol::Inv((n + 2) as nat)]);
    lemma_apply_embedding_singleton(emb, Symbol::Inv((n + 2) as nat));
    assert(apply_embedding_symbol(emb, Symbol::Inv((n + 2) as nat))
        == inverse_word(emb[(n + 2) as int]));
    // inverse_word([Gen(t_idx)]) =~= [Inv(t_idx)]
    lemma_inverse_singleton(Symbol::Gen(t_idx));
    assert(seq![Symbol::Gen(t_idx)] =~= Seq::new(1, |_j: int| Symbol::Gen(t_idx)));
    assert(inverse_word(seq![Symbol::Gen(t_idx)]) =~= seq![Symbol::Inv(t_idx)]);
}

/// **Relator-form.**  `apply_embedding(emb, hnn_relator(slice, i)) = t⁻¹ · IA · t · IB⁻¹` (pure syntax).
pub proof fn lemma_emb_relator_form(n: nat, decls: Seq<Word>, a_idx: nat, t_idx: nat, i: nat)
    requires
        i < (n + 1) as nat,
    ensures
        apply_embedding(miller_collapse_emb(n, a_idx, t_idx),
            hnn_relator(miller_data(n, decls), i as int))
        =~= seq![Symbol::Inv(t_idx)] + col_img_a(n, a_idx, t_idx, i) + seq![Symbol::Gen(t_idx)]
            + inverse_word(col_img_b(n, a_idx, t_idx, i)),
{
    let data = miller_data(n, decls);
    let emb = miller_collapse_emb(n, a_idx, t_idx);
    lemma_slice_stable(n, decls);

    // hnn_relator(data, i) = P0 + a_i + P2 + inverse_word(b_i)
    let t_sym = Seq::new(1, |_j: int| stable_letter(data));
    let t_inv_sym = Seq::new(1, |_j: int| stable_letter_inv(data));
    let a_i = data.associations[i as int].0;
    let b_i = data.associations[i as int].1;
    assert(a_i == a_col(n)[i as int]);
    assert(b_i == b_col(n)[i as int]);

    let p0 = t_inv_sym;
    let p1 = a_i;
    let p2 = t_sym;
    let p3 = inverse_word(b_i);
    assert(hnn_relator(data, i as int) =~= ((p0 + p1) + p2) + p3);

    // distribute apply_embedding over the three concats (left-assoc)
    lemma_apply_embedding_concat(emb, (p0 + p1) + p2, p3);
    lemma_apply_embedding_concat(emb, p0 + p1, p2);
    lemma_apply_embedding_concat(emb, p0, p1);

    // evaluate the singleton / inverse pieces
    lemma_emb_stable_singletons(n, a_idx, t_idx);     // emb(p0)=[Inv t], emb(p2)=[Gen t]
    lemma_apply_embedding_inverse(emb, b_i);          // emb(p3) = inverse_word(emb(b_i)) = inverse_word(IB)
}

/// **Assembly.**  Given the association `t⁻¹·IA·t ≡ IB`, the full collapsed relator is trivial.
pub proof fn lemma_assoc_to_relator_trivial(p: Presentation, n: nat, decls: Seq<Word>,
    a_idx: nat, t_idx: nat, i: nat)
    requires
        i < (n + 1) as nat,
        equiv_in_presentation(p,
            seq![Symbol::Inv(t_idx)] + col_img_a(n, a_idx, t_idx, i) + seq![Symbol::Gen(t_idx)],
            col_img_b(n, a_idx, t_idx, i)),
    ensures
        equiv_in_presentation(p,
            apply_embedding(miller_collapse_emb(n, a_idx, t_idx),
                hnn_relator(miller_data(n, decls), i as int)),
            empty_word()),
{
    let ia = col_img_a(n, a_idx, t_idx, i);
    let ib = col_img_b(n, a_idx, t_idx, i);
    let front = seq![Symbol::Inv(t_idx)] + ia + seq![Symbol::Gen(t_idx)];   // t⁻¹·IA·t ≡ IB

    lemma_emb_relator_form(n, decls, a_idx, t_idx, i);
    // relator image =~= front + inverse_word(ib)

    // front + inverse_word(ib) ≡ ib + inverse_word(ib)
    lemma_equiv_concat_left(p, front, ib, inverse_word(ib));
    // ib + inverse_word(ib) ≡ ε
    lemma_word_inverse_right(p, ib);
    lemma_equiv_transitive(p, front + inverse_word(ib), ib + inverse_word(ib), empty_word());
}

// ---------------------------------------------------------------------------
// The association  t⁻¹·IA·t ≡ IB  per index.
// ---------------------------------------------------------------------------

/// **Base association (i = 0).**  `a_col[0] = b`, `b_col[0] = a`, so `IA = b_sub = tat⁻¹`, `IB = [a]`,
/// and `t⁻¹ · (tat⁻¹) · t ≡ a` by deconjugation.
pub proof fn lemma_assoc_i0(p: Presentation, n: nat, a_idx: nat, t_idx: nat)
    requires
        presentation_valid(p),
        a_idx < p.num_generators,
        t_idx < p.num_generators,
    ensures
        equiv_in_presentation(p,
            seq![Symbol::Inv(t_idx)] + col_img_a(n, a_idx, t_idx, 0) + seq![Symbol::Gen(t_idx)],
            col_img_b(n, a_idx, t_idx, 0)),
{
    let emb = miller_collapse_emb(n, a_idx, t_idx);
    // a_col(n)[0] = [Gen(n+1)] = b ;  b_col(n)[0] = [Gen(n)] = a
    assert(a_col(n)[0] == seq![Symbol::Gen((n + 1) as nat)]);
    assert(b_col(n)[0] == seq![Symbol::Gen(n)]);

    // IA = apply_embedding(emb, [Gen(n+1)]) = emb[n+1] = b_sub = conj_t(t, [a])
    lemma_apply_embedding_singleton(emb, Symbol::Gen((n + 1) as nat));
    lemma_emb_b(n, a_idx, t_idx);     // emb[n+1] == b_sub
    assert(col_img_a(n, a_idx, t_idx, 0) =~= b_sub(a_idx, t_idx));
    assert(b_sub(a_idx, t_idx) =~= conj_t(t_idx, seq![Symbol::Gen(a_idx)]));

    // IB = apply_embedding(emb, [Gen(n)]) = emb[n] = [Gen(a_idx)]
    lemma_apply_embedding_singleton(emb, Symbol::Gen(n));
    lemma_emb_a(n, a_idx, t_idx);     // emb[n] == [Gen(a_idx)]
    assert(col_img_b(n, a_idx, t_idx, 0) =~= seq![Symbol::Gen(a_idx)]);

    // t⁻¹ · conj_t(t, [a]) · t ≡ [a]
    lemma_deconj(p, t_idx, seq![Symbol::Gen(a_idx)]);
}

// ---------------------------------------------------------------------------
// The successor case (i = j+1):  the column images in explicit `{a,t}` form.
// ---------------------------------------------------------------------------

/// `IB = image(b⁻ⁱabⁱ) = (binv_sub)ⁱ · [a] · (b_sub)ⁱ`  (i = j+1).
pub proof fn lemma_ib_form(n: nat, a_idx: nat, t_idx: nat, j: nat)
    requires
        j < n,
    ensures
        col_img_b(n, a_idx, t_idx, (j + 1) as nat)
        =~= word_power(binv_sub(a_idx, t_idx), (j + 1) as nat)
            + seq![Symbol::Gen(a_idx)]
            + word_power(b_sub(a_idx, t_idx), (j + 1) as nat),
{
    let emb = miller_collapse_emb(n, a_idx, t_idx);
    let i = (j + 1) as nat;
    assert(b_col(n)[i as int] == bcol_elt(n, j));
    let q0 = symbol_power(Symbol::Inv((n + 1) as nat), i);
    let q1 = seq![Symbol::Gen(n)];
    let q2 = symbol_power(Symbol::Gen((n + 1) as nat), i);
    assert(bcol_elt(n, j) =~= (q0 + q1) + q2);

    lemma_apply_embedding_concat(emb, q0 + q1, q2);
    lemma_apply_embedding_concat(emb, q0, q1);

    lemma_emb_gen_power(emb, (n + 1) as nat, i);   // emb(q0)=wp(inv(emb[n+1]),i), emb(q2)=wp(emb[n+1],i)
    lemma_emb_b(n, a_idx, t_idx);                  // emb[n+1] == b_sub
    lemma_inverse_b_sub(a_idx, t_idx);             // inverse_word(b_sub) =~= binv_sub
    lemma_apply_embedding_singleton(emb, Symbol::Gen(n));
    lemma_emb_a(n, a_idx, t_idx);                  // emb[n] == [Gen(a_idx)]
}

/// `IA = image(cⱼ·a⁻ⁱ·b·aⁱ) = uⱼ · a⁻ⁱ · b_sub · aⁱ`  (i = j+1, `uⱼ = miller_collapse_word`).
pub proof fn lemma_ia_form(n: nat, a_idx: nat, t_idx: nat, j: nat)
    requires
        j < n,
    ensures
        col_img_a(n, a_idx, t_idx, (j + 1) as nat)
        =~= miller_collapse_word(j, a_idx, t_idx)
            + symbol_power(Symbol::Inv(a_idx), (j + 1) as nat)
            + b_sub(a_idx, t_idx)
            + symbol_power(Symbol::Gen(a_idx), (j + 1) as nat),
{
    let emb = miller_collapse_emb(n, a_idx, t_idx);
    let i = (j + 1) as nat;
    assert(a_col(n)[i as int] == acol_elt(n, j));
    let p0 = seq![Symbol::Gen(j)];
    let p1 = symbol_power(Symbol::Inv(n), i);
    let p2 = seq![Symbol::Gen((n + 1) as nat)];
    let p3 = symbol_power(Symbol::Gen(n), i);
    assert(acol_elt(n, j) =~= ((p0 + p1) + p2) + p3);

    lemma_apply_embedding_concat(emb, (p0 + p1) + p2, p3);
    lemma_apply_embedding_concat(emb, p0 + p1, p2);
    lemma_apply_embedding_concat(emb, p0, p1);

    // p0 → uⱼ
    lemma_apply_embedding_singleton(emb, Symbol::Gen(j));
    lemma_emb_head(n, a_idx, t_idx, j);            // emb[j] == miller_collapse_word(j,a,t)

    // p1 → a⁻ⁱ, p3 → aⁱ
    lemma_emb_gen_power(emb, n, i);                // emb(p1)=wp(inv(emb[n]),i), emb(p3)=wp(emb[n],i)
    lemma_emb_a(n, a_idx, t_idx);                  // emb[n] == [Gen(a_idx)]
    lemma_word_power_singleton(Symbol::Gen(a_idx), i);
    lemma_inverse_singleton(Symbol::Gen(a_idx));
    assert(seq![Symbol::Gen(a_idx)] =~= Seq::new(1, |_k: int| Symbol::Gen(a_idx)));
    assert(inverse_word(seq![Symbol::Gen(a_idx)]) =~= seq![Symbol::Inv(a_idx)]);
    lemma_word_power_singleton(Symbol::Inv(a_idx), i);

    // p2 → b_sub
    lemma_apply_embedding_singleton(emb, Symbol::Gen((n + 1) as nat));
    lemma_emb_b(n, a_idx, t_idx);                  // emb[n+1] == b_sub
}

/// `uⱼ`'s head is exactly `conj_t(t, IB)`:  `uⱼ = conj_t(t, IB) · a⁻ⁱ · binv_sub · aⁱ`  (i = j+1).
/// This is the engineered identity — Miller's `uⱼ` was solved-for-`cᵢ` precisely so its head is the
/// t-conjugate of the association RHS `image(b⁻ⁱabⁱ)`.
pub proof fn lemma_uj_as_conj(n: nat, a_idx: nat, t_idx: nat, j: nat)
    requires
        j < n,
    ensures
        miller_collapse_word(j, a_idx, t_idx)
        =~= conj_t(t_idx, col_img_b(n, a_idx, t_idx, (j + 1) as nat))
            + symbol_power(Symbol::Inv(a_idx), (j + 1) as nat)
            + binv_sub(a_idx, t_idx)
            + symbol_power(Symbol::Gen(a_idx), (j + 1) as nat),
{
    lemma_ib_form(n, a_idx, t_idx, j);
    // col_img_b =~= word_power(binv_sub,i) + [a] + word_power(b_sub,i), so
    // conj_t(t, col_img_b) = [t] + col_img_b + [t⁻¹] =~= [t]+wp(binv_sub,i)+[a]+wp(b_sub,i)+[t⁻¹]
    // = head of miller_collapse_word; the tail a⁻ⁱ·binv_sub·aⁱ matches definitionally.
}

/// **The tail collapses.**  `a⁻ⁱ · binv_sub · aⁱ · a⁻ⁱ · b_sub · aⁱ ≡ ε` — nested free cancellation
/// (`aⁱa⁻ⁱ`, then `binv_sub·b_sub`, then `a⁻ⁱaⁱ`).  Validity-free.
pub proof fn lemma_tail_trivial(p: Presentation, a_idx: nat, t_idx: nat, i: nat)
    ensures
        equiv_in_presentation(p,
            symbol_power(Symbol::Inv(a_idx), i) + binv_sub(a_idx, t_idx)
                + symbol_power(Symbol::Gen(a_idx), i) + symbol_power(Symbol::Inv(a_idx), i)
                + b_sub(a_idx, t_idx) + symbol_power(Symbol::Gen(a_idx), i),
            empty_word()),
{
    let am = symbol_power(Symbol::Inv(a_idx), i);   // a⁻ⁱ
    let ap = symbol_power(Symbol::Gen(a_idx), i);   // aⁱ
    let bm = binv_sub(a_idx, t_idx);                // ta⁻¹t⁻¹
    let bp = b_sub(a_idx, t_idx);                   // tat⁻¹

    // primitive cancellations
    lemma_symbol_power_inverse_cancel(p, Symbol::Gen(a_idx), i);   // aⁱ + a⁻ⁱ ≡ ε
    assert(ap + am == symbol_power(Symbol::Gen(a_idx), i)
        + symbol_power(inverse_symbol(Symbol::Gen(a_idx)), i));    // inverse_symbol(Gen)=Inv
    lemma_symbol_power_inverse_cancel(p, Symbol::Inv(a_idx), i);   // a⁻ⁱ + aⁱ ≡ ε
    assert(am + ap == symbol_power(Symbol::Inv(a_idx), i)
        + symbol_power(inverse_symbol(Symbol::Inv(a_idx)), i));    // inverse_symbol(Inv)=Gen
    lemma_inverse_b_sub(a_idx, t_idx);                             // inverse_word(bp) =~= bm
    lemma_word_inverse_left(p, bp);                               // inverse_word(bp) + bp ≡ ε
    assert(bm + bp =~= concat(inverse_word(bp), bp));            // bm + bp ≡ ε

    // M = bm + (ap + am) + bp ≡ bm + bp ≡ ε
    let m = (bm + (ap + am)) + bp;
    lemma_equiv_concat_right(p, bm, ap + am, empty_word());        // bm+(ap+am) ≡ bm+ε
    assert(bm + empty_word() =~= bm);
    lemma_equiv_concat_left(p, bm + (ap + am), bm, bp);            // (bm+(ap+am))+bp ≡ bm+bp
    lemma_equiv_transitive(p, m, bm + bp, empty_word());          // M ≡ ε

    // TAIL =~= (am + M) + ap ;  am+M ≡ am ; (am+M)+ap ≡ am+ap ≡ ε
    let tail = am + bm + ap + am + bp + ap;
    assert(tail =~= (am + m) + ap);
    lemma_equiv_concat_right(p, am, m, empty_word());             // am+M ≡ am+ε
    assert(am + empty_word() =~= am);
    lemma_equiv_concat_left(p, am + m, am, ap);                   // (am+M)+ap ≡ am+ap
    lemma_equiv_transitive(p, tail, am + ap, empty_word());       // TAIL ≡ am+ap ≡ ε
}

/// `IA ≡ conj_t(t, IB)` — the substituted `cᵢ`-association is the t-conjugate of the RHS  (i = j+1).
pub proof fn lemma_ia_conj(p: Presentation, n: nat, a_idx: nat, t_idx: nat, j: nat)
    requires
        j < n,
    ensures
        equiv_in_presentation(p, col_img_a(n, a_idx, t_idx, (j + 1) as nat),
            conj_t(t_idx, col_img_b(n, a_idx, t_idx, (j + 1) as nat))),
{
    let i = (j + 1) as nat;
    let ib = col_img_b(n, a_idx, t_idx, i);
    let cib = conj_t(t_idx, ib);
    let tail = symbol_power(Symbol::Inv(a_idx), i) + binv_sub(a_idx, t_idx)
        + symbol_power(Symbol::Gen(a_idx), i) + symbol_power(Symbol::Inv(a_idx), i)
        + b_sub(a_idx, t_idx) + symbol_power(Symbol::Gen(a_idx), i);

    lemma_ia_form(n, a_idx, t_idx, j);     // IA =~= uⱼ + a⁻ⁱ + b_sub + aⁱ
    lemma_uj_as_conj(n, a_idx, t_idx, j);  // uⱼ =~= cib + a⁻ⁱ + binv_sub + aⁱ
    // ⟹ IA =~= cib + tail
    assert(col_img_a(n, a_idx, t_idx, i) =~= cib + tail);

    lemma_tail_trivial(p, a_idx, t_idx, i);            // tail ≡ ε
    lemma_equiv_concat_right(p, cib, tail, empty_word());   // cib+tail ≡ cib+ε
    assert(cib + empty_word() =~= cib);
}

/// **Successor association (i = j+1).**  `t⁻¹ · IA · t ≡ IB`  (via `IA ≡ conj_t(t,IB)` + deconjugation).
pub proof fn lemma_assoc_succ(p: Presentation, n: nat, a_idx: nat, t_idx: nat, j: nat)
    requires
        j < n,
    ensures
        equiv_in_presentation(p,
            seq![Symbol::Inv(t_idx)] + col_img_a(n, a_idx, t_idx, (j + 1) as nat)
                + seq![Symbol::Gen(t_idx)],
            col_img_b(n, a_idx, t_idx, (j + 1) as nat)),
{
    let i = (j + 1) as nat;
    let ia = col_img_a(n, a_idx, t_idx, i);
    let ib = col_img_b(n, a_idx, t_idx, i);
    let cib = conj_t(t_idx, ib);
    let it = seq![Symbol::Inv(t_idx)];
    let gt = seq![Symbol::Gen(t_idx)];

    lemma_ia_conj(p, n, a_idx, t_idx, j);          // IA ≡ cib
    lemma_equiv_concat_right(p, it, ia, cib);      // it+IA ≡ it+cib
    lemma_equiv_concat_left(p, it + ia, it + cib, gt);  // (it+IA)+gt ≡ (it+cib)+gt
    lemma_deconj(p, t_idx, ib);                    // it+cib+gt ≡ IB
    lemma_equiv_transitive(p, it + ia + gt, it + cib + gt, ib);
}

/// **THE WELL-DEFINEDNESS BRICK.**  Every HNN association relator of the Miller slice pushes through
/// `emb_M` to a freely-trivial word — so `D̄_M` needs NO association relators (= `pushforward(decls)`).
pub proof fn lemma_collapse_hnn_relator_trivial(p: Presentation, n: nat, decls: Seq<Word>,
    a_idx: nat, t_idx: nat, i: nat)
    requires
        presentation_valid(p),
        a_idx < p.num_generators,
        t_idx < p.num_generators,
        i < (n + 1) as nat,
    ensures
        equiv_in_presentation(p,
            apply_embedding(miller_collapse_emb(n, a_idx, t_idx),
                hnn_relator(miller_data(n, decls), i as int)),
            empty_word()),
{
    if i == 0 {
        lemma_assoc_i0(p, n, a_idx, t_idx);
    } else {
        let j = (i - 1) as nat;
        assert(j < n);
        assert(i == (j + 1) as nat);
        lemma_assoc_succ(p, n, a_idx, t_idx, j);
    }
    lemma_assoc_to_relator_trivial(p, n, decls, a_idx, t_idx, i);
}

} // verus!
