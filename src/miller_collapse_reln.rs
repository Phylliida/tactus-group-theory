use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_word_inverse_right};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat,
    lemma_apply_embedding_inverse};
use crate::hnn::{hnn_relator, stable_letter, stable_letter_inv};
use crate::cohen_layer05::{a_col, b_col, miller_data};
use crate::miller_collapse::{b_sub, miller_collapse_emb};
use crate::miller_collapse_eval::{lemma_apply_embedding_singleton, lemma_emb_a, lemma_emb_b,
    lemma_emb_t};
use crate::miller_collapse_assoc::{conj_t, lemma_deconj};

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

} // verus!
