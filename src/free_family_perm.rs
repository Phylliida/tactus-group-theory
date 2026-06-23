// Layer 2 — Brick 5, C3.2c / the C-arc: free-family permutation invariance.
//
// `is_free_family(gp, gens)` is invariant under reordering the generator list: if `gens` is a free
// family and `sigma` is a permutation of `0..gens.len()`, then `permute_family(gens, sigma)` (the
// list reindexed by `sigma`) is also a free family.  This is the "permute once, early" tool
// (Route A, confirmed with Danielle 2026-06-22): B3 proves `[t,x,b_j,d]` free in `h1_base`
// (`f_free_h1::lemma_f_free_in_h1`), but the C-arc crux needs the `a_words` order `[t,x,d,b_j]`
// (d at index 2). Applying this lemma once at the `pa_data` boundary aligns everything downstream.
//
// The proof routes entirely through F3 (`free_basis::lemma_free_to_embedding`) via relabeling
// embeddings — NO from-scratch free-reduction argument needed.  Key identities:
//   • `apply_embedding(permute_family(gens, sigma), w) = apply_embedding(gens, relabel(sigma, w))`
//     (compose: `permute_family(gens,sigma) = compose(gens, relabel_emb(sigma))`),
//   • `relabel(sigma_inv, relabel(sigma, w)) = w` (compose of inverse relabelings = identity),
//   • F3 turns `relabel(sigma, w) ≡_free ε` back into `w ≡_free ε` along `relabel_emb(sigma_inv)`.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::{lemma_equiv_concat_left, lemma_equiv_concat_right,
    lemma_word_inverse_left, lemma_word_inverse_right};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_valid};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::free_basis::lemma_free_to_embedding;
use crate::f_free::is_free_family;
use crate::h3_ii::{compose_embeddings, lemma_apply_embedding_compose};
use crate::machine_group::lemma_inverse_word_concat;

verus! {

/// The relabeling embedding: generator `i ↦ Gen(sigma[i])`.  As an `apply_embedding` image list,
/// applying it to a word `w` relabels each symbol `Gen(i)/Inv(i) ↦ Gen(sigma[i])/Inv(sigma[i])`.
pub open spec fn relabel_emb(sigma: Seq<nat>) -> Seq<Word> {
    Seq::new(sigma.len(), |i: int| seq![Symbol::Gen(sigma[i])])
}

/// The generator list `gens` reindexed by `sigma`: `permute_family(gens, sigma)[i] = gens[sigma[i]]`.
pub open spec fn permute_family(gens: Seq<Word>, sigma: Seq<nat>) -> Seq<Word> {
    Seq::new(sigma.len(), |i: int| gens[sigma[i] as int])
}

/// **The identity embedding acts trivially**: `apply_embedding([Gen(0),…,Gen(k-1)], w) =~= w`
/// for any `w` valid over `k` generators.  (Induction on `w`.)
proof fn lemma_apply_id_emb(k: nat, w: Word)
    requires
        word_valid(w, k),
    ensures
        apply_embedding(Seq::new(k as int as nat, |i: int| seq![Symbol::Gen(i as nat)]), w) =~= w,
    decreases w.len(),
{
    let id_emb = Seq::new(k, |i: int| seq![Symbol::Gen(i as nat)]);
    if w.len() == 0 {
        assert(apply_embedding(id_emb, w) =~= empty_word());
    } else {
        let sym = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(sym, k)) by { assert(sym == w[0]); }
        assert(word_valid(rest, k)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], k) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_apply_id_emb(k, rest);                                   // IH: apply_embedding(id, rest) =~= rest
        // per-symbol: apply_embedding_symbol(id, sym) =~= [sym]
        match sym {
            Symbol::Gen(i) => {
                assert(i < k);
                assert(apply_embedding_symbol(id_emb, sym) == id_emb[i as int]);
                assert(id_emb[i as int] =~= seq![sym]);
            },
            Symbol::Inv(i) => {
                assert(i < k);
                assert(apply_embedding_symbol(id_emb, sym) =~= inverse_word(id_emb[i as int]));
                reveal_with_fuel(inverse_word, 2);
                assert(inverse_word(id_emb[i as int]) =~= seq![sym]);
            },
        }
        assert(apply_embedding(id_emb, w)
            =~= concat(apply_embedding_symbol(id_emb, sym), apply_embedding(id_emb, rest)));
        assert(w =~= seq![sym] + rest);
    }
}

/// **`permute_family` factors as a relabel then the original embedding**:
/// `apply_embedding(permute_family(gens, sigma), w) =~= apply_embedding(gens, apply_embedding(relabel_emb(sigma), w))`.
proof fn lemma_permute_factors(gens: Seq<Word>, sigma: Seq<nat>, w: Word)
    requires
        word_valid(w, sigma.len()),
    ensures
        apply_embedding(permute_family(gens, sigma), w)
            =~= apply_embedding(gens, apply_embedding(relabel_emb(sigma), w)),
{
    let rl = relabel_emb(sigma);
    let pf = permute_family(gens, sigma);
    assert(rl.len() == sigma.len());
    assert(word_valid(w, rl.len()));
    // apply_embedding(gens, apply_embedding(rl, w)) =~= apply_embedding(compose(gens, rl), w)
    lemma_apply_embedding_compose(gens, rl, w);
    // compose(gens, rl) =~= permute_family(gens, sigma)
    assert(compose_embeddings(gens, rl) =~= pf) by {
        assert forall|i: int| #![auto] 0 <= i < sigma.len()
            implies compose_embeddings(gens, rl)[i] =~= pf[i] by {
            assert(compose_embeddings(gens, rl)[i] == apply_embedding(gens, rl[i]));
            assert(rl[i] == seq![Symbol::Gen(sigma[i])]);
            reveal_with_fuel(apply_embedding, 2);
            lemma_concat_empty_right(gens[sigma[i] as int]);
            assert(apply_embedding(gens, seq![Symbol::Gen(sigma[i])]) =~= gens[sigma[i] as int]);
            assert(pf[i] == gens[sigma[i] as int]);
        }
    }
}

/// **Inverse relabelings compose to the identity**: when `sigma_inv ∘ sigma = id` on `0..k`,
/// `relabel(sigma_inv, relabel(sigma, w)) =~= w`.
proof fn lemma_relabel_inverse(k: nat, sigma: Seq<nat>, sigma_inv: Seq<nat>, w: Word)
    requires
        sigma.len() == k,
        sigma_inv.len() == k,
        forall|i: int| 0 <= i < k ==> #[trigger] sigma[i] < k,
        forall|i: int| 0 <= i < k ==> #[trigger] sigma_inv[i] < k,
        forall|i: int| 0 <= i < k ==> sigma_inv[#[trigger] sigma[i] as int] == i,
        word_valid(w, k),
    ensures
        apply_embedding(relabel_emb(sigma_inv), apply_embedding(relabel_emb(sigma), w)) =~= w,
{
    let rs = relabel_emb(sigma);
    let ri = relabel_emb(sigma_inv);
    assert(rs.len() == k && ri.len() == k);
    assert(word_valid(w, rs.len()));
    // ri(rs(w)) =~= compose(ri, rs)(w)
    lemma_apply_embedding_compose(ri, rs, w);
    let id_emb = Seq::new(k as int as nat, |i: int| seq![Symbol::Gen(i as nat)]);
    // compose(ri, rs) =~= id_emb
    assert(compose_embeddings(ri, rs) =~= id_emb) by {
        assert forall|i: int| #![auto] 0 <= i < k implies compose_embeddings(ri, rs)[i] =~= id_emb[i] by {
            assert(compose_embeddings(ri, rs)[i] == apply_embedding(ri, rs[i]));
            assert(rs[i] == seq![Symbol::Gen(sigma[i])]);
            reveal_with_fuel(apply_embedding, 2);
            lemma_concat_empty_right(ri[sigma[i] as int]);
            assert(apply_embedding(ri, seq![Symbol::Gen(sigma[i])]) =~= ri[sigma[i] as int]);
            assert(ri[sigma[i] as int] == seq![Symbol::Gen(sigma_inv[sigma[i] as int])]);
            assert(sigma_inv[sigma[i] as int] == i);
            assert(id_emb[i] == seq![Symbol::Gen(i as nat)]);
        }
    }
    // apply_embedding(compose(ri,rs), w) == apply_embedding(id_emb, w) =~= w
    lemma_apply_id_emb(k, w);
}

/// **Free families are invariant under generator reordering.**  If `gens` is a free family in `gp`
/// and `sigma` permutes `0..gens.len()` (witnessed by a left inverse `sigma_inv`), then
/// `permute_family(gens, sigma)` is a free family.  Route A's "permute once" tool — applied at the
/// `pa_data` boundary to turn B3's `[t,x,b_j,d]` freeness into the `a_words` order `[t,x,d,b_j]`.
pub proof fn lemma_free_family_permute(
    gp: Presentation, gens: Seq<Word>, sigma: Seq<nat>, sigma_inv: Seq<nat>,
)
    requires
        is_free_family(gp, gens),
        sigma.len() == gens.len(),
        sigma_inv.len() == gens.len(),
        forall|i: int| 0 <= i < gens.len() ==> #[trigger] sigma[i] < gens.len(),
        forall|i: int| 0 <= i < gens.len() ==> #[trigger] sigma_inv[i] < gens.len(),
        forall|i: int| 0 <= i < gens.len() ==> sigma_inv[#[trigger] sigma[i] as int] == i,
    ensures
        is_free_family(gp, permute_family(gens, sigma)),
{
    let k = gens.len();
    let pf = permute_family(gens, sigma);
    assert(pf.len() == k);
    // First conjunct: each pf[i] = gens[sigma[i]] is valid over gp's generators.
    assert forall|i: int| 0 <= i < pf.len() implies word_valid(#[trigger] pf[i], gp.num_generators) by {
        assert(pf[i] == gens[sigma[i] as int]);
        assert(sigma[i] < k);
    }
    // Second conjunct: a relation of pf descends to a free-group triviality of w.
    assert forall|w: Word| (#[trigger] word_valid(w, pf.len())
        && equiv_in_presentation(gp, apply_embedding(pf, w), empty_word()))
        implies equiv_in_presentation(free_group(pf.len()), w, empty_word()) by {
        // relabel w by sigma: w_rel valid over k.
        let w_rel = apply_embedding(relabel_emb(sigma), w);
        assert forall|i: int| 0 <= i < relabel_emb(sigma).len()
            implies word_valid(#[trigger] relabel_emb(sigma)[i], k) by {
            assert(relabel_emb(sigma)[i] == seq![Symbol::Gen(sigma[i])]);
            assert(sigma[i] < k);
        }
        lemma_apply_embedding_valid(relabel_emb(sigma), w, k);
        assert(word_valid(w_rel, k));
        // apply_embedding(pf, w) =~= apply_embedding(gens, w_rel)
        lemma_permute_factors(gens, sigma, w);
        // is_free_family(gp, gens): apply_embedding(gens, w_rel) ≡ ε ⟹ w_rel ≡_free ε
        assert(word_valid(w_rel, gens.len()));
        assert(equiv_in_presentation(gp, apply_embedding(gens, w_rel), empty_word()));
        assert(equiv_in_presentation(free_group(k), w_rel, empty_word()));   // from is_free_family(gp,gens)
        // F3 along relabel_emb(sigma_inv): w_rel ≡_free ε ⟹ relabel(sigma_inv, w_rel) ≡_free ε,
        // and relabel(sigma_inv, w_rel) =~= w.
        lemma_free_group_valid(k);
        assert forall|i: int| 0 <= i < relabel_emb(sigma_inv).len()
            implies word_valid(#[trigger] relabel_emb(sigma_inv)[i], free_group(k).num_generators) by {
            assert(relabel_emb(sigma_inv)[i] == seq![Symbol::Gen(sigma_inv[i])]);
            assert(sigma_inv[i] < k);
        }
        lemma_free_to_embedding(relabel_emb(sigma_inv), free_group(k), w_rel);
        lemma_relabel_inverse(k, sigma, sigma_inv, w);
        assert(apply_embedding(relabel_emb(sigma_inv), w_rel) =~= w);
        assert(pf.len() == k);
    }
}

// ----------------------------------------------------------------------------
// Free families are invariant under uniform conjugation by a fixed word `c`.
// (Used by map_b forward rung (i): [config(l,0), xᵐ] = conj of psi_F_images(m) by x⁻ˡ.)
// ----------------------------------------------------------------------------

/// The family `gens` with every generator conjugated by a fixed word `c`:
/// `conjugate_family(gens, c)[i] = (c · gens[i]) · c⁻¹`.
pub open spec fn conjugate_family(gens: Seq<Word>, c: Word) -> Seq<Word> {
    Seq::new(gens.len(), |i: int| (c + gens[i]) + inverse_word(c))
}

/// **Splice cancellation**: `(A·c⁻¹)·((c·B)·c⁻¹) ≡ (A·B)·c⁻¹` (the inner `c⁻¹·c` cancels).
proof fn lemma_conj_splice(gp: Presentation, a: Word, b: Word, c: Word)
    requires
        presentation_valid(gp),
        word_valid(a, gp.num_generators),
        word_valid(b, gp.num_generators),
        word_valid(c, gp.num_generators),
    ensures
        equiv_in_presentation(gp,
            (a + inverse_word(c)) + ((c + b) + inverse_word(c)),
            (a + b) + inverse_word(c)),
{
    let ng = gp.num_generators;
    let ci = inverse_word(c);
    lemma_inverse_word_valid(c, ng);
    lemma_concat_word_valid(ci, c, ng);
    lemma_concat_word_valid(b, ci, ng);
    lemma_concat_word_valid(a, b, ng);
    lemma_concat_word_valid(a + b, ci, ng);
    lemma_concat_word_valid(ci, c + b, ng);
    lemma_concat_word_valid(c, b, ng);
    // ci·c ≡ ε.
    lemma_word_inverse_left(gp, c);                          // ci + c ≡ ε
    // ((ci+c) + (b+ci)) ≡ (ε + (b+ci)) = b+ci.
    lemma_concat_word_valid(ci + c, b + ci, ng);
    lemma_equiv_concat_left(gp, ci + c, empty_word(), b + ci);
    assert(concat(ci + c, b + ci) == (ci + c) + (b + ci));
    assert(concat(empty_word(), b + ci) =~= b + ci);
    assert(equiv_in_presentation(gp, (ci + c) + (b + ci), b + ci));
    // a + ((ci+c)+(b+ci)) ≡ a + (b+ci).
    lemma_equiv_concat_right(gp, a, (ci + c) + (b + ci), b + ci);
    assert(concat(a, (ci + c) + (b + ci)) == a + ((ci + c) + (b + ci)));
    assert(concat(a, b + ci) == a + (b + ci));
    // the two flat sides are extensionally equal to the regroupings.
    assert((a + ci) + ((c + b) + ci) =~= a + ((ci + c) + (b + ci)));
    assert(a + (b + ci) =~= (a + b) + ci);
}

/// **Conjugating each image by `c` preserves `apply_embedding_symbol`**:
/// `apply_embedding_symbol(conjugate_family(gens,c), sym) =~= (c · apply_embedding_symbol(gens,sym)) · c⁻¹`.
proof fn lemma_conj_emb_symbol(gens: Seq<Word>, c: Word, sym: Symbol)
    requires
        symbol_valid(sym, gens.len()),
    ensures
        apply_embedding_symbol(conjugate_family(gens, c), sym)
            =~= (c + apply_embedding_symbol(gens, sym)) + inverse_word(c),
{
    let cf = conjugate_family(gens, c);
    let ci = inverse_word(c);
    match sym {
        Symbol::Gen(i) => {
            assert(i < gens.len());
            assert(apply_embedding_symbol(cf, sym) == cf[i as int]);
            assert(cf[i as int] == (c + gens[i as int]) + ci);
            assert(apply_embedding_symbol(gens, sym) == gens[i as int]);
        },
        Symbol::Inv(i) => {
            assert(i < gens.len());
            assert(apply_embedding_symbol(cf, sym) =~= inverse_word(cf[i as int]));
            assert(cf[i as int] == (c + gens[i as int]) + ci);
            // inverse_word((c+gens[i]) + ci) = inverse_word(ci) + inverse_word(c+gens[i])
            //                                = c + (inverse_word(gens[i]) + inverse_word(c)).
            lemma_inverse_word_concat(c + gens[i as int], ci);
            crate::word::lemma_inverse_involution(c);
            lemma_inverse_word_concat(c, gens[i as int]);
            assert(inverse_word(cf[i as int])
                =~= c + (inverse_word(gens[i as int]) + ci));
            assert(apply_embedding_symbol(gens, sym) =~= inverse_word(gens[i as int]));
            assert((c + inverse_word(gens[i as int])) + ci =~= c + (inverse_word(gens[i as int]) + ci));
        },
    }
}

/// **Conjugation telescopes through `apply_embedding`**: `emb(conjugate_family(gens,c), w) ≡_{gp}
/// (c · emb(gens, w)) · c⁻¹`.  Induction on `w`, splicing out the inner `c⁻¹·c` at each step.
proof fn lemma_conjugate_emb_telescopes(gp: Presentation, gens: Seq<Word>, c: Word, w: Word)
    requires
        presentation_valid(gp),
        word_valid(c, gp.num_generators),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], gp.num_generators),
        word_valid(w, gens.len()),
    ensures
        equiv_in_presentation(gp, apply_embedding(conjugate_family(gens, c), w),
            (c + apply_embedding(gens, w)) + inverse_word(c)),
    decreases w.len(),
{
    let ng = gp.num_generators;
    let cf = conjugate_family(gens, c);
    let ci = inverse_word(c);
    lemma_inverse_word_valid(c, ng);
    // cf entries valid over ng.
    assert forall|i: int| 0 <= i < cf.len() implies word_valid(#[trigger] cf[i], ng) by {
        assert(cf[i] == (c + gens[i]) + ci);
        lemma_concat_word_valid(c, gens[i], ng);
        lemma_concat_word_valid(c + gens[i], ci, ng);
    }
    if w.len() == 0 {
        // emb(cf, []) = ε;  (c + ε) + ci = c + ci ≡ ε.
        assert(apply_embedding(cf, w) =~= empty_word());
        assert(apply_embedding(gens, w) =~= empty_word());
        lemma_word_inverse_right(gp, c);                    // c + ci ≡ ε
        lemma_equiv_symmetric(gp, c + ci, empty_word());
        assert((c + apply_embedding(gens, w)) + ci =~= c + ci);
    } else {
        let sym = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(sym, gens.len())) by { assert(sym == w[0]); }
        assert(word_valid(rest, gens.len())) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], gens.len())
            by { assert(rest[i] == w[i + 1]); }
        }
        // emb(cf, w) = emb_symbol(cf, sym) + emb(cf, rest).
        let es_cf = apply_embedding_symbol(cf, sym);
        let es_g = apply_embedding_symbol(gens, sym);
        assert(apply_embedding(cf, w) =~= es_cf + apply_embedding(cf, rest));
        // es_cf =~= (c + es_g) + ci.
        lemma_conj_emb_symbol(gens, c, sym);
        // es_g, emb(gens, rest) valid.
        assert(es_g == apply_embedding_symbol(gens, sym));
        assert(word_valid(es_g, ng)) by {
            match sym {
                Symbol::Gen(i) => { assert(es_g == gens[i as int]); },
                Symbol::Inv(i) => {
                    assert(es_g =~= inverse_word(gens[i as int]));
                    lemma_inverse_word_valid(gens[i as int], ng);
                },
            }
        }
        lemma_apply_embedding_valid(gens, rest, ng);
        let b = apply_embedding(gens, rest);
        // IH: emb(cf, rest) ≡ (c + b) + ci.
        lemma_conjugate_emb_telescopes(gp, gens, c, rest);
        // emb(cf, w) ≡ es_cf + ((c+b)+ci)   [equiv_concat_right with IH].
        lemma_apply_embedding_valid(cf, rest, ng);
        lemma_concat_word_valid(c, b, ng);
        lemma_concat_word_valid(c + b, ci, ng);
        lemma_equiv_concat_right(gp, es_cf, apply_embedding(cf, rest), (c + b) + ci);
        assert(concat(es_cf, apply_embedding(cf, rest)) == es_cf + apply_embedding(cf, rest));
        assert(concat(es_cf, (c + b) + ci) == es_cf + ((c + b) + ci));
        // es_cf =~= (c + es_g) + ci = A + ci with A = c + es_g.
        assert(es_cf =~= (c + es_g) + ci);
        assert(es_cf + ((c + b) + ci) =~= ((c + es_g) + ci) + ((c + b) + ci));
        // splice: ((c+es_g)+ci) + ((c+b)+ci) ≡ ((c+es_g)+b)+ci.
        lemma_concat_word_valid(c, es_g, ng);
        lemma_conj_splice(gp, c + es_g, b, c);
        // chain: emb(cf,w) ≡ es_cf+((c+b)+ci) ≡ ((c+es_g)+b)+ci.
        lemma_equiv_transitive(gp, apply_embedding(cf, w), es_cf + ((c + b) + ci),
            ((c + es_g) + b) + ci);
        // ((c+es_g)+b)+ci = (c + (es_g+b)) + ci = (c + emb(gens,w)) + ci.
        assert(apply_embedding(gens, w) =~= es_g + b);
        assert(((c + es_g) + b) + ci =~= (c + apply_embedding(gens, w)) + ci);
    }
}

/// **Uniform conjugation preserves freeness.**  If `gens` is a free family in `gp` and `c` is a
/// `gp`-word, then `conjugate_family(gens, c)` (each generator conjugated by `c`) is also a free
/// family.  (Telescoping: a relation `emb(conj, w) ≡ ε` gives `c·emb(gens,w)·c⁻¹ ≡ ε`, so
/// `emb(gens, w) ≡ ε`, so `w ≡_free ε`.)  Rung (i) of map_b forward's φ_F-injectivity:
/// `[config(l,0), xᵐ] = conjugate_family(psi_F_images(m), x⁻ˡ)`.
pub proof fn lemma_free_family_conjugate(gp: Presentation, gens: Seq<Word>, c: Word)
    requires
        presentation_valid(gp),
        is_free_family(gp, gens),
        word_valid(c, gp.num_generators),
    ensures
        is_free_family(gp, conjugate_family(gens, c)),
{
    let ng = gp.num_generators;
    let k = gens.len();
    let cf = conjugate_family(gens, c);
    let ci = inverse_word(c);
    lemma_inverse_word_valid(c, ng);
    assert(cf.len() == k);
    // gens valid (first conjunct of is_free_family).
    assert forall|i: int| 0 <= i < k implies word_valid(#[trigger] gens[i], ng) by {}
    // cf entries valid.
    assert forall|i: int| 0 <= i < cf.len() implies word_valid(#[trigger] cf[i], ng) by {
        assert(cf[i] == (c + gens[i]) + ci);
        lemma_concat_word_valid(c, gens[i], ng);
        lemma_concat_word_valid(c + gens[i], ci, ng);
    }
    // freeness: a relation of cf descends to w ≡_free ε.
    assert forall|w: Word| (#[trigger] word_valid(w, cf.len())
        && equiv_in_presentation(gp, apply_embedding(cf, w), empty_word()))
        implies equiv_in_presentation(free_group(cf.len()), w, empty_word()) by {
        assert(word_valid(w, k));
        // cf entries valid (re-establish inside this assert-forall context).
        assert forall|i: int| 0 <= i < cf.len() implies word_valid(#[trigger] cf[i], ng) by {
            assert(cf[i] == (c + gens[i]) + ci);
            lemma_concat_word_valid(c, gens[i], ng);
            lemma_concat_word_valid(c + gens[i], ci, ng);
        }
        lemma_apply_embedding_valid(cf, w, ng);             // emb(cf, w) valid over ng
        // telescoping: emb(cf, w) ≡ (c + emb(gens,w)) + ci.
        lemma_conjugate_emb_telescopes(gp, gens, c, w);
        let g = apply_embedding(gens, w);
        lemma_apply_embedding_valid(gens, w, ng);
        lemma_concat_word_valid(c, g, ng);
        lemma_concat_word_valid(c + g, ci, ng);
        // (c+g)+ci ≡ ε  [transitivity with the hypothesis emb(cf,w) ≡ ε].
        lemma_equiv_symmetric(gp, apply_embedding(cf, w), (c + g) + ci);
        lemma_equiv_transitive(gp, (c + g) + ci, apply_embedding(cf, w), empty_word());
        // c·g·c⁻¹ ≡ ε  ⟹  g ≡ ε   (left-mult ci, right-mult c, cancel).
        lemma_conj_cancel(gp, g, c);
        assert(equiv_in_presentation(gp, g, empty_word()));
        // is_free_family(gp, gens): g = emb(gens, w) ≡ ε ⟹ w ≡_free ε.
        assert(equiv_in_presentation(free_group(k), w, empty_word()));
        assert(cf.len() == k);
    }
}

/// **Conjugation cancellation**: `(c·g)·c⁻¹ ≡ ε ⟹ g ≡ ε`.  (`g ≡ c⁻¹·((c·g)·c⁻¹)·c ≡ c⁻¹·ε·c ≡ ε`.)
proof fn lemma_conj_cancel(gp: Presentation, g: Word, c: Word)
    requires
        presentation_valid(gp),
        word_valid(g, gp.num_generators),
        word_valid(c, gp.num_generators),
        equiv_in_presentation(gp, (c + g) + inverse_word(c), empty_word()),
    ensures
        equiv_in_presentation(gp, g, empty_word()),
{
    let ng = gp.num_generators;
    let ci = inverse_word(c);
    let x = (c + g) + ci;                                    // the hypothesis word, ≡ ε
    lemma_inverse_word_valid(c, ng);
    lemma_concat_word_valid(c, g, ng);
    lemma_concat_word_valid(c + g, ci, ng);                  // x valid
    lemma_concat_word_valid(ci, x, ng);
    lemma_concat_word_valid(ci + x, c, ng);                  // (ci+x)+c valid
    lemma_concat_word_valid(ci, c, ng);                      // ci+c valid
    lemma_concat_word_valid(ci + c, g, ng);
    lemma_concat_word_valid(g, ci + c, ng);
    lemma_word_inverse_left(gp, c);                          // ci + c ≡ ε

    // --- Fact A:  g ≡ (ci+x)+c ---
    // (ci+x)+c =~= ((ci+c)+g)+(ci+c)   (both flatten to ci,c,g,ci,c)
    assert((ci + x) + c =~= ((ci + c) + g) + (ci + c));
    // (ci+c)+g ≡ ε+g =~= g
    lemma_equiv_concat_left(gp, ci + c, empty_word(), g);
    assert(concat(ci + c, g) == (ci + c) + g);
    assert(concat(empty_word(), g) =~= g);
    // ((ci+c)+g)+(ci+c) ≡ g+(ci+c)
    lemma_equiv_concat_left(gp, (ci + c) + g, g, ci + c);
    assert(concat((ci + c) + g, ci + c) == ((ci + c) + g) + (ci + c));
    assert(concat(g, ci + c) == g + (ci + c));
    // g+(ci+c) ≡ g+ε =~= g
    lemma_equiv_concat_right(gp, g, ci + c, empty_word());
    assert(concat(g, empty_word()) =~= g);
    // chain: ((ci+c)+g)+(ci+c) ≡ g+(ci+c) ≡ g
    lemma_equiv_transitive(gp, ((ci + c) + g) + (ci + c), g + (ci + c), g);
    // so (ci+x)+c ≡ g  ⟹ g ≡ (ci+x)+c
    assert(equiv_in_presentation(gp, (ci + x) + c, g));
    lemma_equiv_symmetric(gp, (ci + x) + c, g);

    // --- Fact B:  (ci+x)+c ≡ ε ---
    // ci+x ≡ ci+ε =~= ci   (x ≡ ε)
    lemma_equiv_concat_right(gp, ci, x, empty_word());
    assert(concat(ci, x) == ci + x);
    assert(concat(ci, empty_word()) =~= ci);
    // (ci+x)+c ≡ ci+c
    lemma_equiv_concat_left(gp, ci + x, ci, c);
    assert(concat(ci + x, c) == (ci + x) + c);
    assert(concat(ci, c) == ci + c);
    // ci+c ≡ ε  ⟹ (ci+x)+c ≡ ε
    lemma_equiv_transitive(gp, (ci + x) + c, ci + c, empty_word());

    // --- chain Fact A + Fact B:  g ≡ (ci+x)+c ≡ ε ---
    lemma_equiv_transitive(gp, g, (ci + x) + c, empty_word());
}

// ----------------------------------------------------------------------------
// Free families respect per-generator equivalence.
// (Used by map_b forward rung (i): the conjugate of psi_F_images(m) is per-gen ≡ [config(l,0), xᵐ].)
// ----------------------------------------------------------------------------

/// **`apply_embedding` respects per-generator equivalence**: if `gens2[i] ≡_{gp} gens[i]` for each
/// `i`, then `emb(gens2, w) ≡_{gp} emb(gens, w)`.  Induction on `w` (per-symbol uses the gen equiv,
/// `lemma_equiv_inverse` for `Inv`).
pub proof fn lemma_emb_respects_gen_equiv(
    gp: Presentation, gens: Seq<Word>, gens2: Seq<Word>, w: Word)
    requires
        presentation_valid(gp),
        gens.len() == gens2.len(),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], gp.num_generators),
        forall|i: int| 0 <= i < gens2.len() ==> word_valid(#[trigger] gens2[i], gp.num_generators),
        forall|i: int| 0 <= i < gens.len() ==>
            equiv_in_presentation(gp, #[trigger] gens2[i], gens[i]),
        word_valid(w, gens.len()),
    ensures
        equiv_in_presentation(gp, apply_embedding(gens2, w), apply_embedding(gens, w)),
    decreases w.len(),
{
    let ng = gp.num_generators;
    if w.len() == 0 {
        assert(apply_embedding(gens2, w) =~= empty_word());
        assert(apply_embedding(gens, w) =~= empty_word());
        lemma_equiv_refl(gp, empty_word());
    } else {
        let sym = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(sym, gens.len())) by { assert(sym == w[0]); }
        assert(word_valid(rest, gens.len())) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(#[trigger] rest[i], gens.len())
            by { assert(rest[i] == w[i + 1]); }
        }
        let es2 = apply_embedding_symbol(gens2, sym);
        let es = apply_embedding_symbol(gens, sym);
        assert(apply_embedding(gens2, w) =~= es2 + apply_embedding(gens2, rest));
        assert(apply_embedding(gens, w) =~= es + apply_embedding(gens, rest));
        // es2 ≡ es, and validities.
        assert(word_valid(es2, ng) && word_valid(es, ng)) by {
            match sym {
                Symbol::Gen(i) => { assert(es2 == gens2[i as int] && es == gens[i as int]); },
                Symbol::Inv(i) => {
                    assert(es2 =~= inverse_word(gens2[i as int]) && es =~= inverse_word(gens[i as int]));
                    lemma_inverse_word_valid(gens2[i as int], ng);
                    lemma_inverse_word_valid(gens[i as int], ng);
                },
            }
        }
        assert(equiv_in_presentation(gp, es2, es)) by {
            match sym {
                Symbol::Gen(i) => {
                    assert(es2 == gens2[i as int] && es == gens[i as int]);
                    assert(equiv_in_presentation(gp, gens2[i as int], gens[i as int]));
                },
                Symbol::Inv(i) => {
                    assert(es2 =~= inverse_word(gens2[i as int]) && es =~= inverse_word(gens[i as int]));
                    crate::higman_consequences::lemma_equiv_inverse(gp, gens2[i as int], gens[i as int]);
                },
            }
        }
        // IH + concat congruence.
        lemma_emb_respects_gen_equiv(gp, gens, gens2, rest);
        lemma_apply_embedding_valid(gens2, rest, ng);
        lemma_apply_embedding_valid(gens, rest, ng);
        lemma_equiv_concat_left(gp, es2, es, apply_embedding(gens2, rest));
        assert(concat(es2, apply_embedding(gens2, rest)) == es2 + apply_embedding(gens2, rest));
        assert(concat(es, apply_embedding(gens2, rest)) == es + apply_embedding(gens2, rest));
        lemma_equiv_concat_right(gp, es, apply_embedding(gens2, rest), apply_embedding(gens, rest));
        assert(concat(es, apply_embedding(gens, rest)) == es + apply_embedding(gens, rest));
        lemma_equiv_transitive(gp, es2 + apply_embedding(gens2, rest),
            es + apply_embedding(gens2, rest), es + apply_embedding(gens, rest));
    }
}

/// **Free families respect per-generator equivalence**: if `gens` is free and `gens2[i] ≡_{gp}
/// gens[i]` for each `i`, then `gens2` is free.  (A relation `emb(gens2,w)≡ε` transfers to
/// `emb(gens,w)≡ε` via `lemma_emb_respects_gen_equiv`, then `gens` freeness closes it.)
pub proof fn lemma_free_family_respects_equiv(gp: Presentation, gens: Seq<Word>, gens2: Seq<Word>)
    requires
        presentation_valid(gp),
        is_free_family(gp, gens),
        gens2.len() == gens.len(),
        forall|i: int| 0 <= i < gens2.len() ==> word_valid(#[trigger] gens2[i], gp.num_generators),
        forall|i: int| 0 <= i < gens.len() ==>
            equiv_in_presentation(gp, #[trigger] gens2[i], gens[i]),
    ensures
        is_free_family(gp, gens2),
{
    let ng = gp.num_generators;
    let k = gens.len();
    // gens valid (first conjunct of is_free_family).
    assert forall|i: int| 0 <= i < k implies word_valid(#[trigger] gens[i], ng) by {}
    assert forall|w: Word| (#[trigger] word_valid(w, gens2.len())
        && equiv_in_presentation(gp, apply_embedding(gens2, w), empty_word()))
        implies equiv_in_presentation(free_group(gens2.len()), w, empty_word()) by {
        assert(word_valid(w, k));
        // emb(gens2,w) ≡ emb(gens,w);  emb(gens2,w) ≡ ε ⟹ emb(gens,w) ≡ ε.
        lemma_emb_respects_gen_equiv(gp, gens, gens2, w);
        lemma_apply_embedding_valid(gens2, w, ng);
        lemma_apply_embedding_valid(gens, w, ng);
        lemma_equiv_symmetric(gp, apply_embedding(gens2, w), apply_embedding(gens, w));
        lemma_equiv_transitive(gp, apply_embedding(gens, w), apply_embedding(gens2, w), empty_word());
        // gens free ⟹ w ≡_free ε.
        assert(equiv_in_presentation(free_group(k), w, empty_word()));
        assert(gens2.len() == k);
    }
}

// ----------------------------------------------------------------------------
// Nielsen transvection: replacing one generator by `s·g_i` (left-multiply by a letter `s`)
// preserves freeness.  (Used by map_b forward rung (iv): d ↦ b_l·d in [config(l,0),xᵐ,d,b_j].)
// ----------------------------------------------------------------------------

/// The transvection embedding: `gen i ↦ [s, Gen(i)]` (left-multiply by the letter `s`), every other
/// `gen g ↦ [Gen(g)]`.  Composing `gens` with it left-multiplies `gens[i]` by `apply_embedding_symbol(gens, s)`.
pub open spec fn transvect_emb(k: nat, i: int, s: Symbol) -> Seq<Word> {
    Seq::new(k, |g: int| if g == i { seq![s, Symbol::Gen(g as nat)] } else { seq![Symbol::Gen(g as nat)] })
}

/// `apply_embedding_symbol(transvect_emb(k,i,inverse_symbol(s)), s) =~= [s]` when `generator_index(s)
/// = j ≠ i` (the off-`i` entries are identity singletons, so the letter `s` maps to itself).
proof fn lemma_transvect_inv_on_s(k: nat, i: int, s: Symbol)
    requires
        symbol_valid(s, k),
        generator_index(s) != i,
    ensures
        apply_embedding_symbol(transvect_emb(k, i, inverse_symbol(s)), s) =~= seq![s],
{
    let ti = transvect_emb(k, i, inverse_symbol(s));
    let j = generator_index(s);
    assert(j < k);
    assert(ti[j as int] == seq![Symbol::Gen(j)]) by { assert(j != i); }
    match s {
        Symbol::Gen(g) => {
            assert(g == j);
            assert(apply_embedding_symbol(ti, s) == ti[j as int]);
        },
        Symbol::Inv(g) => {
            assert(g == j);
            assert(apply_embedding_symbol(ti, s) =~= inverse_word(ti[j as int]));
            reveal_with_fuel(inverse_word, 2);
        },
    }
}

/// **`compose(τ⁻¹, τ)` is per-generator free-equivalent to the identity embedding.**  At `i`:
/// `[s, s⁻¹, Gen(i)] ≡_free [Gen(i)]` (the `s·s⁻¹` cancels); elsewhere: `[Gen(g)]` unchanged.
proof fn lemma_transvect_compose_inv(k: nat, i: int, s: Symbol, g: int)
    requires
        symbol_valid(s, k),
        generator_index(s) != i,
        0 <= i < k,
        0 <= g < k,
    ensures
        equiv_in_presentation(free_group(k),
            compose_embeddings(transvect_emb(k, i, inverse_symbol(s)), transvect_emb(k, i, s))[g],
            seq![Symbol::Gen(g as nat)]),
{
    let fg = free_group(k);
    lemma_free_group_valid(k);
    let t = transvect_emb(k, i, s);
    let ti = transvect_emb(k, i, inverse_symbol(s));
    let comp = compose_embeddings(ti, t);
    assert(comp[g] == apply_embedding(ti, t[g]));
    if g == i {
        // t[i] = [s, Gen(i)]; emb(ti, [s,Gen(i)]) = aes(ti,s) + ti[i] = [s] + [s⁻¹, Gen(i)].
        assert(t[i] == seq![s, Symbol::Gen(i as nat)]);
        reveal_with_fuel(apply_embedding, 3);
        lemma_transvect_inv_on_s(k, i, s);                       // aes(ti, s) =~= [s]
        assert(ti[i as int] == seq![inverse_symbol(s), Symbol::Gen(i as nat)]);
        // emb(ti, [s, Gen(i)]) =~= [s] + [s⁻¹, Gen(i)] = [s, s⁻¹, Gen(i)].
        assert(apply_embedding(ti, seq![s, Symbol::Gen(i as nat)])
            =~= seq![s] + seq![inverse_symbol(s), Symbol::Gen(i as nat)]);
        assert(comp[g] =~= seq![s, inverse_symbol(s), Symbol::Gen(i as nat)]);
        // [s, s⁻¹] ≡ ε  ⟹  [s, s⁻¹, Gen(i)] ≡ [Gen(i)].
        assert(seq![s] + seq![inverse_symbol(s)] =~= seq![s, inverse_symbol(s)]);
        assert(inverse_word(seq![s]) =~= seq![inverse_symbol(s)]) by { reveal_with_fuel(inverse_word, 2); }
        assert(symbol_valid(s, k));
        assert(word_valid(seq![s], k));
        lemma_word_inverse_right(fg, seq![s]);                   // [s]+[s⁻¹] ≡ ε
        assert(seq![s] + inverse_word(seq![s]) =~= seq![s, inverse_symbol(s)]);
        // splice: [s,s⁻¹]+[Gen(i)] ≡ ε+[Gen(i)] = [Gen(i)].
        assert(symbol_valid(Symbol::Gen(i as nat), k));
        lemma_equiv_concat_left(fg, seq![s, inverse_symbol(s)], empty_word(),
            seq![Symbol::Gen(i as nat)]);
        assert(concat(seq![s, inverse_symbol(s)], seq![Symbol::Gen(i as nat)])
            =~= seq![s, inverse_symbol(s), Symbol::Gen(i as nat)]);
        assert(concat(empty_word(), seq![Symbol::Gen(i as nat)]) =~= seq![Symbol::Gen(i as nat)]);
    } else {
        // t[g] = [Gen(g)]; emb(ti, [Gen(g)]) = ti[g] = [Gen(g)] (g ≠ i).
        assert(t[g] == seq![Symbol::Gen(g as nat)]);
        reveal_with_fuel(apply_embedding, 2);
        lemma_concat_empty_right(ti[g as int]);
        assert(apply_embedding(ti, seq![Symbol::Gen(g as nat)]) =~= ti[g as int]);
        assert(ti[g as int] == seq![Symbol::Gen(g as nat)]) by { assert(g != i); }
        lemma_equiv_refl(fg, seq![Symbol::Gen(g as nat)]);
    }
}

/// **The transvection embedding is injective** on `free(k)`: `emb(transvect_emb(k,i,s), w) ≡_free ε
/// ⟹ w ≡_free ε`.  Undo by `τ⁻¹` (`free_to_embedding`); `compose(τ⁻¹, τ)` is per-gen `≡_free` the
/// identity (`lemma_transvect_compose_inv`), which `respects_gen_equiv` + `apply_id_emb` collapse to `w`.
proof fn lemma_transvect_emb_injective(k: nat, i: int, s: Symbol, w: Word)
    requires
        symbol_valid(s, k),
        generator_index(s) != i,
        0 <= i < k,
        word_valid(w, k),
        equiv_in_presentation(free_group(k), apply_embedding(transvect_emb(k, i, s), w), empty_word()),
    ensures
        equiv_in_presentation(free_group(k), w, empty_word()),
{
    let fg = free_group(k);
    lemma_free_group_valid(k);
    let t = transvect_emb(k, i, s);
    let ti = transvect_emb(k, i, inverse_symbol(s));
    let comp = compose_embeddings(ti, t);
    let id_emb = Seq::new(k as int as nat, |g: int| seq![Symbol::Gen(g as nat)]);
    // t, ti entries valid over k.
    assert(t.len() == k && ti.len() == k);
    assert forall|g: int| 0 <= g < k implies (word_valid(#[trigger] t[g], k) && word_valid(ti[g], k)) by {
        if g == i {
            assert(t[g] == seq![s, Symbol::Gen(g as nat)]);
            assert(ti[g] == seq![inverse_symbol(s), Symbol::Gen(g as nat)]);
            assert(symbol_valid(inverse_symbol(s), k));
        } else {
            assert(t[g] == seq![Symbol::Gen(g as nat)] && ti[g] == seq![Symbol::Gen(g as nat)]);
        }
    }
    // emb(ti, emb(t, w)) ≡_free emb(ti, ε) = ε.
    lemma_apply_embedding_valid(t, w, k);
    lemma_free_to_embedding(ti, fg, apply_embedding(t, w));
    assert(apply_embedding(ti, empty_word()) =~= empty_word());
    // emb(ti, emb(t,w)) = emb(comp, w).
    lemma_apply_embedding_compose(ti, t, w);
    assert(apply_embedding(ti, apply_embedding(t, w)) == apply_embedding(comp, w));
    // comp per-gen ≡_free id_emb ⟹ emb(comp, w) ≡_free emb(id_emb, w) = w.
    assert(comp.len() == k && id_emb.len() == k);
    assert forall|g: int| 0 <= g < k implies (word_valid(#[trigger] comp[g], k)
        && word_valid(id_emb[g], k)) by {
        lemma_apply_embedding_valid(ti, t[g], k);
        assert(comp[g] == apply_embedding(ti, t[g]));
        assert(id_emb[g] == seq![Symbol::Gen(g as nat)]);
    }
    assert forall|g: int| 0 <= g < k implies
        equiv_in_presentation(fg, comp[g], id_emb[g]) by {
        lemma_transvect_compose_inv(k, i, s, g);
        assert(id_emb[g] == seq![Symbol::Gen(g as nat)]);
    }
    lemma_emb_respects_gen_equiv(fg, id_emb, comp, w);          // emb(comp,w) ≡ emb(id_emb,w)
    lemma_apply_id_emb(k, w);                                    // emb(id_emb, w) =~= w
    lemma_apply_embedding_valid(comp, w, k);                     // emb(comp,w) valid over k
    // emb(comp,w) ≡_free ε  (free_to_embedding gave emb(ti,emb(t,w)) ≡ ε; = emb(comp,w)).
    assert(equiv_in_presentation(fg, apply_embedding(comp, w), empty_word()));
    // emb(id_emb,w) = w  ⟹  emb(comp,w) ≡ w  ⟹  w ≡ emb(comp,w) ≡ ε.
    assert(apply_embedding(id_emb, w) =~= w);
    lemma_equiv_symmetric(fg, apply_embedding(comp, w), w);
    lemma_equiv_transitive(fg, w, apply_embedding(comp, w), empty_word());
}

/// **Nielsen transvection preserves freeness.**  If `gens` is a free family in `gp`, `s` a letter
/// over `gens.len()` with `generator_index(s) ≠ i`, then `compose(gens, transvect_emb(·,i,s))` — `gens`
/// with `gens[i]` left-multiplied by `apply_embedding_symbol(gens, s)` — is a free family.  Rung (iv)
/// of map_b forward's φ_F injectivity (`d ↦ b_l·d`).
pub proof fn lemma_free_family_transvect(gp: Presentation, gens: Seq<Word>, i: int, s: Symbol)
    requires
        presentation_valid(gp),
        is_free_family(gp, gens),
        0 <= i < gens.len(),
        symbol_valid(s, gens.len()),
        generator_index(s) != i,
    ensures
        is_free_family(gp, compose_embeddings(gens, transvect_emb(gens.len(), i, s))),
{
    let ng = gp.num_generators;
    let k = gens.len();
    let t = transvect_emb(k, i, s);
    let nf = compose_embeddings(gens, t);
    // gens valid (first conjunct).
    assert forall|g: int| 0 <= g < k implies word_valid(#[trigger] gens[g], ng) by {}
    // t entries valid over k.
    assert forall|g: int| 0 <= g < k implies word_valid(#[trigger] t[g], k) by {
        if g == i { assert(t[g] == seq![s, Symbol::Gen(g as nat)]); }
        else { assert(t[g] == seq![Symbol::Gen(g as nat)]); }
    }
    // nf entries valid over ng (= emb(gens, t[g])).
    assert(nf.len() == k);
    assert forall|g: int| 0 <= g < k implies word_valid(#[trigger] nf[g], ng) by {
        assert(nf[g] == apply_embedding(gens, t[g]));
        lemma_apply_embedding_valid(gens, t[g], ng);
    }
    // freeness: emb(nf, w) ≡_{gp} ε ⟹ w ≡_free ε.
    assert forall|w: Word| (#[trigger] word_valid(w, nf.len())
        && equiv_in_presentation(gp, apply_embedding(nf, w), empty_word()))
        implies equiv_in_presentation(free_group(nf.len()), w, empty_word()) by {
        assert(word_valid(w, k));
        // emb(nf, w) = emb(gens, emb(t, w)).
        lemma_apply_embedding_compose(gens, t, w);
        assert(apply_embedding(gens, apply_embedding(t, w)) == apply_embedding(nf, w));
        // gens free ⟹ emb(t, w) ≡_free ε.
        lemma_apply_embedding_valid(t, w, k);
        assert(equiv_in_presentation(gp, apply_embedding(gens, apply_embedding(t, w)), empty_word()));
        assert(equiv_in_presentation(free_group(k), apply_embedding(t, w), empty_word()));
        // transvect injective ⟹ w ≡_free ε.
        lemma_transvect_emb_injective(k, i, s, w);
        assert(nf.len() == k);
    }
}

} // verus!
