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
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_valid};
use crate::higman_operations::{free_group, lemma_free_group_valid};
use crate::free_basis::lemma_free_to_embedding;
use crate::f_free::is_free_family;
use crate::h3_ii::{compose_embeddings, lemma_apply_embedding_compose};

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

} // verus!
