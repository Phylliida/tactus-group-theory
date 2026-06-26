//! # Layer 0.5 compactness probe (design doc §D) — NON-COMMITTING.
//!
//! The decisive unknown for Layer 0.5 (`docs/machine-bridge-and-infinite-gen-plan.md` §B.3/§C/§D):
//! does Miller Thm 4.1's HNN faithfulness `C₀ ↪ L ↪ G` (over the **infinitely**-generated
//! `L = C₀ ⋆ F₂`) **localize to finite slices** — letting us reuse the proven *finite* Britton +
//! free-product stack — or does it force a multi-week infinite-generator presentation port?
//!
//! This module answers it empirically (the analog of session-12's `pred_presentation.rs` probe).
//! It shows, machine-checked, that for a **fixed word** over a finite slice of generators the whole
//! per-word faithfulness obligation is a legal *finite* `HNNData` that plugs straight into:
//!   * `lemma_single_hnn_base_faithful` (finite Britton base-embed) — for `L^(N) ↪ G^(N)`, and
//!   * `lemma_free_product_injective_left` (free-product faithfulness) — for `C₀^(N) ↪ L^(N)`,
//! with the HNN iso precondition reduced **generically** to two `is_free_family` facts on the
//! association columns (`lemma_iso_from_free_columns`).
//!
//! **Outcome (0 errors): POSITIVE.** Option (i)+compactness is real — NO infinite-generator
//! presentation type is on the critical path. The infinity survives only in (a) the already-done
//! bespoke `ceer_group.rs` forward direction and (b) the meta-level `∀w ∃N` compactness quantifier,
//! which needs no infinite-gen type. The **only** genuinely-new math left is the A-column basis
//! `{b, cᵢa⁻ⁱbaⁱ}` being a free family in the free *product* `C₀⋆F₂` (the B-column `{a, b⁻ⁱabⁱ}`
//! is pure-F₂ = already banked, `lemma_conj_family_b_free`).
//!
//! Per the standing rule (`MESSAGES_FROM_USER.md`): this follows Miller §4.1 literally and does NOT
//! use the §B.4 "C₀ is free" shortcut (a trap — `∼` is only c.e., the basis `ℕ/∼` is not
//! computable; the c-relators are carried opaquely as `decls`).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::benign::*;
use crate::hnn::*;
use crate::free_product::*;
use crate::higman_operations::*;          // free_group
use crate::machine_group::*;              // symbol_power, lemma_symbol_power_valid, lemma_word_valid_mono
use crate::free_basis::*;                 // lemma_free_to_embedding (F3)
use crate::f_free::*;                      // is_free_family
use crate::normal_form_free_product::*;   // lemma_free_product_injective_left

verus! {

// ===========================================================================
// Part A — the GENERIC, reusable nugget.
//   free columns  ⟹  HNN iso  ⟹  base-faithful.
// Column-agnostic: mirrors `lemma_recog_associations_isomorphic` (f_free_a1.rs) but as a
// standalone tool. This is what the real Layer-0.5 build will consume once the A-column
// free-family fact is proven.
// ===========================================================================

/// **Free→iso reduction.** If both association columns of an HNN datum are free families in the
/// base (their common length = the number of associations), the associations are isomorphic:
/// `a_col` free ⟹ `(emb(a,w)≡ε ⟹ w free)` ⟹ (F3) `emb(b,w)≡ε`, and symmetrically.
/// The a-/b-columns of an HNN datum as NAMED spec fns (one closure, defined once) — referencing
/// these at lemma boundaries avoids closure-identity mismatches that inline `Seq::new(..|i|..)`
/// would trigger under the Lean backend.
pub open spec fn assoc_col0(data: HNNData) -> Seq<Word> {
    Seq::new(data.associations.len(), |i: int| data.associations[i].0)
}
pub open spec fn assoc_col1(data: HNNData) -> Seq<Word> {
    Seq::new(data.associations.len(), |i: int| data.associations[i].1)
}

pub proof fn lemma_iso_from_free_columns(data: HNNData)
    requires
        presentation_valid(data.base),
        is_free_family(data.base, assoc_col0(data)),
        is_free_family(data.base, assoc_col1(data)),
    ensures
        hnn_associations_isomorphic(data),
{
    let k = data.associations.len();
    let a_col = Seq::new(k, |i: int| data.associations[i].0);
    let b_col = Seq::new(k, |i: int| data.associations[i].1);
    assert(a_col.len() == k);
    assert(b_col.len() == k);
    // bridge the named columns (requires) to the local closures (= hnn_associations_isomorphic's).
    assert(assoc_col0(data) =~= a_col);
    assert(assoc_col1(data) =~= b_col);
    assert(is_free_family(data.base, a_col));
    assert(is_free_family(data.base, b_col));
    assert forall|w: Word| word_valid(w, k) implies (
        equiv_in_presentation(data.base, apply_embedding(a_col, w), empty_word())
        <==>
        equiv_in_presentation(data.base, apply_embedding(b_col, w), empty_word())
    ) by {
        if equiv_in_presentation(data.base, apply_embedding(a_col, w), empty_word()) {
            // a_col is free ⟹ w is free in F_k; then F3 on b_col ⟹ b-side trivial.
            assert(word_valid(w, a_col.len()));   // fire is_free_family(a_col)'s forall
            assert(equiv_in_presentation(free_group(a_col.len()), w, empty_word()));
            lemma_free_to_embedding(b_col, data.base, w);
        }
        if equiv_in_presentation(data.base, apply_embedding(b_col, w), empty_word()) {
            assert(word_valid(w, b_col.len()));   // fire is_free_family(b_col)'s forall
            assert(equiv_in_presentation(free_group(b_col.len()), w, empty_word()));
            lemma_free_to_embedding(a_col, data.base, w);
        }
    }
}

/// **Base-faithful from free columns.** The finite Britton base-embed with its iso precondition
/// discharged by Part A: a base word trivial in the HNN presentation is trivial in the base.
pub proof fn lemma_hnn_base_faithful_from_free_columns(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        is_free_family(data.base, assoc_col0(data)),
        is_free_family(data.base, assoc_col1(data)),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    reveal(hnn_data_valid);                        // presentation_valid(data.base) for the iso lemma
    lemma_iso_from_free_columns(data);
    lemma_single_hnn_base_faithful(data, w);
}

// ===========================================================================
// Part B — the Miller Thm 4.1 finite slice is a *legal finite* `HNNData`.
//   L^(N) = C₀^(N) ⋆ F₂,  associations  {(b,a)} ∪ {(cᵢa⁻ⁱbaⁱ, b⁻ⁱabⁱ) : i<N}.
// In L^(N)'s alphabet: cᵢ = Gen(i) (i<N),  a = Gen(N),  b = Gen(N+1).
// ===========================================================================

/// `C₀^(N)`: the finite slice — N generators (the `cᵢ`), recursively presented by an explicit
/// finite relator list `decls` (declared CEER pairs among the first N generators). NOT a free
/// group: the relators are carried opaquely (§B.4 — the freeness shortcut is a trap).
pub open spec fn c0_slice(n: nat, decls: Seq<Word>) -> Presentation {
    Presentation { num_generators: n, relators: decls }
}

/// `L^(N) = C₀^(N) ⋆ F₂`.  `num_generators = n + 2`;  a = Gen(n), b = Gen(n+1).
pub open spec fn l_slice(n: nat, decls: Seq<Word>) -> Presentation {
    free_product(c0_slice(n, decls), free_group(2))
}

/// A-basis element `cᵢ · a⁻ⁱ · b · aⁱ` in `L^(N)` (a = Gen(n), b = Gen(n+1)).
pub open spec fn a_basis_elt(n: nat, i: nat) -> Word {
    seq![Symbol::Gen(i)]
        + symbol_power(Symbol::Inv(n), i)
        + seq![Symbol::Gen(n + 1)]
        + symbol_power(Symbol::Gen(n), i)
}

/// B-basis element `b⁻ⁱ · a · bⁱ` in `L^(N)`.
pub open spec fn b_basis_elt(n: nat, i: nat) -> Word {
    symbol_power(Symbol::Inv(n + 1), i)
        + seq![Symbol::Gen(n)]
        + symbol_power(Symbol::Gen(n + 1), i)
}

/// The A-column basis `{b} ∪ {cᵢa⁻ⁱbaⁱ : i<N}` — length `n+1`.
pub open spec fn miller_a_col(n: nat) -> Seq<Word> {
    seq![seq![Symbol::Gen(n + 1)]] + Seq::new(n, |i: int| a_basis_elt(n, i as nat))
}

/// The B-column basis `{a} ∪ {b⁻ⁱabⁱ : i<N}` — length `n+1`.
pub open spec fn miller_b_col(n: nat) -> Seq<Word> {
    seq![seq![Symbol::Gen(n)]] + Seq::new(n, |i: int| b_basis_elt(n, i as nat))
}

/// `G^(N)` = HNN(L^(N), t | t⁻¹·(a_col[i])·t = b_col[i]), the finite slice of Miller's `G`.
pub open spec fn miller_data(n: nat, decls: Seq<Word>) -> HNNData {
    HNNData {
        base: l_slice(n, decls),
        associations: Seq::new((n + 1) as nat,
            |i: int| (miller_a_col(n)[i], miller_b_col(n)[i])),
    }
}

// --- column word-validity (every column word lives over the n+2 generators of L^(N)) ---

/// A single-generator word is valid when its index fits.
proof fn lemma_single_gen_valid(g: nat, nn: nat)
    requires g < nn,
    ensures word_valid(seq![Symbol::Gen(g)], nn),
{
    assert forall|j: int| 0 <= j < seq![Symbol::Gen(g)].len()
        implies symbol_valid(#[trigger] seq![Symbol::Gen(g)][j], nn) by {
        assert(seq![Symbol::Gen(g)][j] == Symbol::Gen(g));
    }
}

proof fn lemma_a_basis_elt_valid(n: nat, i: nat)
    requires i < n,
    ensures word_valid(a_basis_elt(n, i), (n + 2) as nat),
{
    let nn = (n + 2) as nat;
    let aw = seq![Symbol::Gen(i)];
    let p = symbol_power(Symbol::Inv(n), i);
    let bw = seq![Symbol::Gen(n + 1)];
    let q = symbol_power(Symbol::Gen(n), i);
    lemma_single_gen_valid(i, nn);
    lemma_symbol_power_valid(Symbol::Inv(n), i, nn);
    lemma_single_gen_valid((n + 1) as nat, nn);
    lemma_symbol_power_valid(Symbol::Gen(n), i, nn);
    lemma_concat_word_valid(aw, p, nn);
    lemma_concat_word_valid(concat(aw, p), bw, nn);
    lemma_concat_word_valid(concat(concat(aw, p), bw), q, nn);
    assert(a_basis_elt(n, i) =~= concat(concat(concat(aw, p), bw), q));
}

proof fn lemma_b_basis_elt_valid(n: nat, i: nat)
    ensures word_valid(b_basis_elt(n, i), (n + 2) as nat),
{
    let nn = (n + 2) as nat;
    let p = symbol_power(Symbol::Inv(n + 1), i);
    let mid = seq![Symbol::Gen(n)];
    let q = symbol_power(Symbol::Gen(n + 1), i);
    lemma_symbol_power_valid(Symbol::Inv(n + 1), i, nn);
    lemma_single_gen_valid(n, nn);
    lemma_symbol_power_valid(Symbol::Gen(n + 1), i, nn);
    lemma_concat_word_valid(p, mid, nn);
    lemma_concat_word_valid(concat(p, mid), q, nn);
    assert(b_basis_elt(n, i) =~= concat(concat(p, mid), q));
}

proof fn lemma_miller_cols_valid(n: nat)
    ensures
        forall|i: int| 0 <= i < miller_a_col(n).len()
            ==> word_valid(#[trigger] miller_a_col(n)[i], (n + 2) as nat),
        forall|i: int| 0 <= i < miller_b_col(n).len()
            ==> word_valid(#[trigger] miller_b_col(n)[i], (n + 2) as nat),
{
    assert(miller_a_col(n).len() == n + 1);
    assert(miller_b_col(n).len() == n + 1);
    assert forall|i: int| 0 <= i < miller_a_col(n).len()
        implies word_valid(#[trigger] miller_a_col(n)[i], (n + 2) as nat) by {
        if i == 0 {
            assert(miller_a_col(n)[i] == seq![Symbol::Gen(n + 1)]);
        } else {
            assert(((i - 1) as nat) < n);
            assert(miller_a_col(n)[i] == a_basis_elt(n, (i - 1) as nat));
            lemma_a_basis_elt_valid(n, (i - 1) as nat);
        }
    }
    assert forall|i: int| 0 <= i < miller_b_col(n).len()
        implies word_valid(#[trigger] miller_b_col(n)[i], (n + 2) as nat) by {
        if i == 0 {
            assert(miller_b_col(n)[i] == seq![Symbol::Gen(n)]);
        } else {
            assert(miller_b_col(n)[i] == b_basis_elt(n, (i - 1) as nat));
            lemma_b_basis_elt_valid(n, (i - 1) as nat);
        }
    }
}

/// `L^(N)` is a valid presentation, given the c-relators `decls` live over the `n` c-generators.
proof fn lemma_l_slice_valid(n: nat, decls: Seq<Word>)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
    ensures
        presentation_valid(l_slice(n, decls)),
        l_slice(n, decls).num_generators == n + 2,
{
    reveal(presentation_valid);
    let p = l_slice(n, decls);
    assert(p.num_generators == n + 2);
    // relators = decls + shift_relators(empty, n);  shift of empty = empty ⟹ relators =~= decls.
    assert(free_group(2).relators.len() == 0);
    assert(shift_relators(free_group(2).relators, n).len() == 0);
    assert(p.relators =~= decls);
    assert forall|j: int| 0 <= j < p.relators.len()
        implies word_valid(#[trigger] p.relators[j], p.num_generators) by {
        assert(p.relators[j] == decls[j]);
        lemma_word_valid_mono(decls[j], n, (n + 2) as nat);
    }
    assert(presentation_valid(p));
}

/// **Statability + validity.** The Miller finite slice `G^(N)` is a legal finite `HNNData`.
pub proof fn lemma_miller_data_valid(n: nat, decls: Seq<Word>)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
    ensures
        hnn_data_valid(miller_data(n, decls)),
        miller_data(n, decls).base.num_generators == n + 2,
        miller_data(n, decls).associations.len() == n + 1,
{
    let data = miller_data(n, decls);
    lemma_l_slice_valid(n, decls);
    lemma_miller_cols_valid(n);
    assert(data.associations.len() == n + 1);
    assert forall|i: int| 0 <= i < data.associations.len() implies
        word_valid(data.associations[i].0, data.base.num_generators)
        && word_valid(data.associations[i].1, data.base.num_generators) by {
        assert(data.associations[i].0 == miller_a_col(n)[i]);
        assert(data.associations[i].1 == miller_b_col(n)[i]);
    }
}

/// The named association columns of the Miller slice ARE the Miller `a_col`/`b_col`.
proof fn lemma_miller_assoc_cols(n: nat, decls: Seq<Word>)
    ensures
        assoc_col0(miller_data(n, decls)) == miller_a_col(n),
        assoc_col1(miller_data(n, decls)) == miller_b_col(n),
{
    let data = miller_data(n, decls);
    assert(data.associations.len() == n + 1);
    assert(miller_a_col(n).len() == n + 1);
    assert(miller_b_col(n).len() == n + 1);
    assert(assoc_col0(data) =~= miller_a_col(n));
    assert(assoc_col1(data) =~= miller_b_col(n));
}

// ===========================================================================
// Part C — the capstone: per-word faithfulness for the Miller slice reduces to
//   [free-product injectivity: HAVE] + [finite Britton: HAVE] + [two free-family facts].
// The two free-family facts are taken as hypotheses (proving the A-column one IS the real
// Layer-0.5 build; the B-column one is banked). Everything ELSE is discharged here.
// ===========================================================================

/// **THE PROBE RESULT.** For a fixed `C₀`-word `w` (over the `n` c-generators) that is trivial in
/// the Miller finite slice `G^(N)`, faithfulness descends to `w` trivial in `C₀^(N)` — GIVEN only
/// that the two association columns are free families in `L^(N)`. The free-product step
/// (`lemma_free_product_injective_left`) and the finite Britton step
/// (`lemma_single_hnn_base_faithful`, via Part A) are fully discharged; the columns' freeness is
/// the sole remaining input. This is the machine-checked statement that Miller's HNN faithfulness
/// **localizes to finite slices** — no infinite-generator port needed.
pub proof fn lemma_miller_slice_faithfulness_reduces(n: nat, decls: Seq<Word>, w: Word)
    requires
        forall|j: int| 0 <= j < decls.len() ==> word_valid(#[trigger] decls[j], n),
        is_free_family(l_slice(n, decls), miller_a_col(n)),   // A-column free in L^(N)  (the real build)
        is_free_family(l_slice(n, decls), miller_b_col(n)),   // B-column free in L^(N)  (pure-F₂ = banked)
        word_valid(w, n),                                       // w is a C₀^(N)-word
        equiv_in_presentation(hnn_presentation(miller_data(n, decls)), w, empty_word()),  // w = 1 in G^(N)
    ensures
        equiv_in_presentation(c0_slice(n, decls), w, empty_word()),                        // w = 1 in C₀^(N)
{
    let data = miller_data(n, decls);
    lemma_miller_data_valid(n, decls);             // hnn_data_valid(data), base.num_generators == n+2
    lemma_miller_assoc_cols(n, decls);             // generic cols == miller cols
    lemma_l_slice_valid(n, decls);                 // presentation_valid(L^(N)), num_generators == n+2

    // Bridge the Miller-form free-family hypotheses to the named-column form Part A wants.
    assert(data.base == l_slice(n, decls));
    assert(is_free_family(data.base, assoc_col0(data)));   // == miller_a_col(n) + hyp
    assert(is_free_family(data.base, assoc_col1(data)));   // == miller_b_col(n) + hyp

    // w is valid over L^(N)'s generators (n ≤ n+2).
    lemma_word_valid_mono(w, n, (n + 2) as nat);
    assert(word_valid(w, data.base.num_generators));

    // Step 1 — finite Britton base-embed: w = 1 in G^(N) ⟹ w = 1 in L^(N).
    lemma_hnn_base_faithful_from_free_columns(data, w);
    assert(equiv_in_presentation(l_slice(n, decls), w, empty_word()));

    // Step 2 — free-product faithfulness: w (a C₀-word) = 1 in L^(N) ⟹ w = 1 in C₀^(N).
    reveal(presentation_valid);
    assert(presentation_valid(c0_slice(n, decls)));    // = the decls precondition
    lemma_free_group_valid(2);                          // presentation_valid(free_group(2))
    lemma_free_product_injective_left(c0_slice(n, decls), free_group(2), w);
}

} // verus!
