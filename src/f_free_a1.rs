// Layer 2 — Brick 5 COMPLETENESS, C3.2c / A1: the recognition-datum association isomorphism.
//
// `recog_data` (`h3_ii.rs`) recognizes the whole `h2_II` as a single `p`-HNN over `h1_base`, with
// associations `p_assoc ++ family_II_assoc`. Britton over that recognition needs only the iso
// condition `hnn_associations_isomorphic(recog_data)` — the "free-base fallacy": Britton never needs
// a free base, only that the `a_words ↦ b_words` correspondence is a subgroup iso.
//
// A1 (docs/brick5-c3.2c-plan.md §4.2) collapses that iso to an assembly of two ALREADY-PROVEN free
// families through F3 (`free_basis::lemma_free_to_embedding`):
//   • the `.0` column is `config_emb(betas)` with `betas = [0] ++ alphas` (the `p_assoc` head `(t,·)`
//     IS the α=0 case: `config_word(0,0) =~= [t]`),
//   • the `.1` column is `basis_emb(betas)` (the `p_assoc` head rhs `td` IS `basis_elt(0)` since
//     `w_b(_,0)=ε`; each `family_II_rhs(β) == basis_elt(β)` definitionally via `h_w_b = w_b(b_base…)`).
// Both columns are free in `h1_base` (`lemma_config_emb_free_in_h1` lifts F2 via the `kill_hom`
// retraction; `lemma_basis_elt_free` is the 29/0 headline), so the iff is "free ⟹ both trivial" both
// ways.
//
// THIS MODULE delivers the first two rungs (the genuinely-new SHORT pieces):
//   1. `lemma_km_faithful_in_h1`  — the `kill_hom` retraction: `K_M` embeds faithfully in `h1_base`.
//   2. `lemma_config_emb_free_in_h1` — config family free in `h1_base` (= F2 + the retraction).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::homomorphism::{apply_hom, lemma_hom_preserves_equiv};
use crate::machine_group::{ModMachine, mod_machine_wf, g_m, lemma_g_m_num_generators, config_word,
    lemma_config_word_valid, lemma_word_valid_mono, lemma_config_word_zero,
    lemma_single_hnn_base_faithful};
use crate::h1::h1_base;
use crate::benign::{apply_embedding, lemma_apply_embedding_valid};
use crate::free_basis::{kill_hom, lemma_kill_hom_valid, lemma_kill_fixes_low, config_emb,
    lemma_config_emb_free, basis_emb, basis_elt, lemma_basis_elt_free, lemma_free_to_basis_elt,
    lemma_free_to_embedding};
use crate::higman_operations::free_group;
use crate::hnn::{HNNData, hnn_associations_isomorphic};
use crate::h2::{p_assoc, td_word};
use crate::h3_ii::{recog_data, family_II_assoc, family_II_rhs, h2_II, lemma_recog_data_valid,
    lemma_recog_presentation};
use crate::h1::{h_w_b, lemma_h1_base_valid, lemma_h1_base_num_generators};
use crate::layout::{b_base, d_idx, h1_num_gens};
use crate::word_numbering::{numbers_word, w_b, w_c};
use crate::f_free_h1::{f_h1_family, lemma_f_free_in_h1};

verus! {

// ----------------------------------------------------------------------------
// A1, rung 1 — the `kill_hom` retraction:  K_M ↪ h1_base is faithful.
// ----------------------------------------------------------------------------

/// **`K_M` embeds faithfully in `h1_base`.** A `K_M`-word (`< nk` generators) that is trivial in
/// `h1_base` is already trivial in `K_M = g_m`. This is the one genuinely-new piece of A1: the
/// `kill_hom : h1_base → g_m` (identity on the K_M block, killing the c/b/d block) is a RETRACTION,
/// so equivalence in `h1_base` of a low word pushes down to `g_m`.
///
/// Proof: `kill_hom` is a valid homomorphism (`lemma_kill_hom_valid`), so it preserves equivalence
/// (`lemma_hom_preserves_equiv`): `φ(w) ≡_{g_m} φ(ε) = ε`. But `φ` fixes the low word `w`
/// (`lemma_kill_fixes_low`: `φ(w) =~= w`), so `w ≡_{g_m} ε`.
pub proof fn lemma_km_faithful_in_h1(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, g_m(mm).num_generators),
        equiv_in_presentation(h1_base(mm, n), w, empty_word()),
    ensures
        equiv_in_presentation(g_m(mm), w, empty_word()),
{
    let h = kill_hom(mm, n);
    lemma_kill_hom_valid(mm, n);                       // is_valid_homomorphism(h)
    assert(h.source == h1_base(mm, n) && h.target == g_m(mm));
    // φ preserves equivalence: φ(w) ≡_{g_m} φ(ε).
    lemma_hom_preserves_equiv(h, w, empty_word());
    // φ fixes the low word: φ(w) =~= w; and φ(ε) =~= ε.
    lemma_kill_fixes_low(mm, n, w);
    assert(apply_hom(h, empty_word()) =~= empty_word());
}

// ----------------------------------------------------------------------------
// A1, rung 2 — the config family is free in `h1_base`.
// ----------------------------------------------------------------------------

/// **`config_emb(alphas)` is a free family in `h1_base`.** `lemma_config_emb_free` already gives it
/// free in `K_M = g_m`; we LIFT to `h1_base` via the retraction `lemma_km_faithful_in_h1`. The
/// embedded product `apply_embedding(config_emb, w)` is a `K_M`-word (config words live on gens
/// 0–2 < nk), so triviality in `h1_base` descends to `g_m`, where F2 closes it.
pub proof fn lemma_config_emb_free_in_h1(mm: ModMachine, n: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        alphas.no_duplicates(),
        word_valid(w, alphas.len()),
        equiv_in_presentation(h1_base(mm, n),
            apply_embedding(config_emb(alphas), w), empty_word()),
    ensures
        equiv_in_presentation(free_group(alphas.len()), w, empty_word()),
{
    let emb = config_emb(alphas);
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                      // nk = 4 + |quads| ≥ 4 > 3
    // Each config word is valid over the base-A gens {0,1,2}, hence over nk.
    assert forall|i: int| 0 <= i < emb.len() implies word_valid(#[trigger] emb[i], nk) by {
        assert(emb[i] == config_word(alphas[i], 0));
        lemma_config_word_valid(alphas[i], 0);         // word_valid(·, 3)
        lemma_word_valid_mono(emb[i], 3, nk);          // 3 ≤ nk
    }
    // So the whole embedded product is a K_M word.
    lemma_apply_embedding_valid(emb, w, nk);
    // Retraction: ≡_{h1_base} ε  ⟹  ≡_{g_m} ε.
    lemma_km_faithful_in_h1(mm, n, apply_embedding(emb, w));
    // F2: the config family is free in g_m ⟹ w ≡_free ε.
    lemma_config_emb_free(mm, alphas, w);
}

// ----------------------------------------------------------------------------
// A1, rung 3 — the `betas = [0] ++ alphas` index family and column correspondence.
// ----------------------------------------------------------------------------

/// `betas(alphas) = [0] ++ alphas`. The `p_assoc` head `(t, td)` IS the `α = 0` case of the
/// family-(II) associations, so prepending `0` unifies the two recognition columns into a single
/// `config_emb` / `basis_emb` over `betas`.
pub open spec fn betas(alphas: Seq<nat>) -> Seq<nat> {
    seq![0nat] + alphas
}

/// Index facts: `|betas| = |alphas| + 1`, `betas[0] = 0`, `betas[i+1] = alphas[i]`.
pub proof fn lemma_betas_index(alphas: Seq<nat>)
    ensures
        betas(alphas).len() == alphas.len() + 1,
        betas(alphas)[0] == 0,
        forall|i: int| 0 <= i < alphas.len() ==> #[trigger] betas(alphas)[i + 1] == alphas[i],
{
    let b = betas(alphas);
    assert(b[0] == 0);
    assert forall|i: int| 0 <= i < alphas.len() implies #[trigger] b[i + 1] == alphas[i] by {
        assert(b[i + 1] == alphas[i]);
    }
}

/// `betas` numbers words (each digit ok): `0 ∈ I` trivially, and the `alphas` carry the hypothesis.
pub proof fn lemma_betas_numbers_word(n: nat, m: nat, alphas: Seq<nat>)
    requires forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures forall|i: int| 0 <= i < betas(alphas).len() ==> numbers_word(n, m, #[trigger] betas(alphas)[i]),
{
    let b = betas(alphas);
    lemma_betas_index(alphas);
    assert forall|i: int| 0 <= i < b.len() implies numbers_word(n, m, #[trigger] b[i]) by {
        if i == 0 {
            assert(b[0] == 0);            // numbers_word(n,m,0) == true
        } else {
            assert(b[i] == alphas[i - 1]);
        }
    }
}

/// `betas` has no duplicates when `0 ∉ alphas` and `alphas` is distinct.
pub proof fn lemma_betas_no_duplicates(alphas: Seq<nat>)
    requires !alphas.contains(0nat), alphas.no_duplicates(),
    ensures betas(alphas).no_duplicates(),
{
    let b = betas(alphas);
    lemma_betas_index(alphas);
    assert forall|i: int, j: int| 0 <= i < j < b.len() implies b[i] != b[j] by {
        if i == 0 {
            // b[0] = 0, b[j] = alphas[j-1] (j ≥ 1); 0 ∉ alphas ⟹ b[j] != 0.
            assert(b[j] == alphas[j - 1]);
            if b[j] == 0 {
                assert(alphas[j - 1] == 0nat);
                assert(alphas.contains(0nat));      // witness k = j-1
            }
        } else {
            // i, j ≥ 1: b[i] = alphas[i-1], b[j] = alphas[j-1], distinct by no_duplicates.
            assert(b[i] == alphas[i - 1]);
            assert(b[j] == alphas[j - 1]);
        }
    }
}

/// The `.0` recognition column IS `config_emb(betas)` (entrywise seq-equal): head
/// `t = [Gen0] =~= config_word(0,0)` (`lemma_config_word_zero`), tail `config_word(αᵢ,0)` definitional.
proof fn lemma_a_col_eq_config_emb(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    ensures
        Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                 |i: int| recog_data(mm, n, m, alphas).associations[i].0)
        =~= config_emb(betas(alphas)),
{
    let nk = g_m(mm).num_generators;
    let data = recog_data(mm, n, m, alphas);
    let pa = p_assoc(nk, n);
    let fa = family_II_assoc(mm, n, m, alphas);
    let acol = Seq::new(data.associations.len(), |i: int| data.associations[i].0);
    let ce = config_emb(betas(alphas));
    lemma_betas_index(alphas);
    lemma_config_word_zero();                          // config_word(0,0) =~= [Gen0]
    assert(data.associations =~= pa + fa);
    assert(pa.len() == 1);
    assert(data.associations.len() == 1 + alphas.len());
    assert forall|j: int| 0 <= j < acol.len() implies acol[j] =~= ce[j] by {
        if j == 0 {
            assert(data.associations[0] == pa[0]);
            assert(pa[0] == (seq![Symbol::Gen(0)], td_word(nk, n)));
            assert(acol[0] == seq![Symbol::Gen(0)]);
            assert(ce[0] == config_word(betas(alphas)[0], 0));
            assert(betas(alphas)[0] == 0);
        } else {
            let i = j - 1;
            assert(data.associations[j] == fa[i]);
            assert(fa[i] == (config_word(alphas[i], 0), family_II_rhs(mm, n, m, alphas[i])));
            assert(acol[j] == config_word(alphas[i], 0));
            assert(ce[j] == config_word(betas(alphas)[j], 0));
            assert(betas(alphas)[j] == alphas[i]);
        }
    }
}

/// The `.1` recognition column IS `basis_emb(betas)` (entrywise seq-equal): head
/// `td =~= basis_elt(0)` (`config_word(0,0)=[Gen0]`, `w_b(_,0)=ε`), tail
/// `family_II_rhs(αᵢ) == basis_elt(αᵢ)` (since `h_w_b = w_b(b_base…)` definitionally).
proof fn lemma_b_col_eq_basis_emb(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    ensures
        Seq::new(recog_data(mm, n, m, alphas).associations.len(),
                 |i: int| recog_data(mm, n, m, alphas).associations[i].1)
        =~= basis_emb(mm, n, m, betas(alphas)),
{
    let nk = g_m(mm).num_generators;
    let data = recog_data(mm, n, m, alphas);
    let pa = p_assoc(nk, n);
    let fa = family_II_assoc(mm, n, m, alphas);
    let bcol = Seq::new(data.associations.len(), |i: int| data.associations[i].1);
    let be = basis_emb(mm, n, m, betas(alphas));
    lemma_betas_index(alphas);
    lemma_config_word_zero();                          // config_word(0,0) =~= [Gen0]
    assert(data.associations =~= pa + fa);
    assert(pa.len() == 1);
    assert(data.associations.len() == 1 + alphas.len());
    // head: td =~= basis_elt(0)
    assert(w_c(b_base(nk, n), n, m, 0) =~= empty_word());     // α = 0 base case of w_c
    assert(h_w_b(nk, n, m, 0) =~= empty_word());              // = w_b(b_base,…,0) = w_c(…,0)
    assert(basis_elt(mm, n, m, 0) =~= td_word(nk, n));        // [Gen0] + ε + [d]  =~=  [Gen0, d]
    assert forall|j: int| 0 <= j < bcol.len() implies bcol[j] =~= be[j] by {
        if j == 0 {
            assert(data.associations[0] == pa[0]);
            assert(pa[0] == (seq![Symbol::Gen(0)], td_word(nk, n)));
            assert(bcol[0] == td_word(nk, n));
            assert(be[0] == basis_elt(mm, n, m, betas(alphas)[0]));
            assert(betas(alphas)[0] == 0);
        } else {
            let i = j - 1;
            assert(data.associations[j] == fa[i]);
            assert(fa[i] == (config_word(alphas[i], 0), family_II_rhs(mm, n, m, alphas[i])));
            assert(bcol[j] == family_II_rhs(mm, n, m, alphas[i]));
            // family_II_rhs(α) == basis_elt(α): both = config(α,0) + w_b(b_base,…,α) + [d].
            assert(h_w_b(nk, n, m, alphas[i]) == w_b(b_base(nk, n), n, m, alphas[i]));
            assert(family_II_rhs(mm, n, m, alphas[i]) =~= basis_elt(mm, n, m, alphas[i]));
            assert(be[j] == basis_elt(mm, n, m, betas(alphas)[j]));
            assert(betas(alphas)[j] == alphas[i]);
        }
    }
}

// ----------------------------------------------------------------------------
// A1 — the recognition-datum association isomorphism.
// ----------------------------------------------------------------------------

/// **A1 — `hnn_associations_isomorphic(recog_data)`.** The recognition datum's two columns are
/// `config_emb(betas)` and `basis_emb(betas)`, both ALREADY-PROVEN free families in `h1_base`
/// (`lemma_config_emb_free_in_h1` / `lemma_basis_elt_free`). So for any `w` over `|betas|` letters,
/// `apply_embedding(a_words, w) ≡ ε  ⟺  w ≡_free ε  ⟺  apply_embedding(b_words, w) ≡ ε` — the iff
/// transports through F3 (`lemma_free_to_basis_elt` / `lemma_free_to_embedding`) in each direction.
/// This is the `hnn_associations_isomorphic` precondition that Britton over `recog_data` consumes
/// (the "free-base fallacy": Britton needs only this iso, never a free base).
pub proof fn lemma_recog_associations_isomorphic(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
    ensures
        hnn_associations_isomorphic(recog_data(mm, n, m, alphas)),
{
    let data = recog_data(mm, n, m, alphas);
    let bb = betas(alphas);
    let k = data.associations.len();
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);

    lemma_betas_index(alphas);
    assert(k == bb.len());
    assert(data.base == h1_base(mm, n));
    lemma_h1_base_valid(mm, n);
    lemma_h1_base_num_generators(mm, n);               // base.num_generators == h1_num_gens(nk,n)

    // side conditions on betas
    lemma_betas_no_duplicates(alphas);
    lemma_betas_numbers_word(n, m, alphas);

    // columns ARE config_emb / basis_emb over betas
    lemma_a_col_eq_config_emb(mm, n, m, alphas);
    lemma_b_col_eq_basis_emb(mm, n, m, alphas);
    assert(a_words =~= config_emb(bb));
    assert(b_words =~= basis_emb(mm, n, m, bb));

    // config_emb words are valid over the base's generators (for F3 backward).
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);                      // nk ≥ 4
    assert forall|i: int| 0 <= i < config_emb(bb).len() implies
        word_valid(#[trigger] config_emb(bb)[i], data.base.num_generators) by {
        assert(config_emb(bb)[i] == config_word(bb[i], 0));
        lemma_config_word_valid(bb[i], 0);             // word_valid(·, 3)
        lemma_word_valid_mono(config_emb(bb)[i], 3, data.base.num_generators);
    }

    assert forall|w: Word| word_valid(w, k as nat) implies (
        equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word())
        <==>
        equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word())
    ) by {
        assert(word_valid(w, bb.len()));               // k == bb.len()
        if equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word()) {
            // a-side trivial ⟹ w free (config family free in h1) ⟹ b-side trivial (F3 on basis).
            lemma_config_emb_free_in_h1(mm, n, bb, w);
            lemma_free_to_basis_elt(mm, n, m, bb, w);
        }
        if equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word()) {
            // b-side trivial ⟹ w free (basis family free in h1) ⟹ a-side trivial (F3 on config).
            lemma_basis_elt_free(mm, n, m, bb, w);
            lemma_free_to_embedding(config_emb(bb), data.base, w);
        }
    }
}

// ----------------------------------------------------------------------------
// B4 — A1's payoff: Britton over `recog_data` applies to `h2_II`.
// ----------------------------------------------------------------------------

/// **`h1_base ↪ h2_II` is faithful** (the direct payoff of A1). A `h1_base`-word that is trivial in
/// `h2_II` is already trivial in `h1_base`. This is the "base embeds faithfully in the HNN" lemma
/// instantiated at `recog_data`: A1 (`lemma_recog_associations_isomorphic`) discharges the iso
/// precondition, `lemma_recog_data_valid` the validity, and `lemma_recog_presentation`
/// (`hnn_presentation(recog_data) == h2_II`) routes Britton's conclusion onto `h2_II`. The reusable
/// descent-to-base step that the C-forward Britton peel leans on.
pub proof fn lemma_h1_faithful_in_h2_II(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(w, h1_base(mm, n).num_generators),
        equiv_in_presentation(h2_II(mm, n, m, alphas), w, empty_word()),
    ensures
        equiv_in_presentation(h1_base(mm, n), w, empty_word()),
{
    let data = recog_data(mm, n, m, alphas);
    lemma_recog_data_valid(mm, n, m, alphas);                  // hnn_data_valid(data)
    lemma_recog_associations_isomorphic(mm, n, m, alphas);     // A1: hnn_associations_isomorphic(data)
    lemma_recog_presentation(mm, n, m, alphas);                // hnn_presentation(data) == h2_II
    assert(data.base == h1_base(mm, n));
    // word_valid(w, data.base.num_generators) and equiv_in(hnn_presentation(data)=h2_II, w, ε).
    lemma_single_hnn_base_faithful(data, w);
}

/// **`F = [t,x,b_1..b_n,d]` is free in `h2_II`.** Compose B3 (`lemma_f_free_in_h1`: `F` free in
/// `h1_base`) with the faithfulness `lemma_h1_faithful_in_h2_II`: the embedded product
/// `apply_embedding(f_h1_family, w)` is a `h1_base`-word, so its triviality in `h2_II` descends to
/// `h1_base`, where B3's free-family property closes it. (The Route-B von Dyck uses `F` free in
/// `h1_base` directly, but this lifted form makes `A = ⟨t,x,d,b_j,p⟩ = HNN(F, p | family II)` a
/// legitimate subgroup presentation of `h2_II`.)
pub proof fn lemma_f_free_in_h2_II(mm: ModMachine, n: nat, m: nat, alphas: Seq<nat>, w: Word)
    requires
        mod_machine_wf(mm),
        2 * n < m,
        !alphas.contains(0nat),
        alphas.no_duplicates(),
        forall|i: int| 0 <= i < alphas.len() ==> numbers_word(n, m, #[trigger] alphas[i]),
        word_valid(w, f_h1_family(mm, n).len()),
        equiv_in_presentation(h2_II(mm, n, m, alphas),
            apply_embedding(f_h1_family(mm, n), w), empty_word()),
    ensures
        equiv_in_presentation(free_group(f_h1_family(mm, n).len()), w, empty_word()),
{
    let fam = f_h1_family(mm, n);
    let base = h1_base(mm, n);
    let prod = apply_embedding(fam, w);
    lemma_f_free_in_h1(mm, n);                                 // is_free_family(base, fam)
    lemma_h1_base_num_generators(mm, n);                       // base.num_generators == h1_num_gens(nk,n)
    // each fam[i] is valid over base's generators (first conjunct of is_free_family).
    assert forall|i: int| 0 <= i < fam.len() implies
        word_valid(#[trigger] fam[i], base.num_generators) by { }
    // ⟹ the embedded product is a base word.
    lemma_apply_embedding_valid(fam, w, base.num_generators);
    // descend h2_II → h1_base.
    lemma_h1_faithful_in_h2_II(mm, n, m, alphas, prod);
    // is_free_family's implication: base-trivial product ⟹ w ≡_free ε.
    assert(equiv_in_presentation(free_group(fam.len()), w, empty_word()));
}

} // verus!
