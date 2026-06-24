// Layer 2 — Cohen §1, CS-5c RECOGNITION CORE (Route R1, the single-gen relabel).
//
// `docs/cohen-cs5-blueprint.md` §5. The forward `(★k)` `emb(a_col,w) ≡_{h2_pred} ε ⟹
// emb(b_col,w) ≡_{h2_pred} ε` is recognized over the CONCRETE machine base, NOT an abstract ⟨U⟩
// presentation, because `a_col`'s U-block is a single-generator relabel (`g_subgens(mm)[i] =
// [Gen(0)]`/`[Gen(3+i)]`, a SINGLE machine gen). This module builds the **relabel bridge** (step 1):
//
//   * `base_A_plus_base` = `Presentation{ num_generators: nk+n+1, relators: g_m.relators }`
//     (= `g_m ∗ free(d,b_j)` — g_m's relators only touch gens `0..nk-1`, so gens `nk..nk+n` are free).
//   * `a_col_machine` / `b_col_machine` — the machine-scheme columns (over `nk+n+2` gens incl. `p`),
//     the inclusion `a_col_machine` and the `b_j↦b_j c_j` von-Dyck image `b_col_machine`.
//   * `relabel_col` — the injective single-gen relabel psi-scheme → machine-scheme.
//   * the plain emb∘emb compose (`comp_emb` + `lemma_emb_emb_compose`),
//   * **the factoring** `a_col =~= comp_emb(a_col_machine, relabel_col)`,
//     `b_col =~= comp_emb(b_col_machine, relabel_col)`, giving the bridge identities
//     `emb(a_col,w) = emb(a_col_machine, relabel(w))`, `emb(b_col,w) = emb(b_col_machine, relabel(w))`.
//
// So psi-scheme `(★k)` forward reduces to the machine-scheme recognition (step 3) + von-Dyck (step 4).
// Additive/reversible; no regression.

use vstd::prelude::*;
use crate::word::*;
use crate::symbol::*;
use crate::presentation::Presentation;
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat,
    lemma_apply_embedding_inverse};
use crate::machine_group::{ModMachine, g_m, g_subgens, g_m_associations, lemma_g_m_num_generators,
    lemma_g_m_associations_valid};
use crate::layout::{h2_num_gens, d_idx, p_idx, b_idx, c_idx};
use crate::h3::{psi_assoc, psi_ublock, psi_bcblock};
use crate::cohen_cs5::{k_a_col, k_b_col};

verus! {

// ============================================================================
// Plain embedding compose: `emb(outer, emb(inner, w)) = emb(comp_emb(outer, inner), w)`.
// ============================================================================

/// The composite images `comp_emb(outer, inner)[i] = apply_embedding(outer, inner[i])` — the
/// outer embedding applied to each inner image (plain analog of `free_basis::comp_images`).
pub open spec fn comp_emb(outer: Seq<Word>, inner: Seq<Word>) -> Seq<Word> {
    Seq::new(inner.len(), |i: int| apply_embedding(outer, inner[i]))
}

/// **emb∘emb compose.** Applying `outer` to an `inner`-embedded word equals embedding by the
/// composite. Mirror of `lemma_apply_hom_pred_embedding_compose` with `apply_embedding` outer.
pub proof fn lemma_emb_emb_compose(outer: Seq<Word>, inner: Seq<Word>, w: Word)
    requires
        word_valid(w, inner.len()),
    ensures
        apply_embedding(outer, apply_embedding(inner, w)) =~= apply_embedding(comp_emb(outer, inner), w),
    decreases w.len(),
{
    let comp = comp_emb(outer, inner);
    assert(comp.len() == inner.len());
    if w.len() == 0 {
        assert(apply_embedding(inner, w) =~= empty_word());
        assert(apply_embedding(outer, empty_word()) =~= empty_word());
        assert(apply_embedding(comp, w) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, inner.len())) by { assert(w[0] == s); }
        assert(word_valid(rest, inner.len())) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(#[trigger] rest[k], inner.len()) by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_emb_emb_compose(outer, inner, rest);
        // outer(inner_sym(s)) = comp_sym(s).
        match s {
            Symbol::Gen(i) => {
                assert(i < inner.len());
                assert(apply_embedding_symbol(inner, s) == inner[i as int]);
                assert(comp[i as int] == apply_embedding(outer, inner[i as int]));
                assert(apply_embedding_symbol(comp, s) == comp[i as int]);
            },
            Symbol::Inv(i) => {
                assert(i < inner.len());
                assert(apply_embedding_symbol(inner, s) == inverse_word(inner[i as int]));
                lemma_apply_embedding_inverse(outer, inner[i as int]);
                assert(comp[i as int] == apply_embedding(outer, inner[i as int]));
                assert(apply_embedding_symbol(comp, s) == inverse_word(comp[i as int]));
            },
        }
        // emb(inner, w) = inner_sym(s) · emb(inner, rest); apply outer over the concat.
        assert(apply_embedding(inner, w)
            =~= concat(apply_embedding_symbol(inner, s), apply_embedding(inner, rest)));
        lemma_apply_embedding_concat(outer, apply_embedding_symbol(inner, s),
            apply_embedding(inner, rest));
        assert(apply_embedding(comp, w)
            =~= concat(apply_embedding_symbol(comp, s), apply_embedding(comp, rest)));
    }
}

// ============================================================================
// The machine-scheme objects (step 1 definitions).
// ============================================================================

/// `base_A₊` HNN base `= g_m ∗ free(d, b_j)`: `nk+n+1` gens (machine `0..nk-1`, b's `nk..nk+n-1`,
/// d at `nk+n`), relators = `g_m`'s (which only touch gens `0..nk-1`, so b/d are free).
pub open spec fn base_A_plus_base(mm: ModMachine, n: nat) -> Presentation {
    let nk = g_m(mm).num_generators;
    Presentation { num_generators: (nk + n + 1) as nat, relators: g_m(mm).relators }
}

/// The machine-scheme inclusion column `a_col_machine` (length `nk+n+2`, incl. the HNN letter `p`):
/// machine gen `i ↦ [Gen(i)]`, abstract `b_{j+1} ↦ [Gen(b_idx)]`, `d ↦ [Gen(d_idx)]`, `p ↦ [Gen(p_idx)]`.
pub open spec fn a_col_machine(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    Seq::new(nk, |i: int| seq![Symbol::Gen(i as nat)])
    + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))])
    + seq![ seq![Symbol::Gen(d_idx(nk, n))] ]
    + seq![ seq![Symbol::Gen(p_idx(nk, n))] ]
}

/// The machine-scheme von-Dyck image column `b_col_machine` (= `a_col_machine` with `b_{j+1} ↦
/// [Gen(b_idx), Gen(c_idx)]`).
pub open spec fn b_col_machine(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    Seq::new(nk, |i: int| seq![Symbol::Gen(i as nat)])
    + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)),
                                Symbol::Gen(c_idx(nk, (j + 1) as nat))])
    + seq![ seq![Symbol::Gen(d_idx(nk, n))] ]
    + seq![ seq![Symbol::Gen(p_idx(nk, n))] ]
}

/// The injective single-gen relabel, psi-scheme → machine-scheme (length `q+n+2 = psi_assoc.len()`):
/// U-gen `i ↦ g_subgens[i]` (a SINGLE machine gen `[Gen(gi)]`, `gi<nk`), `d ↦ [Gen(nk+n)]`,
/// `b_{j+1} ↦ [Gen(nk+j)]`, `p ↦ [Gen(nk+n+1)]`.
pub open spec fn relabel_col(mm: ModMachine, n: nat) -> Seq<Word> {
    let nk = g_m(mm).num_generators;
    Seq::new(g_subgens(mm).len(), |i: int| g_subgens(mm)[i])
    + seq![ seq![Symbol::Gen((nk + n) as nat)] ]
    + Seq::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)])
    + seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ]
}

/// `relabel(w)` — the machine-scheme word for a psi-scheme `w`.
pub open spec fn relabel(mm: ModMachine, n: nat, w: Word) -> Word {
    apply_embedding(relabel_col(mm, n), w)
}

// ============================================================================
// The factoring (step 1) — `a_col = comp_emb(a_col_machine, relabel_col)` entry-wise.
// ============================================================================

/// `a_col_machine` / `b_col_machine` have length `nk+n+2`; `relabel_col` entries are valid over it.
proof fn lemma_machine_col_len(mm: ModMachine, n: nat)
    ensures
        a_col_machine(mm, n).len() == g_m(mm).num_generators + n + 2,
        b_col_machine(mm, n).len() == g_m(mm).num_generators + n + 2,
        relabel_col(mm, n).len() == psi_assoc(mm, n).len(),
        relabel_col(mm, n).len() == g_subgens(mm).len() + n + 2,
{
    let nk = g_m(mm).num_generators;
    assert(a_col_machine(mm, n).len() == nk + n + 2);
    assert(b_col_machine(mm, n).len() == nk + n + 2);
    assert(relabel_col(mm, n).len() == g_subgens(mm).len() + n + 2);
    assert(psi_assoc(mm, n).len() == g_subgens(mm).len() + n + 2) by {
        assert(psi_ublock(mm).len() == g_subgens(mm).len());
        assert(psi_bcblock(nk, n).len() == n);
    }
}

/// **The a-factoring, entry-wise.** `comp_emb(a_col_machine, relabel_col)[i] = k_a_col[i]` for each
/// psi-index `i`: U-block `apply_embedding(a_col_machine, g_subgens[i]) = a_col_machine[gi] =
/// [Gen(gi)] = g_subgens[i]`; d/b/p blocks pick the single machine-scheme image.
proof fn lemma_a_factor_entry(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < psi_assoc(mm, n).len(),
    ensures
        apply_embedding(a_col_machine(mm, n), relabel_col(mm, n)[i]) =~= k_a_col(mm, n)[i],
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let am = a_col_machine(mm, n);
    let rc = relabel_col(mm, n);
    let q = g_subgens(mm).len();
    lemma_machine_col_len(mm, n);
    assert(am.len() == nk + n + 2);

    // psi_assoc block decomposition (mirror lemma_s_strip_psi_entry).
    let up = psi_ublock(mm);
    let dpair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))])];
    let bc = psi_bcblock(nk, n);
    let ppair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))])];
    assert(up.len() == q);
    assert(bc.len() == n);
    assert(psi_assoc(mm, n) =~= ((up + dpair) + bc) + ppair);
    assert(k_a_col(mm, n)[i] == psi_assoc(mm, n)[i].0);

    // relabel_col block decomposition.
    let r_d: Seq<Word> = seq![ seq![Symbol::Gen((nk + n) as nat)] ];
    let r_b: Seq<Word> = Seq::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)]);
    let r_p: Seq<Word> = seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ];
    let r_u: Seq<Word> = Seq::new(q, |i2: int| g_subgens(mm)[i2]);
    assert(rc =~= ((r_u + r_d) + r_b) + r_p);

    if i < q {
        // U-block: rc[i] = g_subgens[i] = [Gen(gi)], gi < nk; am[gi] = [Gen(gi)].
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_u[i]);
        assert(r_u[i] == g_subgens(mm)[i]);
        let u = g_subgens(mm)[i];
        lemma_g_m_associations_valid(mm);
        assert(u == g_m_associations(mm)[i].1);
        assert(word_valid(u, (3 + mm.quads.len()) as nat));
        // g_subgens[i] is a single gen [Gen(gi)] with gi < nk.
        assert(u.len() == 1) by { assert(word_valid(u, (3 + mm.quads.len()) as nat)); }
        let gi = generator_index(u[0]);
        assert(symbol_valid(u[0], (3 + mm.quads.len()) as nat));
        assert(gi < 3 + mm.quads.len());
        assert(gi < nk);
        assert(u[0] == Symbol::Gen(gi)) by { assert(symbol_valid(u[0], nk)); }
        assert(u =~= seq![Symbol::Gen(gi)]);
        // apply_embedding(am, [Gen(gi)]) = am[gi] = [Gen(gi)].
        assert(am[gi as int] == seq![Symbol::Gen(gi)]) by {
            assert(((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]))
                + seq![ seq![Symbol::Gen(d_idx(nk, n))] ])[gi as int]
                == Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])[gi as int]);
        }
        lemma_emb_single_gen(am, gi);
        assert(apply_embedding(am, u) =~= am[gi as int]);
        assert(k_a_col(mm, n)[i] == g_subgens(mm)[i]);
    } else if i == q {
        // d: rc[q] = [Gen(nk+n)]; am[nk+n] = [Gen(d_idx)].
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_d[i - q]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + n) as nat)]);
        assert(am[(nk + n) as int] == seq![Symbol::Gen(d_idx(nk, n))]);
        lemma_emb_single_gen(am, (nk + n) as nat);
        assert(psi_assoc(mm, n)[i] == dpair[i - q]);
        assert(k_a_col(mm, n)[i] =~= seq![Symbol::Gen(d_idx(nk, n))]);
    } else if i < q + 1 + n {
        // b-block: rc[i] = [Gen(nk + (i-q-1))]; am[nk+(i-q-1)] = [Gen(b_idx(.., i-q))].
        let j = (i - q - 1) as int;     // 0 ≤ j < n
        assert(((r_u + r_d) + r_b)[i] == r_b[j]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + j) as nat)]);
        assert(am[(nk + j) as int] == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]) by {
            assert((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))]))[(nk + j) as int]
                == Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat))])[j]);
        }
        lemma_emb_single_gen(am, (nk + j) as nat);
        // k_a_col[i] = psi_bcblock[i-q-1].0 = [Gen(b_idx(.., j+1))].
        assert(psi_assoc(mm, n)[i] == bc[j]);
        assert(bc[j].0 =~= seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat))]);
    } else {
        // p: i == q+1+n; rc[i] = [Gen(nk+n+1)]; am[nk+n+1] = [Gen(p_idx)].
        assert(i == ((r_u + r_d) + r_b).len());
        assert(rc[i] =~= seq![Symbol::Gen((nk + n + 1) as nat)]);
        assert(am[(nk + n + 1) as int] == seq![Symbol::Gen(p_idx(nk, n))]);
        lemma_emb_single_gen(am, (nk + n + 1) as nat);
        assert(psi_assoc(mm, n)[i] == ppair[0]);
        assert(k_a_col(mm, n)[i] =~= seq![Symbol::Gen(p_idx(nk, n))]);
    }
}

/// `apply_embedding(images, [Gen(g)]) = images[g]` (single positive generator).
proof fn lemma_emb_single_gen(images: Seq<Word>, g: nat)
    ensures
        apply_embedding(images, seq![Symbol::Gen(g)]) =~= images[g as int],
{
    let w: Word = seq![Symbol::Gen(g)];
    assert(w.len() == 1);
    assert(w.first() == Symbol::Gen(g));
    assert(w.drop_first() =~= empty_word());
    assert(apply_embedding(images, w.drop_first()) =~= empty_word());
    assert(apply_embedding_symbol(images, w.first()) == images[g as int]);
    assert(apply_embedding(images, w)
        =~= concat(apply_embedding_symbol(images, w.first()), empty_word()));
    lemma_concat_empty_right(images[g as int]);
}

/// **The b-factoring, entry-wise** (mirror of `lemma_a_factor_entry`; the bc-block image is
/// `[Gen(b_idx), Gen(c_idx)]` instead of `[Gen(b_idx)]`; U/d/p identical to the a-side).
proof fn lemma_b_factor_entry(mm: ModMachine, n: nat, i: int)
    requires
        0 <= i < psi_assoc(mm, n).len(),
    ensures
        apply_embedding(b_col_machine(mm, n), relabel_col(mm, n)[i]) =~= k_b_col(mm, n)[i],
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let bm = b_col_machine(mm, n);
    let rc = relabel_col(mm, n);
    let q = g_subgens(mm).len();
    lemma_machine_col_len(mm, n);
    assert(bm.len() == nk + n + 2);

    let up = psi_ublock(mm);
    let dpair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))])];
    let bc = psi_bcblock(nk, n);
    let ppair: Seq<(Word, Word)> =
        seq![(seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))])];
    assert(up.len() == q);
    assert(bc.len() == n);
    assert(psi_assoc(mm, n) =~= ((up + dpair) + bc) + ppair);
    assert(k_b_col(mm, n)[i] == psi_assoc(mm, n)[i].1);

    let r_d: Seq<Word> = seq![ seq![Symbol::Gen((nk + n) as nat)] ];
    let r_b: Seq<Word> = Seq::new(n, |j: int| seq![Symbol::Gen((nk + j) as nat)]);
    let r_p: Seq<Word> = seq![ seq![Symbol::Gen((nk + n + 1) as nat)] ];
    let r_u: Seq<Word> = Seq::new(q, |i2: int| g_subgens(mm)[i2]);
    assert(rc =~= ((r_u + r_d) + r_b) + r_p);

    if i < q {
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_u[i]);
        assert(r_u[i] == g_subgens(mm)[i]);
        let u = g_subgens(mm)[i];
        lemma_g_m_associations_valid(mm);
        assert(u == g_m_associations(mm)[i].1);
        assert(word_valid(u, (3 + mm.quads.len()) as nat));
        assert(u.len() == 1) by { assert(word_valid(u, (3 + mm.quads.len()) as nat)); }
        let gi = generator_index(u[0]);
        assert(symbol_valid(u[0], (3 + mm.quads.len()) as nat));
        assert(gi < 3 + mm.quads.len());
        assert(gi < nk);
        assert(u[0] == Symbol::Gen(gi)) by { assert(symbol_valid(u[0], nk)); }
        assert(u =~= seq![Symbol::Gen(gi)]);
        assert(bm[gi as int] == seq![Symbol::Gen(gi)]) by {
            assert(((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |j: int| seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)),
                                            Symbol::Gen(c_idx(nk, (j + 1) as nat))]))
                + seq![ seq![Symbol::Gen(d_idx(nk, n))] ])[gi as int]
                == Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])[gi as int]);
        }
        lemma_emb_single_gen(bm, gi);
        assert(apply_embedding(bm, u) =~= bm[gi as int]);
        assert(k_b_col(mm, n)[i] == g_subgens(mm)[i]);
    } else if i == q {
        assert(((r_u + r_d) + r_b)[i] == (r_u + r_d)[i]);
        assert((r_u + r_d)[i] == r_d[i - q]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + n) as nat)]);
        assert(bm[(nk + n) as int] == seq![Symbol::Gen(d_idx(nk, n))]);
        lemma_emb_single_gen(bm, (nk + n) as nat);
        assert(psi_assoc(mm, n)[i] == dpair[i - q]);
        assert(k_b_col(mm, n)[i] =~= seq![Symbol::Gen(d_idx(nk, n))]);
    } else if i < q + 1 + n {
        let j = (i - q - 1) as int;
        assert(((r_u + r_d) + r_b)[i] == r_b[j]);
        assert(rc[i] =~= seq![Symbol::Gen((nk + j) as nat)]);
        assert(bm[(nk + j) as int]
            == seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)), Symbol::Gen(c_idx(nk, (j + 1) as nat))])
        by {
            assert((Seq::new(nk, |i2: int| seq![Symbol::Gen(i2 as nat)])
                + Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat)),
                                             Symbol::Gen(c_idx(nk, (jj + 1) as nat))]))[(nk + j) as int]
                == Seq::new(n, |jj: int| seq![Symbol::Gen(b_idx(nk, n, (jj + 1) as nat)),
                                              Symbol::Gen(c_idx(nk, (jj + 1) as nat))])[j]);
        }
        lemma_emb_single_gen(bm, (nk + j) as nat);
        assert(psi_assoc(mm, n)[i] == bc[j]);
        assert(bc[j].1 =~= seq![Symbol::Gen(b_idx(nk, n, (j + 1) as nat)),
                                Symbol::Gen(c_idx(nk, (j + 1) as nat))]);
    } else {
        assert(i == ((r_u + r_d) + r_b).len());
        assert(rc[i] =~= seq![Symbol::Gen((nk + n + 1) as nat)]);
        assert(bm[(nk + n + 1) as int] == seq![Symbol::Gen(p_idx(nk, n))]);
        lemma_emb_single_gen(bm, (nk + n + 1) as nat);
        assert(psi_assoc(mm, n)[i] == ppair[0]);
        assert(k_b_col(mm, n)[i] =~= seq![Symbol::Gen(p_idx(nk, n))]);
    }
}

// ============================================================================
// Full factoring + the bridge identities (step 1 output).
// ============================================================================

/// `k_a_col = comp_emb(a_col_machine, relabel_col)` (Seq equality, from the per-entry lemma).
pub proof fn lemma_a_col_factors(mm: ModMachine, n: nat)
    ensures
        k_a_col(mm, n) =~= comp_emb(a_col_machine(mm, n), relabel_col(mm, n)),
{
    let comp = comp_emb(a_col_machine(mm, n), relabel_col(mm, n));
    lemma_machine_col_len(mm, n);
    assert(comp.len() == k_a_col(mm, n).len());
    assert forall|i: int| 0 <= i < comp.len() implies comp[i] =~= k_a_col(mm, n)[i] by {
        assert(comp[i] == apply_embedding(a_col_machine(mm, n), relabel_col(mm, n)[i]));
        lemma_a_factor_entry(mm, n, i);
    }
}

/// `k_b_col = comp_emb(b_col_machine, relabel_col)`.
pub proof fn lemma_b_col_factors(mm: ModMachine, n: nat)
    ensures
        k_b_col(mm, n) =~= comp_emb(b_col_machine(mm, n), relabel_col(mm, n)),
{
    let comp = comp_emb(b_col_machine(mm, n), relabel_col(mm, n));
    lemma_machine_col_len(mm, n);
    assert(comp.len() == k_b_col(mm, n).len());
    assert forall|i: int| 0 <= i < comp.len() implies comp[i] =~= k_b_col(mm, n)[i] by {
        assert(comp[i] == apply_embedding(b_col_machine(mm, n), relabel_col(mm, n)[i]));
        lemma_b_factor_entry(mm, n, i);
    }
}

/// **The a-bridge:** `emb(k_a_col, w) = emb(a_col_machine, relabel(w))`. So a psi-scheme `a_col`
/// embedding equals the machine-scheme `a_col_machine` embedding of the relabeled word.
pub proof fn lemma_emb_a_col_via_relabel(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, psi_assoc(mm, n).len()),
    ensures
        apply_embedding(k_a_col(mm, n), w)
            =~= apply_embedding(a_col_machine(mm, n), relabel(mm, n, w)),
{
    lemma_machine_col_len(mm, n);
    assert(word_valid(w, relabel_col(mm, n).len()));
    lemma_emb_emb_compose(a_col_machine(mm, n), relabel_col(mm, n), w);
    lemma_a_col_factors(mm, n);
    // emb(k_a_col, w) = emb(comp_emb(am, rc), w) = emb(am, emb(rc, w)) = emb(am, relabel(w)).
    assert(apply_embedding(k_a_col(mm, n), w)
        =~= apply_embedding(comp_emb(a_col_machine(mm, n), relabel_col(mm, n)), w));
}

/// **The b-bridge:** `emb(k_b_col, w) = emb(b_col_machine, relabel(w))`.
pub proof fn lemma_emb_b_col_via_relabel(mm: ModMachine, n: nat, w: Word)
    requires
        word_valid(w, psi_assoc(mm, n).len()),
    ensures
        apply_embedding(k_b_col(mm, n), w)
            =~= apply_embedding(b_col_machine(mm, n), relabel(mm, n, w)),
{
    lemma_machine_col_len(mm, n);
    assert(word_valid(w, relabel_col(mm, n).len()));
    lemma_emb_emb_compose(b_col_machine(mm, n), relabel_col(mm, n), w);
    lemma_b_col_factors(mm, n);
    assert(apply_embedding(k_b_col(mm, n), w)
        =~= apply_embedding(comp_emb(b_col_machine(mm, n), relabel_col(mm, n)), w));
}

} // verus!
