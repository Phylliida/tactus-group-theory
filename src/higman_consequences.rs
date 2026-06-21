// Layer 2 — Brick 5 (`higman_consequences.rs`): the Higman payoff.
//
// The BRIDGE THEOREM (soundness direction this session):
//
//     (α,0) ∈ H₀(M)   ⟹   h3_pres(mm,n,m) ⊢ w_α(c) = 1.
//
// This is Cohen's "(II),(III) are consequences of the finite set (I)" (book p.281): the
// recursively-presented relations of `C = ⟨c;S⟩` hold in the FINITE presentation `h3_pres` as
// derived theorems. Combined with Layer 1 (`lemma_theorem1`) it realizes the c.e. set
// `S = { w_α(c) : (α,0)∈H₀(M) }` as the word problem of `H₃` among the c-generators.
//
// See `docs/brick5-plan.md` for the full decomposition and the (deferred) completeness routing.
//
// Sub-brick 0 (this file, first): the LIFTING HELPERS. Every relation we use lives at some tower
// level (`h2_pres`, `h3_upto(l)`); we lift it up to `h3_pres` via repeated `lemma_base_embeds_in_hnn`
// (an HNN base embeds in its extension — no validity / iso hypothesis needed).

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::machine_group::*;
use crate::word_numbering::*;
use crate::layout::*;
use crate::benign::{apply_embedding, lemma_apply_embedding_concat};
use crate::prop_v::lemma_emb_signed_scaled;
use crate::h1::*;
use crate::h2::*;
use crate::h3::*;

verus! {

// ----------------------------------------------------------------------------
// Generic commutation algebra.  `commutes(p, a, b)` := `a·b ≡ b·a` in `p`.
// Reused in the `w_bc` split (b-letters past c-words) and in (II) (p past w_α(a)).
// ----------------------------------------------------------------------------

/// `a` and `b` commute in presentation `p`.
pub open spec fn commutes(p: Presentation, a: Word, b: Word) -> bool {
    equiv_in_presentation(p, a + b, b + a)
}

/// Everything commutes with the empty word.
pub proof fn lemma_commutes_empty_right(p: Presentation, a: Word)
    ensures commutes(p, a, empty_word()),
{
    assert(a + empty_word() =~= a);
    assert(empty_word() + a =~= a);
    lemma_equiv_refl(p, a);
}

/// Commutation is symmetric (needs validity of `a·b` for the symmetry of `≡`).
pub proof fn lemma_commutes_sym(p: Presentation, a: Word, b: Word)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        commutes(p, a, b),
    ensures commutes(p, b, a),
{
    lemma_concat_word_valid(a, b, p.num_generators);
    lemma_equiv_symmetric(p, a + b, b + a);
}

/// `a` commutes with `b₁` and `b₂` ⟹ `a` commutes with `b₁·b₂`.
pub proof fn lemma_commutes_concat_right(p: Presentation, a: Word, b1: Word, b2: Word)
    requires
        commutes(p, a, b1),
        commutes(p, a, b2),
    ensures commutes(p, a, b1 + b2),
{
    // a·(b1·b2) = (a·b1)·b2 ≡ (b1·a)·b2 = b1·(a·b2) ≡ b1·(b2·a) = (b1·b2)·a.
    lemma_equiv_concat_left(p, a + b1, b1 + a, b2);     // (a·b1)·b2 ≡ (b1·a)·b2
    assert(concat(a + b1, b2) =~= a + (b1 + b2));
    assert(concat(b1 + a, b2) =~= b1 + (a + b2));
    lemma_equiv_concat_right(p, b1, a + b2, b2 + a);     // b1·(a·b2) ≡ b1·(b2·a)
    assert(concat(b1, a + b2) =~= b1 + (a + b2));
    assert(concat(b1, b2 + a) =~= (b1 + b2) + a);
    lemma_equiv_transitive(p, a + (b1 + b2), b1 + (a + b2), (b1 + b2) + a);
    assert(a + (b1 + b2) =~= a + (b1 + b2));
}

/// If `a` commutes with `b`, it commutes with `b⁻¹` (valid `a`,`b`; conjugate-and-cancel).
pub proof fn lemma_commutes_inv_right(p: Presentation, a: Word, b: Word)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        commutes(p, a, b),
    ensures commutes(p, a, inverse_word(b)),
{
    let ng = p.num_generators;
    let bi = inverse_word(b);
    lemma_inverse_word_valid(b, ng);
    // From a·b ≡ b·a, sandwich by b⁻¹ on both sides:  b⁻¹·(a·b)·b⁻¹ ≡ b⁻¹·(b·a)·b⁻¹.
    lemma_equiv_concat_left(p, a + b, b + a, bi);          // (a·b)·b⁻¹ ≡ (b·a)·b⁻¹
    lemma_equiv_concat_right(p, bi, (a + b) + bi, (b + a) + bi);  // E2: lhs ≡ rhs
    let lhs = bi + ((a + b) + bi);
    let rhs = bi + ((b + a) + bi);
    assert(equiv_in_presentation(p, lhs, rhs));

    // LHS = b⁻¹·a·(b·b⁻¹) ≡ b⁻¹·a  (b·b⁻¹ ≡ ε).
    lemma_word_inverse_right(p, b);                        // b·b⁻¹ ≡ ε
    lemma_equiv_concat_right(p, bi + a, b + bi, empty_word());  // (b⁻¹a)(b b⁻¹) ≡ (b⁻¹a)·ε
    assert(lhs =~= (bi + a) + (b + bi));
    assert((bi + a) + empty_word() =~= bi + a);
    assert(equiv_in_presentation(p, lhs, bi + a));         // E3 (terms collapsed by the =~= above)

    // RHS = (b⁻¹·b)·a·b⁻¹ ≡ a·b⁻¹  (b⁻¹·b ≡ ε).
    lemma_word_inverse_left(p, b);                         // b⁻¹·b ≡ ε
    lemma_equiv_concat_left(p, bi + b, empty_word(), a + bi);   // (b⁻¹b)(a b⁻¹) ≡ ε·(a b⁻¹)
    assert(rhs =~= (bi + b) + (a + bi));
    assert(empty_word() + (a + bi) =~= a + bi);
    assert(equiv_in_presentation(p, rhs, a + bi));         // E4

    // chain:  b⁻¹·a ≡ lhs ≡ rhs ≡ a·b⁻¹, then symmetry gives a·b⁻¹ ≡ b⁻¹·a.
    lemma_concat_word_valid(bi, a, ng);
    lemma_equiv_symmetric(p, lhs, bi + a);                 // b⁻¹·a ≡ lhs
    lemma_equiv_transitive(p, bi + a, lhs, rhs);           // b⁻¹·a ≡ rhs
    lemma_equiv_transitive(p, bi + a, rhs, a + bi);        // b⁻¹·a ≡ a·b⁻¹
    lemma_equiv_symmetric(p, bi + a, a + bi);              // a·b⁻¹ ≡ b⁻¹·a  = commutes(a, b⁻¹)
}

// ----------------------------------------------------------------------------
// Sub-brick 1 — the `w_bc` split:  h1_base ⊢ w_α(bc) ≡ w_α(b)·w_α(c).
// The c-generators commute with the b-generators (commutator relators of set (I)),
// so the interleaved `w_α(bc)` collapses to the b-word times the c-word.
// ----------------------------------------------------------------------------

/// From a Gen–Gen commutation derive all four sign combinations.
pub proof fn lemma_gen_commute_to_combos(p: Presentation, b_g: nat, c_g: nat)
    requires
        presentation_valid(p),
        b_g < p.num_generators,
        c_g < p.num_generators,
        commutes(p, seq![Symbol::Gen(b_g)], seq![Symbol::Gen(c_g)]),
    ensures
        commutes(p, seq![Symbol::Gen(b_g)], seq![Symbol::Gen(c_g)]),
        commutes(p, seq![Symbol::Gen(b_g)], seq![Symbol::Inv(c_g)]),
        commutes(p, seq![Symbol::Inv(b_g)], seq![Symbol::Gen(c_g)]),
        commutes(p, seq![Symbol::Inv(b_g)], seq![Symbol::Inv(c_g)]),
{
    let ng = p.num_generators;
    let gB: Word = seq![Symbol::Gen(b_g)];
    let gC: Word = seq![Symbol::Gen(c_g)];
    let iB: Word = seq![Symbol::Inv(b_g)];
    let iC: Word = seq![Symbol::Inv(c_g)];
    // validities
    assert(word_valid(gB, ng)) by { assert(gB[0] == Symbol::Gen(b_g)); }
    assert(word_valid(gC, ng)) by { assert(gC[0] == Symbol::Gen(c_g)); }
    assert(word_valid(iB, ng)) by { assert(iB[0] == Symbol::Inv(b_g)); }
    assert(word_valid(iC, ng)) by { assert(iC[0] == Symbol::Inv(c_g)); }
    // inverse_word(gC) =~= iC, inverse_word(gB) =~= iB
    lemma_inverse_singleton(Symbol::Gen(c_g));
    assert(gC =~= Seq::new(1, |_i: int| Symbol::Gen(c_g)));
    assert(Seq::new(1, |_i: int| inverse_symbol(Symbol::Gen(c_g))) =~= iC);
    assert(inverse_word(gC) =~= iC);
    lemma_inverse_singleton(Symbol::Gen(b_g));
    assert(gB =~= Seq::new(1, |_i: int| Symbol::Gen(b_g)));
    assert(Seq::new(1, |_i: int| inverse_symbol(Symbol::Gen(b_g))) =~= iB);
    assert(inverse_word(gB) =~= iB);

    // (GenB, InvC)
    lemma_commutes_inv_right(p, gB, gC);                  // commutes(gB, iC)
    // (InvB, GenC)
    lemma_commutes_sym(p, gB, gC);                        // commutes(gC, gB)
    lemma_commutes_inv_right(p, gC, gB);                  // commutes(gC, iB)
    lemma_commutes_sym(p, gC, iB);                        // commutes(iB, gC)
    // (InvB, InvC)  — from commutes(gB, iC)
    lemma_commutes_sym(p, gB, iC);                        // commutes(iC, gB)
    lemma_commutes_inv_right(p, iC, gB);                  // commutes(iC, iB)
    lemma_commutes_sym(p, iC, iB);                        // commutes(iB, iC)
}

/// The commutator `b_i c_j b_i⁻¹ c_j⁻¹` is a relator of `h1_base`, hence `≡ ε`.
pub proof fn lemma_h1_comm_relator_identity(mm: ModMachine, n: nat, i: nat, j: nat)
    requires 1 <= i <= n, 1 <= j <= n,
    ensures
        equiv_in_presentation(h1_base(mm, n),
            comm_relator(g_m(mm).num_generators, n, i, j), empty_word()),
{
    let nk = g_m(mm).num_generators;
    let grels = g_m(mm).relators;
    let idx: int = (i - 1) * (n as int) + (j - 1);
    // 0 ≤ idx < n²
    assert(0 <= idx) by { assert((i - 1) >= 0 && (j - 1) >= 0); }
    assert(idx < n * n) by {
        assert((i - 1) <= (n - 1));
        assert((i - 1) * (n as int) <= (n - 1) * (n as int)) by (nonlinear_arith)
            requires 0 <= (i - 1) <= (n - 1), n >= 1;
        assert((n - 1) * (n as int) + (j - 1) < n * n) by (nonlinear_arith)
            requires (j - 1) < n, n >= 1;
    }
    // idx / n = i-1, idx % n = j-1
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        idx, n as int, (i - 1) as int, (j - 1) as int);
    assert(idx / (n as int) == (i - 1));
    assert(idx % (n as int) == (j - 1));
    let crels = comm_relators(nk, n);
    assert(crels[idx] == comm_relator(nk, n, (idx / (n as int) + 1) as nat, (idx % (n as int) + 1) as nat));
    assert(crels[idx] == comm_relator(nk, n, i, j));
    // locate in h1_base.relators = grels + crels
    let p = h1_base(mm, n);
    assert(p.relators =~= grels + crels);
    let ri = grels.len() + idx;
    assert(0 <= ri < p.relators.len());
    assert(p.relators[ri] == crels[idx]);
    lemma_relator_is_identity(p, ri);
}

/// `b_i` and `c_j` commute in `h1_base` (1 ≤ i,j ≤ n): from `b_i c_j b_i⁻¹ c_j⁻¹ ≡ ε`.
pub proof fn lemma_bc_gen_commute(mm: ModMachine, n: nat, i: nat, j: nat)
    requires 1 <= i <= n, 1 <= j <= n,
    ensures
        commutes(h1_base(mm, n),
            seq![Symbol::Gen(b_idx(g_m(mm).num_generators, n, i))],
            seq![Symbol::Gen(c_idx(g_m(mm).num_generators, j))]),
{
    let nk = g_m(mm).num_generators;
    let p = h1_base(mm, n);
    let ng = h1_num_gens(nk, n);
    lemma_h1_base_valid(mm, n);
    let bb = b_idx(nk, n, i);
    let cc = c_idx(nk, j);
    let gB: Word = seq![Symbol::Gen(bb)];
    let gC: Word = seq![Symbol::Gen(cc)];
    let x: Word = gB + gC;            // u  = b_i c_j
    let y: Word = gC + gB;            // v  = c_j b_i
    let yi = inverse_word(y);
    // index bounds and validities
    assert(bb < ng && cc < ng);
    assert(word_valid(gB, ng)) by { assert(gB[0] == Symbol::Gen(bb)); }
    assert(word_valid(gC, ng)) by { assert(gC[0] == Symbol::Gen(cc)); }
    lemma_concat_word_valid(gB, gC, ng);
    lemma_concat_word_valid(gC, gB, ng);
    // inverse_word(y) = inverse_word(gC·gB) = inverse_word(gB)·inverse_word(gC) = [Inv bb, Inv cc]
    lemma_inverse_singleton(Symbol::Gen(bb));
    lemma_inverse_singleton(Symbol::Gen(cc));
    assert(gB =~= Seq::new(1, |_i: int| Symbol::Gen(bb)));
    assert(gC =~= Seq::new(1, |_i: int| Symbol::Gen(cc)));
    assert(inverse_word(gB) =~= seq![Symbol::Inv(bb)]);
    assert(inverse_word(gC) =~= seq![Symbol::Inv(cc)]);
    lemma_inverse_concat(gC, gB);                         // (gC·gB)⁻¹ = gB⁻¹·gC⁻¹
    assert(concat(gC, gB) =~= y);
    assert(yi =~= seq![Symbol::Inv(bb), Symbol::Inv(cc)]);
    // the relator  r = b_i c_j b_i⁻¹ c_j⁻¹  =  x + yi
    let r = comm_relator(nk, n, i, j);
    assert(r =~= x + yi) by {
        assert(r == seq![Symbol::Gen(bb), Symbol::Gen(cc), Symbol::Inv(bb), Symbol::Inv(cc)]);
    }
    lemma_h1_comm_relator_identity(mm, n, i, j);          // r ≡ ε
    // r·y ≡ ε·y = y ; r·y = x·(yi·y) ≡ x·ε = x  ⟹  x ≡ y.
    lemma_equiv_concat_left(p, r, empty_word(), y);       // r·y ≡ ε·y
    assert(empty_word() + y =~= y);
    assert(equiv_in_presentation(p, r + y, y));           // r·y ≡ y
    lemma_word_inverse_left(p, y);                        // yi·y ≡ ε
    lemma_equiv_concat_right(p, x, yi + y, empty_word()); // x·(yi·y) ≡ x·ε
    assert((r + y) =~= x + (yi + y));
    assert(x + empty_word() =~= x);
    assert(equiv_in_presentation(p, r + y, x));           // r·y ≡ x
    // x ≡ r·y ≡ y  (need word_valid(r·y) for the symmetry)
    lemma_comm_relator_valid(nk, n, i, j, ng);            // word_valid(r, ng)
    lemma_concat_word_valid(r, y, ng);
    lemma_equiv_symmetric(p, r + y, x);                   // x ≡ r·y
    lemma_equiv_transitive(p, x, r + y, y);               // x ≡ y  = commutes(gB, gC)
}

/// A b-letter `alphabet_letter(b_base,n,d)` commutes with any single c-block symbol `s`
/// (generator index in `[c_base, c_base+n)`).
pub proof fn lemma_b_alpha_commutes_c_symbol(mm: ModMachine, n: nat, d: nat, s: Symbol)
    requires
        1 <= d <= 2 * n,
        c_base(g_m(mm).num_generators) <= generator_index(s) < c_base(g_m(mm).num_generators) + n,
    ensures
        commutes(h1_base(mm, n), seq![alphabet_letter(b_base(g_m(mm).num_generators, n), n, d)], seq![s]),
{
    let nk = g_m(mm).num_generators;
    let p = h1_base(mm, n);
    let ng = h1_num_gens(nk, n);
    lemma_h1_base_valid(mm, n);
    let ep = generator_index(s);                 // ∈ [nk, nk+n)
    let j = (ep - nk + 1) as nat;                // ∈ [1, n]
    assert(1 <= j <= n);
    assert(c_idx(nk, j) == ep);                  // nk + (j-1) = ep
    let i = if d <= n { d } else { (d - n) as nat };
    assert(1 <= i <= n);
    let bb = b_idx(nk, n, i);
    assert(bb < ng);                             // nk+n+i-1 ≤ nk+2n-1 < nk+2n+1
    assert(ep < ng);                             // ep < nk+n < ng
    lemma_bc_gen_commute(mm, n, i, j);           // commutes([Gen bb], [Gen ep])
    lemma_gen_commute_to_combos(p, bb, ep);      // all four sign combos
    let bl = alphabet_letter(b_base(nk, n), n, d);
    if d <= n {
        assert(bl == Symbol::Gen(bb));
    } else {
        assert(bl == Symbol::Inv(bb));
    }
    match s {
        Symbol::Gen(g) => { assert(g == ep); assert(seq![s] == seq![Symbol::Gen(ep)]); },
        Symbol::Inv(g) => { assert(g == ep); assert(seq![s] == seq![Symbol::Inv(ep)]); },
    }
    assert(seq![bl] == (if d <= n { seq![Symbol::Gen(bb)] } else { seq![Symbol::Inv(bb)] }));
}

/// A b-letter commutes with any word whose symbols all live in the c-block.
pub proof fn lemma_b_alpha_commutes_c_word(mm: ModMachine, n: nat, d: nat, w: Word)
    requires
        1 <= d <= 2 * n,
        forall|k: int| 0 <= k < w.len() ==>
            c_base(g_m(mm).num_generators) <= generator_index(#[trigger] w[k])
                < c_base(g_m(mm).num_generators) + n,
    ensures
        commutes(h1_base(mm, n), seq![alphabet_letter(b_base(g_m(mm).num_generators, n), n, d)], w),
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let p = h1_base(mm, n);
    let bl_w: Word = seq![alphabet_letter(b_base(nk, n), n, d)];
    if w.len() == 0 {
        lemma_commutes_empty_right(p, bl_w);
        assert(w =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(c_base(nk) <= generator_index(s) < c_base(nk) + n) by { assert(w[0] == s); }
        lemma_b_alpha_commutes_c_symbol(mm, n, d, s);     // commutes(bl_w, [s])
        assert forall|k: int| 0 <= k < rest.len() implies
            c_base(nk) <= generator_index(#[trigger] rest[k]) < c_base(nk) + n by {
            assert(rest[k] == w[k + 1]);
        }
        lemma_b_alpha_commutes_c_word(mm, n, d, rest);    // commutes(bl_w, rest)
        lemma_commutes_concat_right(p, bl_w, seq![s], rest);  // commutes(bl_w, [s]+rest)
        assert(seq![s] + rest =~= w);
    }
}

/// `bc_letter(d) ≡ b_letter(d) · c_letter(d)`: for `d ≤ n` it IS `b_d c_d`; for `d > n` it is
/// `c_i⁻¹ b_i⁻¹` which commutes to `b_i⁻¹ c_i⁻¹`.
pub proof fn lemma_bc_letter_split(mm: ModMachine, n: nat, d: nat)
    requires 1 <= d <= 2 * n,
    ensures
        equiv_in_presentation(h1_base(mm, n),
            bc_letter(b_base(g_m(mm).num_generators, n), c_base(g_m(mm).num_generators), n, d),
            seq![alphabet_letter(b_base(g_m(mm).num_generators, n), n, d)]
                + seq![alphabet_letter(c_base(g_m(mm).num_generators), n, d)]),
{
    let nk = g_m(mm).num_generators;
    let p = h1_base(mm, n);
    let ng = h1_num_gens(nk, n);
    lemma_h1_base_valid(mm, n);
    let bb = b_base(nk, n);
    let cb = c_base(nk);
    let bl = alphabet_letter(bb, n, d);
    let cl = alphabet_letter(cb, n, d);
    let bc = bc_letter(bb, cb, n, d);
    if d <= n {
        assert(bl == Symbol::Gen((bb + d - 1) as nat));
        assert(cl == Symbol::Gen((cb + d - 1) as nat));
        assert(bc =~= seq![bl] + seq![cl]);
        lemma_equiv_refl(p, seq![bl] + seq![cl]);
    } else {
        assert(bc =~= seq![cl] + seq![bl]);
        lemma_alphabet_letter_gen_in_block(cb, n, d);     // cl index ∈ [cb, cb+n)
        lemma_b_alpha_commutes_c_symbol(mm, n, d, cl);    // commutes([bl], [cl])
        lemma_alphabet_letter_valid(bb, n, d, ng);        // bb+n = nk+2n ≤ ng
        lemma_alphabet_letter_valid(cb, n, d, ng);        // cb+n = nk+n ≤ ng
        assert(word_valid(seq![bl], ng)) by { assert(seq![bl][0] == bl); }
        assert(word_valid(seq![cl], ng)) by { assert(seq![cl][0] == cl); }
        lemma_commutes_sym(p, seq![bl], seq![cl]);        // equiv([cl]+[bl], [bl]+[cl])
    }
}

/// **The `w_bc` split.** `h1_base ⊢ w_α(bc) ≡ w_α(b)·w_α(c)`: the interleaved bc-word collapses
/// to the b-word times the c-word (each `c` commutes past the following `b`'s). Induction on α's
/// base-m digits.
pub proof fn lemma_w_bc_split(mm: ModMachine, n: nat, m: nat, alpha: nat)
    requires numbers_word(n, m, alpha), 2 * n < m,
    ensures
        equiv_in_presentation(h1_base(mm, n),
            w_bc(b_base(g_m(mm).num_generators, n), c_base(g_m(mm).num_generators), n, m, alpha),
            w_b(b_base(g_m(mm).num_generators, n), n, m, alpha)
                + w_c(c_base(g_m(mm).num_generators), n, m, alpha)),
    decreases alpha,
{
    let nk = g_m(mm).num_generators;
    let p = h1_base(mm, n);
    let ng = h1_num_gens(nk, n);
    lemma_h1_base_valid(mm, n);
    let bb = b_base(nk, n);
    let cb = c_base(nk);
    if alpha == 0 || m <= 1 {
        assert(w_bc(bb, cb, n, m, alpha) =~= empty_word());
        assert(w_b(bb, n, m, alpha) =~= empty_word());     // w_c(bb,..) = ε
        assert(w_c(cb, n, m, alpha) =~= empty_word());
        assert(w_b(bb, n, m, alpha) + w_c(cb, n, m, alpha) =~= empty_word());
        lemma_equiv_refl(p, w_bc(bb, cb, n, m, alpha));
    } else {
        let ap = alpha / m;
        let d = alpha % m;
        // numbers_word(alpha), alpha≠0, m>1  ⟹  1 ≤ d ≤ 2n ∧ numbers_word(ap)
        assert(1 <= d <= 2 * n && numbers_word(n, m, ap));
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);  // ap < alpha

        let bl_w: Word = seq![alphabet_letter(bb, n, d)];
        let cl_w: Word = seq![alphabet_letter(cb, n, d)];
        let bcL = bc_letter(bb, cb, n, d);
        let bigP = w_b(bb, n, m, ap);          // = w_c(bb,..,ap)
        let bigQ = w_c(cb, n, m, ap);
        let WBC = w_bc(bb, cb, n, m, ap);

        // unfoldings (bridge Seq::new(1,·) to seq![·])
        assert(w_bc(bb, cb, n, m, alpha) =~= WBC + bcL);
        assert(w_b(bb, n, m, alpha) =~= bigP + bl_w);
        assert(w_c(cb, n, m, alpha) =~= bigQ + cl_w);

        // validities
        lemma_w_c_valid(bb, n, m, ap, ng);     // bigP valid (bb+n = nk+2n ≤ ng)
        lemma_w_c_valid(cb, n, m, ap, ng);     // bigQ valid (cb+n = nk+n ≤ ng)
        lemma_alphabet_letter_valid(bb, n, d, ng);
        lemma_alphabet_letter_valid(cb, n, d, ng);
        assert(word_valid(bl_w, ng)) by { assert(bl_w[0] == alphabet_letter(bb, n, d)); }
        assert(word_valid(cl_w, ng)) by { assert(cl_w[0] == alphabet_letter(cb, n, d)); }

        // IH
        lemma_w_bc_split(mm, n, m, ap);        // equiv(WBC, bigP + bigQ)

        // E1: WBC·bcL ≡ (P·Q)·bcL
        lemma_equiv_concat_left(p, WBC, bigP + bigQ, bcL);
        // E2/E3: bcL ≡ bl·cl,  (P·Q)·bcL ≡ (P·Q)·(bl·cl)
        lemma_bc_letter_split(mm, n, d);       // equiv(bcL, bl_w + cl_w)
        lemma_equiv_concat_right(p, bigP + bigQ, bcL, bl_w + cl_w);

        // commute: bl_w past bigQ  ⟹  Q·bl ≡ bl·Q
        lemma_w_c_gens_in_block(cb, n, m, ap); // bigQ letters in c-block
        lemma_b_alpha_commutes_c_word(mm, n, d, bigQ);   // commutes(bl_w, bigQ)
        lemma_concat_word_valid(bl_w, bigQ, ng);
        lemma_commutes_sym(p, bl_w, bigQ);     // equiv(bigQ + bl_w, bl_w + bigQ)

        // E5: (P·Q)·(bl·cl) ≡ (P·bl)·(Q·cl)  via the middle commute
        let m1 = (bigQ + bl_w) + cl_w;
        let m2 = (bl_w + bigQ) + cl_w;
        lemma_equiv_concat_left(p, bigQ + bl_w, bl_w + bigQ, cl_w);   // m1 ≡ m2
        lemma_equiv_concat_right(p, bigP, m1, m2);                    // P·m1 ≡ P·m2
        assert((bigP + bigQ) + (bl_w + cl_w) =~= bigP + m1);
        assert((bigP + bl_w) + (bigQ + cl_w) =~= bigP + m2);

        // chain:  WBC·bcL ≡ (P·Q)·bcL ≡ (P·Q)·(bl·cl) ≡ (P·bl)·(Q·cl)
        lemma_equiv_transitive(p, WBC + bcL, (bigP + bigQ) + bcL, (bigP + bigQ) + (bl_w + cl_w));
        lemma_equiv_transitive(p, WBC + bcL, (bigP + bigQ) + (bl_w + cl_w),
            (bigP + bl_w) + (bigQ + cl_w));
        // connect to the goal forms
        assert(w_bc(bb, cb, n, m, alpha) =~= WBC + bcL);
        assert(w_b(bb, n, m, alpha) + w_c(cb, n, m, alpha) =~= (bigP + bl_w) + (bigQ + cl_w));
    }
}

/// One rung: an equivalence in `h3_upto(l)` lifts to `h3_upto(l+1)` (the `a_{l+1}` HNN whose
/// base is exactly `h3_upto(l)`).
pub proof fn lemma_h3_upto_step_embeds(mm: ModMachine, n: nat, m: nat, l: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_upto(mm, n, m, (l + 1) as nat), w1, w2),
{
    let data = HNNData {
        base: h3_upto(mm, n, m, l),
        associations: phi_assoc(g_m(mm).num_generators, n, m, (l + 1) as nat),
    };
    // h3_upto(l+1) = hnn_presentation(data), and data.base = h3_upto(l).
    assert(h3_upto(mm, n, m, (l + 1) as nat) == hnn_presentation(data));
    lemma_base_embeds_in_hnn(data, w1, w2);
}

/// Climb from level `l` up to level `hi` (`l ≤ hi ≤ 2n`): equivalence is preserved up the tower.
pub proof fn lemma_h3_upto_climbs(mm: ModMachine, n: nat, m: nat, l: nat, hi: nat, w1: Word, w2: Word)
    requires
        l <= hi,
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_upto(mm, n, m, hi), w1, w2),
    decreases hi - l,
{
    if l == hi {
    } else {
        lemma_h3_upto_step_embeds(mm, n, m, l, w1, w2);
        lemma_h3_upto_climbs(mm, n, m, (l + 1) as nat, hi, w1, w2);
    }
}

/// Top rung: an equivalence in `h3_upto(2n)` lifts to `h3_pres` (the `k` HNN whose base is
/// `h3_upto(2n)`).
pub proof fn lemma_h3_upto_top_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h3_upto(mm, n, m, (2 * n) as nat), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    let data = HNNData {
        base: h3_upto(mm, n, m, (2 * n) as nat),
        associations: psi_assoc(mm, n),
    };
    assert(h3_pres(mm, n, m) == hnn_presentation(data));
    lemma_base_embeds_in_hnn(data, w1, w2);
}

/// **Lift from any tower level `l ≤ 2n` to `h3_pres`.**
pub proof fn lemma_h3_upto_in_h3(mm: ModMachine, n: nat, m: nat, l: nat, w1: Word, w2: Word)
    requires
        l <= 2 * n,
        equiv_in_presentation(h3_upto(mm, n, m, l), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    lemma_h3_upto_climbs(mm, n, m, l, (2 * n) as nat, w1, w2);
    lemma_h3_upto_top_in_h3(mm, n, m, w1, w2);
}

/// **Lift from `h2_pres` to `h3_pres`** (= the `l = 0` base of the tower).
pub proof fn lemma_h2_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h2_pres(mm, n), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    // h3_upto(0) == h2_pres.
    assert(h3_upto(mm, n, m, 0) == h2_pres(mm, n));
    lemma_h3_upto_in_h3(mm, n, m, 0, w1, w2);
}

/// **Lift from `h1_base` to `h3_pres`** (through the `p` HNN, then the tower). `h2_pres` is the
/// `p`-HNN over `h1_base`, so an `h1_base` equivalence first lifts to `h2_pres`.
pub proof fn lemma_h1_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires
        equiv_in_presentation(h1_base(mm, n), w1, w2),
    ensures
        equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    // h2_pres = hnn_presentation(h2_data), h2_data.base = h1_base.
    let data = h2_data(mm, n);
    assert(h2_pres(mm, n) == hnn_presentation(data));
    assert(data.base == h1_base(mm, n));
    lemma_base_embeds_in_hnn(data, w1, w2);
    lemma_h2_in_h3(mm, n, m, w1, w2);
}

// ----------------------------------------------------------------------------
// Forward lift from base_A all the way to h3_pres.  Layer-1 config-algebra facts
// (config conjugation, power merges) live at `base_A`; we lift them up the K_M
// tower (`lemma_lift_to_gm`), across the c/b/d-extension (g_m → h1_base, a prefix
// extension with MORE generators — neither `extends_presentation` nor
// `relators_included` applies, so we replay the derivation), then up the Higman
// tower (`lemma_h1_in_h3`).  This is the keystone lift for sub-bricks 2–5.
// ----------------------------------------------------------------------------

/// One derivation step valid in `g_m` replays in `h1_base`. `h1_base.relators` extends
/// `g_m.relators` by the commutators (a prefix), and `h1_base` has MORE generators; `apply_step`
/// gates only on `symbol_valid` (monotone) and on relator index/content (a prefix), so the step
/// produces the identical result.
proof fn lemma_step_gm_to_h1(mm: ModMachine, n: nat, w: Word, step: DerivationStep, w2: Word)
    requires apply_step(g_m(mm), w, step) == Some(w2),
    ensures apply_step(h1_base(mm, n), w, step) == Some(w2),
{
    let g = g_m(mm);
    let h = h1_base(mm, n);
    let nk = g.num_generators;
    lemma_g_m_num_generators(mm);
    assert(h.relators =~= g.relators + comm_relators(nk, n));
    assert(g.num_generators <= h.num_generators);     // nk ≤ nk+2n+1
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {
            // symbol_valid(symbol, nk) ⟹ symbol_valid(symbol, h.num_generators)
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < g.relators.len());
            assert(h.relators[relator_index as int] == g.relators[relator_index as int]);
            assert(get_relator(h, relator_index, inverted) == get_relator(g, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < g.relators.len());
            assert(h.relators[relator_index as int] == g.relators[relator_index as int]);
            assert(get_relator(h, relator_index, inverted) == get_relator(g, relator_index, inverted));
        },
    }
}

/// A whole `g_m` derivation replays in `h1_base`.
proof fn lemma_deriv_gm_to_h1(mm: ModMachine, n: nat, steps: Seq<DerivationStep>, w1: Word, w2: Word)
    requires derivation_produces(g_m(mm), steps, w1) == Some(w2),
    ensures derivation_produces(h1_base(mm, n), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step(g_m(mm), w1, step).unwrap();
        lemma_step_gm_to_h1(mm, n, w1, step, next);
        lemma_deriv_gm_to_h1(mm, n, steps.drop_first(), next, w2);
    }
}

/// **Lift from `g_m` (= K_M) to `h1_base`.** An equivalence in `K_M` holds in `H₁`.
pub proof fn lemma_gm_in_h1(mm: ModMachine, n: nat, w1: Word, w2: Word)
    requires equiv_in_presentation(g_m(mm), w1, w2),
    ensures equiv_in_presentation(h1_base(mm, n), w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(g_m(mm), d, w1, w2);
    lemma_deriv_gm_to_h1(mm, n, d.steps, w1, w2);
    let d2 = Derivation { steps: d.steps };
    assert(derivation_valid(h1_base(mm, n), d2, w1, w2));
}

/// **The keystone lift: `base_A → h3_pres`.** A `base_A` equivalence (config-algebra facts) holds
/// in the full finite group `H₃`. Chains `lemma_lift_to_gm` (K_M tower) → `lemma_gm_in_h1`
/// (c/b/d extension) → `lemma_h1_in_h3` (Higman tower).
pub proof fn lemma_base_A_in_h3(mm: ModMachine, n: nat, m: nat, w1: Word, w2: Word)
    requires equiv_in_presentation(base_A(), w1, w2),
    ensures equiv_in_presentation(h3_pres(mm, n, m), w1, w2),
{
    lemma_lift_to_gm(mm, w1, w2);
    lemma_gm_in_h1(mm, n, w1, w2);
    lemma_h1_in_h3(mm, n, m, w1, w2);
}

// ----------------------------------------------------------------------------
// Sub-brick 2 — the a_l config conjugation:  a_l⁻¹ · t_α · a_l ≡ t_{α·m+l}  in H₃.
// The φ_l HNN relations (t↦t_l, x↦xᵐ) conjugate the config word `t_α = x⁻ᵅ t xᵅ` to
// `x⁻ᵐᵅ · t_l · xᵐᵅ = config(mα+l, 0)`.  Via the conjugation telescope at level l + the
// base_A config-move lemma, lifted to H₃.  This is the per-digit step of (IIa).
// ----------------------------------------------------------------------------

/// The spelling of `config(α,0) = x⁻ᵅ t xᵅ` over an HNN association alphabet (gen 0 = t, gen 1 = x).
pub open spec fn conj_u(alpha: nat) -> Word {
    signed_power(1, -(alpha as int)) + seq![Symbol::Gen(0)] + signed_power(1, alpha as int)
}

/// `apply_embedding(gens, conj_u(α)) = x^{-pp·α} · gens[0] · x^{pp·α}` when `gens[1] = xᵖᵖ`.
pub proof fn lemma_emb_conj_u(gens: Seq<Word>, pp: nat, alpha: nat)
    requires
        1 < gens.len(),
        gens[1] =~= signed_power(1, pp as int),
    ensures
        apply_embedding(gens, conj_u(alpha)) =~=
            signed_power(1, -((pp as int) * (alpha as int))) + gens[0]
                + signed_power(1, (pp as int) * (alpha as int)),
{
    let un = signed_power(1, -(alpha as int));
    let umid: Word = seq![Symbol::Gen(0)];
    let up = signed_power(1, alpha as int);
    assert(conj_u(alpha) =~= (un + umid) + up);
    lemma_apply_embedding_concat(gens, un + umid, up);
    lemma_apply_embedding_concat(gens, un, umid);
    lemma_emb_signed_scaled(gens, 1, pp, -(alpha as int));      // emb(un) = sp(1, pp·(-α))
    lemma_emb_signed_scaled(gens, 1, pp, alpha as int);         // emb(up) = sp(1, pp·α)
    assert((pp as int) * (-(alpha as int)) == -((pp as int) * (alpha as int))) by (nonlinear_arith);
    assert(apply_embedding(gens, umid) =~= gens[0]) by { reveal_with_fuel(apply_embedding, 2); }
    assert(apply_embedding(gens, conj_u(alpha)) =~=
        (apply_embedding(gens, un) + apply_embedding(gens, umid)) + apply_embedding(gens, up));
}

/// **Sub-brick 2 keystone.** `a_l⁻¹ · config(α,0) · a_l ≡ config(α·m+l, 0)` in `h3_pres`
/// (1 ≤ l ≤ 2n). The per-digit conjugation step of (IIa).
pub proof fn lemma_a_conj_config(mm: ModMachine, n: nat, m: nat, l: nat, alpha: nat)
    requires 1 <= l <= 2 * n, 2 * n < m,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            seq![Symbol::Inv(a_idx(g_m(mm).num_generators, n, l))]
                + config_word(alpha, 0)
                + seq![Symbol::Gen(a_idx(g_m(mm).num_generators, n, l))],
            config_word((alpha * m + l) as nat, 0)),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let base = h3_upto(mm, n, m, (l - 1) as nat);
    let data = HNNData { base, associations: phi_assoc(nk, n, m, l) };
    // h3_upto(l) = hnn_presentation(data)
    assert(h3_upto(mm, n, m, l) == hnn_presentation(data));
    // hnn_data_valid(data)
    lemma_h3_upto_valid(mm, n, m, (l - 1) as nat);
    lemma_h3_upto_num_generators(mm, n, m, (l - 1) as nat);     // base.num = nk+2n+1+l
    assert(base.num_generators == h2_num_gens(nk, n) + (l - 1));
    assert(base.num_generators >= nk + 2 * n + 2);
    lemma_phi_assoc_valid(nk, n, m, l, base.num_generators);
    lemma_hnn_data_valid_from(data, base.num_generators);

    let ag = hnn_a_gens(data);
    let bg = hnn_b_gens(data);
    let kk = data.associations.len();                          // = n + 4
    assert(kk == phi_assoc(nk, n, m, l).len());
    assert(1 < kk);
    // u = conj_u(alpha), valid over the association alphabet
    let u = conj_u(alpha);
    assert(word_valid(u, kk)) by {
        lemma_signed_power_valid(1, -(alpha as int), kk);
        lemma_signed_power_valid(1, alpha as int, kk);
        crate::word::lemma_concat_word_valid(signed_power(1, -(alpha as int)), seq![Symbol::Gen(0)], kk);
        crate::word::lemma_concat_word_valid(
            signed_power(1, -(alpha as int)) + seq![Symbol::Gen(0)], signed_power(1, alpha as int), kk);
        assert(seq![Symbol::Gen(0)][0] == Symbol::Gen(0));
    }
    // the conjugation telescope at level l
    lemma_stable_conj_factorization(data, u);
    // a_gens / b_gens generator-0/1 identification
    assert(ag[0] =~= seq![Symbol::Gen(0)]);                    // phi_assoc[0].0 = [t]
    assert(ag[1] =~= signed_power(1, 1));                      // phi_assoc[1].0 = [x] = x¹
    assert(bg[0] =~= config_word(l, 0));                       // phi_assoc[0].1 = t_l
    assert(bg[1] =~= signed_power(1, m as int));               // phi_assoc[1].1 = xᵐ

    // emb(ag, u) = config(α,0)
    lemma_emb_conj_u(ag, 1, alpha);
    lemma_config_signed_matches_nat(alpha, 0);
    assert(apply_embedding(ag, u) =~= config_word(alpha, 0)) by {
        assert((1 as int) * (alpha as int) == alpha as int) by (nonlinear_arith);
        assert(config_word_signed(alpha as int, 0) =~=
            signed_power(1, -(alpha as int)) + seq![Symbol::Gen(0)] + signed_power(1, alpha as int));
    }

    // emb(bg, u) = x^{-mα}·t_l·x^{mα}
    lemma_emb_conj_u(bg, m, alpha);
    let mam: int = (m as int) * (alpha as int);
    assert(apply_embedding(bg, u) =~=
        signed_power(1, -mam) + config_word(l, 0) + signed_power(1, mam));

    // base_A: x^{-mα}·t_l·x^{mα} ≡ config(mα+l, 0)
    lemma_conj_config_signed_by_x(l as int, 0, mam);          // ≡ config_signed(l+mα, 0)
    lemma_config_signed_matches_nat(l, 0);                    // config_signed(l,0) = config(l,0)
    // index arithmetic: l + m·α == α·m + l (with nat→int casts); mam == (m as int)*(alpha as int)
    assert((l as int) + (m as int) * (alpha as int) == (alpha * m + l) as int) by (nonlinear_arith);
    assert((l as int) + mam == (alpha * m + l) as int);
    lemma_config_signed_matches_nat((alpha * m + l) as nat, 0);
    let blob = signed_power(1, -mam) + config_word(l, 0) + signed_power(1, mam);
    assert(blob =~= signed_power(1, -mam) + config_word_signed(l as int, 0) + signed_power(1, mam));
    assert(equiv_in_presentation(base_A(), blob, config_word((alpha * m + l) as nat, 0)));

    // assemble: telescope (h3_upto(l)) + emb identifications, lift to h3_pres, then base_A blob.
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    lemma_h3_a_stable_letter(mm, n, m, l);                    // st = Gen(a_idx(nk,n,l))
    assert(st == Symbol::Gen(a_idx(nk, n, l)));
    assert(si == Symbol::Inv(a_idx(nk, n, l)));
    let conj_lhs = seq![si] + apply_embedding(ag, u) + seq![st];
    // telescope: equiv(h3_upto(l), conj_lhs, emb(bg,u))
    assert(equiv_in_presentation(h3_upto(mm, n, m, l), conj_lhs, apply_embedding(bg, u)));
    lemma_h3_upto_in_h3(mm, n, m, l, conj_lhs, apply_embedding(bg, u));
    // emb(bg,u) ≡ config(mα+l,0) lifted from base_A
    lemma_base_A_in_h3(mm, n, m, blob, config_word((alpha * m + l) as nat, 0));
    assert(apply_embedding(bg, u) =~= blob);
    lemma_equiv_transitive(h3_pres(mm, n, m), conj_lhs, apply_embedding(bg, u),
        config_word((alpha * m + l) as nat, 0));
    // conj_lhs == goal LHS (emb(ag,u) = config(α,0), si/st = a_l⁻¹/a_l)
    assert(conj_lhs =~= seq![Symbol::Inv(a_idx(nk, n, l))] + config_word(alpha, 0)
        + seq![Symbol::Gen(a_idx(nk, n, l))]);
}

// ----------------------------------------------------------------------------
// Sub-brick 3 — the (IIa) / (IIb) inductions  (induction on α's base-m digits).
//
// `w_α(a)` = `w_α(b)` with each digit-letter replaced by the POSITIVE stable letter
// `a_digit = Gen(a_idx(nk,n,digit))` (there are 2n a-stable-letters a₁…a₂ₙ, one per digit
// value — no inverse convention). Snoc recursion mirrors `w_c`.
// ----------------------------------------------------------------------------

/// `w_α(a)` over the a-stable-letters. Lowest base-m digit appended last.
pub open spec fn w_a(nk: nat, n: nat, m: nat, alpha: nat) -> Word
    decreases alpha via w_a_decreases
{
    if alpha == 0 || m <= 1 {
        empty_word()
    } else {
        w_a(nk, n, m, alpha / m) + seq![Symbol::Gen(a_idx(nk, n, alpha % m))]
    }
}

#[via_fn]
proof fn w_a_decreases(nk: nat, n: nat, m: nat, alpha: nat) {
    if alpha != 0 && m > 1 {
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
    }
}

/// **(IIa).** `w_α(a)⁻¹ · t · w_α(a) ≡ t_α = config(α,0)` in `h3_pres`, by induction on α's
/// digits via the per-digit keystone `lemma_a_conj_config`.
pub proof fn lemma_IIa(mm: ModMachine, n: nat, m: nat, alpha: nat)
    requires numbers_word(n, m, alpha), 2 * n < m,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            inverse_word(w_a(g_m(mm).num_generators, n, m, alpha))
                + seq![Symbol::Gen(0)]
                + w_a(g_m(mm).num_generators, n, m, alpha),
            config_word(alpha, 0)),
    decreases alpha,
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    let t: Word = seq![Symbol::Gen(0)];
    let wa = w_a(nk, n, m, alpha);
    if alpha == 0 {
        // w_a = ε, LHS = ε + t + ε = t = [Gen 0] = config(0,0).
        assert(wa =~= empty_word());
        assert(inverse_word(wa) =~= empty_word()) by { lemma_inverse_empty(); }
        assert(config_word(0, 0) =~= t);
        assert(inverse_word(wa) + t + wa =~= t);
        lemma_equiv_refl(p, config_word(alpha, 0));
    } else {
        // α≠0, numbers_word ⟹ m>1 and 1 ≤ d ≤ 2n, numbers_word(ap)
        assert(m > 1);
        let ap = alpha / m;
        let d = alpha % m;
        assert(1 <= d <= 2 * n && numbers_word(n, m, ap));
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);   // ap < alpha
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(alpha as int, m as int);  // α = m·ap + d
        assert(ap * m + d == alpha) by (nonlinear_arith)
            requires alpha as int == m as int * (alpha as int / m as int) + alpha as int % m as int,
                     ap == alpha / m, d == alpha % m;

        let ad: Word = seq![Symbol::Gen(a_idx(nk, n, d))];
        let adi: Word = seq![Symbol::Inv(a_idx(nk, n, d))];
        let wap = w_a(nk, n, m, ap);
        let inner = inverse_word(wap) + t + wap;
        // w_a(α) = w_a(ap) + a_d ;  inverse_word(w_a(α)) = a_d⁻¹ + inverse_word(w_a(ap))
        assert(wa =~= wap + ad);
        lemma_inverse_concat(wap, ad);
        lemma_inverse_singleton(Symbol::Gen(a_idx(nk, n, d)));
        assert(ad =~= Seq::new(1, |_i: int| Symbol::Gen(a_idx(nk, n, d))));
        assert(inverse_word(ad) =~= adi);
        assert(inverse_word(wa) =~= adi + inverse_word(wap));
        // LHS = a_d⁻¹ · inner · a_d
        assert(inverse_word(wa) + t + wa =~= adi + inner + ad);

        // IH:  inner ≡ config(ap, 0)
        lemma_IIa(mm, n, m, ap);
        assert(equiv_in_presentation(p, inner, config_word(ap, 0)));
        // conjugate by a_d:  a_d⁻¹ · inner · a_d ≡ a_d⁻¹ · config(ap,0) · a_d
        lemma_equiv_concat_right(p, adi, inner, config_word(ap, 0));
        lemma_equiv_concat_left(p, adi + inner, adi + config_word(ap, 0), ad);
        assert(equiv_in_presentation(p, adi + inner + ad, (adi + config_word(ap, 0)) + ad));
        // keystone: a_d⁻¹ · config(ap,0) · a_d ≡ config(ap·m+d, 0) = config(α, 0)
        lemma_a_conj_config(mm, n, m, d, ap);
        assert((ap * m + d) as nat == alpha);
        assert((adi + config_word(ap, 0)) + ad
            =~= seq![Symbol::Inv(a_idx(nk, n, d))] + config_word(ap, 0)
                + seq![Symbol::Gen(a_idx(nk, n, d))]);
        // chain
        lemma_equiv_transitive(p, adi + inner + ad, (adi + config_word(ap, 0)) + ad,
            config_word(alpha, 0));
        assert(inverse_word(wa) + t + wa =~= adi + inner + ad);
    }
}

// ----------------------------------------------------------------------------
// (IIb) support — conjugation of φ_d associations by a_d, lifted to H₃.
// ----------------------------------------------------------------------------

/// Conjugating the `i`-th `φ_d` association by `a_d` gives its image, in `H₃`:
/// `a_d⁻¹ · φ_assoc[i].0 · a_d ≡ φ_assoc[i].1`. Shared by `lemma_a_conj_d` (i=2, the d-letter)
/// and the b-commutation (i = 2+j, the b_j block).
pub proof fn lemma_phi_d_conj_in_h3(mm: ModMachine, n: nat, m: nat, d: nat, i: int)
    requires 1 <= d <= 2 * n, 0 <= i < n + 4,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            seq![Symbol::Inv(a_idx(g_m(mm).num_generators, n, d))]
                + phi_assoc(g_m(mm).num_generators, n, m, d)[i].0
                + seq![Symbol::Gen(a_idx(g_m(mm).num_generators, n, d))],
            phi_assoc(g_m(mm).num_generators, n, m, d)[i].1),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let base = h3_upto(mm, n, m, (d - 1) as nat);
    let data = HNNData { base, associations: phi_assoc(nk, n, m, d) };
    assert(h3_upto(mm, n, m, d) == hnn_presentation(data));
    lemma_h3_upto_valid(mm, n, m, (d - 1) as nat);
    lemma_h3_upto_num_generators(mm, n, m, (d - 1) as nat);
    assert(base.num_generators >= nk + 2 * n + 2);
    lemma_phi_assoc_valid(nk, n, m, d, base.num_generators);
    lemma_hnn_data_valid_from(data, base.num_generators);
    assert(data.associations.len() == n + 4);              // 3 + n + 1
    lemma_hnn_conjugation(data, i);
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    lemma_h3_a_stable_letter(mm, n, m, d);
    assert(st == Symbol::Gen(a_idx(nk, n, d)));
    assert(si == Symbol::Inv(a_idx(nk, n, d)));
    let lhs = Seq::new(1, |_j: int| si) + data.associations[i].0 + Seq::new(1, |_j: int| st);
    assert(lhs =~= seq![Symbol::Inv(a_idx(nk, n, d))] + phi_assoc(nk, n, m, d)[i].0
        + seq![Symbol::Gen(a_idx(nk, n, d))]);
    lemma_h3_upto_in_h3(mm, n, m, d, lhs, data.associations[i].1);
}

/// **a_d conjugates d.** `a_d⁻¹ · d · a_d ≡ b_d · d` in `H₃` (φ_d head[2]; `b_d = alphabet_letter`).
pub proof fn lemma_a_conj_d(mm: ModMachine, n: nat, m: nat, d: nat)
    requires 1 <= d <= 2 * n,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            seq![Symbol::Inv(a_idx(g_m(mm).num_generators, n, d))]
                + seq![Symbol::Gen(d_idx(g_m(mm).num_generators, n))]
                + seq![Symbol::Gen(a_idx(g_m(mm).num_generators, n, d))],
            seq![alphabet_letter(b_base(g_m(mm).num_generators, n), n, d),
                 Symbol::Gen(d_idx(g_m(mm).num_generators, n))]),
{
    let nk = g_m(mm).num_generators;
    // phi_assoc[2] = (d, b_d·d)
    assert(phi_assoc(nk, n, m, d)[2].0 == seq![Symbol::Gen(d_idx(nk, n))]);
    assert(phi_assoc(nk, n, m, d)[2].1
        =~= seq![alphabet_letter(b_base(nk, n), n, d), Symbol::Gen(d_idx(nk, n))]);
    lemma_phi_d_conj_in_h3(mm, n, m, d, 2);
}

/// `a_d` commutes with any single b-block symbol (generator index in `[b_base, b_base+n)`).
pub proof fn lemma_a_commutes_b_symbol(mm: ModMachine, n: nat, m: nat, d: nat, s: Symbol)
    requires
        1 <= d <= 2 * n,
        b_base(g_m(mm).num_generators, n) <= generator_index(s)
            < b_base(g_m(mm).num_generators, n) + n,
    ensures
        commutes(h3_pres(mm, n, m), seq![Symbol::Gen(a_idx(g_m(mm).num_generators, n, d))], seq![s]),
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    lemma_h3_pres_valid(mm, n, m);
    lemma_h3_num_generators(mm, n, m);
    lemma_g_m_num_generators(mm);
    let ng = h3_num_gens(nk, n);
    let bg = generator_index(s);                 // ∈ [b_base, b_base+n)
    let j = (bg - b_base(nk, n) + 1) as nat;     // ∈ [1, n]
    assert(1 <= j <= n);
    assert(b_idx(nk, n, j) == bg);
    // phi_assoc[2+j] = b_j ↦ b_j
    let ji: int = 2 + (j as int);
    assert(phi_assoc(nk, n, m, d)[ji].0 == seq![Symbol::Gen(b_idx(nk, n, j))]);
    assert(phi_assoc(nk, n, m, d)[ji].1 == seq![Symbol::Gen(b_idx(nk, n, j))]);
    lemma_phi_d_conj_in_h3(mm, n, m, d, ji);   // a_d⁻¹ b_j a_d ≡ b_j
    let ad = Symbol::Gen(a_idx(nk, n, d));
    let adi = Symbol::Inv(a_idx(nk, n, d));
    let gbj: Word = seq![Symbol::Gen(b_idx(nk, n, j))];
    assert(a_idx(nk, n, d) < ng);                 // a_idx ≤ nk+4n+1 < nk+4n+3
    assert(b_idx(nk, n, j) < ng);
    assert(is_inverse_pair(ad, adi));
    assert(symbol_valid(ad, ng));
    assert(word_valid(gbj, ng)) by { assert(gbj[0] == Symbol::Gen(b_idx(nk, n, j))); }
    assert(equiv_in_presentation(p, seq![adi] + gbj + seq![ad], gbj));
    lemma_commute_from_conj(p, ad, adi, gbj);     // commutes([ad], [Gen b_j])
    // s = Gen(bg) or Inv(bg); bg = b_idx(nk,n,j)
    lemma_inverse_singleton(Symbol::Gen(b_idx(nk, n, j)));
    assert(gbj =~= Seq::new(1, |_i: int| Symbol::Gen(b_idx(nk, n, j))));
    assert(inverse_word(gbj) =~= seq![Symbol::Inv(b_idx(nk, n, j))]);
    match s {
        Symbol::Gen(g) => { assert(g == bg); assert(seq![s] == gbj); },
        Symbol::Inv(g) => {
            assert(g == bg);
            lemma_commutes_inv_right(p, seq![ad], gbj);   // commutes([ad], [Inv b_j])
            assert(seq![s] =~= inverse_word(gbj));
        },
    }
}

/// `a_d` commutes with any word all of whose symbols are b-block symbols.
pub proof fn lemma_a_commutes_b_word(mm: ModMachine, n: nat, m: nat, d: nat, w: Word)
    requires
        1 <= d <= 2 * n,
        forall|k: int| 0 <= k < w.len() ==>
            b_base(g_m(mm).num_generators, n) <= generator_index(#[trigger] w[k])
                < b_base(g_m(mm).num_generators, n) + n,
    ensures
        commutes(h3_pres(mm, n, m), seq![Symbol::Gen(a_idx(g_m(mm).num_generators, n, d))], w),
    decreases w.len(),
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    let ad_w: Word = seq![Symbol::Gen(a_idx(nk, n, d))];
    if w.len() == 0 {
        lemma_commutes_empty_right(p, ad_w);
        assert(w =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(b_base(nk, n) <= generator_index(s) < b_base(nk, n) + n) by { assert(w[0] == s); }
        lemma_a_commutes_b_symbol(mm, n, m, d, s);
        assert forall|k: int| 0 <= k < rest.len() implies
            b_base(nk, n) <= generator_index(#[trigger] rest[k]) < b_base(nk, n) + n by {
            assert(rest[k] == w[k + 1]);
        }
        lemma_a_commutes_b_word(mm, n, m, d, rest);
        lemma_commutes_concat_right(p, ad_w, seq![s], rest);
        assert(seq![s] + rest =~= w);
    }
}

/// **(IIb).** `w_α(a)⁻¹ · d · w_α(a) ≡ w_α(b) · d` in `h3_pres`, by induction on α's digits.
/// Step α↦αm+l: conjugate by `a_l`; push `a_l` past the b-word `w_α(b)` (commutes), then
/// `a_l⁻¹ d a_l ≡ b_l d` (`lemma_a_conj_d`), giving the snoc `w_α(b)·b_l = w_{αm+l}(b)`.
pub proof fn lemma_IIb(mm: ModMachine, n: nat, m: nat, alpha: nat)
    requires numbers_word(n, m, alpha), 2 * n < m,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            inverse_word(w_a(g_m(mm).num_generators, n, m, alpha))
                + seq![Symbol::Gen(d_idx(g_m(mm).num_generators, n))]
                + w_a(g_m(mm).num_generators, n, m, alpha),
            w_b(b_base(g_m(mm).num_generators, n), n, m, alpha)
                + seq![Symbol::Gen(d_idx(g_m(mm).num_generators, n))]),
    decreases alpha,
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    lemma_g_m_num_generators(mm);
    lemma_h3_num_generators(mm, n, m);
    lemma_h3_pres_valid(mm, n, m);
    let ng = h3_num_gens(nk, n);
    let dl: Word = seq![Symbol::Gen(d_idx(nk, n))];
    let wa = w_a(nk, n, m, alpha);
    let wb = w_b(b_base(nk, n), n, m, alpha);
    if alpha == 0 {
        assert(wa =~= empty_word());
        assert(inverse_word(wa) =~= empty_word()) by { lemma_inverse_empty(); }
        assert(wb =~= empty_word());
        assert(inverse_word(wa) + dl + wa =~= dl);
        assert(wb + dl =~= dl);
        lemma_equiv_refl(p, dl);
    } else {
        assert(m > 1);
        let ap = alpha / m;
        let d = alpha % m;
        assert(1 <= d <= 2 * n && numbers_word(n, m, ap));
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);

        let ad = Symbol::Gen(a_idx(nk, n, d));
        let adi = Symbol::Inv(a_idx(nk, n, d));
        let bl = alphabet_letter(b_base(nk, n), n, d);
        let wap = w_a(nk, n, m, ap);
        let wbap = w_b(b_base(nk, n), n, m, ap);
        let inner = inverse_word(wap) + dl + wap;

        // unfold snocs:  wa = wap·a_d ;  wb = wbap·b_d ;  inverse_word(wa) = a_d⁻¹·wap⁻¹
        assert(wa =~= wap + seq![ad]);
        assert(wb =~= wbap + seq![bl]);
        lemma_inverse_concat(wap, seq![ad]);
        lemma_inverse_singleton(Symbol::Gen(a_idx(nk, n, d)));
        assert(seq![ad] =~= Seq::new(1, |_i: int| Symbol::Gen(a_idx(nk, n, d))));
        assert(inverse_word(seq![ad]) =~= seq![adi]);
        assert(inverse_word(wa) =~= seq![adi] + inverse_word(wap));
        assert(inverse_word(wa) + dl + wa =~= seq![adi] + inner + seq![ad]);

        // IH:  inner ≡ wbap·dl
        lemma_IIb(mm, n, m, ap);
        assert(equiv_in_presentation(p, inner, wbap + dl));

        // conjugate by a_d:  a_d⁻¹·inner·a_d ≡ a_d⁻¹·(wbap·dl)·a_d
        lemma_equiv_concat_right(p, seq![adi], inner, wbap + dl);
        lemma_equiv_concat_left(p, seq![adi] + inner, seq![adi] + (wbap + dl), seq![ad]);
        let x1 = (seq![adi] + (wbap + dl)) + seq![ad];
        assert(equiv_in_presentation(p, seq![adi] + inner + seq![ad], x1));

        // a_d (hence a_d⁻¹) commutes with the b-word wbap
        lemma_w_c_gens_in_block(b_base(nk, n), n, m, ap);
        lemma_a_commutes_b_word(mm, n, m, d, wbap);        // commutes([a_d], wbap)
        lemma_w_c_valid(b_base(nk, n), n, m, ap, ng);      // word_valid(wbap, ng)
        assert(word_valid(seq![ad], ng)) by { assert(seq![ad][0] == ad); }
        assert(word_valid(seq![adi], ng)) by { assert(seq![adi][0] == adi); }
        lemma_commutes_sym(p, seq![ad], wbap);             // commutes(wbap, [a_d])
        lemma_commutes_inv_right(p, wbap, seq![ad]);       // commutes(wbap, [a_d⁻¹])
        lemma_commutes_sym(p, wbap, seq![adi]);            // commutes([a_d⁻¹], wbap)
        // x1 =~= ([a_d⁻¹]·wbap)·(dl·a_d) ; commute → (wbap·[a_d⁻¹])·(dl·a_d)
        lemma_equiv_concat_left(p, seq![adi] + wbap, wbap + seq![adi], dl + seq![ad]);
        let x2 = (wbap + seq![adi]) + (dl + seq![ad]);
        assert(x1 =~= (seq![adi] + wbap) + (dl + seq![ad]));
        assert(equiv_in_presentation(p, x1, x2));

        // a_d⁻¹·dl·a_d ≡ b_d·dl  (lemma_a_conj_d)
        lemma_a_conj_d(mm, n, m, d);
        assert(seq![bl, Symbol::Gen(d_idx(nk, n))] =~= seq![bl] + dl);
        assert(equiv_in_presentation(p, seq![adi] + dl + seq![ad], seq![bl] + dl));
        // x2 =~= wbap·(a_d⁻¹·dl·a_d) ; rewrite → wbap·(b_d·dl)
        lemma_equiv_concat_right(p, wbap, seq![adi] + dl + seq![ad], seq![bl] + dl);
        let x3 = wbap + (seq![bl] + dl);
        assert(x2 =~= wbap + (seq![adi] + dl + seq![ad]));
        assert(equiv_in_presentation(p, x2, x3));
        // x3 =~= (wbap·b_d)·dl = wb·dl
        assert(x3 =~= (wbap + seq![bl]) + dl);
        assert(x3 =~= wb + dl);

        // chain:  LHS ≡ x1 ≡ x2 ≡ x3 = wb·dl
        lemma_equiv_transitive(p, seq![adi] + inner + seq![ad], x1, x2);
        lemma_equiv_transitive(p, seq![adi] + inner + seq![ad], x2, x3);
        assert(inverse_word(wa) + dl + wa =~= seq![adi] + inner + seq![ad]);
        assert(wb + dl =~= x3);
    }
}

// ----------------------------------------------------------------------------
// Sub-brick 4 — (II):  p⁻¹ · t_α · p ≡ t_α · w_α(b) · d  in H₃.
// `p` commutes with `w_α(a)` (φ_l: p↦p), and `p⁻¹ t p ≡ t d`; combine with (IIa)/(IIb).
// ----------------------------------------------------------------------------

/// `p` commutes with the single a-stable-letter `a_l` (φ_l tail: `a_l⁻¹ p a_l ≡ p`).
pub proof fn lemma_p_commutes_a_letter(mm: ModMachine, n: nat, m: nat, l: nat)
    requires 1 <= l <= 2 * n,
    ensures
        commutes(h3_pres(mm, n, m), seq![Symbol::Gen(p_idx(g_m(mm).num_generators, n))],
            seq![Symbol::Gen(a_idx(g_m(mm).num_generators, n, l))]),
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    lemma_h3_pres_valid(mm, n, m);
    lemma_h3_num_generators(mm, n, m);
    lemma_g_m_num_generators(mm);
    let ng = h3_num_gens(nk, n);
    let ti: int = (n + 3) as int;                 // phi_assoc tail (p,p)
    assert(phi_assoc(nk, n, m, l)[ti].0 == seq![Symbol::Gen(p_idx(nk, n))]);
    assert(phi_assoc(nk, n, m, l)[ti].1 == seq![Symbol::Gen(p_idx(nk, n))]);
    lemma_phi_d_conj_in_h3(mm, n, m, l, ti);      // a_l⁻¹ p a_l ≡ p
    let al = Symbol::Gen(a_idx(nk, n, l));
    let ali = Symbol::Inv(a_idx(nk, n, l));
    let pg: Word = seq![Symbol::Gen(p_idx(nk, n))];
    assert(a_idx(nk, n, l) < ng);
    assert(p_idx(nk, n) < ng);
    assert(is_inverse_pair(al, ali));
    assert(symbol_valid(al, ng));
    assert(word_valid(pg, ng)) by { assert(pg[0] == Symbol::Gen(p_idx(nk, n))); }
    assert(word_valid(seq![al], ng)) by { assert(seq![al][0] == al); }
    assert(equiv_in_presentation(p, seq![ali] + pg + seq![al], pg));
    lemma_commute_from_conj(p, al, ali, pg);      // commutes([a_l], [p])
    lemma_commutes_sym(p, seq![al], pg);          // commutes([p], [a_l])
}

/// `p` commutes with the whole a-word `w_α(a)`.
pub proof fn lemma_p_commutes_wa(mm: ModMachine, n: nat, m: nat, alpha: nat)
    requires numbers_word(n, m, alpha), 2 * n < m,
    ensures
        commutes(h3_pres(mm, n, m), seq![Symbol::Gen(p_idx(g_m(mm).num_generators, n))],
            w_a(g_m(mm).num_generators, n, m, alpha)),
    decreases alpha,
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    let pg: Word = seq![Symbol::Gen(p_idx(nk, n))];
    if alpha == 0 {
        lemma_commutes_empty_right(p, pg);
        assert(w_a(nk, n, m, alpha) =~= empty_word());
    } else {
        assert(m > 1);
        let ap = alpha / m;
        let d = alpha % m;
        assert(1 <= d <= 2 * n && numbers_word(n, m, ap));
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
        let adw: Word = seq![Symbol::Gen(a_idx(nk, n, d))];
        lemma_p_commutes_wa(mm, n, m, ap);                  // commutes(pg, w_a(ap))
        lemma_p_commutes_a_letter(mm, n, m, d);             // commutes(pg, [a_d])
        lemma_commutes_concat_right(p, pg, w_a(nk, n, m, ap), adw);
        assert(w_a(nk, n, m, alpha) =~= w_a(nk, n, m, ap) + adw);
    }
}

/// `w_α(a)` is valid over any generator count covering the a-block.
pub proof fn lemma_w_a_valid(nk: nat, n: nat, m: nat, alpha: nat, ng: nat)
    requires numbers_word(n, m, alpha), a_base(nk, n) + 2 * n <= ng, 2 * n < m,
    ensures word_valid(w_a(nk, n, m, alpha), ng),
    decreases alpha,
{
    if alpha == 0 || m <= 1 {
        assert(w_a(nk, n, m, alpha) =~= empty_word());
    } else {
        let d = alpha % m;
        assert(1 <= d <= 2 * n);
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
        lemma_w_a_valid(nk, n, m, alpha / m, ng);
        let pref = w_a(nk, n, m, alpha / m);
        let last: Word = seq![Symbol::Gen(a_idx(nk, n, d))];
        assert(a_idx(nk, n, d) < ng);                  // a_base+(d-1) < a_base+2n ≤ ng
        assert(word_valid(last, ng)) by { assert(last[0] == Symbol::Gen(a_idx(nk, n, d))); }
        assert(w_a(nk, n, m, alpha) =~= pref + last);
        lemma_concat_word_valid(pref, last, ng);
    }
}

/// **Sub-brick 4 — (II).** `p⁻¹ · t_α · p ≡ t_α · w_α(b) · d` in `h3_pres`. Combine (IIa)/(IIb)
/// with `p` commuting past `w_α(a)` and `p⁻¹ t p ≡ t d`.
pub proof fn lemma_II(mm: ModMachine, n: nat, m: nat, alpha: nat)
    requires numbers_word(n, m, alpha), 2 * n < m,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            seq![Symbol::Inv(p_idx(g_m(mm).num_generators, n))]
                + config_word(alpha, 0)
                + seq![Symbol::Gen(p_idx(g_m(mm).num_generators, n))],
            config_word(alpha, 0)
                + w_b(b_base(g_m(mm).num_generators, n), n, m, alpha)
                + seq![Symbol::Gen(d_idx(g_m(mm).num_generators, n))]),
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    lemma_g_m_num_generators(mm);
    lemma_h3_num_generators(mm, n, m);
    lemma_h3_pres_valid(mm, n, m);
    let ng = h3_num_gens(nk, n);

    let pg: Word = seq![Symbol::Gen(p_idx(nk, n))];
    let pgi: Word = seq![Symbol::Inv(p_idx(nk, n))];
    let t: Word = seq![Symbol::Gen(0)];
    let dl: Word = seq![Symbol::Gen(d_idx(nk, n))];
    let wa = w_a(nk, n, m, alpha);
    let wai = inverse_word(wa);
    let wb = w_b(b_base(nk, n), n, m, alpha);
    let cfg = config_word(alpha, 0);

    // validities
    assert(word_valid(pg, ng)) by { assert(pg[0] == Symbol::Gen(p_idx(nk, n))); }
    assert(word_valid(pgi, ng)) by { assert(pgi[0] == Symbol::Inv(p_idx(nk, n))); }
    lemma_w_a_valid(nk, n, m, alpha, ng);              // word_valid(wa, ng)
    lemma_inverse_word_valid(wa, ng);                 // word_valid(wai, ng)
    lemma_inverse_singleton(Symbol::Gen(p_idx(nk, n)));
    assert(pg =~= Seq::new(1, |_i: int| Symbol::Gen(p_idx(nk, n))));
    assert(Seq::new(1, |_i: int| inverse_symbol(Symbol::Gen(p_idx(nk, n)))) =~= pgi);
    assert(inverse_word(pg) =~= pgi);

    // ---- atoms ----
    lemma_IIa(mm, n, m, alpha);                        // wai·t·wa ≡ cfg
    let iia = wai + t + wa;
    assert(equiv_in_presentation(p, iia, cfg));
    lemma_equiv_symmetric(p, iia, cfg);               // cfg ≡ wai·t·wa  (need word_valid(iia))
    lemma_IIb(mm, n, m, alpha);                        // wai·dl·wa ≡ wb·dl
    let iib = wai + dl + wa;
    assert(equiv_in_presentation(p, iib, wb + dl));

    // p⁻¹ t p ≡ t d  (lift lemma_h2_p_conjugates_t)
    lemma_h2_p_conjugates_t(mm, n);
    lemma_h2_in_h3(mm, n, m, pgi + t + pg, td_word(nk, n));
    assert(td_word(nk, n) =~= t + dl);
    assert(equiv_in_presentation(p, pgi + t + pg, t + dl));   // A_ptp

    // p commutes with wa  ⟹  c1: pgi·wai ≡ wai·pgi ;  c2: wa·pg ≡ pg·wa
    lemma_p_commutes_wa(mm, n, m, alpha);             // commutes(pg, wa)
    lemma_commutes_sym(p, pg, wa);                    // commutes(wa, pg): wa·pg ≡ pg·wa  (c2)
    lemma_commutes_inv_right(p, pg, wa);              // commutes(pg, wai)
    lemma_commutes_sym(p, pg, wai);                   // commutes(wai, pg)
    lemma_commutes_inv_right(p, wai, pg);             // commutes(wai, pgi)  (inverse_word(pg)=pgi)
    lemma_commutes_sym(p, wai, pgi);                  // commutes(pgi, wai): pgi·wai ≡ wai·pgi  (c1)

    // ---- the chain ----
    // L = pgi·cfg·pg
    let lhs = pgi + cfg + pg;
    // step 2: cfg → wai·t·wa
    lemma_equiv_concat_right(p, pgi, cfg, iia);
    lemma_equiv_concat_left(p, pgi + cfg, pgi + iia, pg);
    let e0 = (pgi + iia) + pg;
    assert(equiv_in_presentation(p, lhs, e0));        // L ≡ pgi·(wai·t·wa)·pg

    // step 3: commute p past wa →  wai·(pgi·t·pg)·wa
    // e0 =~= (pgi+wai) + t + (wa+pg)  ;  target m3 =~= (wai+pgi) + t + (pg+wa)
    let m3 = ((wai + pgi) + t) + (pg + wa);
    lemma_equiv_concat_left(p, pgi + wai, wai + pgi, t + (wa + pg));   // (pgi·wai)·(t·(wa·pg)) ≡ (wai·pgi)·(t·(wa·pg))
    lemma_equiv_concat_right(p, (wai + pgi) + t, wa + pg, pg + wa);    // ((wai·pgi)·t)·(wa·pg) ≡ ((wai·pgi)·t)·(pg·wa)
    assert(e0 =~= (pgi + wai) + (t + (wa + pg)));
    assert((wai + pgi) + (t + (wa + pg)) =~= ((wai + pgi) + t) + (wa + pg));
    lemma_equiv_transitive(p, e0, (wai + pgi) + (t + (wa + pg)), m3);   // e0 ≡ m3
    lemma_equiv_transitive(p, lhs, e0, m3);           // L ≡ m3

    // step 4: pgi·t·pg → t·dl  inside wai·(_)·wa
    // m3 =~= wai·(pgi·t·pg)·wa ; rewrite → wai·(t·dl)·wa
    let m5 = (wai + (t + dl)) + wa;
    lemma_equiv_concat_right(p, wai, pgi + t + pg, t + dl);
    lemma_equiv_concat_left(p, wai + (pgi + t + pg), wai + (t + dl), wa);
    assert(m3 =~= (wai + (pgi + t + pg)) + wa);
    assert(equiv_in_presentation(p, m3, m5));          // m3 ≡ wai·(t·dl)·wa

    // step 5: wai·(t·dl)·wa ≡ cfg·wb·dl
    // N = (wai·t·wa)·(wai·dl·wa) ; N ≡ m5 (cancel wa·wai) and N ≡ cfg·(wb·dl)
    let nN = iia + iib;
    // N ≡ m5 :  N =~= (wai+t)·(wa·wai)·(dl·wa) ; wa·wai ≡ ε
    lemma_word_inverse_right(p, wa);                   // wa·wai ≡ ε
    lemma_equiv_concat_left(p, wa + wai, empty_word(), dl + wa);   // (wa·wai)·(dl·wa) ≡ ε·(dl·wa)
    lemma_equiv_concat_right(p, wai + t, (wa + wai) + (dl + wa), dl + wa);
    assert(nN =~= (wai + t) + ((wa + wai) + (dl + wa)));
    assert((wai + t) + (empty_word() + (dl + wa)) =~= m5);
    assert(equiv_in_presentation(p, nN, m5));          // N ≡ m5
    lemma_equiv_symmetric(p, nN, m5);                  // m5 ≡ N  (need word_valid(nN))
    // N ≡ cfg·(wb·dl)
    lemma_equiv_concat_left(p, iia, cfg, iib);         // (wai·t·wa)·iib ≡ cfg·iib
    lemma_equiv_concat_right(p, cfg, iib, wb + dl);    // cfg·iib ≡ cfg·(wb·dl)
    lemma_equiv_transitive(p, nN, cfg + iib, cfg + (wb + dl));
    assert(equiv_in_presentation(p, nN, cfg + (wb + dl)));

    // assemble:  L ≡ m3 ≡ m5 ≡ N ≡ cfg·wb·dl
    lemma_equiv_transitive(p, lhs, m3, m5);
    lemma_equiv_transitive(p, lhs, m5, nN);
    lemma_equiv_transitive(p, lhs, nN, cfg + (wb + dl));
    assert(cfg + (wb + dl) =~= cfg + wb + dl);
    assert(lhs =~= pgi + cfg + pg);
}

/// Equivalence respects word inverse: `a ≡ b ⟹ a⁻¹ ≡ b⁻¹`.
pub proof fn lemma_equiv_inverse(p: Presentation, a: Word, b: Word)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        equiv_in_presentation(p, a, b),
    ensures equiv_in_presentation(p, inverse_word(a), inverse_word(b)),
{
    let ng = p.num_generators;
    let ai = inverse_word(a);
    let bi = inverse_word(b);
    lemma_inverse_word_valid(a, ng);
    lemma_inverse_word_valid(b, ng);
    // ai·b ≡ ai·a ≡ ε
    lemma_equiv_symmetric(p, a, b);                       // b ≡ a
    lemma_equiv_concat_right(p, ai, b, a);                // ai·b ≡ ai·a
    lemma_word_inverse_left(p, a);                        // ai·a ≡ ε
    lemma_equiv_transitive(p, ai + b, ai + a, empty_word());   // ai·b ≡ ε
    // ai ≡ ai·(b·bi) =~= (ai·b)·bi ≡ ε·bi =~= bi
    lemma_word_inverse_right(p, b);                       // b·bi ≡ ε
    lemma_equiv_symmetric(p, b + bi, empty_word());       // ε ≡ b·bi
    lemma_equiv_concat_right(p, ai, empty_word(), b + bi);     // ai·ε ≡ ai·(b·bi)
    assert(ai + empty_word() =~= ai);
    assert(equiv_in_presentation(p, ai, ai + (b + bi)));
    lemma_equiv_concat_left(p, ai + b, empty_word(), bi);      // (ai·b)·bi ≡ ε·bi
    assert(empty_word() + bi =~= bi);
    assert(ai + (b + bi) =~= (ai + b) + bi);
    assert(equiv_in_presentation(p, ai + (b + bi), bi));
    lemma_equiv_transitive(p, ai, ai + (b + bi), bi);
}

// ----------------------------------------------------------------------------
// Sub-brick 5 — (III):  (α,0)∈H₀(M)  ⟹  w_α(c) ≡ 1  in H₃   (THE HEADLINE).
// k-conjugation is DIRECT in h3_pres = hnn_presentation(psi_data).
// ----------------------------------------------------------------------------

/// `k⁻¹ · b_j · k ≡ b_j c_j` in `h3_pres` (ψ bc-block, 1 ≤ j ≤ n).
pub proof fn lemma_psi_bcblock_conj(mm: ModMachine, n: nat, m: nat, j: nat)
    requires 1 <= j <= n,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            seq![Symbol::Inv(k_top(g_m(mm).num_generators, n))]
                + seq![Symbol::Gen(b_idx(g_m(mm).num_generators, n, j))]
                + seq![Symbol::Gen(k_top(g_m(mm).num_generators, n))],
            seq![Symbol::Gen(b_idx(g_m(mm).num_generators, n, j)),
                 Symbol::Gen(c_idx(g_m(mm).num_generators, j))]),
{
    let nk = g_m(mm).num_generators;
    lemma_g_m_num_generators(mm);
    let base = h3_upto(mm, n, m, (2 * n) as nat);
    let data = HNNData { base, associations: psi_assoc(mm, n) };
    assert(h3_pres(mm, n, m) == hnn_presentation(data));
    lemma_h3_upto_valid(mm, n, m, (2 * n) as nat);
    lemma_h3_upto_num_generators(mm, n, m, (2 * n) as nat);     // base.num = nk+4n+2
    assert(base.num_generators >= nk + 2 * n + 2);
    lemma_psi_assoc_valid(mm, n, base.num_generators);
    lemma_hnn_data_valid_from(data, base.num_generators);

    // index nu+j into psi_assoc = ublock ++ [d] ++ bcblock ++ [p]
    let up = psi_ublock(mm);
    let dpair: Seq<(Word, Word)> = seq![(seq![Symbol::Gen(d_idx(nk, n))], seq![Symbol::Gen(d_idx(nk, n))])];
    let bc = psi_bcblock(nk, n);
    let ppair: Seq<(Word, Word)> = seq![(seq![Symbol::Gen(p_idx(nk, n))], seq![Symbol::Gen(p_idx(nk, n))])];
    let nu = g_subgens(mm).len();
    assert(up.len() == nu);
    assert(bc.len() == n);
    assert(psi_assoc(mm, n) =~= ((up + dpair) + bc) + ppair);
    let idx: int = (nu + j) as int;
    // peel: idx ∈ [nu+1, nu+n] lands in bc at idx-(nu+1) = j-1
    assert(((up + dpair) + bc)[idx] == bc[idx - (nu + 1)]);
    assert(idx - (nu + 1) == (j - 1));
    assert(psi_assoc(mm, n)[idx] == bc[(j - 1) as int]);
    let bj = Symbol::Gen(b_idx(nk, n, j));
    let cj = Symbol::Gen(c_idx(nk, j));
    assert(bc[(j - 1) as int] == (seq![bj], seq![bj, cj]));
    assert(psi_assoc(mm, n)[idx].0 == seq![bj]);
    assert(psi_assoc(mm, n)[idx].1 == seq![bj, cj]);

    lemma_hnn_conjugation(data, idx);
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    lemma_h3_k_stable_letter(mm, n, m);
    assert(st == Symbol::Gen(k_top(nk, n)));
    assert(si == Symbol::Inv(k_top(nk, n)));
    let lhs = Seq::new(1, |_q: int| si) + data.associations[idx].0 + Seq::new(1, |_q: int| st);
    assert(lhs =~= seq![Symbol::Inv(k_top(nk, n))] + seq![bj] + seq![Symbol::Gen(k_top(nk, n))]);
    assert(data.associations[idx].1 =~= seq![bj, cj]);
}

/// `k⁻¹ · b_d · k ≡ bc_letter(d)` for any digit-letter `b_d = alphabet_letter(b_base,n,d)`,
/// 1 ≤ d ≤ 2n. Positive digit from `lemma_psi_bcblock_conj`; inverse digit via `lemma_equiv_inverse`.
pub proof fn lemma_k_conj_b_letter(mm: ModMachine, n: nat, m: nat, d: nat)
    requires 1 <= d <= 2 * n,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            seq![Symbol::Inv(k_top(g_m(mm).num_generators, n))]
                + seq![alphabet_letter(b_base(g_m(mm).num_generators, n), n, d)]
                + seq![Symbol::Gen(k_top(g_m(mm).num_generators, n))],
            bc_letter(b_base(g_m(mm).num_generators, n), c_base(g_m(mm).num_generators), n, d)),
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    lemma_h3_pres_valid(mm, n, m);
    lemma_h3_num_generators(mm, n, m);
    lemma_g_m_num_generators(mm);
    let ng = h3_num_gens(nk, n);
    let kt = k_top(nk, n);
    assert(kt < ng);
    if d <= n {
        lemma_psi_bcblock_conj(mm, n, m, d);
        assert(alphabet_letter(b_base(nk, n), n, d) == Symbol::Gen(b_idx(nk, n, d)));
        assert(bc_letter(b_base(nk, n), c_base(nk), n, d)
            =~= seq![Symbol::Gen(b_idx(nk, n, d)), Symbol::Gen(c_idx(nk, d))]);
    } else {
        let jj = (d - n) as nat;
        assert(1 <= jj <= n);
        lemma_psi_bcblock_conj(mm, n, m, jj);           // [k⁻¹]·b_jj·[k] ≡ [b_jj, c_jj]
        let bjj = Symbol::Gen(b_idx(nk, n, jj));
        let cjj = Symbol::Gen(c_idx(nk, jj));
        let aA: Word = seq![Symbol::Inv(kt)] + seq![bjj] + seq![Symbol::Gen(kt)];
        let bB: Word = seq![bjj, cjj];
        // validities
        assert(b_idx(nk, n, jj) < ng);
        assert(c_idx(nk, jj) < ng);
        assert(word_valid(aA, ng)) by {
            assert forall|q: int| 0 <= q < aA.len() implies symbol_valid(#[trigger] aA[q], ng) by {
                if q == 0 { assert(aA[0] == Symbol::Inv(kt)); }
                else if q == 1 { assert(aA[1] == bjj); }
                else { assert(aA[2] == Symbol::Gen(kt)); }
            }
        }
        assert(word_valid(bB, ng)) by {
            assert forall|q: int| 0 <= q < bB.len() implies symbol_valid(#[trigger] bB[q], ng) by {
                if q == 0 { assert(bB[0] == bjj); } else { assert(bB[1] == cjj); }
            }
        }
        lemma_equiv_inverse(p, aA, bB);                 // inverse_word(aA) ≡ inverse_word(bB)
        // inverse_word(aA) = [k⁻¹, b_jj⁻¹, k]  =  [k⁻¹] + [alphabet_letter(d)] + [k]
        lemma_inverse_concat(seq![Symbol::Inv(kt)] + seq![bjj], seq![Symbol::Gen(kt)]);
        lemma_inverse_concat(seq![Symbol::Inv(kt)], seq![bjj]);
        lemma_inverse_singleton(Symbol::Gen(kt));
        assert(seq![Symbol::Gen(kt)] =~= Seq::new(1, |_i: int| Symbol::Gen(kt)));
        assert(inverse_word(seq![Symbol::Gen(kt)]) =~= seq![Symbol::Inv(kt)]);
        lemma_inverse_singleton(Symbol::Inv(kt));
        assert(seq![Symbol::Inv(kt)] =~= Seq::new(1, |_i: int| Symbol::Inv(kt)));
        assert(inverse_word(seq![Symbol::Inv(kt)]) =~= seq![Symbol::Gen(kt)]);
        lemma_inverse_singleton(bjj);
        assert(seq![bjj] =~= Seq::new(1, |_i: int| bjj));
        assert(inverse_word(seq![bjj]) =~= seq![Symbol::Inv(b_idx(nk, n, jj))]);
        assert(alphabet_letter(b_base(nk, n), n, d) == Symbol::Inv(b_idx(nk, n, jj)));
        assert(inverse_word(aA) =~= seq![Symbol::Inv(kt)]
            + seq![alphabet_letter(b_base(nk, n), n, d)] + seq![Symbol::Gen(kt)]);
        // inverse_word(bB) = [c_jj⁻¹, b_jj⁻¹] = bc_letter(d)
        assert(bB =~= seq![bjj] + seq![cjj]);
        lemma_inverse_concat(seq![bjj], seq![cjj]);
        lemma_inverse_singleton(cjj);
        assert(seq![cjj] =~= Seq::new(1, |_i: int| cjj));
        assert(inverse_word(seq![cjj]) =~= seq![Symbol::Inv(c_idx(nk, jj))]);
        assert(inverse_word(bB) =~= seq![Symbol::Inv(c_idx(nk, jj)), Symbol::Inv(b_idx(nk, n, jj))]);
        assert(bc_letter(b_base(nk, n), c_base(nk), n, d)
            =~= seq![Symbol::Inv(c_idx(nk, jj)), Symbol::Inv(b_idx(nk, n, jj))]);
    }
}

/// **Stage A — `k⁻¹ · w_α(b) · k ≡ w_α(bc)`** in `h3_pres`, by induction on α's digits
/// (`lemma_conj_distributes` + per-letter `lemma_k_conj_b_letter`).
pub proof fn lemma_k_conj_wb(mm: ModMachine, n: nat, m: nat, alpha: nat)
    requires numbers_word(n, m, alpha), 2 * n < m,
    ensures
        equiv_in_presentation(h3_pres(mm, n, m),
            seq![Symbol::Inv(k_top(g_m(mm).num_generators, n))]
                + w_b(b_base(g_m(mm).num_generators, n), n, m, alpha)
                + seq![Symbol::Gen(k_top(g_m(mm).num_generators, n))],
            w_bc(b_base(g_m(mm).num_generators, n), c_base(g_m(mm).num_generators), n, m, alpha)),
    decreases alpha,
{
    let nk = g_m(mm).num_generators;
    let p = h3_pres(mm, n, m);
    lemma_h3_pres_valid(mm, n, m);
    lemma_h3_num_generators(mm, n, m);
    lemma_g_m_num_generators(mm);
    let ng = h3_num_gens(nk, n);
    let kt = k_top(nk, n);
    let ki: Word = seq![Symbol::Inv(kt)];
    let ks: Word = seq![Symbol::Gen(kt)];
    let wb = w_b(b_base(nk, n), n, m, alpha);
    let wbc = w_bc(b_base(nk, n), c_base(nk), n, m, alpha);
    if alpha == 0 || m <= 1 {
        assert(wb =~= empty_word());
        assert(wbc =~= empty_word());
        assert(ki + wb + ks =~= seq![Symbol::Inv(kt), Symbol::Gen(kt)]);
        assert(kt < ng);
        assert(is_inverse_pair(Symbol::Inv(kt), Symbol::Gen(kt)));
        lemma_cancel_pair_equiv_empty(p, Symbol::Inv(kt), Symbol::Gen(kt));
        // [k⁻¹, k] ≡ ε = wbc
    } else {
        assert(m > 1);
        let ap = alpha / m;
        let d = alpha % m;
        assert(1 <= d <= 2 * n && numbers_word(n, m, ap));
        vstd::arithmetic::div_mod::lemma_div_decreases(alpha as int, m as int);
        let bld: Word = seq![alphabet_letter(b_base(nk, n), n, d)];
        let bcd = bc_letter(b_base(nk, n), c_base(nk), n, d);
        let wbap = w_b(b_base(nk, n), n, m, ap);
        let wbcap = w_bc(b_base(nk, n), c_base(nk), n, m, ap);
        assert(wb =~= wbap + bld);
        assert(wbc =~= wbcap + bcd);
        // distribute k over wb = wbap·bld
        assert(is_inverse_pair(Symbol::Gen(kt), Symbol::Inv(kt)));
        assert(kt < ng);
        let kk2: Word = seq![Symbol::Gen(kt), Symbol::Inv(kt)];
        assert(word_valid(kk2, ng)) by {
            assert forall|q: int| 0 <= q < kk2.len() implies symbol_valid(#[trigger] kk2[q], ng) by {
                if q == 0 { assert(kk2[0] == Symbol::Gen(kt)); } else { assert(kk2[1] == Symbol::Inv(kt)); }
            }
        }
        lemma_conj_distributes(p, Symbol::Inv(kt), Symbol::Gen(kt), wbap, bld);
        // ki·(wbap·bld)·ks ≡ (ki·wbap·ks)·(ki·bld·ks)
        lemma_k_conj_wb(mm, n, m, ap);                  // ki·wbap·ks ≡ wbcap
        lemma_k_conj_b_letter(mm, n, m, d);             // ki·bld·ks ≡ bcd
        lemma_equiv_concat_left(p, ki + wbap + ks, wbcap, ki + bld + ks);
        lemma_equiv_concat_right(p, wbcap, ki + bld + ks, bcd);
        lemma_equiv_transitive(p, (ki + wbap + ks) + (ki + bld + ks), wbcap + (ki + bld + ks),
            wbcap + bcd);
        // chain with the distribute step
        assert(ki + (wbap + bld) + ks =~= ki + wb + ks);
        assert(equiv_in_presentation(p, ki + wb + ks, (ki + wbap + ks) + (ki + bld + ks)));
        lemma_equiv_transitive(p, ki + wb + ks, (ki + wbap + ks) + (ki + bld + ks), wbcap + bcd);
        assert(wbcap + bcd =~= wbc);
    }
}

} // verus!
