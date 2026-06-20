use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::benign::{in_generated_subgroup, factors_from_generators, is_generator_or_inverse, concat_all};
use crate::benign::{apply_embedding, lemma_apply_embedding_concat, lemma_identity_in_generated_subgroup,
    lemma_generator_in_generated_subgroup};

verus! {

//  ============================================================
//  kill_t kills the residue-class subgroup (for the (ii)⊆ assembly).
//  ============================================================

//  kill_t fixes any signed x/y power (t doesn't occur).
pub proof fn lemma_kill_t_signed_power(i: nat, a: int)
    requires
        i == 1 || i == 2,
    ensures
        apply_embedding(kill_t_images(), signed_power(i, a)) =~= signed_power(i, a),
{
    if a >= 0 {
        lemma_kill_t_sympower(Symbol::Gen(i), a as nat);
    } else {
        lemma_kill_t_sympower(Symbol::Inv(i), (-a) as nat);
    }
}

//  kill_t sends every (signed) config word to the identity:  kill_t(t(r,s)) ≡ 1.
pub proof fn lemma_kill_t_config_signed_trivial(r: int, s: int)
    ensures
        equiv_in_presentation(base_A(), apply_embedding(kill_t_images(), config_word_signed(r, s)), empty_word()),
{
    let p = base_A();
    lemma_base_A_valid();
    let imgs = kill_t_images();
    reveal_with_fuel(apply_embedding, 2);
    let a_ = signed_power(2, -s);
    let b_ = signed_power(1, -r);
    let c_: Word = seq![Symbol::Gen(0)];
    let d_ = signed_power(1, r);
    let e_ = signed_power(2, s);
    lemma_apply_embedding_concat(imgs, a_ + b_ + c_ + d_, e_);
    lemma_apply_embedding_concat(imgs, a_ + b_ + c_, d_);
    lemma_apply_embedding_concat(imgs, a_ + b_, c_);
    lemma_apply_embedding_concat(imgs, a_, b_);
    lemma_kill_t_signed_power(2, -s);
    lemma_kill_t_signed_power(1, -r);
    lemma_kill_t_signed_power(1, r);
    lemma_kill_t_signed_power(2, s);
    assert(apply_embedding(imgs, c_) =~= empty_word());
    assert(apply_embedding(imgs, config_word_signed(r, s)) =~= a_ + b_ + d_ + e_);
    let v = d_ + e_;
    lemma_inverse_word_concat(d_, e_);
    lemma_signed_power_inverse(1, r);
    lemma_signed_power_inverse(2, s);
    assert(inverse_word(v) =~= a_ + b_);
    assert(apply_embedding(imgs, config_word_signed(r, s)) =~= inverse_word(v) + v);
    lemma_word_inverse_left(p, v);
    assert(concat(inverse_word(v), v) =~= inverse_word(v) + v);
}

//  If kill_t kills every factor, it kills their product.
pub proof fn lemma_kill_t_concat_all_trivial(factors: Seq<Word>)
    requires
        forall|k: int| 0 <= k < factors.len() ==>
            equiv_in_presentation(base_A(), apply_embedding(kill_t_images(), #[trigger] factors[k]), empty_word()),
    ensures
        equiv_in_presentation(base_A(), apply_embedding(kill_t_images(), concat_all(factors)), empty_word()),
    decreases factors.len(),
{
    let p = base_A();
    lemma_base_A_valid();
    let imgs = kill_t_images();
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
        reveal_with_fuel(apply_embedding, 2);
        assert(apply_embedding(imgs, empty_word()) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert forall|k: int| 0 <= k < rest.len() implies
            equiv_in_presentation(p, apply_embedding(imgs, #[trigger] rest[k]), empty_word()) by {
            assert(rest[k] == factors[k + 1]);
        }
        lemma_kill_t_concat_all_trivial(rest);                  // kill_t(concat_all(rest)) ≡ ε
        assert(concat_all(factors) =~= concat(first, concat_all(rest)));
        lemma_apply_embedding_concat(imgs, first, concat_all(rest));
        assert(equiv_in_presentation(p, apply_embedding(imgs, first), empty_word())) by {
            assert(first == factors[0]);
        }
        let aa = apply_embedding(imgs, first);
        let bb = apply_embedding(imgs, concat_all(rest));
        lemma_equiv_concat_left(p, aa, empty_word(), bb);       // aa·bb ≡ ε·bb
        assert(empty_word() + bb =~= bb);
        lemma_equiv_transitive(p, aa + bb, bb, empty_word());   // aa·bb ≡ bb ≡ ε
        assert(apply_embedding(imgs, concat_all(factors)) =~= aa + bb);
    }
}

//  ============================================================
//  (ii)⊆ via exponent counting (gexp respects equiv — already proven).
//  ============================================================

//  A (signed) config word has zero x- and y-exponent (the x's and y's cancel; only t remains).
pub proof fn lemma_gexp_config_signed_zero(i: nat, r: int, s: int)
    requires
        i == 1 || i == 2,
    ensures
        gexp(i, config_word_signed(r, s)) == 0,
{
    let a_ = signed_power(2, -s);
    let b_ = signed_power(1, -r);
    let c_: Word = seq![Symbol::Gen(0)];
    let d_ = signed_power(1, r);
    let e_ = signed_power(2, s);
    lemma_gexp_concat(i, a_ + b_ + c_ + d_, e_);
    lemma_gexp_concat(i, a_ + b_ + c_, d_);
    lemma_gexp_concat(i, a_ + b_, c_);
    lemma_gexp_concat(i, a_, b_);
    lemma_gexp_signed_power(2, i, -s);
    lemma_gexp_signed_power(1, i, -r);
    lemma_gexp_signed_power(1, i, r);
    lemma_gexp_signed_power(2, i, s);
    lemma_gexp_singleton(i, Symbol::Gen(0));
}

//  gexp(i,·) of a product of factors, each with gexp(i)=0, is 0.
pub proof fn lemma_gexp_concat_all_zero(i: nat, factors: Seq<Word>)
    requires
        forall|k: int| 0 <= k < factors.len() ==> gexp(i, #[trigger] factors[k]) == 0,
    ensures
        gexp(i, concat_all(factors)) == 0,
    decreases factors.len(),
{
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert forall|k: int| 0 <= k < rest.len() implies gexp(i, #[trigger] rest[k]) == 0 by {
            assert(rest[k] == factors[k + 1]);
        }
        lemma_gexp_concat_all_zero(i, rest);
        assert(concat_all(factors) =~= concat(first, concat_all(rest)));
        lemma_gexp_concat(i, first, concat_all(rest));
        assert(gexp(i, first) == 0) by { assert(first == factors[0]); }
    }
}

//  A residue gen (config word or its inverse) has zero x/y-exponent.
pub proof fn lemma_gexp_residue_gen_zero(i: nat, ires: int, jres: int, m: int, w: Word)
    requires
        i == 1 || i == 2,
        is_residue_gen(ires, jres, m, w),
    ensures
        gexp(i, w) == 0,
{
    let rs = choose|r: int, s: int| #![trigger config_word_signed(r, s)]
        (r - ires) % m == 0 && (s - jres) % m == 0
        && (w == config_word_signed(r, s) || w == inverse_word(config_word_signed(r, s)));
    let r = rs.0;
    let s = rs.1;
    assert(w == config_word_signed(r, s) || w == inverse_word(config_word_signed(r, s)));
    lemma_gexp_config_signed_zero(i, r, s);
    if w != config_word_signed(r, s) {
        lemma_gexp_inverse(i, config_word_signed(r, s));   // gexp(i, t(r,s)⁻¹) = -gexp(i, t(r,s)) = 0
    }
}

//  Every element of the residue subgroup has zero x/y-exponent.
pub proof fn lemma_gexp_residue_subgroup_zero(i: nat, ires: int, jres: int, m: int, u: Word)
    requires
        i == 1 || i == 2,
        in_residue_class(ires, jres, m, u),
    ensures
        gexp(i, u) == 0,
{
    let pred = residue_pred(ires, jres, m);
    let factors = choose|factors: Seq<Word>| #![trigger factors_from_pred(pred, factors)]
        factors_from_pred(pred, factors) && equiv_in_presentation(base_A(), concat_all(factors), u);
    assert(factors_from_pred(pred, factors)
        && equiv_in_presentation(base_A(), concat_all(factors), u));
    assert forall|k: int| 0 <= k < factors.len() implies gexp(i, #[trigger] factors[k]) == 0 by {
        assert(pred(factors[k]) == is_residue_gen(ires, jres, m, factors[k]));
        lemma_gexp_residue_gen_zero(i, ires, jres, m, factors[k]);
    }
    lemma_gexp_concat_all_zero(i, factors);
    lemma_equiv_in_A_preserves_gexp(i, concat_all(factors), u);
}

//  A product of generators of ⟨t(i,j),xᵐ,yᵐ⟩ is a valid word over A's 3 generators.
pub proof fn lemma_decomp_factors_valid(i: nat, j: nat, m: nat, factors: Seq<Word>)
    requires
        factors_from_generators(
            seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)], factors),
    ensures
        word_valid(concat_all(factors), 3),
    decreases factors.len(),
{
    let gens = seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)];
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
        assert(word_valid(empty_word(), 3));
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies is_generator_or_inverse(gens, #[trigger] rest[k]) by {
                assert(rest[k] == factors[k + 1]);
            }
        }
        assert(is_generator_or_inverse(gens, first)) by { assert(first == factors[0]); }
        lemma_config_word_valid(i, j);
        lemma_signed_power_valid(1, m as int, 3);
        lemma_signed_power_valid(2, m as int, 3);
        let jj = choose|jj: int| 0 <= jj < 3 && (first == gens[jj] || first == inverse_word(gens[jj]));
        assert(0 <= jj < 3 && (first == gens[jj] || first == inverse_word(gens[jj])));
        assert(word_valid(gens[jj], 3));
        if first != gens[jj] { lemma_inverse_word_valid(gens[jj], 3); }
        lemma_decomp_factors_valid(i, j, m, rest);
        assert(concat_all(factors) =~= concat(first, concat_all(rest)));
        lemma_concat_word_valid(first, concat_all(rest), 3);
    }
}

//  ============================================================
//  PROPERTY (ii)⊆ — the assembly.
//  ============================================================
//
//  If w ∈ ⟨t(i,j),xᵐ,yᵐ⟩ has zero x- and y-exponent (e.g. w ∈ T), then w lies in the
//  residue-class subgroup ⟨t(r,s):r≡i,s≡j (mod m)⟩.
pub proof fn lemma_ii_subset(i: nat, j: nat, m: nat, w: Word)
    requires
        m > 0,
        gexp(1, w) == 0,
        gexp(2, w) == 0,
        in_generated_subgroup(base_A(),
            seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)], w),
    ensures
        in_residue_class(i as int, j as int, m as int, w),
{
    let p = base_A();
    lemma_base_A_valid();
    let gens = seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)];
    let factors = choose|factors: Seq<Word>| #![trigger factors_from_generators(gens, factors)]
        factors_from_generators(gens, factors) && equiv_in_presentation(p, concat_all(factors), w);
    assert(factors_from_generators(gens, factors) && equiv_in_presentation(p, concat_all(factors), w));
    let cf = concat_all(factors);
    lemma_decomp_factors_valid(i, j, m, factors);               // word_valid(cf, 3)
    let dec = lemma_decompose_factors(i, j, m, factors);
    let u = dec.0; let ax = dec.1; let by = dec.2;
    let nf = signed_power(1, ax) + signed_power(2, by) + u;      // cf ≡ nf
    //  gexp(1, w) = gexp(1, nf) = ax + 0 + 0;  gexp(2, w) = by
    lemma_equiv_symmetric(p, cf, w);                            // w ≡ cf
    lemma_equiv_transitive(p, w, cf, nf);                       // w ≡ nf
    lemma_equiv_in_A_preserves_gexp(1, w, nf);
    lemma_equiv_in_A_preserves_gexp(2, w, nf);
    lemma_gexp_concat(1, signed_power(1, ax) + signed_power(2, by), u);
    lemma_gexp_concat(1, signed_power(1, ax), signed_power(2, by));
    lemma_gexp_signed_power(1, 1, ax);
    lemma_gexp_signed_power(2, 1, by);
    lemma_gexp_residue_subgroup_zero(1, i as int, j as int, m as int, u);
    lemma_gexp_concat(2, signed_power(1, ax) + signed_power(2, by), u);
    lemma_gexp_concat(2, signed_power(1, ax), signed_power(2, by));
    lemma_gexp_signed_power(1, 2, ax);
    lemma_gexp_signed_power(2, 2, by);
    lemma_gexp_residue_subgroup_zero(2, i as int, j as int, m as int, u);
    assert(ax == 0 && by == 0);
    //  nf collapses to u, so w ≡ u
    assert(signed_power(1, ax) =~= empty_word());
    assert(signed_power(2, by) =~= empty_word());
    assert(nf =~= u);
    lemma_equiv_symmetric(p, cf, u);                            // u ≡ cf
    lemma_equiv_transitive(p, u, cf, w);                        // u ≡ w
    lemma_in_subgroup_pred_respects_equiv(p, residue_pred(i as int, j as int, m as int), u, w);
}

//  ============================================================
//  Generic closure:  a predicate-subgroup contained in a generated subgroup.
//  ============================================================
//  If every pred-element lies in ⟨gens⟩, then so does every element of the pred-subgroup.  This is
//  the closure half of property (ii)⊇ (the residue subgroup ⊆ ⟨t(i,j),xᵐ,yᵐ⟩); the remaining half
//  is showing each residue gen t(r,s) (r≡i, s≡j mod m) lies in ⟨t(i,j),xᵐ,yᵐ⟩ (the move-lemma 2D
//  conjugation induction).

//  concat_all of a factor list, each factor in ⟨gens⟩, is in ⟨gens⟩ (fold via product closure).
pub proof fn lemma_concat_all_in_generated(p: Presentation, gens: Seq<Word>, factors: Seq<Word>)
    requires
        forall|k: int| 0 <= k < factors.len() ==> in_generated_subgroup(p, gens, #[trigger] factors[k]),
    ensures
        in_generated_subgroup(p, gens, concat_all(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
        lemma_identity_in_generated_subgroup(p, gens);
        assert(concat_all(factors) =~= empty_word());
    } else {
        let rest = factors.drop_first();
        assert(concat_all(factors) =~= factors.first() + concat_all(rest));
        assert(in_generated_subgroup(p, gens, factors.first())) by {
            assert(factors[0] == factors.first());
        }
        assert forall|k: int| 0 <= k < rest.len()
            implies in_generated_subgroup(p, gens, #[trigger] rest[k]) by {
            assert(rest[k] == factors[k + 1]);
        }
        lemma_concat_all_in_generated(p, gens, rest);
        lemma_product_in_subgroup(p, gens, factors.first(), concat_all(rest));
    }
}

//  pred-subgroup ⊆ ⟨gens⟩ when each pred-element is in ⟨gens⟩.
pub proof fn lemma_pred_subgroup_in_generated(
    p: Presentation, pred: spec_fn(Word) -> bool, gens: Seq<Word>, w: Word,
)
    requires
        in_subgroup_pred(p, pred, w),
        forall|g: Word| pred(g) ==> in_generated_subgroup(p, gens, g),
    ensures
        in_generated_subgroup(p, gens, w),
{
    let factors = choose|factors: Seq<Word>| #[trigger] factors_from_pred(pred, factors)
        && equiv_in_presentation(p, concat_all(factors), w);
    assert(factors_from_pred(pred, factors) && equiv_in_presentation(p, concat_all(factors), w));
    assert forall|k: int| 0 <= k < factors.len()
        implies in_generated_subgroup(p, gens, #[trigger] factors[k]) by {
        assert(pred(factors[k]));                            //  factors_from_pred
    }
    lemma_concat_all_in_generated(p, gens, factors);
    lemma_in_subgroup_respects_equiv(p, gens, concat_all(factors), w);
}

//  ============================================================
//  (ii)⊇ powers:  m-multiple signed powers of a base generator lie in ⟨gens⟩.
//  ============================================================
//  Given xᵐ (= signed_power(gi, m)) and x⁻ᵐ in ⟨gens⟩, every x^{k·m} is too — built by peeling one
//  ±m at a time with lemma_signed_power_add + product closure.  Used to place the conjugating powers
//  x^{±(r-i)}, y^{±(s-j)} (r≡i, s≡j mod m ⟹ multiples of m) into ⟨t(i,j),xᵐ,yᵐ⟩.

//  is_generator_or_inverse ⟹ in_generated_subgroup (the n=1 case of word_power closure).
pub proof fn lemma_gen_or_inv_in_subgroup(gens: Seq<Word>, w: Word)
    requires
        is_generator_or_inverse(gens, w),
    ensures
        in_generated_subgroup(base_A(), gens, w),
{
    lemma_word_power_in_subgroup(base_A(), gens, w, 1);
    assert(word_power(w, 0) =~= empty_word());
    assert(word_power(w, 1) =~= w);                          //  w + ε
}

//  signed_power(gi, n·m) ∈ ⟨gens⟩, for n: nat (peel +m).
pub proof fn lemma_spow_pos_mult_in_G(gens: Seq<Word>, gi: nat, m: int, n: nat)
    requires
        in_generated_subgroup(base_A(), gens, signed_power(gi, m)),
    ensures
        in_generated_subgroup(base_A(), gens, signed_power(gi, n * m)),
    decreases n,
{
    let p = base_A();
    if n == 0 {
        lemma_identity_in_generated_subgroup(p, gens);
        assert(signed_power(gi, 0) =~= empty_word());
        assert((n * m) == 0);
    } else {
        lemma_spow_pos_mult_in_G(gens, gi, m, (n - 1) as nat);   //  signed_power(gi, (n-1)·m) ∈ G
        lemma_signed_power_add(p, gi, (n - 1) as int * m, m);    //  x^{(n-1)m}·x^m ≡ x^{(n-1)m+m}
        lemma_product_in_subgroup(p, gens, signed_power(gi, (n - 1) as int * m), signed_power(gi, m));
        assert((n - 1) as int * m + m == n * m) by(nonlinear_arith);
        lemma_in_subgroup_respects_equiv(p, gens,
            signed_power(gi, (n - 1) as int * m) + signed_power(gi, m), signed_power(gi, n * m));
    }
}

//  signed_power(gi, -(n·m)) ∈ ⟨gens⟩, for n: nat (peel -m).
pub proof fn lemma_spow_neg_mult_in_G(gens: Seq<Word>, gi: nat, m: int, n: nat)
    requires
        in_generated_subgroup(base_A(), gens, signed_power(gi, -m)),
    ensures
        in_generated_subgroup(base_A(), gens, signed_power(gi, -(n * m))),
    decreases n,
{
    let p = base_A();
    if n == 0 {
        lemma_identity_in_generated_subgroup(p, gens);
        assert(signed_power(gi, 0) =~= empty_word());
        assert(-(n * m) == 0);
    } else {
        lemma_spow_neg_mult_in_G(gens, gi, m, (n - 1) as nat);   //  signed_power(gi, -((n-1)·m)) ∈ G
        lemma_signed_power_add(p, gi, -((n - 1) as int * m), -m); //  x^{-(n-1)m}·x^{-m} ≡ x^{-(n-1)m-m}
        lemma_product_in_subgroup(p, gens, signed_power(gi, -((n - 1) as int * m)), signed_power(gi, -m));
        assert(-((n - 1) as int * m) + -m == -(n * m)) by(nonlinear_arith);
        lemma_in_subgroup_respects_equiv(p, gens,
            signed_power(gi, -((n - 1) as int * m)) + signed_power(gi, -m), signed_power(gi, -(n * m)));
    }
}

//  signed_power(gi, k·m) ∈ ⟨gens⟩ for any integer k (given both ±m in ⟨gens⟩).
pub proof fn lemma_spow_int_mult_in_G(gens: Seq<Word>, gi: nat, m: int, k: int)
    requires
        in_generated_subgroup(base_A(), gens, signed_power(gi, m)),
        in_generated_subgroup(base_A(), gens, signed_power(gi, -m)),
    ensures
        in_generated_subgroup(base_A(), gens, signed_power(gi, k * m)),
{
    if k >= 0 {
        lemma_spow_pos_mult_in_G(gens, gi, m, k as nat);
        assert((k as nat) * m == k * m);
    } else {
        let nn = (-k) as nat;
        assert(nn as int == -k);                            //  k < 0 ⟹ -k > 0 (cast identity)
        lemma_spow_neg_mult_in_G(gens, gi, m, nn);          //  signed_power(gi, -(nn·m)) ∈ G
        assert((nn as int) * m == (-k) * m);                //  congruence from nn as int == -k
        assert((-k) * m == -(k * m)) by(nonlinear_arith);   //  pure distribution
        assert(-(nn * m) == k * m);                         //  chain ⟹ exponents match
    }
}

//  ============================================================
//  (ii)⊇ core:  a residue config word t(r,s) (r≡i, s≡j mod m) lies in ⟨t(i,j),xᵐ,yᵐ⟩.
//  ============================================================
//  Build t(r,s) ≡ x^{-(r-i)}·y^{-(s-j)}·t(i,j)·y^{s-j}·x^{r-i} (two conjugations), each factor in
//  ⟨gens⟩: t(i,j)=gens[0]; the conjugating powers are m-multiples (r-i, s-j ≡ 0 mod m) handled by
//  the power infra; then product closure + respects_equiv.

//  x % m == 0 (m > 0) ⟹ x == (x/m)·m.  (Lean int div-mod: m·(x/m) + x%m = x.)
pub proof fn lemma_exact_div(x: int, m: int)
    requires
        m > 0,
        x % m == 0,
    ensures
        x == (x / m) * m
by {
    have h1 := Int.ediv_add_emod x m
    have h2 := Int.mul_comm (x / m) m
    omega
}

pub proof fn lemma_config_signed_in_G(i: nat, j: nat, m: nat, r: int, s: int)
    requires
        m > 0,
        (r - i) % (m as int) == 0,
        (s - j) % (m as int) == 0,
    ensures
        in_generated_subgroup(base_A(),
            seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)],
            config_word_signed(r, s)),
{
    let p = base_A();
    lemma_base_A_valid();
    let mm = m as int;
    let gens = seq![config_word(i, j), signed_power(1, mm), signed_power(2, mm)];
    let dx = r - i as int;
    let dy = s - j as int;
    //  --- the three generators + the two inverse powers are in ⟨gens⟩ ---
    lemma_generator_in_generated_subgroup(p, gens, 0);      //  config_word(i,j) = gens[0]
    lemma_generator_in_generated_subgroup(p, gens, 1);      //  x^m = gens[1]
    lemma_generator_in_generated_subgroup(p, gens, 2);      //  y^m = gens[2]
    assert(gens[0] == config_word(i, j));
    assert(gens[1] == signed_power(1, mm));
    assert(gens[2] == signed_power(2, mm));
    lemma_signed_power_inverse(1, mm);                      //  inverse_word(x^m) =~= x^{-m}
    lemma_signed_power_inverse(2, mm);
    assert(is_generator_or_inverse(gens, signed_power(1, -mm))) by {
        assert(signed_power(1, -mm) =~= inverse_word(gens[1]));
    }
    lemma_gen_or_inv_in_subgroup(gens, signed_power(1, -mm));
    assert(is_generator_or_inverse(gens, signed_power(2, -mm))) by {
        assert(signed_power(2, -mm) =~= inverse_word(gens[2]));
    }
    lemma_gen_or_inv_in_subgroup(gens, signed_power(2, -mm));
    //  --- the conjugating powers x^{±dx}, y^{±dy} are m-multiples, hence in ⟨gens⟩ ---
    let dr = dx / mm;
    let ds = dy / mm;
    lemma_exact_div(dx, mm);                                //  dx == dr·mm
    lemma_exact_div(dy, mm);                                //  dy == ds·mm
    assert(dr * mm == dx);
    assert(ds * mm == dy);
    assert((-dr) * mm == -(dr * mm)) by(nonlinear_arith);   //  pure distribution
    assert((-ds) * mm == -(ds * mm)) by(nonlinear_arith);
    assert((-dr) * mm == -dx);                              //  chain with dr·mm == dx
    assert((-ds) * mm == -dy);
    lemma_spow_int_mult_in_G(gens, 1, mm, dr);             //  x^{dr·mm} = x^{dx} ∈ G
    lemma_spow_int_mult_in_G(gens, 1, mm, -dr);            //  x^{-dx} ∈ G
    lemma_spow_int_mult_in_G(gens, 2, mm, ds);            //  y^{dy} ∈ G
    lemma_spow_int_mult_in_G(gens, 2, mm, -ds);           //  y^{-dy} ∈ G
    let xnd = signed_power(1, -dx);
    let xpd = signed_power(1, dx);
    let ynd = signed_power(2, -dy);
    let ypd = signed_power(2, dy);
    let t0 = config_word_signed(i as int, j as int);
    let tis = config_word_signed(i as int, s);
    //  t0 = config_word_signed(i,j) =~= config_word(i,j) = gens[0] ∈ G
    lemma_config_signed_matches_nat(i, j);
    assert(t0 =~= gens[0]);
    //  --- membership of CONJ = xnd · (ynd · t0 · ypd) · xpd ---
    let mid = ynd + t0 + ypd;
    lemma_product_in_subgroup(p, gens, ynd, t0);
    lemma_product_in_subgroup(p, gens, ynd + t0, ypd);     //  mid ∈ G
    lemma_product_in_subgroup(p, gens, xnd, mid);
    let conj = xnd + mid + xpd;
    lemma_product_in_subgroup(p, gens, xnd + mid, xpd);    //  conj ∈ G
    //  --- conj ≡ config_word_signed(r,s) ---
    //  inner:  mid ≡ t(i, j+dy) = tis  (by_y)
    lemma_conj_config_signed_by_y(i as int, j as int, dy);
    assert((j as int) + dy == s);
    assert(equiv_in_presentation(p, mid, tis));
    //  congruence:  xnd · mid · xpd ≡ xnd · tis · xpd
    lemma_equiv_concat_right(p, xnd, mid, tis);            //  xnd·mid ≡ xnd·tis
    lemma_equiv_concat_left(p, xnd + mid, xnd + tis, xpd); //  (xnd·mid)·xpd ≡ (xnd·tis)·xpd
    //  outer:  xnd · tis · xpd ≡ t(i+dx, s) = t(r,s)  (by_x)
    lemma_conj_config_signed_by_x(i as int, s, dx);
    assert((i as int) + dx == r);
    assert(equiv_in_presentation(p, xnd + tis + xpd, config_word_signed(r, s)));
    lemma_equiv_transitive(p, conj, xnd + tis + xpd, config_word_signed(r, s));
    //  conj ∈ G ∧ conj ≡ t(r,s) ⟹ t(r,s) ∈ G
    lemma_in_subgroup_respects_equiv(p, gens, conj, config_word_signed(r, s));
}

//  A residue gen (config word t(r,s) or its inverse, r≡i s≡j mod m) lies in ⟨t(i,j),xᵐ,yᵐ⟩.
pub proof fn lemma_residue_gen_in_G(i: nat, j: nat, m: nat, g: Word)
    requires
        m > 0,
        is_residue_gen(i as int, j as int, m as int, g),
    ensures
        in_generated_subgroup(base_A(),
            seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)], g),
{
    let p = base_A();
    lemma_base_A_valid();
    let mm = m as int;
    let gens = seq![config_word(i, j), signed_power(1, mm), signed_power(2, mm)];
    let rs = choose|r: int, s: int| #![trigger config_word_signed(r, s)]
        (r - i as int) % mm == 0 && (s - j as int) % mm == 0
        && (g == config_word_signed(r, s) || g == inverse_word(config_word_signed(r, s)));
    let r = rs.0;
    let s = rs.1;
    assert((r - i as int) % mm == 0 && (s - j as int) % mm == 0
        && (g == config_word_signed(r, s) || g == inverse_word(config_word_signed(r, s))));
    lemma_config_signed_in_G(i, j, m, r, s);                //  t(r,s) ∈ G
    if g != config_word_signed(r, s) {
        //  g = inverse_word(t(r,s)) ∈ G via inverse closure
        assert(g == inverse_word(config_word_signed(r, s)));
        lemma_config_signed_valid(r, s);                    //  word_valid(t(r,s), 3)
        assert(p.num_generators == 3);
        assert forall|t: int| 0 <= t < gens.len()
            implies word_valid(#[trigger] gens[t], p.num_generators) by {
            if t == 0 { lemma_config_word_valid(i, j); assert(gens[0] == config_word(i, j)); }
            else if t == 1 { lemma_signed_power_valid(1, mm, 3); assert(gens[1] == signed_power(1, mm)); }
            else { lemma_signed_power_valid(2, mm, 3); assert(gens[2] == signed_power(2, mm)); }
        }
        crate::normal_form_afp_textbook::lemma_subgroup_inverse(p, gens, config_word_signed(r, s));
    }
}

//  ============================================================
//  PROPERTY (ii)⊇ — the residue-class subgroup ⊆ ⟨t(i,j),xᵐ,yᵐ⟩  (inverts (ii)⊆).
//  ============================================================
pub proof fn lemma_ii_superset(i: nat, j: nat, m: nat, w: Word)
    requires
        m > 0,
        in_residue_class(i as int, j as int, m as int, w),
    ensures
        in_generated_subgroup(base_A(),
            seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)], w),
{
    let p = base_A();
    let mm = m as int;
    let gens = seq![config_word(i, j), signed_power(1, mm), signed_power(2, mm)];
    let pred = residue_pred(i as int, j as int, mm);
    assert(in_subgroup_pred(p, pred, w));                   //  = in_residue_class
    assert forall|gg: Word| pred(gg) implies in_generated_subgroup(p, gens, gg) by {
        assert(pred(gg) == is_residue_gen(i as int, j as int, mm, gg));
        lemma_residue_gen_in_G(i, j, m, gg);
    }
    lemma_pred_subgroup_in_generated(p, pred, gens, w);
}

//  ============================================================
//  Property (vii), the easy half:  every H₀ config word is in ⟨t, rᵢ, lⱼ⟩.
//  ============================================================
//  Composes brick-19 (reaches ⟹ k-commutes) with E1 (k-commutes ⟹ subgroup membership).
//  This is the T(M) ⊆ ⟨t,rᵢ,lⱼ⟩ direction of (vii).
pub proof fn lemma_h0_config_in_subgroup(mm: ModMachine, alpha: nat, beta: nat)
    requires
        mod_machine_wf(mm),
        mm_in_H0(mm, alpha, beta),
    ensures
        in_generated_subgroup(b_m(mm), g_subgens(mm), config_word(alpha, beta)),
{
    let k = choose|k: nat| mm_reaches(mm, alpha, beta, 0, 0, k);
    assert(mm_reaches(mm, alpha, beta, 0, 0, k));
    lemma_reaches_implies_k_commutes(mm, alpha, beta, k);
    lemma_k_commutes_implies_subgroup(mm, alpha, beta);
}

//  ============================================================
//  E2.C — generic property-II: the ⟨K,p⟩-word representation.
//  ============================================================
//  See docs/e2c-property-ii-design.md.  A ⟨K,p⟩-word is ALTERNATING — K-syllables interleaved
//  with signed stable letters — so every pinch-middle is a K-syllable by construction.

pub struct KPWord {
    pub head: Word,
    pub tail: Seq<(bool, Word)>,
}

//  The word a KP-word represents:  head · p^{s₁} · k₁ · p^{s₂} · k₂ · …  (sᵢ: true=p, false=p⁻¹).
pub open spec fn kp_value(stable: Symbol, kp: KPWord) -> Word
    decreases kp.tail.len(),
{
    if kp.tail.len() == 0 {
        kp.head
    } else {
        let p_sym = if kp.tail.first().0 { stable } else { inverse_symbol(stable) };
        kp.head + seq![p_sym]
            + kp_value(stable, KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() })
    }
}

//  The induction measure: the number of stable letters.
pub open spec fn kp_pcount(kp: KPWord) -> nat {
    kp.tail.len()
}

//  Every syllable (head and each kᵢ) is a K-element.
pub open spec fn is_kp_word(in_k: spec_fn(Word) -> bool, kp: KPWord) -> bool {
    &&& in_k(kp.head)
    &&& forall|i: int| 0 <= i < kp.tail.len() ==> in_k(#[trigger] kp.tail[i].1)
}

//  A tail-free KP-word is just its head.
pub proof fn lemma_kp_value_empty(stable: Symbol, head: Word)
    ensures
        kp_value(stable, KPWord { head, tail: Seq::empty() }) =~= head,
{
}

//  Unfolding identity: value of a non-empty KP-word peels off head · p^{s₁} · (value of the rest).
pub proof fn lemma_kp_value_cons(stable: Symbol, kp: KPWord)
    requires
        kp.tail.len() > 0,
    ensures
        kp_value(stable, kp) =~= kp.head
            + seq![if kp.tail.first().0 { stable } else { inverse_symbol(stable) }]
            + kp_value(stable, KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() }),
{
}

//  ============================================================
//  Move lemmas: slide a config word past an x/y power (index-shift, rearranged).
//  ============================================================

//  t(r,s) · xᵏ ≡ xᵏ · t(r+k, s).
pub proof fn lemma_config_move_x(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            config_word_signed(r, s) + signed_power(1, k),
            signed_power(1, k) + config_word_signed(r + k, s)),
{
    let p = base_A();
    lemma_base_A_valid();
    let xk = signed_power(1, k);
    let xnk = signed_power(1, -k);
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r + k, s);
    lemma_conj_config_signed_by_x(r, s, k);                 // x⁻ᵏ·cw·xᵏ ≡ cwk
    lemma_equiv_symmetric(p, xnk + cw + xk, cwk);            // cwk ≡ x⁻ᵏ·cw·xᵏ
    lemma_equiv_concat_right(p, xk, cwk, xnk + cw + xk);     // xᵏ·cwk ≡ xᵏ·(x⁻ᵏ·cw·xᵏ)
    lemma_signed_power_add(p, 1, k, -k);                     // xᵏ·x⁻ᵏ ≡ x⁰
    assert(signed_power(1, 0) =~= empty_word());
    assert(equiv_in_presentation(p, xk + xnk, empty_word()));
    crate::britton_via_tower::lemma_delete_equiv_empty(p, empty_word(), xk + xnk, cw + xk);
    assert(xk + cwk =~= xk + cwk);
    assert(xk + (xnk + cw + xk) =~= (xk + xnk) + (cw + xk));
    assert(empty_word() + (xk + xnk) + (cw + xk) =~= (xk + xnk) + (cw + xk));
    assert(empty_word() + (cw + xk) =~= cw + xk);
    lemma_equiv_transitive(p, xk + cwk, (xk + xnk) + (cw + xk), cw + xk);
    lemma_equiv_symmetric(p, xk + cwk, cw + xk);
}

//  t(r,s) · yᵏ ≡ yᵏ · t(r, s+k).
pub proof fn lemma_config_move_y(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            config_word_signed(r, s) + signed_power(2, k),
            signed_power(2, k) + config_word_signed(r, s + k)),
{
    let p = base_A();
    lemma_base_A_valid();
    let yk = signed_power(2, k);
    let ynk = signed_power(2, -k);
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r, s + k);
    lemma_conj_config_signed_by_y(r, s, k);
    lemma_equiv_symmetric(p, ynk + cw + yk, cwk);
    lemma_equiv_concat_right(p, yk, cwk, ynk + cw + yk);
    lemma_signed_power_add(p, 2, k, -k);
    assert(signed_power(2, 0) =~= empty_word());
    assert(equiv_in_presentation(p, yk + ynk, empty_word()));
    crate::britton_via_tower::lemma_delete_equiv_empty(p, empty_word(), yk + ynk, cw + yk);
    assert(yk + (ynk + cw + yk) =~= (yk + ynk) + (cw + yk));
    assert(empty_word() + (yk + ynk) + (cw + yk) =~= (yk + ynk) + (cw + yk));
    assert(empty_word() + (cw + yk) =~= cw + yk);
    lemma_equiv_transitive(p, yk + cwk, (yk + ynk) + (cw + yk), cw + yk);
    lemma_equiv_symmetric(p, yk + cwk, cw + yk);
}

//  t(r,s) · xᵃ · yᵇ ≡ xᵃ · yᵇ · t(r+a, s+b).
pub proof fn lemma_config_move_xy(r: int, s: int, aa: int, bb: int)
    ensures
        equiv_in_presentation(base_A(),
            config_word_signed(r, s) + signed_power(1, aa) + signed_power(2, bb),
            signed_power(1, aa) + signed_power(2, bb) + config_word_signed(r + aa, s + bb)),
{
    let p = base_A();
    lemma_base_A_valid();
    let xa = signed_power(1, aa);
    let yb = signed_power(2, bb);
    let cw = config_word_signed(r, s);
    let cwa = config_word_signed(r + aa, s);
    let cwab = config_word_signed(r + aa, s + bb);
    lemma_config_move_x(r, s, aa);                          // cw·xa ≡ xa·cwa
    lemma_equiv_concat_left(p, cw + xa, xa + cwa, yb);      // (cw·xa)·yb ≡ (xa·cwa)·yb
    lemma_config_move_y(r + aa, s, bb);                     // cwa·yb ≡ yb·cwab
    lemma_equiv_concat_right(p, xa, cwa + yb, yb + cwab);   // xa·(cwa·yb) ≡ xa·(yb·cwab)
    assert((cw + xa) + yb =~= cw + xa + yb);
    assert((xa + cwa) + yb =~= xa + (cwa + yb));
    assert(xa + (yb + cwab) =~= xa + yb + cwab);
    lemma_equiv_transitive(p, cw + xa + yb, xa + (cwa + yb), xa + (yb + cwab));
}

//  inverse_word(xᵏ) = x⁻ᵏ.
pub proof fn lemma_signed_power_inverse(i: nat, k: int)
    ensures
        inverse_word(signed_power(i, k)) =~= signed_power(i, -k),
{
    if k >= 0 {
        lemma_inverse_word_sympower(Symbol::Gen(i), k as nat);
        assert(inverse_symbol(Symbol::Gen(i)) == Symbol::Inv(i));
    } else {
        lemma_inverse_word_sympower(Symbol::Inv(i), (-k) as nat);
        assert(inverse_symbol(Symbol::Inv(i)) == Symbol::Gen(i));
    }
}

//  config_word_signed(r,s) is a valid word over A's 3 generators.
pub proof fn lemma_config_signed_valid(r: int, s: int)
    ensures
        word_valid(config_word_signed(r, s), 3),
{
    lemma_signed_power_valid(2, -s, 3);
    lemma_signed_power_valid(1, -r, 3);
    lemma_signed_power_valid(1, r, 3);
    lemma_signed_power_valid(2, s, 3);
    let t0: Word = seq![Symbol::Gen(0)];
    assert(word_valid(t0, 3)) by {
        assert forall|k: int| 0 <= k < t0.len() implies symbol_valid(#[trigger] t0[k], 3) by { }
    }
    lemma_concat_word_valid(signed_power(2, -s), signed_power(1, -r), 3);
    lemma_concat_word_valid(signed_power(2, -s) + signed_power(1, -r), t0, 3);
    lemma_concat_word_valid(signed_power(2, -s) + signed_power(1, -r) + t0, signed_power(1, r), 3);
    lemma_concat_word_valid(signed_power(2, -s) + signed_power(1, -r) + t0 + signed_power(1, r),
        signed_power(2, s), 3);
}

//  inverse_word(t(r,s)) · xᵏ ≡ xᵏ · inverse_word(t(r+k, s)).  (from config_move_x at (r+k,s,-k))
pub proof fn lemma_config_inv_move_x(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            inverse_word(config_word_signed(r, s)) + signed_power(1, k),
            signed_power(1, k) + inverse_word(config_word_signed(r + k, s))),
{
    let p = base_A();
    lemma_base_A_valid();
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r + k, s);
    let xnk = signed_power(1, -k);
    //  t(r+k,s)·x⁻ᵏ ≡ x⁻ᵏ·t(r,s)
    lemma_config_move_x(r + k, s, -k);
    //  validity for inversion
    lemma_config_signed_valid(r, s);
    lemma_config_signed_valid(r + k, s);
    lemma_signed_power_valid(1, -k, 3);
    lemma_concat_word_valid(cwk, xnk, 3);
    lemma_concat_word_valid(xnk, cw, 3);
    crate::normal_form_afp_textbook::lemma_equiv_inverse(p, cwk + xnk, xnk + cw);
    //  compute the two inverses
    lemma_inverse_word_concat(cwk, xnk);
    lemma_inverse_word_concat(xnk, cw);
    lemma_signed_power_inverse(1, -k);                      // inverse_word(x⁻ᵏ) =~= xᵏ
    assert(inverse_word(cwk + xnk) =~= signed_power(1, k) + inverse_word(cwk));
    assert(inverse_word(xnk + cw) =~= inverse_word(cw) + signed_power(1, k));
    lemma_inverse_word_valid(cwk, 3);
    lemma_signed_power_valid(1, k, 3);
    lemma_concat_word_valid(signed_power(1, k), inverse_word(cwk), 3);
    lemma_equiv_symmetric(p, signed_power(1, k) + inverse_word(cwk), inverse_word(cw) + signed_power(1, k));
}

//  inverse_word(t(r,s)) · yᵏ ≡ yᵏ · inverse_word(t(r, s+k)).
pub proof fn lemma_config_inv_move_y(r: int, s: int, k: int)
    ensures
        equiv_in_presentation(base_A(),
            inverse_word(config_word_signed(r, s)) + signed_power(2, k),
            signed_power(2, k) + inverse_word(config_word_signed(r, s + k))),
{
    let p = base_A();
    lemma_base_A_valid();
    let cw = config_word_signed(r, s);
    let cwk = config_word_signed(r, s + k);
    let ynk = signed_power(2, -k);
    lemma_config_move_y(r, s + k, -k);
    lemma_config_signed_valid(r, s);
    lemma_config_signed_valid(r, s + k);
    lemma_signed_power_valid(2, -k, 3);
    lemma_concat_word_valid(cwk, ynk, 3);
    lemma_concat_word_valid(ynk, cw, 3);
    crate::normal_form_afp_textbook::lemma_equiv_inverse(p, cwk + ynk, ynk + cw);
    lemma_inverse_word_concat(cwk, ynk);
    lemma_inverse_word_concat(ynk, cw);
    lemma_signed_power_inverse(2, -k);
    assert(inverse_word(cwk + ynk) =~= signed_power(2, k) + inverse_word(cwk));
    assert(inverse_word(ynk + cw) =~= inverse_word(cw) + signed_power(2, k));
    lemma_inverse_word_valid(cwk, 3);
    lemma_signed_power_valid(2, k, 3);
    lemma_concat_word_valid(signed_power(2, k), inverse_word(cwk), 3);
    lemma_equiv_symmetric(p, signed_power(2, k) + inverse_word(cwk), inverse_word(cw) + signed_power(2, k));
}

//  inverse_word(t(r,s)) · xᵃ · yᵇ ≡ xᵃ · yᵇ · inverse_word(t(r+a, s+b)).
pub proof fn lemma_config_inv_move_xy(r: int, s: int, aa: int, bb: int)
    ensures
        equiv_in_presentation(base_A(),
            inverse_word(config_word_signed(r, s)) + signed_power(1, aa) + signed_power(2, bb),
            signed_power(1, aa) + signed_power(2, bb) + inverse_word(config_word_signed(r + aa, s + bb))),
{
    let p = base_A();
    lemma_base_A_valid();
    let xa = signed_power(1, aa);
    let yb = signed_power(2, bb);
    let icw = inverse_word(config_word_signed(r, s));
    let icwa = inverse_word(config_word_signed(r + aa, s));
    let icwab = inverse_word(config_word_signed(r + aa, s + bb));
    lemma_config_inv_move_x(r, s, aa);                      // icw·xa ≡ xa·icwa
    lemma_equiv_concat_left(p, icw + xa, xa + icwa, yb);
    lemma_config_inv_move_y(r + aa, s, bb);                 // icwa·yb ≡ yb·icwab
    lemma_equiv_concat_right(p, xa, icwa + yb, yb + icwab);
    assert((icw + xa) + yb =~= icw + xa + yb);
    assert((xa + icwa) + yb =~= xa + (icwa + yb));
    assert(xa + (yb + icwab) =~= xa + yb + icwab);
    lemma_equiv_transitive(p, icw + xa + yb, xa + (icwa + yb), xa + (yb + icwab));
}

//  ============================================================
//  Property (ii)⊆ — structural decomposition (separate module)
//  ============================================================
//
//  This work lives in its own module so its predicate-heavy `in_residue_class`
//  goals (exists/forall triggers) don't pollute machine_group's triggers — that
//  pollution was tipping a fragile config-basis lemma (lemma_psi_A_stable_count_scales)
//  over the Lean heartbeat edge.  Builds on machine_group's signed config words,
//  index-shifts, and the residue-class predicate.

//  Shifting an index by ±m preserves its residue mod m.
pub proof fn lemma_residue_shift_x(i: int, m: int, r: int)
    requires
        m > 0,
        (r - i) % m == 0,
    ensures
        (r - m - i) % m == 0,
        (r + m - i) % m == 0,
{
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(r - i, m);  // (m + (r-i)) % m == (r-i) % m
    vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(r - i, m);  // (-m + (r-i)) % m == (r-i) % m
    assert(r + m - i == m + (r - i));
    assert(r - m - i == -m + (r - i));
}

//  Single-gen closure: conjugating a residue gen by xᵐ stays in the residue class.
//  xᵐ · t(r,s) · x⁻ᵐ ≡ t(r-m, s), and t(r-m,s) is still a residue gen (r-m ≡ i mod m).
pub proof fn lemma_conj_residue_gen_x(i: int, j: int, m: int, r: int, s: int)
    requires
        m > 0,
        (r - i) % m == 0,
        (s - j) % m == 0,
    ensures
        equiv_in_presentation(base_A(),
            signed_power(1, m) + config_word_signed(r, s) + signed_power(1, -m),
            config_word_signed(r - m, s)),
        in_residue_class(i, j, m, config_word_signed((r - m), s)),
{
    lemma_conj_config_signed_by_x(r, s, -m);   // x^m · t(r,s) · x^-m ≡ t(r-m, s)
    lemma_residue_shift_x(i, m, r);
    lemma_residue_gen_in_class(i, j, m, r - m, s);
}

//  Single-gen closure for y:  yᵐ · t(r,s) · y⁻ᵐ ≡ t(r, s-m), still a residue gen.
pub proof fn lemma_conj_residue_gen_y(i: int, j: int, m: int, r: int, s: int)
    requires
        m > 0,
        (r - i) % m == 0,
        (s - j) % m == 0,
    ensures
        equiv_in_presentation(base_A(),
            signed_power(2, m) + config_word_signed(r, s) + signed_power(2, -m),
            config_word_signed(r, s - m)),
        in_residue_class(i, j, m, config_word_signed(r, (s - m))),
{
    lemma_conj_config_signed_by_y(r, s, -m);
    lemma_residue_shift_x(j, m, s);
    lemma_residue_gen_in_class(i, j, m, r, s - m);
}

//  ============================================================
//  Decomposition induction — per-factor step helpers.
//  ============================================================
//
//  Each takes the IH normal form  rest ≡ x^{aa·m}·y^{bb·m}·u  (u in the residue class)
//  and produces the normal form for  factor·rest.

//  The normal form is parameterized by the actual x,y EXPONENTS (ax, by), each a multiple of m.
//  Each step helper RETURNS the new (u, ax, by) tuple (ghost return — no existential triggers).

//  Prepend x^{de·m} (de = ±1 for the xᵐ / x⁻ᵐ factor): merges into the x-exponent.
pub proof fn lemma_step_x(i: nat, j: nat, m: nat, de: int, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), signed_power(1, de * m) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let xdm = signed_power(1, de * m);
    let xam = signed_power(1, ax);
    let ybm = signed_power(2, by);
    let nf = xam + ybm + u;
    lemma_equiv_concat_right(p, xdm, rest, nf);                  // xdm·rest ≡ xdm·nf
    lemma_signed_power_add(p, 1, de * m, ax);                    // xdm·xam ≡ x^{de·m+ax}
    let xsum = signed_power(1, de * m + ax);
    lemma_equiv_concat_left(p, xdm + xam, xsum, ybm + u);
    assert(xdm + nf =~= (xdm + xam) + (ybm + u));
    assert(xsum + (ybm + u) =~= xsum + ybm + u);
    lemma_equiv_transitive(p, xdm + rest, (xdm + xam) + (ybm + u), xsum + ybm + u);
    //  (de·m + ax) % m == 0
    assert(de * m + ax == (m as int) * de + ax) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(de, ax, m as int);  // (m·de+ax)%m == ax%m
    (u, de * m + ax, by)
}

//  Prepend y^{de·m} (de = ±1): commute past the x-exponent, then merge into the y-exponent.
pub proof fn lemma_step_y(i: nat, j: nat, m: nat, de: int, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), signed_power(2, de * m) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let ydm = signed_power(2, de * m);
    let xax = signed_power(1, ax);
    let yby = signed_power(2, by);
    let ysum = signed_power(2, de * m + by);
    let nf = xax + yby + u;
    lemma_equiv_concat_right(p, ydm, rest, nf);                  // ydm·rest ≡ ydm·nf
    //  commute ydm past xax
    lemma_signed_xy_commute(ax, de * m);                          // xax·ydm ≡ ydm·xax
    lemma_signed_power_valid(1, ax, 3);
    lemma_signed_power_valid(2, de * m, 3);
    lemma_concat_word_valid(xax, ydm, 3);
    lemma_equiv_symmetric(p, xax + ydm, ydm + xax);              // ydm·xax ≡ xax·ydm
    lemma_equiv_concat_left(p, ydm + xax, xax + ydm, yby + u);
    //  merge ydm·yby → ysum
    lemma_signed_power_add(p, 2, de * m, by);                    // ydm·yby ≡ ysum
    lemma_equiv_concat_left(p, ydm + yby, ysum, u);
    lemma_equiv_concat_right(p, xax, (ydm + yby) + u, ysum + u);
    assert(ydm + nf =~= (ydm + xax) + (yby + u));
    assert((xax + ydm) + (yby + u) =~= xax + ((ydm + yby) + u));
    assert(xax + (ysum + u) =~= xax + ysum + u);
    lemma_equiv_transitive(p, ydm + rest, (ydm + xax) + (yby + u), xax + ((ydm + yby) + u));
    lemma_equiv_transitive(p, ydm + rest, xax + ((ydm + yby) + u), xax + ysum + u);
    assert(de * m + by == (m as int) * de + by) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(de, by, m as int);
    (u, ax, de * m + by)
}

//  Prepend the config gen t(i,j): slide it right past x^{ax}·y^{by} (shifting to t(i+ax,j+by),
//  still a residue gen since ax,by ≡ 0 mod m) and absorb into u.
pub proof fn lemma_step_config(i: nat, j: nat, m: nat, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), config_word(i, j) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let cw = config_word(i, j);
    let cws = config_word_signed(i as int, j as int);
    let xax = signed_power(1, ax);
    let yby = signed_power(2, by);
    let cwshift = config_word_signed(i as int + ax, j as int + by);
    let u2 = cwshift + u;
    let nf = xax + yby + u;
    lemma_config_signed_matches_nat(i, j);                       // cws =~= cw
    lemma_equiv_concat_right(p, cw, rest, nf);                   // cw·rest ≡ cw·nf
    lemma_config_move_xy(i as int, j as int, ax, by);           // cws·xax·yby ≡ xax·yby·cwshift
    lemma_equiv_concat_left(p, cws + xax + yby, xax + yby + cwshift, u);
    assert(cw == cws);
    assert(cw + nf =~= (cws + xax + yby) + u);
    assert((xax + yby + cwshift) + u =~= xax + yby + u2);
    lemma_equiv_transitive(p, cw + rest, (cws + xax + yby) + u, (xax + yby + cwshift) + u);
    //  residue class:  cwshift is a residue gen, product with u
    lemma_residue_gen_in_class(i as int, j as int, m as int, i as int + ax, j as int + by);
    lemma_product_in_subgroup_pred(p, residue_pred(i as int, j as int, m as int), cwshift, u);
    (u2, ax, by)
}

//  Prepend the inverse config gen t(i,j)⁻¹: same as config, with the inverse move and inverse residue gen.
pub proof fn lemma_step_inv_config(i: nat, j: nat, m: nat, ax: int, by: int, u: Word, rest: Word) -> (res: (Word, int, int))
    requires
        m > 0,
        ax % (m as int) == 0,
        by % (m as int) == 0,
        in_residue_class(i as int, j as int, m as int, u),
        equiv_in_presentation(base_A(), rest, signed_power(1, ax) + signed_power(2, by) + u),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), inverse_word(config_word(i, j)) + rest,
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
{
    let p = base_A();
    lemma_base_A_valid();
    let icw = inverse_word(config_word(i, j));
    let icws = inverse_word(config_word_signed(i as int, j as int));
    let xax = signed_power(1, ax);
    let yby = signed_power(2, by);
    let icwshift = inverse_word(config_word_signed(i as int + ax, j as int + by));
    let u2 = icwshift + u;
    let nf = xax + yby + u;
    lemma_config_signed_matches_nat(i, j);
    lemma_equiv_concat_right(p, icw, rest, nf);
    lemma_config_inv_move_xy(i as int, j as int, ax, by);       // icws·xax·yby ≡ xax·yby·icwshift
    lemma_equiv_concat_left(p, icws + xax + yby, xax + yby + icwshift, u);
    assert(icw == icws);
    assert(icw + nf =~= (icws + xax + yby) + u);
    assert((xax + yby + icwshift) + u =~= xax + yby + u2);
    lemma_equiv_transitive(p, icw + rest, (icws + xax + yby) + u, (xax + yby + icwshift) + u);
    //  icwshift is an (inverse) residue gen
    assert(is_residue_gen(i as int, j as int, m as int, icwshift)) by {
        assert((i as int + ax - i as int) % (m as int) == 0);
        assert((j as int + by - j as int) % (m as int) == 0);
        assert(icwshift == inverse_word(config_word_signed(i as int + ax, j as int + by)));
    }
    assert(residue_pred(i as int, j as int, m as int)(icwshift) == is_residue_gen(i as int, j as int, m as int, icwshift));
    lemma_gen_in_subgroup_pred(p, residue_pred(i as int, j as int, m as int), icwshift);
    lemma_product_in_subgroup_pred(p, residue_pred(i as int, j as int, m as int), icwshift, u);
    (u2, ax, by)
}

//  ============================================================
//  THE STRUCTURAL DECOMPOSITION (the main induction).
//  ============================================================
//
//  Any product of t(i,j), xᵐ, yᵐ (and inverses) equals  x^{ax}·y^{by}·u  with ax,by ≡ 0 (mod m)
//  and u ∈ ⟨t(r,s) : r≡i, s≡j (mod m)⟩.  Induction on the factor sequence; prepend each factor.
pub proof fn lemma_decompose_factors(i: nat, j: nat, m: nat, factors: Seq<Word>) -> (res: (Word, int, int))
    requires
        m > 0,
        factors_from_generators(
            seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)], factors),
    ensures
        in_residue_class(i as int, j as int, m as int, res.0),
        res.1 % (m as int) == 0,
        res.2 % (m as int) == 0,
        equiv_in_presentation(base_A(), concat_all(factors),
            signed_power(1, res.1) + signed_power(2, res.2) + res.0),
    decreases factors.len(),
{
    let p = base_A();
    lemma_base_A_valid();
    let gens = seq![config_word(i, j), signed_power(1, m as int), signed_power(2, m as int)];
    let pred = residue_pred(i as int, j as int, m as int);
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
        assert(in_subgroup_pred(p, pred, empty_word())) by {
            assert(factors_from_pred(pred, Seq::<Word>::empty()));
            assert(concat_all(Seq::<Word>::empty()) =~= empty_word());
            lemma_equiv_refl(p, empty_word());
        }
        assert(signed_power(1, 0) =~= empty_word());
        assert(signed_power(2, 0) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
        assert(concat_all(factors) =~= signed_power(1, 0) + signed_power(2, 0) + empty_word());
        (empty_word(), 0, 0)
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies is_generator_or_inverse(gens, #[trigger] rest[k]) by {
                assert(rest[k] == factors[k + 1]);
            }
        }
        assert(is_generator_or_inverse(gens, first)) by { assert(first == factors[0]); }
        let ih = lemma_decompose_factors(i, j, m, rest);
        let u2 = ih.0; let ax2 = ih.1; let by2 = ih.2;
        let cr = concat_all(rest);
        assert(concat_all(factors) =~= concat(first, cr));
        let jj = choose|jj: int| 0 <= jj < gens.len() && (first == gens[jj] || first == inverse_word(gens[jj]));
        assert(0 <= jj < 3 && (first == gens[jj] || first == inverse_word(gens[jj])));
        if jj == 0 {
            if first == gens[0] {
                assert(first == config_word(i, j));
                let r = lemma_step_config(i, j, m, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= config_word(i, j) + cr);
                r
            } else {
                lemma_step_inv_config(i, j, m, ax2, by2, u2, cr)
            }
        } else if jj == 1 {
            if first == gens[1] {
                assert(first == signed_power(1, 1 * (m as int)));
                let r = lemma_step_x(i, j, m, 1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(1, 1 * (m as int)) + cr);
                r
            } else {
                lemma_signed_power_inverse(1, m as int);       // inverse_word(xᵐ) =~= x⁻ᵐ
                assert(first == signed_power(1, -1 * (m as int)));
                let r = lemma_step_x(i, j, m, -1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(1, -1 * (m as int)) + cr);
                r
            }
        } else {
            if first == gens[2] {
                assert(first == signed_power(2, 1 * (m as int)));
                let r = lemma_step_y(i, j, m, 1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(2, 1 * (m as int)) + cr);
                r
            } else {
                lemma_signed_power_inverse(2, m as int);
                assert(first == signed_power(2, -1 * (m as int)));
                let r = lemma_step_y(i, j, m, -1, ax2, by2, u2, cr);
                assert(concat_all(factors) =~= signed_power(2, -1 * (m as int)) + cr);
                r
            }
        }
    }
}

} //  verus!
