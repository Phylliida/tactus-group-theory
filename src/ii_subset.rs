use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::machine_group::*;
use crate::hnn::{HNNData, stable_letter, stable_letter_inv, hnn_presentation, hnn_data_valid, lemma_hnn_conjugation, lemma_base_embeds_in_hnn};
use crate::benign::{in_generated_subgroup, factors_from_generators, is_generator_or_inverse, concat_all};
use crate::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat, lemma_apply_embedding_valid};

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
//  Brick C — head-independent `tail_value`:  the surgery substrate.
//  ============================================================
//  The head-first fold `kp_value` is awkward to split at an interior index.  Reformulate the
//  tail's contribution as a head-INDEPENDENT fold `tail_value`, where each entry contributes
//  [p^{s}]·k independently.  Then  kp_value(kp) = head · tail_value(tail)  and `tail_value`
//  distributes over Seq concatenation — so a surgery splicing the tail becomes a local rewrite.

//  The signed stable letter for an entry's bool flag (true = p, false = p⁻¹).
pub open spec fn kp_stable_sym(stable: Symbol, b: bool) -> Symbol {
    if b { stable } else { inverse_symbol(stable) }
}

//  The tail's contribution:  [p^{s₀}]·k₀ · [p^{s₁}]·k₁ · … (no head).
pub open spec fn tail_value(stable: Symbol, tail: Seq<(bool, Word)>) -> Word
    decreases tail.len(),
{
    if tail.len() == 0 {
        empty_word()
    } else {
        seq![kp_stable_sym(stable, tail.first().0)] + tail.first().1
            + tail_value(stable, tail.drop_first())
    }
}

//  kp_value(kp) = head · tail_value(tail).
pub proof fn lemma_kp_value_as_tail(stable: Symbol, kp: KPWord)
    ensures
        kp_value(stable, kp) =~= kp.head + tail_value(stable, kp.tail),
    decreases kp.tail.len(),
{
    if kp.tail.len() == 0 {
        assert(tail_value(stable, kp.tail) =~= empty_word());
    } else {
        let rest_kp = KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() };
        lemma_kp_value_as_tail(stable, rest_kp);
        //  kp_value(kp) = head + [p^{s₀}] + kp_value(rest_kp)
        //              = head + [p^{s₀}] + (tail.first().1 + tail_value(drop_first))
        //              = head + tail_value(tail)
    }
}

//  tail_value distributes over Seq concatenation.
pub proof fn lemma_tail_value_concat(stable: Symbol, a: Seq<(bool, Word)>, b: Seq<(bool, Word)>)
    ensures
        tail_value(stable, a + b) =~= tail_value(stable, a) + tail_value(stable, b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(tail_value(stable, a) =~= empty_word());
    } else {
        assert((a + b).first() == a.first());
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_tail_value_concat(stable, a.drop_first(), b);
    }
}

//  Singleton:  tail_value([(s, k)]) = [p^{s}]·k.
pub proof fn lemma_tail_value_singleton(stable: Symbol, e: (bool, Word))
    ensures
        tail_value(stable, seq![e]) =~= seq![kp_stable_sym(stable, e.0)] + e.1,
{
    let s1: Seq<(bool, Word)> = seq![e];
    assert(s1.first() == e);
    assert(s1.drop_first() =~= Seq::<(bool, Word)>::empty());
    assert(tail_value(stable, Seq::<(bool, Word)>::empty()) =~= empty_word());
}

//  Pair:  tail_value([(s₀,k₀),(s₁,k₁)]) = [p^{s₀}]·k₀·[p^{s₁}]·k₁.
pub proof fn lemma_tail_value_pair(stable: Symbol, e0: (bool, Word), e1: (bool, Word))
    ensures
        tail_value(stable, seq![e0, e1]) =~=
            seq![kp_stable_sym(stable, e0.0)] + e0.1 + seq![kp_stable_sym(stable, e1.0)] + e1.1,
{
    let s2: Seq<(bool, Word)> = seq![e0, e1];
    assert(s2.first() == e0);
    assert(s2.drop_first() =~= seq![e1]);
    lemma_tail_value_singleton(stable, e1);
}

//  ============================================================
//  Brick A — generalized HNN conjugation over a whole subgroup element.
//  ============================================================
//  The single-generator relation  t⁻¹·a_i·t ≡ b_i  (lemma_hnn_conjugation) lifts to an
//  arbitrary element of A₊ = ⟨a_i⟩:  for any witness word `wit` over the k association
//  indices,  t⁻¹·φ_a(wit)·t ≡ φ_b(wit)  where φ_a/φ_b substitute a_i / b_i.  This is the
//  HNN conjugation engine the pinch surgery (L1) needs.

//  The a-side / b-side image word-lists (A₊ resp. A₋ generators).
pub open spec fn hnn_a_words(data: HNNData) -> Seq<Word> {
    Seq::new(data.associations.len(), |i: int| data.associations[i].0)
}

pub open spec fn hnn_b_words(data: HNNData) -> Seq<Word> {
    Seq::new(data.associations.len(), |i: int| data.associations[i].1)
}

//  Per-symbol conjugation:  t⁻¹ · φ_a(sym) · t ≡ φ_b(sym).
pub proof fn lemma_hnn_conj_symbol(data: HNNData, sym: Symbol)
    requires
        hnn_data_valid(data),
        symbol_valid(sym, data.associations.len() as nat),
    ensures
        equiv_in_presentation(hnn_presentation(data),
            seq![stable_letter_inv(data)] + apply_embedding_symbol(hnn_a_words(data), sym)
                + seq![stable_letter(data)],
            apply_embedding_symbol(hnn_b_words(data), sym)),
{
    let hp = hnn_presentation(data);
    let t = stable_letter(data);
    let ti = stable_letter_inv(data);
    let k = data.associations.len();
    let aw = hnn_a_words(data);
    let bw = hnn_b_words(data);
    let ng = hp.num_generators;
    let tiw: Word = seq![ti];
    let tw: Word = seq![t];
    crate::britton_infra::lemma_hnn_presentation_valid(data);
    //  singleton bridges:  seq![x] is the same Seq as Seq::new(1, |_| x).
    assert(tiw =~= Seq::new(1, |_j: int| ti));
    assert(tw =~= Seq::new(1, |_j: int| t));
    let i = generator_index(sym) as int;
    assert(0 <= i < k);
    assert(aw[i] == data.associations[i].0);
    assert(bw[i] == data.associations[i].1);
    lemma_hnn_conjugation(data, i);
    //  lemma_hnn_conjugation:  Seq::new(1,|_|ti) + assoc[i].0 + Seq::new(1,|_|t) ≡ assoc[i].1
    let ai = data.associations[i].0;
    let bi = data.associations[i].1;
    let l_: Word = tiw + ai + tw;
    let r_: Word = bi;
    assert(l_ =~= Seq::new(1, |_j: int| ti) + ai + Seq::new(1, |_j: int| t));
    //  so  l_ ≡ r_  in hp.
    match sym {
        Symbol::Gen(ii) => {
            assert(apply_embedding_symbol(aw, sym) == aw[i]);
            assert(apply_embedding_symbol(bw, sym) == bw[i]);
            assert(tiw + apply_embedding_symbol(aw, sym) + tw =~= l_);
            assert(apply_embedding_symbol(bw, sym) =~= r_);
        }
        Symbol::Inv(ii) => {
            //  goal LHS = inverse_word(l_),  goal RHS = inverse_word(r_).
            assert(word_valid(ai, data.base.num_generators));
            assert(word_valid(bi, data.base.num_generators));
            lemma_word_valid_mono(ai, data.base.num_generators, ng);
            lemma_word_valid_mono(bi, data.base.num_generators, ng);
            assert(symbol_valid(t, ng) && symbol_valid(ti, ng));
            assert(word_valid(tiw, ng)) by {
                assert forall|q: int| 0 <= q < tiw.len() implies symbol_valid(#[trigger] tiw[q], ng) by { }
            }
            assert(word_valid(tw, ng)) by {
                assert forall|q: int| 0 <= q < tw.len() implies symbol_valid(#[trigger] tw[q], ng) by { }
            }
            lemma_concat_word_valid(tiw, ai, ng);
            lemma_concat_word_valid(tiw + ai, tw, ng);
            crate::normal_form_afp_textbook::lemma_equiv_inverse(hp, l_, r_);
            //  inverse_word(l_) = inverse_word(tw) + inverse_word(a_i) + inverse_word(tiw)
            lemma_inverse_word_concat(tiw + ai, tw);
            lemma_inverse_word_concat(tiw, ai);
            lemma_inverse_word_one(t);
            lemma_inverse_word_one(ti);
            assert(inverse_symbol(t) == ti);
            assert(inverse_symbol(ti) == t);
            assert(apply_embedding_symbol(aw, sym) =~= inverse_word(ai));
            assert(apply_embedding_symbol(bw, sym) =~= inverse_word(bi));
            assert(tiw + apply_embedding_symbol(aw, sym) + tw =~= inverse_word(l_));
            assert(apply_embedding_symbol(bw, sym) =~= inverse_word(r_));
        }
    }
}

//  Generalized conjugation:  t⁻¹ · φ_a(wit) · t ≡ φ_b(wit)  for any witness word over k indices.
pub proof fn lemma_hnn_conjugation_subgroup(data: HNNData, wit: Word)
    requires
        hnn_data_valid(data),
        word_valid(wit, data.associations.len() as nat),
    ensures
        equiv_in_presentation(hnn_presentation(data),
            seq![stable_letter_inv(data)] + apply_embedding(hnn_a_words(data), wit)
                + seq![stable_letter(data)],
            apply_embedding(hnn_b_words(data), wit)),
    decreases wit.len(),
{
    let hp = hnn_presentation(data);
    let t = stable_letter(data);
    let ti = stable_letter_inv(data);
    let aw = hnn_a_words(data);
    let bw = hnn_b_words(data);
    crate::britton_infra::lemma_hnn_presentation_valid(data);
    if wit.len() == 0 {
        //  φ_a(ε) = ε, φ_b(ε) = ε;  goal  [ti]·ε·[t] ≡ ε.
        assert(apply_embedding(aw, wit) =~= empty_word());
        assert(apply_embedding(bw, wit) =~= empty_word());
        //  [ti] + ε + [t] = [ti] + [t] = inverse_word([t]) + [t] ≡ ε
        lemma_inverse_word_one(t);
        assert(inverse_symbol(t) == ti);
        assert(inverse_word(seq![t]) =~= seq![ti]);
        lemma_word_inverse_left(hp, seq![t]);
        //  concat(inverse_word([t]), [t]) ≡ ε
        assert(concat(inverse_word(seq![t]), seq![t]) =~= seq![ti] + seq![t]);
        assert(seq![ti] + apply_embedding(aw, wit) + seq![t] =~= seq![ti] + seq![t]);
    } else {
        let sym = wit.first();
        let rest = wit.drop_first();
        assert(word_valid(rest, data.associations.len() as nat)) by {
            assert forall|q: int| 0 <= q < rest.len() implies symbol_valid(#[trigger] rest[q], data.associations.len() as nat) by {
                assert(rest[q] == wit[q + 1]);
            }
        }
        assert(symbol_valid(sym, data.associations.len() as nat)) by { assert(sym == wit[0]); }
        //  IH:  [ti]·φ_a(rest)·[t] ≡ φ_b(rest)
        lemma_hnn_conjugation_subgroup(data, rest);
        //  per-symbol:  [ti]·φ_a(sym)·[t] ≡ φ_b(sym)
        lemma_hnn_conj_symbol(data, sym);

        let asym = apply_embedding_symbol(aw, sym);
        let arest = apply_embedding(aw, rest);
        let bsym = apply_embedding_symbol(bw, sym);
        let brest = apply_embedding(bw, rest);
        //  φ_a(wit) = asym + arest
        assert(apply_embedding(aw, wit) =~= asym + arest);
        assert(apply_embedding(bw, wit) =~= bsym + brest);

        //  --- validity of the manipulated words (needed for lemma_equiv_symmetric) ---
        let ng = hp.num_generators;
        let tiw: Word = seq![ti];
        let tw: Word = seq![t];
        assert(symbol_valid(t, ng) && symbol_valid(ti, ng));
        assert(word_valid(tiw, ng)) by {
            assert forall|q: int| 0 <= q < tiw.len() implies symbol_valid(#[trigger] tiw[q], ng) by { }
        }
        assert(word_valid(tw, ng)) by {
            assert forall|q: int| 0 <= q < tw.len() implies symbol_valid(#[trigger] tw[q], ng) by { }
        }
        assert forall|q: int| 0 <= q < aw.len() implies word_valid(#[trigger] aw[q], ng) by {
            assert(aw[q] == data.associations[q].0);
            assert(word_valid(data.associations[q].0, data.base.num_generators));
            lemma_word_valid_mono(data.associations[q].0, data.base.num_generators, ng);
        }
        //  arest = φ_a(rest) valid
        lemma_apply_embedding_valid(aw, rest, ng);
        //  asym = φ_a([sym]) valid (apply_embedding over the singleton word collapses to asym)
        let symw: Word = seq![sym];
        assert(word_valid(symw, aw.len())) by {
            assert forall|q: int| 0 <= q < symw.len() implies symbol_valid(#[trigger] symw[q], aw.len()) by {
                assert(symw[q] == sym);
            }
        }
        lemma_apply_embedding_valid(aw, symw, ng);
        reveal_with_fuel(apply_embedding, 2);
        assert(symw.drop_first() =~= empty_word());
        assert(apply_embedding(aw, symw) =~= asym);
        //  csym = [ti]·asym·[t],  crest = [ti]·arest·[t]  valid
        lemma_concat_word_valid(tiw, asym, ng);
        lemma_concat_word_valid(tiw + asym, tw, ng);
        lemma_concat_word_valid(tiw, arest, ng);
        lemma_concat_word_valid(tiw + arest, tw, ng);
        lemma_concat_word_valid(seq![ti] + asym + seq![t], seq![ti] + arest + seq![t], ng);

        //  GOAL:  [ti] + asym + arest + [t]  ≡  bsym + brest.
        //  Insert  [t]·[ti] ≡ ε  to split conjugation across the product.
        let csym = seq![ti] + asym + seq![t];     //  ≡ bsym
        let crest = seq![ti] + arest + seq![t];   //  ≡ brest
        //  csym + crest = [ti]·asym·[t]·[ti]·arest·[t]
        //  delete the middle [t]·[ti] ≡ ε  →  [ti]·asym·arest·[t]
        lemma_inverse_word_one(t);
        assert(inverse_symbol(t) == ti);
        lemma_word_inverse_right(hp, seq![t]);   //  [t]·inverse_word([t]) ≡ ε
        assert(inverse_word(seq![t]) =~= seq![ti]);
        assert(equiv_in_presentation(hp, seq![t] + seq![ti], empty_word()));
        //  csym + crest =~= ([ti]+asym) · ([t]+[ti]) · (arest+[t])
        assert(csym + crest =~= (seq![ti] + asym) + (seq![t] + seq![ti]) + (arest + seq![t]));
        crate::britton_via_tower::lemma_delete_equiv_empty(hp, seq![ti] + asym, seq![t] + seq![ti], arest + seq![t]);
        //  → ([ti]+asym)·(arest+[t])
        assert((seq![ti] + asym) + (arest + seq![t]) =~= seq![ti] + asym + arest + seq![t]);
        assert(empty_word() + (arest + seq![t]) =~= arest + seq![t]);
        assert(concat(seq![ti] + asym, concat(seq![t] + seq![ti], arest + seq![t]))
            =~= csym + crest);
        assert(concat(seq![ti] + asym, arest + seq![t]) =~= seq![ti] + asym + arest + seq![t]);
        //  csym + crest ≡ [ti]·asym·arest·[t]   ( = goal LHS )
        lemma_equiv_symmetric(hp, csym + crest, seq![ti] + asym + arest + seq![t]);

        //  csym ≡ bsym, crest ≡ brest  ⟹  csym·crest ≡ bsym·brest
        lemma_equiv_concat_left(hp, csym, bsym, crest);     //  csym·crest ≡ bsym·crest
        lemma_equiv_concat_right(hp, bsym, crest, brest);   //  bsym·crest ≡ bsym·brest
        lemma_equiv_transitive(hp, csym + crest, bsym + crest, bsym + brest);
        //  chain:  goalLHS ≡ csym·crest ≡ bsym·brest = goalRHS
        lemma_equiv_transitive(hp, seq![ti] + asym + arest + seq![t], csym + crest, bsym + brest);
        assert(seq![ti] + apply_embedding(aw, wit) + seq![t] =~= seq![ti] + asym + arest + seq![t]);
        assert(bsym + brest =~= apply_embedding(bw, wit));
    }
}

//  φ_a(wit) and φ_b(wit) are valid words over the HNN presentation's generators.
pub proof fn lemma_hnn_phi_valid(data: HNNData, wit: Word)
    requires
        hnn_data_valid(data),
        word_valid(wit, data.associations.len() as nat),
    ensures
        word_valid(apply_embedding(hnn_a_words(data), wit), hnn_presentation(data).num_generators),
        word_valid(apply_embedding(hnn_b_words(data), wit), hnn_presentation(data).num_generators),
{
    let ng = hnn_presentation(data).num_generators;
    let aw = hnn_a_words(data);
    let bw = hnn_b_words(data);
    assert(aw.len() == data.associations.len());
    assert(bw.len() == data.associations.len());
    assert forall|q: int| 0 <= q < aw.len() implies word_valid(#[trigger] aw[q], ng) by {
        assert(aw[q] == data.associations[q].0);
        assert(word_valid(data.associations[q].0, data.base.num_generators));
        lemma_word_valid_mono(data.associations[q].0, data.base.num_generators, ng);
    }
    assert forall|q: int| 0 <= q < bw.len() implies word_valid(#[trigger] bw[q], ng) by {
        assert(bw[q] == data.associations[q].1);
        assert(word_valid(data.associations[q].1, data.base.num_generators));
        lemma_word_valid_mono(data.associations[q].1, data.base.num_generators, ng);
    }
    lemma_apply_embedding_valid(aw, wit, ng);
    lemma_apply_embedding_valid(bw, wit, ng);
}

//  ============================================================
//  Brick D1 — inverse-direction conjugation:  t · φ_b(wit) · t⁻¹ ≡ φ_a(wit).
//  ============================================================
//  The p·k·p⁻¹ pinch case needs the mirror of Brick A.  Derive it by conjugating Brick A's
//  relation by t on the left and t⁻¹ on the right, then cancelling the t·t⁻¹ collars.
pub proof fn lemma_hnn_conjugation_subgroup_inv(data: HNNData, wit: Word)
    requires
        hnn_data_valid(data),
        word_valid(wit, data.associations.len() as nat),
    ensures
        equiv_in_presentation(hnn_presentation(data),
            seq![stable_letter(data)] + apply_embedding(hnn_b_words(data), wit)
                + seq![stable_letter_inv(data)],
            apply_embedding(hnn_a_words(data), wit)),
{
    let hp = hnn_presentation(data);
    let t = stable_letter(data);
    let ti = stable_letter_inv(data);
    let ng = hp.num_generators;
    let x = apply_embedding(hnn_a_words(data), wit);   //  X = φ_a(wit)
    let y = apply_embedding(hnn_b_words(data), wit);   //  Y = φ_b(wit)
    let tw: Word = seq![t];
    let tiw: Word = seq![ti];
    crate::britton_infra::lemma_hnn_presentation_valid(data);
    lemma_hnn_phi_valid(data, wit);   //  word_valid(x, ng), word_valid(y, ng)
    assert(symbol_valid(t, ng) && symbol_valid(ti, ng));
    assert(word_valid(tw, ng)) by {
        assert forall|q: int| 0 <= q < tw.len() implies symbol_valid(#[trigger] tw[q], ng) by { }
    }
    assert(word_valid(tiw, ng)) by {
        assert forall|q: int| 0 <= q < tiw.len() implies symbol_valid(#[trigger] tiw[q], ng) by { }
    }
    //  validity of the conjugated word  lhs_conj = [t]·([ti]+X+[t])·[ti]
    lemma_concat_word_valid(tiw, x, ng);
    lemma_concat_word_valid(tiw + x, tw, ng);
    let inner = tiw + x + tw;
    lemma_concat_word_valid(tw, inner, ng);
    lemma_concat_word_valid(tw + inner, tiw, ng);
    let lhs_conj = tw + inner + tiw;

    //  A:  [ti]+X+[t] ≡ Y
    lemma_hnn_conjugation_subgroup(data, wit);
    //  conjugate by t (left) and ti (right)
    lemma_equiv_concat_right(hp, tw, inner, y);                //  [t]·inner ≡ [t]·Y
    lemma_equiv_concat_left(hp, tw + inner, tw + y, tiw);      //  ([t]·inner)·[ti] ≡ ([t]·Y)·[ti]
    //  lhs_conj ≡ [t]·Y·[ti] (= goal LHS)
    assert(lhs_conj =~= tw + inner + tiw);
    assert((tw + y) + tiw =~= tw + y + tiw);

    //  [t]+[ti] ≡ ε
    lemma_word_inverse_right(hp, tw);
    lemma_inverse_word_one(t);
    assert(inverse_symbol(t) == ti);
    assert(inverse_word(tw) =~= tiw);
    assert(equiv_in_presentation(hp, tw + tiw, empty_word()));

    //  reduce lhs_conj = [t]+[ti]+X+[t]+[ti]  ≡  X
    //  delete the front [t]+[ti]:
    crate::britton_via_tower::lemma_delete_equiv_empty(hp, empty_word(), tw + tiw, x + tw + tiw);
    assert(empty_word() + (x + tw + tiw) =~= x + tw + tiw);
    assert(concat(empty_word(), concat(tw + tiw, x + tw + tiw)) =~= (tw + tiw) + (x + tw + tiw));
    //  delete the back [t]+[ti]:
    crate::britton_via_tower::lemma_delete_equiv_empty(hp, x, tw + tiw, empty_word());
    assert(concat(x, concat(tw + tiw, empty_word())) =~= x + tw + tiw);
    assert(concat(x, empty_word()) =~= x);
    //  chain:  lhs_conj =~= (tw+tiw)+(x+tw+tiw) ≡ x+tw+tiw ≡ x
    assert(lhs_conj =~= (tw + tiw) + (x + tw + tiw));
    lemma_equiv_transitive(hp, (tw + tiw) + (x + tw + tiw), x + tw + tiw, x);
    //  so  lhs_conj ≡ x.  Combine with  lhs_conj ≡ [t]·Y·[ti].
    lemma_equiv_symmetric(hp, lhs_conj, tw + y + tiw);        //  needs word_valid(lhs_conj)
    lemma_equiv_transitive(hp, tw + y + tiw, lhs_conj, x);
}

//  ============================================================
//  Brick B — subgroup membership ⟹ an embedding witness word.
//  ============================================================
//  in_generated_subgroup uses a factor sequence (each factor a generator-or-inverse word).
//  To feed the conjugation engine (which works on a witness word over the k indices), we
//  convert: a factor sequence over `gens` becomes a witness word `wit` with
//  apply_embedding(gens, wit) = concat_all(factors).

//  Build the witness word from a factor sequence: map each factor to its index-symbol.
pub proof fn lemma_factors_to_witness(gens: Seq<Word>, factors: Seq<Word>) -> (wit: Word)
    requires
        factors_from_generators(gens, factors),
    ensures
        word_valid(wit, gens.len()),
        apply_embedding(gens, wit) =~= concat_all(factors),
    decreases factors.len(),
{
    if factors.len() == 0 {
        assert(concat_all(factors) =~= empty_word());
        assert(apply_embedding(gens, empty_word()) =~= empty_word());
        empty_word()
    } else {
        let first = factors.first();
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|q: int| 0 <= q < rest.len() implies is_generator_or_inverse(gens, #[trigger] rest[q]) by {
                assert(rest[q] == factors[q + 1]);
            }
        }
        let wit_rest = lemma_factors_to_witness(gens, rest);
        assert(is_generator_or_inverse(gens, first)) by { assert(first == factors[0]); }
        let j = choose|j: int| 0 <= j < gens.len() && (first == gens[j] || first == inverse_word(gens[j]));
        assert(0 <= j < gens.len() && (first == gens[j] || first == inverse_word(gens[j])));
        let sym = if first == gens[j] { Symbol::Gen(j as nat) } else { Symbol::Inv(j as nat) };
        let symw: Word = seq![sym];
        let wit = symw + wit_rest;
        //  validity
        assert(symbol_valid(sym, gens.len()));
        assert(word_valid(symw, gens.len())) by {
            assert forall|q: int| 0 <= q < symw.len() implies symbol_valid(#[trigger] symw[q], gens.len()) by {
                assert(symw[q] == sym);
            }
        }
        lemma_concat_word_valid(symw, wit_rest, gens.len());
        //  value:  apply_embedding(gens, wit) = apply_embedding_symbol(gens, sym) + φ(wit_rest)
        lemma_apply_embedding_concat(gens, symw, wit_rest);
        reveal_with_fuel(apply_embedding, 2);
        assert(symw.drop_first() =~= empty_word());
        assert(apply_embedding(gens, symw) =~= apply_embedding_symbol(gens, sym));
        //  apply_embedding_symbol(gens, sym) = first  (both Gen and Inv cases)
        assert(apply_embedding_symbol(gens, sym) =~= first);
        assert(concat_all(factors) =~= concat(first, concat_all(rest)));
        wit
    }
}

//  Membership form:  g ∈ ⟨gens⟩ ⟹ ∃ witness word `wit` with apply_embedding(gens, wit) ≡ g.
pub proof fn lemma_subgroup_member_to_witness(p: Presentation, gens: Seq<Word>, w: Word) -> (wit: Word)
    requires
        in_generated_subgroup(p, gens, w),
    ensures
        word_valid(wit, gens.len()),
        equiv_in_presentation(p, apply_embedding(gens, wit), w),
{
    let factors = choose|factors: Seq<Word>| #![trigger factors_from_generators(gens, factors)]
        factors_from_generators(gens, factors) && equiv_in_presentation(p, concat_all(factors), w);
    assert(factors_from_generators(gens, factors) && equiv_in_presentation(p, concat_all(factors), w));
    let wit = lemma_factors_to_witness(gens, factors);
    //  apply_embedding(gens, wit) =~= concat_all(factors) ≡ w
    assert(apply_embedding(gens, wit) =~= concat_all(factors));
    wit
}

//  ============================================================
//  Brick D2 — the local pinch equivalence (heart of L1).
//  ============================================================
//  K is an abstract subgroup of the base, presented as a predicate-generated subgroup
//  `in_subgroup_pred(base, kpred, ·)` (closure for free).  The only K-specific facts are the
//  φ-compatibility  φ(K∩A₊)=K∩A₋  (both inclusions).

//  φ(K∩A₊) ⊆ K∩A₋ :  if φ_a(wit) ∈ K then φ_b(wit) ∈ K.
pub open spec fn kp_compat_fwd(data: HNNData, kpred: spec_fn(Word) -> bool) -> bool {
    forall|wit: Word| #![trigger apply_embedding(hnn_a_words(data), wit)]
        word_valid(wit, data.associations.len() as nat) ==>
        (in_subgroup_pred(data.base, kpred, apply_embedding(hnn_a_words(data), wit))
            ==> in_subgroup_pred(data.base, kpred, apply_embedding(hnn_b_words(data), wit)))
}

//  φ(K∩A₊) ⊇ K∩A₋ :  if φ_b(wit) ∈ K then φ_a(wit) ∈ K.
pub open spec fn kp_compat_bwd(data: HNNData, kpred: spec_fn(Word) -> bool) -> bool {
    forall|wit: Word| #![trigger apply_embedding(hnn_b_words(data), wit)]
        word_valid(wit, data.associations.len() as nat) ==>
        (in_subgroup_pred(data.base, kpred, apply_embedding(hnn_b_words(data), wit))
            ==> in_subgroup_pred(data.base, kpred, apply_embedding(hnn_a_words(data), wit)))
}

//  φ_a(wit), φ_b(wit) are valid over the BASE generators (they are products of base words).
pub proof fn lemma_kp_phi_base_valid(data: HNNData, wit: Word)
    requires
        hnn_data_valid(data),
        word_valid(wit, data.associations.len() as nat),
    ensures
        word_valid(apply_embedding(hnn_a_words(data), wit), data.base.num_generators),
        word_valid(apply_embedding(hnn_b_words(data), wit), data.base.num_generators),
{
    let nb = data.base.num_generators;
    let aw = hnn_a_words(data);
    let bw = hnn_b_words(data);
    assert(aw.len() == data.associations.len());
    assert(bw.len() == data.associations.len());
    assert forall|q: int| 0 <= q < aw.len() implies word_valid(#[trigger] aw[q], nb) by {
        assert(aw[q] == data.associations[q].0);
    }
    assert forall|q: int| 0 <= q < bw.len() implies word_valid(#[trigger] bw[q], nb) by {
        assert(bw[q] == data.associations[q].1);
    }
    lemma_apply_embedding_valid(aw, wit, nb);
    lemma_apply_embedding_valid(bw, wit, nb);
}

//  A pinch's middle  [p^{b_i}]·k·[p^{b_i1}]  (opposite signs, k in the matching associated
//  subgroup and in K) is HNN-equivalent to a word c that is STILL in K (compatibility).
pub proof fn lemma_kp_pinch_middle(
    data: HNNData, kpred: spec_fn(Word) -> bool, b_i: bool, b_i1: bool, k: Word,
) -> (c: Word)
    requires
        hnn_data_valid(data),
        b_i != b_i1,
        word_valid(k, data.base.num_generators),
        b_i == false ==> in_generated_subgroup(data.base, hnn_a_words(data), k),
        b_i == true ==> in_generated_subgroup(data.base, hnn_b_words(data), k),
        in_subgroup_pred(data.base, kpred, k),
        kp_compat_fwd(data, kpred),
        kp_compat_bwd(data, kpred),
    ensures
        equiv_in_presentation(hnn_presentation(data),
            seq![kp_stable_sym(stable_letter(data), b_i)] + k + seq![kp_stable_sym(stable_letter(data), b_i1)],
            c),
        in_subgroup_pred(data.base, kpred, c),
        word_valid(c, data.base.num_generators),
{
    let hp = hnn_presentation(data);
    let base = data.base;
    let t = stable_letter(data);
    let ti = stable_letter_inv(data);
    let ng = hp.num_generators;
    let aw = hnn_a_words(data);
    let bw = hnn_b_words(data);
    crate::britton_infra::lemma_hnn_presentation_valid(data);
    lemma_word_valid_mono(k, base.num_generators, ng);
    if b_i == false {
        //  p⁻¹·k·p,  k ∈ A₊.  c = φ_b(wit).
        assert(b_i1 == true);
        assert(kp_stable_sym(t, b_i) == ti);
        assert(kp_stable_sym(t, b_i1) == t);
        let wit = lemma_subgroup_member_to_witness(base, aw, k);
        //  word_valid(wit, aw.len()=ka),  equiv(base, φ_a(wit), k)
        assert(aw.len() == data.associations.len());
        let xa = apply_embedding(aw, wit);   //  φ_a(wit)
        let c = apply_embedding(bw, wit);    //  φ_b(wit)
        lemma_hnn_phi_valid(data, wit);      //  word_valid(xa, ng), word_valid(c, ng)
        lemma_kp_phi_base_valid(data, wit);  //  word_valid(xa, nb), word_valid(c, nb)
        assert(presentation_valid(base));
        //  Brick B gave  equiv(base, xa, k);  embed into hp, flip:  equiv(hp, k, xa)
        lemma_base_embeds_in_hnn(data, xa, k);          //  equiv(hp, xa, k)
        lemma_equiv_symmetric(hp, xa, k);               //  equiv(hp, k, xa)
        //  [ti]·k·[t] ≡ [ti]·xa·[t]
        lemma_equiv_concat_right(hp, seq![ti], k, xa);
        lemma_equiv_concat_left(hp, seq![ti] + k, seq![ti] + xa, seq![t]);
        assert((seq![ti] + k) + seq![t] =~= seq![ti] + k + seq![t]);
        assert((seq![ti] + xa) + seq![t] =~= seq![ti] + xa + seq![t]);
        //  Brick A:  [ti]·xa·[t] ≡ c
        lemma_hnn_conjugation_subgroup(data, wit);
        lemma_equiv_transitive(hp, seq![ti] + k + seq![t], seq![ti] + xa + seq![t], c);
        //  in_k(c):  k ∈ K → xa ∈ K (respects equiv) → c ∈ K (compat fwd)
        lemma_equiv_symmetric(base, xa, k);             //  equiv(base, k, xa)
        lemma_in_subgroup_pred_respects_equiv(base, kpred, k, xa);
        assert(kp_compat_fwd(data, kpred));
        assert(in_subgroup_pred(base, kpred, c));        //  trigger compat_fwd on xa
        assert(seq![kp_stable_sym(t, b_i)] + k + seq![kp_stable_sym(t, b_i1)] =~= seq![ti] + k + seq![t]);
        c
    } else {
        //  p·k·p⁻¹,  k ∈ A₋.  c = φ_a(wit).
        assert(b_i1 == false);
        assert(kp_stable_sym(t, b_i) == t);
        assert(kp_stable_sym(t, b_i1) == ti);
        let wit = lemma_subgroup_member_to_witness(base, bw, k);
        assert(bw.len() == data.associations.len());
        let yb = apply_embedding(bw, wit);   //  φ_b(wit)
        let c = apply_embedding(aw, wit);    //  φ_a(wit)
        lemma_hnn_phi_valid(data, wit);
        lemma_kp_phi_base_valid(data, wit);
        assert(presentation_valid(base));
        lemma_base_embeds_in_hnn(data, yb, k);          //  equiv(hp, yb, k)
        lemma_equiv_symmetric(hp, yb, k);               //  equiv(hp, k, yb)
        //  [t]·k·[ti] ≡ [t]·yb·[ti]
        lemma_equiv_concat_right(hp, seq![t], k, yb);
        lemma_equiv_concat_left(hp, seq![t] + k, seq![t] + yb, seq![ti]);
        assert((seq![t] + k) + seq![ti] =~= seq![t] + k + seq![ti]);
        assert((seq![t] + yb) + seq![ti] =~= seq![t] + yb + seq![ti]);
        //  D1:  [t]·yb·[ti] ≡ c
        lemma_hnn_conjugation_subgroup_inv(data, wit);
        lemma_equiv_transitive(hp, seq![t] + k + seq![ti], seq![t] + yb + seq![ti], c);
        //  in_k(c):  k ∈ K → yb ∈ K → c ∈ K (compat bwd)
        lemma_equiv_symmetric(base, yb, k);             //  equiv(base, k, yb)
        lemma_in_subgroup_pred_respects_equiv(base, kpred, k, yb);
        assert(kp_compat_bwd(data, kpred));
        assert(in_subgroup_pred(base, kpred, c));        //  trigger compat_bwd on yb
        assert(seq![kp_stable_sym(t, b_i)] + k + seq![kp_stable_sym(t, b_i1)] =~= seq![t] + k + seq![ti]);
        c
    }
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
