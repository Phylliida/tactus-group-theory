//  ============================================================
//  E2.C / L1 — ⟨K,p⟩ pinch elimination (the central engine of property II).
//  ============================================================
//  Kept in its own module (separate from ii_subset's conjugation engine) to avoid trigger
//  pollution and concurrent-edit churn.  See docs/e2c-property-ii-design.md.
//
//  K is abstracted as `in_k: spec_fn(Word)->bool` with four hypotheses (all instantiated for
//  K=T(M) later via the in_subgroup_pred closure lemmas + property (v)):
//    H_resp : in_k respects base-equivalence
//    H_mul  : in_k closed under product
//    H_ab   : φ-compatibility A→B   (in_k(emb(a_gens,uw)) ⟹ in_k(emb(b_gens,uw)))
//    H_ba   : φ-compatibility B→A
//
//  L1 (this file): a KP-word with a KP-pinch at index i ⟹ a KP-word with 2 fewer p's, ≡ value,
//  still a KP-word.  Recursion is on the pinch index i — the base case (i==0) does the
//  conjugation surgery, the recursive case peels the head and recurses into the tail.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::hnn::*;
use crate::machine_group::{hnn_a_gens, hnn_b_gens, lemma_stable_conj_factorization,
    lemma_stable_conj_factorization_rev, lemma_in_gen_implies_emb, lemma_hnn_presentation_valid,
    lemma_word_valid_mono};
use crate::benign::{in_generated_subgroup, apply_embedding, lemma_apply_embedding_valid};
use crate::ii_subset::{KPWord, kp_value, kp_pcount, is_kp_word, lemma_kp_value_cons};
use crate::britton_via_tower::{is_stable, has_stable_letter};

verus! {

//  Forward φ-helper:  mid ∈ K∩A₊  ⟹  ∃ phi ∈ K with  p⁻¹·mid·p ≡ phi.
pub proof fn lemma_kp_phi_fwd(data: HNNData, in_k: spec_fn(Word) -> bool, mid: Word) -> (phi: Word)
    requires
        hnn_data_valid(data),
        forall|a: Word, b: Word| in_k(a) && #[trigger] equiv_in_presentation(data.base, a, b) ==> in_k(b),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_a_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_b_gens(data), uw)),
        in_k(mid),
        in_generated_subgroup(data.base, hnn_a_gens(data), mid),
    ensures
        in_k(phi),
        equiv_in_presentation(hnn_presentation(data),
            seq![stable_letter_inv(data)] + mid + seq![stable_letter(data)], phi),
{
    let pres = hnn_presentation(data);
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    let ag = hnn_a_gens(data);
    let bg = hnn_b_gens(data);
    let k = data.associations.len();
    lemma_in_gen_implies_emb(data.base, ag, mid);
    let uw = choose|uw: Word| word_valid(uw, ag.len() as nat)
        && equiv_in_presentation(data.base, apply_embedding(ag, uw), mid);
    assert(word_valid(uw, k as nat)
        && equiv_in_presentation(data.base, apply_embedding(ag, uw), mid));
    let g = apply_embedding(ag, uw);
    let phi = apply_embedding(bg, uw);
    //  validity of g (and pres) — needed by the symmetric flip (only its w1 must be valid)
    lemma_hnn_presentation_valid(data);
    assert(presentation_valid(data.base));
    assert(pres.num_generators == data.base.num_generators + 1);
    assert forall|t: int| 0 <= t < ag.len() implies word_valid(#[trigger] ag[t], data.base.num_generators)
        by { assert(ag[t] == data.associations[t].0); }
    lemma_apply_embedding_valid(ag, uw, data.base.num_generators);
    lemma_word_valid_mono(g, data.base.num_generators, pres.num_generators);
    //  conjugation:  [si] + g + [st] ≡ phi
    lemma_stable_conj_factorization(data, uw);
    //  bridge  mid ≡_pres g, flip to  mid ≡_pres g  (only g must be valid)
    lemma_base_embeds_in_hnn(data, g, mid);
    lemma_equiv_symmetric(pres, g, mid);
    //  congruence:  [si] + mid + [st] ≡ [si] + g + [st]
    lemma_equiv_concat_right(pres, seq![si], mid, g);
    lemma_equiv_concat_left(pres, seq![si] + mid, seq![si] + g, seq![st]);
    lemma_equiv_transitive(pres, seq![si] + mid + seq![st], seq![si] + g + seq![st], phi);
    //  in_k(phi):  H_resp (mid → g), then H_ab (uw)
    lemma_equiv_symmetric(data.base, g, mid);
    assert(in_k(g));
    assert(in_k(phi));
    phi
}

//  Reverse φ-helper:  mid ∈ K∩A₋  ⟹  ∃ phi ∈ K with  p·mid·p⁻¹ ≡ phi.
pub proof fn lemma_kp_phi_rev(data: HNNData, in_k: spec_fn(Word) -> bool, mid: Word) -> (phi: Word)
    requires
        hnn_data_valid(data),
        forall|a: Word, b: Word| in_k(a) && #[trigger] equiv_in_presentation(data.base, a, b) ==> in_k(b),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_b_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_a_gens(data), uw)),
        in_k(mid),
        in_generated_subgroup(data.base, hnn_b_gens(data), mid),
    ensures
        in_k(phi),
        equiv_in_presentation(hnn_presentation(data),
            seq![stable_letter(data)] + mid + seq![stable_letter_inv(data)], phi),
{
    let pres = hnn_presentation(data);
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    let ag = hnn_a_gens(data);
    let bg = hnn_b_gens(data);
    let k = data.associations.len();
    lemma_in_gen_implies_emb(data.base, bg, mid);
    let uw = choose|uw: Word| word_valid(uw, bg.len() as nat)
        && equiv_in_presentation(data.base, apply_embedding(bg, uw), mid);
    assert(word_valid(uw, k as nat)
        && equiv_in_presentation(data.base, apply_embedding(bg, uw), mid));
    let g = apply_embedding(bg, uw);
    let phi = apply_embedding(ag, uw);
    //  validity of g (and pres) — needed by the symmetric flip (only its w1 must be valid)
    lemma_hnn_presentation_valid(data);
    assert(presentation_valid(data.base));
    assert(pres.num_generators == data.base.num_generators + 1);
    assert forall|t: int| 0 <= t < bg.len() implies word_valid(#[trigger] bg[t], data.base.num_generators)
        by { assert(bg[t] == data.associations[t].1); }
    lemma_apply_embedding_valid(bg, uw, data.base.num_generators);
    lemma_word_valid_mono(g, data.base.num_generators, pres.num_generators);
    //  reverse conjugation:  [st] + g + [si] ≡ phi
    lemma_stable_conj_factorization_rev(data, uw);
    //  bridge  mid ≡_pres g, flip to  mid ≡_pres g  (only g must be valid)
    lemma_base_embeds_in_hnn(data, g, mid);
    lemma_equiv_symmetric(pres, g, mid);
    //  congruence:  [st] + mid + [si] ≡ [st] + g + [si]
    lemma_equiv_concat_right(pres, seq![st], mid, g);
    lemma_equiv_concat_left(pres, seq![st] + mid, seq![st] + g, seq![si]);
    lemma_equiv_transitive(pres, seq![st] + mid + seq![si], seq![st] + g + seq![si], phi);
    //  in_k(phi):  H_resp (mid → g), then H_ba (uw)
    lemma_equiv_symmetric(data.base, g, mid);
    assert(in_k(g));
    assert(in_k(phi));
    phi
}

//  A KP-pinch at index i: opposite-sign consecutive p's at tail[i], tail[i+1], with the
//  syllable between them (tail[i].1) lying in the appropriate associated subgroup.
//    tail[i].0 == false  (p⁻¹·mid·p)  ⟹  mid ∈ A₊ = ⟨a_gens⟩
//    tail[i].0 == true   (p·mid·p⁻¹)  ⟹  mid ∈ A₋ = ⟨b_gens⟩
pub open spec fn kp_has_pinch_at(data: HNNData, kp: KPWord, i: int) -> bool {
    &&& 0 <= i
    &&& i + 1 < kp.tail.len()
    &&& kp.tail[i].0 != kp.tail[i + 1].0
    &&& (kp.tail[i].0 == false ==> in_generated_subgroup(data.base, hnn_a_gens(data), kp.tail[i].1))
    &&& (kp.tail[i].0 == true ==> in_generated_subgroup(data.base, hnn_b_gens(data), kp.tail[i].1))
}

//  kp_value of a KP-word splits off its head:  value{head,tail} = head + value{ε,tail}.
pub proof fn lemma_kp_value_head_split(stable: Symbol, head: Word, tail: Seq<(bool, Word)>)
    ensures
        kp_value(stable, KPWord { head, tail })
            =~= head + kp_value(stable, KPWord { head: empty_word(), tail }),
{
    if tail.len() == 0 {
        assert(kp_value(stable, KPWord { head, tail }) =~= head);
        assert(kp_value(stable, KPWord { head: empty_word(), tail }) =~= empty_word());
        assert(head + empty_word() =~= head);
    } else {
        lemma_kp_value_cons(stable, KPWord { head, tail });
        lemma_kp_value_cons(stable, KPWord { head: empty_word(), tail });
    }
}

//  ============================================================
//  L1 — eliminate one KP-pinch (the hard core of property II).
//  ============================================================
//  A KP-word with a pinch at i ⟹ a KP-word with 2 fewer p's, ≡ value, still a KP-word.
//  Recursion on the pinch index i:  base case (i==0) splices φ(mid) for the cancelling p's;
//  recursive case peels the head and recurses into the tail.
pub proof fn lemma_kp_eliminate_pinch(
    data: HNNData, in_k: spec_fn(Word) -> bool, kp: KPWord, i: int,
) -> (kp_prime: KPWord)
    requires
        hnn_data_valid(data),
        forall|a: Word, b: Word| in_k(a) && #[trigger] equiv_in_presentation(data.base, a, b) ==> in_k(b),
        forall|a: Word, b: Word| in_k(a) && in_k(b) ==> in_k(#[trigger] (a + b)),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_a_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_b_gens(data), uw)),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_b_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_a_gens(data), uw)),
        is_kp_word(in_k, kp),
        kp_has_pinch_at(data, kp, i),
    ensures
        kp_pcount(kp_prime) == kp_pcount(kp) - 2,
        is_kp_word(in_k, kp_prime),
        equiv_in_presentation(hnn_presentation(data),
            kp_value(stable_letter(data), kp), kp_value(stable_letter(data), kp_prime)),
    decreases i,
{
    let st = stable_letter(data);
    let si = stable_letter_inv(data);
    let pres = hnn_presentation(data);
    let tail = kp.tail;
    assert(inverse_symbol(st) == si);
    if i == 0 {
        //  ===== BASE CASE: the surgery =====
        let mid = tail[0].1;
        let m1 = tail.drop_first().first().1;
        let t2 = tail.drop_first().drop_first();
        let rest1 = KPWord { head: tail.first().1, tail: tail.drop_first() };
        let rest2 = KPWord { head: m1, tail: t2 };
        assert(tail.drop_first()[0] == tail[1]);
        assert(tail.drop_first().first() == tail[1]);
        assert(m1 == tail[1].1);

        lemma_kp_value_cons(st, kp);
        lemma_kp_value_cons(st, rest1);

        let s0sym = if tail[0].0 { st } else { si };
        let s1sym = if tail[1].0 { st } else { si };
        let conj = seq![s0sym] + mid + seq![s1sym];

        let phi: Word;
        if tail[0].0 == false {
            assert(tail[1].0 == true);
            assert(in_generated_subgroup(data.base, hnn_a_gens(data), mid));
            phi = lemma_kp_phi_fwd(data, in_k, mid);
            assert(conj =~= seq![si] + mid + seq![st]);
        } else {
            assert(tail[0].0 == true);
            assert(tail[1].0 == false);
            assert(in_generated_subgroup(data.base, hnn_b_gens(data), mid));
            phi = lemma_kp_phi_rev(data, in_k, mid);
            assert(conj =~= seq![st] + mid + seq![si]);
        }
        assert(equiv_in_presentation(pres, conj, phi));
        assert(in_k(phi));

        let kp_prime = KPWord { head: kp.head + phi + m1, tail: t2 };

        //  --- value preservation ---
        assert(kp_value(st, kp) =~= kp.head + conj + kp_value(st, rest2));
        lemma_equiv_concat_right(pres, kp.head, conj, phi);
        lemma_equiv_concat_left(pres, kp.head + conj, kp.head + phi, kp_value(st, rest2));
        lemma_kp_value_head_split(st, kp_prime.head, t2);
        lemma_kp_value_head_split(st, m1, t2);
        assert(kp.head + phi + kp_value(st, rest2) =~= kp_value(st, kp_prime));
        assert(equiv_in_presentation(pres, kp_value(st, kp), kp_value(st, kp_prime)));

        //  --- is_kp_word(kp_prime) ---
        assert(in_k(kp.head));
        assert(in_k(m1));
        assert(in_k(kp.head + phi));
        assert(in_k(kp.head + phi + m1));
        assert(is_kp_word(in_k, kp_prime)) by {
            assert(in_k(kp_prime.head));
            assert forall|j: int| 0 <= j < kp_prime.tail.len()
                implies in_k(#[trigger] kp_prime.tail[j].1) by {
                assert(kp_prime.tail[j] == tail[j + 2]);
            }
        }
        assert(kp_pcount(kp_prime) == kp_pcount(kp) - 2);
        kp_prime
    } else {
        //  ===== RECURSIVE CASE: peel the head =====
        let rest = KPWord { head: tail.first().1, tail: tail.drop_first() };
        assert(is_kp_word(in_k, rest)) by {
            assert(rest.head == tail[0].1);
            assert(in_k(rest.head));
            assert forall|j: int| 0 <= j < rest.tail.len()
                implies in_k(#[trigger] rest.tail[j].1) by {
                assert(rest.tail[j] == tail[j + 1]);
            }
        }
        assert(kp_has_pinch_at(data, rest, i - 1)) by {
            assert(rest.tail[i - 1] == tail[i]);
            assert(rest.tail[i] == tail[i + 1]);
        }
        let rest_prime = lemma_kp_eliminate_pinch(data, in_k, rest, i - 1);
        let kp_prime = KPWord {
            head: kp.head,
            tail: seq![(tail.first().0, rest_prime.head)] + rest_prime.tail,
        };
        let prefix = kp.head + seq![if tail.first().0 { st } else { inverse_symbol(st) }];
        assert(kp_prime.tail.first() == (tail.first().0, rest_prime.head));
        assert(kp_prime.tail.drop_first() =~= rest_prime.tail);
        lemma_kp_value_cons(st, kp);
        lemma_kp_value_cons(st, kp_prime);
        assert(kp_value(st, kp) =~= prefix + kp_value(st, rest));
        assert(kp_value(st, kp_prime) =~= prefix + kp_value(st, rest_prime));
        lemma_equiv_concat_right(pres, prefix, kp_value(st, rest), kp_value(st, rest_prime));
        assert(equiv_in_presentation(pres, kp_value(st, kp), kp_value(st, kp_prime)));

        assert(is_kp_word(in_k, kp_prime)) by {
            assert(in_k(kp_prime.head));
            assert forall|j: int| 0 <= j < kp_prime.tail.len()
                implies in_k(#[trigger] kp_prime.tail[j].1) by {
                if j == 0 {
                    assert(kp_prime.tail[0] == (tail.first().0, rest_prime.head));
                    assert(in_k(rest_prime.head));
                } else {
                    assert(kp_prime.tail[j] == rest_prime.tail[j - 1]);
                }
            }
        }
        assert(kp_prime.tail.len() == 1 + rest_prime.tail.len());
        assert(kp_pcount(kp_prime) == kp_pcount(kp) - 2);
        kp_prime
    }
}

//  ============================================================
//  L2 — reduce a KP-word to pinch-free form (induction on kp_pcount via L1).
//  ============================================================

//  A KP-word is pinch-free if it has no KP-pinch at any index.
pub open spec fn kp_pinch_free(data: HNNData, kp: KPWord) -> bool {
    forall|i: int| !kp_has_pinch_at(data, kp, i)
}

//  Every KP-word reduces to a pinch-free KP-word with equivalent value.
pub proof fn lemma_kp_reduce_pinch_free(
    data: HNNData, in_k: spec_fn(Word) -> bool, kp: KPWord,
) -> (kp_prime: KPWord)
    requires
        hnn_data_valid(data),
        forall|a: Word, b: Word| in_k(a) && #[trigger] equiv_in_presentation(data.base, a, b) ==> in_k(b),
        forall|a: Word, b: Word| in_k(a) && in_k(b) ==> in_k(#[trigger] (a + b)),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_a_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_b_gens(data), uw)),
        forall|uw: Word| word_valid(uw, data.associations.len() as nat)
            && in_k(apply_embedding(hnn_b_gens(data), uw))
            ==> in_k(#[trigger] apply_embedding(hnn_a_gens(data), uw)),
        is_kp_word(in_k, kp),
    ensures
        is_kp_word(in_k, kp_prime),
        kp_pinch_free(data, kp_prime),
        equiv_in_presentation(hnn_presentation(data),
            kp_value(stable_letter(data), kp), kp_value(stable_letter(data), kp_prime)),
    decreases kp_pcount(kp),
{
    let pres = hnn_presentation(data);
    let st = stable_letter(data);
    if exists|i: int| kp_has_pinch_at(data, kp, i) {
        let i = choose|i: int| kp_has_pinch_at(data, kp, i);
        assert(kp_has_pinch_at(data, kp, i));
        let kp1 = lemma_kp_eliminate_pinch(data, in_k, kp, i);
        assert(kp_pcount(kp1) < kp_pcount(kp));         //  L1 dropped pcount by 2 (≥ 2 before)
        let kp_prime = lemma_kp_reduce_pinch_free(data, in_k, kp1);
        lemma_equiv_transitive(pres,
            kp_value(st, kp), kp_value(st, kp1), kp_value(st, kp_prime));
        kp_prime
    } else {
        assert(kp_pinch_free(data, kp));
        lemma_equiv_refl(pres, kp_value(st, kp));
        kp
    }
}

//  ============================================================
//  Assembly support — no-KP-pinch ⟹ no-raw-pinch (the design's flagged subtlety).
//  ============================================================
//  For the Britton assembly we feed W := kp_value(t, kp) into britton_lemma_full, which needs the
//  raw word to be (a) word_valid over the HNN presentation and (b) RAW-pinch-free.  The structural
//  fact behind (b): every syllable (head, kᵢ) is a BASE word — so the only stable letters in W are
//  the p^{sᵢ} separators, hence a raw pinch's two p's are consecutive separators whose middle is the
//  syllable kₘ, and the pinch condition on it is exactly a KP-pinch at m.  Foundation first (3a/3b):
//  the syllable-validity predicate and W's word-validity.

//  Every syllable (head and each kᵢ) is a word over the BASE generators — i.e. stable-free, since
//  the stable letter is generator index base.num_generators (so a base word can never contain it).
pub open spec fn kp_syllables_valid(data: HNNData, kp: KPWord) -> bool {
    &&& word_valid(kp.head, data.base.num_generators)
    &&& forall|i: int| 0 <= i < kp.tail.len()
            ==> word_valid(#[trigger] kp.tail[i].1, data.base.num_generators)
}

//  3b — W = kp_value(t, kp) is word_valid over the HNN presentation.  Induction on the tail via
//  lemma_kp_value_cons:  head (base, lift by mono) · [p^{s}] (the stable letter, index ng < ng+1) ·
//  kp_value(rest) (IH).
pub proof fn lemma_kp_value_word_valid(data: HNNData, kp: KPWord)
    requires
        hnn_data_valid(data),
        kp_syllables_valid(data, kp),
    ensures
        word_valid(kp_value(stable_letter(data), kp), hnn_presentation(data).num_generators),
    decreases kp.tail.len(),
{
    let ng = data.base.num_generators;
    let st = stable_letter(data);
    let png = hnn_presentation(data).num_generators;
    lemma_hnn_presentation_valid(data);
    assert(png == ng + 1);
    assert(word_valid(kp.head, ng));                 //  from kp_syllables_valid
    lemma_word_valid_mono(kp.head, ng, png);
    if kp.tail.len() == 0 {
        assert(kp_value(st, kp) == kp.head);         //  empty-tail branch of kp_value
    } else {
        let b = kp.tail.first().0;
        let p_sym = if b { st } else { inverse_symbol(st) };
        let rest = KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() };
        lemma_kp_value_cons(st, kp);
        //  kp_value(st, kp) =~= kp.head + [p_sym] + kp_value(st, rest)
        assert(kp_syllables_valid(data, rest)) by {
            assert(kp.tail[0] == kp.tail.first());
            assert(word_valid(rest.head, ng));       //  rest.head = kp.tail[0].1
            assert forall|i: int| 0 <= i < rest.tail.len()
                implies word_valid(#[trigger] rest.tail[i].1, ng)
            by { assert(rest.tail[i] == kp.tail[i + 1]); }
        }
        lemma_kp_value_word_valid(data, rest);       //  IH: word_valid(kp_value(st, rest), png)
        //  p_sym is the stable letter or its inverse: Gen(ng) / Inv(ng), index ng < png.
        assert(st == Symbol::Gen(ng) && inverse_symbol(st) == Symbol::Inv(ng));
        assert(symbol_valid(p_sym, png));
        let psw: Word = seq![p_sym];
        assert(word_valid(psw, png)) by {
            assert forall|k: int| 0 <= k < psw.len()
                implies symbol_valid(#[trigger] psw[k], png) by { }
        }
        //  concat the three valid pieces (concat == +).
        lemma_concat_word_valid(kp.head, psw, png);
        assert(concat(kp.head, psw) == kp.head + psw);
        lemma_concat_word_valid(kp.head + psw, kp_value(st, rest), png);
        assert(concat(kp.head + psw, kp_value(st, rest)) == (kp.head + psw) + kp_value(st, rest));
        assert(kp_value(st, kp) =~= (kp.head + psw) + kp_value(st, rest));
    }
}

//  A word over the base generators contains no stable letter:  t = Gen(ng) and t⁻¹ = Inv(ng) both
//  have generator_index ng, which a base symbol's index never reaches.  Reused by 3c (syllables
//  contribute no stable letters) and by the junction (appending a base word adds no stable letters).
pub proof fn lemma_base_word_no_stable(data: HNNData, w: Word)
    requires
        word_valid(w, data.base.num_generators),
    ensures
        !has_stable_letter(data, w),
{
    let ng = data.base.num_generators;
    assert(generator_index(Symbol::Gen(ng)) == ng && generator_index(Symbol::Inv(ng)) == ng);
    assert forall|i: int| 0 <= i < w.len() implies !is_stable(data, #[trigger] w[i]) by {
        assert(symbol_valid(w[i], ng));   //  generator_index(w[i]) < ng ⟹ w[i] ∉ {Gen(ng), Inv(ng)}
    }
}

} //  verus!
