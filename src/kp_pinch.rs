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
use crate::britton_via_tower::{is_stable, has_stable_letter, has_pinch_at, has_pinch,
    has_adjacent_opposite_at};

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

//  ============================================================
//  3c — the structural core: no-KP-pinch ⟹ no-raw-pinch.
//  ============================================================
//  W := kp_value(t, kp) is ALTERNATING: head and each syllable kᵢ are BASE words (kp_syllables_valid),
//  so the only stable letters of W are the n separators p^{sᵢ}.  Hence a raw Britton pinch (two
//  adjacent-opposite stable letters with a base-word middle) must land on two CONSECUTIVE separators
//  whose middle is exactly a syllable kₘ — and the pinch condition on it is exactly kp_has_pinch_at(kp,m).
//  Proven by head-peeling induction on kp.tail.  Modular helpers keep each Z3 context small.

//  Per-index version of lemma_base_word_no_stable: a base word's k-th symbol is never stable.
pub proof fn lemma_base_word_index_no_stable(data: HNNData, w: Word, k: int)
    requires
        word_valid(w, data.base.num_generators),
        0 <= k < w.len(),
    ensures
        !is_stable(data, w[k]),
{
    let ng = data.base.num_generators;
    assert(symbol_valid(w[k], ng));                  //  generator_index(w[k]) < ng
    assert(generator_index(Symbol::Gen(ng)) == ng);
    assert(generator_index(Symbol::Inv(ng)) == ng);  //  both stable symbols have index ng > index(w[k])
}

//  Subrange of a concatenation lying entirely in the right part shifts down by |pre|.
pub proof fn lemma_word_subrange_concat_right(pre: Word, w2: Word, a: int, b: int)
    requires
        pre.len() <= a,
        a <= b,
        b <= pre.len() + w2.len(),
    ensures
        (pre + w2).subrange(a, b) =~= w2.subrange(a - pre.len() as int, b - pre.len() as int),
{
    let lhs = (pre + w2).subrange(a, b);
    let rhs = w2.subrange(a - pre.len() as int, b - pre.len() as int);
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
        assert(lhs[k] == (pre + w2)[a + k]);
        assert(a + k >= pre.len());
        assert(a + k < (pre + w2).len());
        assert((pre + w2)[a + k] == w2[a + k - pre.len() as int]);
        assert(rhs[k] == w2[(a - pre.len() as int) + k]);
    }
}

//  The pinch generator-lists (inline Seq::new in has_pinch_at) coincide with hnn_a_gens / hnn_b_gens.
pub proof fn lemma_pinch_gens_eq(data: HNNData)
    ensures
        Seq::new(data.associations.len(), |k: int| data.associations[k].0) =~= hnn_a_gens(data),
        Seq::new(data.associations.len(), |k: int| data.associations[k].1) =~= hnn_b_gens(data),
{
    assert(Seq::new(data.associations.len(), |k: int| data.associations[k].0) =~= hnn_a_gens(data));
    assert(Seq::new(data.associations.len(), |k: int| data.associations[k].1) =~= hnn_b_gens(data));
}

//  First-stable structure of W = kp_value(t, kp) when the tail is non-empty:  the head occupies the
//  initial |head| positions (all base/non-stable), and position |head| is the first separator p^{s₀}.
pub proof fn lemma_kp_first_stable(data: HNNData, kp: KPWord)
    requires
        kp_syllables_valid(data, kp),
        kp.tail.len() >= 1,
    ensures
        kp_value(stable_letter(data), kp).len() > kp.head.len(),
        forall|k: int| 0 <= k < kp.head.len()
            ==> !is_stable(data, #[trigger] kp_value(stable_letter(data), kp)[k]),
        is_stable(data, kp_value(stable_letter(data), kp)[kp.head.len() as int]),
        kp_value(stable_letter(data), kp)[kp.head.len() as int]
            == (if kp.tail.first().0 { stable_letter(data) } else { inverse_symbol(stable_letter(data)) }),
        kp_value(stable_letter(data), kp).subrange(0, kp.head.len() as int) =~= kp.head,
{
    let st = stable_letter(data);
    let ng = data.base.num_generators;
    let p_sym = if kp.tail.first().0 { st } else { inverse_symbol(st) };
    let rest = KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() };
    let Wp = kp_value(st, rest);
    let W = kp_value(st, kp);
    let pre = kp.head + seq![p_sym];
    let H = kp.head.len() as int;
    lemma_kp_value_cons(st, kp);
    assert(W =~= pre + Wp);
    assert(pre.len() == H + 1);
    assert(W.len() == pre.len() + Wp.len());
    assert(W.len() > H);
    //  head positions are non-stable
    assert forall|k: int| 0 <= k < H implies !is_stable(data, #[trigger] W[k]) by {
        assert(W[k] == pre[k]);            //  k < H+1 = pre.len()
        assert(pre[k] == kp.head[k]);      //  k < H = kp.head.len()
        lemma_base_word_index_no_stable(data, kp.head, k);
    }
    //  position H is the first separator
    assert(W[H] == pre[H]);                //  H < H+1
    assert(H >= kp.head.len());
    assert(pre[H] == seq![p_sym][0]);      //  H >= |head| ⟹ index into the [p_sym] tail of pre
    assert(W[H] == p_sym);
    assert(st == Symbol::Gen(ng) && inverse_symbol(st) == Symbol::Inv(ng));
    assert(is_stable(data, p_sym));
    //  prefix subrange == head
    assert(W.subrange(0, H) =~= kp.head) by {
        assert(W.subrange(0, H).len() == H);
        assert forall|k: int| 0 <= k < H implies #[trigger] W.subrange(0, H)[k] == kp.head[k] by {
            assert(W.subrange(0, H)[k] == W[k]);
            assert(W[k] == pre[k]);
            assert(pre[k] == kp.head[k]);
        }
    }
}

//  Case A of the head-peel: when the raw pinch's first stable letter IS the leading separator p^{s₀}
//  (position |head|), the pinch is exactly kp_has_pinch_at(kp, 0) — its middle is the first syllable k₀.
pub proof fn lemma_kp_pinch_case_a(data: HNNData, kp: KPWord, i: int, j: int)
    requires
        kp_syllables_valid(data, kp),
        kp.tail.len() >= 1,
        i == kp.head.len() as int,
        has_pinch_at(data, kp_value(stable_letter(data), kp), i, j),
    ensures
        kp_has_pinch_at(data, kp, 0),
{
    let st = stable_letter(data);
    let ng = data.base.num_generators;
    let W = kp_value(st, kp);
    let H = kp.head.len() as int;
    let p_sym = if kp.tail.first().0 { st } else { inverse_symbol(st) };
    let rest = KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() };
    let Wp = kp_value(st, rest);
    let pre = kp.head + seq![p_sym];
    lemma_kp_value_cons(st, kp);
    assert(W =~= pre + Wp);
    assert(pre.len() == H + 1);
    assert(W.len() == pre.len() + Wp.len());
    //  surface the raw-pinch facts
    assert(is_stable(data, W[i]) && is_stable(data, W[j]) && W[i] != W[j] && 0 <= i < j < W.len());
    //  first separator: W[H] == p_sym, W[i] == p_sym
    lemma_kp_first_stable(data, kp);
    assert(kp.tail.first() == kp.tail[0]);
    assert(W[i] == p_sym);
    //  the second stable letter lives in Wp at jp
    assert(j >= H + 1);
    assert(j >= pre.len());
    let jp = j - (H + 1);
    assert(W[j] == Wp[jp]);
    assert(jp >= 0 && jp < Wp.len());
    assert(is_stable(data, Wp[jp]));
    //  no stable strictly before jp in Wp (mapped from "no stable between i and j" in W)
    assert forall|k2: int| 0 <= k2 < jp implies !is_stable(data, #[trigger] Wp[k2]) by {
        assert(k2 + (H + 1) >= pre.len());
        assert(k2 + (H + 1) < W.len());
        assert(W[k2 + (H + 1)] == Wp[k2]);
        assert(i < k2 + (H + 1) < j);          //  i == H
    }
    //  Wp must contain a separator ⟹ rest.tail is non-empty
    if rest.tail.len() == 0 {
        assert(Wp == rest.head);
        lemma_base_word_index_no_stable(data, rest.head, jp);
        assert(false);
    }
    assert(rest.tail.len() >= 1);
    assert(rest.tail.len() == kp.tail.len() - 1);
    assert(kp.tail.len() >= 2);
    //  syllable-validity of rest
    assert(kp_syllables_valid(data, rest)) by {
        assert(kp.tail[0] == kp.tail.first());
        assert(word_valid(rest.head, ng));
        assert forall|t: int| 0 <= t < rest.tail.len()
            implies word_valid(#[trigger] rest.tail[t].1, ng) by {
            assert(rest.tail[t] == kp.tail[t + 1]);
        }
    }
    //  first-stable of Wp pins jp == |rest.head|
    lemma_kp_first_stable(data, rest);
    let Hp = rest.head.len() as int;
    if jp < Hp { assert(!is_stable(data, Wp[jp])); assert(false); }
    if jp > Hp { assert(0 <= Hp < jp); assert(!is_stable(data, Wp[Hp])); assert(false); }
    assert(jp == Hp);
    //  second separator p^{s₁}
    assert(rest.tail.first() == kp.tail[1]) by {
        assert(rest.tail =~= kp.tail.drop_first());
        assert(rest.tail.first() == kp.tail.drop_first()[0]);
        assert(kp.tail.drop_first()[0] == kp.tail[1]);
    }
    let p1_sym = if kp.tail[1].0 { st } else { inverse_symbol(st) };
    assert(Wp[Hp] == p1_sym);
    assert(W[j] == p1_sym);
    //  signs differ
    assert(st == Symbol::Gen(ng) && inverse_symbol(st) == Symbol::Inv(ng));
    assert(st != inverse_symbol(st));
    assert(kp.tail[0].0 != kp.tail[1].0) by {
        if kp.tail[0].0 == kp.tail[1].0 {
            assert(p_sym == p1_sym);
            assert(W[i] == W[j]);
            assert(false);
        }
    }
    //  middle == k₀ = kp.tail[0].1
    lemma_word_subrange_concat_right(pre, Wp, i + 1, j);
    assert(i + 1 - pre.len() == 0);
    assert(j - pre.len() == jp);
    assert((pre + Wp).subrange(i + 1, j) =~= Wp.subrange(0, jp));
    assert(W.subrange(i + 1, j) =~= Wp.subrange(0, jp));
    assert(Wp.subrange(0, jp) =~= rest.head);                  //  jp == Hp; first-stable(rest) prefix
    assert(rest.head == kp.tail[0].1);
    assert(W.subrange(i + 1, j) =~= kp.tail[0].1);
    //  gens bridge
    let a_gens = Seq::new(data.associations.len(), |k: int| data.associations[k].0);
    let b_gens = Seq::new(data.associations.len(), |k: int| data.associations[k].1);
    lemma_pinch_gens_eq(data);
    assert(a_gens == hnn_a_gens(data));
    assert(b_gens == hnn_b_gens(data));
    //  conclude kp_has_pinch_at(kp, 0)
    assert(kp_has_pinch_at(data, kp, 0)) by {
        assert(0 + 1 < kp.tail.len());
        assert(kp.tail[0].0 != kp.tail[1].0);
        if kp.tail[0].0 == false {
            assert(W[i] == Symbol::Inv(ng));               //  p_sym == inverse_symbol(st) == Inv(ng)
            assert(in_generated_subgroup(data.base, a_gens, W.subrange(i + 1, j)));
            assert(W.subrange(i + 1, j) == kp.tail[0].1);
            assert(in_generated_subgroup(data.base, hnn_a_gens(data), kp.tail[0].1));
        }
        if kp.tail[0].0 == true {
            assert(W[i] == Symbol::Gen(ng));               //  p_sym == st == Gen(ng)
            assert(in_generated_subgroup(data.base, b_gens, W.subrange(i + 1, j)));
            assert(W.subrange(i + 1, j) == kp.tail[0].1);
            assert(in_generated_subgroup(data.base, hnn_b_gens(data), kp.tail[0].1));
        }
    }
}

//  Case B of the head-peel: when the raw pinch lies strictly past the leading separator, it is a raw
//  pinch of the peeled word Wp = kp_value(t, rest), shifted down by |head|+1.
pub proof fn lemma_kp_pinch_transfer_tail(data: HNNData, kp: KPWord, i: int, j: int)
    requires
        kp_syllables_valid(data, kp),
        kp.tail.len() >= 1,
        i > kp.head.len() as int,
        has_pinch_at(data, kp_value(stable_letter(data), kp), i, j),
    ensures
        has_pinch_at(data, kp_value(stable_letter(data),
            KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() }),
            i - (kp.head.len() as int + 1), j - (kp.head.len() as int + 1)),
{
    let st = stable_letter(data);
    let W = kp_value(st, kp);
    let H = kp.head.len() as int;
    let p_sym = if kp.tail.first().0 { st } else { inverse_symbol(st) };
    let rest = KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() };
    let Wp = kp_value(st, rest);
    let pre = kp.head + seq![p_sym];
    lemma_kp_value_cons(st, kp);
    assert(W =~= pre + Wp);
    assert(pre.len() == H + 1);
    assert(W.len() == pre.len() + Wp.len());
    let ip = i - (H + 1);
    let jp = j - (H + 1);
    assert(is_stable(data, W[i]) && is_stable(data, W[j]) && W[i] != W[j] && 0 <= i < j < W.len());
    assert(i >= H + 1 && i >= pre.len() && j >= pre.len());
    assert(ip >= 0 && ip < jp && jp < Wp.len());
    assert(W[i] == Wp[ip]);
    assert(W[j] == Wp[jp]);
    //  no stable strictly between ip and jp in Wp
    assert forall|k2: int| ip < k2 < jp implies !is_stable(data, #[trigger] Wp[k2]) by {
        assert(k2 + (H + 1) >= pre.len());
        assert(k2 + (H + 1) < W.len());
        assert(W[k2 + (H + 1)] == Wp[k2]);
        assert(i < k2 + (H + 1) < j);
    }
    //  middle subrange is preserved (shifted)
    lemma_word_subrange_concat_right(pre, Wp, i + 1, j);
    assert(i + 1 - pre.len() == ip + 1);
    assert(j - pre.len() == jp);
    assert((pre + Wp).subrange(i + 1, j) =~= Wp.subrange(ip + 1, jp));
    assert(W.subrange(i + 1, j) =~= Wp.subrange(ip + 1, jp));
    //  assemble has_pinch_at(Wp, ip, jp): symbols and middle (and the inline gen-lists) all match W's
    assert(has_pinch_at(data, Wp, ip, jp)) by {
        assert(0 <= ip < jp < Wp.len());
        assert(is_stable(data, Wp[ip]) && is_stable(data, Wp[jp]) && Wp[ip] != Wp[jp]);
        assert(Wp.subrange(ip + 1, jp) == W.subrange(i + 1, j));
    }
}

//  Index-shift for KP-pinches under head-peeling:  a KP-pinch of rest at m is a KP-pinch of kp at m+1.
pub proof fn lemma_kp_pinch_lift(data: HNNData, kp: KPWord, m: int)
    requires
        kp.tail.len() >= 1,
        kp_has_pinch_at(data, KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() }, m),
    ensures
        kp_has_pinch_at(data, kp, m + 1),
{
    let rest = KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() };
    assert(rest.tail =~= kp.tail.drop_first());
    assert(rest.tail.len() == kp.tail.len() - 1);
    assert(rest.tail[m] == kp.tail[m + 1]) by {
        assert(rest.tail[m] == kp.tail.drop_first()[m]);
        assert(kp.tail.drop_first()[m] == kp.tail[m + 1]);
    }
    assert(rest.tail[m + 1] == kp.tail[m + 2]) by {
        assert(rest.tail[m + 1] == kp.tail.drop_first()[m + 1]);
        assert(kp.tail.drop_first()[m + 1] == kp.tail[m + 2]);
    }
    assert(kp_has_pinch_at(data, kp, m + 1)) by {
        assert(0 <= m + 1);
        assert((m + 1) + 1 < kp.tail.len());
        assert(kp.tail[m + 1].0 == rest.tail[m].0 && kp.tail[m + 1].1 == rest.tail[m].1);
        assert(kp.tail[m + 2].0 == rest.tail[m + 1].0);
    }
}

//  The structural core (3c, witness form):  a raw pinch of W = kp_value(t, kp) yields a KP-pinch of kp.
pub proof fn lemma_kp_raw_pinch_gives_kp_pinch(data: HNNData, kp: KPWord, i: int, j: int) -> (m: int)
    requires
        kp_syllables_valid(data, kp),
        has_pinch_at(data, kp_value(stable_letter(data), kp), i, j),
    ensures
        kp_has_pinch_at(data, kp, m),
    decreases kp.tail.len(),
{
    let st = stable_letter(data);
    let W = kp_value(st, kp);
    let H = kp.head.len() as int;
    if kp.tail.len() == 0 {
        //  W = head, a base word ⟹ no stable letters ⟹ the pinch is impossible.
        assert(W == kp.head);
        assert(0 <= i < j < W.len());
        lemma_base_word_index_no_stable(data, kp.head, i);
        assert(is_stable(data, W[i]));
        assert(false);
        0
    } else {
        lemma_kp_first_stable(data, kp);
        //  i >= H: positions before H are non-stable, but W[i] is stable
        if i < H {
            assert(0 <= i < H);
            assert(!is_stable(data, W[i]));
            assert(is_stable(data, W[i]));
            assert(false);
        }
        assert(i >= H);
        if i == H {
            lemma_kp_pinch_case_a(data, kp, i, j);
            0
        } else {
            assert(i > H);
            let rest = KPWord { head: kp.tail.first().1, tail: kp.tail.drop_first() };
            lemma_kp_pinch_transfer_tail(data, kp, i, j);
            assert(kp_syllables_valid(data, rest)) by {
                let ng = data.base.num_generators;
                assert(kp.tail[0] == kp.tail.first());
                assert(word_valid(rest.head, ng));
                assert forall|t: int| 0 <= t < rest.tail.len()
                    implies word_valid(#[trigger] rest.tail[t].1, ng) by {
                    assert(rest.tail[t] == kp.tail[t + 1]);
                }
            }
            assert(rest.tail.len() < kp.tail.len());
            let mp = lemma_kp_raw_pinch_gives_kp_pinch(data, rest, i - (H + 1), j - (H + 1));
            lemma_kp_pinch_lift(data, kp, mp);
            mp + 1
        }
    }
}

//  3c (the headline):  a KP-pinch-free KP-word with base-word syllables has a RAW-pinch-free value —
//  exactly what britton_lemma_full needs (the design's flagged "no KP-pinch ⟹ no raw-pinch").
pub proof fn lemma_kp_no_raw_pinch(data: HNNData, kp: KPWord)
    requires
        kp_syllables_valid(data, kp),
        kp_pinch_free(data, kp),
    ensures
        !has_pinch(data, kp_value(stable_letter(data), kp)),
{
    let st = stable_letter(data);
    let W = kp_value(st, kp);
    if has_pinch(data, W) {
        let ij = choose|i: int, j: int| has_pinch_at(data, W, i, j);
        assert(has_pinch_at(data, W, ij.0, ij.1));
        let m = lemma_kp_raw_pinch_gives_kp_pinch(data, kp, ij.0, ij.1);
        assert(kp_has_pinch_at(data, kp, m));
        assert(!kp_has_pinch_at(data, kp, m));   //  from kp_pinch_free
        assert(false);
    }
}

//  ============================================================
//  Junction — appending a stable-free word preserves raw-pinch-freeness.
//  ============================================================
//  For the Britton assembly we need `W·g⁻¹` raw-pinch-free, where W = kp_value(t, kp) is raw-pinch-free
//  (3c) and g⁻¹ is stable-free (g is a base/H word).  Appending a p-free word adds no stable letters,
//  so any raw pinch's two stable letters live in W and its middle is unchanged — hence it is a raw
//  pinch of W, contradicting raw-pinch-freeness.

//  Subrange of a concatenation lying entirely in the LEFT part is just that part's subrange.
pub proof fn lemma_word_subrange_concat_left(w1: Word, w2: Word, a: int, b: int)
    requires
        0 <= a,
        a <= b,
        b <= w1.len(),
    ensures
        (w1 + w2).subrange(a, b) =~= w1.subrange(a, b),
{
    let lhs = (w1 + w2).subrange(a, b);
    let rhs = w1.subrange(a, b);
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
        assert(lhs[k] == (w1 + w2)[a + k]);
        assert(a + k < w1.len());               //  a + k < b <= w1.len()
        assert((w1 + w2)[a + k] == w1[a + k]);
        assert(rhs[k] == w1[a + k]);
    }
}

//  Junction:  W raw-pinch-free ∧ u stable-free ⟹ W·u raw-pinch-free.
pub proof fn lemma_kp_junction(data: HNNData, w: Word, u: Word)
    requires
        !has_pinch(data, w),
        !has_stable_letter(data, u),
    ensures
        !has_pinch(data, w + u),
{
    if has_pinch(data, w + u) {
        let ij = choose|i: int, j: int| has_pinch_at(data, w + u, i, j);
        let i = ij.0;
        let j = ij.1;
        assert(has_pinch_at(data, w + u, i, j));
        let wu = w + u;
        assert(is_stable(data, wu[i]) && is_stable(data, wu[j]) && wu[i] != wu[j] && 0 <= i < j < wu.len());
        //  both stable letters lie in w (u contributes none)
        assert(i < w.len()) by {
            if i >= w.len() {
                assert(0 <= i - w.len() < u.len());
                assert(wu[i] == u[i - w.len() as int]);
                assert(!is_stable(data, u[i - w.len() as int]));   //  from !has_stable_letter(u)
                assert(false);
            }
        }
        assert(j < w.len()) by {
            if j >= w.len() {
                assert(0 <= j - w.len() < u.len());
                assert(wu[j] == u[j - w.len() as int]);
                assert(!is_stable(data, u[j - w.len() as int]));
                assert(false);
            }
        }
        //  the middle (and the "no stable between") lie entirely within w
        lemma_word_subrange_concat_left(w, u, i + 1, j);
        assert(wu.subrange(i + 1, j) =~= w.subrange(i + 1, j));
        assert(w[i] == wu[i] && w[j] == wu[j]);                 //  i, j < w.len()
        //  the pinch transfers to w (same symbols, same middle, same inline gen-lists)
        assert(has_pinch_at(data, w, i, j)) by {
            assert(0 <= i < j < w.len());
            assert(is_stable(data, w[i]) && is_stable(data, w[j]) && w[i] != w[j]);
            assert forall|k: int| i < k < j implies !is_stable(data, #[trigger] w[k]) by {
                assert(w[k] == wu[k]);                          //  k < j < w.len()
            }
            assert(w.subrange(i + 1, j) == wu.subrange(i + 1, j));
        }
        assert(has_pinch(data, w));
        assert(false);
    }
}

} //  verus!
