// thue.rs — the Thue-rewriting congruence + the positivity spec (Law P), Phase 0.
//
// docs/zfc-group-2-plan.md Part II Phase 0.  Makes "positivity" (Law P / the M-ladder
// theorem shape) a machine-checkable statement, and proves the EASY bridge
// (Thue-rewriting ⟹ group equality) — a Thue rule l→r is the relator l·r⁻¹, and a
// subword replacement is a group-congruence step.  The HARD direction (group ⟹ Thue on
// positive words) is per-machine work (the M-ladder); this module states it and gives the
// spec both sides compile against.  Reuses Word/Presentation/free-reduction wholesale.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;

verus! {

// A Thue rule l → r (used two-way as the string-rewriting relation l ↔ r).
pub struct ThueRule { pub lhs: Word, pub rhs: Word }

// The group relator of a rule:  l·r⁻¹  (so l ≡ r in the presentation).
pub open spec fn thue_relator(r: ThueRule) -> Word { concat(r.lhs, inverse_word(r.rhs)) }

// The presentation ⟨ n gens | { l·r⁻¹ : rules } ⟩ whose word problem the Thue system tracks.
pub open spec fn rules_pres(rules: Seq<ThueRule>, n: nat) -> Presentation {
    Presentation {
        num_generators: n,
        relators: Seq::new(rules.len(), |i: int| thue_relator(rules[i])),
    }
}

// A positive word: only Gen letters (no formal inverses) — the code words of a machine.
pub open spec fn positive_word(w: Word) -> bool {
    forall|i: int| 0 <= i < w.len() ==> exists|j: nat| #[trigger] w[i] == Symbol::Gen(j)
}

// ── the core algebraic lemma: a rule's two sides are group-equal ──
// (relator l·r⁻¹ ≡ ε  ⟹  l ≡ r, by right-multiplying by r and cancelling r⁻¹·r.)
pub proof fn lemma_rule_sides_equiv(rules: Seq<ThueRule>, n: nat, r: int)
    requires
        0 <= r < rules.len(),
        presentation_valid(rules_pres(rules, n)),
        word_valid(rules[r].lhs, n),
        word_valid(rules[r].rhs, n),
    ensures
        equiv_in_presentation(rules_pres(rules, n), rules[r].lhs, rules[r].rhs),
{
    let p = rules_pres(rules, n);
    let lhs = rules[r].lhs;
    let rhs = rules[r].rhs;
    let rel = thue_relator(rules[r]);
    assert(p.relators[r] =~= rel);
    lemma_relator_is_identity(p, r);                    // rel ≡ ε
    // rel·rhs ≡ ε·rhs =~= rhs
    lemma_equiv_concat_left(p, rel, empty_word(), rhs); // rel ≡ ε ⟹ rel·rhs ≡ ε·rhs
    assert(concat(empty_word(), rhs) =~= rhs);
    // rel·rhs = lhs·(rhs⁻¹·rhs)
    assert(concat(rel, rhs) =~= concat(lhs, concat(inverse_word(rhs), rhs)));
    lemma_word_inverse_left(p, rhs);                    // rhs⁻¹·rhs ≡ ε
    lemma_equiv_concat_right(p, lhs, concat(inverse_word(rhs), rhs), empty_word());
    assert(concat(lhs, empty_word()) =~= lhs);
    // now: concat(rel,rhs) ≡ rhs  and  concat(rel,rhs) ≡ lhs  ⟹  lhs ≡ rhs
    lemma_inverse_word_valid(rhs, n);
    assert(word_valid(concat(rel, rhs), n));
    lemma_equiv_symmetric(p, concat(rel, rhs), lhs);
    lemma_equiv_transitive(p, lhs, concat(rel, rhs), rhs);
}


// ── the Thue rewriting relation (either orientation) and its transitive closure ──
pub open spec fn thue_step_at(rule: ThueRule, u: Word, v: Word, pos: int, fwd: bool) -> bool {
    let l = if fwd { rule.lhs } else { rule.rhs };
    let rr = if fwd { rule.rhs } else { rule.lhs };
    &&& 0 <= pos && pos + l.len() <= u.len()
    &&& u.subrange(pos, pos + l.len() as int) == l
    &&& v == u.subrange(0, pos) + rr + u.subrange(pos + l.len() as int, u.len() as int)
}

pub open spec fn thue_step(rules: Seq<ThueRule>, u: Word, v: Word) -> bool {
    exists|r: int, pos: int, fwd: bool|
        0 <= r < rules.len() && thue_step_at(rules[r], u, v, pos, fwd)
}

pub open spec fn thue_chain(rules: Seq<ThueRule>, ws: Seq<Word>) -> bool
    decreases ws.len()
{
    ws.len() <= 1 || (thue_step(rules, ws[0], ws[1]) && thue_chain(rules, ws.drop_first()))
}

pub open spec fn thue_equiv(rules: Seq<ThueRule>, u: Word, v: Word) -> bool {
    exists|ws: Seq<Word>|
        ws.len() >= 1 && ws.first() == u && ws.last() == v && thue_chain(rules, ws)
}

// ── LAW P: positivity — the group trace on positive words equals Thue rewriting. ──
// The M-ladder theorem shape. ⟸ is `lemma_thue_implies_group` (this module);
// ⟹ is the per-machine positivity work (m0_token is the base case: G_T ≅ free).
pub open spec fn positivity(rules: Seq<ThueRule>, n: nat) -> bool {
    forall|u: Word, v: Word|
        #![trigger equiv_in_presentation(rules_pres(rules, n), u, v)]
        positive_word(u) && positive_word(v) && word_valid(u, n) && word_valid(v, n)
        ==> (equiv_in_presentation(rules_pres(rules, n), u, v) <==> thue_equiv(rules, u, v))
}

// ── validity is preserved by a Thue step (so intermediate words stay valid) ──
pub proof fn lemma_thue_step_valid(rules: Seq<ThueRule>, n: nat, u: Word, v: Word)
    requires
        thue_step(rules, u, v),
        word_valid(u, n),
        forall|r: int| 0 <= r < rules.len() ==>
            word_valid(#[trigger] rules[r].lhs, n) && word_valid(rules[r].rhs, n),
    ensures word_valid(v, n)
{
    let (r, pos, fwd) = choose|r: int, pos: int, fwd: bool|
        0 <= r < rules.len() && thue_step_at(rules[r], u, v, pos, fwd);
    let l = if fwd { rules[r].lhs } else { rules[r].rhs };
    let rr = if fwd { rules[r].rhs } else { rules[r].lhs };
    let pre = u.subrange(0, pos);
    let suf = u.subrange(pos + l.len() as int, u.len() as int);
    assert(v =~= concat(concat(pre, rr), suf));
    assert(word_valid(rr, n));
    assert forall|i: int| 0 <= i < v.len() implies symbol_valid(#[trigger] v[i], n) by {
        if i < pre.len() { assert(v[i] == u[i]); }
        else if i < pre.len() + rr.len() { assert(v[i] == rr[i - pre.len()]); }
        else { assert(v[i] == u[i - rr.len() + l.len()]); }
    }
}

// ── one Thue step is a group equality (the per-step bridge) ──
pub proof fn lemma_thue_step_equiv(rules: Seq<ThueRule>, n: nat, u: Word, v: Word)
    requires
        thue_step(rules, u, v),
        presentation_valid(rules_pres(rules, n)),
        forall|r: int| 0 <= r < rules.len() ==>
            word_valid(#[trigger] rules[r].lhs, n) && word_valid(rules[r].rhs, n),
        word_valid(u, n),
    ensures equiv_in_presentation(rules_pres(rules, n), u, v)
{
    let p = rules_pres(rules, n);
    let (r, pos, fwd) = choose|r: int, pos: int, fwd: bool|
        0 <= r < rules.len() && thue_step_at(rules[r], u, v, pos, fwd);
    let l = if fwd { rules[r].lhs } else { rules[r].rhs };
    let rr = if fwd { rules[r].rhs } else { rules[r].lhs };
    lemma_rule_sides_equiv(rules, n, r);                 // lhs ≡ rhs
    if !fwd { lemma_equiv_symmetric(p, rules[r].lhs, rules[r].rhs); }
    // now l ≡ rr in either orientation
    let pre = u.subrange(0, pos);
    let suf = u.subrange(pos + l.len() as int, u.len() as int);
    assert(u =~= concat(concat(pre, l), suf));
    assert(v =~= concat(concat(pre, rr), suf));
    lemma_equiv_refl(p, pre);
    lemma_equiv_refl(p, suf);
    lemma_equiv_concat(p, pre, pre, l, rr);              // pre·l ≡ pre·rr
    lemma_equiv_concat(p, concat(pre, l), concat(pre, rr), suf, suf);
}

// ── a Thue chain is a group equality (induction) ──
pub proof fn lemma_thue_chain_equiv(rules: Seq<ThueRule>, n: nat, ws: Seq<Word>)
    requires
        ws.len() >= 1,
        thue_chain(rules, ws),
        presentation_valid(rules_pres(rules, n)),
        forall|r: int| 0 <= r < rules.len() ==>
            word_valid(#[trigger] rules[r].lhs, n) && word_valid(rules[r].rhs, n),
        word_valid(ws[0], n),
    ensures equiv_in_presentation(rules_pres(rules, n), ws.first(), ws.last())
    decreases ws.len()
{
    let p = rules_pres(rules, n);
    if ws.len() == 1 {
        assert(ws.first() =~= ws.last());
        lemma_equiv_refl(p, ws.first());
    } else {
        assert(thue_step(rules, ws[0], ws[1]));
        lemma_thue_step_equiv(rules, n, ws[0], ws[1]);
        lemma_thue_step_valid(rules, n, ws[0], ws[1]);
        let tail = ws.drop_first();
        assert(tail[0] == ws[1]);
        assert(thue_chain(rules, tail));
        lemma_thue_chain_equiv(rules, n, tail);
        assert(tail.first() == ws[1] && tail.last() == ws.last());
        lemma_equiv_transitive(p, ws.first(), ws[1], ws.last());
    }
}

// ── THE BRIDGE: Thue-rewriting ⟹ group equality (easy direction of positivity) ──
pub proof fn lemma_thue_implies_group(rules: Seq<ThueRule>, n: nat, u: Word, v: Word)
    requires
        thue_equiv(rules, u, v),
        presentation_valid(rules_pres(rules, n)),
        forall|r: int| 0 <= r < rules.len() ==>
            word_valid(#[trigger] rules[r].lhs, n) && word_valid(rules[r].rhs, n),
        word_valid(u, n),
    ensures equiv_in_presentation(rules_pres(rules, n), u, v)
{
    let ws = choose|ws: Seq<Word>|
        ws.len() >= 1 && ws.first() == u && ws.last() == v && thue_chain(rules, ws);
    assert(ws[0] == u);
    lemma_thue_chain_equiv(rules, n, ws);
}

} // verus!