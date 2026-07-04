# Response to the M0-closure findings

*2026-07-04. Minimal handback: what I did with your `m0-closure.md`, the results of the two §7
runs you flagged mandatory, and my answer to your closing question. Full detail: `docs/m0-closure.md`
§9; the checker is `tools/m0_check.py`.*

---

## What I did

- Saved your doc as `docs/m0-closure.md`.
- Built `tools/m0_check.py` and **ran both §7 checks** (you marked them mandatory, and half-expected
  a scar-table correction — so this was the highest-value move).
- Appended the real results as §9; cross-referenced into the P′ doc and memory.

## The two runs — both CLEAN, and the streak broke

**§7(a) KB critical-pair pass: CLEAN.** 35 critical pairs (overlaps + containments) over the nine
oriented rules, **0 non-joinable**, every overlap word has a unique normal form. `R̂` is confluent;
KB adds **zero rules**. Your §3 headline holds mechanically: **the fifth rule does not exist.**

**§7(b) injectivity fuzz: CLEAN at scale.** All `R̂`-irreducible positive words up to length 9:
**9,447,857 words → 9,447,857 distinct `ψ`-images → 0 collisions.** The scar lemma / readback
argument (your flagged residual-risk proof) survived ~9.4M witnesses untouched. Spot checks:
`ψ(⟩⟨M1) = ε` (bicyclic finding, now a one-line free-group fact — the invariant retires as you
said) and `ψ(X0) = ψ(M1) = (M,1)` (the `r1` collision).

**The honest headline:** you half-expected the fuzz to hand back a correction in the scar table's
fine print. **It didn't** — first fuzz this week that left the human's hand-trace intact. Worth
stating plainly because the streak (S9, deposit-order, flip-pairing, the length-filter) had made
"the tool corrects the human" feel like a law; this is the counterexample. Caveat in both
directions: 9.4M-to-length-9 is strong *evidence*, not a proof — the marker-count induction is
still the eventual ground truth — but there is no fine-print bug at this depth.

## What I agree is now settled vs. still open

- **Settled (paper + heavy corroboration):** `G_T ≅ F(Σ∖{⟩,0})` (the second Tietze elimination is
  clean and dissolves the marker–relator overlap — I think this is the real insight of your doc,
  and it's unarguable); `R̂` convergent; M0 = `Thue(T̂)` at paper-strength.
- **Still open (unchanged):** the *formal* `proof fn` for injectivity (marker-count induction), and
  M0's place inside Lemma 2 proper (the join with `Thue(R)`). The freeness makes the base a
  concrete `F(Σ∖{⟩,0})` + `ψ`, so junction decoupling instantiates rather than parameterizes —
  that's a real simplification for the formal campaign.

## Answer to your closing question

You asked: draft `thue.rs` against `positivity_mod` now, or run §7 first?

**§7 is now run (clean), so the blocker you were hedging against is gone — draft `thue.rs` next.**
My reasoning: the one thing that could have forced a base-layer redesign was a scar-table
correction, and 9.4M words say there isn't one at reachable depth. The base is pinned concrete
(`F(Σ∖{⟩,0})`, `ψ`), termination is a lex measure, local confluence is a finite case split the KB
pass already enumerated (35 pairs) — all three are Verus-friendly exactly as your §5 says. So
`thue.rs` can bake in the §5 shape without waiting. I'd sequence it: `thue.rs` core defs +
`positivity_mod` + the bridge lemma first (Phase 0), then the M0 module (`m0.rs`: the nine rules,
the lex-termination `decreases`, the 35-pair local-confluence `proof fn`, and the marker-count
injectivity lemma with the scar table as the case skeleton) as the first *content* module — it's
self-contained, needs no Miller machinery, and its checker already exists in Python to cross-oracle
against.

One meta-note to close the loop on your meta-note: the tool didn't out-score the human this time,
but it did something better — it turned a "half-expect a correction" into a 9.4M-witness *licence
to proceed*. That's the other thing the auditor is for.
