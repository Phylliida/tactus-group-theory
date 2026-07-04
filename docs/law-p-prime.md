# law-p-prime.md — Law P′, the M0 rung, and the NF-3/NF-2b bricks

*2026-07-04, continuation session (Danielle + Fable). Status: paper-math + tool specs, with a
mechanical run appended (§11). The P′ investigation found (i) a DERIVED data-only token the
whitelist must carry, with its own witness, and (ii) a proof that the naive extended-Thue
statement is FALSE — rotations are load-bearing. NF-3 is proven; NF-2b's valuation is pinned to
signature level.*

---

## 1. Why plain positivity is false for the Boolean machine (the precise failure)

Every rule of `R` carries exactly one state per side (the M8-avoidance convention). Hence
**state-free positive words are Thue(R)-inert** — no rule window can match. But A.7's collapsed
token gives `⟨M1⟩ = ε` in `G` as a derived group consequence. So `u = ⟨M1⟩` and `v = ε` are
group-equal and Thue-disconnected: the V.3 spec `positivity(rules, n)` is **unprovable as
drafted** for any system with a whitelist. The M-ladder rungs are unaffected (no data-only
survivors in M1–M7; plain positivity = `positivity_mod` with empty token list), so Phase 0/1
proceed unchanged; only `theorem_boolean_logic_group`'s target statement changes.

## 2. Law P′ (two-layer positivity)

Let `T` = the declared whitelist tokens (data-only words trivial in `G`, each witnessed), and
`≈_T` = the positive trace of `ncl(T)` in `F(data)`.

> **Law P′.** For positive `u, v`: `u = v` in `G` ⟺ `u ~ v` under `Thue(R) ∨ ≈_T`
> (the join of the machine congruence and the token congruence).
>
> **M0 rung (the finiteness half).** `≈_T` is itself a finitely generated Thue congruence, by
> an explicit finite token system `T̂` ⊇ T.

Splitting it this way keeps the M-ladder's Lemma-2 architecture intact and isolates the new
content in M0 — which sits *below* M1 on the ladder: it is the unique data-only rung.

## 3. Computing `T̂`: the token subsystem, eliminated

Tokens so far: `⟨M1⟩ = ε`, `⟨X0⟩ = ε`. Tietze-eliminate `⟩ = 1⁻¹M⁻¹⟨⁻¹` from the first; the
second becomes `⟨X0·1⁻¹M⁻¹⟨⁻¹`, cyclically reducing to the **derived positive pair**

> `M1 = X0`.

Is it sound? It had better be — and it is, delightfully: `M1 ↔ X0` is the collapsed window of
the tail-sharing schema **`1∧u ↔ 0⊕u`** (both `≡ u`). Witness: `f(0⊕u)·f(1∧u)⁻¹` freely
reduces to the `H₀⟨`-conjugate of `X0·(M1)⁻¹`, literally an element of `Sem`. **The group
derived a true schema nobody wrote down.** This is §2.1's cancellation-collapse running in
reverse gear — consequences of honest tokens are honest tokens, but the whitelist must be
**consequence-closed**, and every derived entry owes its own witness. (Here the witness
exists; if some derived token ever lacks one, the design dies at that point — same protocol
as A.7.)

Note the base-group consequence: after eliminating `⟩`, the data-only quotient
`G_T = F(Σ)/ncl(T)` is the **one-relator group `⟨Σ∖{⟩} | M1 = X0⟩`** — Adjan cycle-free (left
graph edge `M–X`, right graph edge `1–0`, acyclic), so Adjan/Remmers applies to the base. No
cascade, no collapse: the Boolean-collapse disaster does not recur, because the token relator
is affix-disjoint (`M`≠`X`, `1`≠`0`).

## 4. The rotation-necessity finding (naive `T̂` is refuted, mechanically)

First guess: `T̂ = {⟨M1⟩ ↔ ε, ⟨X0⟩ ↔ ε, M1 ↔ X0}`. **This is false**, and the refutation is
a pleasingly machine-flavored invariant:

Every rotation of a trivial token is trivial (conjugates stay in `ncl`), so e.g.
`⟩⟨M1 = ε` in `G_T` (check: `⟩ ↦ 1⁻¹M⁻¹⟨⁻¹`, then `1⁻¹M⁻¹⟨⁻¹·⟨M1 = ε` ✓). But send
`⟨ ↦ p`, `⟩ ↦ q`, all other letters `↦ 1` into the **bicyclic monoid** `⟨p,q | pq = 1⟩`:
every rule of the naive `T̂` maps to `1 = 1`, so the bicyclic image is a Thue invariant — and
`⟩⟨M1 ↦ qp ≠ 1`. Hence `⟩⟨M1 ≁ ε` under naive `T̂` while `⟩⟨M1 = ε` in `G`: an **emergent
ambiguity, caught before it could bite the formal campaign.**

> **Rotation-closure law.** Whitelist tokens are CYCLIC words, not words: `T̂` must contain
> every cyclic rotation of every `ε`-token as an explicit Thue rule. (The auditor's `cyckey`
> matching was already rotation-invariant — prescient on the recognition side; the *derivation*
> side needs the rotations as rules.)

So the corrected candidate:
`T̂ = { all 4 rotations of ⟨M1⟩ ↔ ε, all 4 rotations of ⟨X0⟩ ↔ ε, M1 ↔ X0 }`.

**M0 positivity conjecture.** `≈_T = Thue(T̂)`. Proof plan (one session, existing mechanisms
only): eliminate `⟩`; positive words map to marker words (`⟩` emits the unforgeable negative
triple `1⁻¹M⁻¹⟨⁻¹` — M6-style) over the **Adjan base** `⟨… | M1 = X0⟩` (Adjan/Remmers gives
the base's positive normal forms — M5(c)'s tool, promoted from monster-taming to
infrastructure). Parse ambiguities to enumerate: full marker cancellation = token deletion;
the four partial-cancellation phases = the four rotations; base-relator application =
`M1 ↔ X0`. If every ambiguity is one `T̂`-rule — the parser-principle checklist — M0 closes.
One honest flag: the marker triple's *interior* letters (`1⁻¹M⁻¹`) can interact with the base
relator (`M1 = X0` touches the same letters); the enumeration must cover marker–relator
overlaps. This is the one spot where M0 could demand a fifth rotation-like rule; the bicyclic
trick above is the model for hunting it.

**Cost acknowledged:** P′ upgrades Lemma 2's base layer from "free group normal forms" to
"free-mod-tokens normal forms" at every junction. Since the token quotient is a Tietze
elimination plus one Adjan relation, this is bookkeeping, not architecture — but it is
*global* bookkeeping, and the junction-decoupling formalization should take the base as a
parameter now rather than retrofit it later.

## 5. Endpoint lemma (canonicity survives the tokens)

**Lemma.** Canonical codes are `T̂`-irreducible. *Proof sketch:* canonical ANF has constants
only as whole codes (`0`, `1`), so `M1` and `X0` never occur (monomials contain no constants);
`⟩⟨` occurs only at monomial boundaries, always followed by `X` and never by `M1`/`X0`-material,
so no rotated token occurs either. Hence token rules can neither fire on nor manufacture
identifications between canonical codes: soundness at endpoints is carried entirely by Lemma 2,
exactly as the witness-liberation lemma already arranged for intermediate configurations. ∎
(Transcribe the substring check into the fuzzer: assert no canonical code contains any `T̂`-window.)

## 6. The revised formal target (Phase 0 delta)

```rust
pub open spec fn tokens_derivable(rules: Seq<ThueRule>, toks: Seq<ThueRule>, n: nat) -> bool {
    forall|k: int| 0 <= k < toks.len() ==>
        equiv_in_presentation(rules_pres(rules, n),
                              #[trigger] toks[k].lhs, toks[k].rhs)   // whitelist = consequences
}
pub open spec fn positivity_mod(rules: Seq<ThueRule>, toks: Seq<ThueRule>, n: nat) -> bool {
    forall|u: Word, v: Word| positive_word(u) && positive_word(v)
        && word_valid(u, n) && word_valid(v, n)
        ==> (equiv_in_presentation(rules_pres(rules, n), u, v)
             <==> thue_equiv(rules + toks, u, v))
}
```

`tokens_derivable` makes the ⟸ direction trivial (a token step is a group equality by
hypothesis), so the theorem content is ⟹, as always. Plain `positivity` = `positivity_mod`
with the empty token list; every M-ladder module compiles against either. `thue.rs` can now be
written without a wall waiting in Phase 3.

## 7. Auditor upgrade: the token-interaction probe

The whitelist protocol gains a closure obligation. Seed implementation (now RUN — see §11):
cancel every pair of tokens at every cyclic alignment; each novel data-only survivor is a
REQUIRED whitelist entry (owes a witness) or a design-killer. Also: every token containing
bracket letters must ship its rotations as Thue rules (rotation-closure law).

---

## 8. NF-3, proven (the escape combinatorics)

**Lemma (weight bound).** For a finite pair-list `E`, define
`w(E) = Σ_{C ∈ classes(E), |C| ≥ 2} (|C| − 1)`. Then `w(E) ≤ |E|`.

*Proof.* Induction on `|E|`. Empty: closure is equality, `w = 0`. Adding one pair either
leaves the partition unchanged (`+0`) or merges two classes `C_x, C_y`; in all three shapes —
singleton+singleton (`+1`), singleton+class (`(|C|−1) → |C|`, `+1`), class+class
(`(|C_x|−1)+(|C_y|−1) → |C_x|+|C_y|−1`, `+1`) — the weight grows by at most 1. ∎

**Corollary (class bound).** Every class of `closure(E)` has size `≤ |E| + 1`.

**Corollary (escape).** If `~` has an infinite class `{e₀, e₁, …}` (pairwise distinct), then
for every finite stage `m` with `k` declared pairs: the elements `e₀, …, e_{k+1}` cannot all be
pairwise `closure(stage-m)`-related (class bound), so **some pair `(eᵢ, eⱼ)` is `~`-related but
escapes the stage-`m` closure** — and is `P_∞`-identified (the chain through the declared pairs
exists at high enough stage). ∎

**Verus shape (the brick's design choice):** don't formalize partitions — use **contraction
induction**, which matches the substrate's idioms: to show `k+2` distinct pairwise-related
elements contradict `k` pairs, contract the last pair `(a,b)` via `ρ = (b ↦ a, else id)`;
chains descend to the contracted `(k−1)`-pair list, and `ρ` merges at most two of the `k+2`
values, leaving `≥ k+1` distinct pairwise-related elements — IH. Base `k = 0`: closure is
equality vs distinctness. Spec skeleton:

```rust
pub open spec fn pair_related(ps: Seq<(nat, nat)>, x: nat, y: nat) -> bool
pub open spec fn in_closure(ps: Seq<(nat, nat)>, x: nat, y: nat) -> bool  // ∃ chain
pub proof fn lemma_closure_class_bound(ps: Seq<(nat, nat)>, xs: Seq<nat>)
    requires distinct_seq(xs), xs.len() >= ps.len() + 2,
        forall|i, j| 0 <= i < j < xs.len() ==> in_closure(ps, xs[i], xs[j]),
    ensures false,
```

This brick is fully self-contained (no Miller machinery) — the ideal warm-up before 2b.

## 9. NF-2b, pinned (the valuation, exactly)

The gating brick, now at signature level. `c0_slice(m)` presents `⟨gᵢ | g_α g_β⁻¹ : (α,β)
declared at stage ≤ m⟩`. Backward direction via the **representative collapse**:

- `spec fn rep(ps, i) -> nat` — least `j` with `in_closure(ps, i, j)` (well-defined; `rep` is
  constant on closure classes, and `rep(i) = rep(j) ⟹ in_closure(ps, i, j)` by transitivity
  through the shared representative).
- `spec fn collapse_word(ps, w) -> Word` — letterwise `gᵢ ↦ g_{rep(i)}`, sign-preserving.
- **Key lemma:** every relator collapses to a word that freely reduces to `ε` (same
  representative on both letters), so `collapse` transports `c0_slice`-equivalence to
  **free-group** equivalence — the exact shape of `lemma_hom_pred_preserves_equiv`, target
  group free.
- **Headline:** `g_α g_β⁻¹` trivial in `c0_slice(m)` ⟹ `collapse` image trivial in the free
  group ⟹ `g_{rep(α)} g_{rep(β)}⁻¹` reduces to `ε` ⟹ `rep(α) = rep(β)` ⟹
  `in_closure(pairs(m), α, β)`. ∎

Chain NF-3 + NF-2b through the banked descent (extract → lift → `collapse_injective` →
faithfulness → `c0_slice`) and `limit_escapes_every_slice` is discharged — NF-A goes
unconditional, and the first machine-verified non-finite-presentability theorem for an explicit
f.g. group is done except for NF-6/NF-7's assembly.

---

## 10. Session ledger

| Item | Status |
|---|---|
| Plain positivity for the Boolean machine | REFUTED precisely (state-free inertia vs `⟨M1⟩ = ε`) |
| Law P′ | stated, two-layer; spec delta written |
| Derived token `M1 = X0` | found by hand-elimination; witnessed (`1∧u ↔ 0⊕u`); soundness ✓ |
| Naive `T̂` | REFUTED (bicyclic invariant; rotations necessary) → rotation-closure law |
| M0 rung | posed, proof plan = markers over Adjan base; one flagged overlap case |
| Endpoint lemma | proved at sketch strength (canonical codes token-irreducible) |
| Auditor | token-interaction probe specced + seeded; RUN in §11 |
| NF-3 | PROVEN (weight induction); contraction-induction Verus shape chosen |
| NF-2b | valuation pinned to signature level; mirrors banked hom-transport |

---

## 11. MECHANICAL RUN (2026-07-04, this session — the tool corrected the hand-trace)

Ran the probe + bicyclic check in `tools/semantic_audit.py` on the two-token whitelist
`{⟨M1⟩, ⟨X0⟩}`. Two corrections and one strengthening:

**(a) The bicyclic refutation is CONFIRMED.** Image of `ε` = `(0,0)`; image of `⟩⟨M1` = `(1,1)`
(= `qp` in bicyclic normal form). Nonidentity ⟹ `⟩⟨M1 ≁ ε` under naive `T̂` while `= ε` in `G`.
The rotation-closure law stands, mechanically.

**(b) The FIRST probe (length filter) was WRONG — it found nothing.** `M1 = X0` is a length-4
relator, NOT strictly shorter than the length-4 parents, so `len(cc) < min(len parents)` filtered
out exactly the signal. Fixed: the correct filter is **genuine two-sided positive pair** (`P = N`,
both `P, N` nonempty) — a cancellation product of two positive tokens is always `P·N⁻¹` by
construction, and the readable derived token is that pair, regardless of length. (Lesson for the
formal auditor: derived tokens are recognized by SHAPE, not length.)

**(c) The corrected probe REPRODUCES `M1 = X0` and STRENGTHENS §3+§4 into one output.** It
returns 26 derived positive-pair tokens, which are generated by exactly:
- `⟨M1⟩ = M1⟩⟨ = 1⟩⟨M = ⟩⟨M1` — the four rotations of `⟨M1⟩`, identified as positive words;
- `⟨X0⟩ = X0⟩⟨ = 0⟩⟨X = ⟩⟨X0` — the four rotations of `⟨X0⟩`;
- **`M1 = X0`** — the derived token from §3;
- (all cross-terms follow from those + `M1 = X0`).

So the probe **mechanically rediscovered the rotation-closure law** (the 8 rotation-identities)
AND the derived token in one sweep — unifying §3's Tietze elimination and §4's bicyclic argument,
which were two separate hand-derivations. The minimal `T̂` generating set is therefore
confirmed: **{4 rotations of `⟨M1⟩`, 4 rotations of `⟨X0⟩`, `M1 = X0`} + the ε-triviality of the
base tokens** — exactly §4's corrected candidate, now with the `M1 = X0` cross-link shown
necessary by the cross-terms.

**(d) Corpus regression: `ALL EXPECTATIONS MET` (32 systems unchanged).** The probe is additive.

Honest residue: this validates the token *algebra* (which relations hold) but NOT the M0
positivity conjecture (that `Thue(T̂)` reproduces the whole positive trace) — that still needs
the marker-over-Adjan-base proof of §4, including the flagged marker–relator overlap case. The
probe tells us what `T̂` must contain; it does not tell us `T̂` suffices.
