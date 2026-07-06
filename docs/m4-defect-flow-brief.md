# M4 — mixed transduction (defect flow): a self-contained brief for the planner

**Purpose of this doc.** We just finished formalizing **M3 (the blinker)** — a positivity theorem for a
small string-rewriting machine — in Verus/tactus (`src/m3_blinker.rs`, 124/0). **M4 is the next rung.**
This brief gives you (a) exactly what we are proving, (b) the group theory behind it, (c) the "defect
flow" proof technique from the design doc, (d) what infrastructure already exists to reuse, (e) a crash
course in the tactus proof assistant, and (f) a request to produce a brick-by-brick plan. You do **not**
need prior context beyond this doc.

At the end, **please produce a resumable, brick-by-brick plan** in the style described in §7 — we will
then execute it. Ask clarifying questions if any step is under-determined.

---

## 1. The one-paragraph picture

We study finite string-rewriting systems ("Thue systems") that model tiny machines, and their associated
**groups**. A rewrite rule like `qa = bq′` both is a Thue rewriting rule *and* a group relator. For a
machine to be a faithful "semantic basis," we need **positivity**: on *positive* words (no formal
inverses), two words are equal **in the group** iff they are connected by **Thue rewriting**. The `⟸`
(Thue ⟹ group) direction is trivial and already banked. The `⟹` direction (group-equal ⟹ Thue-equal) is
the real theorem, proved per-machine. M4 is the machine `{ qa = bq′, q′b = aq }`.

---

## 2. Exactly what we are proving

Alphabet: 4 generators, encoded as `Symbol::Gen(i)`:
`a = Gen(0)`, `b = Gen(1)`, `q = Gen(2)`, `q′ = Gen(3)`.

**M4 rules** (mirror `m3_rules()` in `src/m3_blinker.rs`):
```rust
pub open spec fn m4_rules() -> Seq<ThueRule> {
    seq![
        ThueRule { lhs: seq![Symbol::Gen(2), Symbol::Gen(0)], rhs: seq![Symbol::Gen(1), Symbol::Gen(3)] }, // qa = bq′
        ThueRule { lhs: seq![Symbol::Gen(3), Symbol::Gen(1)], rhs: seq![Symbol::Gen(0), Symbol::Gen(2)] }, // q′b = aq
    ]
}
```
(This is a right-moving transducer: in state `q` it rewrites `a→b`, in state `q′` it rewrites `b→a`. Both
rules move the state letter one position rightward. It is the smallest machine whose *cycle word is mixed*.)

**The goal theorem** (mirror `lemma_m3_positivity`):
```rust
pub proof fn lemma_m4_positivity()
    ensures positivity(m4_rules(), 4)
```
where `positivity` is already defined in `src/thue.rs`:
```rust
pub open spec fn positivity(rules: Seq<ThueRule>, n: nat) -> bool {
    forall|u: Word, v: Word|
        #![trigger equiv_in_presentation(rules_pres(rules, n), u, v)]
        positive_word(u) && positive_word(v) && word_valid(u, n) && word_valid(v, n)
        ==> (equiv_in_presentation(rules_pres(rules, n), u, v) <==> thue_equiv(rules, u, v))
}
```
Key spec fns (all in `thue.rs`): `Word = Seq<Symbol>`; `positive_word(w)` = every symbol is `Gen(_)`
(no `Inv(_)`); `word_valid(w, n)` = every symbol index `< n`; `thue_equiv` = connected by a chain of
single-rule rewrites (either direction, anywhere in the word); `rules_pres(rules, n)` = the group
presentation with `n` generators and one relator `lhs·rhs⁻¹` per rule; `equiv_in_presentation(p, u, v)` =
equal in the group `p`.

**Both directions**, exactly as M3:
- `⟸`  `thue_equiv ⟹ equiv_in_presentation`: **free**, via `lemma_thue_implies_group(rules, n, u, v)`
  (in `thue.rs`; needs rule-validity + `word_valid(u,n)` + `presentation_valid`). M3 wraps this as
  `lemma_m4_backward`-style; copy `lemma_m3_backward`.
- `⟹`  `equiv_in_presentation ⟹ thue_equiv`: **the real work** (§3–§4 below).

---

## 3. The group behind M4, and why M3's machinery mostly transfers

### 3.1 Tietze elimination → an HNN extension (SAME substitution as M3)

Rule 1 (`qa = bq′`) is **identical** in M3 and M4. It lets us eliminate `q′ = b⁻¹qa`. Substituting into
rule 2:

- M3 rule 2 `q′a = bq` becomes `qa² q⁻¹ = b²` — associated subgroups `⟨a²⟩ → ⟨b²⟩`.
- **M4 rule 2 `q′b = aq` becomes `q(ab)q⁻¹ = ba`** — associated subgroups `⟨ab⟩ → ⟨ba⟩`.

So:
> **`G_M4 ≅ ⟨ a, b, q | q(ab)q⁻¹ = ba ⟩`** — an **HNN extension of the free group `F(a,b)`**, stable
> letter `q`, associated subgroups `⟨ab⟩ → ⟨ba⟩` (the cycle word is now *mixed*, `ab` vs `ba`).

The **substitution homomorphism** `sub` (`q′ ↦ b⁻¹qa`, `a↦a, b↦b, q↦q`) is **byte-for-byte identical to
M3's `sub_hom()`**. Everything that connects the Thue presentation to the HNN presentation transfers.

### 3.2 What to reuse from M3 (mechanical copies / retargets)

`m4_data()` is `m3_data()` with the association tuple swapped:
```rust
pub open spec fn m4_data() -> crate::hnn::HNNData {
    crate::hnn::HNNData {
        base: crate::higman_operations::free_group(2),
        // M3 was: [ (b², a²) ] = [ (seq![Gen1,Gen1], seq![Gen0,Gen0]) ]
        associations: seq![ ( seq![Symbol::Gen(1), Symbol::Gen(0)],   // ba
                             seq![Symbol::Gen(0), Symbol::Gen(1)] ) ], // ab   (confirm tuple ORDER against hnn.rs)
    }
}
```
- `m4_rules_valid`, `m4_data_valid`, `m4_pres_valid`, `sub_hom` (unchanged), `lemma_sub_valid`,
  `lemma_m4_iso` (Tietze), `lemma_group_to_hnn`, `lemma_m4_backward`: **direct copies of the M3 versions**
  with `m3_→m4_`. The *proof of the iso* changes only in the second relator's word; re-verify.
- **R1 — `hnn_associations_isomorphic(m4_data())`:** M3 discharged this with the automorphism
  `swap: a↦b, b↦a` of `F(a,b)`, because `swap(a²)=b²`. For M4 we need an automorphism carrying the
  associated subgroup structure `⟨ab⟩ → ⟨ba⟩`. **The same swap `a↔b` works:** `swap(ab)=ba`. So R1 is a
  near-verbatim reuse of M3's `swap_hom()` machinery. (Confirm the exact `hnn_associations_isomorphic`
  obligation and that swap maps the association columns correctly.)
- The **generic HNN / Britton / normal-form engine is HNNData-polymorphic** and already banked — it
  works for `m4_data()` unchanged. See §5 for the reusable lemmas.

### 3.3 Where M4 genuinely diverges: the READBACK

In M3 the readback was *clean*: for a Thue-normal-form word, each HNN "gap" (base word between stable
letters) had **`b_rcoset_rep(gap) = gap`** (the coset representative of a normal-form gap *is* the gap,
because leading-`a` runs were capped at length ≤ 1). That let us match syllables one-for-one.

**For M4 this local head-cap FAILS.** Because a data letter `a` may follow `q′`, syllable heads are
unbounded, and there is a genuine **local masquerade**: with defect `m = 1`, the `u`-side syllable `a`
(from `…q′q…`) maps under the mixed cycle exactly to the `v`-side syllable `b⁻¹` (from `…qq′…`), since
`(ab)⁻¹·a = b⁻¹`. The group *locally tries* to commute the resting head's phase `q′q ↔ qq′`. So per-gap
matching is not locally decidable — the compensations are only **globally** inconsistent. This is the
new phenomenon and the whole point of M4.

---

## 4. The proof technique: DEFECT FLOW (from `docs/semantic-finite-basis.md` §4.4)

Write a positive word in syllable form `u = w₀ s₁ w₁ ⋯ sₖ wₖ`, where `sᵢ ∈ {q, q′}` are the state
letters and `wᵢ ∈ {a,b}*` are the data blocks. Substituting `q′ ↦ b⁻¹qa` gives the HNN normal-form data
`sub(u) = g₀ q g₁ q ⋯ q gₖ` with base syllables `gᵢ`. Two positive words equal in `G_M4` have HNN normal
forms whose syllables are related by **compensations** carrying the mixed cycle word:
```
    hᵢ = (ab)^{ −mᵢ } · gᵢ · (ba)^{ mᵢ₊₁ }          (mᵢ ∈ ℤ are the "defects")
```
Positivity ⟺ **all `mᵢ = 0`** (then syllables are literally equal and we read states/data back as in M3).
The argument that forces `mᵢ = 0` is a **conservation-and-boundary-discharge** ("defect flow"):

**Local forcing** — the constrained syllable shapes (`gᵢ` is `P` or `P·b⁻¹` with `P` positive, plus the
state-dependent start constraint: no `a` after `q`, no `b` after `q′`) kill all but the masquerade:
1. `mᵢ < 0` is **impossible** (prepends positive `ab…`, forcing an `h`-syllable with `s′ᵢ = q′` whose data
   starts with `b` — forbidden by the "no `b` after `q′`" irreducibility).
2. `mᵢ ≥ 2` is **impossible** (≥ 3 uncancellable negative letters: after the single `a`-head cancels, the
   next junction pits `b⁻¹` against a non-`b`-starting `wᵢ`).
3. `mᵢ = 1` **forces the exact masquerade**: `gᵢ = a` (`sᵢ=q′, wᵢ=ε, sᵢ₊₁=q`), `hᵢ = b⁻¹`
   (`s′ᵢ=q, w′ᵢ=ε, s′ᵢ₊₁=q′`), and `mᵢ₊₁ = 0`.

**Propagation + boundary discharge** — a defect at junction `i` forces `mᵢ₊₂ = 1` with syllable `i+1`
empty on both sides (`u = ⋯q′qq′q⋯` vs `v = ⋯qq′qq′⋯`, pure alternating state runs). Any data letter in
the run yields an `a`-start-after-`q` on one side → contradiction. So **the defect flows strictly
rightward through state-only material and cannot stop.** At the right boundary `m_{k+1} = 0` (by
definition), the final equation `hₖ = (ab)^{−1} gₖ` demands a positive syllable equal to `b⁻¹wₖ` —
impossible. Hence all `mᵢ = 0`; tuples equal; states and data read back exactly as in M3. ∎

**Mental model:** the group's "cheat" is a conserved particle that must exit through the word boundary and
can't. (Corollary/warning, not needed for us: on *circular* words the defect could cycle forever —
conjugacy-positivity may fail where equality-positivity holds. Our target only needs equality on words.)

**Formalization challenge for the plan.** The M3 readback (`ffnf` → reduced `sub` → `rep = gap` →
`act_syls = gap_syls` → right-cancellation → prefix-code injectivity) provides the *scaffolding* (the HNN
normal form `act_syls`, the syllables `gᵢ`), but the **matching step is different**: instead of per-gap
equality, M4 needs the defect-flow induction (cases 1–3 + rightward propagation + boundary). The planner
must decide how to represent the defects `mᵢ` and the compensation equation in the `act_syls` framework,
and how to structure the propagation induction. This is the crux and the main design risk.

---

## 5. Available infrastructure (concrete pointers)

**Free `⟸` direction & Thue layer** (`src/thue.rs`): `positivity`, `thue_equiv`, `thue_step`,
`lemma_thue_implies_group`, `lemma_thue_refl/single/trans/symmetric/prepend`, `lemma_thue_step_valid`.

**Generic HNN / Britton engine** (HNNData-polymorphic — works for `m4_data()` as-is):
- `src/hnn.rs`: `HNNData`, `hnn_data_valid`, `hnn_presentation`, `hnn_associations_isomorphic`,
  `lemma_base_embeds_in_hnn`.
- `src/britton_via_tower.rs`: `britton_lemma_full` (w ≡ ε + has-stable ⟹ has-pinch),
  `britton_lemma_unconditional` (**base word ≡ ε in HNN ⟹ ≡ ε in the base free group** — the base
  embedding; this is how M3 got base-word faithfulness), `textbook_act_hnn` (the normal-form action),
  `lemma_act_base`, `lemma_act_compose`, net-level lemmas.
- `src/machine_group.rs`: `act_syls(data, w)` = `textbook_act_hnn(data, w, ε, []).1` (the syllable list —
  the HNN normal form), and `lemma_no_relator_equiv_implies_freely_equivalent`.
- `src/free_word_problem.rs`: `lemma_free_group_equiv_freely_equivalent` (free-group word problem).

**The M3 template** (`src/m3_blinker.rs`, 124 fns — copy/retarget the group-side, replace the readback):
- Group-side (near-verbatim for M4): `m3_rules/m3_data/sub_hom` and their `_valid`, `lemma_m3_iso`,
  `lemma_group_to_hnn`, `lemma_m3_backward`, `swap_hom` + R1, `lemma_sub_valid`,
  `lemma_apply_hom_word_valid` usage, `lemma_reduced_unique` (reduced base words equal-in-base ⟹ equal),
  `lemma_base_reduced_unique_hnn` (reduced base words equal-in-HNN ⟹ equal),
  `lemma_syls_preserved` (group-equal ⟹ same `act_syls`), `lemma_sub_injective` (sub is a prefix code).
- Readback that will need **redesign** for defect flow (do NOT expect verbatim reuse): `ffnf` +
  `lemma_u_thue_ffnf`, `rep=gap`/`nf_gap`/`gap_syls`/`gap_word`/`split_q`, `lemma_act_syls_split`,
  `lemma_m3_nf_readback`, `lemma_exists_nf` (`num_a` reduction — note: M4's Thue termination is by
  *state-letters-move-right*, **not** `#a`, since `q′b→aq` *adds* an `a`; the planner must pick M4's
  termination measure).

**Design doc:** `docs/semantic-finite-basis.md` §4.3 (M3, done) and **§4.4 (M4, the target — read it)**.
**M3 plan (structure to mirror):** `docs/m3-blinker-plan.md` — steps **R1** (associations isomorphic),
**R2** (the readback engine — "THE BIG ONE"), **R3** (Thue confluence + final assembly), plus the P1–P7
sub-brick breakdown of R2. Also `docs/ROADMAP.md` (project status) and the `reference_tactus_*` /
`project_semantic_finite_basis` memory notes.

---

## 6. How tactus (the proof assistant) works — crash course

**Tactus is a fork of [Verus](https://github.com/verus-lang/verus).** Verus lets you write **Rust** and
prove it correct with SMT; tactus replaces the Z3 SMT backend with a **Lean 4** backend. For our purposes
it behaves like Verus. You write specs and proofs in Rust-with-annotations inside a `verus! { ... }` block.

**Three function modes:**
- `spec fn` — pure mathematical definitions (ghost; e.g. `m4_rules`, `positivity`). May be recursive with
  a `decreases` clause. `open` = body visible to the solver; `closed`/`opaque` = hidden.
- `proof fn` — lemmas: `requires` (preconditions), `ensures` (postconditions), a ghost body that must
  discharge the obligation. This is where the work is.
- `exec fn` — compiled Rust (not used here).

**Core constructs:** `assert(P)` (prove `P` here); `assert(P) by { ... }` (scoped proof, only `P` leaks);
`forall|i: int| ...`, `exists|i| ...` (with `#[trigger]` hints); `Seq<T>` with `s.len()`, `s[i]`,
`s.drop_first()`, `s.subrange(a,b)`, `s + t` (concat), `seq![..]`; `=~=` is extensional (structural)
equality for sequences — use it, then `==` follows. Recursion needs a `decreases` measure that provably
strictly decreases.

**Verifying (IMPORTANT):** use the **crate-local `./check.sh`** (it runs the Lean backend with the
group-theory export). Examples:
```
./check.sh --verify-module m4_defect_flow      # verify just the new module (fast iteration)
./check.sh                                     # full crate gate
```
Read `N verified, M errors`; assert on **`0 errors`**, not exact counts (counts drift). A reported
**"rlimit exceeded" is a mislabel for Lean `maxHeartbeats`** — the proof is too big for one solver call;
**split it into smaller helper `proof fn`s** (each gets a fresh solver context). Verification is
deterministic — a failure is never a "cache issue"; diagnose it.

**Battle-tested idioms (from M1/M2/M3 — apply throughout):**
- **Split big proofs.** A `proof fn` with 40+ lemma calls will blow the heartbeat limit. Factor into
  focused helpers (M3's capstone was split into `lemma_sfu_setup` + `lemma_right_cancel_p0` +
  orchestrator). Each helper = its own Lean context.
- **`positive_word` is recursive, not `forall`-shaped.** To prove it, use a `cons` helper
  (`lemma_positive_cons`) or a `forall ⟹ positive_word` bridge (`lemma_forall_positive`), not a bare
  `assert forall`. `word_valid` *is* `forall`-shaped, so it's easy.
- **`.drop_first()` needs `w.len() > 0`** to index/unfold; guard your recursive lemmas with it.
- **Recursive spec fns on singletons** (`num_a`, `no_sym`, custom predicates) often need an explicit
  unfold step (`assert(f(seq![x]) == ...)`) — the solver won't always peel them for free.
- **`spec fn` applications inside quantifiers** hurt trigger inference; prefer named recursive predicates.
- **Struct literals / two-step `subrange` unfolds** sometimes need intermediate `assert(x == rules_pres(..))`
  helper equalities so the solver evaluates a field like `.num_generators`.
- **Search the crate before building.** M3's scariest-looking obligation (HNN base-word faithfulness)
  turned out to be already banked as `britton_lemma_unconditional`. Grep first.
- **Commit freely, in small green units.** After each helper verifies (`0 errors`), commit.

---

## 7. What we need from you (the plan)

Produce a **resumable, brick-by-brick plan** for `lemma_m4_positivity`, in the spirit of
`docs/m3-blinker-plan.md`. Concretely:

1. **Group-side bricks (expected near-verbatim from M3):** list them (`m4_rules/_valid`, `m4_data/_valid`,
   `m4_pres_valid`, reuse `sub_hom`, `lemma_m4_iso`, `lemma_group_to_hnn`, `lemma_m4_backward`, **R1**
   `hnn_associations_isomorphic` via the `a↔b` swap). Note the exact `m4_data` association-tuple order to
   confirm against `hnn.rs`, and any place the second-relator word makes the iso proof differ from M3.
2. **The readback (R2) — the real design.** Propose how to formalize **defect flow** on top of the
   `act_syls` HNN normal form: how to represent the defects `mᵢ` and the compensation equation
   `hᵢ = (ab)^{−mᵢ} gᵢ (ba)^{mᵢ₊₁}`; how to state and prove the three local-forcing lemmas (cases
   `m<0`, `m≥2`, `m=1`); how to structure the rightward-propagation induction and the boundary discharge;
   and how it feeds `⟹`. Identify which M3 readback pieces survive (the NF scaffolding) and which are new.
   Flag the **main risk** and, where the argument is subtle, suggest a first assertion-level decomposition.
3. **M4's Thue side:** the termination measure for normal-form reduction is **not `#a`** (rule 2 adds an
   `a`); it is "state letters move strictly right." Specify the measure and the `lemma_exists_nf` analog
   (or argue we can avoid an explicit reduction, as the readback may allow).
4. **R3 / assembly:** the dispatcher + `lemma_m4_positivity` (combine `⟹` with the free `⟸`).
5. **Ordering & checkpoints:** dependency-ordered brick list, each a small verifiable unit, with
   `./check.sh --verify-module` checkpoints and suggested commit points. Call out anything you'd want a
   human decision on before starting.

Please also flag any place where you think the paper argument in §4 has a gap or an unstated assumption —
we would rather find it now than mid-proof.

---

## 8. CATALOG findings (reuse map — added after scanning `docs/CATALOG.md`)

**⭐ Key de-risking fact.** The Britton/coset engine is **fully data-parametrized**, not hardcoded to
M3's subgroups: `a_words(data)`/`b_words(data)` (`normal_form_afp_textbook.rs:27,32`) read the associated
subgroups from `data.identifications`, and `textbook_act_hnn(data, …)` / `act_syls(data, …)` /
`b_rcoset_rep(data, …)` all take the data. So M4's `⟨ab⟩→⟨ba⟩` flows through the **entire** normal-form
engine automatically. **M4 = reuse the engine, write a new readback analysis.** The engine will correctly
*compute* the `⟨ba⟩`-coset reps; the defect-flow argument is about *what those reps are*.

**(A) Group-side — near-verbatim copies of M3 (swap the association tuple + 2nd-relator word):**
`m3_rules/m3_data/sub_hom/swap_hom` and `lemma_m3_rules_valid, _pres_valid, m3_backward, m3_data_valid,
lemma_qa2_equiv_b2` (→ `qab_equiv_ba`), `lemma_sub_valid, group_to_hnn, swap_valid, swap_emb, m3_iso,
sub_on_base, m3_base` (all in `m3_blinker.rs`, see catalog line 552 for exact `@line`s).

**(B) Generic engine — reuse wholesale, no changes (HNNData/AmalgamatedData-polymorphic):**
- `britton_via_tower.rs`: `textbook_act_hnn@4627`, `britton_lemma_unconditional@2195`, `britton_lemma_full@8743`,
  `lemma_act_base@4654`, `lemma_act_compose@4677`, `lemma_single_step_preserves_syls@8644`,
  `lemma_derivation_preserves_syls@8701`, `lemma_group_cancel_right@6219`, and the `b_rcoset_rep`/`_h`
  plumbing (`lemma_psi_p_*`, `lemma_b_rcoset_h_*`).
- `normal_form_afp_textbook.rs`: `a_rcoset_rep@425, b_rcoset_rep@529, same_a_rcoset@354, same_b_rcoset@471,
  a_rcoset_h@455, b_rcoset_h@603`, `lemma_afp_injectivity_textbook@7941`, + the shortlex coset lemmas.
- `machine_group.rs`: `act_syls`. `hnn.rs`: `hnn_associations_isomorphic@74, lemma_base_embeds_in_hnn@158,
  lemma_hnn_conjugation@173`. `base_swap.rs`: `lemma_same_group_iff@433` (the Tietze iso tool).
- `presentation_lemmas.rs`: `lemma_equiv_concat_left@62/right@166, word_inverse_left@325/right@271` (cancellation).
- `free_word_problem.rs`: `lemma_free_group_equiv_freely_equivalent`. `m3_blinker.rs` (generic-enough to lift):
  `lemma_syls_preserved@764, reduced_unique@827, base_reduced_unique_hnn@2377, sub_first_decode@2414,
  sub_injective@2427` (retarget to `m4_data`).

**(C) Readback — REDESIGN for defect flow (do NOT reuse M3's parity machinery):**
M3-specific and tied to the `⟨a²⟩` parity head-cap — replace, don't copy: `nf_gap, gap_word, gap_syls,
split_q, no_qa/no_qpa/no_qaa, no_sub3, sub_alpha, parity_head_cap, lemma_parity_head_cap,
lemma_b_rcoset_rep_eq_gap` (**the `rep=gap` lemma — M4 needs a defect-flow analog, this is the crux**),
`lemma_act_gap_word, lemma_act_syls_split, lemma_split_gaps_nf, lemma_m3_nf_readback`. Also
`ffnf/num_a/is_redex_at/fire_at/exists_nf` — **M4's Thue termination is not `#a`** (rule 2 `q′b→aq` adds an
`a`); it is "state letters move right," so the nf-reduction measure must change.

**Possibly useful new tool for the global argument:** `abelianization.rs` (`abelianization@38,
lemma_abelianization_preserves_equiv@348`) — a conserved-quantity invariant could underpin the
defect-conservation / boundary-discharge step (the doc's `2(a−b)=0` remark hints an abelian invariant is
in play). Worth the planner's consideration.

**Precedents for the defect-CONSERVATION step (from a full CATALOG read).** The defect `mᵢ` argument is a
"conserved ℤ-quantity that must discharge at the word boundary." The crate already has this exact
proof-pattern in several places — study them as models for the hardest brick:
- `conj_free_core.rs`: `asum`/`bsep` are net-exponent invariants with `lemma_asum_inverse_pair_zero@108`,
  `lemma_reduce_preserves_bsep@391`, `lemma_count1_bsep_invariant@886` (a ℤ-count preserved under free
  reduction, then used to force a boundary conclusion) — **the closest structural analog**.
- `machine_group.rs`: `x_exp_sum@4994` + `lemma_x_exp_sum_step_invariant@5133`,
  `lemma_x_exp_sum_equiv_invariant@5212` (a generator-exponent sum invariant under *group equivalence*).
- `abelianization.rs`: `lemma_abelianization_preserves_equiv@348` (the clean off-the-shelf ℤⁿ invariant).
The recommended pattern: define the defect/net-exponent as a `spec fn` on words, prove it's preserved under
`reduce_at`/single Thue-or-free step (mirror `lemma_reduce_preserves_bsep`), and use it to annihilate the
defect at the right boundary. **Bottom line of the full catalog read:** the crate splits into two campaigns
— the traditional Higman/Miller ZFC route (most modules, NOT on M4's path) and the M-ladder Thue-positivity
route (Area 12 + Areas 1–3, which is all M4 needs). No hidden M4 blocker; the engine is ready, the readback
is the design.
