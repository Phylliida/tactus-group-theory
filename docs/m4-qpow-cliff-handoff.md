# `lemma_qpow_conj` — a verification-cliff handoff (tactus / Verus + Lean backend)

**What we need from you:** make `lemma_qpow_conj` (and its helpers) in `src/m4_qpow.rs` **verify in a
reasonable time** (target: seconds, not minutes). Right now a *single non-recursive* helper in this file
runs **>42 minutes at 100% CPU without finishing**. The math is (we believe) correct; the problem is
verification cost / an apparent non-termination under the **Lean backend**. The full current code is in
§6 below, verbatim.

---

## 1. Environment (important — this is not stock Verus)

This crate (`tactus-group-theory`) is verified with **tactus**, a fork of
[Verus](https://github.com/verus-lang/verus) that **replaces the Z3 SMT backend with a Lean 4 backend**
(`--lean-backend`). Everything is written in Verus-flavored Rust inside `verus! { }`. A reported
"rlimit exceeded" is a **mislabel for Lean `maxHeartbeats`**. Standard Verus idioms mostly apply, but
**performance characteristics differ from Z3** — in particular we suspect the Lean backend does **not**
apply Z3-style *fuel* to recursive `spec fn`s the same way (see §4).

**How to verify (crate-local):**
```bash
# whole module (all 5 fns in m4_qpow):
../tactus/source/target-verus/release/verus --lean-backend --crate-type=lib src/lib.rs --verify-module m4_qpow
# ONE function (scopes verification; still compiles whole crate ~30s floor):
... --verify-only-module m4_qpow --verify-function qpow_step_pos
# ALWAYS wrap in a timeout so a hang can't run for 40+ min:
timeout 300 ../tactus/source/.../verus --lean-backend ... --verify-function qpow_step_pos
```
Baseline for "normal": a *light* sibling module (`m1_guard`, 34 fns) verifies in **54s**; the whole
`m4_defect_flow` module (43 fns, incl. the `abpow`/`bapow` "pw library") verifies in **55s, 0 errors**.
So the compile floor is ~30s and a healthy module is ~1 min. `qpow_step_pos` **alone** does not finish
in 42 min. That is the anomaly.

---

## 2. The theorem

We are proving the HNN-conjugation power law for the M4 group `⟨a,b,q | q(ab)q⁻¹ = ba⟩` (an HNN extension
of `F(a,b)`, stable letter `q`, associated subgroups `⟨ab⟩→⟨ba⟩`):

> **`lemma_qpow_conj(e)`**: `equiv_in_presentation(hnn_presentation(m4_data()),  q·(ab)^e·q⁻¹,  (ba)^e)`
> for **all `e: int`** (both signs).

Symbols: `a=Gen(0)`, `b=Gen(1)`, `q=Gen(2)`, `q⁻¹=Inv(2)`. `(ab)^e` and `(ba)^e` are the spec fns
`abpow(e)`/`bapow(e)`. This is future infrastructure (a "peeling producer" step); it is **not yet used**
by anything, but we want it verified.

The mathematical proof is a trivial induction: `q·(ab)^e·q⁻¹ = (q·ab·q⁻¹)·(q·(ab)^{e-1}·q⁻¹) ≡ ba·(ba)^{e-1}
= (ba)^e`, using the base relator once and the (e-1) case. The base case `q·ab·q⁻¹ ≡ ba` is
`lemma_qab_equiv_ba` and **verifies fast** (see §3).

---

## 3. Key definitions & the diagnostic that localizes the problem

**`equiv_in_presentation` (src/presentation.rs) — an OPEN existential over derivations:**
```rust
pub open spec fn equiv_in_presentation(p: Presentation, w1: Word, w2: Word) -> bool {
    exists|d: Derivation| derivation_valid(p, d, w1, w2)
}
```
The chaining lemmas are purely atomic at the `equiv` level (they build the witness `Derivation`
internally):
```rust
pub proof fn lemma_equiv_transitive(p, w1, w2, w3) requires equiv(p,w1,w2), equiv(p,w2,w3) ensures equiv(p,w1,w3)
pub proof fn lemma_equiv_symmetric (p, w1, w2)     requires equiv(p,w1,w2)                  ensures equiv(p,w2,w1)
// (src/presentation_lemmas.rs)
pub proof fn lemma_equiv_concat_left (p, w1, w2, s) requires equiv(p,w1,w2) ensures equiv(p, w1+s, w2+s)
pub proof fn lemma_equiv_concat_right(p, s, w1, w2) requires equiv(p,w1,w2) ensures equiv(p, s+w1, s+w2)
```

**`abpow`/`bapow` (src/m4_defect_flow.rs) — recursive over a symbolic `int`, prepend-style:**
```rust
pub open spec fn abpow(t: int) -> Word decreases (if t >= 0 { t } else { -t }) {
    if t == 0 { empty_word() }
    else if t > 0 { seq![Gen(0), Gen(1)] + abpow(t - 1) }     // ab · (ab)^{t-1}
    else          { seq![Inv(1), Inv(0)] + abpow(t + 1) }     // (ab)⁻¹ · (ab)^{t+1}
}
// bapow identical with ba = [Gen(1),Gen(0)] and (ba)⁻¹ = [Inv(0),Inv(1)]
```

**The base fact, which VERIFIES FAST (part of the 55s module):**
```rust
pub proof fn lemma_qab_equiv_ba()
    ensures equiv_in_presentation(hnn_presentation(m4_data()),
        seq![Gen(2),Gen(0),Gen(1),Inv(2)],   // q·ab·q⁻¹  (all CONCRETE symbols)
        seq![Gen(1),Gen(0)]);                 // ba
```

**⭐ The diagnostic split.** `lemma_qab_equiv_ba` does an `equiv`-derivation chain over **concrete** words
and is fast. `qpow_step_pos` does a *structurally identical* `equiv`-derivation chain, but over words that
contain the **symbolic recursive** terms `abpow(e-1)`, `bapow(e-1)`, `abpow(e)`, `bapow(e)` — and it does
**not terminate in 42 min**. The only difference is symbolic-power-words vs concrete words. So the cost
is the interaction of `equiv_in_presentation` reasoning with **symbolic `abpow`/`bapow`**.

There is also `lemma_hnn_conjugation(data, i)` (src/hnn.rs) giving the single-step base
`q⁻¹·assoc[i].0·q ≡ assoc[i].1` — usable but only for one power, so it doesn't avoid the induction.

---

## 4. What we've tried (all failed) and the current hypothesis

Original `lemma_qpow_conj`: one recursive fn with three branches (`e==0`, `e>0`, `e<0`), each building the
`equiv` chain inline. **Cliff** — never finished; the whole `m4_defect_flow` module went from ~1 min to
>12 min the moment it was added (which is why it's quarantined into its own `m4_qpow.rs`).

1. **Branch-split** (current structure): extracted the `e>0` and `e<0` bodies into **non-recursive** step
   lemmas (`qpow_step_pos`/`qpow_step_neg`) that take the `(e∓1)` result as a *precondition*, leaving
   `lemma_qpow_conj` a slim dispatcher. Rationale: give each heavy chain its own Lean context, remove the
   recursion from the heavy part. **Result: `qpow_step_pos` alone still ran 195s and climbing.** So the
   recursion was **not** the cause.
2. **`hide(equiv_in_presentation)`** at the top of every fn (treat equiv facts as opaque atoms so Lean
   never unfolds the `∃Derivation` body). Rationale: the atoms are all the chaining lemmas need.
   **Result: `qpow_step_pos` alone ran >42 min and did not finish.** So (apparently) not the equiv
   existential either — or `hide` is not honored by the Lean backend.
3. **`hide(abpow); hide(bapow)`** (added on top of `hide(equiv)`). **Result: `qpow_step_pos` alone
   TIMED OUT at 300s.** No improvement.

**Big signal: `hide` may be a no-op under the Lean backend.** `hide(equiv)` and `hide(abpow)` both
changed nothing (42 min → still hanging). If `hide`/`reveal` are silently ignored by `--lean-backend`,
every opacity-based idea below is dead on arrival — **verify that first** (e.g. does `reveal_with_fuel`
even compile/matter here?). The fix may need to be structural (don't put symbolic-power words inside
`equiv` goals at all) rather than opacity-based.

**Current hypothesis — a symbolic-unfolding / fuel loop.** 42 min at 100% CPU for a *non-recursive*
function smells like **unbounded work**, not superlinear-but-terminating. The prime suspect: the Lean
backend unfolds `abpow(e)` for **symbolic `e`** without a fuel bound, so `abpow(e) → abpow(e-1) →
abpow(e-2) → …` never bottoms out (it never reaches the `e==0` base for symbolic `e`). This fits the
concrete-fast / symbolic-hang split exactly. The pw-library lemmas (`lemma_abpow_add`, etc.) *do* reason
about symbolic `abpow` and verify fast — but they use `reduces_to`/`freely_equivalent` (free reduction),
**not** `equiv_in_presentation`; something about combining the two may be what triggers the blowup.

If the hypothesis is right, the fix is to **hide `abpow`/`bapow`** and unfold them **exactly once** where
needed (the only spots that need an unfold are `blk + t =~= abpow(e)` and `ba + bapow(e-1) =~= bapow(e)`,
each a single `e>0`/`e<0`-branch step), e.g. via `reveal_with_fuel(abpow, 1)` in a scoped
`assert(...) by { }`. We have not yet confirmed this works.

### ⭐⭐ CORRECTED, VALID DIAGNOSIS — the cliff is a *recursive proof fn with an `equiv`-over-`abpow` ensures*

**METHODOLOGY WARNING that invalidated our first round of probes:** `--verify-function NAME` on this
build does **NOT** verify only `NAME` — it re-verifies **every function in that function's module**
(despite printing "verifying module … (selected functions)"). So any probe placed in a module that also
contains the cliff function will "time out" because of the cliff, not the probe. **To isolate a function
you must put it in a module that contains *only* it (or only it + its deps).** We did this with a scratch
module `m4_probe` and `--verify-module m4_probe`, which *does* scope correctly.

With valid isolation (`timeout`-capped, in dedicated modules), the picture is completely different from
our first (broken) round:

| Isolated in its own module | Result |
|---|---|
| bare `abpow(e) =~= ab + abpow(e-1)` (no equiv) | **51s, 0 errors — FINE** (kills the "module-boundary"/`=~=` theories) |
| `lemma_conj_split`, `lemma_qabinv_equiv_bainv` (equiv, no power) | **fast, verify** |
| `qconj_step_generic` (equiv over *opaque* words) | **fast, verifies** |
| `qpow_step_pos` / `qpow_step_neg` (equiv over `abpow`, **non-recursive**) | **fast, verify** (~40s for the whole non-recursive set: 7 fns) |
| `lemma_qpow_conj` (**recursive** proof fn, ensures `equiv(q·abpow(e)·q⁻¹, bapow(e))`) | **HANGS (>240s)** |

**The cliff is exactly and only the recursive proof fn whose `ensures` is an
`equiv_in_presentation`-over-`abpow` goal.** Every non-recursive ingredient is fast. And note the pw
library (`lemma_abpow_add`, etc.) contains **recursive** proofs over `abpow` that are fast — but their
ensures is `reduces_to` (`∃n. reduces_in_steps`), not `equiv_in_presentation` (`∃d. derivation_valid`).
So the trigger is specifically **a recursive well-founded proof whose motive carries the `equiv` /
`∃Derivation` existential** (with `abpow` inside it).

**Source-level fixes we tried on the recursion — all still HANG (>240s):**
- `decreases (if e>=0 {e} else {-e})` (the original) → hang.
- Split into two recursions with **simple** `decreases e` / `decreases -e` → hang. (Not the `decreases` form.)
- **Opaque motive**: `#[verifier::opaque] spec fn qpc(e)=equiv(...)`, recurse with `ensures qpc(e)`,
  `reveal(qpc)` in the body → still hangs.
- **Opaque Word PARAMS**: `proof fn rec(e, va, vb) requires va==abpow(e), vb==bapow(e) ensures
  equiv(q·va·q⁻¹, vb)` → still hangs. (The recursive *call* `rec(e-1, abpow(e-1), bapow(e-1))`
  re-instantiates the different-words equiv, so the opaque motive doesn't remove it.)

**⭐⭐⭐ SHARPEST characterization (from same-only-in-a-dedicated-module probes, all `timeout`-capped):**

| recursive proof fn, ensures/uses… | result |
|---|---|
| `equiv(abpow(e), abpow(e))` — same word | **fast** |
| recursive result *used* via a same-word `equiv` precondition | **fast** |
| `equiv(abpow(e)+bapow(e), abpow(e)+bapow(e))` — both fns *present*, same word | **fast** |
| `equiv(q·abpow(e)·q⁻¹, bapow(e))` — **`abpow` LHS *related to* `bapow` RHS** | **HANG** |

So the trigger is **not** recursion, **not** the motive existential, **not** merely having `abpow`/`bapow`
present — it is a recursive proof whose equiv motive **relates two *different* symbolic-recursive words**
(`abpow(e)` on one side, `bapow(e)` on the other). Non-recursively, `qpow_step_pos` proves exactly that
different-words equiv and is *fast* — it only loops inside a recursion.

**Why no source dodge works:** the theorem's induction hypothesis *is* that different-words equiv
(`equiv(q·abpow(e-1)·q⁻¹, bapow(e-1))`); the recursion must produce it (recursive call) and consume it
(the step). It's intrinsic to the statement, so opaque motives/params only relocate it — they can't
remove it. **This looks like it requires the backend fix** (see §5.1/§5.2): make the Lean translation
stop unfolding both recursive `spec fn`s when relating them in a recursive `equiv` goal.

**What DOES verify (committed, in `src/m4_qpow.rs`, 8/0, ~54s):** the full non-recursive restructure —
`lemma_pow_zero/unfold_pos/unfold_neg` (the `==` unfold equations), `qconj_step_generic` (generic
HNN-conj step over opaque words), `qpow_step_pos/neg`. These are the reusable "peeling" machinery. Only
the ~10-line recursive `lemma_qpow_conj` (commented out at the bottom of the file) is blocked.

**Where to go from here (this now looks backend-level, and you own the fork):**
1. **Read the generated Lean for the recursive `lemma_qpow_conj`** (`--emit-lean` / keep temp files) and
   run it with `set_option trace.profiler true; set_option maxHeartbeats 400000`. This will name the
   looping tactic and confirm whether it's the well-founded-recursion *motive* setup (our hypothesis) or
   the body. Diff the generated `.lean` for the recursive vs the non-recursive (`step_pos`) version — the
   delta is the culprit.
2. **Compare how the backend translates a recursive proof fn's `equiv`-ensures vs a `reduces_to`-ensures**
   (the pw library is the fast control). If `derivation_valid`/`equiv_in_presentation` is being fed to an
   unconditional simp/search tactic in the recursion's termination or motive elaboration, gate it (real
   fuel/`hide` semantics, or don't emit recursive-fn equation lemmas into the default simp set).
3. **Source-side escape hatch if the backend can't be touched now:** find/write a *non-recursive* proof of
   the power law — e.g. a general "conjugation distributes over powers" result already in the crate, or an
   induction principle that returns the `equiv` as a `reduces_to`-shaped statement first and converts once
   at the end. (We did not find one; the math inherently needs induction, and every inductive encoding we
   tried routes through a recursive proof fn.)

---

## 5. What we'd like you to try (ideas, not prescriptions)

- **Confirm/deny the fuel loop.** A minimal probe: does a non-recursive `proof fn p(e:int) requires e>0
  ensures abpow(e) =~= seq![Gen(0),Gen(1)] + abpow(e-1) { }` verify instantly, or hang? Does adding
  `hide(abpow)` + `reveal_with_fuel(abpow,1)` change it? (Wrap in `timeout`.)
- **Split-and-binary-search** `qpow_step_pos`: cut its body into many tiny scoped `assert(F) by { … }`
  blocks / sub-lemmas, verify incrementally, and find the *exact* statement that explodes. (This is our
  planned next step regardless.)
- **`reveal_with_fuel` discipline** for `abpow`/`bapow`, and/or marking them `#[verifier::opaque]` at the
  definition with targeted reveals (note: opaque-at-definition affects the whole crate — the 55s pw
  library relies on them, so measure that too).
- **Avoid symbolic-power words in `equiv` goals entirely**: e.g. prove the `e≥0` case by induction where
  the induction variable is a `nat` and the words are built by an *exec-free* structural recursion that
  Lean can see terminates, or restructure so `equiv` is only ever asserted between *concrete-shaped*
  words with the symbolic tail carried as an opaque `Word` variable (so Lean never peers inside it).
- **Scope every lemma's facts** with `assert(F) by { lemma(); }` so equiv facts don't accumulate in one
  context (backend-agnostic; from our rlimit guide).

Please **wrap every verification attempt in `timeout 300`** — a bare run can burn 40+ minutes. Report
which single statement/technique moved the needle; we care about the mechanism, not just a green check.

Constraints: **no `#[verifier::external_body]`, `assume`, or `admit`** — this must be a real proof. If you
change `abpow`/`bapow`'s definition or opacity, re-verify `m4_defect_flow` (must stay 43/0) since the pw
library depends on them.

---

## 6. The code, verbatim (`src/m4_qpow.rs`)

```rust
// m4_qpow.rs — M4 B8 enabler (2): q·(ab)^e·q⁻¹ ≡ (ba)^e  (used later by the peeling producer).
//
// QUARANTINED out of m4_defect_flow.rs: lemma_qpow_conj is a verification CLIFF under the Lean
// backend (recursive equiv_in_presentation derivation-building — the module verified in minutes at
// 43 fns and stopped finishing the moment this trio was added). Isolating it keeps m4_defect_flow
// fast + green while this is reworked. Rework idea: prove the e≥0 case by a single-branch
// induction, then derive e<0 non-recursively via lemma_equiv_inverse (mirroring qab→qabinv),
// and drop the intermediate `assert(equiv_in_presentation(...))` re-assertions.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::m4_defect_flow::*;

verus! {

// conjugation splits over concat: (q·x·q⁻¹)·(q·y·q⁻¹) ≡ q·(x·y)·q⁻¹  (middle q⁻¹q cancels).
proof fn lemma_conj_split(x: Word, y: Word)
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        (seq![Symbol::Gen(2)] + x + seq![Symbol::Inv(2)]) + (seq![Symbol::Gen(2)] + y + seq![Symbol::Inv(2)]),
        seq![Symbol::Gen(2)] + (x + y) + seq![Symbol::Inv(2)]),
{
    use crate::presentation_lemmas::*;
    hide(equiv_in_presentation);  // atomic equiv facts — don't unfold the ∃Derivation body
    hide(abpow); hide(bapow);     // B-test: stop symbolic power-word unfolding (fuel-loop hypothesis)
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let ax = seq![Symbol::Gen(2)] + x;                       // q·x
    let by = y + seq![Symbol::Inv(2)];                       // y·q⁻¹
    let mid = seq![Symbol::Inv(2), Symbol::Gen(2)];          // q⁻¹·q
    assert(inverse_word(seq![Symbol::Gen(2)]) =~= seq![Symbol::Inv(2)]) by (compute);
    lemma_word_inverse_left(hp, seq![Symbol::Gen(2)]);        // q⁻¹·q ≡ ε
    assert(concat(inverse_word(seq![Symbol::Gen(2)]), seq![Symbol::Gen(2)]) =~= mid);
    lemma_equiv_concat_right(hp, ax, mid, empty_word());     // ax·mid ≡ ax·ε
    assert(concat(ax, empty_word()) =~= ax);
    lemma_equiv_concat_left(hp, concat(ax, mid), ax, by);    // (ax·mid)·by ≡ ax·by
    assert((ax + mid) + by =~= (seq![Symbol::Gen(2)] + x + seq![Symbol::Inv(2)]) + (seq![Symbol::Gen(2)] + y + seq![Symbol::Inv(2)]));
    assert(ax + by =~= seq![Symbol::Gen(2)] + (x + y) + seq![Symbol::Inv(2)]);
}

// q·(ab)⁻¹·q⁻¹ ≡ (ba)⁻¹  — the inverse of lemma_qab_equiv_ba.
pub proof fn lemma_qabinv_equiv_bainv()
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)],   // q·b⁻¹a⁻¹·q⁻¹
        seq![Symbol::Inv(0), Symbol::Inv(1)]),                                  // (ba)⁻¹
{
    hide(equiv_in_presentation);  // atomic equiv facts — don't unfold the ∃Derivation body
    hide(abpow); hide(bapow);     // B-test: stop symbolic power-word unfolding (fuel-loop hypothesis)
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    lemma_qab_equiv_ba();
    assert(hp.num_generators == 3);
    assert(word_valid(seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)], 3));
    assert(word_valid(seq![Symbol::Gen(1), Symbol::Gen(0)], 3));
    crate::normal_form_afp_textbook::lemma_equiv_inverse(hp,
        seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)],
        seq![Symbol::Gen(1), Symbol::Gen(0)]);
    assert(inverse_word(seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)]) =~= seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)]) by (compute);
    assert(inverse_word(seq![Symbol::Gen(1), Symbol::Gen(0)]) =~= seq![Symbol::Inv(0), Symbol::Inv(1)]) by (compute);
}

// e>0 inductive STEP (non-recursive): from the (e-1) conjugation result, derive the e result.
// Extracted into its own lemma so the heavy equiv-derivation chain gets a clean Lean context,
// separate from the recursion — this is what tamed the qpow_conj verification cliff.
proof fn qpow_step_pos(e: int)
    requires
        e > 0,
        equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
            seq![Symbol::Gen(2)] + abpow(e - 1) + seq![Symbol::Inv(2)], bapow(e - 1)),
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2)] + abpow(e) + seq![Symbol::Inv(2)], bapow(e)),
{
    use crate::presentation_lemmas::*;
    use crate::presentation::{lemma_equiv_symmetric, lemma_equiv_transitive};
    hide(equiv_in_presentation);  // atomic equiv facts — don't unfold the ∃Derivation body
    hide(abpow); hide(bapow);     // B-test: stop symbolic power-word unfolding (fuel-loop hypothesis)
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    let goal_l = q + abpow(e) + qi;
    let blk = seq![Symbol::Gen(0), Symbol::Gen(1)];          // ab
    let t = abpow(e - 1);
    let a = (q + blk + qi) + (q + t + qi);
    let ba = seq![Symbol::Gen(1), Symbol::Gen(0)];
    lemma_conj_split(blk, t);                                // equiv(a, q·(blk·t)·q⁻¹)
    assert(blk + t =~= abpow(e));                            // abpow(e) = ab + abpow(e-1)
    assert(q + (blk + t) + qi =~= goal_l);
    assert(equiv_in_presentation(hp, a, goal_l));
    assert(q + blk + qi =~= seq![Symbol::Gen(2), Symbol::Gen(0), Symbol::Gen(1), Symbol::Inv(2)]);
    lemma_qab_equiv_ba();                                    // equiv(q·ab·q⁻¹, ba)
    assert(equiv_in_presentation(hp, q + blk + qi, ba));
    lemma_equiv_concat_left(hp, q + blk + qi, ba, q + t + qi);       // equiv(a, ba·(q+t+qi))
    lemma_equiv_concat_right(hp, ba, q + t + qi, bapow(e - 1));      // uses the precondition
    lemma_equiv_transitive(hp, a, ba + (q + t + qi), ba + bapow(e - 1));
    assert(ba + bapow(e - 1) =~= bapow(e));                  // bapow(e) = ba + bapow(e-1)
    assert(equiv_in_presentation(hp, a, bapow(e)));
    lemma_equiv_symmetric(hp, a, goal_l);
    lemma_equiv_transitive(hp, goal_l, a, bapow(e));
}

// e<0 inductive STEP (non-recursive): mirror of qpow_step_pos with the (ab)⁻¹/(ba)⁻¹ blocks.
proof fn qpow_step_neg(e: int)
    requires
        e < 0,
        equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
            seq![Symbol::Gen(2)] + abpow(e + 1) + seq![Symbol::Inv(2)], bapow(e + 1)),
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2)] + abpow(e) + seq![Symbol::Inv(2)], bapow(e)),
{
    use crate::presentation_lemmas::*;
    use crate::presentation::{lemma_equiv_symmetric, lemma_equiv_transitive};
    hide(equiv_in_presentation);  // atomic equiv facts — don't unfold the ∃Derivation body
    hide(abpow); hide(bapow);     // B-test: stop symbolic power-word unfolding (fuel-loop hypothesis)
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    let goal_l = q + abpow(e) + qi;
    let blk = seq![Symbol::Inv(1), Symbol::Inv(0)];          // (ab)⁻¹
    let t = abpow(e + 1);
    let a = (q + blk + qi) + (q + t + qi);
    let bai = seq![Symbol::Inv(0), Symbol::Inv(1)];          // (ba)⁻¹
    lemma_conj_split(blk, t);
    assert(blk + t =~= abpow(e));                            // abpow(e) = (ab)⁻¹ + abpow(e+1)
    assert(q + (blk + t) + qi =~= goal_l);
    assert(equiv_in_presentation(hp, a, goal_l));
    assert(q + blk + qi =~= seq![Symbol::Gen(2), Symbol::Inv(1), Symbol::Inv(0), Symbol::Inv(2)]);
    lemma_qabinv_equiv_bainv();                              // equiv(q·(ab)⁻¹·q⁻¹, (ba)⁻¹)
    assert(equiv_in_presentation(hp, q + blk + qi, bai));
    lemma_equiv_concat_left(hp, q + blk + qi, bai, q + t + qi);
    lemma_equiv_concat_right(hp, bai, q + t + qi, bapow(e + 1));     // uses the precondition
    lemma_equiv_transitive(hp, a, bai + (q + t + qi), bai + bapow(e + 1));
    assert(bai + bapow(e + 1) =~= bapow(e));                 // bapow(e) = (ba)⁻¹ + bapow(e+1)
    assert(equiv_in_presentation(hp, a, bapow(e)));
    lemma_equiv_symmetric(hp, a, goal_l);
    lemma_equiv_transitive(hp, goal_l, a, bapow(e));
}

// q·(ab)^e·q⁻¹ ≡ (ba)^e — slim recursion: dispatch to the non-recursive step lemmas.
pub proof fn lemma_qpow_conj(e: int)
    ensures equiv_in_presentation(crate::hnn::hnn_presentation(m4_data()),
        seq![Symbol::Gen(2)] + abpow(e) + seq![Symbol::Inv(2)], bapow(e)),
    decreases (if e >= 0 { e } else { -e }),
{
    use crate::presentation_lemmas::*;
    hide(equiv_in_presentation);  // atomic equiv facts — don't unfold the ∃Derivation body
    hide(abpow); hide(bapow);     // B-test: stop symbolic power-word unfolding (fuel-loop hypothesis)
    let hp = crate::hnn::hnn_presentation(m4_data());
    lemma_m4_data_valid();
    crate::britton_infra::lemma_hnn_presentation_valid(m4_data());
    let q = seq![Symbol::Gen(2)];
    let qi = seq![Symbol::Inv(2)];
    if e == 0 {
        assert(abpow(0) =~= empty_word() && bapow(0) =~= empty_word());
        assert(inverse_word(q) =~= qi) by (compute);
        lemma_word_inverse_right(hp, q);                     // q·q⁻¹ ≡ ε
        assert(concat(q, inverse_word(q)) =~= q + qi);
        assert(q + abpow(0) + qi =~= q + qi);
        assert(empty_word() =~= bapow(0));
        assert(equiv_in_presentation(hp, q + abpow(0) + qi, bapow(0)));
    } else if e > 0 {
        lemma_qpow_conj(e - 1);
        qpow_step_pos(e);
    } else {
        lemma_qpow_conj(e + 1);
        qpow_step_neg(e);
    }
}

} // verus!
```

---

*(Note: the `hide(abpow); hide(bapow)` lines are the in-progress "test 3" from §4 — remove or keep per your investigation.)*
