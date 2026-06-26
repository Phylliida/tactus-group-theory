# The final gate — removing `axiom_ceer_fp_embedding`: design map

*Written 2026-06-26. A review + design-drafting pass over the last remaining arc, done in an
unsupervised session. **Nothing here is built** — the implementation is co-design-gated ("NOT taken
solo", `MESSAGES_FROM_USER.md` 2026-06-22 + AGENDA §3.3 + many prior sessions). This doc pins the
exact current proven endpoints, the precise gap to the axiom, the three sub-gaps with proposed lemma
signatures, the §3.3 Aanderaa–Cohen machine reduction sketch, and — most importantly — the **one
central architectural question** that must be answered against the textbook before any code. It is a
runway, not a build.*

> **Standing rule honored** (`MESSAGES_FROM_USER.md` 2026-06-22): follow the textbook, do not
> reinvent. Sources: Miller `CGTMiller.pdf` §4.1 (Layer 0.5), Cohen §9.6 p.279 + Aanderaa–Cohen
> *Modular machines…* (the machine reduction). The two known *dragons* (`§B` below) are flagged.

---

## 0. TL;DR

- **Baseline is green** (2026-06-26): `tactus-computability-theory ./check.sh` = **250 verified, 0
  errors**; `tactus-group-theory` export validated (per session-2026-06-26 commit `c766c7e`).
- **The axiom** `axiom_ceer_fp_embedding` (`tactus-computability-theory/src/ceer_benign.rs:66`,
  `external_body`) asserts: for `ceer_wf(e)`, ∃ valid finite `p: Presentation` and `emb: nat→Word`
  with `ceer_equiv(e,n,m) ⟺ equiv_in_presentation(p, emb(n), emb(m))`. It is used in exactly ONE
  place: `lemma_ceer_embeds_in_fp_group_main` → `lemma_higman_embedding` (`higman.rs:80`) →
  `theorem_zfc_equiv_in_fp_group`.
- **Two explicit endpoints are PROVEN** that should replace it (Layer 0.5 + Layer 2). They are
  *two different spec representations of the f.g. group `C`*, and **the gate is, in essence, the work
  of identifying them via a fixed modular machine.**
- **The central architectural question** (must be resolved with the textbook, NOT solo): the
  Layer-0.5 artifact `equiv_in_g_limit` is a direct limit with **growing generators** (it keeps the
  c-block explicit, deliberately *not* collapsing Miller's `G` to its fixed finite generating set),
  whereas Layer-2's `c_pred` is a **fixed finite c-block**. Reconciling these is the crux. See §3.

---

## 1. The two proven endpoints (with exact references)

### 1.1 Layer 0.5 — CEER group ↪ Miller `C` (direct-limit form), PROVEN
`tactus-computability-theory/src/ceer_layer05_bridge.rs:955`
```
lemma_ceer_native_embeds_in_c_iff(e, n, w):
    requires word_valid(ceer_to_word(w), n)
    ensures  ceer_group_equiv(e, w, ε)
             <==> equiv_in_g_limit(ceer_decls_fam(e), n, ceer_to_word(w), ε)
```
- `ceer_group_equiv(e, ·, ·)` = the ∞-generated CEER group `⟨gₙ | gₐg_b⁻¹ : declared⟩`
  (`ceer_group.rs`). CEER generator word `gₙ = generator_word(n) = [Gen(n)]`; relator
  `ceer_relator(a,b) = [Gen(a), Inv(b)]`.
- `equiv_in_g_limit(fam, n, w1, w2)` (`cohen_layer05.rs:735`)
  `:= ∃ M ≥ n. equiv_in_presentation(hnn_presentation(miller_data(M, fam(M))), w1, w2)`.
  **Growing-generator direct limit**: `miller_data(M, decls).base.num_generators == M+2`
  (M c-generators `Gen(0..M)` + a,b), `M+1` HNN associations, stable letter `t`. The c-block is
  `Gen(0..M)` — one explicit generator per CEER generator, growing with the slice.
- `ceer_decls_fam(e)(M)` (`ceer_layer05.rs:70`) `= Seq::new(M, |s| ceer_relator_at(e,s,M))`, where
  `ceer_relator_at` = the translated `[Gen(a),Inv(b)]` for stage-`s`'s declared pair (if it fits the
  M-slice), else `empty_word()`. So the relator family literally is `{cₐc_b⁻¹ : (a,b) declared}`.

Also banked (`ceer_layer05.rs`): `lemma_ceer_decls_family_valid` (`decls_family_valid(ceer_decls_fam(e))`),
`lemma_ceer_c0_embeds_in_c_iff` (= `lemma_c0_embeds_in_c_iff` specialized to the CEER family).

### 1.2 Layer 2 — Cohen `C = ⟨c;S⟩` ↪ printable f.p. `h3_pres`, PROVEN
`tactus-group-theory/src/cohen_bridge.rs:125`
```
lemma_C_faithful_printable_canonical(mm, n, m, w):     // mm: ModMachine  (exact, cohen_bridge.rs:125)
    requires mod_machine_wf(mm), mm_terminal(mm,0,0), 2*n < m,
             is_c_word(g_m(mm).num_generators, n, w),
             equiv_in_presentation(h3_pres(mm,n,m), w, ε)          // FAITHFULNESS direction
    ensures  equiv_in_pred_presentation(c_pred(mm,n,m,is_S_canonical(mm,n,m)), w, ε)
```
- `h3_pres(mm,n,m)` is a **finite `Presentation`** (uses plain `equiv`, not `equiv_pred`) — Cohen's
  set (I). So it can serve *directly* as the witness `p` of the final theorem. ✓
- `c_pred(mm,n,m,is_S)` (`cohen-section1-assembly-plan.md` §3) = Cohen's `⟨c;S⟩` as a
  `PredPresentation`: `num_generators = h2_num_gens`, relators `= is_S(w) ∨ (Gen(g)≡ε for every
  non-c generator g)`. **Fixed finite c-block** at indices `[c_base, c_base+n)`.
- `is_S_canonical(mm,n,m)` (`cohen_bridge.rs:49`)
  `= { w : ∃α. numbers_word(n,m,α) ∧ mm_in_H0(mm,α,0) ∧ w = w_c(c_base, n, m, α) }`.
- **Soundness direction also available**: `lemma_III` (`higman_consequences.rs`):
  `(α,0)∈H₀(mm) ⟹ w_α(c) ≡ 1 in h3_pres`. Together with faithfulness this gives the iff *for the
  relator words `w_α(c)`* (`cohen_cs6.rs:100` note).
- Modular machine (`machine_group.rs:145,192`): `ModMachine{m,n,quads}`; `mm_in_H0(mm,α,β) :=
  mm_terminal(mm,0,0) ∧ ∃k. mm_reaches(mm,α,β,0,0,k)` — exactly the classic Aanderaa–Cohen `H₀(M)`
  (matches `docs/aanderaa-cohen-construction.md` §1 verbatim).

---

## 2. The target chain (what replaces the axiom)

`theorem_zfc_equiv_in_fp_group` needs `∃ p, emb. presentation_valid(p) ∧ ∀n,m. zfc_equiv_nat(n,m) ⟺
equiv_in_presentation(p, emb(n), emb(m))`. With `p := h3_pres(mm,n,m)` and `emb := the c-encoding of
CEER generators`, the chain is:

```
zfc_equiv_nat(n,m)
  ⟺ ceer_equiv(e,n,m)                              [DONE: lemma_zfc_equiv_is_ceer, e from it]
  ⟺ ceer_group_equiv(e, gen(n), gen(m))            [DONE: lemma_ceer_equiv_iff_group_equiv]
  ⟺ equiv_in_g_limit(ceer_decls_fam(e), …)         [DONE: lemma_ceer_native_embeds_in_c_iff]   (L0.5)
  ⟺ equiv_in_pred_presentation(c_pred(mm,…), …)    [GAP 1 — identify the two C's]
  ⟺ equiv(h3_pres(mm,n,m), emb(n), emb(m))         [GAP 3 — Layer-2 faithful (have) + sound (have)]
```
with `mm` produced by **GAP 2** so that `H₀(mm)` realizes the declared pairs.

(The pairwise form `gen(n) ≡ gen(m)` reduces to the trivial-word form `gen(n)·gen(m)⁻¹ ≡ ε` that all
the lemmas use — mechanical.)

---

## 3. GAP 1 — identify the two `C`s  ⚠ **the central architectural question**

`equiv_in_g_limit(ceer_decls_fam(e), …)` and `equiv_in_pred_presentation(c_pred(mm,…), …)` are
different spec objects. Connecting them is the heart of the gate.

### 3.1 The tension, stated precisely
- **Miller side (Layer 0.5)** keeps the c-block *explicit and growing* — `Gen(0..M)`, one generator
  per CEER generator `gₖ`. The note at `cohen_layer05.rs:706` says this was a *deliberate* choice to
  avoid the "Tietze tax" and "keep Layer 2's c-block view." But the consequence is that
  `equiv_in_g_limit` does **not** exhibit Miller's `G` as *finitely generated* — it is morally the
  ∞-generated `C₀` sitting in a growing-generator `G`-limit.
- **Cohen side (Layer 2)** needs a **fixed finite** c-block of size `n` (Higman's `C = ⟨c₁,…,c_n;S⟩`),
  with the (infinitely many) CEER generators encoded as **words** `w_α(c)` over those `n` generators.

So the formal artifacts disagree on *what the generators are*: growing `Gen(0..M)` vs. fixed
`Gen(c_base..c_base+n)` with everything-as-words.

### 3.2 What the textbook says (Miller §4.1 + companion-confirmed)
The growing-generator direct limit is a **proof device for the relator enumeration**, not the real
generating set. Miller's `G` is genuinely *2-generated* `{a,t}`; the original `gₖ` are the **words**
`gₖ ↦ cₖ a⁻ᵏbaᵏ`-style conjugates living inside `F₂=⟨a,b⟩` (this is exactly the banked
`conj_family`/`conj_family_b` free families, `conj_free_core.rs`/`conj_free_b.rs`). So:
> The finitely-generated input to Cohen's embedding is `⟨a,t | eval(⋃ R_M)⟩` where `eval` substitutes
> each `cₖ ↦ wₖ(a,t)`. The cost of finite generation is *absorbed into the relator words*, which
> remain an r.e. set over the fixed alphabet — exactly the recursively-presented input Higman needs.

### 3.3 The decision (FOR DANIELLE — do not pick solo)
**How should the formal reconciliation be done?** Three candidate routings:

| Route | What | Cost / risk |
|---|---|---|
| **(R1) Substitute-and-collapse** | a hom `Gen(k) ↦ wₖ(c-block)` carrying `equiv_in_g_limit` relators onto fixed-c-block words; prove the c-word problems coincide | the "Tietze tax" the L0.5 authors *avoided* — may be large; but it is the textbook object |
| **(R2) Re-present Miller `G` fixed** | bypass `equiv_in_g_limit`; build a fixed-finite-generator `Presentation` for Miller's `G` directly and re-run the L0.5 faithfulness over it | duplicates L0.5; throws away the direct-limit work |
| **(R3) Common spec predicate** | define `IsCeerGroup(eqpred, e)` abstractly; prove both `equiv_in_g_limit` and `c_pred`-c-word-problem satisfy it; conclude word-problem equality | companion-recommended *organizing* principle — but still needs the relator-set match underneath (does not remove work, only packages it) |

The companion (independent read) favors **substitution wrapped in a spec predicate** (R1∘R3) and
warns: **do not reason about normal closures directly** — prove relator-set containment *both ways*
(`S_CEER ⊆ S_canonical` and ⊇), after which quotient/word-problem identity is the easy lemma.

**This routing choice is the single most important undesigned decision and is exactly the kind of
thing that has burned the project (13k lines) when picked without the textbook.** Surfaced, not taken.

### 3.4 The relator-set match (the concrete obligation under any routing)
Whatever the routing, the math reduces to: the c-word problem of Miller's `C` (relators
`{cₐc_b⁻¹ : (a,b) declared}`) equals that of Cohen's `c_pred` (relators `is_S_canonical =
{w_α(c) : (α,0)∈H₀(mm)}`). Sufficient: **set equality of relators after the c-encoding**, i.e. an
explicit bijection
```
β : (declared-pair index) → (word-number α),   with   w_{β(·)}(c) = encode(cₐ c_b⁻¹)   and
    (α,0) ∈ H₀(mm)  ⟺  α = β(declared pair)
```
The second conjunct is GAP 2. The first (`w_α(c)` hits exactly the encoded CEER relators, with c-block
reindexing `Gen(k) ↔ Gen(c_base+enc(k))`) is the **word-numbering bridge** (AGENDA §3.3 item 1).

---

## 4. GAP 2 — §3.3 machine reduction (Aanderaa–Cohen)

**Goal**: build a single fixed `mm: ModMachine` with `mod_machine_wf(mm)` and an encoding `enc` such
that
```
mm_in_H0(mm, enc(relator-index α), 0)   ⟺   α is the word-number of a declared CEER relator.
```
i.e. `H₀(mm)` realizes the c.e. set `{α : w_α(c) is a CEER relator cₐc_b⁻¹ with (a,b) declared}`.

### 4.1 Source + substrate
- Modular machine + `H₀` already exist and are the classic Aanderaa–Cohen object
  (`machine_group.rs:145–195`, matches `docs/aanderaa-cohen-construction.md` §1).
- *Source note*: the Aanderaa paper PDF in this dir is **not text-extractable** (scanned; poppler
  absent) — read it with the Read tool's visual/PDF mode in the build session, don't burn time on
  `pdftotext`. The modular-machine def is already transcribed into `aanderaa-cohen-construction.md`;
  the un-transcribed part is the *reduction* (register/Turing machine → modular machine).
- The CEER enumerator is a **`RegisterMachine`** (`ceer.rs:13`, `CEER{enumerator}`), with
  `declared_pair(e,s)` = `(reg[1],reg[2])` when `e.enumerator` halts on input `s`.
- **The reduction is: register machine → modular machine.** This is standard (Aanderaa–Cohen prove
  modular machines simulate Turing/register machines), but it is *new computability theory in this
  repo* and must follow the paper's encoding (the `(α,β)` pair simulates the tape/registers via the
  `m`-ary residues; each quadruple = one machine step). **This is the bulk of the gated effort.**

### 4.2 Proposed lemma shape (sketch only — exact form is the design)
```
spec  fn ceer_to_modmachine(e: CEER) -> ModMachine                 // the reduction
proof fn lemma_ceer_modmachine_wf(e) requires ceer_wf(e) ensures mod_machine_wf(ceer_to_modmachine(e))
proof fn lemma_modmachine_realizes(e, a, b)                        // the correctness theorem
    requires ceer_wf(e)
    ensures  mm_in_H0(ceer_to_modmachine(e), enc(a,b), 0) <==> declared_equiv(e, a, b)
```
**Open design sub-questions** (textbook-gated):
1. What is `enc : (a,b) ↦ α`? It must compose with the word-numbering so `w_{enc(a,b)}(c) =
   encode(cₐc_b⁻¹)`. (The numbering `numbers_word`/`w_c` constrains the digit structure — digits
   `1≤d≤2n`; the encoding of a 2-letter relator must fit it.)
2. Does the reduction target `declared_equiv` (one-step declared pairs) or `ceer_equiv` (the full
   transitive closure)? Cohen's `S` is the *relators* (declared pairs); the transitive closure is the
   `ncl(S)` taken by the group, so the machine should realize `declared_equiv` and let the group do
   the closure. **Confirm against the paper.**
3. The modular machine is *deterministic* (`mod_machine_wf`: ≤1 quad per residue pair) and its
   `H₀` is "reaches `(0,0)`". The enumerator is a *search* over stages `s`. The reduction must encode
   "∃ stage s halting with output `(a,b)`" as "the config drives to the origin" — i.e. simulate the
   dovetailed enumerator. This is the real content; **it is where reinvention is most dangerous.**

---

## 5. GAP 3 — final assembly

Given GAP 1 + GAP 2:
- `mm := ceer_to_modmachine(e)`, `p := h3_pres(mm, n, m)` (a finite `Presentation`).
- `emb(k) := w_{enc'(k)}(c)` — the c-word encoding of CEER generator `gₖ` (single-c-generator or
  conjugate image, per the GAP-1 routing).
- **Faithfulness** (`h3_pres ⟹ C`): `lemma_C_faithful_printable_canonical` (HAVE).
- **Soundness** (`C ⟹ h3_pres`): for relator words, `lemma_III` (HAVE). For the assembled iff over
  generator images, check whether a general `equiv_in_pred_presentation(c_pred,·) ⟹ equiv(h3_pres,·)`
  is needed and whether it follows from `lemma_III` applied per-relator (`cohen_cs6.rs:100` /
  `cohen_cs7.rs:23` suggest the only-needed direction is faithfulness for the printable transport —
  verify which direction the *final* iff actually consumes).
- Then rewrite `lemma_higman_embedding` / `lemma_ceer_embeds_in_fp_group_main` to produce `(p, emb)`
  from the explicit chain instead of `axiom_ceer_fp_embedding`, and **delete the axiom**.

---

## 6. Surfaced decisions (for Danielle — none taken)

1. **GAP-1 routing** (§3.3): R1 substitute-and-collapse vs R2 re-present-fixed vs R3 spec-predicate
   (likely R1∘R3). *This is the load-bearing architectural choice.* Needs the Miller §4.1 reading +
   a call on whether the deliberate "no Tietze" choice in `cohen_layer05.rs` is compatible with
   feeding Cohen's fixed-c-block embedding.
2. **GAP-2 encoding** (§4.2): the exact `enc`, the `declared_equiv`-vs-`ceer_equiv` target, and the
   register→modular simulation, all to be pinned against the Aanderaa–Cohen paper *before* code.
3. **Effort go**: GAP 2 (register→modular reduction) is a multi-step new-computability-theory build;
   GAP 1 may be large depending on routing. Both want an explicit effort go, per the standing gate.

## 7. What is solid right now
- Baseline green (250/0 computability; group-theory export validated).
- Both endpoints (§1.1, §1.2) are machine-checked. The remaining work is *connective* (GAP 1, 3) +
  *one new reduction* (GAP 2). No part of the existing construction is in question.
- The two dragons remain marked: (B-dragon-1) the CEER relations cannot be imposed inside a free
  group (the naive telescope collapses F₂); (B-dragon-2) the old `machine_group_backward`
  `external_body` is *slain* (= Layer-1 Theorem 1 ⟹, DONE). The free-group `F∞↪F₂` "shortcut" is a
  dragon (`∼` only c.e.). Follow Miller; carry `C₀`'s relators opaquely.

*Do not start GAP 1/2 implementation without Danielle's design go on §6.1–6.2.*
