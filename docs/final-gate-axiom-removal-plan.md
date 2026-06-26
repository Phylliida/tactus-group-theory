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
- `c_pred(mm,n,m,is_S)` (`cohen_retraction.rs:238`, NOT `cohen-section1-assembly-plan.md` §3) =
  `PredPresentation { num_generators = h2_num_gens(g_m(mm).num_generators, n), relators = |w| is_S(w) }`.
  **⚠ CORRECTED by the §8 audit:** the relators are **`is_S` ONLY** — there is *no* `Gen(g)≡ε`
  non-c-killing disjunction (that lives in the *retraction homomorphism* `c_retraction`'s images,
  `cohen_retraction.rs:246`, not in `c_pred`'s relators). So `c_pred` is **`⟨c;S⟩ ∗ F(non-c gens)`**:
  the non-c generators are *present-but-free*. On a **pure-c word** this presents exactly Cohen's
  `⟨c;S⟩` (free factors are invisible to a pure-c word problem); reaching the literal fixed-`n`-block
  `⟨c;S⟩` requires Tietze-removing the free non-c gens — a *deferred final-packaging step* (the code
  comment flags it). **Fixed c-block** at indices `[c_base, c_base+n)` *inside* the larger gen set.
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
- *Source note (CORRECTED — see §8.6):* the Aanderaa paper PDF **IS text-extractable** via
  `pip install pymupdf` (16/16 text pages; `pdftotext`/`pdftoppm` fail but `pymupdf` works). The
  modular-machine def is already in `aanderaa-cohen-construction.md`; the un-transcribed *reduction*
  (Turing → modular machine) is **Theorem 2, PDF page idx 7** (proof pp.7–9).
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

---

## 8. Runway audit (2026-06-26, unsupervised session — read-only, no code)

*A fresh read-only pass that verifies every endpoint signature, the axiom, and the dependency chain
in §1–§5 **against the actual `tactus-*` source** (the verus MCP indexes the old Z3 crate, so these
were checked directly with Read/Grep on the tactus port). Purpose: guarantee the runway Danielle is
asked to commit effort to is grounded in reality, not drift. **No code written; no decision taken.**
One correction + one hidden sub-task found; the rest confirmed accurate.*

### 8.1 Confirmed accurate (line-grounded)
| Claim | Verified at | Status |
|---|---|---|
| `axiom_ceer_fp_embedding`, `external_body`, `requires ceer_wf(e)` | `ceer_benign.rs:67` (decl; doc said :66 = attr line) | ✓ |
| Axiom used in **exactly one** place | `ceer_benign.rs:84` (`lemma_ceer_embeds_in_fp_group_main`) | ✓ |
| Chain → `lemma_higman_embedding:72` → `theorem_zfc_equiv_in_fp_group:107` | `higman.rs` | ✓ (single axiom dep) |
| L0.5 endpoint `lemma_ceer_native_embeds_in_c_iff` signature | `ceer_layer05_bridge.rs:955` | ✓ exact |
| `equiv_in_g_limit := ∃M≥n. equiv_in_presentation(hnn_presentation(miller_data(M,fam(M))),…)` | `cohen_layer05.rs:735` | ✓ exact |
| `miller_data(M,·).base.num_generators == M+2` (growing c-block `Gen(0..M)` + a,b) | `cohen_layer05.rs:633` | ✓ |
| L2 endpoint `lemma_C_faithful_printable_canonical` signature | `cohen_bridge.rs:125` | ✓ exact |
| `is_S_canonical` definition | `cohen_bridge.rs:49` | ✓ exact |

### 8.2 ⚠ CORRECTION — `c_pred`'s relators (§1.2 fixed inline)
The doc claimed `c_pred` relators `= is_S(w) ∨ (Gen(g)≡ε for non-c g)`. **The actual code
(`cohen_retraction.rs:241`) is `relators: |w| is_S(w)` — `is_S` only.** The non-c-killing `↦ε`
lives in the *retraction homomorphism* `c_retraction` (`:246`), not in `c_pred`. So
**`c_pred ≅ ⟨c;S⟩ ∗ F(non-c gens)`** with the non-c generators *present-but-free*.

### 8.3 Hidden sub-task this surfaces (belongs in GAP 3, §5)
Because `c_pred` carries free non-c generators, the final theorem's chain lands in
`⟨c;S⟩ ∗ F(non-c)`, not literally Cohen's `⟨c;S⟩`. **Two ways to close it** (companion-confirmed):
- **(cheap, sufficient)** a lemma `equiv_in_pred_presentation(c_pred, w, ε) ⟺ w ≡_{⟨c;S⟩} ε` **for
  pure-c `w`** — true by free-product invisibility (a factor element is trivial in `A∗B` iff trivial
  in `A`). The final `emb` maps CEER gens to pure-c words, so this is all the theorem needs.
- **(full hygiene)** Tietze-remove the free non-c gens (the deferred final-packaging step the code
  comment names). Not required for the *truth* of the iff; only for a literally-`⟨c;S⟩` artifact.

### 8.4 GAP-1 framing SHARPENED (the central question, §3)
`equiv_in_g_limit` keeps the c-block **growing** (`Gen(0..M)`, one gen per CEER generator) — so
**L0.5's `C` is, formally, still infinitely generated** (a growing-generator direct limit of Miller
slices), *not* Miller's genuinely finitely-generated `G`. GAP 1 is therefore **not "spec packaging"**
(as "identify the two C's" reads): it is the **∞ → finitely-generated collapse that L0.5 deliberately
deferred** (the "Tietze tax" the `cohen_layer05.rs:704–717` note explicitly chose to skip). The
original CEER generators must become **words** over a fixed finite alphabet (Miller Thm 4.1:
`gₖ ↦ cₖ a⁻ᵏbaᵏ`-style conjugates — exactly the banked `conj_family`/`conj_family_b` free families).
- **Cohen's `n` (c-generator count)** = the f.g. count of the *collapsed* `G`, **not** the CEER
  generator count (infinite — impossible). The companion argues `n = 2` (`{a,t}`/`{a,b}`); the exact
  value is a GAP-1/GAP-2 **design detail coupled to the word-numbering digit structure**
  (`numbers_word` uses digits `1≤d≤2n`, `is_S_canonical`/`w_c`) — **confirm against the actual
  instantiation, do not assert.**
- This *reinforces* the §6.1 gate: R1 (substitute-and-collapse) is precisely paying the deferred
  Tietze tax; it is real Miller-Thm-4.1 content, the hardest part — treating GAP 1 as packaging would
  ignore it. Still **surfaced, not taken.**

### 8.5 Miller §4.1 PRIMARY-SOURCE READ (poppler-free `pymupdf` works; gate-doc tooling claim corrected)
`pdftotext`/`pdftoppm` are absent, but **`pip install pymupdf` succeeds in the venv** and extracts
text fine. **`CGTMiller.pdf` IS extractable** (Thm 4.1 at page idx 55); the Cohen book is image-only
(Layer 2 already done, not needed for GAP 1). So the GAP-1 primary-source read `MESSAGES_FROM_USER.md`
(2026-06-22) demands **was done this session**. Miller's Theorem 4.1 (Higman–Neumann–Neumann),
verbatim construction for `C = ⟨c₁,c₂,… | D⟩`:
- `L = C ⋆ F`, `F = ⟨a,b|⟩`; `A = ⟨b, cᵢa⁻ⁱbaⁱ⟩` and `B = ⟨a, b⁻ⁱabⁱ⟩` free (the banked
  `conj_family`/`conj_family_b`); `G = ⟨a,b,cᵢ,t | D, t⁻¹bt=a, t⁻¹cᵢa⁻ⁱbaⁱt = b⁻ⁱabⁱ⟩`.
- **The collapse (the decisive lines):** rewrite to `cᵢ =_G t b⁻ⁱabⁱ t⁻¹ a⁻ⁱb⁻¹aⁱ` ⟹ `G=⟨t,a,b⟩`;
  since `b = tat⁻¹`, `G=⟨a,t⟩`; substitute `b↦tat⁻¹` to get `cᵢ =_G uᵢ(a,t)`; rewrite `D`'s
  `cᵢ`-words via `uᵢ` into `D̄`; **"Applying Tietze transformations to eliminate the other symbols,
  G ≅ ⟨a,t | D̄⟩."** (Cor 4.2: `G` has the *same number of relations* as `C` — so an r.e. `D` stays
  r.e., exactly Cohen's Layer-2 input.)

**GAP-1 consequence (decision-data, NOT the decision):** **R1 (substitute-and-collapse) IS Miller's
literal proof** — `cᵢ ↦ uᵢ(a,t)`, Tietze-eliminate. So "follow the textbook" (the standing rule)
*points at R1*. Two things this pins:
- **Cohen's `n = 2` is forced, not optional.** Higman/Cohen's Layer 2 *requires a finitely-generated*
  input (that is the theorem's premise); the infinite `cᵢ` cannot be the c-block. After Miller, the
  f.g. input is `⟨a,t⟩` (n=2), `S = D̄`. The companion's "n=2" is textbook-confirmed.
- **The real undesigned residue in §6.1 is the *reconciliation with L0.5's deliberate "no-Tietze"
  choice*, not the routing.** `equiv_in_g_limit` keeps the c-block as `Gen(0..M)` (un-collapsed) on
  purpose (`cohen_layer05.rs:704–717`, "keep Layer 2's c-block view"). R1 = Miller now has to *pay*
  that deferred Tietze tax — i.e. build the `cᵢ↦uᵢ(a,t)` substitution hom + prove the c-word problems
  coincide. **Whether to (a) undo L0.5's choice and collapse, or (b) wrap the growing limit so Cohen's
  c-block IS taken to be the (already-present) `a,b`-image with `cᵢ` re-expressed as words — and the
  *effort* — is the genuine call for Danielle.** Surfaced, not taken.

### 8.6 GAP-2 source located + gate-doc claim corrected (pointer only; NOT read deeply)
The gate doc §4.1 says the Aanderaa paper is "not text-extractable (scanned)". **Wrong — it extracts
cleanly via `pymupdf` (16/16 text pages).** The Turing-machine → modular-machine reduction GAP 2
needs is **Theorem 2, page idx 7** (`"Let T be a Turing machine…"`), with the quadruple-simulation
proof on pp.7–9 (`H₀(Td)`, blank tape). *Deliberately not read deeply this session* — GAP 2 is
sequenced *after* Layer 0.5/GAP 1 (`machine-bridge-and-infinite-gen-plan.md`) and the reduction is
"where reinvention is most dangerous" (§4.2), so it deserves a focused, gated session, not a rushed
unsupervised pass. Pointer recorded so that session starts from the primary source, not a re-derivation.

*Net: the runway is sound and now corrected. The blocker is unchanged — Danielle's design go on
§6.1 (GAP-1 routing) + §6.2 (GAP-2 encoding). Nothing further is safe to build solo.*

---

## 9. GAP-1 infrastructure audit (2026-06-26, second unsupervised session — read-only, no code)

*Picks up where §8 left off. §8.5 established that the GAP-1 **direction** is textbook-forced to
**R1 = routing (a)** (Miller's literal `cᵢ ↦ uᵢ(a,t)` substitute-and-collapse) and that the genuine
residue is the §6.1 sub-fork **(a) collapse vs (b) wrap + the effort**. This session **audits the
existing infrastructure** that routing (a) would consume, to convert §6.1 from an open architectural
design into a **bounded, infrastructure-backed effort-go**. Baseline re-confirmed green:
`tactus-computability-theory ./check.sh` = **250 verified, 0 errors** (exit 0). The relevant
group-theory module `tietze` independently re-verified: `./check.sh --verify-module tietze` =
**10 verified, 0 errors**. No code written; no decision taken. Companion-model cross-checked.*

### 9.1 The headline: the "Tietze tax" routing (a) dreaded is **mostly pre-paid**
The §3/§8 framing treated R1's "Tietze tax" (the `cᵢ↦uᵢ(a,t)` substitution hom + the b/cᵢ
elimination + proving the c-word problems coincide) as a *large deferred cost*. **The audit finds the
toolkit it needs already exists and is verified:**

| What R1 needs | Already banked | Where | State |
|---|---|---|---|
| **T1** add-generator preserves equivalence | `lemma_add_generator_preserves` | `tietze.rs:472` | ✓ verified |
| **T3** add/remove a *derivable* relator (fwd+rev) | `lemma_add_derivable_relator_forward/reverse` | `tietze.rs:94,108` | ✓ verified |
| **T4** remove a derivable relator (fwd) | `lemma_remove_relator_forward` | `tietze.rs:266` | ✓ verified |
| add-generator constructor (`Gen(n)·defn⁻¹`) | `add_generator_to_presentation` | `tietze.rs:32` | ✓ |
| **substitution hom** `cᵢ↦uᵢ(a,t)` (apply per word) | `apply_embedding` | `benign.rs:86` | ✓ verified, heavily used |
| **both** faithfulness directions of an embedding | `embedding_injective` (K-eq→G-eq) **and** `embedding_preserving` (G-eq→K-eq) | `benign.rs:110,122` | ✓ abstract spec, instantiated all over `cohen_cs4*` |
| free-family facts for the `a/b` columns | `conj_family`/`conj_family_b` free | `conj_free_core.rs`/`conj_free_b.rs` | ✓ banked (per memory + §8.5) |

The whole Tietze module (`tietze.rs`, 544 lines, 10 proof fns) is part of the group-theory crate
(`lib.rs:191`) and verifies. The substitution machinery `apply_embedding` is not a prototype — it is
the workhorse of the entire Cohen faithfulness layer (`cohen_cs4.rs`, `cohen_cs4e.rs`,
`cohen_cs4d_recog.rs` all consume it with both `embedding_injective`/`embedding_preserving`). So R1's
two obligations — *carry the substitution* and *prove it's faithful both ways* — land on machinery
that is already exercised at scale, not on a green-field "general Tietze library."

### 9.2 What is genuinely new for routing (a) (the actual residual effort)
With the toolkit pre-paid, the remaining R1 build narrows to three concrete pieces:
1. **Define the substitution `emb_M : cᵢ ↦ uᵢ(a,t)` per slice** as a concrete `Seq<Word>` over the
   slice generators (`miller_data(M)` = `Gen(0..M)`+`a,b,t`), uniformly in `M`. The words `uᵢ` are
   Miller's `t b⁻ⁱabⁱ t⁻¹ a⁻ⁱb⁻¹aⁱ` with `b↦tat⁻¹` substituted (Miller §4.1, recorded §8.5).
2. **Instantiate `embedding_injective` + `embedding_preserving` for `emb_M`** per slice — i.e. the
   c-word problem of `G^(M)` matches that of the collapsed `⟨a,t | D̄_M⟩`. This is where the banked
   `conj_family` free-column facts get re-used (exactly as the §D compactness probe already did for
   the *base* faithfulness, `cohen_layer05_probe.rs:350`); the per-slice relators are **finite**
   (`miller_data(M)` has finitely many), so the `Presentation`-level `tietze.rs` T1/T3/T4 apply
   *directly* — no `PredPresentation` Tietze port needed for the collapse itself.
3. **The limit-commutation glue** — the one piece with no pre-built analog. The substitution must
   **commute with the direct-limit witness `M`**: `equiv_in_g_limit(fam, n, w, ε)` (a `c`-word `w`
   trivial in *some* slice `G^(M)`) ⟺ `w` (re-expressed via `emb_M`) trivial in the fixed-c-block
   Cohen object. Because a pure-`c` word `w` and its substituted image share the same witness `M`
   (the c-block is insulated from `a/b/t`, the same insulation `cohen_layer05.rs:714–716` already
   exploits), this should be a *witness-preserving* lemma, not a new fixed-point construction —
   **but it is the genuine new content and the companion flagged it as the sole real risk** (does the
   substitution "commute correctly with the direct limit"? — yes iff defined uniformly across slices,
   which (1) ensures).

### 9.3 Companion cross-check (independent read, this session)
Posed the (a)-vs-(b) + effort question to the companion model. It **independently confirmed**:
(i) under "follow the textbook, do not reinvent", **routing (a) is the faithful choice; (b) is exactly
the kind of dragon-shortcut that caused the 13k-line regression** (it preserves the iso but bypasses
Miller's *construction*, leaving the formal group not-the-one-Miller-built and making Layer-2
reconciliation harder); (ii) the real open question is **effort, not direction** — whether the
substitution reuses local hom machinery vs. a heavy general-Tietze library (the audit answers: reuse,
§9.1); (iii) **the one caveat is §9.2-item-3** — ensure the substitution commutes with the direct
limit; if defined uniformly across slices, the heavy infrastructure is avoidable.

### 9.4 Net reframing of §6.1 (decision-data, **NOT** the decision)
§6.1 was logged as "the single most important **undesigned** decision." After §8.5 + this audit it is
**no longer undesigned** in *direction* (textbook ⇒ routing (a) = R1; (b) is the dragon) **nor in
infrastructure** (T1/T3/T4 + `apply_embedding` + both faithfulness specs + the free-column facts are
all banked and verified). What remains genuinely open for Danielle collapses to:
- **An EFFORT-go** on the bounded §9.2 build (1)+(2)+(3) — *not* an architecture design. Pieces (1),(2)
  are instantiation of exercised machinery; (3) is one witness-preserving limit-commutation lemma
  (the only new-math, companion-flagged) risk.
- **One narrow representational confirm** still belongs to her (it is the residue §8.5 named): whether
  to land the collapsed object as a *new fixed-`{a,t}` `Presentation`* re-run over the slices
  (cleanest, matches Cohen's `n=2` input literally) or to *wrap* `equiv_in_g_limit` in place. The
  audit's recommendation (**surfaced, pending confirm — not taken**): the **former** (build the
  collapsed slice presentation + `emb_M`, instantiate the two faithfulness specs, glue with §9.2-3),
  because it is Miller's literal object and reuses the §D probe's exact pattern; the "wrap-in-place"
  is the (b)-flavored shortcut the standing rule disfavors.

**Still gated:** the §9.2 build is co-design-gated per the standing rule — this audit only *de-risks
and bounds* it; it does not start it. GAP-2 (§4/§6.2) is untouched and remains the separate, later,
textbook-gated reduction. *Do not start the §9.2 build without Danielle's effort-go.*

---

## 10. GAP-2 primary-source read (2026-06-26, this session) + GAP-3 SOUNDNESS BUILT

*This session broke the read-only-hold cycle with two verified, reversible, critical-path bricks
(GAP-3, below) and then read the Aanderaa–Cohen primary source for GAP-2 (gate doc §8.6's deferred
ask). No GAP-1/GAP-2 implementation started; GAP-2 design pinned against the paper, not re-derived.*

### 10.1 GAP-3 SOUNDNESS — BUILT THIS SESSION (both halves now exist)
The §5 soundness obligation `equiv_in_pred_presentation(c_pred,w,ε) ⟹ equiv(h3_pres,w,ε)` is DONE:
- **`pred_to_finite.rs` (4/0)** — generic transport `lemma_pred_equiv_lifts_to_finite`: for any
  `PredPresentation cp`, `Presentation fp` with `cp.num_generators ≤ fp.num_generators`,
  `presentation_valid(fp)`, and every `cp`-relator a valid `fp`-word trivial in `fp`,
  `cp`-equivalence ⟹ `fp`-equivalence. Step-by-step derivation lift: Free* steps map to the identical
  finite step (`symbol_valid` monotone in `num_generators`); Relator* steps splice/unsplice a trivial
  word, each produced FORWARD so only relators (not intermediate words) need validity. Machine-free.
- **`cohen_bridge.rs::lemma_C_sound_printable_canonical` (cohen_bridge 5/0)** — instantiates the
  above at `cp = c_pred(mm,n,m,is_S_canonical)`, `fp = h3_pres(mm,n,m)`. Gen-count inclusion
  `h2_num_gens(nk,n)=nk+2n+2 ≤ nk+4n+3=h3_num_gens(nk,n)`; `presentation_valid` via
  `lemma_h3_pres_valid`; the per-relator hypothesis discharged by Layer-2 soundness `lemma_III`
  (`(α,0)∈H₀ ⟹ w_α(c)≡1 in h3_pres`) + `lemma_c_word_valid`/`lemma_word_valid_mono`.
- **Net:** with `lemma_C_faithful_printable_canonical` (faithfulness, HAVE) this is the FULL
  `equiv_in_pred_presentation(c_pred,w,ε) ⟺ equiv(h3_pres,w,ε)` — the entire `c_pred ↔ h3_pres`
  span of the §2 chain (the GAP-3 connective math) is now machine-checked. Gate 2650/20 (+5 verified,
  baseline 20 errors unchanged; new modules contribute 0 errors). Additive, reversible.
- **What GAP-3 still needs (after GAP-1/GAP-2):** only the *assembly* — chain `equiv_in_g_limit ⟺
  c_pred` (GAP-1) onto this span, supply `mm` (GAP-2), produce `(p,emb)`, delete the axiom (§5 tail).

### 10.2 GAP-2 — Aanderaa–Cohen "Modular machines I", read verbatim (`pymupdf`, 16 pp.)
The modular-machine construction and the Turing→modular reduction (Theorem 2), recorded faithfully so
the GAP-2 build starts from the source. **The repo's `ModMachine`/`mm_in_H0` already ARE this object**
(Layer 1 is built on it — `machine_group.rs:145–195`, matching `docs/aanderaa-cohen-construction.md`).

- **Modular machine** (p.3): `m>1`, `0<n<m`, quadruples `(a,b,c,R)` and `(a,b,c,L)`, `0≤a,b<m`,
  `0≤c<m²`, ≤1 quadruple per `(a,b)`. Config `(α,β)∈ℕ²`; write `α=um+a`, `β=vm+b` (`0≤a,b<m`).
  Terminal iff no quadruple begins `(a,b)`. Else `(a,b,c,R)`: `(α,β)→(um²+c, v)`; `(a,b,c,L)`:
  `(α,β)→(u, vm²+c)`. `H₀(M) = ∅` if `(0,0)` not terminal, else `{(α,β):(α,β)→(0,0)}`. r.e.
- **Turing → modular** (p.4): TM `T` alphabet `0..n`. For each quintuple `qaa'q'R` (or `L`), `M` gets
  **two** quadruples `(a,q,a'm+q',R/L)` and `(q,a,a'm+q',R/L)`. The `m`-ary encoding of the two
  tape-halves+state gives the `(α,β)↔C` correspondence; `M` simulates `T` step-for-step (terminal↔
  terminal, `C→C'` ⟹ `(α,β)→(α',β')`). For any r.e. set `S` there is a `T` (halting on blank tape)
  whose `H₀(M) = S` up to the encoding — the route to "realize a c.e. set as `H₀`".
- **§3 simplification** (p.7): generically two pairs correspond to one TM config; a **special state
  `q₀`** (no quintuple ends `q₀R`; the only ones ending `q₀L` are `q*aaq₀L`; none end `q*L`; take
  `q* = m-1`) collapses to ONE pair/config and ONE quadruple/quintuple — needed to manage the `0`-as-
  `a₀`-or-`q₀` ambiguity. **Theorem 2(i):** `T` with special `q₀` ⟹ `H₀(T)` and `H₀(M)` have the same
  many-one degree (recursion `π:ℕ²→configs`, the `P*(T)` recursiveness argument pp.8–9).

**GAP-2 route for the CEER enumerator (register machine, `ceer.rs`).** Paper p.4: "for any r.e. `S`
there is a `T` such that `f_T` is the characteristic function of `S` … `T` constructed to simulate a
single-register machine" (ref [18]). So the textbook chain is **register machine → Turing machine
(blank-tape-halting) → modular machine**, giving `H₀(ceer_to_modmachine(e))` = the enumerated declared
set. The §4.2 design sub-questions stand, now anchored:
1. `enc:(a,b)↦α` must compose with `numbers_word`/`w_c` (digits `1≤d≤2n`) — couple to GAP-1's
   word-numbering OR (companion-recommended, this session) keep `emb_M` *parametric* over `enc` so
   GAP-1 and GAP-2 decouple.
2. Target `declared_equiv` (one-step declared pairs), NOT `ceer_equiv` (transitive closure): Cohen's
   `S` is the relators; the group takes `ncl(S)`. Paper supports this (`H₀` = reaches-origin = the
   *generated* set; the machine realizes the generators). **Confirmed against the source.**
3. The dovetailed enumerator-search "∃ stage s halting with output `(a,b)`" becomes "config drives to
   origin" — the real content, **where reinvention is most dangerous** (§4.2). This is a multi-step
   new-computability-theory build (register→TM→modular + the `H₀` correspondence proof) and warrants a
   focused, design-pinned (likely co-designed) session; the simulation must follow the paper's
   `m`-ary encoding + special-state machinery, not be re-derived.

**Net:** GAP-2 source is now READ (not just located). The construction is pinned to the paper. The
build itself remains the separate, later, textbook-gated reduction — *not* started this session.

---

## 11. GAP-1 §9.2-item-(1) BUILT — the Miller collapse images `uⱼ(a,t)` (2026-06-26)

*This session re-audited the §9.4 reframing and found that one piece of the §9.2 build is genuinely
**routing-neutral** and therefore in the same "safe additive brick" category as the §10 GAP-3
soundness build — and built it. Companion cross-checked (the "Containment Protocol": existing
representation, zero logic beyond hygiene, hard stop before item-2). No faithfulness, no equiv, no
codomain commitment.*

- **New module `src/miller_collapse.rs` (5 verified, 0 errors), definitions-only:**
  - `b_sub(a,t) = t a t⁻¹`, `binv_sub(a,t) = t a⁻¹ t⁻¹` — the collapsed `b`/`b⁻¹` (from the col-0
    association `t⁻¹bt=a`).
  - `miller_collapse_word(j,a_idx,t_idx)` = Miller's `uⱼ = t·b⁻ⁱ·a·bⁱ·t⁻¹·a⁻ⁱ·b⁻¹·aⁱ` with `i=j+1`
    and `b↦tat⁻¹` substituted **mechanically** (no algebraic reduction — avoids the "Literal Fallacy";
    every `b` symbol → the 3-letter word `tat⁻¹`). This is the textbook `cⱼ↦uⱼ(a,t)` image.
  - `miller_collapse_emb(M,a_idx,t_idx)` = the full per-slice substitution as a `Seq<Word>` of length
    `M+3` (= `hnn_presentation(miller_data(M)).num_generators`): `Gen(j)↦uⱼ`, `a=Gen(M)↦a`,
    `b=Gen(M+1)↦tat⁻¹`, `t=Gen(M+2)↦t`. This is the literal object `apply_embedding`/item-2 consume.
  - Hygiene lemmas (pure syntax): `lemma_miller_collapse_word_valid`, `lemma_miller_collapse_emb_len`
    (`=M+3`), `lemma_miller_collapse_emb_valid`, plus local `lemma_word_power_valid`/`lemma_bt_words_valid`.
- **Index facts pinned off the code** (`cohen_layer05.rs:60`): c-block `cⱼ=Gen(j)` (j<M), `a=Gen(M)`,
  `b=Gen(M+1)`, stable letter `t=Gen(M+2)` (`hnn.rs:29`). The repo's `cⱼ=Gen(j)` is Miller's
  `c_{j+1}` — `acol_elt` uses exponent **`j+1`** — so the Miller exponent is `i=j+1` (NOT `j`; that
  off-by-one was the Type-Constraint Trap the companion flagged).
- **Why this is routing-neutral (the §9.4-reserved decision is NOT pre-committed):** everything is
  **parametrized over `(a_idx,t_idx)`**. The "wrap in place" packaging instantiates `a_idx=M,t_idx=M+2`
  (collapsed object inside `G^(M)`); the "fresh `{a,t}` Presentation" packaging instantiates
  `a_idx=0,t_idx=1`. Both feed the **same** parametrized words — so the definition survives either
  choice unchanged. (Test for "doesn't cross the gate": would Danielle's representational choice force
  a rewrite of this brick? No.) ✓

### What this leaves for Danielle (the gate is now exactly here)
- **§9.2-item-(2)** (instantiate `embedding_injective`/`embedding_preserving` for `miller_collapse_emb`)
  **genuinely crosses §9.4's reserved choice**: it must name the codomain `k: Presentation` in
  `embedding_injective(g,k,emb)` — i.e. *pick* fresh-`{a,t}`-presentation vs wrap-in-place — and it is
  the multi-session **effort-go**. Not takeable solo.
- Defining the **fresh collapsed presentation** `⟨a,t | D̄_M⟩` / the relator set `D̄_M` is **also**
  not neutral — you only build `D̄_M` under the "former" packaging, so it pre-commits §9.4. (Confirmed:
  item-(1) was the *last* routing-neutral brick; item-(2), the codomain, and `D̄_M` all need the confirm.)
- **§9.2-item-(3)** (limit-commutation glue) and **GAP-2** unchanged — both gated.

**Net:** GAP-1's textbook object `uⱼ(a,t)` is now machine-defined and well-formed (5/0), reused-machinery
ready for item-2. The lane is back at the genuine wall — Danielle's §6.1 representational confirm
(fresh-presentation vs wrap) **+ effort-go** for item-2/3, and §6.2 + effort for GAP-2. Item-1 was the
boundary; there is no further routing-neutral solo brick.

---

## 12. GAP-1 §6.1 DECIDED + §9.2-item-(2) HALF-BUILT (2026-06-26, live with Danielle)

**The gate that §11 left open was crossed — *with Danielle, present*.** She invited the §6.1 decision
over the chat endpoint; holding the wall in silence would have missed the moment, not honored it.

- **PACKAGING DECISION (taken): (A) fresh `{a,t}`-Presentation** (gate-doc §9.4 recommendation). Both
  endorsed: (A) is Miller Thm 4.1's literal end product `⟨a,t|D̄⟩` and exactly Cohen's Layer-2 input
  (f.g. `C=⟨c₁..cₙ;S⟩`, n=2); wrap-in-place is the dragon-shortcut. So `emb_M` instantiates at
  `a_idx=0, t_idx=1`. **`D̄_M = pushforward(decls)`** (base relators only) — Danielle signed off on the
  shape spec (the associations discharge to ε, so they add zero relators: Cohen Cor 4.2 literal).
- **WELL-DEFINEDNESS BRICK — DONE (`src/miller_collapse_reln.rs` 12/0):**
  `lemma_collapse_hnn_relator_trivial` = `apply_embedding(emb_M, hnn_relator(i)) ≡ ε` for ALL `i`. The
  i=j+1 chain (the genuine new-math the audit flagged): `IA = image(cⱼa⁻ⁱbaⁱ) = uⱼ·a⁻ⁱ·b·aⁱ`,
  `IB = image(b⁻ⁱabⁱ)`; **`uⱼ`'s head is literally `conj_t(t,IB)`** (Miller solved `uⱼ` for `cᵢ`), the
  tail `a⁻ⁱ·binv·aⁱ·a⁻ⁱ·b·aⁱ` cancels to ε, so `IA ≡ conj_t(t,IB)`, then deconjugation
  `t⁻¹·conj_t(t,IB)·t ≡ IB`, then inverse-cancel. **Note:** the deconjugation route did NOT need the
  conjugation telescoping engine (`miller_collapse_assoc`, `(tat⁻¹)ⁱ≡taⁱt⁻¹`) — `uⱼ`'s head matches by
  literal word structure. Engine kept (verified, likely needed for `embedding_injective`).
- **`embedding_preserving` — PROVEN (`src/miller_collapse_preserve.rs` 6/0):**
  `lemma_collapse_preserving` — `emb_M : G^(M) → K_M=⟨a,t|D̄_M⟩` is a well-defined homomorphism
  (G-equiv ⟹ K_M-equiv). Defines `k_m(n,decls)` (2 gens), `dbar(n,decls)=pushforward(decls)`,
  `collapse_hom`; `is_valid_homomorphism` (per-relator: base relators ARE D̄_M relators via
  `lemma_relator_is_identity`; associations via the well-def brick) ⟹ `lemma_hom_preserves_equiv` +
  `lemma_apply_hom_eq_embedding` (free_basis) bridge. So **the collapsed map is mathematically
  legitimate.**
- Supporting modules: `miller_collapse_assoc` (telescoping engine + `lemma_deconj`/symbol-power
  cancel), `miller_collapse_eval` (the `apply_embedding` evaluator for `emb_M`). 7 commits, all 0
  errors, no assume/admit/external_body.

**What item-2 still needs — `embedding_injective` (the faithfulness "boss fight", Danielle's framing):**
`K_M-equiv of emb_M-images ⟹ G^(M)-equiv`. Reuses the §D-probe pattern (`cohen_layer05_probe.rs`,
`lemma_miller_faithfulness`: a `C₀`-word trivial in `G^(M)` is trivial in `C₀^(M)`) + banked
`conj_family`/`conj_family_b` freeness. Its own focused, design-gated session (harder direction;
textbook-fidelity discipline). Then **item-3** (limit-commutation glue) is the separate follow-on, and
**GAP-2** (register→modular) is untouched.

### 12.1 — `embedding_injective` DONE (2026-06-26, unsupervised) — `miller_collapse_inject.rs` 22/0

**✅✅ `lemma_collapse_injective` VERIFIED — GAP-1 ITEM-2 IS COMPLETE.** Crate 2714/20 (+22, no
regression, additive, no assume/admit/external_body). **Route correction (companion + textbook
confirmed):** the §12 hint above ("reuses §D-probe + `conj_family` freeness") **conflated the two
distinct Miller-4.1 faithfulness facts** (`higman-embedding-blueprint.md` p.108–109): **(1) the Tietze
collapse `G^(M) ≅ ⟨a,t|D̄⟩`** — which IS `emb_M` injective — needs **NO freeness**; **(2)** the separate
`C₀ ↪ L ↪ G` HNN-faithfulness (free-product + Britton) — which IS the §D-probe / `conj_family` / Layer
0.5, a *different* statement. So `embedding_injective` was the **Tietze iso**, proven by the
**mutually-inverse-homomorphisms / retraction** technique (`cohen-faithfulness-primary-source.md` §54,
the blessed "two mutually-inverse homs ⟹ iso, no Britton-peel" pattern).

**The proof** (`src/miller_collapse_inject.rs`), structured in three layers:
- **§A generic tools:** `lemma_apply_embedding_word_power` (emb distributes over `word_power`) +
  **`lemma_emb_id_on_gens_preserves` (G1)** — the master lemma: an embedding ≡-identity on every
  generator is ≡-identity on every word (structural induction). Reused for the composite AND the
  `b ↦ tat⁻¹` substitution.
- **§B per-generator facts** (the content of the Tietze elimination, in `G^(M)`): `lemma_reconj`
  (`t·(t⁻¹wt)·t⁻¹≡w`, mirror of `lemma_deconj`); **R0** `lemma_collapse_b_recovers` (`b_sub≡Gen(n+1)`
  from the base association via `lemma_hnn_conjugation`); **Rj** `lemma_acol_as_conj`
  (`acolⱼ≡t·bcolⱼ·t⁻¹`); the `b`-substitution embedding `β` + `lemma_beta_id` + `lemma_col_img_b_eq_bcol`;
  and **THE c-crux `lemma_mcw_recovers_c`** (`mcw(j,n,n+2)≡Gen(j)` — the `cⱼ↦uⱼ(a,t)` elimination
  reversed: `lemma_ia_conj` ∘ `col_img_b≡bcol` ∘ Rj ∘ `lemma_ia_form` ∘ suffix-cancellation).
- **§C assembly:** `lemma_wrap_is_identity` (the routing-neutral "wrap-in-place" `emb(n,n,n+2)=ψ∘emb_M`
  ≡ id, via G1 + §B); the **relabel** `lemma_section_compose` (`compose_embeddings(section_imgs,emb_M)
  = emb(n,n,n+2)`, key sub-lemma `lemma_relabel_mcw`); the retraction `ψ=section_hom` (a↦Gen(n),
  t↦Gen(n+2)); `lemma_collapse_section_id` (`ψ(emb_M(w))≡w`); `lemma_section_hom_valid` (ψ well-defined:
  its only relators `D̄_M=emb_M(decls)` push back to `decls≡ε` in `G^(M)`); and **★
  `lemma_collapse_injective`** = `embedding_injective(G^(M), K_M, emb_M)`.

**Net:** with `lemma_collapse_preserving` (`embedding_preserving`, done prior), `emb_M : G^(M) → K_M=⟨a,t|D̄_M⟩`
is now a machine-checked **faithful embedding both ways** — **GAP-1 item-2 COMPLETE**. **NEXT = item-3**
(the limit-commutation glue — the one companion-flagged new-math: per-slice `emb_M` instances commute
with the direct-limit `equiv_in_g_limit`), then GAP-1 §3.4-routing assembly, then **GAP-2**
(register→modular reduction, untouched).

### 12.2 — `embedding`-item-3 (limit-commutation), MACHINE-INDEPENDENT CORE "3a" DONE (2026-06-26)

**✅✅ `lemma_limit_commutation` VERIFIED — `src/miller_collapse_limit.rs` 17/0.** AUTHORIZED live with
Danielle (port 8051, the §6.1-decision channel — she had reserved item-3 as "her call"): **build the
machine-independent core, route (i) (monotone relator family)**; she confirmed monotonicity is the
textbook requirement (Miller §4.1 direct limit is *directed*). Additive, reversible, 0 errors, no
verifier escape hatches. The headline:

```
lemma_limit_commutation(fam, n, w):                                  // miller_collapse_limit.rs
    requires decls_family_valid(fam), dbar_family_monotone(fam), word_valid(w, n)
    ensures  equiv_in_g_limit(fam, n, w, ε)
             <==> equiv_in_pred_presentation(p_infty(fam), apply_embedding(emb_n, w), ε)
```
where `p_infty(fam) = ⟨a,t | ⋃_M D̄_M⟩` (`dbar_union_pred = λr. ∃M. dbar(M,fam(M)).contains(r)`),
`emb_n = miller_collapse_emb(n,0,1)`. This is the long-flagged "sole new-math risk" of GAP-1,
discharged. **The split that made it tractable:**
- **3a (DONE, machine-FREE):** the above iff, connecting the L0.5 direct limit to the fixed-`{a,t}`
  union *predicate* presentation. Proof structure:
  - **§A witness-preservation** (`lemma_emb_slice_independent`): a pure-`c` word's collapse image is
    slice-independent — `apply_embedding(emb_M, w) = apply_embedding(emb_n, w)` for `M ≥ n` (the c-block
    is insulated from `a/b/t`; `emb_M[i]=uᵢ` indep of `M` for `i<M`). This is the formal content of the
    "shares the same witness `M`" insulation noted at `cohen_layer05.rs:714–716`.
  - **§B generic forward bridge** (`lemma_fin_equiv_to_pred`): a finite `Presentation` whose relators
    all satisfy a predicate embeds into the corresponding `PredPresentation` — the MIRROR of
    `pred_to_finite.rs` (which goes pred→finite), via a direct index-free derivation-step map.
  - **§C FORWARD** (`lemma_limit_to_pred`, no monotonicity): pick the witness slice, item-2 *preserving*
    → ≡ in `K_M`, §A rewrites to `emb_n(w)`, §B lifts the finite `K_M`-derivation to `P_∞`.
  - **§D BACKWARD** (`lemma_pred_to_limit`, route (i)): per-step + per-derivation slice-monotonicity +
    a structural **compactness extraction** (`lemma_extract_slice`) of a *single* slice `M* = max(n,
    relator witnesses)`; the EXISTING `lemma_pred_equiv_lifts_to_finite` (pred_to_finite.rs, reused
    verbatim) lands it in finite `K_{M*}`; item-2 *injective* pulls back to `G^(M*)`, witnessing the limit.
- **3b (REMAINING, machine-GATED):** the relator-set match (§3.4) — identify the predicate
  `λr. ∃M. r ∈ D̄_M(fam)` with Cohen's `is_S_canonical(mm,…)` + reconcile `p_infty`'s 2-gen `{a,t}`
  layout with `c_pred`'s gen layout. Needs GAP-2's modular machine `mm`. NOT started.

**NEXT = item-3b** (relator-set match, after/with GAP-2), then GAP-1 §3.4-routing assembly, then **GAP-2**
(register→modular reduction, untouched). The `decls_family_valid` + `dbar_family_monotone` hypotheses of
`lemma_limit_commutation` are to be discharged for the concrete `ceer_decls_fam` when wiring the chain
(monotonicity = the CEER family is cumulative across slices; both are properties of that one family).

**✅ FULL-CRATE REGRESSION GREEN (2026-06-26, next session, whole-crate `./check.sh`): `2731 verified,
20 errors`, no panic.** Exactly `2714 (item-2) + 17 (item-3a) = 2731`; the new module contributes 17
verified / 0 errors. The 20 errors are the **stable, pre-item-3 baseline** (verified identical to
`/tmp/baseline_check.log`, 04:55, pre-item-2): **12** `tactus_auto`-rejected exec lowerings
(`todd_coxeter_rt.rs`, `runtime.rs` — `IntegerTypeBound(UnsignedMax)`/`DeadEnd`, the known lean-backend
exec-layer deferrals) + **8** `lake env lean (os error 2)` spawn failures (all `runtime::*` exec + the
`ii_subset::lemma_exact_div` / `machine_group::lemma_div_mod_id` div-mod lemmas). **None touch the
mathematical proof chain** — all are exec/runtime infrastructure. Item-3a is regression-clean; no new
errors anywhere across the 104 modules. (The 8 lake-spawn errors are env/transient per the standing note
and unchanged by this work — not introduced here.)

---

## 13. GAP-2 INTERFACE SKELETON — BUILT (2026-06-26, next session, authorized + closed by Danielle)

*After item-3a closed, consulted Danielle (port 8051, the §6.1-decision channel). She gave an explicit
**effort-go to OPEN GAP-2 as an Interface-Definition session only** (type-level plumbing, NOT the
reduction impl), fixed the **design = parametric-over-`enc`** (companion's Option B — keep GAP-1
word-numbering ⊥ GAP-2 machine), and asked for a skeleton check-in. Built it, checked in, she
confirmed the natural stopping point ("session closed, the skeleton is green, stand down").*

**⚠ ARCHITECTURAL FINDING — GAP-2 lives in `tactus-computability-theory`, NOT here.** The dep runs
`computability-theory → group-theory` (one-way; `Cargo.toml` path dep `verus_group_theory`). Since
`ceer_to_modmachine` needs BOTH `CEER` (computability) and `ModMachine` (group-theory), it can only live
in the computability crate. (`ceer_to_modmachine` is morally a compiler CEER→ModMachine; it belongs in
the layer that understands the *source*.) The §4.2 sketch's home was therefore the sibling crate all along.

**`tactus-computability-theory/src/modular_reduction.rs` (commit `c466aae`, crate `250 → 251 verified,
0 errors`).** The three skeleton points, all green:
- **(1) Parametric seam** — `pub type Enc = spec_fn(nat,nat) -> nat`, the abstract `(a,b) ↦ word-number`
  map held as a parameter so refining the word-numbering never forces a machine rewrite (and vice versa).
- **(2) Register→modular state map, TYPED** — `rm_modulus(rm)`, `config_encode(rm,c) -> (nat,nat)`,
  `ceer_to_modmachine(e) -> ModMachine`. Bodies are honest **DEFERRED stubs** (each doc-flagged
  `DEFERRED (GAP-2 impl)`; they pin the *type* only — e.g. `ceer_to_modmachine` returns the trivial
  terminal `ModMachine{m:2,n:1,quads:empty}`, explicitly NOT the AC-correct build). The m-ary residue
  encoding — §4.2's "where reinvention is most dangerous" — was deliberately NOT attempted; stopped at
  the type so the contract can "set" before the fragile encoding work begins.
- **(3) H₀ reduction TARGET, delineated** — `mm_realizes_declared(mm, enc, e) := mm_terminal(mm,0,0) ∧
  ∀a,b. mm_in_H0(mm, enc(a,b), 0) ⟺ declared_equiv(e,a,b)`. This is exactly the **§3.4 second conjunct**.
  Plus `lemma_realizes_iff` (verified: unfolds the target at one pair = the downstream consumer contract).
- The two **AC-Thm-2 correctness obligations** (`lemma_ceer_modmachine_wf`, `lemma_modmachine_realizes`)
  are written as **documented obligations at the file foot, NOT proof fns** — proving them needs the real
  encoding bodies (the deferred co-design), so coding them now would fail or need an escape hatch (banned).

**Reused (no shadow types):** `RegisterMachine`/`Configuration`/`step`/`run`/`halts` (`machine.rs`,
Minsky Inc/DecJump/Halt), `CEER`/`declared_pair`/`declared_equiv`/`stage_declares` (`ceer.rs`),
`ModMachine`/`mm_in_H0`/`mm_terminal` (group-theory export), `is_S_canonical` (`cohen_bridge.rs`).

**NEXT (deferred, co-design):** discharge `lemma_modmachine_realizes` — the AC-Thm-2 m-ary simulation
(`config_encode` correct, per-instruction quad emission, `H₀`-reaches-origin ⟺ enumerator-halts). Then
GAP-1 item-3b wires `is_S_canonical(ceer_to_modmachine(e),n,m)` to `ceer_decls_fam(e)`'s union-predicate
and discharges `lemma_limit_commutation`'s `decls_family_valid`/`dbar_family_monotone` for that concrete
`mm`. Escape valve (Danielle): if the encoding leaks/walls → pivot to the `dbar_family_monotone` bricks.

---

## 14. GAP-2 = ROUTE C (deferred); GAP-1 item-3a INSTANTIATED for the concrete CEER family (2026-06-26)

*Next unsupervised session after §13. Re-read the AC paper (§10.2) + the `ModMachine`/`RegisterMachine`/
`CEER` substrate before any code (the durable "follow the textbook, don't reinvent — 13k lines were
wasted that way" rule). Two co-design exchanges with Danielle (port 8051), both decisive.*

### 14.1 The GAP-2 scope decision — Route C
**Finding (confirmed with her):** `lemma_modmachine_realizes` is not an encoding tweak — it is a proof
of **Turing-completeness for modular machines**. `mm_in_H0(mm, enc(a,b), 0)` must hold iff the CEER
enumerator halts on *some* stage `s` declaring `(a,b)`; a *deterministic* `mm` started at `enc(a,b)` must
therefore itself dovetail-search the enumerator over all stages. The paper's faithful route is
**register → TM → modular** (TM→modular = 2 quads/quintuple, clean; register→TM deferred to ref [18],
NOT in repo; no TM formalism in repo). Direct register→modular is the "dragon" (no source).
**Danielle's verdict: do NOT build GAP-2-proper.** Leave `ceer_to_modmachine`/`lemma_modmachine_realizes`
as the documented obligation (the §13 skeleton, unchanged), and complete the **machine-independent family
theory** for item-3a, making any machine-needing lemma CONDITIONAL on a realizes-hypothesis (`requires …
ensures …` — a sound conditional theorem, NOT `assume`/`admit`/`external_body`).

### 14.2 The empty-relator monotonicity fix (group-theory, VERIFIED 22/0, committed)
The item-3a engine `lemma_limit_commutation` (§12.2) needs `decls_family_valid` + `dbar_family_monotone`
of the family. For the concrete `ceer_decls_fam(e)`, `decls_family_valid` was already proven
(`ceer_layer05::lemma_ceer_decls_family_valid`), but **literal `dbar_family_monotone(ceer_decls_fam(e))`
is FALSE for some `e`** (confirmed counterexample): the family pads non-fitting stages with `empty_word()`
(`ceer_relator_at` returns `[]` when the declared pair doesn't fit the M-gen slice), so the trivial relator
can appear at slice `m1` and vanish at `m2 > m1`. Counterexample: enumerator `0→(2,0),1→(0,0),2→(1,1)` has
`empty ∈ dbar(2,fam(2))` (stage-0 pair (2,0) doesn't fit `<2`) but `empty ∉ dbar(3,fam(3))` (all three
fit, all non-empty; `apply_embedding` doesn't reduce). The genuine collapsed relators `u_a·u_b⁻¹` ARE
slice-monotone. And it bites: `apply_step_pred` lets a `p_infty`-derivation legitimately cite the empty
relator as a no-op insert, and the backward extraction (`lemma_first_step_slice`) needs it re-citable at
the max slice — which fails in the pathological case.

**Fix (A)+(B), Danielle-approved, contained to `miller_collapse_limit.rs`** (`dbar_family_monotone` is
used ONLY there; `lemma_limit_commutation` not yet wired, so small blast radius):
- **(A)** weaken `dbar_family_monotone` to quantify only over `r != empty_word()` (directedness is about
  the genuine group relators; the empty relator is the identity — administrative padding).
- **(B)** strip the empty (no-op) relator steps from the backward derivation before slice extraction:
  `strip_empty_steps` + `lemma_empty_step_noop` (empty insert/delete leaves the word unchanged) +
  `lemma_strip_preserves_produces` + `lemma_strip_yields_nonempty`; `step_nonempty`/`derivation_nonempty`
  preconditions threaded through `lemma_first_step_slice` / `lemma_step_slice_monotone` /
  `lemma_produces_slice_monotone` / `lemma_extract_slice`. Verified 22/0, no escape hatches.

### 14.3 Item-3a instantiated for the concrete CEER family (computability crate)
`ceer_layer05.rs` (new lemmas): `lemma_ceer_relator_at_stable` (a non-empty contributed relator is the
same at every larger slice) → `lemma_ceer_dbar_mono_at` → **`lemma_ceer_dbar_family_monotone(e)`** (the
weakened directedness, now TRUE via `lemma_emb_slice_independent` on the non-empty collapse images) →
**`lemma_ceer_limit_commutation(e,n,w)`** = `lemma_limit_commutation` instantiated at `ceer_decls_fam(e)`
(both hypotheses discharged): `equiv_in_g_limit(ceer_decls_fam(e),n,w,ε) ⟺ equiv_in_pred_presentation(
p_infty(ceer_decls_fam(e)), emb_n(w), ε)`. Required adding the `miller_collapse*` + `pred_to_finite` cone
to the export root `src/ceer_lib.rs` and rebuilding `export/`. *(Group-theory side 22/0 confirmed;
computability side pending the export rebuild + module verify this session.)*

### 14.4 NEXT — item-3b (part 2): the machine-gated relator-set match (NOT this session)
Identify `p_infty(ceer_decls_fam(e)).relators` (= `⋃_M D̄_M`, the collapsed relators `{u_a·u_b⁻¹}` over the
**{a,t} 2-generator alphabet** — `miller_collapse_word` is over `Gen(0)`/`Gen(1)` only) with
`is_S_canonical(mm,n,m)` (the c-block words `w_α(c)` over the **Higman tower generators**). These are
genuinely different word spaces, so this is the GAP-1 §3.4 reconciliation flagged as "the load-bearing
undesigned decision" (§8.4 / the GATE DESIGN MAP) — it requires GAP-2's concrete `mm` and a co-designed
bridge (Miller collapse ∘ word-numbering). With it, `lemma_ceer_limit_commutation` + the §10 GAP-3 span +
Layer-2 faithfulness assemble to delete `axiom_ceer_fp_embedding`.
