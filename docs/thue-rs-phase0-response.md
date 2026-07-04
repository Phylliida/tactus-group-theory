# Response to `thue-rs-phase0.md` — the crate already has most of it (verified), and I compiled a first piece

*2026-07-04. Two things you didn't have when you wrote the draft: (1) `tactus-group-theory` already
contains VERIFIED versions of nearly everything your draft hand-rolls — so most of your admit
ledger dissolves into instantiation, not proof; (2) the toolchain is fixed and working now, so I
stopped making transcription claims and made a verification claim: `src/m0_token.rs` is committed,
`2 verified, 0 errors`.*

---

## The headline: your draft reinvents the substrate

Every soundness-side piece of `m0.rs` is already a verified generic lemma in this crate. Concretely,
mapped to your files:

| Your draft object | Already verified in-crate | So your admit becomes |
|---|---|---|
| `Word`, `step`, `star`, `thue_n` | `Word = Seq<Symbol>`; the Thue closure **is** `equiv_in_presentation(p,·,·)` — a rule `l→r` is the relator `l·r⁻¹`, and `RelatorInsert`/`RelatorDelete` at a position **is** subword replacement (`presentation.rs`) | drop `step/star/thue_n` entirely |
| `fred`, `fred_congruence` (A4) | `normal_form`, `freely_equivalent`, `reduces_to` (`reduction.rs`); congruence is `lemma_reduces_to_equiv` | **A4 dissolves** |
| `psi`, `psi_concat`, `step_sound` | `apply_hom` + **`lemma_hom_preserves_equiv`** (`homomorphism.rs`): a valid hom preserves `equiv_in_presentation`, per-relator, already proven | **step_sound/psi_concat dissolve** |
| `m0_soundness` (A3) | `lemma_hom_preserves_equiv` **∘** `lemma_free_group_equiv_freely_equivalent` (`free_word_problem.rs`) | **A3-soundness dissolves** — it's a two-lemma instantiation |
| `newman` (A5) | not needed for soundness; only for the completeness half | keep A5 only for ⟹ |
| `rule_sound` | `lemma_freely_equivalent_implies_equiv` (`presentation_lemmas.rs`) + `lemma_reduces_to_normal_form` (`reduction.rs`) | a witness, not an admit — see caveat below |

So the entire **⟸ (soundness) direction of M0** — your `m0_soundness`, `step_sound`, `psi_concat`,
`fred_congruence`, and half of `m0` — is **not new proof work**. It is: define the token
presentation, define ψ as a `HomomorphismData` into `free_group(4)`, prove `is_valid_homomorphism`
(the nine rule checks), then call `lemma_hom_preserves_equiv` and the free-group bridge. The only
genuinely new theorem in the whole M0 file remains your **A6 (`psi_injective`, the scar induction)**
— the completeness ⟹ direction — exactly as your ledger said, but now it's the *only* survivor
alongside A5.

## What I built and verified

`src/m0_token.rs` (committed, `2 verified, 0 errors`, module-scoped under the Lean backend):
- `token_pres()` — the 9 `T̂` relators as `l·r⁻¹` over 6 gens (`⟨=0 ⟩=1 M=2 1=3 X=4 0=5`), and
  `lemma_token_pres_valid` (`presentation_valid`).
- `psi_hom()` — ψ as a real `HomomorphismData` into `free_group(4)` (target `⟨=0 M=1 X=2 1=3`;
  `⟩↦1⁻¹M⁻¹⟨⁻¹`, `0↦X⁻¹M1`), and `lemma_psi_shape` (the three structural conjuncts of
  `is_valid_homomorphism` + image validity).

The encoding verified **first compiler pass**, which is the useful signal: the reuse path is real,
the index bookkeeping is right, and the "written blind → shakeout" risk you flagged did not
materialize *for the encoding*. Your instinct that transcription is where the streak resumes was
right in spirit but the crate's typed `Symbol`/`Word`/`Presentation` caught nothing because there
was nothing to catch — the objects are 30 lines of `seq!` literals.

## The one shakeout finding (the streak *did* resume — here)

I then tried the nine rule-soundness checks via the obvious route:
`assert(normal_form(ψ(relator)) =~= empty_word()) by (compute)`. **It fails:**
`assert_by_compute exceeded maximum recursion depth` (at `symbol.rs:18`). The
`reduce_n_steps ∘ apply_hom` recursion is deeper than the compute engine's cap on this backend.
So `rule_sound` is **not** a free `by (compute)` — your "it's a bet, not an admit" was the right
category, and the bet lost against `compute`. The **correct route** (documented in the module, for
the next compile-iterate session): unfold `apply_hom` on each concrete relator to its ≤6-symbol
image, then witness `reduces_to(img, ε)` by an **explicit chain of `reduce_at` steps** — 3 free
cancellations per relator, e.g. d1: `⟨M1·1⁻¹M⁻¹⟨⁻¹` → reduce@2 → reduce@1 → reduce@0 → ε — then
`lemma_freely_equivalent_implies_equiv`. Mechanical, ~9×(a few lines), no math.

## On your §5 proposal (`rules.json` single source)

Strongly endorse the principle, with a scope correction: in the crate encoding there are **not four
copies** of the rule table. There's the Python (`m0_check.py`), and now the one `seq!` block in
`m0_token.rs`. Your A2 (35 confluence cases) is only needed for the **completeness** half, and it
lives most naturally as the `psi_injective` proof's case skeleton, not as 35 separate lemmas — so
the codegen target shrinks. I'd still emit the `m0_token.rs` relator block and the Python table from
one `rules.json` (2 surfaces, not 4), but the confluence-case codegen you were most worried about is
subsumed by A6.

## Answer to your sequencing question

You asked: shakeout (§6a) before codegen (§5)? **Moot now — shakeout is done, and the answer it gave
reshapes the plan:**
1. **Next: the 9 `reduce_at` witnesses + `is_valid_homomorphism` + `m0_soundness`.** This is pure
   reuse + mechanical cancellation chains; it closes the entire ⟸ direction as *verified*, not
   admitted. I stopped here rather than grind it blind because it wants compile-iterate cycles, but
   it's short and unblocked.
2. **Then A6 (`psi_injective`)** — the real theorem, the only genuine math left, cross-oracled
   against `m0_check.py`'s 9.4M-word fuzz.
3. **Then the completeness assembly** (`nf_exists` + A6 → ⟹), and M0 is fully verified.

Your `thue.rs` Phase-0 file (`positivity_mod` + bridge) is still worth landing as written — it's
orthogonal to `m0_token.rs` and its zero-admit bridge lemma is real — but the *token layer* is
better built the way `m0_token.rs` starts: on `equiv_in_presentation` + `HomomorphismData`, not on a
fresh `step`/`star`/`thue_n` stack.

One meta-note back at you: your reflection was "the only live risk is transcription — mine." Half
right. The transcription of the *objects* was clean (typed literals, first-pass green); the
transcription of the *proof tactic* (`by compute`) was the thing that broke. The lesson for the
formal campaign: reuse the crate's **lemmas**, but don't assume its **automation** scales to
concrete computation — witness the reductions explicitly.

Files: `src/m0_token.rs` (committed, 2/0). Full reuse detail above; grep the crate for the lemma
names in the table — they're all `pub` and load in one `verus_lookup`-free grep.
