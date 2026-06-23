# Brick 5 — Fork re-evaluation: the Fork-B engine has an UNDESIGNED CORE (2026-06-23)

Companion to `brick5-completeness-plan.md` (§2.3 Fork A/B decision) and `brick5-c4-plan.md`
(§7–§8 the route-A reframe). **Read this before writing any C3.2/C4 completeness code.** It records
a finding that changes the architecture and a recommendation that re-opens the Fork A/B decision.

> **STATUS: FINDING + RECOMMENDATION, pending real-Danielle confirmation.** This was reasoned out
> + co-designed against the Danielle endpoint-proxy in one session; it re-opens a fork that was
> originally decided WITH Danielle (2026-06-21), so the *decision to commit weeks to building the
> Fork-A foundation* should be confirmed with Danielle directly before the build starts. The
> *finding* (the engine core is undesigned) is machine-traced and solid; act on the finding (do NOT
> build the Fork-B engine), but treat the Fork-A build as proposed-not-committed.

---

## 1. The finding: the Fork-B "virtual-iso" engine core is a theoretical void, not an implementation gap

The completeness arc (C3.2 a-levels + C4 k-level) was reframed (sessions 7–9, `brick5-c4-plan.md`
§7–§8) to a **word-restricted / virtual-iso** engine after the universal a-level iso
(`hnn_associations_isomorphic(phi_l_data)`) was proven **vacuous** — its side condition
`sigma_sat_upto` is UNSATISFIABLE for finite `alphas` (machine-checked,
`lemma_sigma_sat_upto_unsatisfiable`, `phi_l_iso_unsat.rs`). The route-A plan (§8) was: peel a FIXED
`w` by Britton, invoking the iso only at the pinch-middles that arise, with indices bounded by
`sigma_orbit(L₀,m,n,2n)` (finite). Danielle's "virtual iso" framing (`brick5-completeness-plan.md`
§2.3 end): replace `hnn_associations_isomorphic(data)` with a per-pinch "iso-holds-in-the-quotient"
membership obligation.

**The obstruction (machine-traced this session):** the iso is NOT consumed only at pinch-middles. The
two iso-consuming calls in the engine (`kp_pinch.rs::lemma_kp_property_ii_core`) are

- `britton_lemma_full(data, wgi)`            (line 1166) — raw-pinch-free `wgi` + trivial ⟹ stable-free;
- `britton_lemma_unconditional(data, wgi)`   (line 1200) — stable-free base word ≡ ε in HNN ⟹ ≡ ε in base.

**Both apply to a `wgi` that is already raw-pinch-free**, yet both still require the *universal* iso,
because the work they do routes through

```
britton_lemma_full / britton_lemma_unconditional
  → lemma_derivation_preserves_syls (britton_via_tower.rs:8636, requires the iso)
    → lemma_single_step_preserves_syls (8579, requires the iso)
```

and `lemma_single_step_preserves_syls` needs the association to be a genuine subgroup isomorphism *to
keep the syllable action well-defined under EACH relator-application step of an **arbitrary**
derivation of `wgi ≡ ε`*. The derivation is arbitrary — it can apply any HNN relator anywhere — so the
iso requirement is irreducibly the **universal `∀ww`** statement. It cannot be restricted to "the
pinch-middles of the fixed word `w`": the syllable-invariance argument quantifies over derivation
steps, not over the word's own pinches.

**Why "iso-in-the-quotient" does not rescue it.** Britton's Lemma reduces HNN-equivalence to
base-equivalence **plus a genuine isomorphism of the associated subgroups IN THE BASE**. An iso that
holds only in the quotient `h3_pres` (i.e. *after* the k-relators are applied) is exactly the k-relator
itself (`k` conjugates `A₊` to `A₋`); feeding it into a Britton argument *about* `h3_pres` is circular
— it uses the conclusion of Britton's Lemma to discharge its premise. So the Fork-B engine would
require a genuinely **new "virtual Britton's Lemma"** (HNN faithfulness from a quotient-iso), which is a
research-level proof-theory problem, not a coding task. **There is no extant sketch of this core.**

This is the deeper root cause beneath the session-7/8/9 vacuity discoveries: the σ-saturation
unsatisfiability is a *symptom*; the disease is that a finite presentation cannot carry the iso the
Britton machinery structurally demands, and the planned "virtual iso" substitute does not type-check
against how Britton actually consumes the iso.

---

## 2. The cost calculus has shifted since the Fork-B decision (2026-06-21)

When Fork B was chosen (`brick5-completeness-plan.md` §2.3), the case was: **"surgical strike — one
k-level, avoid the predicate-relator refactor cascade."** Two post-decision findings invalidate that
case:

1. **The a-levels are ALSO virtual** (§2.2bis correction + sessions 7–9). So Fork B now needs the same
   (undesigned) virtual-iso engine at **all `2n+1` tower levels**, not one. The "surgical / single
   level" appeal is gone.
2. **The engine core is undesigned** (§1 above). Fork B is no longer "a `tower_peel`-scale arc + two new
   non-iso Britton variants"; it is "invent virtual Britton's Lemma," open-ended.

Meanwhile **Fork A's cost is infrastructure we need for Layer 0.5 ANYWAY.** Layer 0.5 is blocked on
exactly the same wall: the CEER group `C = ⟨c_i | S⟩` is infinitely generated (and `S` is an infinite
r.e. relator set), but `Presentation { num_generators: nat, relators: Seq<Word> }` is finite by
construction (`docs/higman-embedding-blueprint.md` §"Build order" step 2; `AGENDA.md` §3.2). Both
frontiers are blocked by the **finite-presentation constraint**.

**Synthesis:** a predicate / countable presentation notion is the *common* foundation for both
frontiers. Build it once and it unblocks (a) Layer 0.5 (state `L = C ⋆ F₂` over infinitely many gens)
and (b) a **clean Fork-A C4** — carry `S` as a predicate so the k-level association iso is *genuine in
the base*, and standard Britton applies with no undesigned engine. This converts Fork A from "a cost we
avoided" into "a force multiplier we need regardless."

---

## 3. Recommendation (pending real-Danielle confirmation)

**Re-open Fork A: build a predicate / countable presentation foundation.** Proxy-Danielle endorsed
this strongly; the reasoning is sound and based on genuinely-new (post-2026-06-21) findings. But this
is a large undertaking that re-opens a real-co-designed decision, so confirm with Danielle before the
build, and scope it before committing.

**Proposed shape (to be confirmed/refined with Danielle):**

- A NEW parallel type, e.g.
  ```
  PredPresentation { num_generators: GenCount /* Finite(nat) | Countable */, relators: spec_fn(Word) -> bool }
  ```
  kept SEPARATE from the verified finite `Presentation` so the 12k-line finite tower
  (`britton_via_tower.rs`, `normal_form_afp_textbook.rs`, …) is untouched — no refactor cascade.
- Generalized `hnn_pred_extension`, a predicate `hnn_associations_isomorphic`, and a
  **`britton_pred_lemma`** taking the relator predicate as a first-class argument. **CAUTION:** a
  predicate Britton's Lemma over an infinite relator set is itself nontrivial — it is *not* obviously a
  mechanical generalization of the finite proof (Britton's syllable machinery is built on the relator
  structure). Scope this carefully; it may be the bulk of the work. Confirm feasibility before committing.
- Map C4 onto it: k-level base = `h3_upto(2n) + S` (S as predicate) ⟹ the ψ association iso is GENUINE
  in this base ⟹ standard (predicate) Britton peels `w_α(c)` ⟹ `in_C(w_α(c))`. No virtual-iso engine.
- Bridge Layer 0.5: the same predicate-relator logic represents `C` and `L = C ⋆ F₂`.

**Open scoping questions for the real co-design session:**
1. Is `PredPresentation` worth it vs. some lighter encoding (e.g. relators indexed by an r.e. predicate
   but materialized finitely per-derivation)? The full predicate-Britton may be avoidable if the only
   consumer is the k-level decode.
2. How hard is `britton_pred_lemma` really? If it is as hard as the Fork-B virtual engine, the pivot
   buys less than it appears (though it still unblocks Layer 0.5). Prototype the predicate-Britton
   statement + the iso-in-base discharge for the `S`-augmented base before sinking the full build.
3. Does the `S`-augmented base actually make the ψ iso provable in the base, or does it relocate the
   circularity? (It should be genuine: `S` kills exactly the `w_α(c)` witnesses that break the iso,
   §2.2 — but verify the iso's von-Dyck direction is dischargeable from the `S`-predicate + soundness +
   `lemma_theorem1` without re-introducing the universal-derivation problem.)

---

## 4. What is SOLID vs. what is PROPOSED

- **SOLID (machine-traced, act on it):** the Fork-B virtual-iso engine core is undesigned (§1). Do NOT
  attempt to build it / do NOT re-declare route-A "buildable." `lemma_phi_l_iso` /
  `lemma_h3_II_upto_faithful` remain vacuous (`sigma_sat_upto`-refuted); the R1–R4 directional pinch
  machinery is verified but its *packaging* into a tower-level faithfulness is blocked by §1.
- **PROPOSED (confirm with real Danielle before the build):** the Fork-A pivot + `PredPresentation`
  (§2–§3). High-confidence reasoning, proxy-endorsed, but a major re-opened fork — scope question #2
  (predicate-Britton difficulty) is the gating unknown.

**Net for the next session:** if Danielle confirms the pivot, the first concrete brick is the
`PredPresentation` type + a *prototype* `britton_pred_lemma` statement (signature only) + the
`S`-augmented k-base iso discharge sketch — enough to answer scoping question #2 before the full build.
The `{a⁻ⁱbaⁱ}`-free crux (`conj_free_core.rs` 34/0) is representation-independent and feeds straight
into the Layer-0.5 half once `PredPresentation` exists.
