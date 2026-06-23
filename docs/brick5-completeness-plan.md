# Brick 5 — COMPLETENESS: `C ↪ H₃` faithful

Companion to `brick5-plan.md` (soundness, DONE: `lemma_III`, `higman_consequences.rs` 60/0).
This doc is the completeness arc — the deep faithfulness direction of the Higman bridge. It
**corrects the target** stated in the soundness doc and surfaces two structural facts that change
the routing. Read this before writing any completeness code.

Source: Cohen, *Combinatorial Group Theory* §9.6, book p.279–281 (PDF 284–286; offset +5). Pages
read 2026-06-21.

---

## 1. The target was mis-stated. The correct target is faithfulness.

The soundness doc states the completeness goal as

> ~~`h3_pres ⊢ w_α(c) = 1  ⟹  (α,0) ∈ H₀(M)`~~      ← **imprecise; do not aim for this**

This conflates two different things:
- `w_α(c) ∈ S` — membership in the c.e. **set** `S`, which is `⟺ (α,0)∈H₀(M)` **by design of the
  machine `M`** (Cohen p.279: "when all the details are filled in … `w_α(c)∈S` iff `(α,0)∈H₀(M)`").
  This is the §3.3 *machine-to-S bridge*, NOT a group-theoretic theorem.
- `w_α(c) = 1` in `C = ⟨c ; S⟩` — i.e. `w_α(c) ∈ ncl(S)` (normal closure). Peeling `w_α(c)=1` down
  the HNN tower lands here, NOT at `S`-membership. `ncl(S) ∩ {numbered words} = S` is **not** true in
  general (C's word problem is only c.e., not decidable), so there is no group-theoretic route from
  `w_α(c)=1 in H₃` back to `(α,0)∈H₀` directly.

**Corrected target (the real content of Higman's theorem, confirmed with Danielle 2026-06-21):**

> **FAITHFULNESS:  `h3_pres ⊢ w_α(c) = 1  ⟹  C ⊢ w_α(c) = 1`**   (i.e. `C ↪ H₃` is injective on
> the c-generators; equivalently `w_α(c) ∈ ncl(S)`).

The `(α,0)∈H₀` connection lives entirely in (a) soundness — where it shows the relations *hold* —
and (b) the §3.3 machine bridge — where it *defines* `S`. It does **not** belong in the
group-theoretic faithfulness proof. The bridge biconditional we ultimately advertise,
`f(σ)=f(τ) in H₃ ⟺ ZFC⊢σ↔τ`, factors as:
`f=f in H₃ ⟺ f=f in C` (THIS arc, faithfulness) ∘ `f=f in C ⟺ ZFC-equiv` (§3.3 + Layer-0.5 CEER↪C).

---

## 2. Two structural facts that fix the routing

### 2.1 `S` is INFINITE ⟹ there is no literal "h3_with_S" Presentation

`S = { w_β(c) : β∈I, (β,0)∈H₀(M) }` is a **c.e. (infinite)** set of relators. A `Presentation` has a
`relators: Seq<Word>` — finite. So the soundness-doc's Route-A phrase "`h3_pres = h3_with_S` as
groups" can **not** be realized as an equality of two `Presentation` values, and the tempting first
move — "build the with-S tower `h1_base_S/h2_pres_S/h3_pres_S` and run `britton_lemma_unconditional`"
— is a **DEAD END**. (It is the natural instinct; this note exists to stop the next session burning a
day on it.)

`C = ⟨c ; S⟩` must be carried as a `spec_fn(Word)->bool` **predicate** (the Approach-(b) decision,
`docs/layer2-build-plan.md`), and the with-S analysis must use the **`kp_pinch` predicate engine**
(`kp_pinch.rs`, `lemma_property_ii`), which does pinch-by-pinch elimination against an abstract
`in_k: spec_fn(Word)->bool` — exactly the tool that does not need a finite relator list.

### 2.2 The ψ (k-level) association is NOT isomorphic in `h3_pres` — and that is the whole point

`britton_lemma_unconditional`/`britton_lemma_full` require `hnn_associations_isomorphic(data)`. For
the k-level `psi_data = HNNData{ base: h3_upto(2n), associations: psi_assoc }` this is **FALSE**, and
the refutation is exactly `w_α(c)`:

In the base `h3_upto(2n)` the c-generators are **free** (h1_base has the c's as free gens + only
`b_i c_j = c_j b_i`; the p- and a_i-HNNs never resolve c's). Take the abstract association-word `w`
that evaluates, on the A₊ side (`b_j↦b_j`), to `p⁻¹t_α p · (t_α w_α(b) d)⁻¹` for some `(α,0)∈H₀`.
- A₊ side `≡ ε` in the base — this is family (II), `p⁻¹t_α p ≡ t_α w_α(b) d`, which is **derivable in
  `h3_upto(2n)`** (it only uses p and the a_i's; cf. `lemma_II`, proven one level up but valid here).
- A₋ side (`b_j↦b_j c_j`) evaluates to `p⁻¹t_α p · (t_α w_α(bc) d)⁻¹ ≡ w_α(c)⁻¹` (mod the same II
  move), which is `≢ ε` because the c's are free and `w_α(c)` is a nonempty reduced c-word.

So `emb(A₊,w)≡ε` but `emb(A₋,w)≢ε`: `hnn_associations_isomorphic(psi_data)` fails, on precisely the
`w_α(c)` witnesses. **Adding `S` (which kills `w_α(c)` for `(α,0)∈H₀`) is exactly what repairs the
iso.** This is the mechanism of Higman's theorem, and it is why the predicate engine — which resolves
each pinch locally against the `S`-predicate, rather than demanding a global iso — is *mandatory*, not
a stylistic choice.

(The same analysis shows the φ_i / a_i levels *are* fine to Britton-peel directly — they only touch
`t,x,d,b_j` and use the residue facts; the c-entanglement is purely at the k-level.)

### 2.2bis CORRECTION (2026-06-21, w/ Danielle): the a-levels are ALSO non-iso over the literal base

The parenthetical above is **WRONG**, and so is C3's hope that "`hnn_associations_isomorphic(phi_l_data)`
holds *literally* over `h3_upto(l-1)`." It does **not**. The a-levels are just as "virtual" as the
k-level, for the *same* Approach-(b) reason (only finite set (I) in the literal base; the derived
families live one level up).

**The finding (proven, not conjectured).** Two steps:
- **Base-swap collapse.** IF `φ_1..φ_{l-1}` are isos, then by Britton base-faithfulness
  (`lemma_single_hnn_base_faithful`, applied down the a-tower) any word over `h2_pres`-generators is
  trivial in `h3_upto(l-1)` iff trivial in `h2_pres`. Since `a_words`/`b_words` use only `t,x,d,b_j,p`
  (all `h2_pres` gens; the `a_i` sit at higher indices), `emb(a,w)`/`emb(b,w)` are `h2_pres`-words, so
  **`φ_l` iso over `h3_upto(l-1)`  ⟺  `φ_l` iso over `h2_pres`.**
- **`φ_l` iso over `h2_pres` is FALSE.** Concrete witness at `l=1`: read the `p`-relator as
  association-letters, i.e. `w` with `emb(a,w) = p⁻¹ t p d⁻¹ t⁻¹` (≡ε in `h2_pres` — it *is* the
  set-(I) relator) and `emb(b,w) = p⁻¹ t_1 p (b_1 d)⁻¹ t_1⁻¹` with `t_1 = x⁻¹ t x`. In `h2_pres` the
  only `p`-association is `(t, td)`, so the associated subgroup is `⟨t⟩`; `p⁻¹ (x⁻¹ t x) p` is a
  genuine Britton pinch that does **not** reduce (`x⁻¹ t x ∉ ⟨t⟩`), so `emb(b,w) ≢ ε`. The iff fails:
  `φ_1` is non-iso over `h2_pres = h3_upto(0)`.

**Root cause.** Cohen's HNN-recognition of `A` (Prop 1.34) needs the *full* family (II)
`p⁻¹ t_α p = t_α w_α(b) d` (α∈I) as relations of the base — and Cohen's `H₂` *has* them by
definition (blueprint line 38). OUR `h2_pres` carries only the single `α=0` relation `p⁻¹tp=td`
(Approach (b)); family (II) is only **derivable** in the full tower (`lemma_IIa` conjugates by the
`a_i`, `lemma_II` assembles it in `h3_pres`). So the recognition simply isn't available at the
literal intermediate level. **C3-as-stated is a dead end — do not try to prove the literal a-level
iso.**

### 2.2ter THE REROUTE: finite family-(II) augmentation ("Local Fork A"), virtuality re-isolated to k

> **⚠ REFUTED 2026-06-22 (w/ Danielle, `brick5-c4-plan.md` §7).** The premise of this whole subsection —
> "a FINITE family-(II) augmentation `h3_II` makes the a-levels **literal** isos" — is **FALSE**. The
> a-level `hnn_associations_isomorphic` over a finite `h3_II` requires `σ_l(alphas) ⊆ alphas`
> (von-Dyck-backward needs `family_II_relator(m·β+l) ≡_base ε` for every β the base covers), which is
> forward-closure ⟹ **infinite**. Machine-checked: `lemma_sigma_sat_upto_unsatisfiable` (`phi_l_iso_unsat.rs`).
> A finite presentation cannot carry the full family (II), so the a-levels are virtual isos too — the
> SAME situation as the k-level. **C3.2 must be reframed to a word-restricted virtual iso (Fork B applied
> to the a-levels as well).** The `h3_II` *group-preservation* infra (C3.0/C3.1, `lemma_same_group_iff`,
> `lemma_h3_II_group_preserving`) and the R1–R4 directional Britton-peel machinery survive and are reused;
> only the universal-iso target is wrong. Read `brick5-c4-plan.md` §7 before continuing C3.2/C4.

The fix recovers the original "isolate the hard part to the k-level" plan **without** a uniform
virtual-iso tower engine (which would mean re-deriving all of `britton_via_tower` for virtual
associations — enormous). Instead, exploit that faithfulness is **per-α**: for a fixed `α`, `w_α(c)`
is a fixed finite word whose Britton analysis touches only **finitely many** family-(II) relators.

- **Augment with finite family (II).** Define a base `h3_II = h3_upto(2n) + [the finite list of
  family-(II) relators `p⁻¹ t_β p (t_β w_β(b) d)⁻¹` actually needed]`. This is a **finite
  `Presentation`**. Over `h3_II` the a-level associations become **literal isomorphisms** (the witness
  above now *reduces*: with the `β=1` relator present, `p⁻¹ t_1 p ≡ t_1 w_1(b) d = t_1 b_1 d`, so
  `emb(b,w) ≡ ε` — verified by hand against `lemma_II`/the numbering `w_1(b)=b_1`).
- **Group-preserving (the soundness swap).** Each family-(II) relator is a *consequence* of `h3_pres`
  (`lemma_II`, soundness), so `h3_II` and `h3_pres` are the **same group**:
  `equiv_in_presentation(h3_pres, w, ε) ⟺ equiv_in_presentation(h3_II, w, ε)`. (⟸: `h3_II` has
  more relators, all derivable in `h3_pres` ⟹ use the *reflecting* base-swap lemma below. ⟹: `h3_II`
  extends `h3_pres`'s relators ⟹ `lemma_add_relators_preserves_equiv`.) So we may run the engine over
  `h3_II` and transport the conclusion back to `h3_pres`.
- **Virtuality re-isolated to the k-level.** Over `h3_II` the a-levels are clean ⟹ they
  **Britton-peel directly** with the existing `britton_lemma_unconditional` (no new engine). The
  k-level still fails (S absent, c's free) ⟹ the **single** Fork-B virtual-iso descent (in_C
  licensed) — exactly the size originally budgeted. NET: C3 reduces to "the b-augmented a-level
  recognition **over `h3_II`**" (literal, residue-fact-driven, `tower_peel`-scale but standard), and
  C4 reverts to the surgical single-level k-engine.

**Foundation stone (fork-independent, build first):** the *reflecting* base-swap lemma —
`equiv_in_presentation(add_relators(p, rs), w1, w2) ∧ (∀i. rs[i] ≡_p ε) ⟹
 equiv_in_presentation(p, w1, w2)`. Its forward partner already exists
(`lemma_add_relators_preserves_equiv`, `quotient.rs`); together they give the group-preservation
swap. (`lemma_C_resp`-style; see §4 C3 below.)

### 2.3 ARCHITECTURAL LANDMINE: `lemma_property_ii` requires the iso it cannot get at k-level

The `kp_pinch` engine's headline `lemma_property_ii(data, in_k, g)` has, among its `requires`, the
hard precondition **`hnn_associations_isomorphic(data)`**. For `data = psi_data` this is the iso of
§2.2 — over the base `h3_upto(2n)`, where it is **false**. No `in_k` predicate can repair a false
statement about a literal base presentation. So **the engine cannot be instantiated at the k-level as
written** — the brick5-plan's "Route A = instantiate `lemma_property_ii`" is blocked by exactly the
non-iso fact. (In Layer-1 the engine was used where the iso *did* hold — the `b_m`/T(M) tower.)

The deeper reason: under Approach-(b) our `h3_pres` carries only finite set (I); II/III hold in it
only as *derived consequences* (soundness). As a **group**, `h3_pres` therefore equals Cohen's H₃
(all his relations are consequences), and there the iso `A₊≅A₋` holds. But the iso the engine checks
is about the *base presentation* `h3_upto(2n)` (free c's), not the group `h3_pres` — and at the base,
before climbing into the k-HNN that resolves the c's, the iso genuinely fails. The standard Britton
engine wants a base that *already* has the iso; our finite-(I) base does not.

**The fork (a real architecture decision — resolve before building C4):**
- **Fork A — predicate-relator "with-S" base.** Make the k-level base be `h3_upto(2n)` *plus S* so the
  iso holds there. `S` infinite ⟹ need (i) a **predicate-relator presentation** notion (relators as a
  `spec_fn(Word)->bool`, not a `Seq`), (ii) a predicate version of `hnn_associations_isomorphic`, and
  (iii) a predicate version of `lemma_property_ii`/Britton over it. Large new infra, but each piece is
  a clean generalization of an existing finite one (`quotient.rs add_relators`, `hnn.rs`, `kp_pinch`).
- **Fork B — bespoke non-iso k-engine (Route B).** A Britton/pinch variant **not** gated on the global
  iso: decode each k-pinch of `w_α(c)=1` locally, each pinch licensed by the `S`-predicate (the
  "Pinch-to-Membership" idea), bottoming at `lemma_theorem1`. Avoids predicate-relator presentations
  but needs a new pinch-decode lemma the generic engine doesn't provide.

Both bottom out at the same circularity-breaker (`lemma_theorem1`).

> **⚠ DECISION RE-OPENED (2026-06-23) — see `docs/brick5-fork-reevaluation.md`.** The Fork-B "virtual
> iso" core was found to be UNDESIGNED (the two iso-consuming Britton calls route through
> `lemma_single_step_preserves_syls`, which needs the *universal* iso over an *arbitrary* derivation —
> not word-restrictable; "iso in the quotient" feeds standard Britton only circularly). Combined with
> the post-decision finding that the a-levels are virtual too (Fork B now needs the engine at all
> `2n+1` levels, not one), the cost calculus that favored Fork B has flipped. RECOMMENDATION (pending
> real-Danielle confirmation): pivot to **Fork A** — a predicate/countable presentation foundation,
> which is ALSO the common blocker for Layer 0.5. Treat the decision below as historical.

**DECISION (2026-06-21, w/ Danielle): Fork B.** Fork A is an architectural trap — making the base use
predicate-relators triggers a cascade of refactoring across every lemma that assumes a concrete finite
presentation (`hnn`, `britton_via_tower`, `quotient`, the whole tower). Fork B is the surgical strike:
decode the k-pinch locally via the `S`-predicate, replacing the *structural* iso requirement with a
*membership* proof, bottoming at `lemma_theorem1`. Danielle's "third way" — a lifting lemma letting
`lemma_property_ii` accept a **virtual isomorphism** (iso provable in the *group* `h3_pres` even though
it fails in the base presentation `h3_upto(2n)`) — is the useful conceptual framing of Fork B: the
new engine takes "iso-holds-in-the-quotient" (a per-pinch membership fact, discharged by soundness +
`lemma_theorem1`) where the old one took `hnn_associations_isomorphic`.

---

## 3. Cohen's faithfulness design (p.280–281) — the math we are formalizing

The HNN tower is faithful because every association is a genuine subgroup isomorphism:

- **`A ≅ A_i`** via stated gens (`t↦t_i, x↦xᵐ, d↦b_i d, b_j↦b_j, p↦p`). Cohen: by Prop 1.34
  (HNN-recognition), `A` is the HNN of free `F=⟨t,x,d,b_j⟩` by `p` with relations
  `p⁻¹t_β p = t_β w_β(b) d` (β∈I), and `A_i` similarly with β≡i (mod m); `w_{αm+i}(b)=w_α(b)b_i`
  makes the stated-gen correspondence a well-defined iso. Reduces to the **residue facts** (Layer-1
  property (v)/(vi) territory, `prop_v`/`tower_peel`) lifted to the b-augmented subgroups.
- **`A₊ ≅ A₋`** via stated gens (`U↦U, d↦d, b_j↦b_j c_j, p↦p`). The crux:
  - *inverse `A₋→A₊`* = the endomorphism of H₂ killing every `c_j` (von Dyck, trivially well-defined).
  - *forward `A₊→A₋`* = von Dyck + check `p⁻¹t_α p = t_α w_α(bc) d` for `(α,0)∈H₀`. Holds because
    `w_α(bc)=w_α(b)w_α(c)` (b,c commute) and **`w_α(c)=1` in `C` when `(α,0)∈H₀`** — i.e. soundness.
    The HNN-recognition of `A₊` (Prop 1.34) restricts the relations to `(α,0)∈H₀`, which is the
    **Layer-1 faithfulness fact** `t_α∈⟨U⟩ ⟺ (α,0)∈H₀`. WE HAVE THIS: `lemma_theorem1`
    (`prop_v.rs`), and the half we need (`t_α∈⟨U⟩ ⟹ (α,0)∈H₀`) is `lemma_vii_subset` + `lemma_vi` +
    `lemma_in_TM_config_implies_H0`.

Once all associations are isos, Britton's lemma at each level peels `w_α(c)` (no `k/a_i/p`) down to
`h1`, and the free-product/H₁ projection lands `w_α(c)=1 in C`.

---

## 4. Brick decomposition (proposed)

Bottom-up. Each brick names the existing infra it reduces to.

- **C0 — structural lemmas (small, do first).** `w_α(c) = h_w_c(nk,n,m,α)` is valid over the c-block
  (`c_base..c_base+n`), hence over `h1_base.num_generators`, hence has **no stable letter** of any
  tower HNN (`p`, `a_i`, `k` all sit at indices `≥ h1_num_gens`). This is what lets the peel start.
  Pure index arithmetic over `layout.rs`. *(Verifiable immediately; good build-shakedown brick.)*
- **C1 — the C predicate + `in_C` — DONE** (`higman_completeness.rs` 3/0, 2026-06-21). Resolved
  the co-design with C4 (peer-reviewed). Key outcomes:
  - **`in_C(w)` = `w ∈ ncl(S)` over the k-HNN base `B = h3_upto(2n)`** — *exactly* what a virtual-iso
    `britton_lemma_unconditional` outputs (Britton lands base-word-trivial-in-HNN at "trivial in the
    base", and over the free-c base the honest version is "trivial mod ncl(S)"). Representation: the
    explicit conjugate-product form `∃ factors. all_conj_S_factors(factors) ∧ concat_all(factors) ≡_B w`,
    each factor a conjugate `g·r^{±1}·g⁻¹` of an S-relator `r = w_β(c)` (`(β,0)∈H₀`, `is_S_relator`),
    conjugators `g` arbitrary `B`-words. Chosen over the finite-subset-of-S-adjoined form (which has a
    relator-*ordering* wrinkle in H_mul: `add_relators(B, rs_a+rs_b)` is not an `extends_presentation`
    superset of `add_relators(B, rs_b)`). The conjugate-product form makes the three closure props fall
    out of `concat_all`/`equiv` directly.
  - **Two structural decisions, both peer-confirmed (see §2.3 / Fork B):**
    (i) **C4 is a direct virtual-iso descent, NOT a `lemma_property_ii` instantiation** — in the
    faithfulness instantiation the `in_kp_subgroup` membership witness is the EMPTY factor list (since
    `w_α(c) ≡ ε`), so the generic engine's `choose` over witnesses is a liability (it may pick a
    non-empty `W`, reviving the pinch loop + the false base-descent). C4's input is a base word by
    construction. (ii) **One predicate suffices** — `ncl_B(S) ∩ {pure c-words} = ncl_{F(c)}(S)` (the
    b's commute with the c's so b-conjugators cancel; p/a/U don't enter pure c-words), so C5 is an
    *unfolding* of `in_C` to "= 1 in C", not a bridge between two predicates.
  - **Down-payment proved:** `lemma_in_C_empty` (H_id), `lemma_in_C_mul` (H_mul), `lemma_in_C_resp`
    (H_resp) — the three subgroup-closure props C4 consumes as it accumulates the factor list.
  - **Signature pinned:** `faithfulness_statement(mm,n,m,α)` (a `spec` predicate, no proof obligation
    yet) states `h3_pres ⊢ w_α(c)=1 ⟹ in_C(w_α(c))` with the precise hypotheses (incl. `mm_terminal`
    feeding `lemma_theorem1`, the circularity-breaker). The `proof fn lemma_C_faithful` lands at the
    end of the Fork-B arc (no verifier-bypass stub before then).
- ~~**C1 — the C predicate + `in_C`.**~~ *(original sketch, superseded by the DONE block above.)*
  Define `in_C : spec_fn(Word)->bool` capturing `w ∈ ncl(S)` (NOT
  relators — `S` infinite). Template = `quotient.rs`'s finite normal-closure lemmas
  (`add_relator`/`lemma_normal_closure_contains_conjugates`: a relator's conjugates are identity),
  made **predicate-valued**: `in_C(w)` = `∃` a finite product of base-conjugates `cᵢ·rᵢ^{±}·cᵢ⁻¹` of
  `S`-predicate relators `rᵢ` (each `rᵢ = w_β(c)` with `(β,0)∈H₀`) that is `≡_base w`. **CAUTION
  (learned 2026-06-21):** the *exact* shape of `in_C` is **coupled to the Fork-B engine (C4)** — it
  must be precisely what the non-iso virtual-iso engine consumes as `in_k` and produces as the
  per-pinch membership obligation. So **co-design `in_C` with C4's engine signature**, don't pin it
  speculatively first. The structural closure props (`in_C(ε)`, H_mul, H_resp) hold for almost any
  reasonable ncl predicate, so proving them does NOT validate the design — validate against C4's
  needs. State the faithfulness theorem `lemma_C_faithful` (`h3_pres ⊢ w_α(c)=1 ⟹ in_C(w_α(c))`)
  signature once `in_C` is fixed.
- **C2 — p-level iso (the free basis).** `A₊`'s HNN-recognition uses `{t_α w_α(b) d}` free basis —
  **already proven**, `free_basis.rs` (`lemma_basis_elt_free`). Package it as the p-level
  `kp_pinch` instantiation / the A₊ recognition.
- **C3 — a_i-level isos (φ_i) — REROUTED (see §2.2bis/§2.2ter).** The literal version
  (`hnn_associations_isomorphic(phi_l_data)` over `h3_upto(l-1)`) is **FALSE** — do not attempt it.
  The rerouted C3 is: prove the a-level iso **over the finite family-(II)-augmented base `h3_II`**,
  where it *does* hold literally. Sub-steps:
  - **C3.0 — the reflecting base-swap lemma — DONE** (`base_swap.rs` 13/0). Built the reflecting
    direction `equiv_in(add_relators(p,rs),·,·) ∧ (∀i. rs[i] ≡_p ε) ⟹ equiv_in(p,·,·)`
    (`lemma_add_relators_reflects_equiv`) + the iff `lemma_add_derivable_relators_iff`. **GENERALIZED**
    to the order-agnostic mutual-derivability swap **`lemma_same_group_iff(p, q, w1, w2)`**: any two
    presentations with `q.num_generators == p.num_generators` whose relators are mutually `≡`-derivable
    present the same group. This is what dissolves the relator-*splice/shift* between `h3_II` and
    `h3_pres` (they are NOT in an `extends_presentation` prefix relation). Pure presentation theory.
  - **C3.1 — `h3_II` + group-preservation — DONE** (`h3_ii.rs` 14/0). `h3_II` = the BOTTOM-augmented
    tower: `h2_II = add_relators(h2_pres, family_II)`, a-tower rebuilt on top (same `φ_l`), `k` (ψ) on
    top — so each a-level base carries family (II) (what C3.2 needs). Group-preservation
    `equiv_in(h3_pres,·,·) ⟺ equiv_in(h3_II,·,·)` (`lemma_h3_II_group_preserving`) via the flat splice
    `h3_pres ≃ H + M`, `h3_II ≃ H + family_II + M` (`M = phi_blocks(2n)+Krel`), discharged at the TOP
    level by `lemma_same_group_iff`. **The compositional (level-by-level) route is IMPOSSIBLE** —
    `h2_II ≠ h2_pres` as groups (family (II) needs the `a_i`), so the group-equality is genuinely
    top-level. `family_II_relator = (p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹`, each `≡_{h3_pres} ε` by `lemma_II`.
    Structural support: `lemma_hnn_relators_eq` (Krel/Φ_l agree across same-num_gen bases),
    `lemma_h3_upto_relators` / `lemma_h3_II_upto_relators` (the splice), tower num_gen/valid mirrors.
  - **C3.2 — the b-augmented a-level recognition over `h3_II` — NEXT (the real cost of C3).**
    `A ≅ A_i` via the stated gens, now a *literal* `britton_lemma_unconditional`/`lemma_property_ii`
    argument (the iso is real over `h3_II`): prove
    `hnn_associations_isomorphic(HNNData{ base: h3_II_upto(l-1), associations: phi_assoc(..l) })` for
    each `l`. Reduce to the residue facts (`prop_v`/`tower_peel`) **b-augmented** — `tower_peel`-scale
    but standard (no virtual machinery). Co-design with C4: the family-(II) `alphas` C3.2 needs are the
    β's appearing in the φ_l iso witnesses (the C3.1 lemmas leave `alphas` open for exactly this).
- **C4 — k-level decode via a NON-ISO pinch engine (THE crux; Fork B, see §2.3).** **Cannot** call
  `lemma_property_ii` (its `hnn_associations_isomorphic(psi_data)` precondition is false, §2.2/§2.3).
  Instead build a **"virtual-iso" pinch-decode**: a variant of the `kp_pinch` machinery whose iso
  input is replaced by a per-pinch **membership** obligation discharged from the `S`-predicate
  (`in_C`) + soundness + `lemma_theorem1`. Mechanically reuse as much of `kp_pinch.rs` as possible
  (`lemma_kp_phi_fwd/rev`, the pinch-elimination recursion) — those parts already take the φ-compat
  (H_ab/H_ba) as *predicate* hypotheses, NOT the global iso. The iso is consumed at exactly **two
  spots** — inside `lemma_kp_property_ii_core` (`kp_pinch.rs`), the calls `britton_lemma_full(data,
  wgi)` (~line 1166) and `britton_lemma_unconditional(data, wgi)` (~line 1200), i.e. the
  "`W·g⁻¹≡ε` ∧ no-pinch ⟹ no-stable-letter, then descend to base" Britton-decode half. **Fork B's
  surgical target = replace those two calls with non-iso variants** whose missing iso is supplied by a
  per-pinch membership obligation (virtual iso) from `in_C` + soundness + `lemma_theorem1`. Everything
  else in `kp_pinch.rs` (the `lemma_kp_phi_fwd/rev` conjugation surgery, the pinch-elimination
  recursion, the KPWord folding) is already iso-free and reusable verbatim. Size: a `tower_peel`-scale
  arc plus the two new non-iso Britton variants.

  **Framing correction (important).** `w_α(c)` is a **base word** of the k-HNN — pure c-generators,
  all at indices `< k_top`, no `k`. So completeness is **NOT** "Britton-peel `w_α(c)` down to the
  base": that would need the ψ-iso (false, §2.2) and would give the *contradiction* `w_α(c)=1 in the
  free-c base`. Rather, `w_α(c)` is a base word that **becomes trivial in `h3_pres` precisely because
  ψ is non-iso** — the realization of S. The engine's job is to characterize *which* base words the
  non-iso ψ collapses, and to show that collapse is exactly `in_C` (licensed by S). I.e. the input is
  `equiv_in_presentation(h3_pres, w_α(c), ε)` (from soundness it is consistent; in completeness it is
  the hypothesis), the engine routes it through the (K=in_C, p=k) pinch structure, and the output is
  `in_C(w_α(c))`. The gap "`=ε in the k-HNN` ⟹ `in_kp_subgroup` (pinch factorization)" is the
  Britton-decode half that the engine consumes; it is the same shape consumed in Layer-1 (vi)/(vii).
- **C5 — assembly.** `w_α(c)=1 in h3_pres` ⟹ [k-level engine, C4] ⟹ `in_C(w_α(c))` ⟹ [C1
  unfolding] `w_α(c)=1 in C`. The a_i/p levels (C2/C3) feed C4 as the discharge of H_ab/H_ba (the
  A₊-recognition needs the p-level free basis and the a_i residue isos), **not** as a separate outer
  peel of `w_α(c)`. ∎

**The single circularity-breaker (as in soundness):** Layer-1's `t_α∈⟨U⟩ ⟺ (α,0)∈H₀`
(`lemma_theorem1`). Every iso discharge bottoms out there.

---

## 5. Honest scope

This is a **multi-session arc**, comparable in size to all of E2 (the `ii_subset`/`kp_pinch`/
`tower_peel`/`prop_v` cluster). **Routing corrected 2026-06-21 (§2.2bis/§2.2ter):** the a-levels are
NOT clean — they are as "virtual" as the k-level over the literal base. The reroute is the **finite
family-(II) augmentation** (`h3_II`, group-preserving via `lemma_II`), which re-isolates the virtual
content to the k-level (so C4 stays the *surgical* single-level Fork-B engine) at the cost of a real
b-augmented a-level recognition over `h3_II` (C3.2). No verifier bypasses (standing rule). Sequence:
**C0 DONE** → **C1 DONE** (`in_C` + closure props + signature, `higman_completeness.rs` 3/0) →
**C3.0 DONE** (`base_swap.rs` 13/0: reflecting swap + `lemma_same_group_iff`) → **C3.1 DONE**
(`h3_ii.rs` 14/0: `h3_II` bottom-augmented tower + `lemma_h3_II_group_preserving`) → **C3.2 NEXT**
(b-augmented a-level recognition over `h3_II`) → C2 (package the `free_basis.rs` p-level recognition)
→ C4 (the surgical Fork-B k-engine) → C5 (assembly).

**Most valuable next concrete step = C3.2**, the b-augmented a-level recognition: prove
`hnn_associations_isomorphic(HNNData{ base: h3_II_upto(l-1), associations: phi_assoc(..l) })`. The
foundation (`lemma_same_group_iff`, `h3_II`, group-preservation) is in place. C3.2 is the genuine
`tower_peel`-scale work — now a *literal* Britton argument over `h3_II` (the iso is real because the
base carries family (II)), reducing to the b-augmented residue facts (`prop_v`/`tower_peel`).
Co-design with C4: the concrete `alphas` (which β's of family (II) to splice) = the β's the φ_l iso
witnesses touch; the C3.1 lemmas keep `alphas` open for exactly this. C2 packages `free_basis.rs`;
C4 = the Fork-B k-descent (`faithfulness_statement` body), consuming C1 closure props + C2/C3 isos +
soundness/`lemma_theorem1`, then transporting back to `h3_pres` via `lemma_h3_II_group_preserving`.
