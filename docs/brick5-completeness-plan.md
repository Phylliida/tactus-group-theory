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
- **C1 — the C predicate + `in_C`.** Define `in_C(α-word stuff)` / `c_trivial: spec_fn(Word)->bool`
  capturing `w ∈ ncl(S)` at the h1 level via the benign/predicate machinery (NOT relators). State the
  target faithfulness theorem signature against it.
- **C2 — p-level iso (the free basis).** `A₊`'s HNN-recognition uses `{t_α w_α(b) d}` free basis —
  **already proven**, `free_basis.rs` (`lemma_basis_elt_free`). Package it as the p-level
  `kp_pinch` instantiation / the A₊ recognition.
- **C3 — a_i-level isos (φ_i).** `A≅A_i`. Reduce to the residue facts (`prop_v`/`tower_peel`,
  b-augmented). These levels admit a *direct* `britton`-style peel (c's not involved) — possibly
  reusable `britton_lemma_unconditional` if `hnn_associations_isomorphic(phi_l)` can be shown for
  `h3_upto(l-1)` (the φ_l associations only touch t,x,d,b_j,p — no c — so the iso may hold literally;
  CHECK whether the residue facts give it without S). If it holds literally, C3 is *not* blocked on
  the predicate engine.
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
`tower_peel`/`prop_v` cluster), and **harder than the brick5-plan routing suggested** — the generic
engine does not apply at the k-level (§2.3), so C4 is **Fork B**: build the two non-iso Britton
variants + thread them through a virtual-iso `kp_property_ii_core`. No `assume`/`admit`/`external_body`
(standing rule). Sequence: **C0 DONE** → C1 (the `in_C` predicate + faithfulness theorem statement) →
C3 (check whether φ_i iso holds *literally* at `h3_upto(l-1)` — likely yes, no c's — so a_i levels may
use the existing `britton_lemma_unconditional` directly) → C2 (package the `free_basis.rs` p-level
recognition) → C4 (the Fork-B non-iso k-engine — the crux) → C5 (assembly + free-product projection).

**Most valuable next concrete step after C0 = C1:** pin down `in_C: spec_fn(Word)->bool` ("trivial in
`C=⟨c;S⟩`", i.e. `∈ ncl(S)`; mirror `quotient.rs`'s finite `add_relators`/normal-closure-conjugate
lemmas but predicate-valued over the `S`-predicate) and the exact faithfulness theorem signature, so
C2–C5 have a fixed target. Shape `in_C` to satisfy the engine's `in_k` hypotheses by construction
(`in_C(ε)`, H_mul, H_resp are structural; H_ab/H_ba are the deep §3 content for C4). Get this
signature right *before* proving anything downstream. The easy closure props (`in_C(ε)`, H_mul,
H_resp) are a safe first verifiable down-payment on C1.
