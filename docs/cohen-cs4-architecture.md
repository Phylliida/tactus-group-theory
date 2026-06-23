# CS-4 architecture finding — the a_i iso `A ≅ A_i` over the predicate base

*Written 2026-06-23 (session 19), a deep read-only scoping pass before touching any `.rs`.
Companion-model co-design confirmed the core point. This note **corrects the scope** of CS-4 as
stated in `cohen-section1-assembly-plan.md` §4/§5 ("`tower_peel`-scale; reduces to recognition +
relabeling + residue facts"). It does NOT — there is a substrate-expressivity wall that the plan did
not surface. The finding is captured here for a route decision (co-design w/ Danielle) before the
build, per the standing rule: don't go in undesigned directions (13k lines lost that way before).*

---

## 0. What CS-4 actually asks

For each a-level `l`, the single-letter datum
`data_l = PredHNNData{ base: h3_pred_upto(l-1), associations: phi_assoc(nk,n,m,l) }`.
`hnn_pred_associations_isomorphic(data_l)` unfolds (`pred_hnn.rs:102`) to: for every word `w` valid
over `k = phi_assoc.len() = n+4` generators,

```
  emb(a_col, w) ≡_{h3_pred_upto(l-1)} ε   ⟺   emb(b_col, w) ≡_{h3_pred_upto(l-1)} ε
```

where `a_col = phi_assoc(..).0 = [t, x, d, b_1..b_n, p]` (the literal stated gens) and
`b_col = phi_assoc(..).1 = [config(l,0), xᵐ, b_l·d, b_1..b_n, p] = φ_l(a_col)`.

By **base-faithfulness up the tower** (a word over h2-gens is trivial in `h3_pred_upto(l-1)` iff in
`h2_pred`, via `britton_lemma_unconditional` down the a-levels — needs levels `<l`'s isos, a clean
downward induction), this reduces to the iso **over `h2_pred` directly**. So the heart of CS-4 is:

```
  emb(a_col, w) ≡_{h2_pred} ε   ⟺   emb(b_col, w) ≡_{h2_pred} ε        (★)
```

---

## 1. The standard two-maps factoring (textbook = Cohen §1a)

Let `pa_pred` = the abstract `P_A = HNN(F, p | family (II))`, `F = free⟨t,x,d,b_j⟩` (n+3 gens),
written as a flat `PredPresentation` (base F is free ⟹ its only relators are the family-(II)
p-conjugations, an infinite predicate over all α∈I). Cohen recognizes both `A=⟨a_col⟩` and
`A_i=⟨b_col⟩` as copies of `pa_pred` (Prop 1.34). (★) then factors through `pa_pred`:

- **von Dyck (the EASY halves, now UNCONDITIONAL over the predicate base):**
  - `w ≡_{pa_pred} ε ⟹ emb(a_col, w) ≡_{h2_pred} ε` — `a_col` is the inclusion, so the image of
    `family_II_relator(α)` is *itself*, an `h2_pred` relator ⟹ `≡ ε`.
  - `w ≡_{pa_pred} ε ⟹ emb(b_col, w) ≡_{h2_pred} ε` — the image of `family_II_relator(α)` is
    `family_II_relator(mα+l)` (`lemma_phi_l_on_family_II_relator`, already proven in `phi_l_iso.rs`,
    base-independent), which is **also** an `h2_pred` relator (mα+l is a number word when α is and
    `1≤l≤2n<m`) ⟹ `≡ ε`. **No σ-slice side condition** — this is the predicate-base win that
    killed the finite-tower vacuity.
- **faithfulness (the HARD halves):**
  - `map_a` faithful: `emb(a_col, w) ≡_{h2_pred} ε ⟹ w ≡_{pa_pred} ε`.
  - `map_b` faithful: `emb(b_col, w) ≡_{h2_pred} ε ⟹ w ≡_{pa_pred} ε`.

Then (★) is: forward `a⟹b` = `map_a` faithful ∘ `b`-von-Dyck; backward `b⟹a` = `map_b` faithful ∘
`a`-von-Dyck. **Both faithfulness halves are genuinely needed** — von Dyck only handles `w` that is
already `pa_pred`-trivial; converting "emb trivial" *back* to "`w` `pa_pred`-trivial" is exactly
faithfulness. (No endo trick: unlike the k-iso's c-killing endomorphism — a genuine `H₂` hom — `φ_l`
maps `x↦xᵐ` and breaks the `K_M` machine relators, so it is NOT an `H₂` endomorphism; there is no
analogous shortcut for the a_i iso. Companion-confirmed.)

---

## 2. The wall: faithfulness needs a p-peel over an INFINITE-association HNN

`map_a` faithful is Prop-1.34 recognition of `A`: the only relations among `t,x,d,b_j,p` in `H₂` are
the family-(II) ones. To prove it you **peel `p`** from `emb(a_col,w)` over `H₂ = HNN(H₁, p | family
(II))`. But **family (II) is infinite**, so the associated subgroup of the p-HNN is the
**infinitely-generated** `A_p = ⟨t_α : α∈I⟩`, and a Britton pinch references membership in it.

The substrate's Britton (`pred_britton_via_tower::britton_lemma_unconditional`) is over a predicate
**base** but a **finite** `associations: Seq<(Word,Word)>` (`PredHNNData`). It cannot express an
HNN with infinitely many p-associations. The finite-tower attempt peeled `p` over
`recog_data = HNN(h1_base, p | family (II) FINITE slice over alphas)` and `britton_lemma_full`, and
got stuck because the slice cannot be σ-closed (`σ_l(γ)=mγ+l` strictly grows; `lemma_map_b_forward`
needs `sigma_fwdsat`, machine-refuted vacuous by `lemma_sigma_sat_upto_unsatisfiable`).

**So CS-4's faithfulness is NOT `tower_peel`-scale.** It needs infinite/predicate-association
handling. This is the textbook situation (Prop 1.34 over the *infinitely-presented* `H₂`), so it is
not a reinvention — but it is substantial substrate, not a residue-fact application.

---

## 3. Two candidate routes (the decision)

### Route 1 — compactness-to-finite for the FORWARD; relabeling-iso for the BACKWARD
A *finite* derivation witnessing `≡_{h2_pred} ε` uses only finitely many relators, so it is valid in
a **finite slice presentation** `h2_II(D)`. This lets the forward reuse the **real** (non-vacuous!)
`lemma_map_a_forward` (`phi_l_pinch.rs:773`; preconditions `!contains(0)/no_duplicates/numbers_word`
are satisfiable):

1. `lemma_pred_deriv_finite_support` (NEW, generic): a pred-derivation in `h2_pred` from `u` to `ε`
   is a derivation in the finite `Presentation` holding exactly its used relators.
2. strip `S` first via a CS-2-style c-retraction `ρ_c : h2_pred → h2_pred∖S` (fixes c-free words;
   `a_col`/`b_col` words are c-free), so the slice has only K_M + comm + family-(II) relators.
3. build `alphas` = the family-(II) indices used (dedup, drop 0 [it is in `h2_pres`], `numbers_word`
   holds for each), apply `lemma_map_a_forward` over `h2_II(alphas)` ⟹ `w ≡_{pa_data(betas)} ε`.
4. lift `pa_data(slice)`-triviality to `pa_pred` (easy forward — `pa_pred` has more relators).

**Backward (`map_b` faithful = `map_a` faithful + M2).** `emb(b_col,w) = emb(a_col, φ_l_src(w))`
(`lemma_mapb_factor_source`), so `map_a` faithful gives `φ_l_src(w) ≡_{pa_pred} ε`; the residue is
**M2 = `φ_l_src` injective on `pa_pred`**: `φ_l_src(w) ≡_{pa_pred} ε ⟹ w ≡_{pa_pred} ε`. The
existing `lemma_mapb_M2` needs `sigma_fwdsat` (vacuous) because it forces `φ_l_src` to be an endo of
a **single** slice (`σ_l(slice)⊆slice`). **The escape:** as a relabeling *between* slices
`φ_l_src : pa_data(G) → pa_data(σ_l(G))` it is an **isomorphism needing only σ-INJECTIVITY** (always
true — `mγ+l` is injective in γ), NOT σ-closure. So a fresh per-word M2 ("`φ_l_src(w) ≡_{pa_data(E)} ε`
⟹ `w ≡_{pa_data(G)} ε`" with `E = σ_l(G)`, then lift to `pa_pred`) plausibly closes M2 without the
infinite Britton. ⚠ **Wrinkle to check:** a derivation of `φ_l_src(w) ≡ ε` may use an "irrelevant"
family-(II) relator over `η ∉ σ_l(I)` (insert+delete); need to argue those can be confined to
`σ_l(G)` or dropped. *(This route is PROMISING but unproven — the wrinkle is the gating unknown.)*

- **Pros:** reuses the big finite `map_a`-forward + residue machinery (already verified, REAL);
  no new 21k-line substrate. Forward arc is concrete and startable now.
- **Cons:** the M2 relabeling-iso wrinkle is unverified; multiple new generic lemmas
  (finite-support, c-strip, slice-building, relabeling-iso); intricate bookkeeping.

### Route 2 — a unified predicate/infinite-association Britton substrate
Build `PredHNNData`-with-**predicate** associations (the associated subgroup as a predicate, or
association-pairs as `spec_fn`) + its Britton lemma (FA-9b-scale or larger, since it generalizes
associations on top of the base). Then recognize `h2_pred` and `pa_pred` as such p-HNNs and get
`map_a` faithful + M2 + (★) natively; σ-closure is **automatic** over the infinite, σ-closed `I`.

- **Pros:** uniform; the math is clean (σ-closure free over `I`); also the canonical Prop-1.34
  formalization; reusable for any later infinite-base recognition.
- **Cons:** large new substrate (re-derive Britton with predicate associations); companion estimates
  ≥ FA-9b effort. Multi-week.

---

## 4. Recommendation (for the route decision)

**Prototype Route 1's M2 relabeling-iso wrinkle first (cheap, decisive).** If `φ_l_src : pa_data(G)
≅ pa_data(σ_l(G))` is establishable as a finite presentation iso and the "irrelevant extra relator"
wrinkle resolves, Route 1 closes CS-4 by **reusing the already-verified finite forward machinery**
and avoids the multi-week substrate entirely — a large win. If the wrinkle is fatal, Route 2 (the
predicate-association Britton) is the textbook fallback and is sound (companion-confirmed).

The forward half of Route 1 (compactness → `lemma_map_a_forward`) is independently valuable and
startable regardless, BUT it should not be built before the route is chosen, since Route 2 would
supersede the compactness plumbing. **Held for the route decision** (this note + the AGENDA update).

### Shape-stable pieces (safe to build under either route)
- `pa_pred` as a flat `PredPresentation` (free F + p, relators = family-(II) predicate) + validity.
  Referenced by the von-Dyck statements and the final (★) either way.
- The von-Dyck (easy) directions over `h2_pred` — unconditional; the predicate-base win made
  concrete. Reusable building blocks for (★).

---

## 5. One-line status

CS-4 = (★). von-Dyck halves: EASY/unconditional (predicate-base win). Faithfulness halves: the wall
— need infinite-association handling. Route 1 (compactness-forward + relabeling-iso-backward) may
avoid new substrate (prototype the M2 wrinkle to decide); Route 2 (predicate-association Britton) is
the sound textbook fallback. **No code committed this session — surfaced for the route decision.**
