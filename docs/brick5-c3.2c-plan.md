# Brick 5 — C3.2c: the bottom crux (b-augmented `conj_scaling_trivial_iff` over `h2_II`)

The single gating item of C3.2 (see `brick5-c3.2-plan.md` §4/§5). C3.2a (a_words/b_words backbone)
and C3.2d-infra (collapse halves) are DONE (`h3_ii.rs` 20/0); the tower lift (C3.2d) and von Dyck
(C3.2b) are both *inline pieces of the faithfulness induction whose bottom fact IS this crux* — so
none can close until C3.2c exists, and (standing rule) no `assume`-pinned skeleton is allowed.
Written 2026-06-22 after studying the machine-group template + a companion-model design review.

---

## 1. The exact statement

```
lemma_phi_l_iso_at_h2II(mm, n, m, alphas, l):
  requires 1 ≤ l ≤ 2n,  2n < m,  ∀i. numbers_word(n,m,alphas[i]),  <alphas ⊇ the β's w touches>
  ensures  hnn_associations_isomorphic(HNNData {
               base: h2_II(mm, n, m, alphas),
               associations: phi_assoc(g_m(mm).num_generators, n, m, l),
           })
```

Unfolds (with `k = n+4`, `a_words`/`b_words` from `lemma_phi_assoc_index`) to: **for every `w` valid
over `k`,** `emb(a_words,w) ≡_{h2_II} ε  ⟺  emb(b_words,w) ≡_{h2_II} ε`, where
- `a_words = [t, x, d, b_1..b_n, p]` (literal gens),
- `b_words = [t_l=config(l,0), xᵐ, b_l·d, b_1..b_n, p]` (φ_l images).

Both embeddings are `h2`-words (`lemma_phi_l_emb_h2_valid`, already verified).

---

## 2. The template — and where it breaks

The machine-group crux `lemma_conj_scaling_trivial_iff` (`machine_group.rs:6522`) proves
`emb([config(a,b),x^px,y^py], w) ≡_{base_A} ε ⟺ w ≡_{base_A} ε` via:
- `a_as_hnn()` (`machine_group.rs:3935`): `base_A = ⟨t,x,y|[x,y]⟩` recognized as `HNN(free ⟨t,x⟩, y |
  y⁻¹xy = x)` — **base FREE, association TRIVIAL (identity on ⟨x⟩), iso immediate**
  (`lemma_a_as_hnn_isomorphic`: `a_words =~= b_words`).
- conjugation-telescope `emb(aw,w) ≡ ig·pw·g` + `lemma_psi_A_injective` (Britton-peel over `a_as_hnn`).

**Three things break for the b-augmented case (why this is a `prop_v`-scale arc, not a copy):**
1. **The recognition free-base gens are SCATTERED, not a prefix.** ⟨t,x,d,b_j⟩ live at indices
   `0, 1, d_idx=nk+2n, b_idx=nk+n..nk+2n-1` — interleaved with `y=2` and the K_M machine gens
   `3..nk-1` which are NOT in the recognition subgroup. So there is no clean `pres_F` analog of
   `pres_tx`; the recognition is about a **subgroup of `h2_II`**, and `h2_II` itself carries relators
   (h2_pres + family_II). The `a_as_hnn` trick (free base, 0 relators) does not transcribe directly.
2. **The associations are NON-trivial and INFINITE.** Cohen Prop 1.34 recognizes the subgroup
   `A = ⟨t,x,d,b_j,p⟩` as `HNN(F=⟨t,x,d,b_j⟩, p | p⁻¹ t_β p = t_β w_β(b) d, β∈I)`. The associated
   subgroups are `⟨t_β : β∈I⟩` and `⟨t_β w_β(b) d : β∈I⟩` (NOT a single cyclic ⟨x⟩). The iso of the
   association is the **b-augmented residue content** (`prop_v`/`tower_peel` territory), not `=~=`.
   `I` is infinite; `h2_II` carries only the finite `β∈alphas` slice.
3. **φ_l augments `t↦t_l` (digit-scaling in x) AND `d↦b_l·d`.** The endomorphism whose injectivity we
   port from `lemma_psi_A_injective` is scaling-plus-augmentation, not pure scaling.

---

## 3. Sub-lemma ladder (ordered; maps existing infra + companion review)

The companion review (2026-06-22) recommended the **two-direction split (von Dyck + Britton
injectivity)** over the telescope ("the telescope is elegant on paper but a nightmare of induction
indices in a formal system" — plausible here given the augmentation), a **complexity-measure
induction** for the peel (p-count + base-segment length — matches `britton_via_tower`'s `decreases`),
and residue facts as a **standalone base lemma = the Britton-peel precondition**. Mapped to our infra:

**Phase A — residue / base layer (the real cost; reuse `prop_v`/`tower_peel`).**
- **A1 `lemma_tbeta_wb_residue_iso`**: the correspondence `t_β ↦ t_β w_β(b) d` extends to a subgroup
  iso `⟨t_β:β⟩ → ⟨t_β w_β(b) d:β⟩` over `F`. This IS the b-augmented residue fact. Reuse: the
  numbering identity `w_{αm+i}(b)=w_α(b)b_i` (`word_numbering.rs`), and the `prop_v` accumulator /
  `tower_peel` coordinate-survival machinery, lifted to the b-augmented subgroup. **Hardest brick.**
- **A2 `lemma_phi_scaling_injective_F`**: the φ_l endomorphism `t↦t_l, x↦xᵐ, d↦b_l d, b_j↦b_j` is
  injective on `F` (analog of `lemma_psi_A_injective`'s base step). Conjugation-telescope OK at this
  pure-free-group level (no p), so the telescope objection doesn't bite here.

**Phase B — HNN recognition layer.**
- **B1 `recog_data` — DONE** (`h3_ii.rs` 25/0, 2026-06-22). **Design resolved (w/ Danielle): recognize
  the WHOLE `h2_II` as a single `p`-HNN over `h1_base`, NOT a subgroup over free `F`.** The scattered-gen
  worry (§2.1) evaporates: we never isolate a free `F`. Key realization — `h2_pres = HNN(h1_base, p |
  p⁻¹ t p = td)` carries only the α=0 p-relation, and `h2_II = add_relators(h2_pres, family_II)` adds the
  family-(II) relators `(p⁻¹ t_β p)·(t_β w_β(b) d)⁻¹`, which are EXACTLY more `p`-conjugation relations.
  Folding them into the HNN association list gives `recog_data = HNNData { base: h1_base, associations:
  p_assoc ++ family_II_assoc }` (where `family_II_assoc[i] = (config(β,0), t_β w_β(b) d)`, neither side
  touching `p`, so valid over `h1_num_gens = nk+2n+1`). Delivered:
  - `family_II_assoc`, `recog_data` (spec); `lemma_family_II_rhs_valid_h1` (rhs valid over H₁ gens).
  - `lemma_recog_data_valid` = analog of `lemma_a_as_hnn_valid`.
  - `lemma_recog_relator_is_family` (`hnn_relator(recog,1+j) = family_II_relator(alphas[j])`) +
    `lemma_recog_hnn_relators_split` (`hnn_relators(recog) =~= hnn_relators(h2_data) ++ family_II`).
  - **`lemma_recog_presentation`** = the headline: `hnn_presentation(recog_data) == h2_II` LITERALLY
    (analog of `lemma_a_as_hnn_presentation`). So Britton over `recog_data` applies directly to `h2_II`.
  **The "free-base fallacy" (Danielle, confirmed):** Britton's lemma needs ONLY the iso condition
  `hnn_associations_isomorphic(recog_data)` (= A1, the residue iso), never a free base. Non-freeness of
  `h1_base` bites in exactly ONE place — the A1 iso proof — and nowhere else.
- **B2 `lemma_finite_beta_suffices`**: any `w`'s Britton p-analysis touches only finitely many β,
  all `∈ alphas` (the finite augmentation covers them). Makes "infinite I" rigorous as "the finite
  slice `h2_II` carries." (Companion's "Local Alphas"; our `h2_II` bakes the finite slice in already,
  so this may be a `requires alphas ⊇ betas(w)` side-condition rather than a separate lemma.)

**Phase C — the crux assembly.**
- **C1 von Dyck (`⟸`, = C3.2b at the bottom)**: `emb(b_words,w)` satisfies every relator the
  `a_words` (literal gens) satisfy in `h2_II`. The p-relator maps to a `family_II` relation — present
  literally in `h2_II` (C3.1). Via `lemma_emb_respects_source_equiv` against the recognition's relators.
- **C2 forward (`⟹`, faithful)**: Britton-peel `emb(b_words,w) ≡ ε` over `recog_data` using A1 (the
  residue iso = the peel's well-definedness precondition) + A2; descend to `F`-triviality, then back
  to `emb(a_words,w) ≡ ε`. Complexity-measure `decreases` (p-count, then base length).
- **C3 biconditional**: combine C1+C2; package as `lemma_phi_l_iso_at_h2II`.

Then C3.2d wraps this in the `decreases l` faithfulness induction (mirror `lemma_b_m_upto_faithful`)
to get `lemma_phi_l_iso` at every tower level.

---

## 3b. Sharpened ladder (post-B1, 2026-06-22)

B1's whole-group recognition (`h2_II == hnn_presentation(recog_data)`) reshapes the ladder. The old
A1/A2/B1/B2 split was written for the subgroup-over-free route; with the global `p`-HNN recognition the
crux becomes cleanly **"the φ_l endomorphism is faithful over `h2_II`"**, mirroring
`lemma_conj_scaling_trivial_iff` but with `base_A → h2_II` and `ψ (scale x,y) → φ_l (t↦t_l, x↦xᵐ, d↦b_l·d)`.

Key reframing: in the crux `emb(a_words,w) ≡_{h2_II} ε ⟺ emb(b_words,w) ≡_{h2_II} ε`, the a-side
`a_words=[t,x,d,b_j,p]` is the *identity-ish* embedding (each stated gen ↦ itself), so `emb(a_words,w)` is
just `w` relabeled into the real generators — a word in the subgroup `⟨t,x,d,b_j,p⟩`. The b-side is its
φ_l-image: **`emb(b_words,w) = subst(emb(a_words,w))`** where `subst` is the φ_l endomorphism on ALL
`h2_II` gens (t↦config(l,0), x↦xᵐ, d↦b_l·d, b_j↦b_j, p↦p; non-stated gens y/machine/c_j ↦ themselves).
So the crux = "subst faithful on `emb(a_words,w)`".

**B1.5 DONE** (`h3_ii.rs` 28/0, 2026-06-22): the subst-factoring bridge.
`emb(b_words,w) =~= apply_embedding(phi_l_subst, emb(a_words,w))`. Delivered `compose_embeddings` +
`lemma_apply_embedding_compose` (general composition `f(g(w))=(f∘g)(w)`, reusing benign's
`lemma_apply_embedding_concat`/`_inverse`), `phi_l_subst` (φ_l as the full h2-gen substitution),
`lemma_phi_l_subst_on_a_words` (`compose(phi_l_subst, a_words) =~= b_words`), and the bridge
`lemma_phi_l_factor_through_subst`. Both crux directions consume it.

**ROUTING CORRECTION — von Dyck goes through the SUBGROUP, NOT subst-as-h2_II-endo (confirmed w/
Danielle 2026-06-22).** The "subst respects every `h2_II` relator (incl. K_M machine relators)" reading
is **Route A = a TRAP**: it would force proving `phi_l_subst` (t↦config(l,0), x↦xᵐ, fix machine gens) is
an endomorphism of the whole machine group `G(M)` — since `subst(config(a,b)) = config(ma+l, b)`, the
per-quad relators `r⁻¹ config(a,b) r = config(c,0)` would have to survive a digit-scaling, which is
property-(iii)-scale work and conceptually the wrong altitude. **Route B (Cohen's actual route):** a map
`φ: A → H` is a homomorphism iff it respects `A`'s OWN relations — the machine relators are relations of
the ambient `H`, not of the subgroup `A`, so they never enter. `A = ⟨t,x,d,b_j,p⟩` is recognized as
`HNN(F = free⟨t,x,d,b_j⟩, p | family II)`, so `A`'s only relations are the `p`-conjugations. Von Dyck =
check `φ_l` (and `φ_l⁻¹`) respect those `p`-conjugations — the **family-(II) payoff** (the residue
identity `w_{αm+i}(b)=w_α(b)·b_i` aligns the images). The d↦b_l·d augmentation lives entirely inside the
`p`-conjugation check, not in any machine relator.

**Corrected next-bricks (gating order):**
1. **F1 — `F = ⟨t,x,d,b_j⟩` is free in `h2_II`** (the Route-B prerequisite). Relate to `free_basis.rs`
   (`lemma_basis_elt_free` proved `{t_α w_α(b) d}` free; here we need `{t,x,d,b_j}` free — different
   family, similar base-descent machinery). This is what makes "`A = HNN(F, p | family II)`" the actual
   presentation of the subgroup `A` (so `A`'s only relations are the p-conjugations).
2. **A1 — the residue/p-conjugation iso = `hnn_associations_isomorphic(recog_data)`** AND the φ_l
   p-conjugation checks. The genuine `prop_v`-scale content (`t_β ↦ t_β w_β(b) d` is a subgroup iso over
   `h1_base`; the von Dyck p-relations are its by-product). Reuse `prop_v`'s `lemma_accumulator_inv` +
   `tower_peel`'s coordinate survival; the numbering identity `w_{αm+i}(b)=w_α(b)·b_i`
   (`word_numbering.rs`). **Do NOT start at a session tail.**
3. **C-forward (faithful).** Britton-peel `p` over `recog_data` (B1 gives `h2_II = hnn_presentation(recog_data)`,
   so `britton_lemma_full` applies) using A1 as the iso precondition; descend to `h1_base`.
4. **C-backward (von Dyck).** Via the subgroup-A presentation (F1 + the p-conjugation checks); the
   family-(II) payoff. NOTE the bridge B1.5 still helps frame the image, but the homomorphism check is
   over `A`'s relations, NOT over `h2_II`'s.
5. **C3 — biconditional** = forward + backward; package as `lemma_phi_l_iso_at_h2II`.

The original §3 A2 (`lemma_phi_scaling_injective_F`) and B2 (`lemma_finite_beta_suffices`) are subsumed:
A2's injectivity is the base-descent tail of C-forward; B2 becomes the `requires alphas ⊇ betas(w)`
side-condition baked into `h2_II`'s finite slice.

## 4. F1 — the route (DE-RISKED 2026-06-22) and first down-payment

### 4.0 F1a DONE — `⟨t,x⟩` free in `K_M` (`f_free.rs` 1/0)
`lemma_tx_free_in_g_m`: a word over `{t=Gen0, x=Gen1}` trivial in `K_M = g_m(mm)` is trivial in
`pres_tx = free⟨t,x⟩`. Chain: `lemma_g_m_base_faithful` (g_m→base_A, in `free_basis.rs`) +
the EXISTING `lemma_a_base_faithful` (base_A→pres_tx, Tietze bridge + peel the `y`-HNN layer
`base_A = HNN(pres_tx, y | y⁻¹xy=x)`). **No retraction `K_M → ⟨t,x⟩` exists** (the machine relators
are conjugacy relations among config words that can't be killed while fixing `t,x`); `⟨t,x⟩` is free
in `K_M` but NOT a retract — established by the FAITHFUL embedding, not a homomorphism.

### 4.1 The assembly route — CORRECTED
Danielle's first instinct (a projection homomorphism `h1_base → Free(t,x,b_j,d)` collapsing `K_M` onto
`Free(t,x)`) is IMPOSSIBLE — no such retraction exists (above). The available free-product machinery
(`normal_form_free_product.rs`: `lemma_free_product_injective_left/right`, `lemma_free_product_reflects_left`,
`fp_left/right_retraction`) is FACTOR-LEVEL ONLY (a word IN ONE factor, trivial in `G1∗G2` ⟹ trivial in
that factor). There is NO spanning normal-form theorem (alternating-nontrivial-syllables ⟹ nontrivial)
and no free-product associativity. So the spanning faithfulness of `F = ⟨t,x⟩*⟨b_j⟩*⟨d⟩` (which spans all
three factors) is NOT off-the-shelf.

**THE CLEAN ROUTE (verified sound 2026-06-22): "free family extends by a free stable letter".** Adding a
free generator `s` to a group `G'` is exactly `HNN(G', s | NO associations)` — with `associations = []`
(`k=0`): `hnn_associations_isomorphic` is VACUOUS (only the empty word is valid over 0 gens), and
`has_pinch_at` reads `in_generated_subgroup(base, [], middle)` = `middle ≡_{G'} ε` (the trivial subgroup),
so a `pinch` is exactly an adjacent `s … s⁻¹` whose between-part is trivial in `G'` — precisely free-generator
behaviour. So `britton_lemma_full` (`britton_via_tower.rs:8678`: `w ≡ ε ∧ has_stable_letter ⟹ has_pinch`)
APPLIES (iso vacuous). This reuses the project's strongest tool (Britton) instead of reinventing the AFP
spanning normal form.

**B1 (THE reusable meat) — `lemma_extend_free_by_stable` — DONE (2026-06-22, `f_free.rs` 18/0):**
```
requires
  presentation_valid(gp),
  (∀i) word_valid(gens[i], gp.num_generators),
  // free-family hypothesis (higher-order precondition):
  (∀u) word_valid(u, gens.len()) ∧ equiv_in(gp, apply_embedding(gens,u), ε)
        ⟹ equiv_in(free_group(gens.len()), u, ε),
  word_valid(w, gens.len()+1),
  equiv_in(hnn_presentation(free_stable_data(gp)),
           apply_embedding(stable_emb(gp,gens), w), ε)        // stable_emb = gens.push([Gen(gp.num_generators)])
ensures equiv_in(free_group(gens.len()+1), w, ε)
```
Proof = length induction (port of `lemma_psi_F_injective`): base case (`stable_count(outer,w)==0` ⟹ `w` valid
over `gens.len()`) delegates to `lemma_extend_free_no_stable`; the step (`W` has a stable letter, is trivial)
calls `britton_lemma_full` (iso VACUOUS over empty associations) → `lemma_extend_pinch_descends` (a pinch in `W`
descends to a pinch in `w`, port of `_pinch_descends`) → `lemma_free_stable_pinch_out` (generic empty-assoc
pinch-out: `w ≡ wshort` in `hnn_presentation(outer) == free_group(gens.len()+1)`, the latter by
`lemma_free_stable_of_free_group`) → `lemma_emb_respects_source_equiv` (relator-free source ⟹ `W_short ≡ ε`) →
IH. **The pinch-middle↔free-reduction match** is realised inside `_pinch_descends`'s spanning case: the pinch
middle `W[1..J] ≡_{gp} ε`, which via the prefix correspondence (`lemma_extend_spanning`) equals
`apply_embedding(gens, w2[0..l]) ≡_{gp} ε`, so the free-family hyp gives `w2[0..l] ≡_free ε` — exactly the
outer pinch's trivial-middle condition. **The W↔w position correspondence** is `lemma_extend_spanning` (port of
`_spanning`); note the RUN-ROLES are SWAPPED vs `ψ_F`: there the stable gen `x↦xᵖ` is a run and `t↦t` is length-1,
here the stable gen `s↦[s]` is length-1 (so the spanning case fires when the STABLE letter is peeled) and the
non-stable gens `↦gens[i]` are arbitrary stable-free runs (so a non-stable peel strips a variable-length prefix).
Support lemmas: `lemma_extend_stable_count_eq` (inner stable count of `W` = outer stable count of `w`, the
factor-1 analog of `lemma_psi_F_stable_count_scales`), `lemma_free_stable_data_valid/_isomorphic`,
`lemma_word_valid_no_inner_stable`, `lemma_trivial_in_empty_subgroup`. (The free-product route via
`lemma_free_product_injective_left` is used only in the base case `lemma_extend_free_no_stable`.)

**B2 — iterate B1 — DONE (2026-06-22, `f_free_tower.rs` 9/0, NEW module).** Seed F1a (`[t,x]` free in `K_M`),
add `b_1,…,b_n`, then `d` ⟹ `[t,x,b_j,d]` free in `K_M ∗ F(b) ∗ ⟨d⟩`. Spec fns `free_stable_tower(gp,j)` (j-fold
empty-assoc HNN over `gp`) + `free_stable_family(gp,gens,j)` (gens + the j adjoined top gens); the induction is
`lemma_free_stable_tower_extends` (decreases j, each step `lemma_free_family_extends`). Headline
`lemma_txbd_free_in_tower`: `is_free_family(free_stable_tower(g_m,n+1), free_stable_family(g_m,[t,x],n+1))` AND
`free_stable_tower(g_m,n+1) == free_product(g_m, free_group(n+1))`. Closed forms — `lemma_free_stable_tower_closed`
(tower = gp + j gens, SAME relators), `lemma_free_stable_family_closed` / `lemma_txbd_family_layout` (`t,x`@`0,1`,
`b_j`@`nk..nk+n-1`, `d`@`nk+n`), `lemma_free_stable_tower_is_free_product` — pin the layout the B3 bridge consumes.

**B3 — connect to `h1_base` — DONE (2026-06-22, `f_free_h1.rs` 11/0, NEW module).** `h1_base` carries the
`c_j` + comm relators (`b_i c_j = c_j b_i`). The homomorphism `kill_c : h1_base → free_stable_tower(g_m,n+1)`
(= `K_M ∗ F(b) ∗ ⟨d⟩`) kills the `c`-block (↦ε), fixes K_M, and shifts `b,d` DOWN by `n` past the dropped
`c`-block. Valid (`lemma_kill_c_hom_valid`): K_M relators fixed (`lemma_kill_c_fixes_low`) and trivial in the
target (= g_m relators, `lemma_relator_is_identity`); each commutator `b_i c_j b_i⁻¹ c_j⁻¹ ↦ b_i' b_i'⁻¹ ≡ ε`
(`lemma_kill_c_on_comm_relator`: c's vanish, leaving a cancelling pair — the index recovery isolated in
`lemma_kill_c_on_comm_idx` for a clean nonlinear-`n*n` context). Then the pullback engine
(`free_basis::lemma_pullback_free`): `comp_images(kill_c, f_h1_family) ==` B2's tower family
(`lemma_comp_is_b2_family`, each appended `Gen(nk+n+i) ↦ Gen(nk+i) = free_stable_letter(nk,i)`), so B2's
freeness (`lemma_txbd_free_in_tower`) descends any source relation to free-triviality. Headline =
`lemma_f_free_in_h1` (`is_free_family(h1_base(mm,n), f_h1_family(mm,n))`), where `f_h1_family = [t,x]` + the
literal h1 b/d block `Gen(nk+n+i)`, `i=0..n`. The reindex was clean (no fold-c-as-stable-letters fallback
needed). **NEXT = B4 (lift `h1_base ↪ h2_II` = A1, §4.2).**

**B4 — lift to `h2_II`:** `F` free in `h1_base` + `h1_base ↪ h2_II` faithful (= A1, the recog_data HNN validity)
⟹ `F` free in `h2_II`. So F1-at-h2_II depends on A1; but von Dyck only needs the subgroup-`A` presentation,
which uses `F` free in `h1_base` (B3) directly.

### 4.2 A1 — REFRAMED & DE-RISKED (2026-06-22, peer-confirmed). NOT `prop_v`-scale after all.
**A1 = `hnn_associations_isomorphic(recog_data(mm,n,m,alphas))`.** The earlier "genuine `prop_v`-scale
residue iso, hardest brick" estimate was PESSIMISTIC. Recon (2026-06-22) collapses A1 to an assembly of two
**already-proven** freeness lemmas through F3. The companion model independently confirmed the logic sound.

**The key observation.** `recog_data.associations = p_assoc ++ family_II_assoc`, so its two columns are:
- `a_words` (`.0`) = `[t] ++ [config(αᵢ,0)]`  (`p_assoc[0].0 = seq![Gen0]`; `family_II_assoc[i].0 = config(αᵢ,0)`).
- `b_words` (`.1`) = `[td] ++ [config(αᵢ,0)·w_{αᵢ}(b)·d]`  (`p_assoc[0].1 = td_word`; `family_II_assoc[i].1 = family_II_rhs(αᵢ) = basis_elt(αᵢ)`).

**The `p_assoc` head IS the α=0 case** (VERIFIED concretely): `config_word(0,0) =~= seq![Gen0]`
(`lemma_config_word_zero`), and `w_b(_,_,_,0) = ε` (the `α==0` base case of `w_c`), so `basis_elt(0) =
config(0,0)·ε·d = [Gen0, Gen(d_idx)] = td_word`. Hence with **`betas = seq![0] + alphas`**:
`a_words ≡ config_emb(betas)` and `b_words = basis_emb(betas)` entry-wise (head up to the `config_word(0,0)` ≡).

**The iso reduces to "both columns are free families" + F3** (peer-confirmed valid):
`apply_embedding(a_words,w) ≡_{h1} ε ⟹ (a free) w ≡_free ε ⟹ (F3 on b) apply_embedding(b_words,w) ≡_{h1} ε`,
and symmetric. So `hnn_associations_isomorphic(recog_data)` follows from:
1. **`config_emb(betas)` free in `h1_base`.** `lemma_config_emb_free` already gives it free in `K_M = g_m`;
   LIFT to `h1_base` via the **`kill_hom` retraction** (`free_basis::kill_hom` is identity on the K_M block ⟹
   `K_M` faithfully embeds in `h1_base`: a K_M word `≡_{h1} ε` ⟹ `apply_hom(kill_hom,·) ≡_{g_m} ε` ⟹ (kill_hom
   fixes low) `≡_{g_m} ε`). This retraction lemma is the one genuinely-new (but SHORT) piece.
2. **`basis_emb(betas)` free in `h1_base`.** ALREADY PROVEN — `lemma_basis_elt_free` (`free_basis.rs` 29/0),
   the headline free-basis lemma. Reused verbatim.
3. **F3 = `free_basis::lemma_free_to_embedding`** (a free-trivial `w` maps to `ε` under any valid embedding) —
   both directions.
4. **`betas.no_duplicates()`** side-condition (`0 ∉ alphas ∧ alphas.no_duplicates()`) so neither column has a
   repeated generator — needed by `lemma_config_emb_free`/`lemma_basis_elt_free` (both `require no_duplicates`).
   The `α=0`/`p_assoc` "overlap" is NOT a problem: `betas = [0]++alphas` unifies the special case into the
   family; just carry `0 ∉ alphas` (true in the C3.2c context where `alphas` are the β's `w` touches, all > 0).

**Concrete A1 sub-ladder (NEW module `f_free_a1.rs`):**
- [x] **`lemma_km_faithful_in_h1` — DONE** (`f_free_a1.rs` 2/0, 2026-06-22): the `kill_hom` retraction:
  `word_valid(w, nk) ∧ w ≡_{h1_base} ε ⟹ w ≡_{g_m} ε`. Three lines: `lemma_kill_hom_valid` (valid hom)
  → `lemma_hom_preserves_equiv` (`φ(w) ≡_{g_m} φ(ε)=ε`) → `lemma_kill_fixes_low` (`φ(w) =~= w`, since `w`
  is a low/K_M word). The "genuinely-new" piece — and it was short, as predicted.
- [x] **`lemma_config_emb_free_in_h1` — DONE** (`f_free_a1.rs`, same commit): config family free in
  `h1_base`. The embedded product `apply_embedding(config_emb,w)` is a `K_M`-word (config words on gens
  0–2 < nk, `lemma_config_word_valid` + `lemma_word_valid_mono` + `lemma_apply_embedding_valid`), so
  triviality in `h1_base` descends to `g_m` via rung 1, where `lemma_config_emb_free` (F2) closes it.
- [x] **`lemma_a_col_eq_config_emb` / `lemma_b_col_eq_basis_emb` — DONE** (`f_free_a1.rs`, 2026-06-22):
  the `betas=[0]++alphas` correspondence. Both columns are LITERAL seq-equal (`=~=`) to
  `config_emb(betas)` / `basis_emb(betas)`: head via `lemma_config_word_zero` (`config_word(0,0) =~=
  [Gen0]`) + `w_c(_,0)=ε` (so `basis_elt(0) =~= td_word`); tail `family_II_rhs(αᵢ) == basis_elt(αᵢ)`
  since `h_w_b = w_b(b_base…)` definitionally. Side facts also done: `betas` index (`lemma_betas_index`),
  `numbers_word(n,m,0)=true` so betas all number words (`lemma_betas_numbers_word`), and
  `betas.no_duplicates()` from `0∉alphas ∧ alphas.no_duplicates()` (`lemma_betas_no_duplicates`).
- [x] **`lemma_recog_associations_isomorphic` — DONE** (`f_free_a1.rs` 8/0, 2026-06-22): assembled. For
  `w` valid over `betas.len()`, `apply_embedding(a_words,w) ≡_{h1} ε ⟺ apply_embedding(b_words,w)
  ≡_{h1} ε`. Forward: rung 2 (`lemma_config_emb_free_in_h1`) ⟹ `w ≡_free ε` ⟹ `lemma_free_to_basis_elt`
  ⟹ b-side trivial. Backward: `lemma_basis_elt_free` ⟹ `w ≡_free ε` ⟹ `lemma_free_to_embedding(config_emb)`
  ⟹ a-side trivial. **A1 IS COMPLETE — `hnn_associations_isomorphic(recog_data)` holds.** The "hardest
  brick" was, as the de-risking predicted, a clean ~190-line focused arc that verified first try.

Once A1 lands, **B4** is immediate (`lemma_recog_data_valid` + A1 ⟹ `hnn_data` valid+iso ⟹ Britton over
`recog_data` applies to `h2_II`; F free `h1_base ↪ h2_II`), and the C-forward Britton peel + C-backward von
Dyck (the family-(II) payoff) follow per §3b. The old `prop_v`/`tower_peel`/`lemma_accumulator_inv` reuse
that this section used to anticipate is **NOT needed** — that machinery was already spent inside
`lemma_basis_elt_free`, which A1 now consumes wholesale. **A1 is a clean focused arc, not a multi-session crux.**

**B4 DONE 2026-06-22** (`f_free_a1.rs` 10/0): A1's direct payoff, both first-try.
- **`lemma_h1_faithful_in_h2_II`** — the reusable `h1_base ↪ h2_II` faithfulness (a `h1_base`-word trivial in
  `h2_II` is trivial in `h1_base`). = `lemma_single_hnn_base_faithful(recog_data, ·)` with A1 + `lemma_recog_data_valid`
  discharging its two preconditions, and `lemma_recog_presentation` (`hnn_presentation(recog_data)==h2_II`)
  routing the conclusion onto `h2_II`. This is the descent-to-base step the C-forward Britton peel leans on.
- **`lemma_f_free_in_h2_II`** — `F=[t,x,b_j,d]` free in `h2_II` (compose B3 `lemma_f_free_in_h1` with the
  faithfulness above): the embedded product is a `h1_base`-word, its `h2_II`-triviality descends, B3 closes it.

**NEXT = the C-forward / C-backward / C3 arc** (the substantial remaining work — a Britton-peel proof,
"`tower_peel`-sized", best as a fresh arc). C-forward: Britton-peel `p` over `recog_data` (now valid via A1)
to analyze `emb(a_words,w) ≡_{h2_II} ε` and descend; C-backward: von Dyck over `A`'s p-conjugations (the
family-(II) payoff, using `F` free in `h1_base` = B3 to make `A=HNN(F,p|family II)` the genuine subgroup
presentation); C3: biconditional `lemma_phi_l_iso_at_h2II`. Then C3.2d (`decreases l` faithfulness induction,
mirror `lemma_b_m_upto_faithful`) → C2(p-level)/C4(Fork-B k-engine)/C5.

## 5. The C-arc — `lemma_phi_l_iso_at_h2II` via a UNIFIED HNN lifting lemma (design locked 2026-06-22, w/ Danielle)

The crux is the biconditional, over `h2_II`, for every `w` valid over `n+4`:
```
emb(a_words, w) ≡ ε   ⟺   emb(b_words, w) ≡ ε
```
with `a_words = [t,x,d,b_j,p]` (literal generators), `b_words = φ_l(a_words) = [t_l, xᵐ, b_l·d, b_j, p]`,
and (B1.5) `emb(b_words,w) = φ_l(emb(a_words,w))`.

**Decision (Danielle's review): Option A — abstract presentation + ONE unified lifting lemma**, NOT two
separate inline Britton inductions. Build the abstract `P_A = HNN(F = free_group(n+3), p | family II over F)`
(generators `t=0, x=1, d=2, b_j=2+j, p=n+3`; the family-II associations are F-words since `config(β,0)=x⁻ᵝtxᵝ`
uses `t,x` and `w_β(b)·d` uses `b_j,d`). Then both directions chain through `w ≡_{P_A} ε`:
```
emb(a_words,w) ≡_{h2_II} ε  ⟺ (map_a faithful) w ≡_{P_A} ε  ⟺ (map_b faithful) emb(b_words,w) ≡_{h2_II} ε
```
So the crux = **two faithful embeddings of `P_A` into `h2_II`** (`map_a` = inclusion, `map_b` = φ_l), each a
biconditional `emb(map, w) ≡_{h2_II} ε ⟺ w ≡_{P_A} ε`.

### The unified lifting lemma (the deep core, the "tower_peel-sized" Britton-peel)
Prove ONCE (parametric over the base-map ψ: F → h1_base):
> If ψ: F → h1_base is a faithful embedding, ψ preserves the family-II associations (sends `P_A`'s
> association subgroups into `h2_II`'s, matching the recog_data columns), and the **intersection
> property** ψ(F) ∩ AssocSub(h2_II) = ψ(AssocSub(P_A)) holds, THEN the induced map
> `P_A = HNN(F,p|·) → h2_II = HNN(h1_base,p|·)` is a faithful embedding.

Proof = the Britton-peel induction on `w.len()` (mirror `lemma_psi_A_injective`): peel `p`-stable letters of
`emb(map,w)`; a pinch `p⁻¹·ψ(mid)·p` forces `ψ(mid) ∈ AssocSub(h2_II)`, so by the intersection property
`mid ∈ AssocSub(P_A)` ⟹ `w` had a pinch; pinch out, recurse. The base case (no `p`) = `single_hnn_base_faithful`
+ F-freeness (B3). **The intersection property is the real content** and is where the iso A1 + F-freeness enter.

### Instantiation
- **map_a** (ψ_a = inclusion `F ↪ h1_base`): faithful = B3 (`lemma_f_free_in_h1`/`lemma_f_free_in_h2_II`);
  preserves associations trivially (the F-words ARE recog_data's columns).
- **map_b** (ψ_b = φ_l restricted to F: `t↦t_l, x↦xᵐ, d↦b_l·d, b_j↦b_j`): faithful = φ_l injective on F (the
  digit-scaling endo, `lemma_psi_A_injective`-style); preserves associations via the **digit-scaling +
  numbering identities** (this brick).

### Concrete bricks (ordered)
- [x] **C-a (`phi_l_iso.rs` 2/0)** — `lemma_phi_l_on_config_zero`: `φ_l(config(β,0)) =~= config(mβ+l,0)`
  (the digit-scaling word identity; von-Dyck-b's algebraic core). `lemma_config_zero_form` support.
- [x] **C-b word core (`phi_l_iso.rs` 6/0)** — `lemma_phi_l_on_family_II_rhs`: `φ_l(family_II_rhs(β)) =~=
  family_II_rhs(mβ+l)`. C-a + b-block fixing (`lemma_phi_l_fixes_w_b` via `lemma_w_c_gens_in_block` + the
  general `lemma_apply_embedding_fixes`) + `φ_l(d)=b_l·d` + numbering snoc `lemma_w_b_snoc`.
- [x] **C-b relator word core (`phi_l_iso.rs` 8/0)** — `lemma_phi_l_on_family_II_relator`:
  `φ_l(family_II_relator(β)) =~= family_II_relator(mβ+l)` (LHS half `lemma_phi_l_on_family_II_lhs` =
  C-a + φ_l fixes p; combine via `apply_embedding` over concat/inverse). So when `mβ+l ∈ alphas` the
  image is a LITERAL `h2_II` relator (`≡ ε`).
- [x] **C-b group lift — DONE** (`phi_l_iso.rs` 10/0, 2026-06-22): `lemma_phi_l_relator_equiv_empty`
  (`φ_l(family_II_relator(β)) ≡_{h2_II} ε` when `mβ+l ∈ alphas`) + support `lemma_family_II_relator_in_h2_II`
  (a relator in the finite augmentation is trivial in `h2_II = add_relators(h2_pres, family_II(alphas))`, via
  `lemma_add_relators_relators` + `lemma_relator_is_identity`).  This is von-Dyck-b's homomorphism condition
  in `h2_II`-indexing; the `pa_data`-routed assembly (below) consumes it.
- [x] **C-P_A — define `pa_data` + validity — DONE** (`pa_data.rs` 2/0, 2026-06-22). `pa_data(n,m,gammas)
  = HNN(free_group(n+3), p | family II over F)`, F-indexed `[t=0,x=1,d=2,b_j=2+j,p=n+3]`; associations
  `(config(γ,0), config(γ,0)·w_c(3,n,m,γ)·[Gen2])`.  `lemma_pa_data_valid` + `lemma_pa_data_shape`.
  **CORRECTION (this session): `gammas = betas(alphas) = [0]++alphas`, NOT `alphas`** — `recog_data`'s
  associated subgroups are over `betas` (A1: columns = `config_emb(betas)`/`basis_emb(betas)`, the `α=0`
  head = the `p_assoc` relation `p⁻¹tp=td`).  For the lifting lemma's pinch to descend index-for-index, `P_A`
  must match `recog_data`, so it is over `betas`; the `β=0` case (`config(0,0)=t`, `w_0(b)=ε`) recovers the
  `(t,td)` head.  **The iso `hnn_associations_isomorphic(pa_data)` is NOT needed** — Britton in the lifting
  lemma runs over `recog_data` (TARGET, iso = A1 done), never over `pa_data`.
- [x] **map_a faithful — DONE** (`phi_l_maps.rs` 4/0, 2026-06-22). `lemma_map_a_faithful`:
  `a_words_F = [t,x,d,b_j]` (the F-part of `a_words`, the literal inclusion) is FREE in `h1_base`.
  Route A: B3 (`lemma_f_free_in_h1`, `[t,x,b_j,d]`) + **`free_family_perm::lemma_free_family_permute`**
  (`free_family_perm.rs` 4/0, NEW — free families invariant under generator reordering, via F3 +
  relabeling embeddings) with `pa_sigma` moving `d` from last to index 2.  This is the `ψ_a` hypothesis of
  the lifting lemma. **map_a (full) = `a_words_F.push([Gen(p_idx)])` = `a_words`** (the `p ↦ p` extension).
- **von-Dyck backwards (the easy half of C-lift)** — `w ≡_{P_A} ε ⟹ emb(map,w) ≡_{h2_II} ε`, both maps,
  via `lemma_emb_respects_source_equiv(hnn_presentation(pa_data), h2_II, map, w, ε)`.  The discharge needs the
  **association-preservation**: `apply_embedding(map_a, hnn_relator(pa_data,j)) =~= family_II_relator(gammas[j])`
  (= `hnn_relator(recog_data,j)`), which is `≡_{h2_II} ε`.
  - [x] **`w_c`-relabel — DONE** (`phi_l_maps.rs` 7/0): `lemma_a_words_relabel_wc`
    (`apply_embedding(a_words, w_c(3,n,m,γ)) =~= w_c(nk+n,n,m,γ)`; induction on `γ`, digit sub-step
    `lemma_a_words_on_alpha_letter` = b-block shift `Gen(3+j)↦Gen(nk+n+j)` + `lemma_a_words_bblock`).  Full
    map `a_words = a_words_F.push([Gen(p_idx)])` also defined here.
  - [x] **column translations — DONE** (`phi_l_maps.rs` 10/0): `lemma_a_words_fixes_config` (a-column:
    `a_words` fixes `config(γ,0)`) + `lemma_a_words_on_pa_rhs` (b-column: `ae(a_words, pa_rhs(γ)) =~=
    family_II_rhs(γ)`, via relabel + config-fix + `d=Gen2 ↦ Gen(d_idx)`) + `lemma_a_words_head` support.
  - [ ] **REMAINING**: (i) the `hnn_relator` assembly `ae(a_words, hnn_relator(pa_data,j)) =~=
    family_II_relator(gammas[j])` (peel `hnn_relator = [Inv(n+3)]+a_col+[Gen(n+3)]+inverse(b_col)`; `a_words`
    on `Gen(n+3)/Inv(n+3) = p ↦ Gen(p_idx)`, on `a_col=config` via fixes_config, on `inverse(b_col=pa_rhs)`
    via `on_pa_rhs` + `lemma_apply_embedding_inverse`); (ii) **`family_II_relator(0) ≡_{h2_II} ε`** (the
    `γ=0` / `p_assoc` head case: `family_II_relator(0) = p⁻¹tp(td)⁻¹` = the `h2_pres` p-relator, a prefix
    relator of `h2_II`; needs unfolding `h2_pres`/`h2_data`/`p_assoc` in `h2.rs` + `lemma_config_word_zero`
    + `w_c(_,0)=ε`); for `γ∈alphas` it's `lemma_family_II_relator_in_h2_II` (DONE, `phi_l_iso.rs`); (iii) the
    `lemma_emb_respects_source_equiv` wiring (validity preconds + `src.relators[j]=hnn_relator(pa_data,j)`).
    For **map_b**: the b-side column translations are the C-b word cores (`lemma_phi_l_on_family_II_rhs` etc.,
    DONE); the relator triviality is the C-b group lift (`lemma_phi_l_relator_equiv_empty`, DONE) `≡_{h2_II} ε`
    when `m·γ+l ∈ alphas`.
- [ ] **C-lift forward — the unified HNN lifting lemma** (the deep Britton-peel, the BOTTLENECK). Mirror
  `lemma_psi_A_injective` (`machine_group.rs:6265`) + `lemma_psi_A_pinch_descends` (`:5893`):
  `emb(map,w) ≡_{h2_II} ε ⟹ w ≡_{P_A} ε`, `decreases w.len()`.  Recognize `h2_II = hnn_presentation(recog_data)`
  (B1), peel `p`-stable letters.  **Base case** (`stable_count(pa_data,w)==0`, w an F-word): `emb(ψ,w)≡_{h2_II}ε`
  ⟹ (B4 `lemma_h1_faithful_in_h2_II`) `≡_{h1_base}ε` ⟹ (ψ faithful = map_a/map_b free) `w≡_{free(n+3)}ε` ⟹
  (`lemma_base_embeds_in_hnn`) `w≡_{P_A}ε`.  **Step case**: `britton_lemma_full(recog_data, emb(map,w))` ⟹
  has_pinch ⟹ **the pinch descends to a pinch in `w` over `pa_data`** (mirror `lemma_psi_A_pinch_descends`)
  ⟹ pinch out, recurse.  **The intersection property is the real content**, living in the spanning case of
  pinch-descent: the pinch middle `ψ(w-mid) ∈ AssocSub(h2_II)=⟨recog cols⟩` ⟹ (ψ-faithful + F-freeness +
  column translation) `w-mid ∈ AssocSub(P_A)=⟨pa cols⟩`.  Reuse the GENERIC helpers
  `lemma_strip_prefix_preserves_pinch`/`lemma_prepend_preserves_pinch` (check they're generic over HNNData
  — the template instantiates them at `a_as_hnn`).  **map_b faithful = ψ_a faithful + φ_l-injective-on-free-F**
  (a real simplification: `map_b = ψ_a ∘ φ_l`, `emb(b_words,w)=ψ_a(φ_l(w))≡_{h1}ε ⟹ (ψ_a faithful) φ_l(w)≡_F ε
  ⟹ (φ_l inj on free F) w≡_F ε`; the φ_l-injectivity is a `lemma_psi_A_injective`-style peel over the FREE
  group `F`, NOT over h1_base — much cleaner; the K_M machine relators never enter since `F` is free).
- [ ] **C-asm — `lemma_phi_l_iso_at_h2II`**: instantiate C-lift at map_a, map_b; chain through `w ≡_{P_A} ε`.
  Bookkeeping: relate `a_words`/`b_words` (= `phi_assoc` columns, the crux's literal lists) to
  `a_words_F.push([p])` / `b_words_F.push([p])` (the map forms).
- [ ] **C3.2d** — `decreases l` outer induction (mirror `lemma_b_m_upto_faithful`): build `hnn_associations_isomorphic(phi_l_data)`
  at each level from C-asm (bottom crux over `h2_II`) + IH-descent (`lemma_single_hnn_base_faithful` +
  `lemma_h2II_equiv_lifts_to_tower`) → C2/C4/C5.

**Finite-slice side condition** (`alphas`): von-Dyck-b needs `m·γ+l ∈ alphas` for each `γ ∈ betas` that `w`'s
relators touch (so the image relation is present in the finite augmentation).  NOTE the `γ=0` case gives
**`l ∈ alphas`** (since `m·0+l = l`).  Bake `{l} ∪ {m·α+l : α∈alphas} ⊆ alphas` into the crux's `requires`;
C4 picks the concrete finite set.
