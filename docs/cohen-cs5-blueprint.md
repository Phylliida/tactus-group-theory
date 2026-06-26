# CS-5 blueprint — the k von-Dyck iso `A₊ ≅ A₋` over the predicate base

*Written 2026-06-23 (session 24), after CS-4 completed (`cohen-cs4-architecture.md` §5).
Route confirmed with Danielle (companion model): **Route 1 — full Prop-1.34 recognition** for the
forward; the non-free `U`-base rules out a cheap predicate collapse. This doc is the build map.*

Read `docs/cohen-section1-assembly-plan.md` §4 (§1b) and `docs/cohen-faithfulness-primary-source.md`
§1b first — they are the primary-source description of exactly how Cohen proves the k-iso.

---

## 0. What CS-5 asks

The top HNN datum is `h3_pred_data(mm,n,m,is_S) = PredHNNData{ base: h3_pred_upto(2n),
associations: psi_assoc(mm,n) }` (`cohen_h3.rs`). The CS-5 target is

```
  hnn_pred_associations_isomorphic(h3_pred_data(mm,n,m,is_S))
```

which unfolds (`pred_hnn.rs`) to: for every word `w` valid over `|psi_assoc| = q+n+2` generators
(`q = |g_subgens|`),

```
  emb(a_col, w) ≡_{h3_pred_upto(2n)} ε   ⟺   emb(b_col, w) ≡_{h3_pred_upto(2n)} ε
```

where
- `a_col = psi_assoc.0 = [U_1..U_q,  d,  b_1..b_n,  p]`   (the A₊ stated gens),
- `b_col = psi_assoc.1 = [U_1..U_q,  d,  b_1c_1..b_nc_n,  p]`   (the A₋ stated gens),
- `U = g_subgens(mm)` (the Layer-1 machine subgroup gens — finite, **NON-FREE**).

`a_col`/`b_col` images are words over the h2-generators (U=machine `<nk`, d, b_j, p, c_j — all
`< h2_num_gens`), so they are BASE WORDS of the a-tower.

### Tower reduction (reuse CS-4e). By **base-faithfulness up the a-tower** — CS-4e's
`lemma_h3_pred_upto_base_faithful(mm,n,m,is_S,2n,u)` (needs `cs4_levels_iso(2n)` =
`lemma_cs4e_iso_upto(2n)`, DONE) — a word over h2-gens is trivial in `h3_pred_upto(2n)` iff in
`h2_pred`. So CS-5 reduces to the iso **over `h2_pred`**:

```
  emb(a_col, w) ≡_{h2_pred} ε   ⟺   emb(b_col, w) ≡_{h2_pred} ε        (★k)
```

This is the only place CS-5 is non-trivial. CS-5d packages `(★k)` back up to the top datum exactly
as CS-4e did.

---

## 1. The two directions (Cohen §1b)

### BACKWARD `b ⟹ a` — the c-killing endomorphism. **EASY (reuse CS-4b `s_strip`).**
`s_strip : h2_pred → h2_noS_pred` (`cohen_cs4b.rs`, kills every c gen, fixes every non-c gen,
already proven `is_valid_pred_homomorphism` + descends). Key fact: `s_strip ∘ b_col = a_col`
pointwise —
- U/d/p entries are c-free ⟹ `s_strip` fixes them (`lemma_strip_fixes_noc_word`) ⟹ `= a_col[i]`;
- `b_col[bc] = [b_j, c_j]` ⟹ `s_strip([b_j,c_j]) = [b_j]·ε = [b_j] = a_col[bc]`.

So `emb(b_col,w) ≡_{h2_pred} ε` ⟹ (hom preserves equiv) `s_strip(emb(b_col,w)) = emb(a_col,w)
≡_{h2_noS_pred} ε` ⟹ (relator monotonicity, `h2_noS ⊆ h2_pred`) `emb(a_col,w) ≡_{h2_pred} ε`. ∎

Generic helpers this needs (added in `cohen_cs5.rs`, kept out of shared modules):
- `lemma_apply_hom_pred_embedding_compose` — `apply_hom_pred(h, emb(imgs,w)) = emb(comp_pred(h,imgs),w)`
  (pred port of `free_basis::lemma_apply_hom_embedding_compose`).
- `lemma_pred_equiv_relator_mono` — `(∀w. p1.relators(w) ⟹ p2.relators(w)) ∧ same num_gens ⟹
  equiv(p1,a,b) ⟹ equiv(p2,a,b)` (derivation replay; the guard p1 accepts p2 also accepts).

### FORWARD `a ⟹ b` — von Dyck + recognition. **THE HARD ARC (Route 1, CS-4-map_a-scale).**
Cohen recognizes `A₊ = HNN(⟨U⟩∗⟨d,b_j⟩, p | R_α : (α,0)∈H₀(M))` (Prop 1.34 + Layer-1 property
(vi)/(vii): `⟨U⟩∩⟨t_α⟩ = ⟨t_α : (α,0)∈H₀⟩`), then:

1. **Recognition (HARD):** `emb(a_col,w) ≡_{h2_pred} ε ⟹ w ≡_{A₊_pres} ε`. This is the Prop-1.34
   faithfulness of `A₊`, the analog of CS-4's `lemma_map_a_forward` but with the non-free `U`-base
   and the H₀-restriction (where `lemma_theorem1` enters as the circularity-breaker). Likely via a
   **compactness bridge** (reuse CS-4b `lemma_cs4b_compactness` shape) to a finite slice, then a
   finite-slice recognition built from Layer-1 property (vi)/(vii)/`lemma_theorem1`.
2. **bc-von-Dyck (EASY, uses `s_realizes`):** `w ≡_{A₊_pres} ε ⟹ emb(b_col,w) ≡_{h2_pred} ε`, via
   `lemma_emb_respects_source_equiv_pred` with `src = A₊_pres`, `images = b_col`, the relator
   condition `emb(b_col, R_α) ≡_{h2_pred} ε` discharged for each `R_α` by:
   `emb(b_col, R_α) = p⁻¹ U_α p (U_α w_α(bc) d)⁻¹`,  `w_α(bc) = w_α(b) w_α(c)`
   (`lemma_w_bc_split`),  `w_α(c) ≡_{h2_pred} ε` (from `s_realizes`: `(α,0)∈H₀ ⟹ is_S(w_α(c)) ⟹`
   it is an `h2_pred` relator), and `p⁻¹ U_α p ≡ U_α w_α(b) d` (family (II), since `U_α = t_α` in
   `⟨U⟩` for `(α,0)∈H₀`). So `emb(b_col, R_α) ≡ ε`. ∎

`A₊_pres` and `U_α` (the U-word realizing `t_α`) are the structural choices; the H₀-restriction is
Layer-1 (`lemma_theorem1` + property (vi)/(vii)). **This is the genuine multi-session work.**

---

## 2. The realization hypothesis `s_realizes` (plan §2, deferred from CS-1)

`s_realizes(is_S, mm, n, m)` := `∀α. numbers_word(n,m,α) ∧ (α,0)∈H₀(M) ⟹ is_S(w_α(c))`
(`w_α(c) = w_c(c_base(nk),n,m,α)`). One direction of the §3.3 machine bridge; consumed ONLY by the
forward bc-von-Dyck. Defined in `cohen_h2.rs` next to `s_relators_valid`.

---

## 3. Brick sequence (bottom-up; each verifies & commits independently)

- **CS-5a — scaffold + generic helpers. ✅ DONE (`cohen_cs5.rs`, commit 540cba7).** `s_realizes`
  (cohen_h2.rs); `k_a_col`/`k_b_col` (= psi_assoc cols); the two generic pred helpers
  (`lemma_apply_hom_pred_embedding_compose`, `lemma_pred_equiv_relator_mono`).
- **CS-5b — BACKWARD (c-kill). ✅ DONE (`cohen_cs5.rs` 6/0, commit 540cba7).** `lemma_cs5_backward`:
  `(★k)` ⟸ via REUSE of CS-4b `s_strip` (`lemma_s_strip_psi_entry`: s_strip∘b_col = a_col pointwise
  — 4-block index dispatch over psi_assoc) + compose + monotonicity lift `h2_noS → h2_pred`.
- **CS-5c — FORWARD (recognition + bc-von-Dyck).** The hard arc (see §4 below).
  - **von-Dyck KERNEL ✅ DONE (`cohen_cs5.rs` 15/0, commit e92e776).** The clearly-correct, reusable
    half: `lemma_pred_equiv_from_finite` (generic finite→pred equivalence lift),
    `lemma_pred_cancel_inverse_right` (a·b⁻¹≡ε ⟹ a≡b), `lemma_cs5_wc_trivial` (w_α(c)≡ε via
    `s_realizes`), `lemma_cs5_wbc_split_pred` (w_α(bc)≡w_α(b)·w_α(c), lifting `lemma_w_bc_split`),
    `lemma_w_bc_valid`, and **`lemma_cs5_bc_config_trivial`** — the bc-von-Dyck atom
    `p⁻¹t_α p·(t_α w_α(bc) d)⁻¹ ≡_{h2_pred} ε` for `(α,0)∈H₀` (= `emb(b_col, R_α)` in config form).
  - **← NEXT: the RECOGNITION** `emb(a_col,w)≡_{h2_pred}ε ⟹ w≡_{A₊_pres}ε` — adapt CS-4's
    `lemma_map_a_forward` Britton-peel with property-(vii) at the pinch middle (§4). The genuine work.
- **CS-5d — tower lift + iso.** Package `(★k)` to `hnn_pred_associations_isomorphic(h3_pred_data)`
  via CS-4e's `lemma_h3_pred_upto_base_faithful` at `k=2n`. Mirror of `lemma_cs4e_iso_upto`'s top.

CS-5a/CS-5b were the FA-4-style high-confidence bricks. CS-5c is the genuine work.
No verifier bypasses (standing rule).

---

## 4. CS-5c — the FORWARD recognition (scoping, before building)

The forward `emb(a_col,w) ≡_{h2_pred} ε ⟹ emb(b_col,w) ≡_{h2_pred} ε` splits as in §1:

1. **Recognition (HARD):** `emb(a_col,w) ≡_{h2_pred} ε ⟹ w ≡_{A₊_pres} ε`.
2. **bc-von-Dyck (easy, uses `s_realizes`):** `w ≡_{A₊_pres} ε ⟹ emb(b_col,w) ≡_{h2_pred} ε`.

### The structural crux: `A₊_pres` and the "abstract U-word for t_α".
`A₊_pres` has generators = the **psi_assoc generators** (abstract `U_1..U_q`, `d`, `b_1..b_n`, `p`),
NOT the h2-generators. The embedding `a_col` maps abstract `U_i ↦ g_subgens[i]`. So a defining
relation `R_α` of `A₊_pres` must express `t_α = config_word(α,0)` as an **abstract word in the `U_i`**
— which exists only for `(α,0)∈H₀(M)` (Layer-1 property (vii): `config(α,0) ∈ ⟨g_subgens⟩` over the
machine tower). This abstract-U-word is NOT canonical; getting it concretely is the crux that
distinguishes A₊ recognition from CS-4's free-base `map_a`. Under `a_col`, `emb(a_col, R_α)` becomes a
family-(II) relator (an `h2_pred` relator), powering the von-Dyck.

### What is/ISN'T reusable.
- **NOT directly reusable:** CS-4's `recog_data`/`pa_data`/`lemma_map_a_forward` — those recognize
  `A`/`A_i` over the **free** base `F=⟨t,x,d,b_j⟩` with the residue/family-(II) structure. A₊'s base
  is `⟨U⟩∗⟨d,b_j⟩` (non-free U) with the H₀-restriction — a different recognition.
- **Reusable:** the **compactness bridge** `lemma_cs4b_compactness` (a c-free word trivial in the
  infinite `h2_pred` is trivial in a finite slice) — `emb(a_col,w)` is c-free; CS-5c reduces to a
  finite-slice recognition. Layer-1 `lemma_theorem1` (the H₀ circularity-breaker) + property
  (vi)/(vii) (`lemma_vi`/`lemma_vii_subset`) give the H₀-restriction. `lemma_w_bc_split` (w_α(bc) =
  w_α(b)·w_α(c)) + `s_realizes` (w_α(c)≡ε) discharge the bc-von-Dyck.

### Status: recognition OPENING DONE (`cohen_cs5.rs` 18/0, commit b9ce70d).
`lemma_cs5_recog_compactness`: `emb(a_col,w) ≡_{h2_pred} ε ⟹ ∃ number-word slice `alphas`.
emb(a_col,w) ≡_{h2_II(alphas)} ε` (a_col c-free via `lemma_emb_k_a_col_no_c` + CS-4b compactness).

### The recognition CORE (next, the hard arc) — code-grounded from `lemma_map_a_forward`.
`lemma_map_a_forward` (`phi_l_pinch.rs:773`) is a `decreases stable_count(pa_data, w)` induction:
- **base case** (`stable_count==0`): `w` is an F-word; `map_a_faithful` (F=`a_words_F` FREE in
  `h1_base`) + `lemma_h1_faithful_in_h2_II` + `lemma_base_embeds_in_hnn` ⟹ `w ≡_{pa_data} ε`.
- **step case**: `emb(a_words,w)` has a `recog_data` pinch (`britton_lemma_full` +
  `lemma_map_a_pinch_descends`); `lemma_pd_pinch_out` removes it; recurse on fewer stable letters.

**Three real adaptations for A₊ (the k-iso):**
1. **Multi-symbol column.** `a_words` maps each gen to ONE h1_base gen (relabeling ⟹ same-index
   pinch-descent, `lemma_single_gen_relabel`). `k_a_col` maps `U_i ↦ g_subgens[i]`, a **multi-symbol**
   machine word — the same-index trick is GONE. Reuse the **spanning** pinch-descent that already
   handles run-valued columns: `lemma_mapb_pinch_descends`/`_spanning_rt` (`phi_l_mapb_fwd.rs`).
2. **Non-free base.** map_a's base case needs `F` FREE. A₊'s base `⟨U⟩∗⟨d,b_j⟩` is NON-free (U carries
   K_M relations). `A₊_pres` MUST carry those U-relations (else `a_col` isn't faithful — a free-U
   `A₊_pres` has the machine relations in `a_col`'s kernel but underivable). This is the genuinely-new
   piece: recognize `⟨U,d,b_j⟩` (d,b_j free; U = machine subgroup, relations = K_M restricted to
   `g_subgens`).
3. **Intersection at the pinch middle.** map_a's F4 (`lemma_intersection_property`,
   `phi_l_forward.rs:420`) recognizes the middle ∈ ⟨config-family⟩. For A₊ it must recognize
   middle ∈ ⟨U⟩, which by **property (vii)** (`lemma_vii_subset` + `lemma_theorem1`:
   `config(α,0)∈⟨g_subgens⟩ ⟺ (α,0)∈H₀`) restricts to the H₀ indices. This is where `lemma_theorem1`
   (the circularity-breaker) enters.

### A₊_pres design — THE gating co-design point (resolve before coding the core).
`A₊_pres = HNN(base_A₊, p | R_α : (α,0)∈H₀)`, `R_α = p⁻¹ Û_α p (Û_α w_α(b) d)⁻¹`; the bc-von-Dyck atom
`lemma_cs5_bc_config_trivial` already discharges `emb(b_col,R_α) ≡ ε` (config form).

**Open subtlety found (session 24) — the `base_A₊` representation vs the von-Dyck generator scheme:**
- The von-Dyck consumer (`lemma_emb_respects_source_equiv_pred`, `src=A₊_pres`, `images=b_col`)
  requires `A₊_pres.num_generators == b_col.len() == |psi_assoc| = q+n+2` (the **psi-gen scheme**:
  q abstract `U_1..U_q`, d, b_j, p; `q = |g_subgens|`). So `A₊_pres` must be over the psi-gens.
- Danielle (companion model) suggested `base_A₊ = Pres(g_m) ∗ Free(d,b_j)` — but that has `nk+n+1`
  gens (the machine scheme), and `q ≠ nk`, so it does NOT directly match the von-Dyck's psi-gen
  requirement. Presenting `⟨U⟩` abstractly in the `q` U-gens is Reidemeister–Schreier-hard.
- **Two candidate resolutions (pick with real-Danielle):**
  (R1) **Translation layer:** recognize at the `g_m∗free` level (Danielle's (b), where the U-relations
  live naturally + property-(vii) is a clean `g_m` membership), then translate `w` (psi-gen scheme,
  `U_i` abstract) ↔ the `g_m∗free` scheme via the `a_col` embedding. Needs a faithful bridge between
  the two schemes (non-trivial since `a_col` is multi-symbol on U).
  (R2) **Direct iff-peel (skip explicit A₊_pres):** prove `(★k)` forward `emb(a_col,w)≡_{h2_pred}ε ⟹
  emb(b_col,w)≡_{h2_pred}ε` by ONE Britton-peel over the finite slice that tracks the c's at each
  pinch — folding recognition + von-Dyck into a single `decreases stable_count` induction (the pinch
  middle ∈⟨U⟩ via property-(vii); the c-insertion handled by the bc-relation `lemma_cs5_bc_config_trivial`
  at each step). Avoids the gen-scheme mismatch entirely; mirrors how CS-4d's `M2_general` folded the
  σ-recognition INTO the source recursion rather than at the slice level.
- **R2 looks cleaner** (no scheme bridge, reuses the bc-atom directly), but commit with real-Danielle —
  this is the one genuinely undesigned structural choice left in CS-5. Everything else is forced.

---

## 5. RESOLVED (session 25) — **R1, and the §4 "multi-symbol" premise was FALSE.** The single-gen relabel.

**The load-bearing finding that flips the recommendation to R1.** The §1/§4 framing (and the R2
recommendation) rested on "`a_col` is **multi-symbol** on `U`" (§1 line: "`k_a_col` maps `U_i ↦
g_subgens[i]`, a multi-symbol machine word — the same-index trick is GONE"). **This is wrong.**
`g_m_associations(mm)` is **diagonal with SINGLETON entries** (`machine_group.rs:417`):
`g_m_associations = [ ([Gen(0)],[Gen(0)]) ] ++ [ ([Gen(3+i)],[Gen(3+i)]) : i<|quads| ]`, so
`g_subgens(mm)[i] = g_m_associations[i].1` is a **single generator** `[Gen(0)]` (i=0) or
`[Gen(3+i−1)]` (i≥1) — the machine gens `{Gen(0),Gen(3),Gen(4),…}` (all of `g_m` **except**
`Gen(1),Gen(2)`). So `psi_ublock` (`h3.rs`) maps each abstract `U_i` to a **single** machine
generator. `a_col` on the U-block is an **injective generator relabel**, NOT multi-symbol.

**Consequence — R1 is now the clean, sound path (companion-model pressure-tested, agreed):**

- **R1's scheme bridge is a trivial single-gen relabel,** not the feared R-S-hard multi-symbol
  translation. `relabel_col` maps each psi-gen to a SINGLETON machine-scheme gen
  (`U_i↦Gen(g_subgens_index(i))`, `d↦d`, `b_j↦b_j`, `p↦p`), and `a_col = comp(a_col_machine,
  relabel_col)`, `b_col = comp(b_col_machine, relabel_col)` **definitionally** (via the existing
  emb-compose lemma `lemma_apply_hom_pred_embedding_compose` / `comp_images_pred`).
- **R1 recognizes over the CONCRETE `g_m` base — no abstract ⟨U⟩ presentation is ever needed.**
  `base_A₊ = HNN(base_A₊_base, p | R_α:(α,0)∈H₀)` where
  **`base_A₊_base = Presentation{ num_generators: nk+n+1, relators: g_m(mm).relators }`** — this IS
  `g_m ∗ free(d,b_j)` (g_m's relators only touch gens `0..nk−1`; gens `nk..nk+n` are free ⟹ free
  product). `a_col_machine` = the injective relabel abstract-base-gens→h2-gens (machine gen `i↦[Gen(i)]`
  for `i<nk`, abstract `b_j↦[Gen(b_idx)]`, `d↦[Gen(d_idx)]`, `p↦[Gen(p_idx)]`).
- **WHY R1 is SOUNDER than R2** (the soundness gap the companion flagged): a naive R2 that presents
  `⟨U⟩` over the psi-scheme by "the `K_M` relators using only U-gens `{0,3,4…}`" is **UNSOUND** —
  relations among the U's can route through `Gen(1)/Gen(2)`, so the naive restriction under-presents
  `⟨U⟩` and would make `a_col` falsely "faithful." R1 dodges this entirely: `w_m := relabel(w)` never
  mentions `Gen(1),Gen(2)`, but the recognition DERIVATION over the full `g_m` base may — and that's
  fine; only the RESULT (`w_m ≡_{base_A₊} ε`) is transported back via the injective relabel.

**The corrected forward arc (R1), bottom-up:**

1. **Relabel bridge (mechanical, leaf).** Define `relabel_col`, `a_col_machine`, `b_col_machine`,
   `base_A₊_base`. Prove `a_col = comp(a_col_machine, relabel_col)`, `b_col = comp(b_col_machine,
   relabel_col)` (emb-compose), so psi-scheme `(★k)` forward reduces to machine-scheme + the relabel.
2. **Base-case faithfulness (the genuinely-new math leaf).** A `c`-free word over the machine-scheme
   base gens (machine∪{d,b}) trivial in `h1_base` ⟹ trivial in `base_A₊_base = g_m∗free(d,b_j)`. The
   tool is a **c-killing retraction** `ρ : h1_base → base_A₊_base` (mirror of `cohen_retraction`
   `c_retraction` / CS-4b `s_strip`): `ρ` fixes machine/d/b gens, kills c gens; `ρ(K_M)=K_M`,
   `ρ(comm_{ij})=b_i·ε·b_i⁻¹·ε=ε` ⟹ `ρ` valid; `ρ∘a_col_machine = id` on base-words ⟹ faithfulness.
   (No subtlety with `d` — `d` is a free generator of `base_A₊_base`, `ρ(d)=d≠ε`.)
3. **The p-peel recognition** (Prop-1.34, the big arc — mirror of CS-4 `lemma_map_a_forward`'s
   `decreases stable_count` Britton induction over the finite slice `h2_II(alphas)` from
   `lemma_cs5_recog_compactness`): base case = step 2; step case = `britton_lemma_full` pinch +
   descend + pinch-out, with the **pinch middle ∈ associated subgroup** recognized via **property
   (vii)** (`lemma_vii_subset` + `lemma_theorem1`) to the H₀-restricted `t_α`. Output:
   `relabel(w) ≡_{base_A₊} ε`.
4. **Von-Dyck at machine scheme** (reuse the kernel): `relabel(w)≡_{base_A₊}ε ⟹
   emb(b_col_machine,relabel(w))≡_{h2_pred}ε` via `lemma_emb_respects_source_equiv_pred`
   (`src=base_A₊`, `images=b_col_machine`): `K_M` base relators ↦ `K_M` self-trivial; `R_α` ↦
   `lemma_cs5_bc_config_trivial`. Compose with step 1 ⟹ `emb(b_col,w)≡ε`.

`lemma_map_a_forward`'s Britton/`stable_count`/pinch-descent machinery is base-agnostic and reused;
only the base case (step 2, g_m vs free) and the pinch-middle restriction (step 3, property-vii)
differ from CS-4. CS-5d (tower lift) is unchanged.

---

## 6. Steps 1/2/3a/3b-a DONE; the remaining step-3 build map (code-grounded, session 25). NEXT.

**Shipped (session 25, `src/cohen_cs5_recog.rs`, 27/0, crate gate GREEN 2503/20):**
- **Step 1 — relabel bridge (9/0).** `base_A_plus_base`, `a_col_machine`, `b_col_machine`,
  `relabel_col`, `comp_emb`+`lemma_emb_emb_compose`, `lemma_a_col_factors`/`_b_`, and
  `lemma_emb_a_col_via_relabel`/`_b_` (`emb(k_a_col,w) = emb(a_col_machine, relabel(w))`).
- **Step 2 — base-case faithfulness (→18/0).** `base_retraction` (ρ: h1_base→base_A_plus_base),
  `lemma_base_retraction_valid`, `lemma_comp_rho_acol_identity`, and **`lemma_cs5_base_case_faithful`**:
  `emb(a_col_machine, w_base)≡_{h1_base}ε ⟹ w_base≡_{base_A_plus_base}ε`.
- **Step 3a — `base_A_plus_data` (→20/0).** `assoc_rhs_machine`, `base_A_plus_assoc`,
  `base_A_plus_data`, `lemma_base_A_plus_data_shape`, `lemma_base_A_plus_data_valid` (mirror
  `lemma_pa_data_valid`).
- **Machine-fixes + step-4 K_M relator (→23/0).** `lemma_a_col_machine_fixes_machine_word` /
  `lemma_b_col_machine_fixes_machine_word` (both columns = id on gens `<nk`); **`lemma_cs5_vondyck_KM_relator`**
  (`emb(b_col_machine, K_M_rel) ≡_{h2_pred} ε` — the base-relator half of step-4 von-Dyck).
- **Step 3b a-side — the descent bridge (→27/0).** `lemma_a_col_machine_bblock`,
  `lemma_a_col_machine_on_alpha_letter` (digit relabel), `lemma_a_col_machine_relabel_wc`
  (`emb(a_col_machine, w_c(nk,…)) = w_c(nk+n,…)`, mirror CS-4 `lemma_a_words_relabel_wc`), and
  **`lemma_a_col_machine_assoc_rhs`**: `emb(a_col_machine, assoc_rhs_machine(β)) = family_II_rhs(β)`.

### Step 3 — what REMAINS (3b-b-side, 3c, 3d). The hard arc (CS-4 `lemma_map_a_forward`-scale).

**3b-b-side (NEXT, mechanical):** `emb(b_col_machine, assoc_rhs_machine(β)) = family_II_bc_rhs(β)`
(`family_II_bc_rhs` in `cohen_cs5.rs`, the bc-config form). More involved than the a-side: `b_col_machine`
maps machine-b `nk+j ↦ [Gen(b),Gen(c)]`, so `w_b(nk,…)` relabels to **`w_bc(nk+n, nk, …)`** (b's gain
c's), NOT a pure base-shift. Mirror `lemma_a_col_machine_relabel_wc` but the digit-letter image is the
2-symbol `[b_j, c_j]`/`[c_j⁻¹, b_j⁻¹]`; reuse `lemma_w_bc_split`/`w_bc` structure. Powers the step-4
**HNN** relator (the bc-atom `lemma_cs5_bc_config_trivial` then closes it).

Build map for the remaining (3a's HNN object is DONE; the bridge identities are 3b):

**3a. `base_A_plus_data` (the machine-scheme HNN) — the LAYOUT is the subtlety.** Mirror
`pa_data`/`recog_data` (`pa_data.rs`, `h3_ii.rs:739`) but over `base_A_plus_base`:
```
  base_A_plus_data(mm,n,m, h0_slice: Seq<nat>) = HNNData{
      base: base_A_plus_base(mm,n),                       // nk+n+1 gens
      associations: [ (config_word(α,0),  config_word(α,0) ++ w_b(nk, n, m, α) ++ [Gen(nk+n)])
                      : α ∈ h0_slice ] }                  // p-assoc head (α=0) ++ the H₀ family-(II)
```
**Machine-scheme layout ≠ h2 layout.** `base_A_plus_base` puts b's at `nk..nk+n−1` and d at `nk+n`
(NO c-block). So the association rhs MUST use the **machine-scheme `w_b(b_base=nk, …)`** and `d=Gen(nk+n)`
— NOT the h2 `w_b(b_base=nk+n)`/`d=Gen(nk+2n)`. The slice `h0_slice` carries only `α` with `(α,0)∈H₀`
(needed by 3d's von-Dyck + 3c's intersection). Validity (`hnn_data_valid`): mirror `lemma_pa_data_valid`
— config uses gens {0,1}⊂nk; `w_b(nk,…)` the b-block `[nk,nk+n)`; d=`nk+n`; all `< nk+n+1`. ✓

**3b. `a_col_machine` carries `base_A_plus_data` → `recog_data` (the descent bridge).** Prove
`emb(a_col_machine, assoc_rhs_machine(α)) = family_II_rhs(mm,n,m,α)` (the h2 rhs): `a_col_machine`
relabels machine-scheme b `nk+j ↦ h2 b `nk+n+j`, turning `w_b(nk,…)`→`w_b(nk+n,…)`, and `d nk+n ↦
h2 d nk+2n`. So `a_col_machine` maps the machine-scheme HNN to the slice HNN `recog_data` whose
presentation is `h2_II(slice)` — the peel runs over `recog_data` exactly as CS-4. (One new relabeling
identity per association column; reuse `lemma_emb_emb_compose`/`lemma_w_b` index lemmas.)

**3c. The pinch-middle intersection (THE crux, property vi/vii).** In the step case the
`britton_lemma_full` pinch over `recog_data` has middle `∈ ⟨t_α : α∈slice⟩` (the family-(II) associated
subgroup — NOT H₀-restricted). But the middle is also `∈ ⟨U,d,b⟩` (the base of `a_col_machine`'s image)
and `t_α` is machine-only, so middle `∈ ⟨U⟩ ∩ ⟨t_α:α∈slice⟩ = ⟨t_α:(α,0)∈H₀⟩` by **property (vi)**
(`tower_peel.rs:533 lemma_vi`) + **`lemma_theorem1`** (`prop_v.rs:1800`, the circularity-breaker:
`config(α,0)∈⟨g_subgens⟩ ⟺ (α,0)∈H₀`). So the recog pinch middle is AUTOMATICALLY a valid
`base_A_plus_data` association ((α,0)∉H₀ can't arise for an `a_col_machine`-image word's pinch) — this
is how the H₀-restriction is forced. Analog of CS-4 `lemma_intersection_property` (`phi_l_forward.rs:420`),
but the recognition target is `∈⟨U⟩` via property-(vii) instead of `∈⟨config-family⟩`.

**3d. The induction (`decreases stable_count(base_A_plus_data, relabel(w))`).** Mirror
`lemma_map_a_forward` (`phi_l_pinch.rs:773`): **base case** (stable_count==0) = step 2
(`lemma_cs5_base_case_faithful`, descend h2_II→h1_base via `lemma_h1_faithful_in_h2_II`, then ρ);
**step case** = 3b descent of the `britton_lemma_full` pinch (3c gives the middle ∈ H₀-assoc) → pinch-out
(`lemma_pd_pinch_out` analog) → recurse. Output: `relabel(w) ≡_{hnn_presentation(base_A_plus_data(H₀-slice))} ε`.

### Step 4 — von-Dyck at machine scheme + assembly. (Mostly ready; needs 3a's HNN object.)
`lemma_emb_respects_source_equiv_pred(src = hnn_presentation(base_A_plus_data(H₀-slice)),
tgt = h2_pred, images = b_col_machine, relabel(w), ε)`. Relator conditions:
- **base K_M relators:** `emb(b_col_machine, K_M_rel) = K_M_rel` (b_col_machine fixes machine gens —
  same proof shape as step-2 `lemma_rho_fixes_machine_word`) ⟹ an `h2_pred` relator ⟹ `≡ε`.
- **HNN relators `R_α` (α∈H₀-slice):** `emb(b_col_machine, hnn_relator(base_A_plus_data,j))` is the
  bc-config form `p⁻¹ t_α p (t_α w_α(bc) d)⁻¹` ⟹ `lemma_cs5_bc_config_trivial` (DONE) ⟹ `≡ε`. (One
  relabeling identity: `emb(b_col_machine, assoc_rhs_machine(α)) = family_II_bc_rhs(mm,n,m,α)`, the
  b-block `nk+j ↦ [b,c]` turning machine-scheme `w_b` into `w_bc`.)
Then compose with step-1 bridges: `emb(k_b_col,w) = emb(b_col_machine, relabel(w)) ≡ ε` ⟹ **(★k) forward**.
Glue forward (step 3+4) + backward (`lemma_cs5_backward`, DONE) ⟹ `(★k)` ⟹ **CS-5d** tower lift (reuse
CS-4e `lemma_h3_pred_upto_base_faithful` at k=2n) ⟹ `hnn_pred_associations_isomorphic(h3_pred_data)`.

**Risk note:** 3c (property vi/vii at the pinch middle) is the one genuinely-new proof vs CS-4's
free-base `lemma_intersection_property`; everything else is the CS-4 peel structure with the
machine-scheme layout translation (3a/3b) and the step-2 base case swapped in. The layout translation
(machine-scheme `w_b(nk)` vs h2 `w_b(nk+n)`) is mechanical but pervasive — define the `assoc_rhs_machine`
↔ `family_II_rhs`/`family_II_bc_rhs` relabeling identities (3b, 4) once and reuse.

---

## 7. ⚠ DESIGN CORRECTION (2026-06-25, session 26) — R1 needs a `⟨U,d,b,p⟩`-SUBGROUP INVARIANT through 3d.

**The finding (confirmed: textbook §1b + companion model + analysis).** The §5/§6 R1 route — peel
`relabel(w)` over `base_A_plus_data` whose base is the **full** `g_m ∗ free(d,b)` — has a **recursion
gap** at the H₀-restriction (3c). The H₀-restriction needs each pinch middle `∈ ⟨U⟩ ∩ ⟨t_β:slice⟩ =
⟨t_β:(β,0)∈H₀⟩` (property vi/vii). The middle is `∈ ⟨U⟩` ONLY because the recognized base is `⟨U⟩`.
With a **full-`g_m`** base this holds at **iteration 0 only**: `relabel(w)` literally avoids `x=Gen(1)`,
`y=Gen(2)` (since `relabel_col` maps U-gens → `g_subgens = {Gen0,Gen3,Gen4,…}`, never x/y), so its
middles are `⟨U,d,b⟩`-words. But a pinch-OUT reinserts the association image `config(β,0)·w_β(b)·d`,
and `config(β,0) = x⁻ᵝ t xᵝ` **uses x** — so at iteration ≥1 the peeled word uses x, and later middles
are no longer forced into `⟨U⟩`. **A full-`g_m` base cannot prove the per-step H₀-restriction.** This is
exactly Cohen's reason for the base being `⟨U⟩ ∗ ⟨d,b⟩` (pp.280–281), not `K ∗ ⟨d,b⟩`.

**The fix (textbook-faithful, salvages ALL prior work — steps 1/2/3a/3b/3c-C1/step-4 stand).** R1's
machine base (`base_A_plus_base = g_m ∗ free(d,b)`) is KEPT (it dodges the unsound standalone-`⟨U⟩`
presentation §5 rejected). Cohen's `⟨U⟩ ∗ ⟨d,b⟩` is MODELED as the **subgroup
`⟨g_subgens, d-block, b-block, p⟩`** of `hnn_presentation(base_A_plus_data(H₀-slice))`. Thread an extra
induction invariant through 3d:

> **INVARIANT (3d):** the word `w_k` currently being peeled is `∈ ⟨g_subgens ∪ {b-block, d}, p⟩` as a
> subgroup of `base_A_plus_data(H₀-slice)`'s presentation (equivalently: `w_k ≡` a word literally over
> those generator indices).

- **Base case (iteration 0):** `relabel(w) = apply_embedding(relabel_col, w)` is a literal product of
  `relabel_col` entries `= [g_subgens…, d, b…, p]` ⟹ `∈` the subgroup by
  `lemma_apply_embedding_in_subgroup` (near-free).
- **Preservation:** pinch-out replaces a middle (`∈ ⟨t_β:(β,0)∈H₀⟩ ⊆ ⟨g_subgens⟩` by `theorem1`, since
  `(β,0)∈H₀ ⟹ config(β,0)∈⟨g_subgens⟩`) with the opposite association column `config(β,0)·w_β(b)·d`
  (`∈ ⟨g_subgens,d,b⟩` for `β∈H₀`). `pre`/`suf` are subwords of `w_k` (invariant by IH). So `w_{k+1} ∈`
  the subgroup. ∎
- **Use at the pinch middle:** the stable-free middle of `w_k` is `∈ ⟨g_subgens, d, b⟩` (base part of
  the subgroup, no `p`) — THIS supplies the `∈ ⟨U,d,b⟩` hypothesis that C2 (below) needs.

### 7.1 — The corrected 3c-C2 (the H₀-restriction INTERSECTION lemma — E2.E generalization, the crux).
The per-step tool, robust to the invariant threading. Signature (machine scheme):
```
lemma_cs5_middle_h0_restrict(mm, n, m, slice, mid_w):
  requires
    [slice number-words, 2n<m, mod_machine_wf, mm_terminal(mm,0,0)]
    word_valid(mid_w, nk+n+1),                                       // base word, no p
    in_generated_subgroup(base_A_plus_base, ublock_db_gens(mm,n), mid_w),   // ∈ ⟨g_subgens,d,b⟩  (from INVARIANT)
    in_generated_subgroup(base_A_plus_base, config_cols(slice), mid_w),     // ∈ ⟨config(β,0):slice⟩ (from C1)
  ensures
    in_generated_subgroup(base_A_plus_base, config_cols(h0_filter(slice)), mid_w)  // ∈ ⟨config(β,0):H₀∩slice⟩
```
Proof route (generalizes E2.E `lemma_in_TM_config_implies_H0` from a single config to a product):
1. **Project `d,b` away** (a `g_m`-retraction `base_A_plus_base → g_m`, kill `d,b`, fix machine): get
   `g' ≡ mid_w` with `g' ∈ ⟨g_subgens⟩` (a literal U-word) AND `g' ∈ ⟨config(β,0):slice⟩` over `g_m`.
2. **`g' ∈ ⟨g_subgens⟩` over `b_m` ⟹ `in_TMstable(g')`** (`lemma_vii_subset`, `g_subgens=hnn_a_gens`
   diagonal) **⟹ `in_TM(g'_3)`** (`lemma_vi`, needs a `word_valid(·,3)` rep — take the config-product
   form of `g'`, which IS over `{t,x,y}`).
3. **Coordinate survival** (`lemma_tfree_coord_restrict`, the E2.E core): `g'_3 ∈ ⟨config(β,0):slice⟩`
   reduces to a CanonLetter form whose surviving coords `(β,0)` each appear in the H₀-canon of `in_TM`
   ⟹ every surviving `β ∈ H₀`. (The `config(β,0)` are a FREE family — companion-confirmed: this is a
   free-basis-subset intersection `⟨config:S⟩ ∩ ⟨config:H₀⟩ = ⟨config:S∩H₀⟩`, coord-survival rules out
   hidden relations.)
4. **Reconstruct** `g'` from its reduced H₀-coords as a product of `config(β,0):H₀∩slice` (the
   `gsconfig` power-in-subgroup recursion, cf. `r_prime.rs`); lift back to `mid_w ≡ g'`.

This is the genuine multi-session work (E2.E-scale + a reconstruction). Build bottom-up; each rung
verifies & commits.

#### 3c-C2 — ✅ **COMPLETE (session 27, `cohen_cs5_recog` 56/0).** `lemma_cs5_middle_h0_restrict`.
Built bottom-up exactly per the 4-step route, every rung verified & committed:
- **Step 1 — projection application** (`lemma_cs5_project_to_gsubgens`, →48/0). A machine word in
  `⟨g_subgens,d,b⟩` over `base_A_plus_base` lands in `⟨g_subgens⟩` over `g_m`, via the `d,b`-killing
  `π` + two **new presentation-agnostic** transfer lemmas: `lemma_hom_maps_subgroup` (a valid hom maps
  `⟨gens⟩`-membership to `⟨φ(gens)⟩`-membership) and `lemma_in_subgroup_gens_in_core` (drop generators
  that already lie in `⟨core⟩` — here the `ε`-images of `d,b`). `ublock_db_gens` = the `⟨g_subgens,d,b⟩`
  generating set (uniform free tail `[Gen(nk+j)]_{j=0..n}`).
- **Step 2 — vii→vi→in_TM** (`lemma_cs5_cfg_in_TM`, →51/0). `lemma_g_m_base_faithful_2word` (a NEW
  two-word `k`-layer base-faithfulness, mirror of `lemma_quad_base_faithful`, via
  `lemma_single_hnn_base_faithful` on the difference) lands the `⟨g_subgens⟩`-membership in `b_m`; then
  the Layer-1 `lemma_vii_subset` + `lemma_vi` (diagonal `g_subgens=hnn_a_gens`) give `in_TM(cfg_rep)`.
- **Step 3 — product coordinate-survival** (`lemma_cs5_canon_coords_h0`, →52/0). `canw_eval(cs)∈T(M)`
  ⟹ every `cw_reduce(cs)` coordinate is `H₀` — the single-config E2.E (`lemma_in_TM_config_implies_H0`)
  generalised to a product by applying the coordinate-survival core `lemma_tfree_coord_restrict` at each
  surviving reduced coordinate (against the `H₀`-canon from `lemma_in_TM_to_canon`). First-try verify.
- **Step 4 — reconstruct + assemble** (→56/0). `h0_filter` (`slice∩H₀`, a recursive filter) +
  `lemma_h0_filter_contains`; reconstruct `cw_reduce(cs)` as a `config_emb(h0_filter)` product over
  `free_group(3)` (`lemma_canw_in_config_subgroup` + `lemma_free_cw_reduce_eval`) and lift it once to
  `base_A_plus_base` via `lemma_free_subgroup_to_pres` (free reduction sound in any presentation,
  `freely_equivalent`), then `respects_equiv` back to `mid_w`.

All fully verified, no `assume`/`admit`/`external_body`. Purely additive — nothing else in the crate
touched, so the gate is undisturbed. The companion-model + textbook cross-check confirmed: `[x,y]=1`
only affects intra-`β`-block structure (handled by `cw_reduce`), so the free-family coordinate argument
is safe.

### 7.2 — Then 3d (with the invariant) + step 4 (DONE) + CS-5d.   ← **NEXT**
3d mirrors `lemma_map_a_forward` (`phi_l_pinch.rs:773`) PLUS the §7 invariant (extra conjunct in the
`decreases stable_count` induction; the per-step **3c-C2 call now exists** and consumes the
invariant-supplied `∈⟨g_subgens,d,b⟩` precondition — `lemma_cs5_middle_h0_restrict`). Step 4 von-Dyck
(`lemma_cs5_vondyck_relator`, DONE) already wants the H₀-slice — it composes unchanged. CS-5d
(tower lift via `lemma_h3_pred_upto_base_faithful` at k=2n) unchanged.

**Status (session 27):** 3c-C1 (`lemma_cs5_middle_reflect`) + 3c-C2 (`lemma_cs5_middle_h0_restrict`)
both COMPLETE; `cohen_cs5_recog` GREEN at 56/0. NEXT = build **3d** (the `lemma_map_a_forward`-analog
peel over `base_A_plus_data`, threading the §7 `⟨g_subgens,d,b,p⟩`-subgroup invariant; base case = step
2 `lemma_cs5_base_case_faithful`, step case = 3b descent + 3c-C1/C2 at the pinch middle + pinch-out +
recurse) → assemble `(★k)` forward → glue backward → CS-5d tower lift.
