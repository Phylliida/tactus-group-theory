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
