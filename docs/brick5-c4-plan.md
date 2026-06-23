# Brick 5 — C4: the σ-closure blocker and the RETARGETING redesign

> **⚠ SUPERSEDED in part (2026-06-23) — read `docs/brick5-fork-reevaluation.md` FIRST.** §8's
> route-A ("surgically peel a fixed `w`, invoke the iso only at pinch-middles") was found to have an
> UNDESIGNED CORE: pinch-existence/base-descent route through `lemma_single_step_preserves_syls`,
> which needs the *universal* iso for *every step of an arbitrary derivation* of `wgi ≡ ε` — not just
> the fixed word's pinch-middles. So the iso CANNOT be word-restricted, and the "virtual iso" substitute
> would require a new "virtual Britton's Lemma" (research-level, no extant sketch). Recommendation
> (pending real-Danielle confirmation): pivot to **Fork A** (a predicate/countable presentation
> foundation, common to Layer 0.5). The R1–R4 directional machinery here is still verified + reusable;
> only the route-A packaging is blocked.

Companion to `brick5-completeness-plan.md` (the C-arc) and `brick5-c3.2c-plan.md` (map_a/map_b).
Written 2026-06-22 after discovering that C3.2's side condition `sigma_sat_upto` is **unsatisfiable**
and the root cause is architectural, not a missing lemma. Read this before touching C4.

---

## 1. The finding: `sigma_sat_upto` is unsatisfiable for finite `alphas`

C3.2's per-level isos (`lemma_phi_l_iso`, `lemma_h3_II_upto_faithful`, `phi_l_iso_tower.rs`) carry the
side condition

```
sigma_sat_upto(alphas, m, l) = ∀ j∈[1,l]. sigma_backsat(betas(alphas), m, j)
                                         ∧ sigma_fwdsat(betas(alphas), m, j)
```

where `σ_j(β) = m·β + j` APPENDS base-m digit `j` (number-word indices = base-m strings, digits in
`[1,2n]`, `2n<m`), and

- `sigma_backsat(bet,m,j) = ∀b. bet∋(m·b+j) ⟹ bet∋b`   (digit-STRIP closure — finite-satisfiable)
- `sigma_fwdsat(bet,m,j)  = ∀k. bet∋(m·bet[k]+j)`        (digit-APPEND closure — **never** finite)

`betas(alphas)=[0]++alphas` always contains 0, so `sigma_fwdsat` forces `bet ∋ {j, mj+j, m²j+mj+j, …}`
— an infinite strictly-ascending chain. **No finite `Seq` satisfies it.** So every C3.2 iso has an
always-false hypothesis: verified, but vacuous and unusable by C4. (The agenda/comment "σ-orbits are
finite among number-word indices" is wrong — only the *backward* (digit-strip) orbit is finite.)

## 2. Two consumers of `sigma_fwdsat` — one fixed, one is the real blocker

**(a) The b-side reflection `lemma_pa_rhs_reflect_full` / `lemma_r_prime_b` — FIXED, backsat-only**
(commit `28b2898`). The old σ-selector needed each `σbet[k]∈bet`. The fix keys the selector to the
canonical COORDINATES of `emb(φ',u)` (each is σ-shaped AND already in `bet`, via the now-strengthened
`lemma_coords_in_sigma`), so it is valid without forward-saturation; backsat only identifies each
coord with a σbet-value at the end. New machinery: `lemma_phi_prime_canon`, `coord_vals`/`coord_sel` +
compose lemmas, `lemma_in_subgroup_gens_superset`, split into `lemma_coord_config_membership` /
`lemma_coord_pa_transfer`. **This is likely SUPERSEDED by the retargeting (§3) — see §5.**

**(b) The von-Dyck `lemma_phi_l_src_on_pa_relator` — THE REAL BLOCKER, not reflection-fixable.**
It proves `φ_l_src` is a self-ENDOMORPHISM of `P_A(bet) = HNN(F=free(n+3), p | family-II over bet)`:
`φ_l_src` maps the j-th relator (over `γ=bet[j]`) to the `σγ`-relator (`σγ=m·γ+l`), and to be `≡ε` in
`P_A(bet)` that `σγ`-relator must be a LITERAL `P_A(bet)` relator ⟹ `σγ∈bet` (line 487-491,
`phi_l_mapb_fwd.rs`). That is forward-saturation `σ(bet)⊆bet` = **impossible for finite `bet`**. It is
intrinsic to "`φ_l` is a well-defined HNN association iso" (C3.2's goal). No coordinate trick removes
it. This propagates: `lemma_phi_l_src_on_pa_relator → lemma_mapb_M2 → lemma_map_b_forward →
lemma_phi_l_iso_at_h2II → lemma_phi_l_iso / sigma_sat_upto`.

## 3. The fix: RETARGET `φ_l_src : P_A(bet) → P_A(σbet)` (model-confirmed, peer-reviewed)

`φ_l_src` should NOT be a self-endo. Make its target the `σ(bet)`-indexed `P_A`, a DIFFERENT (also
finite) group. Then the von-Dyck is **automatic by construction**: `φ_l_src(relator_j) = σγ-relator`,
and `σγ ∈ σ(bet)` literally (`σbet[j]=σγ`). No forward-closure. This aligns the formalization with the
actual group-theoretic behaviour of `σ` (an open σ-orbit chain, not a closed loop).

Consequences:
1. **von-Dyck** (`lemma_phi_l_src_on_pa_relator`): ensures `≡ε in hnn_presentation(pa_data(σbet))`
   (not `pa_data(bet)`). Body already computes `emb(src,hr) = σγ-relator form`; just identify it as
   `pa_data(σbet)`-relator `j` (since `σbet[j]=σγ`) instead of `pa_data(bet)`-relator `k` via fwdsat.
   Drops `sigma_fwdsat` entirely.
2. **M2** (`lemma_mapb_M2`, `φ_l_src` injective): a Britton peel where `w` is over `pa_data(bet)` but
   the image `emb(φ_l_src,w)` is over `pa_data(σbet)`. The base `F=free(n+3)` is common to both, and
   the descent is on `w.len()` / `stable_count`, so crossing index sets is sound (Britton only needs a
   pinch in the target + a common base). **The spanning pinch-middle `emb(φ_F,mid)` is NATIVELY in
   `⟨pa_rhs_emb(σbet)⟩`** (the σbet association column), so the intersection property
   (`compose(φ_F,pa_rhs_emb(bet))=pa_rhs_emb(σbet)`) gives `mid∈⟨pa_rhs_emb(bet)⟩` DIRECTLY — **no
   bet→σbet reflection, no saturation at all.** (This is why §2(a) is superseded.)
3. **map_b forward** (`lemma_map_b_forward`): `emb(b_words,w)≡_{h2_II}ε ⟹ w≡_{P_A(bet)}ε`, routed
   `M1 → map_a fwd(σbet) → M2 → map_a fwd(bet)`. Needs `map_a` faithful over BOTH `bet` and `σbet`
   (map_a = `F↪h1_base` is index-set-agnostic, so fine), and `h2_II` to carry family-II for both `bet`
   and `σbet`.
4. **The crux** (`lemma_phi_l_iso_at_h2II`) + **tower** (`lemma_h3_II_upto_faithful`, `lemma_phi_l_iso`):
   the base `h3_II_upto(l-1)` must carry family-II for the σ-shifted index sets at each level. So
   `h3_II`'s `alphas` must contain the BOUNDED σ-orbit (`bet ∪ σbet ∪ σ²bet ∪ … up to tower depth 2n`),
   which for a FIXED faithfulness instance is FINITE — **satisfiable**, not forward-closed.
5. **`sigma_sat_upto`**: replaced by "`alphas ⊇ bounded σ-orbit`" (or per-level `σbet ⊆ alphas`), which
   a finite `alphas` CAN satisfy. C4 then picks `alphas` = the bounded orbit of the digits of the fixed
   `w_α(c)`.

## 4. Brick decomposition for the retargeting (the C4 arc proper)

This is a **type-level cascade** through the most intricate verified code (the `decreases w.len()`
pinch-descent). Land it as a coordinated unit; it cannot be split lemma-by-lemma without breaking the
chain (M2 consumes the von-Dyck; retargeting one breaks the other). Suggested order:

- **R1 — retargeted von-Dyck — DONE 2026-06-22** (`phi_l_mapb_fwd.rs` 12/0,
  `lemma_phi_l_src_on_pa_relator_retarget`): `φ_l_src(j-th pa_data(bet) relator) ≡ε` in `P_A(σbet)`,
  AUTOMATIC (σbet[j]=σγ literal relator), no `sigma_fwdsat`. + `lemma_sigma_numbers_word` /
  `lemma_sigma_betas_numbers_word` (σ preserves number-word-ness). The self-endo
  `lemma_phi_l_src_on_pa_relator` stays for now; the parallel retargeted chain replaces it at R2–R7.
- **R2 — cross-index pinch-descent — DONE 2026-06-22** (`phi_l_mapb_fwd.rs` 16/0):
  `lemma_pa_rhs_reflect_intersection` / `lemma_config_reflect_intersection` (the σbet→bet reflection via
  `lemma_intersection_property`, replacing (R)/(R)_b, NO saturation) + `lemma_mapb_pinch_spanning_rt`
  (spanning, middle natively in `⟨col(σbet)⟩`) + `lemma_mapb_pinch_descends_rt` (head-peel, pinch ops
  over `pa_data(σbet)`, w-pinch over `pa_data(bet)`, common base `free(n+3)`). Verified ~first try.
- **R3 — cross-index M2 — DONE 2026-06-22** (`phi_l_mapb_fwd.rs` 17/0, `lemma_mapb_M2_rt`):
  `emb(φ_l_src,w)≡_{P_A(σbet)}ε ⟹ w≡_{P_A(bet)}ε`. `britton_lemma_full` over `pa_data(σbet)` (iso as a
  HYPOTHESIS), R2 to descend, pinch-out over `pa_data(bet)`, R1 for the cross-presentation
  `lemma_emb_respects_source_equiv`. **R1+R2+R3 = the full injectivity `φ_l_src: P_A(bet)↪P_A(σbet)`, no
  σ-saturation — the bottleneck is CRACKED.**
- **R4 — retargeted map_b forward (NEXT, the index-set-generalization layer).** Current
  `lemma_map_b_forward` does `M1 → map_a fwd → M2(self-endo)`, where `lemma_map_a_forward` gives
  `pw ≡_{P_A(betas(alphas))} ε`. But `lemma_mapb_M2_rt` wants `pw ≡_{P_A(σbet)} ε` (σbet =
  `sigma_betas(betas(alphas),m,l)`). So R4 needs **map_a forward over the index set σbet** (and
  `hnn_associations_isomorphic(pa_data(σbet))`). Both `lemma_map_a_forward` and `lemma_pa_data_isomorphic`
  are currently tied to `betas(alphas)` (via `recog_data`/`h2_II`'s own alphas) — R4 = **generalize them
  to an arbitrary number-word, no-dup index set `S ⊆ alphas`** (so `h2_II` carries family-II over `S`),
  then instantiate at `S = σbet`. This forces `σbet ⊆ alphas` = the **bounded-orbit alphas (R6)**: alphas
  must contain `betas(alphas) ∪ σ(betas(alphas)) ∪ …` up to the needed depth (FINITE for a fixed
  instance — the satisfiable replacement for `sigma_sat_upto`).
- **R4 — map_b forward** over the two index sets (map_a fwd both, M1, M2).
- **R5 — the crux** `lemma_phi_l_iso_at_h2II`: the association iso over a base carrying family-II for
  `bet ∪ σbet`. New side condition `σbet ⊆ alphas` (satisfiable).
- **R6 — `h3_II` index threading** (`h3_ii.rs`): `alphas` = bounded σ-orbit; the tower base at level
  `l` carries family-II for the level's index sets. Redefine `sigma_sat_upto` → bounded-orbit
  containment; thread through `lemma_h3_II_upto_faithful` / `lemma_phi_l_iso`.
- **R7 — C4 instantiation**: pick the finite `alphas` = bounded σ-orbit of `w_α(c)`'s digits;
  discharge the new satisfiable side condition; feed the C4 k-engine.

## 5. Status of the §2(a) reflection fix

It is verified (commit `28b2898`) and correct, but the §3 retargeting **obviates the bet→σbet
reflection** (the pinch-middle becomes natively σbet, intersection property suffices). KEEP for now —
the reusable parts survive: the strengthened `lemma_coords_in_sigma` (exposes `coord∈bet`), the
`lemma_phi_prime_canon` factoring, `lemma_in_subgroup_gens_superset`, and the coord-selector technique
may be reused; the intersection-property tail of `(R)_b` is exactly what R2 uses. When R2 lands, the
now-dead `lemma_r_prime_b` / `coord_sel` machinery + the `sigma_selector`/`sigma_fwdsat` helpers can be
pruned.

## 6. Honest scope

The retargeting is the bulk of C4 — a `tower_peel`-sized arc touching `phi_l_mapb_fwd.rs`,
`phi_l_iso_tower.rs`, and `h3_ii.rs`. It is the RIGHT design (peer-confirmed: the self-endo framing is
mathematically impossible for finite index sets; retargeting makes the von-Dyck a triviality). No
verifier bypasses (standing rule). Lean-backend, `./check.sh --verify-module <name>`.

---

## 7. ⚠ THE FINITE-SLICE IS ALSO UNSATISFIABLE — C3.2 IS VACUOUS (found 2026-06-22, w/ Danielle)

**The R4 retargeting did NOT crack the blocker — it relocated it.** The new `sigma_sat_upto`
(`backsat` + `finite-slice`, `phi_l_iso_tower.rs`) is **just as unsatisfiable for finite `alphas`** as
the `sigma_fwdsat` it replaced. So `lemma_phi_l_iso` and `lemma_h3_II_upto_faithful` verify ONLY because
their hypothesis is a contradiction — they are **vacuous and cannot be instantiated**. C3.2 is NOT done.

### 7.1 The unsatisfiability (machine-checked: `lemma_sigma_sat_upto_unsatisfiable`, `phi_l_iso_unsat.rs` 3/0)

The finite-slice requires, at level `j = 1`, for every `γ ∈ betas(alphas) = [0]++alphas`:
`m·γ + 1 ∈ alphas`. With `γ = betas[0] = 0` this forces `1 ∈ alphas`; then `γ = 1` forces `m+1 ∈ alphas`;
then `m²+m+1`, … — a strictly increasing infinite chain into a finite `Seq`. Proof: take `M = max(alphas)`
(exists, alphas∋1); `M ∈ betas` ⟹ `m·M+1 ∈ alphas`; but `m·M+1 > M = max`. Contradiction. The "bounded
σ-orbit" idea (§3 consequence 4–5) is **wrong**: only the *backward* (digit-strip) orbit is finite; the
finite-slice is a *forward* (digit-append) requirement, so it inherits the original infinity.

### 7.2 Root cause — a finite presentation cannot host a universal HNN iso here

`hnn_associations_isomorphic(phi_l_data)` is `∀ww. emb(a_words,ww)≡_base ε ⟺ emb(b_words,ww)≡_base ε`.
The `⟸`/von-Dyck-backward direction needs `family_II_relator(m·β+l) ≡_base ε` (= `emb(b_words, β-relator)`),
which the finite base `h3_II` (= `h2_pres` + a FINITE family-(II) slice over `alphas`) derives ONLY when
`m·β+l ∈ alphas` (`lemma_b_words_relator_trivial` → `lemma_phi_l_relator_equiv_empty`). Since the iso is
universal over `ww`, it ranges over β-relators for **every** `β` the base covers (all of `alphas`), so it
needs `σ_l(alphas) ⊆ alphas` — forward-closure — infinite. **Decoupling the source index set from the
base coverage does NOT help** (the universal `ww` produces relators over all of `alphas`, not just the
source set). A finite presentation simply cannot carry the full (infinite) family (II); the a-level
associations are therefore **virtual isos** (true in the *group* `h3_pres`, false in the *base
presentation*), EXACTLY the situation `brick5-completeness-plan.md` §2.2/§2.3 already names for the
k-level. **§2.2ter's premise — "a finite family-(II) augmentation makes the a-levels LITERAL isos" — is
false.**

### 7.3 The reframe (Danielle-confirmed): a-levels get the virtual-iso / Fork-B treatment too

Faithfulness is **per-α** (a fixed `w_α(c)`), whose Britton analysis touches **finitely many** β's. So:

- **Do NOT target the universal `hnn_associations_isomorphic`.** Target a **word-restricted** a-level
  faithfulness: the iso need only hold for the pinches actually arising in peeling the fixed word.
- **The R1–R4 directional machinery is REUSABLE** (Danielle: "the correct tool"). `lemma_map_a_forward`,
  `lemma_map_b_forward_rt`, `lemma_map_*_von_dyck_backward`, and the pinch-descents are real per-direction
  Britton pieces. What is wrong is ONLY (i) the *universal* packaging `lemma_phi_l_iso_at_h2II` (`∀ww`),
  and (ii) the `britton_lemma_full`-based tower lift `lemma_h3_II_upto_faithful` (which consumes the
  universal `hnn_associations_isomorphic`).
- **Concretely**, the directional lemmas' precondition `∀γ∈betas. σ_l(γ)∈alphas` must be **weakened to
  the betas the specific `w` touches** (a satisfiable, word-relative finite-slice; `alphas` = bounded
  σ-orbit of `w`'s betas, which IS finite for a fixed word). Then a word-restricted Britton variant
  (the same engine Fork-B budgets for the k-level) replaces the universal `britton_lemma_full` so the
  whole tower (a-levels AND k-level) runs on **one** virtual-iso engine.

### 7.4 Suggested next steps (fresh arc; co-design the engine signature with Danielle)

1. **Pin the word-restricted iso notion** — an analog of `hnn_associations_isomorphic` quantified over a
   *given finite set of association-words* (or a bound on the config-indices touched), satisfiable by a
   bounded `alphas`. This is the Fork-B engine's input shape; design it once, use it at every tower level.
2. **Bounded σ-orbit + satisfiability — ✅ DONE 2026-06-23** (`sigma_orbit.rs` 13/0). `sigma_orbit(d,m,n,depth)`
   = the depth-stratified accumulation `orbit(0)=d`, `orbit(k+1)=orbit(k) ++ σ-expand(orbit(k))`, built as
   an explicit finite `Seq<nat>`. Proven: number-word preservation (`lemma_sigma_orbit_numbers_word`, via
   the existing `lemma_sigma_numbers_word`), depth-stratified σ-closure `lemma_sigma_orbit_closed_step`
   (`orbit(d)→orbit(d+1)` — a DAG, the top layer's σ-shifts are NOT required, which is *why* it dodges the
   unsat forward-closure), monotonicity, and the **satisfiability witness** `lemma_sigma_slice_satisfiable`
   + `lemma_sigma_orbit_covers` (one finite `alphas` covers all `2n` levels). The reframed
   `sigma_slice_ok(seed, alphas, m, n)` is pinned there: it quantifies the digit-append requirement over a
   SEPARATE finite `seed` (decoupled from `alphas`), so no element forces its own σ-image — the direct
   refutation of the session-7/8 "even the bounded slice is vacuous". See §7.5 for how it slots in.
3. **Weaken + re-verify the directional lemmas** to the word-relative finite-slice (they already only USE
   it at the pinches encountered; the `∀γ∈betas` precondition is gratuitously strong).
4. **Word-restricted tower lift** replacing `lemma_h3_II_upto_faithful`'s `britton_lemma_full` with the
   virtual-iso engine. Then C3.2 (word-restricted), C2, C4 (k-level), C5 assembly all share it.

**Status:** keep `phi_l_iso_tower.rs` / the R1–R4 modules — they verify and the directional pieces are
reused. `lemma_phi_l_iso` / `lemma_h3_II_upto_faithful` remain in-tree, **marked vacuous** (their
hypothesis is `lemma_sigma_sat_upto_unsatisfiable`-refuted); do NOT build on them as written.

---

## 8. The route decision: SURGICAL (route A), not full-Britton re-prove (2026-06-23)

With the de-risking brick landed (§7.4 step 2), the next gating decision is *how* to consume a
word-restricted iso. The universal `hnn_associations_isomorphic(data)` threads through **all** of
`britton_via_tower.rs` (dozens of lemmas) via `lemma_tower_textbook_chain_from_hnn_iso`, so the naive
"thread a word-restricted predicate through the whole tower-textbook chain" (route B) is enormous.

**Decision (peer-confirmed 2026-06-23): take route A — derivation-local / surgical.** Re-derive
faithfulness for a FIXED `w` by peeling `w` with Britton (induction on stable-letter count), invoking
the iso ONLY at the pinch-middles that actually arise. This turns a group-theory ∀-statement into a
rewriting-theory statement about a finite derivation object — and we already have the verified
per-direction pinch pieces (`lemma_map_a_forward`, `lemma_map_b_forward_rt`, the von-Dyck backwards, the
pinch-descents). Route B fights the ∀w quantifier we *know* is UNSAT; route A never forms it.

**Why route A's index set is a-priori finite (the satisfiability we lacked):**
- *Lyapunov bound on pinch count.* Each Britton step consumes one `s … s⁻¹` pair, so the stable-letter
  count strictly decreases by 2; total pinches ≤ ½·(stable-letter count of `w`). No step *introduces*
  stable letters. ⟹ **finitely many pinch-middles**, bounded by `w` alone.
- *Bounded index growth = the σ-orbit at depth ≤ 2n.* Each pinch-middle is a base word whose config
  generators carry indices `β`; eliminating a level-`l` pinch applies `φ_l : β ↦ m·β+l = σ_l(β)`, so the
  middles' indices σ-shift by one digit **per tower level**, and the tower height is `2n`. ⟹ all indices
  ever touched live in `sigma_orbit(L₀, m, n, 2n)` where `L₀` = config-indices appearing in `w`. That set
  is FINITE (the brick), so `alphas ⊇ sigma_orbit(L₀,m,n,2n)` discharges every per-pinch von-Dyck-backward
  `family_II_relator(σ_l(β)) ≡ ε`. **This is precisely what `sigma_orbit.rs` was built to supply.**
  (Caveat for the next session: the index set is the σ-*orbit* of `L₀`, not just `L₀` — the middles' indices
  genuinely grow by σ as you descend; the Lyapunov argument bounds the *count* of middles, the orbit bounds
  their *indices*. Both finite.)

**The remaining co-design with Danielle (the actual signature — do NOT guess solo; wrong-signature has
burned two sessions):**
1. *Shape of the word-restricted faithfulness lemma.* Two candidate signatures:
   (i) `iso_on(data, W)` = the iff quantified over a precomputed finite word-set `W` (clean, but you must
   pre-extract `W` from `w`'s derivation, which is awkward since the derivation is `choose`-n); or
   (ii) thread the iso as a *per-pinch obligation* inside a fresh `decreases stable_count` peel of `w`
   (no precomputed `W`; the iso is discharged at each pinch from `alphas ⊇ sigma_orbit(...)`). (ii) matches
   route A's derivation-local nature and the existing pinch-descent lemmas better, but is a new induction.
2. *Where it attaches.* A word-restricted analog of `lemma_single_hnn_base_faithful` (NOT a re-prove of
   `lemma_tower_textbook_chain_from_hnn_iso`), used at each a-tower level in place of the vacuous
   `lemma_phi_l_iso_at_h2II` + `britton_lemma_full` calls in `phi_l_iso_tower.rs`.
3. *The satisfiable side condition* replacing `sigma_sat_upto`: `sigma_backsat(...)` (still needed, still
   finite-satisfiable — the digit-STRIP closure) **+** `alphas ⊇ sigma_orbit(L₀, m, n, 2n)` (via
   `sigma_slice_ok` / `lemma_sigma_orbit_covers`), with `L₀` extracted from the fixed `w`. C4 then picks
   `alphas` = that bounded orbit for the fixed `wα(c)`.

**Status going into the co-design session:** step 2 (the index-set tool) is verified and committed. The
directional Britton pieces (R1–R4) are verified and reusable. What is NOT yet built is the route-A
word-restricted peel itself (item 2 above) and its signature (item 1) — that is the next arc.
