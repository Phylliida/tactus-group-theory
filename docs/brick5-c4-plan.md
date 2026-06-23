# Brick 5 — C4: the σ-closure blocker and the RETARGETING redesign

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

- **R1 — retargeted von-Dyck.** `lemma_phi_l_src_on_pa_relator` ⟹ ensures over `pa_data(σbet)`, drop
  `sigma_fwdsat`. (Easy; the model calls it "trivial by construction".)
- **R2 — cross-index pinch-descent.** Rework `lemma_mapb_pinch_descends` / `lemma_mapb_pinch_spanning`:
  pinch of `emb(φ_l_src,w)` over `pa_data(σbet)` descends to a pinch of `w` over `pa_data(bet)`. The
  spanning case uses ONLY the intersection property (no (R)/(R)_b). **The bottleneck.**
- **R3 — cross-index M2.** `lemma_mapb_M2`: `emb(φ_l_src,w)≡_{P_A(σbet)}ε ⟹ w≡_{P_A(bet)}ε`, Britton
  peel over `pa_data(σbet)` for the image + R2 to descend pinches, recurse on `stable_count`.
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
