# Property (vi) — THE CRUX: A ∩ ⟨T(M),rᵢ,lⱼ⟩ = T(M)

The hardest sub-arc of the whole construction — the convergence point where properties (ii),
(iv), (v), the tower Britton, and the pinch-elimination all meet. Source: Aanderaa–Cohen §2,
properties (ii) p.212, (iii)(iv) p.216–221, (vi) p.233.

## Statement (tactus)

> `lemma_vi(mm, w)`: `mod_machine_wf(mm)` ∧ `mm_terminal(mm,0,0)` ∧ **`in_TMstable(mm, w)`** ∧
> **`word_valid(w, 3)`** (w is a base_A word, i.e. in A) ⟹ **`in_TM(mm, w)`**.

(The ⊇ direction `T(M) ⊆ A ∩ ⟨T(M),rᵢ,lⱼ⟩` is easy and may not even be needed for E — E only uses ⊆.)

## The induction (alternating form, on stable-FACTOR count)

`in_TMstable(mm,w)` gives factors `F` (each a config word t(a,b) for (a,b)∈H₀, or a stable letter
rᵢ/lⱼ, or an inverse) with `concat_all(F) ≡_{b_m} w`. **Induct on the number of stable-letter
factors in F.**
- **0 stable factors:** every factor is a config word ⟹ `concat_all(F) ∈ T(M)` (in base_A). With
  `concat_all(F) ≡_{base_A} w` (lift the b_m-equiv down — both are base words — via tower
  injectivity), `respects_equiv` ⟹ `in_TM(mm,w)`. ✔ base case.
- **≥1 stable factor:** `concat_all(F)·w⁻¹ ≡_{b_m} ε` has a stable letter ⟹ (tower Britton)
  `has_pinch`. The pinch is a stable pair `[rᵢ⁻¹]·middle·[rᵢ]` whose **middle is the config-word
  block between two adjacent stable factors** ⟹ `middle ∈ T(M)`; and `middle ∈ A_rᵢ` (has_pinch_at).
  **Pinch it out** (brick 111): `[rᵢ⁻¹]·middle·[rᵢ] ≡ φ(middle)`, and **property (v) group-level**
  gives `φ(middle) ∈ T(M)`. So the new factorization `F'` has 2 fewer stable factors and
  `concat_all(F') ≡_{b_m} w` still. IH.

## Dependencies — status

| dep | what | status |
|---|---|---|
| (ii)⊇ | `t(am+i,bm+j) ∈ ⟨t(i,j),xᵐ,yᵐ⟩` | ✅ brick 109 |
| **(ii)⊆** | `T ∩ ⟨t(i,j),xᵐ,yᵐ⟩ ⊆ {t(r,s):r≡i,s≡j}` | ❌ **build** — uses A = T ⋊ ⟨x,y⟩ |
| **(iv)** | iso `t(r,s) ↦ t(r',s')` of the assoc subgroups + their T-intersections | ❌ **build** (from ii,iii) |
| (v) machine | `(a,b)→(a',b') ⟹ [(a,b)∈H₀ ⟺ (a',b')∈H₀]` | ✅ brick 112 |
| **(v) group** | `φ_rᵢ(T(M) ∩ A_rᵢ) ⊆ T(M) ∩ A_{-rᵢ}` | ❌ **build** (= ii⊆ + iv + v-machine) |
| pinch-out | `a∈⟨a_gens⟩ ⟹ rᵢ⁻¹·a·rᵢ ≡ φ(a) ∈ ⟨b_gens⟩` | ✅ brick 111 |
| T(M) reprs | in_TM / in_TMstable + closures | ✅ bricks 113,114 |
| tower Britton | trivial b_m word + stable ⟹ has_pinch (topmost letter) | ❓ establish (single-HNN top + recurse, or reuse tower machinery) |
| factor↔pos | pinch-middle = config-word block between two stable factors | ❌ **build** (sub-brick 2, the bridge) |
| tower inj | base words equiv in b_m ⟹ equiv in base_A | ❓ reuse (`lemma_tower_injectivity_peel`-style) |

## The genuinely-hard sub-bricks (and their substance)

1. **(ii)⊆** — paper: *"any element of ⟨t(i,j),xᵐ,yᵐ⟩ is u·xᵃᵐ·yᵇᵐ with u ∈ ⟨t(r,s):r≡i,s≡j⟩;
   intersecting with T kills xᵃᵐyᵇᵐ."* Needs **A = T ⋊ ⟨x,y⟩**: T=⟨t⟩^A normal, A/T = ⟨x,y⟩ abelian,
   and conjugating t(i,j) by xᵐ,yᵐ shifts indices within the residue class. The "kill xᵃᵐyᵇᵐ" step
   reads off the ⟨x,y⟩-component being trivial. Intricate — the semidirect structure is new.
2. **(iv)** — the index-shift iso. Once ii⊆ pins the basis, the map `t(r,s)↦t(r',s')` (with the
   machine step) is the relabelling; from (iii) (`⟨t(i,j),xᵐ,yᵐ⟩ ≅ A`, a conjugate of `⟨t,xᵐ,yᵐ⟩`).
3. **(v) group-level** — the convergence: `middle ∈ T(M)∩A_rᵢ` ⟹(ii⊆)⟹ `middle = ∏ t(r,s)`,
   r≡aᵢ,s≡bᵢ, all H₀ ⟹(iv)⟹ `φ(middle) = ∏ t(r',s')` with (r,s)→(r',s') ⟹(v-machine)⟹ all H₀
   ⟹ `φ(middle) ∈ T(M)`. This is where ii⊆+iv+v-machine fuse.
4. **factor↔position bridge** — Britton's pinch is positional (`has_pinch_at` at symbol indices);
   F is factor-level. Bridge: stable symbols of `concat_all(F)` ↔ the stable FACTORS (config words
   have no stable symbols), so the pinch-middle = the config-word factors between two stable factors.
5. **tower Britton** — `britton_lemma_full` is single-HNNData; b_m is the heterogeneous tower. Get
   "some stable pair pinches" by top-down recursion (topmost present stable letter is a single HNN
   over `b_m_upto(level-1)`), or by reusing the tower machinery that powered config-basis injectivity.

## Recommended build order

1. **(ii)⊆** first — everything (iv, v-group) rests on it, and it forces us to nail A's semidirect
   structure, which several later steps reuse.
2. **(iv)** — the index-shift iso, on top of ii.
3. **(v) group-level** — fuse ii⊆ + iv + v-machine into `φ(T(M)∩A_rᵢ) ⊆ T(M)∩A_{-rᵢ}`.
4. **tower Britton** + **factor↔position bridge** — the two positional/tower mechanics.
5. **the pinch-elimination induction** (the heart) using 3+4 + brick-111 pinch-out.
6. **base case** (tower injectivity) + **(vi) assembly**.

## Risk notes

- **(ii)⊆ is the new conceptual content** (A = T ⋊ ⟨x,y⟩). Likely the single hardest sub-brick;
  if it stalls, consider whether the config-basis injectivity (T-free, done) already gives most
  of the semidirect structure to reuse.
- The **factor↔position bridge** is the same flavor of intricacy as the no-pinch positional work —
  budget for it.
- **tower Britton / tower injectivity**: prefer REUSING the machinery that proved config-basis
  injectivity (it already navigated the tower) over re-deriving.
- After (vi): only **`in_TM → H₀`** (T-free readoff: a single basis element is a product of
  H₀-basis-elements only if it is one of them) + **E assembly** + **F** remain — all comparatively light.
- Faithful to property (i)–(vii); the paper's pinch-elimination + semidirect structure is canonical.
