# Layer 2 — build plan (module / brick decomposition)

Concrete implementation plan for AGENDA §3.2 (the Higman embedding `C ↪ H₃`). Math is fixed by
`higman-embedding-blueprint.md` (now carrying the **verified** transcription of Cohen p.279–281).
This doc is the *engineering* decomposition: what modules, in what order, each independently
verifiable on the existing substrate.

## What we build on (already proven)

- **Substrate:** `presentation.rs` (`Presentation = {num_generators, relators}`), `word.rs`
  (`Word = Seq<signed symbol>`), `hnn.rs` / `britton_via_tower.rs` (HNN + Britton normal form),
  `free_product.rs`, `amalgamated_free_product.rs`, `benign.rs`, `homomorphism.rs`.
- **Layer 1 (`machine_group.rs`, `prop_v.rs`, …):** `config_word(r,s)` = `t(r,s)`, the machine
  group `K_M = G(M)`, `in_TM` / `in_TMstable`, `g_subgens(mm)` = `⟨t, rᵢ, lⱼ⟩` generators (this is
  exactly Cohen's `U`!), and **Theorem 1** `lemma_theorem1`: `[k,t(α,β)]=1 ⟺ (α,β)∈H₀(M)`, with the
  faithfulness `(α,0)∈H₀(M) ⟺ t_α ∈ ⟨U⟩` available via `in_TM`/`(vi)`/`(vii)`.

## Bricks (each a module; verify before moving on)

### Brick 1 — `word_numbering.rs` (foundation; pure word combinatorics, NO group theory)
The α↔word numbering of book p.279 and the three substitution maps. Self-contained on `word.rs`.
- `spec fn numbers_word(m, alpha) -> bool`  (= `α ∈ I`: α's m-ary digits are all in `1..=2n`).
- `spec fn w_c(n, m, alpha) -> Word`   (`w_α(c)` on `c₁,…,c_{2n}`, `c_{n+i}=c_i⁻¹`).
- `spec fn w_b(n, m, alpha) -> Word`   (`w_α(b)`: each `c_j^{±1}` ↦ `b_j^{±1}`).
- `spec fn w_bc(n, m, alpha) -> Word`  (`w_α(bc)`: each `c_j^{±1}` ↦ `(b_j c_j)^{±1}`).
- **Recursion lemmas** (the load-bearing facts):
  - `w_x(αm+i) = w_x(α) · [digit i]` for `x∈{c,b}`, the snoc rule (book: `w_{αm+i}(b)=w_α(b)b_i`).
  - `w_bc(α) = w_b(α) · w_c(α)` **modulo `b_i c_j = c_j b_i`** — i.e. as elements of `C×⟨b⟩`,
    `w_α(bc)` collapses to `w_α(b) w_α(c)`. (Needed for the (III) derivation.)
- Decide the generator indexing convention up front (which indices are `t,x,y,k`, the `rᵢ/lⱼ`, the
  `b_j`, `c_j`, `d`, `p`, `a_i`, `k_top`) — Layer 2 is one big presentation, so fix a global layout
  table here and reuse it in bricks 2–5.

### Brick 2 — `h1.rs` (`H₁ = K_M ∗ (C × ⟨b⟩) ∗ ⟨d⟩`)
- Build the `Presentation` for `H₁` (free product of `K_M`, the direct product `C×⟨b⟩`, and `⟨d⟩`).
  Reuse `free_product.rs` for `∗` and add `b_i c_j = c_j b_i` relators for the `×`.
- Prove `{ t_α w_α(b) d : α∈I }` is a **free basis** of the subgroup it generates (map `H₁→K_M`
  killing `c_j,b_j,d`; image `{t_α}` free by Layer-1 property (i); pull back via Prop-1.8-Cor-1
  analogue). This is the one nontrivial lemma of brick 2.

### Brick 3 — `h2.rs` (`H₂ = HNN(H₁, p ∣ p⁻¹ t_α p = t_α w_α(b) d)`)
- HNN over `H₁` with stable `p`; associated subgroups `⟨t_α : α∈I⟩` ↔ `⟨t_α w_α(b) d : α∈I⟩`
  (both free bases from brick 2) ⟹ HNN-valid.
- `C ⊆ H₂` (already `C ⊆ H₁`; record the embedding `c_j ↦ c_j`).
- Identify `A = ⟨t,x,d,b_j,p⟩` as the `p`-HNN of free `F=⟨t,x,d,b_j⟩`.

### Brick 4 — `h3.rs` (`H₃ = HNN(H₂; a_i, k ∣ a_i:A↔A_i, k:A₊↔A₋)`)
- The two iso families (stated-gen ↦ stated-gen): `φ_i: A→A_i` and `ψ: A₊→A₋`. Prove each is an
  isomorphism (the `A₊→A₋` inverse is the `c_j↦1` endomorphism of `H₂`).
- HNN-validity of the `a_i` (2n of them) and `k`; `H₃ ⊇ C`; `H₃` finitely **generated**.

### Brick 5 — `higman_consequences.rs` (the payoff: `H₃` finitely **presented**)
- Relation sets (I) finite, (II)/(III) infinite (blueprint).
- **(III) from (I)+(II):** faithfulness `t_α∈⟨U⟩` (Layer 1) ⟹ `k⁻¹ t_α k = t_α` ⟹ conjugate (II) by
  `k` ⟹ `k⁻¹ w_α(b) k = w_α(b)`; but `k:b_j↦b_j c_j` ⟹ `= w_α(bc) = w_α(b) w_α(c)` (brick-1 split)
  ⟹ `w_α(c)=1`.
- **(II) from (I):** `w_α(a)` (replace `b_i↦a_i`); induction on word length ⟹
  `w_α(a)⁻¹ t w_α(a) = t_α`, `w_α(a)⁻¹ d w_α(a) = w_α(b)d`; with `p⁻¹tp=td`, `a_i⁻¹pa_i=p` ⟹ (II).
- Headline: `H₃` is presented by the finite set (I) — the f.p. embedding `C ↪ H₃`.

## Deferred / parallel
- **Layer 0.5** (`docs`: locate Cohen's HNN "Embedding Theorem", countable → f.g. r.p. `C`): the
  tower (bricks 2–5) is generic over a f.g. r.p. `C = ⟨c₁,…,cₙ;S⟩`, so build it first and slot the
  ZFC-CEER `C` in afterward. Not on the critical path for the tower.
- **Bridge / instantiate / print** (AGENDA §3.3–3.4): after bricks 1–5 + Layer 0.5.

## Sequencing note
Brick 1 is the only fully self-contained piece (no Layer-1 / HNN dependency) — start there to lock
the generator-layout convention and the `w_α` algebra, then bricks 2→5 in order (each needs the
prior). Bricks 2 and 4 carry the two real proof obligations (free-basis pullback; iso well-defined);
brick 5 is where Layer 1's faithfulness is finally consumed.

---

## STATUS (2026-06-20) — Brick 1 DONE

`src/word_numbering.rs` landed & verified (`9 verified, 0 errors`, commit e54c765), wired into
`lib.rs` after `prop_v`. It deliberately left the generator layout ABSTRACT (base-offset params
`c_base`/`b_base`/`n`/`m`), per the design; the global layout is pinned below for Brick 2.

### De-risking: infinite relation families are NOT a representation blocker
The recursively-presented intermediate groups carry infinite relation families — `S` (= C's
relators, r.e. via `w_α(c)∈S ⟺ (α,0)∈H₀(M)`), and H₂'s `p`-HNN whose associated subgroup
`⟨t_α : α∈I⟩` is **infinitely generated**. Both `Presentation.relators` and
`HNNData.associations` are **finite `Seq`s**, so they can't hold these directly. BUT the Layer-1
code already solves this: subgroup membership is carried by a **`spec_fn(Word) -> bool` predicate**
(`ii_subset.rs:318` `pred: spec_fn(Word)->bool`; the entire E2.C/`kp_pinch` property-II engine is
abstract over `in_k: spec_fn(Word)->bool`), and `benign.rs` is the dedicated Higman r.e.-subgroup
("benign") framing (G ↪ f.p. K, H = G∩L). So H₂'s `p`-HNN associated subgroup is a predicate
`in_t_alpha_subgroup: spec_fn(Word)->bool` (≈ "is a product of `t_α`, α∈I"), and its faithfulness
goes through the existing `kp_pinch`-style engine. **No new core representation needed** — reuse
the predicate-subgroup abstraction. (Only the FINAL `H₃` set (I) is a literal finite `Presentation`.)

### Global generator layout table (pin in Brick 2 `h1.rs`, reuse in bricks 3–5)
Let `N_K := g_m(mm).num_generators = 4 + |mm.quads|` (K_M's count) and `n` = #c-gens = #b-gens.
K_M's own layout (from `machine_group.rs`): `0=t, 1=x, 2=y`, then `3 .. N_K-2` = the per-quad
r/l HNN stable letters (= `U`/`g_subgens` minus `t`), and `N_K-1 = 3+|quads|` = `k'` (`k_gen`, the
Layer-1 commutator witness). Order the H₃ factors **K_M, then (C×⟨b⟩), then ⟨d⟩, p, a-block, k**
so `free_product`'s left-to-right offset convention places each block at the index below:

| block        | symbols          | base index            | count | end index (excl) |
|--------------|------------------|-----------------------|-------|------------------|
| K_M          | t,x,y,(r/l)…,k'  | `0`                   | `N_K` | `N_K`            |
| c            | c₁…cₙ            | `c_base = N_K`        | `n`   | `N_K+n`          |
| b            | b₁…bₙ            | `b_base = N_K+n`      | `n`   | `N_K+2n`         |
| d            | d                | `N_K+2n`              | `1`   | `N_K+2n+1`       |
| p (H₂ stbl)  | p                | `N_K+2n+1`            | `1`   | `N_K+2n+2`       |
| a (H₃ stbl)  | a₁…a₂ₙ           | `a_base = N_K+2n+2`   | `2n`  | `N_K+4n+2`       |
| k (H₃ top)   | k                | `k_top = N_K+4n+2`    | `1`   | `N_K+4n+3`       |

`total = N_K + 4n + 3 = 7 + |quads| + 4n`. **Naming clash guard:** Layer-1's `k'` (commutator
witness, index `N_K-1`) is DISTINCT from Layer-2's top stable letter `k` (index `N_K+4n+2`) — keep
them separate (`k_machine`/`k_gen` vs `k_top`). Word-numbering instantiation: `w_α(c)` at `c_base=N_K`,
`w_α(b)` at `b_base=N_K+n`. H₁ only uses blocks K_M..d (`0 .. N_K+2n`); p/a/k enter at H₂/H₃.

### Recommended Brick 2 first step (verifiable, self-contained) — DONE
`layout.rs` landed (commit 49860ee, 1/0): spec fns `c_base`/`b_base`/`d_idx`/`p_idx`/`a_base`/
`k_top`/`h{1,2,3}_num_gens` (parameterized by `nk` = K_M gen count, `n`) + `lemma_layout_consistent`
(blocks strictly ordered, tile `0..h3_num_gens`). Convention locked.

### DESIGN DECISION (2026-06-20): represent C as predicate, keep all Presentations finite (Approach b)
The recursively-presented C = ⟨c;S⟩ is NOT stored as a `Presentation` (S is r.e./infinite). Instead:
keep `Presentation` **strictly finite** (so "finitely presented" stays a type-level guarantee, no
predicate-pollution of word-reduction / Tietze machinery), and represent C as a spec pair
`(gens, relator_pred: spec_fn(Word)->bool)`. Build **`H₃` as the literal finite `Presentation` of
set (I)**; the embedding `C ↪ H₃` is then two lemmas on the map `φ: C → H₃`:
- **soundness** `relator_pred(w) ⟹ H₃ ⊢ φ(w)=1` — from (III)-as-consequence-of-(I);
- **completeness / faithfulness** `H₃ ⊢ φ(w)=1 ⟹ relator_pred(w)` — via `benign.rs`'s G∩L framing
  + the `spec_fn(Word)->bool` predicate-subgroup machinery (the `kp_pinch` HNN-faithfulness engine).

Consequence for brick order: the intermediate H₁/H₂ are **not** materialized as infinite
Presentations; they are recovered as subgroups of the finite H₃, with their defining relations
[(II) `p⁻¹t_α p = t_α w_α(b)d`, and S] holding as *derived theorems* in H₃. The h1/h2/h3 bricks
still organize the GENERATOR/RELATOR definitions (commutators, `p⁻¹tp=td`, the finite a_i/k HNN
associations — all of which ARE in finite set (I)); the faithfulness is brick 5. (Cross-checked with
Danielle's local model, 2026-06-20.)

### Brick 2 next (in progress): `h1.rs`
Finite, unambiguous-under-Approach-(b) pieces first — instantiate `word_numbering` maps at the
layout bases (`h_w_c`/`h_w_b`/`h_w_bc`) + the `n²` commutator relators `b_i c_j = c_j b_i` (a member
of set (I)) with validity. Then the K_M-relator embed + `p⁻¹tp=td` + the a_i/k HNN associations to
assemble set (I); the free-basis lemma + faithfulness are the deep tail (brick 5).
