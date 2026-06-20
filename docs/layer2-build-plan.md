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
