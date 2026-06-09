# Layer 2 — Higman embedding of a recursively presented group (blueprint)

Source: D. E. Cohen, *Combinatorial Group Theory: A Topological Approach* (1989),
**§9.4 (modular machines, p.265–267)** and **§9.6 (Higman's embedding theorem, p.274–281)**.
PDF in `tactus-group-theory/` (scanned, image-only). Read via: `pypdf` → `page.images[0]`
(TIFF) → Pillow `.save('.png')` → Read tool. **Page offset: PDF page = book page + 5.**
So §9.6 = PDF 279–286; §9.4 = PDF 270–272.

This sits ON TOP of Layer 1 (the machine group `K_M = G(M)`, see `aanderaa-cohen-construction.md`).

## The bridge: word-numbering (book p.279)

`C = ⟨c₁,…,cₙ ; S⟩` a **finitely generated** recursively presented group (`S` = r.e. set of
relators, words in the free monoid on `c₁,…,c₂ₙ` where `c_{n+i}=c_i⁻¹`). Number words:
`w₀(c)=1`, `w_i(c)=c_i` (i≤2n), `w_{αm+i}(c)=w_α(c)·c_i`. Let `I = {α : α numbers a word}`.
`w_α(b)`, `w_α(bc)`: replace each `c_j^{±1}` (j≤n) by `b_j^{±1}` resp. `(b_j c_j)^{±1}` (new letters `b_j`).

Take the modular machine `M` (and modulus `m`) so that:
> **`w_α(c) ∈ S  ⟺  (α,0) ∈ H₀(M)`**   (the relator set realized by the machine).

## The HNN tower (book p.280–281), ending in the f.p. group H₃

Write `t_α := t(α,0)` (Layer-1 config word). `{t_α : α∈I}` freely generate.

1. **`H₁ = K_M × ⟨b₁,…,bₙ⟩ × ⟨d⟩`** (direct product; `b_{n+i}=b_i⁻¹`).
   `{ t_α w_α(b) d : α∈I }` is a free basis of the subgroup it generates (Prop 1.8 Cor 1).
2. **`H₂ = ⟨ H₁, p | p⁻¹ t_α p = t_α w_α(b) d,  all α∈I ⟩`** — HNN, stable letter `p`.
   **`C` embeds in `H₂`** (via `c_j ↦ b_j`-ish; the `S`-relators become derivable).
   The single "schematic" relation is `p⁻¹ t p = t d`; the family over `α∈I` follows.
3. Subgroups for the next HNN (book p.280):
   - `A   = ⟨ t, x, d, b_j (1≤j≤n), p ⟩`
   - `A_i = ⟨ t_i, xᵐ, b_i d, b_j (1≤j≤n), p ⟩`   (for 1≤i≤2n)
   - `A₊ = ⟨ U, d, b_j, p ⟩`, `A₋ = ⟨ U, d, b_j, p ⟩` where **`U = { t, all r-symbols, all l-symbols }`**
     (`U ⊆ K_M`; `⟨U⟩∩K_M = ⟨t_α : (α,0)∈H₀(M)⟩` = the faithfulness fact from Layer 1).
4. **`H₃ = ⟨ H₂, a_i (1≤i≤2n), k | a_i: A ↔ A_i,  k: A₊ ↔ A₋ ⟩`** — HNN, stable letters `a_i, k`.
   **`H₃` contains `C` and is FINITELY PRESENTED.**

**The finite presentation `H₃` — relation set (I), book p.281 (the payoff):**
- the finitely many **relations of `K_M`** (Layer 1: A-relations `xy=yx`, the `r_i`/`l_j` HNN
  relations, `k'` commutations — see Layer-1 doc);
- `b_i c_j = c_j b_i` for `1≤i,j≤n`;
- `p⁻¹ t p = t d`;
- the finitely many HNN relations for the stable letters `a_i, k` of `H₃` (the `A↔A_i`, `A₊↔A₋`
  associations above).

Cohen proves the infinite families **(II)** `p⁻¹ t_α p = t_α w_α(b) d` and **(III)** `w_α(c)=1`
for `(α,0)∈H₀(M)` are *consequences* of the finite set (I). *"Since (I) is finite, we have proved
Higman's Embedding Theorem."*

## Full chain for our goal (and a needed pre-layer)

Cohen's `C` is **finitely generated**; our CEER group `⟨gₙ | g_a g_b⁻¹ : a~b⟩` is **infinitely
generated**. So:

- **Layer 0.5 (pre-step):** embed the (countable, recursively presented) CEER group into a
  **finitely generated** recursively presented `C = ⟨c₁,…,cₙ; S⟩` — the Higman–Neumann–Neumann
  embedding of a countable group into a 2-generator group (Cohen calls the relevant result "the
  Embedding Theorem", referenced p.278; locate its statement/§ and add relators here).
- **Layer 1:** `K_M = G(M)` with `(α,0)∈H₀(M) ⟺ [k', t_α]=1` and `w_α(c)∈S ⟺ (α,0)∈H₀(M)`.
- **Layer 2:** `H₁ → H₂ → H₃` above; `H₃` f.p., contains `C` ⊇ CEER group.
- `f(σ) = ` image of `g_{code(σ)}` in `H₃`. Then `f(σ)=f(τ) ⟺ ZFC⊢σ↔τ`. **Print `H₃`.**

## Build order (each layer reads its exact relators from the cited pages at build time)

1. **Layer 1 `K_M`** — obligations A–F in `aanderaa-cohen-construction.md` (faithfulness E via
   `britton_lemma_full` is the crux). Build first; everything rests on it.
2. **Layer 0.5** — HNN embedding countable → f.g. r.p. (locate Cohen's "Embedding Theorem" §, ~earlier
   in ch.9 or ch.1/HNN chapter; transcribe relators).
3. **Layer 2** — `H₁` (direct product), `H₂` (HNN, stable letter `p`), `H₃` (HNN, stable letters
   `a_i, k`); prove `C ↪ H₃` and `H₃` f.p. with relations (I). Re-read book p.279–281 (PDF 284–286)
   for the precise `A/A_i/A₊/A₋` generators and associations.
4. **Bridge** — reduce the ZFC register-machine enumerator to a classic modular machine `M` with
   `H₀(M)` = declared-pairs set; instantiate the tower; extract & print the explicit `H₃`.

All HNN/Britton tooling needed is already proven in tactus (`britton_via_tower`, `hnn`, `benign`,
free-group normal forms). This is intricate but canonical — no improvising relators.
