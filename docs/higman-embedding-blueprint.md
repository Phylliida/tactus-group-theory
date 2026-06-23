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

> **VERIFIED TRANSCRIPTION (book p.279–281, scans read 2026-06-20).** The earlier draft of this
> section had two errors, now corrected: H₁ is a **free product** (not a direct product) and its
> middle factor carries `C`; and `A₋` uses `b_j c_j` (not `b_j`). Exact relators below.

Write `t_α := t(α,0)` (Layer-1 config word, `config_word(α,0)`). `{t_α : α∈I}` freely generate
(Layer-1 property (i)). `b_{n+i} := b_i⁻¹`.

1. **`H₁ = K_M ∗ (C × ⟨b₁,…,bₙ⟩) ∗ ⟨d⟩`** — a **FREE product** of three factors:
   - `K_M` = the Layer-1 machine group `G(M)`;
   - `C × ⟨b₁,…,bₙ⟩` = the **direct** product of `C=⟨c₁,…,cₙ;S⟩` with the free group on the `b_j`
     (so `c_i b_j = b_j c_i`, i.e. relation `b_i c_j = c_j b_i`); **this is where `C` lives**;
   - `⟨d⟩` = infinite cyclic.

   Mapping `H₁ → K_M` (identity on `K_M`, kill all other gens) and Cor 1 to Prop 1.8 ⟹
   `{ t_α w_α(b) d : α∈I }` is a **free basis** of the subgroup it generates.
2. **`H₂ = ⟨ H₁, p ∣ p⁻¹ t_α p = t_α w_α(b) d,  all α∈I ⟩`** — HNN, stable letter `p`.
   **`C ⊆ H₂`** (already `C ⊆ H₁`). The single "schematic" relation noted for later is
   `p⁻¹ t p = t d` (`α=0`: `t_0=t`, `w_0(b)=1`).
   `A := ⟨t, x, d, b_j (1≤j≤n), p⟩` is the HNN extension of free `F=⟨t,x,d,b_j (1≤j≤n)⟩` by `p`
   with those relations restricted to `α∈I` — i.e. `A` is itself the relevant `p`-HNN piece.
3. Subgroups for the top HNN (book p.280), all of `H₂`:
   - `A   = ⟨ t, x, d, b_j (1≤j≤n), p ⟩`
   - `A_i = ⟨ t_i, xᵐ, b_i d, b_j (1≤j≤n), p ⟩`   (for `1≤i≤2n`)
   - `A₊ = ⟨ U, d, b_j (1≤j≤n), p ⟩`
   - `A₋ = ⟨ U, d, b_j c_j (1≤j≤n), p ⟩`   ← **`b_j c_j`, the only difference from `A₊`**
   - `U = { t } ∪ { all r-symbols } ∪ { all l-symbols }` ⊆ `K_M` (= Layer-1 `g_subgens`).
     Faithfulness fact (Layer 1): `⟨U⟩ ∩ ⟨t_α : α∈I⟩ = ⟨t_α : α∈I, (α,0)∈H₀(M)⟩`
     — i.e. `t_α ∈ ⟨U⟩  ⟺  (α,0)∈H₀(M)` (this is `in_TM` / Theorem 1's `(vi)/(vii)`).
   - **Isomorphism `A → A_i`** (stated gens ↦ stated gens): `t↦t_i, x↦xᵐ, d↦b_i d, b_j↦b_j, p↦p`.
     Well-defined because `A`,`A_i` are HNN extensions of free groups on the stated generators with
     "the same" `p`-relations (uses `w_{αm+i}(b)=w_α(b) b_i`).
   - **Isomorphism `A₊ → A₋`** (stated gens ↦ stated gens): `U↦U (pointwise), d↦d, b_j↦b_j c_j, p↦p`.
     Inverse comes from the endomorphism of `H₂` killing every `c_j` (maps `A₋ → A₊`).
4. **`H₃ = ⟨ H₂, a_i (1≤i≤2n), k ∣ a_i: A ↔ A_i,  k: A₊ ↔ A₋ ⟩`** — HNN, stable letters `a_i, k`.
   I.e. `a_i⁻¹ g a_i = φ_i(g)` for the stated gens `g` of `A` (`φ_i = A→A_i` iso); `k⁻¹ h k = ψ(h)`
   for stated gens `h` of `A₊` (`ψ = A₊→A₋` iso). **`H₃ ⊇ C` and is FINITELY PRESENTED.**

**The finite presentation `H₃` — relation set (I), book p.281 (the payoff):**
- **(I)** (FINITE):
  - the finitely many **relations of `K_M`** (Layer 1: `A`-relation `xy=yx`, the `r_i`/`l_j` HNN
    relations, `k'`(=Layer-1 `k`) commutations — see `aanderaa-cohen-construction.md`);
  - `b_i c_j = c_j b_i` for `1≤i,j≤n`;
  - the single relation `p⁻¹ t p = t d`;
  - the finitely many HNN relations for `H₃`'s stable letters `a_i, k`: the `a_i: A↔A_i` and
    `k: A₊↔A₋` associations (each stated-gen ↦ stated-gen rule above).
- **(II)** (infinite) `p⁻¹ t_α p = t_α w_α(b) d`, all `α∈I`, `α≠0`.
- **(III)** (infinite) `w_α(c) = 1`, all `α∈I` with `(α,0)∈H₀(M)`.

**Cohen's argument that (II),(III) are consequences of (I)** (book p.281 — this IS the proof body):
- *(III) from (I)+(II):* If `(α,0)∈H₀(M)` then, by the relations of `K_M`, `t_α` is a product of
  elements of `U∪U⁻¹` (faithfulness). The `k`-relations fix `U` pointwise, and `k⁻¹pk=p`,
  `k⁻¹dk=d`, so `k⁻¹ t_α k = t_α`. Conjugating (II) `p⁻¹t_α p = t_α w_α(b)d` by `k` then gives
  `k⁻¹ w_α(b) k = w_α(b)`. But (I)'s `k: b_j ↦ b_j c_j` gives `k⁻¹ w_α(b) k = w_α(bc) =
  w_α(b)·w_α(c)` (the `c_j` commute with `b_i`, so `w_α(bc)` splits). Hence `w_α(c)=1`.
- *(II) from (I):* Write `w_α(b)` with only positive `b_i` (`1≤i≤2n`, `b_{n+i}=b_i⁻¹`); let
  `w_α(a)` replace each `b_i` by `a_i`. By induction on word length, (I) gives
  `w_α(a)⁻¹ t w_α(a) = t_α` and `w_α(a)⁻¹ d w_α(a) = w_α(b) d`. With `p⁻¹tp=td` and `a_i⁻¹ p a_i = p`
  (both in (I)), conjugating gives `p⁻¹ t_α p = t_α w_α(b) d`. Hence all of (II) follows from (I).
- *"Since (I) is finite, we have proved Higman's Embedding Theorem."*

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
2. **Layer 0.5** — HNN embedding countable → f.g. r.p. **SOURCE LOCATED (2026-06-23).** The Cohen
   book PDF in this crate is a SCANNED image (no text layer — un-greppable); use instead **Miller,
   *Combinatorial Group Theory*** (`../verus-group-theory/CGTMiller.pdf`, has a text layer), **§4.1
   Theorem 4.1 (Higman–Neumann–Neumann), PDF pp.53–54.** The exact construction:
   - Input: countable `C = ⟨c₁,c₂,…|D⟩`. Form `L = C ⋆ F` with `F = ⟨a,b⟩` free of rank 2.
   - Two subgroups, **both free with the listed free bases** (Miller's "previous discussion", p.53):
     `A = ⟨b, c₁a⁻¹ba, c₂a⁻²ba², …⟩` and `B = ⟨a, b⁻¹ab, b⁻²ab², …⟩`.
   - HNN `G = ⟨a,b,c₁,…,t | D, t⁻¹bt=a, t⁻¹cᵢa⁻ⁱbaⁱ t = b⁻ⁱabⁱ (i≥1)⟩`, `t` conjugating `A`'s basis
     to `B`'s. Then `b = tat⁻¹` and each `cᵢ = uᵢ(a,t)`, so **`G` is 2-generated by `{a,t}`**; Tietze
     to `G = ⟨a,t | D̄⟩`. `C ↪ L ↪ G` (free-product + HNN faithfulness). Corollary 4.2: same #relations.
   - **The crux foundational lemma** = `{a⁻ⁱbaⁱ : i≥0}` is a FREE FAMILY in `F = free_group(2)` ("the
     central `b` of each term survives free reduction"); `A`/`B` free bases generalize it in `L`.
   - **⚠ INFRASTRUCTURE PREREQUISITE (the real blocker, a foundational design decision — co-design
     with Danielle):** the input `C` (our CEER group `⟨gₙ | g_a g_b⁻¹⟩`, and the generic Miller `C`)
     is **infinitely generated**, but the substrate's `Presentation { num_generators: nat, … }` is
     **finite by construction**. So Layer 0.5 cannot even *state* `L = C ⋆ F` until we choose a
     representation for infinitely-generated groups (a predicate-presentation over ℕ-indexed gens, or
     an explicit ℕ→generator scheme). This is WHY Layer 0.5 is "deferred/parallel" — it needs new
     core infra the finitely-generated tower never did. The crux `{a⁻ⁱbaⁱ}`-free lemma is itself
     representation-independent (pure `F₂`), but is a fresh from-scratch normal-form arc: the existing
     freeness machinery (`f_free.rs`) descends via *structured retractions* and never computes a free
     normal form, so it needs a new `equiv_in_presentation(free_group(n)) ⟺ free-reduction` bridge +
     the b-survival cancellation analysis. The crux is buildable now (representation-independent); the
     *broader* Layer 0.5 (the `A`/`B` bases over the c's, `L`, `G`) is what waits on the infra decision.
   - **PROGRESS (2026-06-23) + the executable plan for the crux `{a⁻ⁱbaⁱ}`-free lemma:**
     - ✅ **The bridge DONE** (`free_word_problem.rs` 4/0, `lemma_free_group_equiv_freely_equivalent`):
       `equiv_in_presentation(free_group(n), w1, w2) ⟹ freely_equivalent(w1, w2)` (relator-free ⟹ every
       derivation step is a free reduction/expansion). The missing converse of
       `lemma_freely_equivalent_implies_equiv`.
     - **NEXT — the `{a⁻ⁱbaⁱ}`-free lemma** `is_free_family(free_group(2), conj_family(K))` where
       `conj_word(i) = symbol_power(Inv(0),i) ++ [Gen(1)] ++ symbol_power(Gen(0),i)` (a=Gen0, b=Gen1).
       Architecture for the forward obligation (build bottom-up; each sub-lemma verifies independently
       so partial progress banks cleanly):
       1. `w' = normal_form(w)` over `K` letters (`lemma_reduces_to_normal_form` / `_is_reduced`);
          `equiv(free_group(K), w, w')` via `lemma_reduces_to_equiv`. Goal ⟸ `w' = ε`.
       2. φ respects source equiv: `equiv(free_group(K), w, w') ⟹ equiv(free_group(2), φ(w), φ(w'))`
          via `lemma_emb_respects_source_equiv` (machine_group.rs) — relator condition VACUOUS for a
          free source. With the hypothesis `equiv(free_group(2), φ(w), ε)` ⟹ `equiv(·, φ(w'), ε)`.
       3. Bridge (done) ⟹ `freely_equivalent(φ(w'), ε)` ⟹ `reduces_to(φ(w'), ε)` (ε is reduced) ⟹
          `normal_form(φ(w')) = ε` (`lemma_reduces_to_reduced_unique`).
       4. **THE CORE (B)** — `w'` reduced (`is_reduced`) ∧ `|w'|>0` ⟹ `normal_form(φ(w')) ≠ ε`,
          contradicting 3 ⟹ `w' = ε`. **(B) is the real work** — the "central b survives" cancellation.
          Two routes (both ~200–400 lines of `reduce_at`/`subrange` surgery):
          • **spelled-form**: define `R(w') = a⁻ⁱ¹bᵉ¹a^(i₁−i₂)bᵉ²…bᵉⁿaⁱⁿ` (signed a-powers, recursive);
            prove `φ(w') reduces_to R(w')` (each `aⁱᵏa⁻ⁱᵏ⁺¹` junction cancels — induction), then `R(w')`
            `is_reduced` (a-blocks same-sign; empty-a junctions force same-sign b's since `w'` reduced)
            and `|R(w')|>0` (leftmost `bᵉ¹` survives); conclude via `lemma_reduces_to_reduced_unique`.
          • **count_b invariant**: `count_b(φ(w')) = |w'|` and free reduction of a φ-image never cancels
            a b (opposite-sign b's never become adjacent — `w'` reduced rules out the only way), so
            `count_b(normal_form(φ(w'))) = |w'| > 0`.
     - ✅ **counting infra DONE** (`conj_free.rs` 8/0): `count1` (#b-letters), additive/inverse-invariant/
       zero-on-a-powers, `lemma_count1_emb`: `count1(φ(w)) = |w|`. The count_b route's first half.
     - **THE CLEANER CORE INSIGHT (2026-06-23) — the net-exponent invariant** (recommended over the
       spelled-form): a free-reduction step removes an `a a⁻¹` (index-0) pair, which preserves the
       **signed sum of index-0 symbols between any two fixed b's**. So "the net index-0 exponent between
       consecutive b's" is a REDUCTION INVARIANT. In `φ(w')` that net between `bₖ, bₖ₊₁` is `iₖ − iₖ₊₁`.
       Two b's can only cancel if they become ADJACENT (their between-block empties) AND have opposite
       sign; the block empties ⟹ net = 0 ⟹ `iₖ = iₖ₊₁` ⟹ (w' reduced) `εₖ = εₖ₊₁` (SAME sign) ⟹ no
       cancel. So **no φ-image reduction ever cancels a b** ⟹ `count1(normal_form(φ(w'))) = |w'| > 0`.
       This avoids defining the explicit signed-exponent spelled form `R(w')`; instead carry the
       reduction invariant `no_adjacent_opposite_b ∧ (between consecutive b's: net=0 ⟹ same sign)` —
       preserved by `reduce_at`, holds for `φ(w')`, and forbids any index-1 cancellation. The remaining
       work = formalize "net index-0 exponent between consecutive index-1 symbols" + its `reduce_at`
       invariance + the φ(w')-base-case. (~150–250 lines; the next iteration's task.)
     - ✅ **CRUX COMPLETE 2026-06-23** (`conj_free_core.rs` 34/0, `lemma_conj_family_free`:
       `is_free_family(free_group(2), conj_family(k))`). Implemented exactly the net-exponent invariant
       above. Pieces (bottom-up, each banked independently):
       1. **`asum`** = signed index-0 (a) exponent; additive over concat; a length-2 inverse pair has
          `asum 0` (`lemma_asum_inverse_pair_zero`). Removing a non-b pair preserves `count1`
          (`lemma_count1_reduce_non_b`).
       2. **`bsep(w)`** = ∀ consecutive inverse-pair b-letters `p<q`: `asum(w[p+1..q]) ≠ 0`.
          `lemma_bsep_no_b_cancel`: under `bsep` every cancellation is a non-b pair (an adjacent b-pair
          would be a consecutive inverse-pair with empty `asum 0` block).
       3. **`lemma_reduce_preserves_bsep`**: `bsep` survives removing any non-b pair. Proof via the
          prefix-`asum` reformulation (`asum(w[a..b]) = pa(b) − pa(a)`) + `lemma_pa_reduce` (the removed
          pair, having `asum 0`, doesn't shift prefix exponents past the hole) — no fragile "literal word
          equality at the q==i boundary" needed.
       4. **`lemma_count1_bsep_invariant`** (induction mirroring `reduce_n_steps`): under `bsep`, every
          normal-form reduction step cancels a non-b pair, so `count1` and `bsep` both persist ⟹
          `count1(normal_form(w)) = count1(w)`.
       5. **Base case `lemma_bsep_emb`** (`bsep(φ(w'))` for reduced `w'`): `apply_embedding_symbol` of a
          source letter is `phi_block(s) = a⁻ᶜ b^{±} aᶜ` (`lemma_phi_block` + `lemma_inverse_conj_word`);
          head/tail induction (`lemma_emb_first_block`) with two consecutive-pair cases — boundary
          (head-b vs first-b-of-rest: `asum = c − c'`, nonzero since `w'` reduced ⟹ same-index ⟹ same
          sign) and inner (both in the rest, straight from the IH). Helpers `lemma_emb_first_b`,
          `lemma_concat_subrange_{right,mid}`.
       6. **Assembly `lemma_conj_family_free`**: the forward obligation `φ(w)≡_{F₂}ε ⟹ w≡_{free(k)}ε`
          (reduce `w→w'=nf(w)`, push equiv through φ via `lemma_emb_respects_source_equiv`, bridge to
          `nf(φ(w'))=ε`, then `|w'| = count1(φ(w')) = count1(ε) = 0`). Representation-independent — done
          ahead of the infinite-gen-`C` infra decision.
3. **Layer 2** — `H₁` (direct product), `H₂` (HNN, stable letter `p`), `H₃` (HNN, stable letters
   `a_i, k`); prove `C ↪ H₃` and `H₃` f.p. with relations (I). Re-read book p.279–281 (PDF 284–286)
   for the precise `A/A_i/A₊/A₋` generators and associations.
4. **Bridge** — reduce the ZFC register-machine enumerator to a classic modular machine `M` with
   `H₀(M)` = declared-pairs set; instantiate the tower; extract & print the explicit `H₃`.

All HNN/Britton tooling needed is already proven in tactus (`britton_via_tower`, `hnn`, `benign`,
free-group normal forms). This is intricate but canonical — no improvising relators.
