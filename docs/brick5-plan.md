# Brick 5 — the Higman payoff: `C ↪ H₃` faithful + `H₃` finitely presented

Layer 2 final brick (AGENDA §3.2). Builds on the finished tower (`h1`/`h2`/`h3`, all valid finite
presentations of Cohen's set (I)) and the **free-basis lemma** (`free_basis.rs` 29/0).
Module: `higman_consequences.rs`.

## The headline = the BRIDGE THEOREM

Avoid abstract `C` / Layer 0.5 for now (those are §3.3 *instantiation*). The real mathematical
content of Brick 5 is, for `α ∈ I` (α numbers a word):

> **`h3_pres(mm,n,m) ⊢ w_α(c) = 1   ⟺   (α,0) ∈ H₀(M)`.**

Combined with Layer 1 (`lemma_theorem1`: `[k',t_α]=1 ⟺ (α,0)∈H₀`), this realizes the c.e. set
`S = { w_α(c) : (α,0)∈H₀(M) }` as the word problem of the **finite** presentation `h3_pres`.
That *is* Higman's embedding theorem made explicit: a recursively-presented `C=⟨c;S⟩` sitting inside
the f.p. `H₃`, with `S` recovered as `H₃`'s relations among the `c`'s.

- **⟸ (SOUNDNESS):** `(α,0)∈H₀(M) ⟹ h3_pres ⊢ w_α(c)=1`. = Cohen's "(II),(III) are consequences
  of (I)". **This session.** Bounded, top-down, builds only on proven infra.
- **⟹ (COMPLETENESS):** `h3_pres ⊢ w_α(c)=1 ⟹ (α,0)∈H₀(M)`. The deep faithfulness. **Deferred**
  (separate arc; routing analysis below).

## SOUNDNESS — decomposition (Cohen p.281 proof body)

All relations live AT a tower level and lift up to `h3_pres` via `lemma_base_embeds_in_hnn`
(HNN base embeds). Sub-bricks, bottom-up:

0. **Lifting helpers.** `equiv in h2_pres ⟹ equiv in h3_pres`; `equiv in h3_upto(l) ⟹ … h3_pres`.
   Repeated `lemma_base_embeds_in_hnn` up the iterated tower. (Foundational, low-risk.)
1. **`w_bc` split** (Brick-1 leftover, pure `h1_base`): `h1_base ⊢ w_α(bc) ≡ w_α(b)·w_α(c)`.
   Induction on α's digits; reorder `b_i c_j → c_j b_i` via the `comm_relators` of set (I). Lifts
   to `h3_pres`. **Self-contained — good first deliverable.**
2. **`config(r,0)=x⁻ʳtxʳ`** + the a_i power-conjugation algebra. `config_word(r,0)` already unfolds
   to `x⁻ʳ·t·xʳ` (the s=0 case; y-powers vanish). Need `a_i⁻¹ xᵏ a_i ≡ x^{mk}` and reassembly.
3. **(IIa)** `w_α(a)⁻¹ t w_α(a) ≡ t_α` and **(IIb)** `w_α(a)⁻¹ d w_α(a) ≡ w_α(b) d`, by induction
   on α's digits. Step α↦αm+i uses the `a_i` HNN conjugations (`φ_i`): `a_i⁻¹ x a_i = xᵐ`,
   `a_i⁻¹ t a_i = t_i = config(i,0)`, `a_i⁻¹ d a_i = b_i d`, `a_i⁻¹ b_j a_i = b_j`, `a_i⁻¹ p a_i = p`.
   The clean tool is `lemma_stable_conj_factorization` (telescope: `a⁻¹·emb(A_gens,u)·a ≡ emb(A_i_gens,u)`).
   - `w_α(a)` = `w_α(b)` with `b_i ↦ a_i` (the stable letters). Define `w_a(α)`.
4. **(II)** `p⁻¹ t_α p ≡ t_α w_α(b) d`. From (IIa): `t_α ≡ w_α(a)⁻¹ t w_α(a)`; `p` commutes with each
   `a_i` (`a_i⁻¹ p a_i=p`) ⟹ commutes with `w_α(a)`; `p⁻¹ t p = t d` (`lemma_h2_p_conjugates_t`);
   regroup with (IIa)+(IIb).
5. **(III)** `w_α(c) ≡ 1`. From `(α,0)∈H₀ ⟹ t_α∈⟨U⟩` (Layer-1 (vii) easy half), `k` fixes `U`
   pointwise (`ψ:U↦U`), `k⁻¹pk=p`, `k⁻¹dk=d` ⟹ `k⁻¹ t_α k ≡ t_α`. Conjugate (II) by `k`:
   LHS `k⁻¹(p⁻¹t_α p)k ≡ p⁻¹ t_α p ≡ t_α w_α(b) d` (II); RHS `k⁻¹(t_α w_α(b) d)k ≡ t_α·(k⁻¹w_α(b)k)·d`.
   `ψ:b_j↦b_jc_j` ⟹ `k⁻¹ w_α(b) k ≡ w_α(bc)` ⟹ (split, sub-brick 1) `≡ w_α(b)w_α(c)`. Equate ⟹
   `w_α(c) ≡ 1`. ∎

## COMPLETENESS — routing analysis (DEFERRED, but the key insight is here)

**The trap.** A naive Britton peel ("`w_α(c)` has no `k`/`a_i`/`p`, so peel down to free `h1_base`
⟹ `w_α(c)` freely trivial") CONTRADICTS soundness. Reason: in `h3_pres` the `c`'s are **not free**
— `ψ:b_j↦b_jc_j` means `c_j = b_j⁻¹ k⁻¹ b_j k`, so the `c`'s are *resolved by k-conjugation*.
Equivalently, the k-HNN association `ψ:A₊↔A₋` is **NOT a faithful iso in the free-c base**, and its
(non-)iso-ness *is* the faithfulness we're proving. So `britton_lemma_full` (which REQUIRES
`hnn_associations_isomorphic`) does **not** apply directly to `h3_pres`'s k-layer.

**The resolution (the bridge between Approach-(b) and Cohen's with-S group).**
Soundness proves *every* `S`-relation `w_α(c)` (for `(α,0)∈H₀`) is a consequence of (I), i.e.
holds in `h3_pres`. Therefore adding `S` changes nothing:

> **`h3_pres  =  h3_with_S`  as groups** (a quotient by relations that already hold is identity).

So the word problems coincide: `h3_pres ⊢ w=1 ⟺ h3_with_S ⊢ w=1`. In the **with-S** tower, the
`φ_i`/`ψ` associations ARE genuine isomorphisms (Cohen's design), so the tower is Britton-faithful
and `britton_lemma_full` applies. Completeness is then the classical peel in `h3_with_S`, transferred
back to `h3_pres` via the group equality.

The catch: `h3_with_S` carries the **infinite** relator set `S`. Two ways to handle it:
- **Route A (benign G∩L):** keep presentations finite; carry `S` as a `spec_fn(Word)->bool`
  predicate; realize `C=⟨c;S⟩` as `G∩L` in a f.p. group (`benign.rs`) and run the predicate-subgroup
  `kp_pinch` engine. The c.e. set is recovered as the intersection, *controlled by Layer-1
  faithfulness* `t_α∈⟨U⟩ ⟺ (α,0)∈H₀`.
- **Route B (direct):** the local-model's pick — Britton's "trivial ⟹ pinch" is the filter; a
  k-pinch on `w_α(c)` translates to `t_α∈⟨U⟩` (the **Pinch-to-Membership lemma**), then Layer-1
  closes it. Clean *idea*, but needs a Britton variant not gated on full ψ-iso (or the with-S group).

**The single circularity-breaker (both routes):** Layer-1's `t_α∈⟨U⟩ ⟺ (α,0)∈H₀` (`in_TM`/(vi)/(vii),
`lemma_theorem1`). That is where a group-theoretic equality becomes a machine-halting statement.

**Recommendation for the completeness arc:** establish `h3_pres = h3_with_S` (free corollary of
soundness), then prove completeness in the with-S group via the `kp_pinch` predicate engine (Route A
mechanics) — `ψ`/`φ_i` iso-validity in with-S reduces to Layer-1 faithfulness, no circularity.

## Build order (this session)
1. `higman_consequences.rs` skeleton + sub-brick 0 (lifting helpers) — verify, commit.
2. sub-brick 1 (`w_bc` split) — verify, commit.
3. sub-bricks 2–3 (config algebra + (IIa)/(IIb)) — the meat.
4. sub-bricks 4–5 ((II) + (III)) — assemble the soundness headline.
