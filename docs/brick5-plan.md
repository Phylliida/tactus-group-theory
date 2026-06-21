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

## Build order + STATUS (`higman_consequences.rs`, 28/0 so far)

- [x] **sub-brick 0 — lifting helpers** (`lemma_h3_upto_in_h3`, `lemma_h2_in_h3`, `lemma_h1_in_h3`,
      `lemma_h3_upto_climbs`). Lift any tower level → `h3_pres` via `lemma_base_embeds_in_hnn`.
- [x] **keystone forward lift `base_A → h3_pres`** (`lemma_base_A_in_h3`): `lemma_lift_to_gm`
      (existing, K_M tower) → `lemma_gm_in_h1` (NEW — g_m→h1_base derivation replay; prefix relators
      + MORE generators, so neither `extends_presentation` nor `relators_included` applies) →
      `lemma_h1_in_h3`. **Every base_A config fact now lifts to H₃.**
- [x] **generic commutation algebra** (`commutes`, `lemma_commutes_{empty_right,sym,concat_right,inv_right}`,
      `lemma_gen_commute_to_combos`). Reused in sub-brick 1 AND (II)/(III).
- [x] **sub-brick 1 — `w_bc` split** (`lemma_w_bc_split`): `h1 ⊢ w_α(bc) ≡ w_α(b)·w_α(c)`. Supporting:
      `lemma_h1_comm_relator_identity`, `lemma_bc_gen_commute`, `lemma_b_alpha_commutes_c_{symbol,word}`,
      `lemma_bc_letter_split`.
- [x] **sub-brick 2 keystone — `lemma_a_conj_config`**: `a_l⁻¹·config(α,0)·a_l ≡ config(α·m+l,0)` in
      H₃ (1≤l≤2n). Via `lemma_stable_conj_factorization` (telescope at level l) + `conj_u`/`lemma_emb_conj_u`
      (`emb(a_gens/b_gens, u)` using `lemma_emb_signed_scaled`) + `lemma_conj_config_signed_by_x`
      (base_A config-move) + `lemma_config_signed_matches_nat`, lifted by `lemma_a_conj_config`'s
      `lemma_h3_upto_in_h3` + `lemma_base_A_in_h3`.

### REMAINING (next session) — sub-bricks 3–5
- [ ] **w_a spec fn**: `w_a(nk,n,m,α)` = `w_α(b)` with each digit-letter `b_i` replaced by the POSITIVE
      stable letter `a_digit = Gen(a_idx(nk,n,digit))` (NB: there are 2n a-stable-letters a₁…a₂ₙ, one per
      digit value — NO inverse convention, unlike the n-letter b/c alphabet). Snoc recursion mirrors `w_c`.
- [ ] **sub-brick 3 — (IIa)/(IIb)** by induction on α's digits:
  - **(IIa)** `w_α(a)⁻¹·t·w_α(a) ≡ t_α = config(α,0)`. Step α↦αm+l: `(w_α(a)·a_l)⁻¹ t (w_α(a)·a_l)
    = a_l⁻¹·(w_α(a)⁻¹ t w_α(a))·a_l ≡ a_l⁻¹·config(α,0)·a_l ≡ config(αm+l,0)` (IH + `lemma_a_conj_config`
    + "conjugation-by-a_l respects ≡" = concat_left/right). Need `inverse_word(w_α(a)·a_l) = a_l⁻¹·w_α(a)⁻¹`
    (`lemma_inverse_concat`).
  - **(IIb)** `w_α(a)⁻¹·d·w_α(a) ≡ w_α(b)·d`. Analogous, but the per-digit step uses the φ_l relation
    `a_l⁻¹ d a_l ≡ alphabet_letter(b_base,n,l)·d` (`lemma_hnn_conjugation` on `phi_assoc` head[2], lifted).
    Build a companion keystone `lemma_a_conj_d`: `a_l⁻¹·(W·d)·a_l ≡ (W·b_l)·d`-style, OR conjugate d
    directly then prepend. The b_l here IS `alphabet_letter(b_base,n,l)` (inverse convention) ⟹ result is
    `w_c(b_base,…) = w_α(b)`.
- [x] **sub-brick 4 — (II) DONE** (`lemma_II`): `p⁻¹·t_α·p ≡ t_α·w_α(b)·d`. `p` commutes with `w_α(a)`
      (`lemma_p_commutes_a_letter` via `lemma_commute_from_conj` on φ_l tail + `lemma_p_commutes_wa`);
      `p⁻¹ t p ≡ t d` (`lemma_h2_p_conjugates_t` lifted via `lemma_h2_in_h3`); (IIa)+(IIb); full
      conjugation-commute chain.

### SOUNDNESS COMPLETE — sub-brick 5 (III) DONE (`higman_consequences.rs` 60/0)
- [x] **(III) DONE** (`lemma_III`): `(α,0)∈H₀(M) ⟹ w_α(c) ≡ 1` in `h3_pres`. THE HEADLINE.
      Stage A `lemma_k_conj_wb` (`k⁻¹ w_α(b) k ≡ w_α(bc)`: per-letter `lemma_k_conj_b_letter` +
      `lemma_conj_distributes` induction; ψ-bcblock via `lemma_psi_bcblock_conj`/`lemma_psi_conj_in_h3`).
      Stage B `lemma_k_commutes_t_alpha` (k fixes t_α: `lemma_h0_config_in_subgroup` → `lemma_bm_in_h3`
      → `lemma_k_commutes_diag` per U-factor → `lemma_commutes_respects_equiv_right`). Stage C: helpers
      `lemma_k_fixes_V` (k fixes `V=p⁻¹t_α p`), `lemma_k_conj_W` (`k⁻¹Wk ≡ t_α w_α(bc) d`),
      `lemma_cancel_both_sides` (`X·Z≡(X·Y)·Z ⟹ Y≡ε`). `lemma_III` conjugates (II) by k and cancels.
      (Split into helpers to stay under rlimit.) Also reusable: `lemma_equiv_inverse`,
      `lemma_conj_of_commuting`.

**The whole soundness direction of the Higman bridge theorem `h3_pres ⊢ w_α(c)=1 ⟸ (α,0)∈H₀(M)` is
machine-checked.** Remaining for the full bridge theorem ⟺: the COMPLETENESS direction (⟹), a
separate large arc — see the routing analysis above (`h3_pres = h3_with_S`; benign/kp_pinch engine).

#### (III) — original plan (now realized)
- [x] **(III)** `(α,0)∈H₀(M) ⟹ w_α(c) ≡ 1` in `h3_pres`. Precise plan (all pointers confirmed):
  - **k-conjugation is DIRECT in `h3_pres`** = `hnn_presentation(psi_data)`, `psi_data = {base: h3_upto(2n),
    associations: psi_assoc(mm,n)}`, `k = Gen(k_top)`. No lifting for k-facts: use `lemma_hnn_conjugation(psi_data, i)`
    / `lemma_stable_conj_factorization(psi_data, u)` straight at `h3_pres`. `psi_assoc` layout:
    `psi_ublock` (len `nu = g_subgens.len() = 1+|quads|`) ++ `[d↦d]` (idx `nu`) ++ `psi_bcblock` (b_j at idx
    `nu+1+(j-1)`, j∈1..n) ++ `[p↦p]` (idx `nu+1+n`).
  - **Stage A — `k⁻¹ w_α(b) k ≡ w_α(bc)`**: per-letter `k⁻¹·alphabet_letter(b_base,n,d)·k ≡ bc_letter(d)`
    (ψ bcblock at idx `nu+j`; positive b from `lemma_hnn_conjugation`, inverse-digit via inverse), then induct
    on α's digits with `lemma_conj_distributes` (machine_group: `[k⁻¹](X+Y)[k] ≡ ([k⁻¹]X[k])([k⁻¹]Y[k])`).
  - **Stage B — `k` commutes with `t_α`**: `lemma_h0_config_in_subgroup(mm,α,0)` (`(α,0)∈H₀ ⟹
    in_generated_subgroup(b_m, g_subgens, t_α)`) → lift the witness equiv `concat_all(factors) ≡ t_α` to
    `h3_pres` (NEW `lemma_bm_in_h3` = `lemma_base_embeds_in_hnn`(g_m k'-HNN) → `lemma_gm_in_h1` →
    `lemma_h1_in_h3`) → `k` commutes with each `g_subgens` factor (ψ ublock `u↦u`, `lemma_hnn_conjugation` +
    `lemma_commute_from_conj`) → `lemma_commutes_concat_right` over the factor list → `commutes(k, concat_all)`
    → `commutes(k, t_α)` (NEW `lemma_commutes_respects_equiv_right`). Also `k` commutes with `p`,`d`
    (ψ `p↦p`,`d↦d`).
  - **Stage C — assemble + cancel**: conjugate (II) `V≡W` (V=`p⁻¹t_α p`, W=`t_α w_α(b) d`) by k:
    `k⁻¹Vk ≡ V` (k commutes with p,t_α ⟹ with V); `k⁻¹Wk ≡ t_α·w_α(bc)·d` (distribute via
    `lemma_conj_distributes`; k commutes with t_α,d; Stage A) `≡ t_α w_α(b) w_α(c) d` (sub-brick 1 `lemma_w_bc_split`
    lifted via `lemma_h1_in_h3`). So `t_α w_α(b) d ≡ t_α w_α(b) w_α(c) d` ⟹ `w_α(c) ≡ ε` (NEW
    `lemma_cancel_both_sides(p,X,Y,Z): X+Z ≡ X+Y+Z ⟹ Y ≡ ε`, X=t_α·w_α(b), Y=w_α(c), Z=d).

Cast gotcha learned: `(a*b) as int == (a as int)*(b as int)` for nats needs `by (nonlinear_arith)`
with the product INLINED (a `let mam = …` binding is opaque inside the nonlinear block).
