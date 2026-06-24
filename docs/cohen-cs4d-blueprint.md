# CS-4d backward (`b ⟹ a`) — the design blueprint

*Written 2026-06-23 (session 22), after a deep read-only pass + companion co-design. This note
**resolves** the open wrinkle flagged in `cohen-cs4-architecture.md` §4 (CS-4d) and **corrects** two
points there. Per the standing "no undesigned directions" rule, this is the blueprint to approve
before the deep build; the zero-risk pieces (slice arithmetic) are started in `cohen_cs4d.rs`.*

---

## 0. The goal and the chain

CS-4d is the `⟸` half of the a_i association iso `(★)` over the predicate base:

```
  emb(b_col, w) ≡_{h2_pred} ε   ⟹   emb(a_col, w) ≡_{h2_pred} ε
```

The reduction (same skeleton as the DONE forward `lemma_cs4c_forward`, but the hard core is
`map_b` faithful instead of `map_a` faithful):

1. **M1 factor** (`lemma_mapb_factor_source`): `emb(b_col, w) = emb(a_col, pw)`, `pw = emb(φ_l_src, w)`.
   So `emb(a_col, pw) ≡_{h2_pred} ε`.
2. **compactness + normalize** (CS-4b + CS-4c-prep, both DONE): a finite no-dup ∌0 number-word slice
   `norm` with `emb(a_col, pw) ≡_{h2_II(norm)} ε`.
3. **map_a forward** (`lemma_map_a_forward`, DONE): `pw ≡_{pa_data(betas(norm))} ε`,
   `betas(norm) = [0] ++ norm`.
4. **M2 (φ_l_src injective)**: convert `pw ≡_{pa_data(...)} ε` into `w ≡_{pa_data(bet)} ε`.
5. **a-von-Dyck** (`lemma_a_col_relator_trivial_pred` via `lemma_emb_respects_source_equiv_pred`,
   free / any number-word slice): `w ≡_{pa_data(bet)} ε ⟹ emb(a_col, w) ≡_{h2_pred} ε`.

Steps 1–3, 5 are DONE or trivial. **The whole of CS-4d is step 4.**

---

## 1. The obstruction (recap, sharpened)

`lemma_mapb_M2_rt` consumes `pw ≡_{pa_data(sigma_betas(bet))} ε` (target slice = **exactly**
`σbet = {mβ+l : β∈bet}`) and yields `w ≡_{pa_data(bet)} ε`. But step 3 yields
`pw ≡_{pa_data(betas(norm))} ε` with `betas(norm) = [0] ++ norm`. Two structural mismatches:

- **0-head**: `0 ∈ betas(norm)` is never a σ-image (`mβ+l ≥ l ≥ 1 > 0`).
- **non-σ junk**: a number-word `γ` is a σ_l-image **iff** `γ % m == l` (since `numbers_word` =
  every base-m digit ∈ `[1,2n]`, and `σ(β)=mβ+l` appends the digit `l`). `norm`'s elements have
  arbitrary last digit, so most are **not** σ-images.

So `betas(norm) ⊋ σbet` for any `bet`, and the monotone lift "more relators ⟹ still trivial"
needs `betas(norm) ⊆ σbet`, which fails. The junk associations (last digit `≠ l`, incl. the
0-head) are present in the slice but **never needed** to reduce the φ-image `pw` — this is exactly
Cohen Prop-1.34 recognition content.

---

## 2. Why the two "obvious" escapes both fail

- **Strengthen map_a to land in σbet** — FALSE for opaque words (the R4 comment in
  `phi_l_mapb_fwd.rs:1378`): a `pa_data(betas)` relator over `γ ∈ betas∖σbet` is trivial in `h2_II`
  but nontrivial in `P_A(σbet)`. There is no homomorphism `pa_data(S) → pa_data(σbet)` fixing
  φ-images (it would have to kill `config(γ,0)` for junk `γ` while fixing `config(δ,0)` for σ-image
  `δ` — impossible, they share `t,x`).
- **"Purify" `pw` as black-box preprocessing** (`pw ≡_{pa_data(S)} ε ⟹ pw ≡_{pa_data(σbet)} ε`,
  then feed M2_rt unchanged) — reducing `pw` **directly** hits the **R4 invariant-loss**: after one
  pinch-out, the word is no longer a φ-image, so induction on `pw`'s reduction can't keep the
  recognition invariant. **This is why the companion's "Option A" does not actually work** — the
  recognition cannot be decoupled from the source recursion.

The escape that DOES work uses the same insight that makes M2_rt avoid R4: **recurse on the source
`w`** (re-deriving `pw = φ(w)` fresh each level), so the φ-image structure is maintained *by
construction*.

---

## 3. The route — `M2_general` (additive copy of M2_rt over a superset slice)

Build `lemma_mapb_M2_general(mm, n, m, l, bet, S, w)`:

```
  requires  σbet := sigma_betas(bet) ,  σbet ⊆ S (sub-slice),  S/bet no-dup number-words,
            hnn_associations_isomorphic(pa_data(S)),         // ← needs the GENERAL iso (§4.1)
            (∀ γ∈S. γ%m==l ⟹ (γ/m)∈bet),                     // bet = all σ-preimages in S
            word_valid(w, n+4),
            equiv_in_presentation(hnn_presentation(pa_data(S)), pw, ε)
  ensures   equiv_in_presentation(hnn_presentation(pa_data(bet)), w, ε)
  decreases stable_count(pa_data(bet), w)
```

It is `lemma_mapb_M2_rt` **verbatim** except three steps, where `pdt := pa_data(S)` replaces
`pa_data(σbet)`:

| step | M2_rt | M2_general | new work |
|---|---|---|---|
| 1. find pinch | `britton_lemma_full(pa_data(σbet), pw)` | `britton_lemma_full(pa_data(S), pw)` | needs **general iso** of `pa_data(S)` (§4.1) |
| 1b. **recognition** | — | `has_pinch(pa_data(S),pw) ⟹ has_pinch(pa_data(σbet),pw)` | **the crux single-pinch lemma** (§4.2) |
| 2. descend | `lemma_mapb_pinch_descends_rt` (σbet→bet) | **same, UNCHANGED** | — (reuses the 340-line descent!) |
| 3. pinch out `w` over `pa_data(bet)` | as-is | as-is | — |
| 4. φ respects relators | into `pa_data(σbet)` | into `pa_data(S)` | monotone (more relators) — trivial generalization of `lemma_phi_l_src_on_pa_relator_retarget` |
| 5. recurse | `M2_rt(wshort)` | `M2_general(wshort)` same `S` | — |

The insertion of step 1b after `britton_lemma_full` is the whole trick: it converts the pinch found
over the big slice into a pinch over the exact σbet slice, so the **existing, proven** descent and
the **existing, proven** M2_rt recursion shape both apply with no edits to `phi_l_mapb_fwd.rs`.

### CS-4d assembly (once `M2_general` exists)
`emb(a_col,pw) ≡_{h2_pred} ε` → compactness+normalize → `pw ≡_{pa_data(betas(norm))} ε`
[`S := betas(norm)`] → choose `σbet := filter(S, %m==l)`, `bet := map(σbet, /m)` →
`M2_general(bet, S, w)` → `w ≡_{pa_data(bet)} ε` → a-von-Dyck → `emb(a_col,w) ≡_{h2_pred} ε`. ∎

---

## 4. The two genuinely-new lemmas (everything else reuses proven machinery)

### 4.1 General `pa_data` iso (the missing precondition)
`lemma_pa_data_isomorphic` only covers the `betas(alphas)` (0-head) form via the `recog_data`
correspondence. `σbet`/`S` are not `betas`-form, and **nothing currently supplies M2_rt's
`hnn_associations_isomorphic(pa_data(σbet))` precondition** (M2_rt was built but never top-called).

Prove instead, for ANY no-dup number-word slice `S`:
```
  hnn_associations_isomorphic(pa_data(n, m, S))
```
**directly from freeness**, bypassing `recog_data`: the a-column is `config_emb(S) = {x⁻ᵞtxᵞ}`
(free family — `lemma_conj_family_free`) and the b-column is `pa_rhs_emb(S) = {config(γ,0)·w_γ(b)·d}`
= the basis elements (free — `lemma_basis_elt_free`, `free_basis.rs`). Two free families of equal
rank `|S|` ⟹ the index-bijection `a[i]↦b[i]` extends to a subgroup iso ⟹ associations-iso. Bridge
tool = `free_family_injective` (+ a short "equal-rank free ⟹ index-bijection iso" glue). Strictly
more general than `lemma_pa_data_isomorphic`; CS-5 reuses it.

### 4.2 The recognition crux (single pinch, image level — NO recursion, NO R4)
```
  lemma_phi_pinch_in_sigbet(S, bet, w, i, j):
    has_pinch_at(pa_data(S), emb(φ_l_src, w), i, j)
      ⟹  has_pinch_at(pa_data(σbet), emb(φ_l_src, w), i, j)
```
A pinch fixes positions `i,j`; the middle `mid ∈ ⟨config_emb(S)⟩` (a-side associated subgroup). The
middle is a φ_F-image, so by **`lemma_phi_canon_invariant`** its canonical config coordinates satisfy
**`cong_l`** (`≡ l mod m`); by **`lemma_sat_bridge`** each such coordinate is a `σ(bet)`-coordinate
(using `bet = all σ-preimages in S`). Hence `mid ∈ ⟨config_emb(σbet)⟩`, so the SAME positions `i,j`
witness a pinch over `pa_data(σbet)`. The pure-subgroup core:
```
  lemma_phi_image_config_support(u, S):
    word_valid(u, n+3),  emb(φ_F, u) ∈ ⟨config_emb(S)⟩,  (S no-dup number-words; bet=preimages)
      ⟹  emb(φ_F, u) ∈ ⟨config_emb(σbet)⟩
```
This is a **sibling of `lemma_r_prime`** (same `phi_canon_invariant`/`cong_l` technique, different
conclusion — support ⊆ σbet instead of bet→σbet). It is squarely within the established `r_prime.rs`
σ-recognition idiom — **not a new direction**. (`lemma_r_prime` goes `bet → σ(bet)`; this goes
`S → σ-images-in-S`; both are the cong_l coordinate argument.)

---

## 5. Slice arithmetic (zero design risk — pure Seq; build first, in `cohen_cs4d.rs`)

For `S` no-dup number-words (e.g. `S = betas(norm)`):
- `sigbet_of(S) := S.filter(|γ| γ % m == l)` — the σ-image elements of `S`.
- `bet_of(S) := sigbet_of(S).map(|γ| γ / m)` — their σ-preimages.
- Lemmas (all pure-Seq induction):
  - `sigma_betas(bet_of(S)) =~= sigbet_of(S)` (round-trip: `γ%m==l ⟹ σ(γ/m)=γ`).
  - `sigbet_of(S)` is a sub-slice of `S` (⊆), no-dup, number-words.
  - `bet_of(S)` no-dup (σ injective on the filtered set), number-words (`γ/m` digits ⊆ `γ` digits).
  - `∀γ∈S. γ%m==l ⟹ (γ/m) ∈ bet_of(S)` (the "bet = all preimages" condition for §4.2).

---

## 6. Status / honest risk read

- **Slice arithmetic (§5)**: zero risk, pure Seq. Build now.
- **General iso (§4.1)**: moderate; reuses `lemma_conj_family_free` + `lemma_basis_elt_free`; the
  only new glue is "equal-rank free families ⟹ index-bijection iso". Low design risk.
- **Recognition crux (§4.2)**: the real work, but **de-risked** — the hard coordinate-tracking
  (`lemma_phi_canon_invariant`, `cong_l`, `lemma_sat_bridge`) is **already proven**; the crux is a
  sibling assembly of it. The single-pinch / image-level framing **kills the R4 invariant-loss**.
- **`M2_general` (§3)**: an additive ~250-line copy of `lemma_mapb_M2_rt` with 3 changed steps; the
  340-line descent and the recursion shape are reused unchanged.

**Net**: CS-4d reduces to two new lemmas (§4.1, §4.2) + slice arithmetic (§5) + an additive M2 copy
(§3). No edits to the proven `phi_l_mapb_fwd.rs` descent; no new infinite-association substrate; no
σ-closure (the vacuous `sigma_fwdsat`/R4 finite-slice route is **not** used). Recommend: build §5,
then §4.1, then §4.2, then assemble §3 + CS-4d.
