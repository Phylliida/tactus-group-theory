# E2.C — generic property-II (the central engine). Design.

Goal (one HNN level `HNN(H,p)`, associations `(aₖ,bₖ)` i.e. `p⁻¹aₖp=bₖ`, `A₊=⟨aₖ⟩`, `A₋=⟨bₖ⟩`):
> `g` over `H` (no stable letter) ∧ `g ∈ ⟨K,p⟩`  ⟹  `g ∈ K`,
for any `K ≤ H` with the **compatibility** `φ(K∩A₊)=K∩A₋` (where `φ(a)=p⁻¹ap`).

This is the HNN subgroup-intersection lemma. No tooling exists; built on `britton_lemma_full`.

## The representation: a ⟨K,p⟩-word is ALTERNATING, not flat

A flat factorization (`in_generated_subgroup`) hides the structure pinch-elimination needs. Instead:

```
KPWord = (head: Word, tail: Seq<(bool, Word)>)
//   value = head · p^{s₁} · k₁ · p^{s₂} · k₂ · … · p^{sₙ} · kₙ
//   where head=k₀ and tail = [(s₁,k₁),…,(sₙ,kₙ)],  sᵢ:bool (true=p, false=p⁻¹)
spec fn kp_value(stable, kp) -> Word   // head + foldr over tail of (p^{sᵢ} ++ kᵢ)
spec fn kp_pcount(kp) -> nat := kp.tail.len()          // the induction measure
spec fn is_kp_word(in_K, kp) -> bool := in_K(head) ∧ ∀i. in_K(kp.tail[i].1)
//   every syllable (head and each kᵢ) is a K-element.
```

**Why alternating wins:** the maximal `H`-segment between two consecutive `p`'s is *exactly one
syllable `kᵢ`*, which `is_kp_word` forces to be in `K`. So Britton's symbol-level pinch
(middle ∈ `A`) lands on a `kᵢ`, giving `kᵢ ∈ K∩A` **for free** — the crux of "pinching preserves
`⟨K,p⟩`." (In a flat factorization this would be a theorem; here it's the data structure.)

`K` is abstracted as a predicate `in_K: spec_fn(Word)->bool` with closure (product/inverse/identity)
— exactly like `in_T` / `residue_pred`, so it instantiates to `T(M)` later. (De-risk: test on a
simple `in_K` first.)

## The pinch and its elimination (L1 — the hard core)

A **KP-pinch at i** (`0 ≤ i < n-1`): `tail[i].0 = ¬tail[i+1].0` (opposite signs) AND `kᵢ` (the
syllable between the two p's, `= tail[i].1`) lies in the right associated subgroup:
`Inv·kᵢ·Gen ⟹ kᵢ∈A₊`, `Gen·kᵢ·Inv ⟹ kᵢ∈A₋`.

**L1 (eliminate one pinch):** a KPWord with a pinch at `i` ⟹ a KPWord `kp'` with
`kp_pcount(kp') = n-2`, `is_kp_word(in_K, kp')`, and `kp_value(kp') ≡_{HNN} kp_value(kp)`.
- *surgery:* replace `…kᵢ₋₁ · p^{sᵢ} · kᵢ · p^{sᵢ₊₁} · kᵢ₊₁…` by `…(kᵢ₋₁ · φ(kᵢ) · kᵢ₊₁)…`
  (one merged syllable; two p's gone).
- *value preserved:* the HNN relation `p⁻¹·kᵢ·p ≡ φ(kᵢ)` (= `bₖ`-side; via `lemma_hnn_conjugation`)
  wrapped in congruence.
- *stays a KP-word:* `kᵢ∈K∩A₊` (syllable ⇒ K; pinch ⇒ A₊) and **compatibility ⟹ `φ(kᵢ)∈K`**; the
  merged syllable `kᵢ₋₁·φ(kᵢ)·kᵢ₊₁ ∈ K` by closure. ← the ONLY place compatibility is used.

## Reduce, then Britton (L2 + assembly)

**L2 (reduce to pinch-free):** every KPWord ⟹ a **pinch-free** KPWord with `≡` value. Induction on
`kp_pcount` via L1 (has a pinch ⇒ eliminate, `pcount` drops, recurse; else done). decreases pcount.

**Junction lemma:** `W` pinch-free (as a raw word) ∧ `u` has no stable letter ⟹ `W·u` is pinch-free
(appending a p-free word adds no stable letters, so every adjacent-stable middle is unchanged).

**Assembly:**
1. `g ∈ ⟨K,p⟩` ⟹ ∃ KPWord `kp₀` with `kp_value(kp₀) ≡ g`.  (← conversion from the membership form)
2. L2: reduce to pinch-free `kp`, `W := kp_value(kp) ≡ g`, still a KP-word.
3. `g` over `H` (no stable) ⟹ `W·g⁻¹` ≡ ε and (junction, `kp`-pinch-free ⟹ `W` raw-pinch-free) is
   **raw-pinch-free**.
4. `britton_lemma_full(W·g⁻¹)`: `≡ε` ∧ raw-pinch-free ⟹ **no stable letter** (contrapositive of
   `≡ε ∧ stable ⟹ pinch`).
5. `W·g⁻¹` stable-free ⟹ `W` stable-free ⟹ `kp.tail` empty ⟹ `W = head ∈ K` ⟹ `g ≡ W ∈ K`. ∎

The only genuinely new, hard lemma is **L1**. L2 is a clean induction; the junction/assembly are
Britton bookkeeping we've done before (E1 is the template for steps 3–4).

## Subtlety to pin down at build time
- **KP-pinch ⟺ Britton symbol-pinch:** L2 reduces KP-pinches; but step 4 needs `W` *raw*-pinch-free
  (no Britton symbol-pinch). Must show: a KP-pinch-free KPWord has a raw-pinch-free value. A raw
  pinch's middle is an `H`-segment between consecutive p's = a syllable `kᵢ`; raw-pinch ⟹ `kᵢ∈A` ⟹
  KP-pinch. So **no KP-pinch ⟹ no raw-pinch.** (Same structural fact as "alternating" — re-used.)
  Mind boundary cases (the two p's of a raw pinch must be *consecutive* in the stable sequence,
  which they are since a syllable has no p).

## Build order (de-risk L1 first)
1. **Representation:** `KPWord`, `kp_value`, `kp_pcount`, `is_kp_word` + tiny value identities
   (empty tail; cons). *(first brick — pure definitions, low risk, validates the encoding.)*
2. **L1** (eliminate one pinch) — the hard core; test with a simple `in_K`/compatibility instance.
3. **L2** (reduce to pinch-free) — induction.
4. Junction + "no KP-pinch ⟹ no raw-pinch" + assembly.
5. Generalize `in_K` to `in_T`; connect `in_generated_subgroup → ∃ KPWord` (step 1 of assembly);
   wire into the B(M) tower peel (E2.D).

Fallback if L1's surgery won't formalize cleanly: the direct pinch-decoding route (scope doc).

## Implementation note — single source of truth for the conjugation engine

The HNN conjugation telescope (`t⁻¹·φ_a(u)·t ≡ φ_b(u)` and its reverse) lives **once**, in
`machine_group.rs`:
- `hnn_a_gens` / `hnn_b_gens` — the A₊ / A₋ generator word-lists.
- `lemma_stable_conj_symbol` (per-symbol) → `lemma_stable_conj_factorization` (subgroup element) +
  `lemma_stable_conj_factorization_rev` (the `t·g·t⁻¹` orientation).

`kp_pinch.rs` consumes these directly to build the **abstract** pinch-middle helpers
`lemma_kp_phi_fwd` / `lemma_kp_phi_rev` (over `in_k: spec_fn(Word)->bool`), which feed
`lemma_kp_eliminate_pinch` (L1). `ii_subset.rs` supplies only the **KPWord representation**
(`KPWord`, `kp_value`, `kp_pcount`, `is_kp_word`, `lemma_kp_value_cons`).

A first draft once re-derived the whole engine inside `ii_subset.rs`
(`hnn_a_words`/`hnn_b_words`, `lemma_hnn_conjugation_subgroup`(`_inv`), and a *concrete*
`lemma_kp_pinch_middle` over `in_subgroup_pred` + `kp_compat_fwd`/`bwd`). That copy was
character-identical to the machine_group engine and was never wired into the live L1 path — it was
pruned (2026-06-19). **Do not reintroduce a second conjugation engine in `ii_subset`:** import from
`machine_group` and keep the abstract `in_k` interface in `kp_pinch`. When K=T(M) is instantiated,
discharge `kp_pinch`'s `H_ab`/`H_ba` hypotheses via property (v) directly — not via a concrete
pinch-middle lemma.
