# M1 positivity — the resumable plan (guard motion `⟨a,b,g,n | gn=ng⟩`)

*2026-07-04. Status: `src/m1_guard.rs` at **7/0** (checkpoints 1+2a committed). The ⟸ half and the
`delete_x` infra are DONE; this doc pins the remaining ⟹ arc so it resumes cleanly after a /roll.*

Alphabet: `a=Gen(0) b=Gen(1) g=Gen(2) n=Gen(3)`. `m1_rules()` = single rule `gn ↔ ng`
(`lhs=[Gen2,Gen3]`, `rhs=[Gen3,Gen2]`). `rules_pres(m1_rules(),4)` = `⟨a,b,g,n | [g,n]⟩` = F(a,b)∗ℤ².

## Goal
`positivity(m1_rules(), 4)` (from `thue.rs`): for positive `u,v` valid over 4 gens,
`equiv_in_presentation(rules_pres, u, v) ⟺ thue_equiv(m1_rules(), u, v)`.

- **⟸ DONE** — `lemma_m1_backward` = `lemma_thue_implies_group` instance.
- **⟹ REMAINING** — the two-projection route below (NO free-product NF).

## Done infra (committed, 7/0)
- `delete_x(w, x)`: remove all `Gen(x)`. `lemma_delete_concat` (distributes over concat),
  `lemma_delete_removes` (result is x-free), `lemma_positive_reduced` (positive ⟹ `is_reduced`).
- Notation here: `dn(w) := delete_x(w,3)` (removes n → the a,b,g subsequence);
  `dg(w) := delete_x(w,2)` (removes g → the a,b,n subsequence).

## ⟹ route (two projections + one combinatorial core)

### Part A — group-equal ⟹ same deletes (mechanical, M0-style; ~7 lemmas)
Define `kill_n_hom` / `kill_g_hom` : `rules_pres(m1_rules(),4) → free_group(4)`:
- `kill_n` images `[[Gen0],[Gen1],[Gen2], empty]`  (n=Gen3 ↦ ε);
- `kill_g` images `[[Gen0],[Gen1], empty, [Gen3]]`  (g=Gen2 ↦ ε).

1. `lemma_killn_valid` / `lemma_killg_valid` : `is_valid_homomorphism`. Only nontrivial conjunct =
   relator condition: `apply_hom(kill_n, [Gen2,Gen3,Inv2,Inv3]) = [Gen2,Inv2] ≡_{free4} ε`
   (via `lemma_word_inverse_right`/reduces); `kill_g` → `[Gen3,Inv3] ≡ ε`. (mirror `lemma_psi_valid`.)
2. `lemma_applyhom_killn_eq_delete(u)` : `positive_word(u) ⟹ apply_hom(kill_n_hom(), u) =~= dn(u)`
   (induction on u; per-symbol `Gen(j) ↦ [Gen j]` if j≠3 else ε, matches delete_x). Same for kill_g.
3. `lemma_reduced_reduces_to_self(w)` : `is_reduced(w) ∧ reduces_to(w, x) ⟹ x == w`
   (induction on the step count; a reduced word has no `reduces_one_step`). [may already exist —
   grep `lemma_reduced_no_step`, `lemma_reduces_in_steps` first]
4. `lemma_delete_positive(u, x)` : `positive_word(u) ⟹ positive_word(delete_x(u,x))`.
5. `lemma_group_implies_same_deletes(u, v)` : group-equal + positive ⟹ `dn(u)==dn(v)` ∧ `dg(u)==dg(v)`.
   Chain: `lemma_hom_preserves_equiv(kill_n, u, v)` → `equiv(free4, dn(u), dn(v))` →
   `lemma_free_group_equiv_freely_equivalent` → `freely_equivalent(dn(u),dn(v))` → both reduced
   (positive) + #3 ⟹ `dn(u)==dn(v)`. Same for dg.

### Part B — the combinatorial core (THE MEAT; elementary 4-case peel induction)
`lemma_deletes_imply_thue(u, v)` :
`positive(u) ∧ positive(v) ∧ dn(u)==dn(v) ∧ dg(u)==dg(v) ⟹ thue_equiv(m1_rules(), u, v)`.
Strong induction on `u.len() + v.len()`.

- **Case u empty:** `dn(u)=dg(u)=empty` ⟹ v is all-n (dn) AND all-g (dg) ⟹ v empty. `thue` refl.
- **Case u[0] ∈ {a,b} (wall):** walls survive both deletes, so `dn(v)[0]=dg(v)[0]=u[0]`; a leading
  g would fail dn (dn(v)[0]=g), a leading n would fail dg ⟹ `v[0]=u[0]`. Recurse on `u.drop_first(),
  v.drop_first()` (deletes match on tails), then `lemma_thue_prepend`.
- **Case u[0]=g:** `dn(u)[0]=g` ⟹ `dn(v)[0]=g` ⟹ v's first non-n is g ⟹ `v = n^k · g · rest`.
  Bubble: `n^k·g·rest ~thue g·n^k·rest` (`lemma_bubble`: k applications of `ng→gn`, the BWD step).
  Match the g; the deletes of `(u.drop_first(), n^k·rest)` match (checked in the design), recurse,
  `lemma_thue_prepend` + `lemma_thue_transitive` (via chain concat).
- **Case u[0]=n:** symmetric (swap g↔n, dn↔dg): `v = g^k·n·rest ~ n·g^k·rest`.

Sub-lemmas for B:
- `lemma_thue_prepend(rules, s, u, v)`: `thue_equiv(rules,u,v) ⟹ thue_equiv(rules, [s]+u, [s]+v)`
  (shift each step's position by 1; the `thue_chain` maps `ws ↦ ws.map(|w| [s]+w)`).
- `lemma_thue_trans(rules, u, m, v)`: `thue_equiv(u,m) ∧ thue_equiv(m,v) ⟹ thue_equiv(u,v)`
  (concat the two witness chains). [general; belongs in thue.rs — add there and reuse]
- `lemma_bubble(k, rest)`: `thue_equiv(m1_rules, n^k·g·rest, g·n^k·rest)`. Induction on k:
  `n·(g·n^{k-1}·rest)` — one `ng→gn` step at pos 0 gives `g·n·(n^{k-1}...)`? Careful: bubble g left
  past ONE n at a time from the right end of the n-run, or use `thue_prepend` on the inductive
  `n^{k-1} g ~ g n^{k-1}`. Cleanest: `n^k g = n·(n^{k-1} g) ~ n·(g n^{k-1})` [prepend n to IH]
  `= (n g) n^{k-1} ~ (g n) n^{k-1}` [one step at pos 0] `= g·n^k`.
- leading-run split: `lemma_leading_n_split(v)`: if `dn(v)[0]=g` (v's first non-n is g) then
  `∃ k, rest: v =~= n^k · seq![g] · rest` with `n^k` all-n. (count leading n's.)

### Part C — assemble
`lemma_m1_forward(u,v)`: group-equal + positive ⟹ thue_equiv, via A (#5) + B.
`lemma_m1_positivity()`: `positivity(m1_rules(), 4)` — combine `lemma_m1_backward` (⟸) and
`lemma_m1_forward` (⟹). THE HEADLINE — first M-ladder rung fully verified.

## tactus idioms banked this session (apply throughout)
- `by (compute)` on FULL literals only (never `let`-bound words/symbols); works to depth ~4;
  FAILS on `normal_form∘apply_hom` (recursion cap) and PANICS on `word_valid` (poly.rs) — prove
  `word_valid` by index-split, `inverse_word` validity by `lemma_inverse_word_valid`.
- `else if` chains (not separate `if`s). `inverse_word(seq![Gen(g)])` needs the `Seq::new(1,…)`
  bridge. Qualify cross-module lemmas (`crate::higman_consequences::lemma_equiv_inverse`).
- Reduction witnesses: explicit `reduce_at` chains (see m0_token `reduces3`/`reduces4`), not compute.
- Retraction/faithfulness engine: `lemma_hom_preserves_equiv` + `lemma_free_group_equiv_freely_equivalent`
  + `lemma_emb_id_on_gens_preserves` (see m0_token `lemma_psi_faithful`, and
  `miller_collapse_inject::lemma_collapse_injective`).
- Verify: `./check.sh --verify-module m1_guard`. Full gate `./check.sh` (baseline: proof modules 0-err;
  runtime/todd_coxeter exec noise is pre-existing, ~27 lines / apply_hom_symbol_exec — check LOCATIONS).
