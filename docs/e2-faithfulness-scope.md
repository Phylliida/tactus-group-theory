# E2 — the deep faithfulness (the monster). Scope.

Goal: `in_generated_subgroup(b_m(mm), g_subgens(mm), t(α,β)) ⟹ (α,β) ∈ H₀(M)`.
(The input is E1's output. This is the ⟹ half of Theorem 1 minus property III, and was the
Z3 `admit` `axiom_machine_group_backward`.) Paper route: §2 properties (i),(ii),(v),(vi),(vii).

## The two representation facts that shape everything

1. **`⟨t, rᵢ, lⱼ⟩` is FINITELY generated** → `g_subgens(mm)` (a `Seq<Word>`) + `in_generated_subgroup`
   works. ✓ (E1 already produces membership in this form.)
2. **`T(M) = ⟨t(α',β') : (α',β')∈H₀(M)⟩` is INFINITELY generated** → cannot be a `Seq<Word>` of
   generators. **Decision:** represent T(M)-membership as a PREDICATE via a *finite* factorization
   over H₀ configs:
   ```
   spec fn in_T(mm, w) := ∃ factors: Seq<(nat,nat,bool)>,
       (∀i. config_in_H0(mm, factors[i])) ∧ product_of_signed_configs(factors) ≡_A w
   ```
   The factorization is finite even though the generating set is infinite. (Mirrors
   `in_generated_subgroup`/`factors_from_generators` but with an H₀-membership side condition
   instead of a fixed `Seq` of generators.)

## Tooling reality
- HAVE: `britton_lemma_full` (≡ε + stable ⟹ pinch); `has_pinch_at`/`has_adjacent_opposite_at`;
  `textbook_act_hnn` (the HNN normal-form action — the engine Britton is built on); `net_level`;
  syllable counts; `in_generated_subgroup`/`factors_from_generators`/`concat_all`.
- DO NOT HAVE: any property-II / subgroup-intersection / pinch-free-representative lemma, any
  "pinching preserves ⟨K,p⟩" lemma, any free-group free-factor-membership lemma. **All built from
  scratch.**

## The faithful route (paper §2), as bricks
- **E2.A — property (vii):** `⟨t,rᵢ,lⱼ⟩ = ⟨T(M),rᵢ,lⱼ⟩`. `⊇`: `t = t(0,0) ∈ T(M)` since
  `(0,0)∈H₀` (terminal, reaches itself in 0 steps). `⊆`: each `t(α',β')` for `(α',β')∈H₀` is in
  `⟨t,rᵢ,lⱼ⟩` — this is the FORWARD direction (brick 19's induction shows exactly
  `(α',β')∈H₀ ⟹ t(α',β')∈⟨t,rᵢ,lⱼ⟩`, modulo restating it as subgroup membership rather than
  k-commutation). Reuse that.
- **E2.B — property (v) (the φ-compatibility):** for each association, `rᵢ` maps
  `T(M) ∩ ⟨t(aᵢ,bᵢ),xᵐ,yᵐ⟩` ↔ `T(M) ∩ ⟨t(cᵢ,0),xᵐ²,y⟩` isomorphically — because a config in one
  side is in H₀ **iff** its machine-image is (`mm_yields` is a partial bijection on the relevant
  residue class; H₀-membership is step-invariant both ways). This is where the machine's
  determinism + reversibility-on-H₀ enters the group argument.
- **E2.C — property (II), generic (THE CENTRAL MONSTER):** for a single HNN level `HNN(H,p)` with
  associated subgroups `A₊,A₋` and a K-membership predicate satisfying E2.B's compatibility:
  `g over H ∧ g ∈ ⟨K, p⟩  ⟹  g ∈ K`. Proof (paper): the witnessing word has a pinch (Britton);
  pinching it stays inside `⟨K,p⟩` (needs E2.B) and drops one `p`; induct to a `p`-free word; a
  `p`-free word `≡` something with a `p` is impossible by Britton ⟹ the rep is a K-word. Build on
  `britton_lemma_full` + `textbook_act_hnn`. **No engine exists; this is the bulk of E2.**
- **E2.D — property (vi) via the tower:** apply E2.C down each level of the B(M) tower (peeling
  `rᵢ`/`lⱼ` one at a time) with `K = T(M)`, reducing `A ∩ ⟨T(M),rᵢ,lⱼ⟩` to `T(M)`.
- **E2.E — T freeness (property (i)) + free-factor membership:** `T = ⟨t⟩^A` is free on
  `{t(r,s)}` (paper: "expand a product of `t(r,s)`"; we have free-product machinery in
  `free_product.rs` since `A = ⟨t⟩ * ⟨x,y;xy=yx⟩`). Then `t(α,β) ∈ T(M)` (a free generator lying in
  the subgroup on the subset `{t(r,s):(r,s)∈H₀}`) ⟹ `(α,β)∈H₀`. The "last mile".
- **E2.glue:** `t(α,β) ∈ A` (only t,x,y) ∧ `∈ ⟨t,rᵢ,lⱼ⟩` →(vii)→ `∈ A∩⟨T(M),rᵢ,lⱼ⟩` →(vi)→
  `∈ T(M)` →(E2.E)→ `(α,β)∈H₀`. ∎

## Alternative route (noted, not chosen): direct pinch-decoding
Induct on the stable-letter count of the witnessing word; each pinch = one machine step (the
forward-step relation, run backward), accumulating a computation `(α,β)→*(0,0)`. Avoids defining
`T(M)`, but the induction is murky about assembling the pinches into ONE coherent computation, and
it's less faithful to the paper. Keep as fallback if the abstract route stalls.

## Honest assessment + recommended first brick
E2 is genuinely multi-session. **E2.C (generic property-II)** is the central, highest-uncertainty
engine — nothing like it exists. Two sane ways to open:

- **(de-risk first) E2.C-mini:** prove property-II for ONE HNN level with the *simplest* K (e.g.
  `K = ⟨t⟩`, or even trivial K) to validate "pinch-elimination preserves the subgroup" before the
  full T(M) version. If this technique doesn't formalize cleanly, we want to know now.
- **(clean win first) E2.E:** T-freeness + free-factor membership — most self-contained (free-group
  theory via `free_product.rs`), it's the motivating "last mile," and it's reusable regardless of
  how the middle goes.

Recommendation: **E2.C-mini** (de-risk the engine), since everything downstream depends on
property-II working at all; fall back to E2.E for momentum if the engine proves stubborn.
