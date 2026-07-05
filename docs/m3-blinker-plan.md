# M3 blinker positivity — the resumable plan

*2026-07-05. `src/m3_blinker.rs` at **9/0**: the entire GROUP-SIDE is wired. This doc pins the
remaining ⟹ (the Britton syllable/parity argument — the single largest formalization of the
M-ladder). Read `semantic-finite-basis.md` §4.3 for the paper proof.*

Alphabet: `a=Gen0 b=Gen1 q=Gen2 q′=Gen3`. `m3_rules()` = `{qa=bq′, q′a=bq}`. THE CRITICAL TEST:
`G = rules_pres(m3_rules(),4) ≅ ⟨a,b,q | qa²q⁻¹=b²⟩` — an **HNN extension of F(a,b)**, stable letter
q, associated subgroups `⟨a²⟩→⟨b²⟩`. Not free ⟹ neither M1 (two-projection) nor M2 (readback) applies.

## DONE (committed, 9/0)
- `m3_rules` + validity + `lemma_m3_backward` (⟸, from thue.rs).
- `m3_data()` = `HNNData{ base: free_group(2), associations: [(b²,a²)] }` + `lemma_m3_data_valid`.
  (association `(A,B)=(b²,a²)` encodes `q⁻¹b²q=a²` ⟺ `qa²q⁻¹=b²`; stable letter q=Gen2.)
- `sub_hom()`: G → `hnn_presentation(m3_data())` (3 gens), `q′↦b⁻¹qa` (SAME images as M2, HNN target).
- `lemma_qa2_equiv_b2`: `qa²q⁻¹ ≡ b²` in the HNN presentation (conjugate the HNN relator q⁻¹b²qa⁻²≡ε).
- `lemma_sub_valid` (relator 1 reduces freely to ε; relator 2 = b⁻¹qa²q⁻¹b⁻¹ ≡ ε via qa2_equiv_b2).
- `lemma_group_to_hnn(u,v)`: `G-equal ⟹ equiv_in_presentation(hnn_pres, sub(u), sub(v))`.
- helpers: `m3_reduces2/3` (reduces_to chains).

## REMAINING ⟹  (group-equal positive u,v ⟹ thue-equal)

### Step R1 — discharge `hnn_associations_isomorphic(m3_data())`   ✅ DONE (13/0)
`lemma_m3_iso` — proven NOT via exponent counting but via the **a↔b swap automorphism**: swap: F(a,b)→
F(a,b) (a↦b,b↦a), `swap(A-emb w)=B-emb w`, and homs preserve `≡ε` both ways (swap is an involution) ⟹
the iff directly, no exponent-converse needed. Bricks: `swap_hom` + `lemma_swap_valid` (free base ⟹
relator cond vacuous) + `lemma_apply_hom_concat` (local) + `lemma_swap_emb` (induction, per-symbol swap
facts as hypotheses). GOTCHA (cost a hang): `by(compute)` HANGS on let-bound args — compute on LITERALS.

### Step R2 — the Britton engine   [THE BIG ONE — bespoke, largest M-ladder piece]

**REFINED induction structure (worked out at the 15/0 checkpoint).** `lemma_m3_readback(u,v)`:
u,v nf + positive + word_valid(u,4)/(v,4) + `equiv(hp, sub(u), sub(v))` ⟹ `u==v`. Strong induction on
`stable_count(sub(u)) + stable_count(sub(v))` (= #state-letters(u)+#state-letters(v)).
Three cases on (has-state-letters u?, has-state-letters v?):
- **(no, no)** — ✅ DONE = `lemma_m3_base` (15/0). sub=identity on {a,b}, britton_lemma_unconditional.
- **(yes,no) / (no,yes)** — ✅ DONE = `lemma_m3_no_mixed` (30/0). w all-same-sign stable ⟹ ¬has_pinch
  contradicts britton_lemma_full ⟹ ex falso. Bricks (banked, reusable for case 3): `no_sym`/`has_gen2`
  recursive preds + cons-unfolds, `lemma_sub_no_inv2`, `lemma_sub_has_gen2`, `lemma_no_inv2_no_pinch`
  (all-same-sign ⟹ no pinch), `lemma_has_gen2_stable`, `lemma_wv2_no_stable`.
- **(yes,yes)** — THE PINCH CASCADE [THE HARD CORE, parity head-cap]: w = sub(u)·sub(v)⁻¹ has Gen2's
  (from sub(u)) then Inv2's (from sub(v)⁻¹). `britton_lemma_full` ⟹ pinch, which must be at the
  junction (last Gen2 of sub(u), first Inv2 of sub(v)⁻¹) with base-word-between ∈ B=⟨a²⟩ = the
  compensation a^{2mₖ}. Peel the two q's + the compensation (Britton reduction), recurse on the
  smaller instance; thread the parity head-cap: nf ⟹ each syllable a-head ∈{0,1}, even shift −2mᵢ
  exits {0,1} ⟹ all mᵢ=0 ⟹ syllables literally equal ⟹ readback. **This is the genuinely new math**
  — HNN normal-form uniqueness specialized to M3. May need syllable-decomposition infra (net-a-exp
  per gap) or a bespoke induction peeling one junction pinch at a time.

Original prose (semantic-finite-basis §4.3):
Two banked engines (britton_via_tower.rs, both need only R1's iso condition):
- `britton_lemma_full(data, w)`: `w≡ε` + `has_stable_letter` ⟹ `has_pinch(data, w)`.
- `britton_lemma_unconditional(data, w)`: `w≡ε` + w over base gens ⟹ `w≡ε in base` (BASE EMBEDDING).

Proof shape (semantic-finite-basis §4.3):
1. **Base case** (u,v have no state letters ⟹ sub(u),sub(v) over {a,b}, no q): sub(u)≡sub(v) in HNN,
   both base words ⟹ `britton_lemma_unconditional` ⟹ equal in F(a,b) ⟹ freely-equal ⟹ (positive,
   reduced) equal ⟹ u=v.  *(This case is fully tractable with banked tools — do it FIRST.)*
2. **Inductive step** (both have ≥1 q): sub(u)·sub(v)⁻¹ ≡ ε has stable letters ⟹ `britton_lemma_full`
   ⟹ a pinch. sub(u) has only q, sub(v)⁻¹ only q⁻¹ ⟹ the pinch is at the junction: last gap of
   sub(u) · (first gap of sub(v))⁻¹ ∈ ⟨a²⟩ (the compensation dₖ=a^{2mₖ}). Britton-reduce (remove the
   pinch) and recurse. Threading through: the **parity head-cap** — Thue-irreducible ⟹ each syllable's
   a-head ∈ {0,1}; a nonzero even shift −2mᵢ exits {0,1} ⟹ all mᵢ=0 ⟹ tuples literally equal ⟹
   heads read back the state sequence (εᵢ↦sᵢ), then data blocks match ⟹ u=v.

   The genuinely NEW content (no banked lemma): the pinch-cascade induction extracting the
   compensations + the parity head-cap forcing mᵢ=0. This is HNN normal-form uniqueness specialized
   to M3; expect to build syllable-decomposition + net-a-exponent-per-gap infra. Consider whether
   `textbook_act_hnn` / `stable_count` / syllable machinery in britton_via_tower.rs can be leveraged
   vs. a bespoke induction on #q.

### Step R3 — Thue confluence + assemble
nf side: orient both rules L→R (#a decreases, no critical pairs ⟹ complete; nf = "no state letter
followed by a"). `lemma_nf_exists` (analogue of M2's, two rules). Then `lemma_m3_forward` (sub
injective on nf via R2) + `lemma_m3_positivity` (combine with ⟸).

## tactus idioms banked (M1/M2 — apply throughout)
- `by(compute)` on FULL literals / bare spec-fn calls only — **HANGS on let-bound spec-fn structs**
  (compute on `sub_hom()`/`m3_data()` directly, never `let h = sub_hom()`).
- Recursive spec fns need a **cons-unfold helper** on literals (M2's `count_cons`, M1's `delete_cons`).
- **"rlimit exceeded" = Lean maxHeartbeats** → SPLIT big fns into helpers (don't raise a limit).
- Quantified open spec fn `forall` does NOT fold under Lean → make predicates RECURSIVE + a
  `lemma_positive_gen`-style element-access bridge.
- Mutual recursion needs lexicographic `decreases (measure, phase)`.
- Qualify cross-module lemmas (`lemma_hnn_presentation_valid` is in `britton_infra`, not `hnn`).
- Verify: `./check.sh --verify-module m3_blinker` (use `timeout 260` — cold module is slow).
