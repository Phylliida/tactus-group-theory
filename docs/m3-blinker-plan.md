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
- **(yes,yes)** — ✅✅ CONCEPTUAL CRUX SOLVED via `act_syls` SHORTCUT (32/0, the user knew the crate
  had it). The pinch cascade is REPLACED by **Britton normal-form invariance**: `act_syls(data,w)` (=
  `textbook_act_hnn(data,w,ε,[]).1`, the canonical syllable sequence) is a GROUP INVARIANT. Bricks:
  `lemma_deriv_syls` (generalize `lemma_derivation_preserves_syls` to arbitrary target) +
  `lemma_syls_preserved` (equiv ⟹ act_syls equal). Made `lemma_single_step_preserves_syls` pub.
  **REMAINING = THE READBACK** (the only piece of case 3 left): `sub(u)≡sub(v)` ⟹ [preservation, on
  `sub(u)·q` so the LAST gap becomes a syllable too] `act_syls(sub(u)·q) =~= act_syls(sub(v)·q)` ⟹
  [readback] `u==v`. The readback = `act_syls∘(sub·q)` injective on nf words. Dives into the AFP
  coset machinery (`textbook_psi_p` → `b_rcoset_rep`/`a_rcoset_rep` of `tower_afp_data(data,0)`): show
  (a) nf ⟹ no COLLAPSE in the action (cf. `lemma_p_reduced_initial_no_collapse`) ⟹ act_syls is the
  literal list of gap-reps; (b) `b_rcoset_rep(nf gap)=gap` — THIS is where the parity head-cap now
  lives (coset rep reduces a-exp mod ⟨a²⟩; nf caps head at {0,1} ⟹ already reduced); (c) the gap +
  is_left sequence determines u (state seq from εᵢ heads, blocks from gaps). Deep but BOUNDED — wants
  a fresh focused study of the b_rcoset_rep internals.

  ── READBACK BRICKS (live, post-roll; m3 at 34/0) ──
  Use `w_u = [Gen2] + sub(u) + [Gen2]` (q·sub(u)·q) so BOTH end gaps + the accumulator become syllables
  (.0 → ε). `w_u ≡ w_v` from sub(u)≡sub(v) + congruence.
  * B1 ✅ `lemma_sub_no_collapse` (33/0): sub(u)·q has no Inv2 ⟹ !has_pinch ⟹ `textbook_no_collapse`
    (via `lemma_p_reduced_initial_no_collapse`, made pub). [does q·sub(u)·q too — redo for the qq form]
  * B2 ✅ `lemma_sub_syls_count` (34/0): `act_syls(sub(u)·q).len() == stable_count` (via
    `lemma_no_collapse_gives_m`, made pub). ⟹ #state(u)=#state(v).
  * B4 ✅ DONE (38/0) `lemma_parity_head_cap`: two reduced no-a⁻¹ words g1,g2, a-head≤1, g1≡a^{2k}·g2
    ⟹ g1=g2. k>0 blows a-head≥2 (`lemma_prepend_gen0`+`lemma_reduced_unique`); k<0 sign-flip; k=0 direct.
  * B3-FOUNDATION ✅ DONE (52/0) `lemma_b_rcoset_rep_eq_gap`: `b_rcoset_rep(m3_afp(), g) =~= g` for g
    reduced + `no_sym(_,Inv0)` + `lead(_,0)≤1`. The delicate geodesic-coset lemma — proven end-to-end
    via the prover-agent's route (rep from `lemma_b_rcoset_rep_props`+`_satisfiable`[made pub] → reduced
    (min-len) → decompose `rep=a^m·s` → `g≡a^{2k}·rep=a^j·s` reduced ⟹ literal `g=a^j·s` → hyps force
    `0≤j≤1`, `|m|≤j` → `m=-1` killed by min-lex (Gen0<Inv0) → parity `j-m=2k` even ⟹ `m=j` ⟹ `rep=g`).
    Helpers (all in m3_blinker.rs): m3_afp, no_shorter_below, no_smaller_lex_below, suffix_reduced,
    rank_head, signed_power_concat_reduced, same_b_rcoset refl/respects_equiv, min_coset_word_reduced,
    signed_head_decompose, symbol_power_cons, a2_factors_signed_power, shift_carrier. ⟹ carries vanish.
  * B3 [remaining] EXPLICIT act_syls: define `nf_syls(u): Seq<Syllable>` = the gap sequence, prove
    `act_syls(q·sub(u)·q) =~= nf_syls(u)` by induction on u tracking (h,syls) through `textbook_psi_p`
    PREPEND (no-collapse ⟹ always prepend {is_left:false, rep:b_rcoset_rep(gap)}). **FOUNDATION =
    `b_rcoset_rep(nf gap)=gap`** (⟹ carry `phi_inv(b_rcoset_h)`=ε, clean syllables). FEASIBLE: lex
    `symbol_to_column(Gen i)=2i < 2i+1=Inv i` ⟹ head-1 tie a·rest<a⁻¹·rest ⟹ positive wins; head-0
    unique min-len. But NO crate helper — must prove from scratch: (i) same_b_rcoset(gap,gap) trivial;
    (ii) `b_rcoset_min_len(afp,gap)==gap.len()` = geodesic-in-coset (no word in ⟨a²⟩·gap shorter — the
    ONE delicate piece, a length bound over all k: |reduced(a^{2k}·gap)|≥|gap|, tie only at k=±1,h=1);
    (iii) lex-min = gap; (iv) uniqueness via `lemma_word_lex_rank_base_injective`. Then rep=gap ⟹ B3.
  * B5 [BIG] gap-parsing injectivity: from act_syls equal + rep=gap + `lemma_b_rcoset_rep_invariant`,
    get per-gap `same_b_rcoset(gap_i(u),gap_i(v))` ⟹ [B4] gap_i(u)=gap_i(v) ⟹ [parse a-prefix/b⁻¹-suffix
    ↔ q'/q, blocks ↔ a,b] u=v. Or simpler: rep=gap ⟹ act_syls literally = [gaps] ⟹ sub(u)=sub(v) as
    WORDS ⟹ u=v (sub prefix-injective on symbols). Combinatorial.
  * ASSEMBLE: readback dispatcher (base ✓ / no_mixed ✓ / B3–B5) ⟹ `lemma_m3_readback` ⟹ ⟹ direction.
  NOTE: B1/B2 used sub(u)·q; the assembly wants q·sub(u)·q — re-establish no-collapse/count for that form.

  Old pinch-cascade prose (superseded):

  Superseded raw-Britton description:
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
