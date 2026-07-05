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
  * B3-CARRY [needed by B3 induction]: `b_rcoset_h(m3_afp(), g) =~= ε` when `b_rcoset_rep(g)=g` (nf gap).
    Because target=g·rep⁻¹=g·g⁻¹≡ε ⟹ h=ε is the min-len (0) witness. ANOTHER min-len shortlex argument
    (same flavor as rep=gap; there's `lemma_b_rcoset_h_identity`: b_rcoset_h(ε)=ε, and satisfiable/props
    private helpers at :1494/:1728). ⟹ carry `phi_inv_h = apply_embedding(a_words, b_rcoset_h(g)) = ε`.
  * B3-ACT-SYLS ✅ MACHINERY DONE (55/0): `lemma_act_compose` (britton_via_tower, act(w1·w2)=act(w1,act(w2))),
    `lemma_act_base` (base words accumulate), `lemma_psi_p_nf_gap` (one q on nf-gap → {false,gap}::syls),
    `lemma_act_gap_word` (act(gap_word(gs),ε,[])=(ε,gap_syls(gs)) for nf gaps). Computes act_syls of any
    reduced-gap-interleaved word. `nf_gap`/`gap_word`/`gap_syls` defined.

  ⚠️  **CRITICAL SUBTLETY FOUND (blocks the simple B5; the ORIGINAL DOC GLOSSED THIS):**
  Gaps of `sub(nf u)` are **NOT freely reduced**. `sub(q')=[Inv1,Gen2,Gen0]=b⁻¹qa`, so `u=bq'` ⟹
  `sub(bq')=[Gen1,Inv1,Gen2,Gen0]=b·b⁻¹·q·a` — the gap `b·b⁻¹` cancels. And the reduction **loses the
  q'/q marker**: `q·sub(bq')·q` and `q·sub(qa)·q` have the SAME reduced gaps `[ε,a,ε]`. Injectivity
  still HOLDS (only `bq'` is nf; `qa` is not — `qa→bq'`), but recovering u needs **nf-disambiguation**,
  NOT `gap_word∘split`. Worse, the nf orientation is forced: standard nf (no qa/q'a) gives a-head≤1
  (needed for parity B4) but allows `bq'` (non-reduced gaps); reverse nf (no bq'/bq) gives reduced gaps
  but a-head≤2 (parity B4 fails). NO orientation gives both. So `act_syls(q·sub(u)·q)` = the REDUCED
  gaps (Britton nf), and the remaining obligation is exactly: **the map (nf word u) ↦ (reduced-gap
  sequence) is INJECTIVE** — equivalently, no two distinct nf words share a Britton normal form. This is
  the genuine remaining content; needs a fresh argument (likely: reconstruct the unique nf word from
  reduced gaps by re-inserting b·b⁻¹ where nf-ness demands, or a direct induction on u). B4/rep=gap give
  "reduced gaps of u,v match" from act_syls equality; the NEW piece is nf-word↦reduced-gaps injective.
  * B5 [was oversimplified — see subtlety]: prefix-code idea FAILS because reduced gaps ≠ raw sub(u).

  ── THE FIX (validated; crux ✅ 56/0) ──
  Insight: the ONLY free cancellation in sub is `sub(b)·sub(q')=b·b⁻¹` (checked ALL sub-image boundaries),
  and it is EXACTLY the Thue rule `qa↔bq'`. So free-reduction of sub = firing `bq'→qa` Thue moves.
  * FIX-CRUX ✅ `lemma_bq_qa_thue` (56/0): `x·bq'·y ~thue x·qa·y` (rule 0 backward, via thue_step_at + lemma_thue_single).
  ── FIX ASSEMBLY PROGRESS (m3 at 68/0) ──
  * P1 ✅ (59/0): `ffnf` (fire all bq'→qa, L-to-R, decreases |u|), `lemma_thue_prepend_word`, `lemma_u_thue_ffnf` (u ~thue ffnf(u)).
  * P2a ✅ (65/0): `no_bq` pred + `lemma_ffnf_nonempty`/`_first` + `lemma_ffnf_no_bq` (ffnf is bq'-free).
  * P2b ✅ (68/0): `lemma_sub_img` (per-image props) + `lemma_sub_first` + `lemma_sub_reduced` (no_bq ⟹ is_reduced(sub(w))).
  ⚠️⚠️  **SECOND SUBTLETY FOUND (P3, blocks the act_syls(.1) approach) — 2026-07-05:**
  `act_syls(w) = textbook_act_hnn(w,ε,[]).1` drops the `.0` accumulator `h`. The LEADING base part of a
  word (before its first stable letter) lands in `h`, NOT in the syllables. e.g. NF(sub("aaq"))=(a²,[{false,ε}]),
  NF(sub("q"))=(ε,[{false,ε}]) — SAME syllables, DIFFERENT words/group-elements. So `act_syls` is NOT
  injective on nf words, and `lemma_syls_preserved` (preserves .1 ONLY) is INSUFFICIENT for the readback.
  Adding leading/trailing q's does NOT help: a leading gap with a-head≥2 (e.g. "aa") triggers an a²→b²
  conversion whose b² lands in `.0` (dropped) while the syllable becomes {false,ε} — same information loss.
  **FIX = compare the FULL normal form `(h, syls) = textbook_act_hnn(sub(u),ε,[])` (NO added q's):**
  h = leading base P_0 (faithful — accumulates AFTER all q's, no conversion), syls = the AFTER-q gaps
  (a-head≤1 from nf: no qa/q'a). Structural: sub(ffnf u) = base_run(sub) · gap_word(after-q gaps);
  NF = (base_run, gap_syls(after-q gaps)) via composition ✅ + act_base ✅ + W-induction ✅. NEEDS a NEW
  **h-preservation lemma** (`textbook_act_hnn(w1,ε,[]).0 =~= .0(w2)` under group-equiv) — extend
  lemma_deriv_syls to the full output, OR a "Britton NF is a complete invariant" lemma. The MATH is fine
  (sub is a group iso, positivity holds); this is a proof-strategy course-correction. The after-q-gap
  a-head≤1 (below) is STILL needed for the syls part.
  * P3 [TODO] ffnf gaps nf: `no_qpa`(no q'a)+`no_qaa` preserved through ffnf (junction args like no_bq) ⟹
    gaps of q·sub(ffnf u)·q have a-head≤1 (+ reduced from P2b, no-Inv0 trivial) ⟹ nf_gap.
  * P4 [TODO] structural: `split_q(W)` (split q-word at Gen2's) + `gap_word∘split_q = id` for q-words ⟹
    q·sub(ffnf u)·q = gap_word(gaps(ffnf u)).
  * P5 [TODO] connect: act_syls(q·sub(u)·q) = act_syls(q·sub(ffnf u)·q) [sub(u)≡sub(ffnf u) via u~thue ffnf u]
    = gap_syls(gaps(ffnf u)) [W-induction ✅ lemma_act_gap_word].
  * P6 [TODO] injectivity: act_syls(u)=act_syls(v) ⟹ gaps(ffnf u)=gaps(ffnf v) ⟹ [gap_word inj / split_q]
    q·sub(ffnf u)·q = q·sub(ffnf v)·q ⟹ sub(ffnf u)=sub(ffnf v) ⟹ [sub PREFIX CODE] ffnf u=ffnf v ⟹
    u~thue ffnf u=ffnf v~thue v ⟹ u~thue v ⟹ [both Thue-nf] u=v.
  * P7 [TODO] dispatcher (base ✓/no_mixed ✓/P6) → lemma_m3_readback → R3 (Thue-nf reduce + positivity iff).
  (OLD abstract sketch below, superseded by the ffnf-based P1-P7:)
  * FIX ARCHITECTURE (clean induction, TODO): define `fr_gaps(u)` = free-reduced gaps of q·sub(u)·q
    (= the b_rcoset_rep syllables since nf u ⟹ a-head≤1 so a²-reduction trivial), `decode(gs)` = read
    positive word from a reduced-gap sequence, `nbq(u)` = #occurrences of "bq'" in u.
    - `lemma_u_thue_decode`: `u ~thue decode(fr_gaps(u))` by induction on `nbq(u)`:
        · nbq=0 ⟹ sub(u) reduced ⟹ fr_gaps(u)=raw gaps ⟹ decode=u (refl).
        · nbq>0 ⟹ fire one bq'→qa (lemma_bq_qa_thue) → u'; nbq(u')<nbq(u) (firing removes 1, creates 0);
          fr_gaps(u')=fr_gaps(u) (bq'→qa preserves the free-reduced form of sub); IH ⟹ u'~thue decode(fr_gaps(u))
          ⟹ u~thue decode(fr_gaps(u)).
    - `lemma_act_syls_fr_gaps`: `act_syls(q·sub(u)·q) = gap_syls(fr_gaps(u))` — via `decode(fr_gaps(u))=:ū`
      bq'-free ⟹ sub(ū) reduced ⟹ ū-gaps nf ⟹ q·sub(ū)·q=gap_word(ū-gaps); sub(u)≡sub(ū) (thue⟹group)
      ⟹ act_syls(q sub u q)=act_syls(q sub ū q)=gap_syls(ū-gaps) [W-induction ✅].
    - ASSEMBLE (`lemma_m3_readback`): act_syls(u)=act_syls(v) ⟹ fr_gaps(u)=fr_gaps(v) ⟹ decode equal ⟹
      u~thue decode=decode~thue v ⟹ u~thue v ⟹ [both Thue-nf] u=v. Then dispatcher + R3.
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
