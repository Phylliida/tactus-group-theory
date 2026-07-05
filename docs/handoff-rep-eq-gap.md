# Handoff: `b_rcoset_rep(nf gap) = gap` — a free-group geodesic-coset lemma

**Audience:** a Verus proving agent picking this up cold.
**Crate:** `/home/bepis/prog/verus-cad/tactus-group-theory` (a Verus fork with a **Lean 4 backend** — see §7).
**Verify with:** `./check.sh --verify-module m3_blinker` (crate-local script; Lean backend + group-theory export).
Do **not** use `assume`/`admit`/`external_body`. Full end-to-end proof required.

---

## 0. YOUR TASK (read this first)

**Prove exactly one lemma — `lemma_b_rcoset_rep_eq_gap` — end-to-end in Verus, and nothing else.**

Concretely, I am asking you to:
1. **Write and fully verify** the proof body of `lemma_b_rcoset_rep_eq_gap` (statement in §1). It must
   verify with `./check.sh --verify-module m3_blinker` (plus whichever module hosts it) reporting
   **`0 errors`**, using **no `assume`, no `admit`, no `#[verifier::external_body]`, no `#[verifier::exec_allows_no_decreases_clause]`-style escape hatches** — a genuine end-to-end proof.
2. You **may** add small helper `proof fn`/`spec fn` lemmas, and you **may** make at most these
   supporting items `pub`: `lemma_word_lex_rank_base_injective` (`normal_form_afp_textbook.rs:72`), and
   any other existing private lemma in the `b_rcoset`/reduction machinery you genuinely need. Note any
   `pub` you flip. Do **not** weaken or change any existing lemma's statement.
3. You **choose** the proof route — the **parity route (§5, §8) is recommended** (reuses the already-
   proven `lemma_parity_head_cap`); the direct `min_len`/`min_lex` route (§4) is the fallback. Either is
   fine as long as it verifies honestly.
4. **Do NOT prove or modify anything upstream/downstream.** Everything in §2 (the M3 word problem, the
   `act_syls` induction "B3", the parsing "B5") is **background only** — it explains *why* the lemma
   matters. Your deliverable is this single lemma; the rest is already handled or handled elsewhere.

**Definition of done / what to report back:** the final verifying source (the lemma + any helpers),
the host module, the exact `./check.sh --verify-module …` command(s) you ran and their
`N verified, 0 errors` output line, and a list of any `pub` flips you made. If you get **stuck**, report
the smallest failing sub-goal with the exact Verus/Lean error and what you tried — do not paper over it.

**If the lemma statement itself needs a tweak** to be provable (e.g. an extra hypothesis that the nf
gaps genuinely satisfy — they are `word_valid(_,2)`, reduced, `no_sym(_,Inv0)`, `lead(_,0)≤1`, and the
AFP is `tower_afp_data(m3_data(),0)` which is valid), flag it explicitly and explain why, rather than
silently changing it — the caller (`B3`) must be able to supply the hypotheses.

---

## 1. The one lemma we need

Prove (target location: `src/m3_blinker.rs`, or `src/normal_form_afp_textbook.rs` if you need
private helpers there — see §6):

```rust
pub proof fn lemma_b_rcoset_rep_eq_gap(g: Word)
    requires
        word_valid(g, 2),                                   // over free_group(2) = F(a,b)
        crate::reduction::is_reduced(g),                    // freely reduced (no adjacent inverse pair)
        no_sym(g, Symbol::Inv(0)),                          // contains no a⁻¹  (a = Gen(0))
        crate::m1_guard::lead(g, 0) <= 1,                   // leading run of a (Gen(0)) has length ≤ 1
    ensures
        crate::normal_form_afp_textbook::b_rcoset_rep(
            crate::tower::tower_afp_data(crate::m3_blinker::m3_data(), 0), g) =~= g
{
    ... // THIS is the task
}
```

`no_sym` is a small recursive predicate already defined in `m3_blinker.rs`:
```rust
pub open spec fn no_sym(w: Word, t: Symbol) -> bool
    decreases w.len()
{ w.len() == 0 || (w[0] != t && no_sym(w.drop_first(), t)) }
```
and `m3_blinker.rs` already has `lemma_no_sym_concat`, `lemma_no_sym_index`
(`no_sym(w,t) ⟹ ∀i. w[i] != t`), and `lemma_no_sym_cons`.

### Why these three hypotheses = "nf gap"
`g` ranges over the *gaps* of `sub(u)` for a Thue-**normal-form** word `u` (see §2). Gaps are
sub-words over {a, b, b⁻¹} (Gen0, Gen1, Inv1) — they contain **no a⁻¹** (that's `no_sym(g,Inv(0))`),
they're **reduced**, and the M3 normal form caps the **leading a-run at ≤ 1** (`lead(g,0) ≤ 1`). These
three are exactly what makes `g` its own coset representative.

---

## 2. Context — why this lemma matters (you do NOT need to prove anything in this section)

M3 is the group `G = ⟨q,a,b,q′ | qa=bq′, q′a=bq⟩`, proven (via Tietze `q′=b⁻¹qa`) isomorphic to the
**HNN extension** `⟨a,b,q | q a² q⁻¹ = b²⟩` of `F(a,b)`, associated subgroups `⟨a²⟩ ↔ ⟨b²⟩`.
We are proving `sub` is injective on normal-form words (the `⟹` direction of the word problem).

The crate provides a **canonical syllable sequence** `act_syls(data, w)` (see §3) that is a **group
invariant** (already proven: `lemma_syls_preserved` in `m3_blinker.rs`). For a Britton-reduced word,
`act_syls` reads off one syllable per stable letter (`q`), each syllable's `rep` field being
`b_rcoset_rep(afp, gap)` — the canonical representative of the base-group gap between two `q`'s,
modulo the associated subgroup.

**The action `textbook_psi_p` (§3) leaves a "carry" `phi_inv(b_rcoset_h(gap))` between syllables,
which is `ε` iff `b_rcoset_rep(gap) = gap`.** So THIS lemma (rep = gap for nf gaps) is exactly what
makes the carries vanish, the syllables come out as the literal gaps, and the readback injective.
Everything downstream (the `act_syls` induction "B3", the gap-parsing "B5") depends on it.

---

## 3. The AFP coset machinery (all definitions you need, with file:line)

**`tower_afp_data`** (`src/tower.rs:32`): for `data = m3_data()` and `k=0` it builds an `AmalgamatedData`:
```rust
pub open spec fn tower_afp_data(data: HNNData, k: nat) -> AmalgamatedData {
    AmalgamatedData {
        p1: tower_presentation(data, k),
        p2: data.base,                                   // = free_group(2) = F(a,b)
        identifications: Seq::new(data.associations.len(),
            |i| (shift_word(data.associations[i].0, k*ng), data.associations[i].1)),
    }
}
```
For `m3_data()` (`src/m3_blinker.rs`): `base = free_group(2)`, `associations = [ (b², a²) ]` where
`b² = [Gen(1),Gen(1)]`, `a² = [Gen(0),Gen(0)]`. So with `k=0`, `shift_word(b²,0)=b²`, and the
AFP has `p2 = free_group(2)`, `identifications = [ (b², a²) ]`, hence:
- `b_words(afp) = [ identifications[i].1 ] = [ a² ] = [ [Gen0,Gen0] ]`.
- **the right subgroup B = ⟨a²⟩**.

**`b_rcoset_rep`** (`src/normal_form_afp_textbook.rs:529`) — the value we must show equals `g`:
```rust
pub open spec fn b_rcoset_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = b_rcoset_min_len(data, g);
    let r = b_rcoset_min_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p2.num_generators)
        && same_b_rcoset(data, g, rep)
        && rep.len() == l
        && word_lex_rank_base(rep, 2 * data.p2.num_generators + 1) == r
}
```
Supporting defs (same file):
```rust
// 471 (normal_form_amalgamated.rs actually):
same_b_rcoset(data, w1, w2) := in_right_subgroup(data, concat(w1, inverse_word(w2)))   // w1·w2⁻¹ ∈ B
// normal_form_amalgamated.rs:674
in_right_subgroup(data, w) := in_generated_subgroup(data.p2, b_words(data), w)          // w ∈ ⟨a²⟩
// benign.rs:41
in_generated_subgroup(p, gens, w) := ∃ factors. factors_from_generators(gens,factors)
                                       && equiv_in_presentation(p, concat_all(factors), w)
// normal_form_afp_textbook.rs:474
has_b_rcoset_word_of_len(data,g,l) := ∃ w. word_valid(w,p2.num_gens) && same_b_rcoset(data,g,w) && w.len()==l
// 482 (recursive on l):
no_shorter_b_rcoset_word(data,g,l) := l==0 || (!has_b_rcoset_word_of_len(data,g,l-1) && no_shorter_...(l-1))
// 492:
is_min_b_rcoset_len(data,g,l) := has_b_rcoset_word_of_len(data,g,l) && no_shorter_b_rcoset_word(data,g,l)
// 496:
b_rcoset_min_len(data,g) := choose|l| is_min_b_rcoset_len(data,g,l)
// 501 has_b_rcoset_word_of_len_rank, 508 no_smaller_b_rcoset_lex (recursive on r),
// 519 is_min_b_rcoset_lex, 523 b_rcoset_min_lex(data,g) := choose|r| is_min_b_rcoset_lex(data,g, min_len, r)
```
**Lex rank** (`src/normal_form_afp_textbook.rs:61`, base passed is `2*p2.num_generators+1 = 5`):
```rust
word_lex_rank_base(w, base) := if w.len()==0 {0}
    else { symbol_to_column(w.first()) + base * word_lex_rank_base(w.drop_first(), base) }
// src/todd_coxeter.rs: symbol_to_column(Gen(i)) = 2*i ;  symbol_to_column(Inv(i)) = 2*i+1
```
**KEY lex fact:** `symbol_to_column(Gen(0)) = 0 < 1 = symbol_to_column(Inv(0))`. First symbol dominates
the rank (it's the low-order digit, but among **equal-length** words with equal tails the first symbol
decides). So among the two min-length reps in a head-1 coset (`a·tail` vs `a⁻¹·tail`), `a·tail = g`
has the smaller rank ⇒ is chosen.

**(only needed if you go the "compute act_syls" route later — NOT for this lemma):**
`textbook_psi_p`/`textbook_act_hnn`/`act_syls` live at `src/britton_via_tower.rs:4627,4458` and
`machine_group.rs:4458`.

---

## 4. The mathematics (complete, rigorous)

Write `g = a^h · tail` where `h = lead(g,0) ∈ {0,1}` and `tail = g` with its leading a-run removed
(so `tail` has **no leading Gen(0)**, and — inheriting from `g` — **no Inv(0)** anywhere, and is reduced).

**The coset `⟨a²⟩·g` (left coset).** `same_b_rcoset(g, w)` ⟺ `g·w⁻¹ ∈ ⟨a²⟩` ⟺ `g·w⁻¹ ≡ a^{2k}`
(free group; a word in `⟨a²⟩` is freely-equivalent to `a^{2k}` for some `k∈ℤ`, via
`in_generated_subgroup` with `gens=[a²]`). Hence `w ≡ a^{-2k}·g = a^{-2k}·a^h·tail = a^{h-2k}·tail`.
Because `tail` starts with a non-`a`, non-`a⁻¹` symbol (Gen1 or Inv1), the word `a^{j}·tail` (any `j∈ℤ`,
`a^j` meaning `Gen0^j` if `j≥0` else `Inv0^{-j}`) is **already reduced**, of length `|j| + |tail|`.

**Geodesic bound.** Any coset word `w` satisfies `w ≡ a^{h-2k}·tail` for some `k`, so
`|reduced(w)| = |h-2k| + |tail|`. Over `k∈ℤ`, `min |h-2k|`:
- `h=0`: minimized at `k=0`, value `0`. Unique minimizer ⇒ min-len word is `tail = g`, unique.
- `h=1`: `|1-2k|` is minimized at `k=0` (`=1`) and `k=1` (`|1-2|=1`); value `1`. **Two** minimizers,
  `a·tail = g` (k=0) and `a⁻¹·tail` (k=1), both length `1+|tail|`.

Therefore `b_rcoset_min_len(afp, g) = h + |tail| = |g|`, and:
- `h=0`: the unique min-len rep is `g`. ⇒ `b_rcoset_rep(afp,g) = g`.
- `h=1`: two min-len reps `g=a·tail` and `a⁻¹·tail`; by the lex fact `rank(a·tail) < rank(a⁻¹·tail)`
  (first symbols `Gen0` col 0 vs `Inv0` col 1, equal tails), so `b_rcoset_min_lex` selects `rank(g)`,
  and `g` is the unique word of that (len, rank) ⇒ `b_rcoset_rep(afp,g) = g`.

Uniqueness of the `choose` is handled by `lemma_word_lex_rank_base_injective`
(`normal_form_afp_textbook.rs:72`, **currently private — make it `pub`**): equal length + equal rank +
each column `< base` ⇒ equal words.

---

## 5. Existing lemmas you can lean on (file:line — sig)

- `lemma_b_rcoset_rep_props` (`normal_form_afp_textbook.rs:10404`): for valid AFP + `word_valid(g,p2.ng)`,
  gives `same_b_rcoset(g, rep)`, `word_valid(rep,p2.ng)`, `rep.len()==b_rcoset_min_len(g)`,
  `word_lex_rank_base(rep,5)==b_rcoset_min_lex(g)`. **Use this to get `rep`'s properties, then show `g`
  matches them and invoke injectivity — you may not need to compute `min_len`/`min_lex` as raw numbers.**
- `lemma_b_rcoset_rep_invariant` (`:10640`): `same_b_rcoset(g1,g2) ⟹ b_rcoset_rep(g1)=~=b_rcoset_rep(g2)`.
- `lemma_b_rcoset_rep_idempotent` (`:10698`): `b_rcoset_rep(b_rcoset_rep(g)) =~= b_rcoset_rep(g)`.
- `lemma_word_lex_rank_base_injective` (`:72`, **private → make pub**): equal len + equal rank +
  columns < base ⇒ `w1 =~= w2`.
- `lemma_tower_afp_data_valid(data,k)` (`tower.rs:170`): the AFP is valid (needed as a precondition
  for the coset lemmas). Also `crate::hnn::lemma_hnn_...`/`m3_blinker::lemma_m3_data_valid` for
  `hnn_data_valid(m3_data())`, and `crate::higman_operations::lemma_free_group_valid(2)`.
- `lemma_concat_reduced(a,b)` (`machine_group.rs:8955`): `is_reduced(a)`, `is_reduced(b)`,
  `(len>0 ⟹ !is_inverse_pair(a.last,b[0])) ⟹ is_reduced(a+b)`.
- `signed_power(i,a)` (`machine_group.rs:3469`): `a≥0 ⟹ symbol_power(Gen(i),a)`, else `symbol_power(Inv(i),-a)`.
  `symbol_power(s,n) = Seq::new(n, |_| s)` (`machine_group.rs`). `lemma_signed_power_add`
  (`:7615`, equiv form), `lemma_inverse_signed_power` (`:8017`).
- `lemma_free_group_equiv_freely_equivalent(n,w1,w2)` (`free_word_problem.rs:135`):
  `equiv(free_group(n),w1,w2) ⟹ freely_equivalent(w1,w2)`. `freely_equivalent(w1,w2) := ∃w. reduces_to(w1,w)&&reduces_to(w2,w)` (`reduction.rs`).
- `lemma_reduced_reduces_to_self(w,w2)` (`reduction.rs:818`): `is_reduced(w) && reduces_to(w,w2) ⟹ w==w2`.
- **Already proven in `m3_blinker.rs` and reusable** — the parity lemma this feeds into:
  - `lemma_parity_head_cap(g1,g2,k)`: reduced g1,g2, `no_sym(_,Inv0)`, `lead(_,0)≤1`,
    `equiv(free_group(2), g1, concat(signed_power(0,2k), g2)) ⟹ g1 =~= g2`.
  - helpers `lemma_reduced_unique(g1,g2)` (equiv + both reduced ⟹ equal), `lemma_prepend_gen0(g,n)`
    (`n≥2` + reduced + head≠a⁻¹ ⟹ `a^n·g` reduced with `lead ≥ 2`), `lemma_gen0_pow_valid(n)`.

  **ALTERNATIVE PROOF ROUTE using `lemma_parity_head_cap` (may be much shorter than raw min_len):**
  From `lemma_b_rcoset_rep_props`, `rep := b_rcoset_rep(afp,g)` satisfies `same_b_rcoset(g,rep)`, i.e.
  `g·rep⁻¹ ∈ ⟨a²⟩`, i.e. `equiv(free_group(2), g, concat(signed_power(0,2k), rep))` for some `k`
  (unfold `in_generated_subgroup` to extract the `a^{2k}` and the exponent `k`). If you can show `rep`
  is **also** nf (reduced + `no_sym(_,Inv0)` + `lead≤1`), then `lemma_parity_head_cap(g, rep, k)`
  gives `g =~= rep` directly — **no explicit `min_len`/`min_lex` computation needed.** The remaining
  obligation becomes "the canonical rep of an nf word is itself nf": `rep` is reduced (min-len ⇒ no
  cancellation, else a reduction gives a strictly shorter same-coset word — contradiction with
  `no_shorter_b_rcoset_word`), `lead(rep,0)≤1` (min-len ⇒ can't have `a²` prefix, else drop it for a
  shorter coset word), and `no_sym(rep,Inv0)` (the lex-min among min-len avoids the `a⁻¹`-headed tie —
  this is the one place the lex fact `Gen0<Inv0` is essential). **Weigh this route vs the direct
  min_len route in §4; the parity route reuses machinery you already have and may dodge the recursive
  `no_shorter_b_rcoset_word`/`no_smaller_b_rcoset_lex` inductions.**

---

## 6. Where to put it / `pub` changes

- The lemma can live in `src/normal_form_afp_textbook.rs` (next to the coset machinery — then the
  private `lemma_word_lex_rank_base_injective` and the `no_shorter_*` defs are in scope), exposed `pub`
  for `m3_blinker.rs` to call. OR in `m3_blinker.rs` if you make `lemma_word_lex_rank_base_injective`
  `pub` (one-word edit at `normal_form_afp_textbook.rs:72`). The latter keeps M3 code together.
- Several helper spec fns (`no_shorter_b_rcoset_word`, `has_b_rcoset_word_of_len`, `b_rcoset_min_len`,
  …) are already `pub open spec`. Good.
- Making a `proof fn` `pub` re-verifies its home module once (slow for big files) but is sound and
  additive. `m3_blinker.rs` already made `lemma_single_step_preserves_syls`,
  `lemma_p_reduced_initial_no_collapse`, `lemma_no_collapse_gives_m` pub this way.

---

## 7. Verus-fork / Lean-backend idioms & gotchas (IMPORTANT — this fork differs from stock Verus)

- **Verify:** `./check.sh --verify-module m3_blinker` from the crate root. Success line:
  `verification results:: N verified, 0 errors`. Ignore `-->` span lines (they are notes, not errors).
  A full-crate run is just `./check.sh` (slow). Do NOT pass `raw=true`-style verbosity.
- **Lean backend:** "rlimit exceeded" is a mislabel for Lean `maxHeartbeats`. If you hit it, split the
  proof into smaller `proof fn` helpers (each gets a fresh context) rather than raising limits.
- **Recursive spec fns do NOT auto-unfold on literals** (Lean backend). For a concrete word like
  `[Gen0,Gen0]`, `no_sym`/`lead`/`word_lex_rank_base` won't compute by themselves — add explicit
  cons/`drop_first` step asserts, or a one-step unfold helper (see `lemma_no_sym_cons` in m3_blinker.rs
  for the pattern). `by (compute)` works on **literal** args but **HANGS on `let`-bound args** — inline
  literals into the `by(compute)` assert.
- **`choose` uniqueness:** `b_rcoset_min_len`/`b_rcoset_min_lex`/`b_rcoset_rep` are all `choose`. To pin
  `b_rcoset_rep(afp,g) =~= g`, you must show the chosen witness is forced: prove `g` satisfies the
  `choose` predicate AND that any other witness equals `g` (use `lemma_word_lex_rank_base_injective`
  for the len+rank tie-break). The crate's own `lemma_b_rcoset_rep_props` already extracts the chosen
  `rep`'s properties — prefer proving `rep =~= g` over recomputing the `choose` from scratch.
- **`=~=` vs `==`:** words are `Seq<Symbol>`; use `=~=` (extensional) for equality goals; it implies `==`.
- **`equiv_in_presentation` congruence** helpers (used heavily in m3_blinker): `lemma_equiv_concat_left`
  (right-multiply), `lemma_equiv_concat_right` (left-multiply), `lemma_equiv_transitive`,
  `lemma_equiv_symmetric` (in `presentation.rs`/`presentation_lemmas.rs`).
- **Commit freely** (`git add . && git commit` inside the crate) at each green sub-lemma. The verus
  function-level cache persists; small edits re-verify fast.
- **Full quick-reference of idioms:** `CLAUDE.md` at the repo root (`/home/bepis/prog/verus-cad/CLAUDE.md`)
  — §4 Patterns, §5 Common Errors. The M3 plan with the full readback design is
  `tactus-group-theory/docs/m3-blinker-plan.md` (see "READBACK BRICKS" — this lemma is the B3 foundation).

---

## 8. Suggested proof skeleton (parity route — recommended)

```rust
pub proof fn lemma_b_rcoset_rep_eq_gap(g: Word)
    requires word_valid(g,2), is_reduced(g), no_sym(g,Inv(0)), lead(g,0) <= 1,
    ensures b_rcoset_rep(afp(), g) =~= g          // afp() := tower_afp_data(m3_data(),0)
{
    // 0. validity: lemma_m3_data_valid(); lemma_tower_afp_data_valid(m3_data(),0);
    //    lemma_free_group_valid(2); establish amalgamated_data_valid(afp()) & presentation_valid(p2).
    let rep = b_rcoset_rep(afp(), g);
    lemma_b_rcoset_rep_props(afp(), g);            // same_b_rcoset(g,rep), word_valid(rep,2), len/rank facts

    // 1. Extract k with  equiv(free_group(2), g, signed_power(0,2k) + rep):
    //    same_b_rcoset(g,rep) = in_right_subgroup(g·rep⁻¹) = in_generated_subgroup(p2,[a²], g·rep⁻¹).
    //    Unfold in_generated_subgroup ⟹ ∃ factors of a²/a⁻² with concat_all ≡ g·rep⁻¹.
    //    concat_all(factors) ≡ signed_power(0, 2k) where k = (#a² − #a⁻²).   [helper: factors of a² ≡ a^{2k}]
    //    Then g·rep⁻¹ ≡ a^{2k} ⟹ g ≡ a^{2k}·rep  (right-multiply by rep, congruence).

    // 2. rep is nf:  (a) is_reduced(rep):  suppose has_cancellation(rep); reduce_at gives rep' with
    //        reduces_one_step(rep,rep'), same group element ⟹ same_b_rcoset(g,rep'), |rep'| < |rep| = min_len
    //        ⟹ has_b_rcoset_word_of_len(g, min_len−1), contradicting no_shorter_b_rcoset_word. So reduced.
    //    (b) lead(rep,0) ≤ 1: if rep = a·a·rest then a⁻²·rep is a shorter same-coset word (drop the a²
    //        head) ⟹ contradiction with min_len as in (a).
    //    (c) no_sym(rep,Inv(0)): the min-len rep can't be a⁻¹-headed — a⁻¹·rest is len-tied with a·rest
    //        (=drop the leading a⁻¹, prepend a) which has SMALLER lex rank (Gen0 col 0 < Inv0 col 1),
    //        contradicting rep being min_lex. (And rep has no interior Inv0 because the coset only shifts
    //        the a-head; formally: from g ≡ a^{2k}·rep with g having no Inv0 and the a^{2k} only touching
    //        the head, rep's non-head part = g's non-head part, which has no Inv0.)

    // 3. lemma_parity_head_cap(g, rep, k)  ⟹  g =~= rep.  Return  rep =~= g.
}
```
If the parity route's step 2(c)/1 turn out awkward, fall back to the **direct min_len/min_lex route**
of §4: prove `is_min_b_rcoset_len(afp,g,|g|)` and `is_min_b_rcoset_lex(afp,g,|g|,rank(g))` and pin the
two `choose`s (uniqueness via `lemma_word_lex_rank_base_injective` + a min-uniqueness helper), then the
outer `choose` for `b_rcoset_rep` resolves to `g`. This is more mechanical but heavier on the recursive
`no_shorter_*`/`no_smaller_*` inductions.

**Deliverable:** `lemma_b_rcoset_rep_eq_gap` verifying with `./check.sh --verify-module m3_blinker`
(and whichever module hosts it), `0 errors`, no `assume`/`admit`/`external_body`.
