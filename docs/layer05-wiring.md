# Layer 0.5 wiring — exporting `cohen_layer05` and instantiating `decls_fam`

*Resolves AGENDA task #5 ("instantiate `decls_fam` with the actual CEER group"). This doc records
the cross-crate **export-surface decision** and the concrete wiring, so future sessions don't
re-derive it.*

## The goal

`src/cohen_layer05.rs` proves the Miller embedding `C₀ ↪ C` (`lemma_c0_embeds_in_c_iff`, 31/0) for an
**abstract** declared-relator family `fam: spec_fn(nat) -> Seq<Word>` satisfying `decls_family_valid`.
The wiring lives in **`tactus-computability-theory`** (which imports group-theory, not vice-versa):
`src/ceer_layer05.rs` instantiates `fam` with the real CEER enumerator's declared relators and
consumes the embedding iff.

## The export-surface tension (and its resolution)

The old export root `src/ceer_lib.rs` listed only 12 ghost modules — it deliberately excluded the
Britton/normal-form cone "not needed downstream". But `cohen_layer05`'s real dependency cone is **48
modules** (`britton_via_tower → normal_form_afp_textbook → todd_coxeter`, plus `free_basis`,
`conj_free*`, `machine_group`, …). Naively adding it dragged in the **exec showcase** (`runtime`,
`todd_coxeter`'s `*_exec` fns), which uses `usize::MAX` — rejected by the Lean backend's `tactus_auto`
(`IntegerTypeBound(UnsignedMax)`). Those verification errors then **block the `--compile` step from
emitting the `.rlib`** (rustc aborts on errors).

Three facts made the fix clean:
1. `runtime` is used **only** by `todd_coxeter.rs`.
2. **No** module outside `todd_coxeter.rs` references the exec items (`RuntimeCosetTable`, `rt_*`, …).
3. `normal_form_*` uses **only** `todd_coxeter`'s ghost SPEC layer (`CosetTable`, `symbol_to_column`,
   `coset_table_wf/consistent`, `trace_word`, `relator_closed`, `inverse_column`).

**Resolution:**
- **Split `todd_coxeter.rs`** → spec math stays in `todd_coxeter.rs` (lines 1–120: `CosetTable` +
  the 6 spec fns + 2 trace lemmas); the runtime/exec showcase moved to **`todd_coxeter_rt.rs`**
  (added to `src/lib.rs`, full crate only). The split is regression-free (full crate still 2630/20;
  the 9 `usize::MAX` exec-rejections simply relocated to `todd_coxeter_rt`).
- **`src/ceer_lib.rs`** now lists the 48-module cone of `cohen_layer05` **minus** `runtime` /
  `todd_coxeter_rt`. The spec `todd_coxeter` (0 errors) is included; the exec layer is not.
- **`build-export.sh` is now two steps** (see its header):
  - `.vir` = the verification artifact, built WITH verification + `-V cache`.
  - `.rlib` = a ghost-**erased** rustc codegen stub for cross-crate `--extern` name resolution. It
    carries no proofs (soundness is entirely in the `.vir`), so it is built `--no-verify` — which
    also sidesteps the `lake env lean` spawn flake (below). **Both share the one root
    `src/ceer_lib.rs`** so crate hashes match, else the consumer gets `error[E0463]: can't find
    crate for verus_group_theory`.

### Known-tolerated `.vir` errors (the project's pre-existing 20-error baseline)

The two cone functions proved by a direct Mathlib tactic — `ii_subset::lemma_exact_div` and
`machine_group::lemma_div_mod_id` (`... ; omega`) — spawn `lake env lean`, which intermittently
fails (`Failed to spawn lake env lean: No such file or directory`). Both are trivial, true div-mod
identities and are part of the project's accepted baseline. `lemma_act_sym_preserves_canonical_g2`
(in `normal_form_afp_textbook.rs`) was the **one new** issue — it passes at the default budget in the
full-crate composition but exceeded it in the smaller export composition; fixed with a monotone-safe
`#[verifier::rlimit(400)]` (the file already uses 28 such annotations).

## The concrete wiring (`tactus-computability-theory/src/ceer_layer05.rs`)

- `ceer_sym_to_sym` / `ceer_to_word`: index-preserving translation `CeerSymbol{Gen,Inv}` →
  `Symbol{Gen(nat),Inv(nat)}`, lifted to words.
- `ceer_relator_at(e, s, M)`: stage `s`'s contribution to level `M` — the translated relator
  `[Gen(a),Inv(b)]` when `declared_pair(e,s)=Some((a,b))` with `a,b < M`, else the inert
  `empty_word()`.
- `ceer_decls_fam_at(e, M) = Seq::new(M, |s| ceer_relator_at(e, s, M))`; `ceer_decls_fam(e)` wraps it
  as the `spec_fn(nat)->Seq<Word>` family.
- `lemma_ceer_decls_family_valid`: `decls_family_valid(ceer_decls_fam(e))` (every entry is empty or a
  2-symbol word with both indices `< M`).
- `lemma_ceer_c0_embeds_in_c_iff`: consumes `lemma_c0_embeds_in_c_iff` for the concrete family —
  `equiv_in_g_limit ⟺ equiv_in_c0_limit` over `ceer_decls_fam(e)`.

## Step (ii) — the native bridge — DONE (`ceer_layer05_bridge.rs`, 41/0)

Connects the group-theory `equiv_in_g_limit(ceer_decls_fam(e), …)` to the CEER group's **native**
`ceer_group_equiv(e, …)` by translating `CeerGroupStep ↔ DerivationStep` at a finite slice level `M`
(picked past every generator index + stage in the finite derivation; relator index = stage,
`inverted` = whether `declared_pair` is stored as `(b,a)`). Both directions —
`lemma_ceer_group_equiv_implies_c0_limit` (forward) + `lemma_c0_limit_implies_ceer_group_equiv`
(backward, with inert empty-relator steps lifting to zero CEER steps) — assembled into
**`lemma_ceer_native_embeds_in_c_iff`**: `ceer_group_equiv(e,w,ε) ⟺ equiv_in_g_limit(…)`. With
`ceer_group_backward::lemma_ceer_equiv_iff_group_equiv` this lands `ceer_equiv ⟺ equiv_in_g_limit` —
the `is_ceer_fp_embedding` shape, but over the **direct-limit** `C`.

## What remains — the Layer-2 cross-crate arc (CO-DESIGN GATED, a fresh major piece)

To actually remove `axiom_ceer_fp_embedding` (`ceer_benign.rs`) we need a SINGLE printable f.p.
presentation, i.e. collapse the direct-limit `C` to the finite Higman group `H₃`. Layer 2 already
proves this faithfully in group-theory: `cohen_cs7::lemma_C_faithful_printable` /
`cohen_bridge::lemma_C_faithful_printable_canonical`. But a feasibility scan (2026-06-26) shows this
is **not** a quick wiring step:
- ~~`lemma_C_faithful_printable` is **not** in the `cohen_layer05` export cone~~ — **the
  export-surface extension is now DONE (2026-06-26).** `src/ceer_lib.rs` was widened from the
  48-module `cohen_layer05` cone to the **87-module union** that also covers the
  `cohen_cs7`/`cohen_bridge` cone (the Higman-tower + predicate-presentation modules: `cohen_cs4*`,
  `cohen_cs5*`, `cohen_cs6`, `cohen_cs7`, `cohen_h2`, `cohen_h3`, `cohen_retraction`, `pred_*`,
  `phi_l_*`, `f_free_*`, `r_prime*`, `pa_data`, …). All 39 added modules are pure ghost (no exec
  fn / `usize::MAX` / external_body), so the feared exec-layer snags did **not** materialise —
  `runtime`/`todd_coxeter_rt` stay excluded. `lemma_C_faithful_printable` /
  `lemma_C_faithful_printable_canonical` are now importable from the computability crate. This is
  *availability only*; nothing downstream USES it yet — that is the gated collapse below.
- The mathematical bridge is the **§3.3 machine reduction**: tie the Miller direct-limit `C` (relator
  set `S = D̄`) to Cohen's `C = ⟨c;S⟩` with `is_S = {w_α(c) : (α,0)∈H₀(M)}`, matching the CEER
  `decls_fam` to the machine set `s_realizes`. The AGENDA + `machine-bridge-and-infinite-gen-plan.md`
  flag this as **co-design-gated (a foundational decision, "NOT taken solo")** — the sequential
  successor to Layer 0.5, not a mechanical finish. Do not start it without Danielle's design go.

~~Also outstanding (unrelated): `…formula.rs::lemma_encode_ge_cost_inner` fails…~~ **RESOLVED
(2026-06-26).** A fresh full-crate run of `tactus-computability-theory` is now **250 verified,
0 errors** — `lemma_encode_ge_cost_inner` passes (it also passes module-isolated, `formula` 37/0).
The earlier 208/1 was a transient toolchain-drift state that has since stabilised; no source change
was needed. The computability crate is fully green.
