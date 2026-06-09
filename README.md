# tactus-group-theory

Britton's Lemma and the Higman Rope Trick, formalized in Lean (via [Tactus](https://github.com/Phylliida/tactus)) and implemented in Rust.

This is a port of [`verus-group-theory`](../verus-group-theory) from the Verus/Z3 backend to
Tactus's Lean 4 backend. The Z3 path got Britton's lemma proved but stalled afterward under Z3's
verbosity; Lean is expected to make the remaining machinery — the Higman embedding ("rope trick"),
the benign-subgroup construction, and ultimately a finitely presented group whose word problem *is*
ZFC-provable-equivalence — tractable to formalize.

## Building / checking

Requires the Tactus toolchain built and Mathlib set up (see
[`../tactus-tutorial/chapters/00-setup`](../tactus-tutorial/chapters/00-setup)). Then:

```bash
./check-modules.sh   # per-module (current default — see note below)
./check.sh           # whole-crate (currently aborts on the runtime panic)
```

`check.sh` runs `verus --lean-backend` over the whole crate. It currently **aborts** on a
fatal Lean-backend panic while lowering the exec module `runtime`
(see [`../BUG-vec-copy-datatype-index-lean-panic.md`](../BUG-vec-copy-datatype-index-lean-panic.md)),
which masks every other module. Until that's fixed upstream, use `check-modules.sh`, which
verifies each module independently with `--verify-module` (same cross-module coverage, just
not aborted by one panic).

## Porting discipline

- **Faithful first.** Port modules bottom-up along the dependency DAG; keep the Rust spec/exec
  structure and theorem statements identical to `verus-group-theory`.
- **Keep Britton's proof technique.** Do not substitute a different proof method for Britton's
  lemma — earlier work found alternative routes to be deceptive dead ends. Preserve the
  architecture; only compress the Z3-bloat mechanics into idiomatic Lean.
- **simp only as a closer.** Never use `simp` as an intermediate tactic (Mathlib's `@[simp]` set
  drifts); pin intermediate rewrites with `rw [show LHS = RHS from by …]`.

## Status

**The general Britton's lemma is verified on the Lean backend** (`britton_via_tower`:
194 verified, 0 errors — matching the historical Z3 count). The entire ghost/spec/proof
mathematics of the `britton_via_tower` cone ports **verbatim** — zero changes, no compression,
even for the 12.4k-line `normal_form_afp_textbook` (231 verified). `./check-modules.sh` reports
**765 verified, 9 errors** across the crate; the only failures are the exec layer:

| Module | Status |
|---|---|
| 24 modules (symbol … `britton_via_tower`, `normal_form_afp_textbook`, `britton`, …) | ✅ verified |
| `todd_coxeter` | ⚠️ 15 verified, **9 errors** — exec fns use `usize::MAX`/`ArchWordBits` (documented tactus deferral) |
| `runtime` | 💥 **PANIC** — Lean-backend bug on `Vec<CopyDatatype>` indexing ([bug report](../BUG-vec-copy-datatype-index-lean-panic.md)) |

Both failing modules are the **exec/runtime layer**, off the Britton/Higman *math* path (the
Higman modules `higman_operations`/`machine_group` don't reference them). `britton.rs` is the
t-free base case (HNN-injectivity core), a separate partial route kept as a building block; the
general lemma is `britton_via_tower`.

Next: the **Higman rope trick** (`higman_operations`, `machine_group`), then a sibling
`tactus-computability-theory` crate for the ZFC → CEER → finitely-presented-group construction.
