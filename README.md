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
./check.sh
```

This runs the bundled tactus `verus --lean-backend` over the whole crate. Expect
`N verified, 0 errors`.

## Porting discipline

- **Faithful first.** Port modules bottom-up along the dependency DAG; keep the Rust spec/exec
  structure and theorem statements identical to `verus-group-theory`.
- **Keep Britton's proof technique.** Do not substitute a different proof method for Britton's
  lemma — earlier work found alternative routes to be deceptive dead ends. Preserve the
  architecture; only compress the Z3-bloat mechanics into idiomatic Lean.
- **simp only as a closer.** Never use `simp` as an intermediate tactic (Mathlib's `@[simp]` set
  drifts); pin intermediate rewrites with `rw [show LHS = RHS from by …]`.

## Status

| Module | Source lines | Status |
|---|---|---|
| `symbol` | 80 | ✅ ported, verified |
| `word` | 208 | ✅ ported, verified |

Foundation (`symbol`, `word`) ports **verbatim** — the definitional lemmas close under the Lean
default closer with no changes, and `Seq`/`=~=`/quantifier/recursion reasoning all work under
`--lean-backend`. Next along the DAG: `reduction`, `presentation`, `free_product`, `hnn` → `britton`.
