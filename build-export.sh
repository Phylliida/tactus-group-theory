#!/usr/bin/env bash
# Build the clean cross-crate export for tactus-computability-theory.
#
# Exports ONLY the CEER->f.p.-group dependency cone (src/ceer_lib.rs) — a closed,
# fully-verified 12-module subset that excludes the exec layer (runtime/todd_coxeter,
# which hits the Lean-backend panic / usize::MAX deferral) and the Britton/normal-form
# showcase (not needed downstream). Crate-named `verus_group_theory` so the
# computability-theory sources' `use verus_group_theory::...` resolve unchanged.
#
# Produces  export/verus_group_theory.vir  +  export/libverus_group_theory.rlib
# which the dependent crate imports via:
#   --import verus_group_theory=<.vir> --extern verus_group_theory=<.rlib>
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"
mkdir -p "$HERE/export"
exec "$VERUS" --lean-backend --crate-type=lib --compile \
  --export "$HERE/export/verus_group_theory.vir" \
  --crate-name verus_group_theory \
  "$HERE/src/ceer_lib.rs" \
  -o "$HERE/export/libverus_group_theory.rlib"
