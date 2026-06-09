#!/usr/bin/env bash
# Per-module verification of tactus-group-theory under the Lean backend.
#
# Interim driver: whole-crate `./check.sh` currently aborts on a fatal Lean-backend
# panic when lowering the exec module `runtime` (see ../BUG-vec-copy-datatype-index-lean-panic.md).
# A panic in one module aborts the whole run, masking everything else. This script
# runs `--verify-module` per module so each is reported independently; --verify-module
# still loads the whole crate's context, so cross-module reasoning is unchanged.
#
# Switch back to `./check.sh` (whole crate) once the runtime panic is fixed upstream.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"

mods=$(grep -oE 'pub mod [a-z_]+' "$HERE/src/lib.rs" | awk '{print $3}')
tot_v=0; tot_e=0; fail=0
for m in $mods; do
  out=$("$VERUS" --lean-backend --crate-type=lib "$HERE/src/lib.rs" --verify-module "$m" 2>&1)
  if echo "$out" | grep -q 'tuple_field_accessor\|panicked'; then
    printf "  %-28s PANIC (lean-backend bug)\n" "$m"; fail=1
  else
    res=$(echo "$out" | grep -oE '[0-9]+ verified, [0-9]+ errors' | head -1)
    v=$(echo "$res" | grep -oE '^[0-9]+'); e=$(echo "$res" | grep -oE '[0-9]+ errors' | grep -oE '^[0-9]+')
    tot_v=$((tot_v + ${v:-0})); tot_e=$((tot_e + ${e:-0}))
    [[ "${e:-0}" != "0" ]] && fail=1
    printf "  %-28s %s\n" "$m" "$res"
  fi
done
echo "  ----"
printf "  TOTAL: %d verified, %d errors\n" "$tot_v" "$tot_e"
exit $fail
