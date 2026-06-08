#!/usr/bin/env bash
# Verify tactus-group-theory under the Lean backend.
#
# Usage:
#   ./check.sh                 # verify the whole crate (src/lib.rs)
#   ./check.sh <extra args>    # pass extra flags through to verus
#
# Requires the tactus verus binary to be built at ../tactus/source/target-verus/release/verus
# (see tactus-tutorial/chapters/00-setup) and Mathlib set up in the tactus install.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"

if [[ ! -x "$VERUS" ]]; then
  echo "error: tactus verus binary not found at $VERUS" >&2
  echo "build it with: cd ../tactus/source && vargo build --release" >&2
  exit 1
fi

exec "$VERUS" --lean-backend --crate-type=lib "$HERE/src/lib.rs" "$@"
