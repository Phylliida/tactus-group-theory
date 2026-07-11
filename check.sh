#!/usr/bin/env bash
# Verify tactus-group-theory under the Lean backend.
#
# Usage:
#   ./check.sh                 # verify the whole crate (src/lib.rs)
#   ./check.sh <extra args>    # pass extra flags through to verus
#
# Always passes `-V cache` (function-level result cache in target/verus-cache/) so
# unchanged functions are skipped on re-runs, and always tees full output to a log file
# (default /tmp/tactus-gt-check.log, override with $TACTUS_CHECK_LOG) so a mistaken
# grep/filter never forces a re-run — just read the log.
#
# Requires the tactus verus binary to be built at ../tactus/source/target-verus/release/verus
# (see tactus-tutorial/chapters/00-setup) and Mathlib set up in the tactus install.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"
LOG="${TACTUS_CHECK_LOG:-/tmp/tactus-gt-check.log}"

if [[ ! -x "$VERUS" ]]; then
  echo "error: tactus verus binary not found at $VERUS" >&2
  echo "build it with: cd ../tactus/source && vargo build --release" >&2
  exit 1
fi

"$VERUS" --lean-backend -V cache --crate-type=lib "$HERE/src/lib.rs" --emit-lean "$@" 2>&1 | tee "$LOG"
rc="${PIPESTATUS[0]}"
echo "[check.sh] full output saved to $LOG (exit $rc)" >&2
exit "$rc"
