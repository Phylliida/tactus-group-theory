#!/usr/bin/env bash
# Verify tactus-group-theory under the Lean backend — the LIVE package-check
# gate (Lean actually elaborates). The old `--emit-lean` Lean-skipping flag was
# dropped 2026-07-16: post-M6 a warm verifying run costs about the same as
# emit-only, so the gate verifies for real on every run.
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

# B6: the no-search claim below must cover ONLY the current emission — stale
# .lean files from older binaries linger in the tree. Delete .lean artifacts
# (NOT .olean/.verified caches — those are content-keyed and stay valid) so
# the run regenerates exactly what the current binary emits.
find "$HERE/target/tactus-lean" -name '*.lean' -delete 2>/dev/null || true

"$VERUS" --lean-backend -V cache --crate-type=lib "$HERE/src/lib.rs" "$@" 2>&1 | tee "$LOG"
rc="${PIPESTATUS[0]}"
echo "[check.sh] full output saved to $LOG (exit $rc)" >&2
[[ "$rc" -ne 0 ]] && exit "$rc"

# B6 no-search gate claim (DESIGN-transparent-automation.md §5): no emitted
# artifact imports the search module, and no search-ladder tactic is named in
# tactic position. The derivation-first closer (S2c) means this must hold with
# ZERO allowed residue — a violation fails the gate.
#
# The check covers ONLY the current emission: stale .lean files from older
# binaries linger in the tree (the gate doesn't clean it), so .lean artifacts
# are deleted before the run and the current binary regenerates exactly its
# own output (.olean/.verified caches survive — content-keyed, still valid).
TOOLS="$(dirname "$(dirname "$(dirname "$VERUS")")")"
python3 "$TOOLS/tools/check-no-search.py" "$HERE/target/tactus-lean" || {
  echo "[check.sh] no-search gate claim FAILED — see above" >&2
  exit 1
}
echo "[check.sh] no-search gate claim holds" >&2
