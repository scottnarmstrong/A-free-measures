#!/usr/bin/env bash
# Run leanprover/comparator on Challenges/AFreeMeasures/comparator.json, including NanoDa.
# Verification script, released under Apache-2.0.
# Usage: scripts/verify_comparator.sh
#
# Environment:
#   COMPARATOR_BIN, COMPARATOR_LEAN4EXPORT  existing toolchain-compatible binaries (otherwise the
#                                           pinned commits below are cloned and built in the cache)
#   COMPARATOR_LANDRUN, COMPARATOR_NANODA   landrun and nanoda_bin (default: found in PATH)
#   AFREE_COMPARATOR_CACHE                  tool cache (default: ~/.cache/a-free-measures-comparator)
#   COMPARATOR_BUILD_LOCK                   optional lock file; the prebuild then runs under flock
#   LEAN_NUM_THREADS                        threads for the prebuild and the comparator (default 2)
set -euo pipefail
if [ "$#" -ne 0 ]; then
  echo "usage: scripts/verify_comparator.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/.." && pwd)
config=Challenges/AFreeMeasures/comparator.json
cache=${AFREE_COMPARATOR_CACHE:-"$HOME/.cache/a-free-measures-comparator"}
comparator_commit=32bd61da1d68fbaa310234964e9b820b03a0f82f
lean4export_commit=6cea97789dc088ea47fcea15692db85685aedac5

# Use pinned builds: globally installed exporters may use another .olean format.
# Explicit overrides may point to existing toolchain-compatible binaries.
comparator=${COMPARATOR_BIN:-"$cache/comparator/.lake/build/bin/comparator"}
lean4export=${COMPARATOR_LEAN4EXPORT:-"$cache/lean4export/.lake/build/bin/lean4export"}
checkout_tool() {
  local name=$1 commit=$2
  mkdir -p "$cache"
  [ -d "$cache/$name/.git" ] || git clone -q --filter=blob:none \
    "https://github.com/leanprover/$name.git" "$cache/$name"
  git -C "$cache/$name" fetch -q --depth 1 origin "$commit"
  git -C "$cache/$name" checkout -q --detach "$commit"
  [ "$(tr -d '[:space:]' < "$cache/$name/lean-toolchain")" = \
    "$(tr -d '[:space:]' < "$root/lean-toolchain")" ] || {
    echo "error: $name toolchain differs from the project's" >&2; exit 1;
  }
  [ -x "$cache/$name/.lake/build/bin/$name" ] || \
    (cd "$cache/$name" && LEAN_NUM_THREADS=2 nice -n 10 lake build "$name")
}
if [ -z "${COMPARATOR_BIN:-}" ]; then
  checkout_tool comparator "$comparator_commit"
  comparator="$cache/comparator/.lake/build/bin/comparator"
fi
if [ -z "${COMPARATOR_LEAN4EXPORT:-}" ]; then
  checkout_tool lean4export "$lean4export_commit"
  lean4export="$cache/lean4export/.lake/build/bin/lean4export"
fi
landrun=${COMPARATOR_LANDRUN:-$(command -v landrun || true)}
nanoda=${COMPARATOR_NANODA:-$(command -v nanoda_bin || true)}
for tool in "$comparator" "$lean4export" "$landrun" "$nanoda"; do
  [ -n "$tool" ] && [ -x "$tool" ] || {
    echo "error: comparator, lean4export, landrun and nanoda_bin must be executable" >&2
    exit 1
  }
done

cd "$root"
[ -f "$config" ] || { echo "error: $config not found" >&2; exit 1; }

mapfile -t modules < <(python3 -I -c \
  'import json,sys; c=json.load(open(sys.argv[1])); print(c["challenge_module"]); print(c["solution_module"])' \
  "$config")
[ ${#modules[@]} -eq 2 ] || { echo "error: invalid comparator config" >&2; exit 1; }
# Discard only the challenge library's artifacts so both environments are freshly built.
rm -rf "$root/.lake/build/lib/lean/Challenges" "$root/.lake/build/ir/Challenges"
echo "=== comparator: Challenges/AFreeMeasures"
# Prebuild with bounded parallelism (this also builds the library if it is not yet built);
# comparator's sandboxed builds then find warm artifacts.
prebuild=(lake build "${modules[@]}")
if [ -n "${COMPARATOR_BUILD_LOCK:-}" ]; then
  prebuild=(flock "$COMPARATOR_BUILD_LOCK" "${prebuild[@]}")
fi
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} nice -n 10 "${prebuild[@]}" < /dev/null || {
  echo "=== Challenges/AFreeMeasures: FAIL (build)"; exit 1;
}
if COMPARATOR_LEAN4EXPORT="$lean4export" COMPARATOR_NANODA="$nanoda" \
  COMPARATOR_LANDRUN="$landrun" LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} \
  nice -n 10 lake env "$comparator" "$config"; then
  echo "=== Challenges/AFreeMeasures: PASS"
else
  echo "=== Challenges/AFreeMeasures: FAIL"; exit 1
fi
