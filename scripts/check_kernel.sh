#!/usr/bin/env bash
# Re-checks every module under Lab/ with leanchecker, one module at a time.
# `leanchecker Lab` matches every module whose name starts with `Lab` and replays them in
# parallel, each with its own copy of mathlib in memory, which can exhaust a GitHub runner.
# The root file Lab.lean only imports and declares nothing, so it is not replayed itself.
#
# Modes:
#   bash scripts/check_kernel.sh                 full replay of every module (the default;
#                                                CI runs this on every push to main)
#   KERNEL_REPLAY=incremental bash scripts/...   skip a module only if this exact build of it
#                                                already passed leanchecker on an earlier run
#
# Incremental mode keeps one record per module in .lake/build/kernel-replayed/ (CI caches it with
# the rest of .lake/build). A record holds Lake's dependency hash for the module, which covers its
# source, the full transitive import closure, the Lean version and the compiler options, plus the
# SHA-256 of the module's .olean. A module is skipped only when both match a record written after
# a successful leanchecker run, i.e. when it is byte-for-byte the object that was already checked
# against the very same dependencies. Anything new or changed, and everything that imports it, is
# replayed again.
set -euo pipefail
mode=${KERNEL_REPLAY:-full}
state=.lake/build/kernel-replayed
mods=$(find Lab -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | sort)
checked=0; skipped=0
mkdir -p "$state"
for m in $mods; do
  base=.lake/build/lib/lean/$(echo "$m" | tr . /)
  key=""
  if [ -f "$base.trace" ] && [ -f "$base.olean" ]; then
    dep=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["depHash"])' "$base.trace")
    key="$dep $(sha256sum "$base.olean" | cut -d' ' -f1)"
  fi
  if [ "$mode" = incremental ] && [ -n "$key" ] && [ -f "$state/$m" ] && [ "$(cat "$state/$m")" = "$key" ]; then
    echo "leanchecker: $m (unchanged since its last successful replay, skipped)"
    skipped=$((skipped + 1))
    continue
  fi
  echo "leanchecker: $m"
  lake env leanchecker "$m"
  [ -n "$key" ] && echo "$key" > "$state/$m"
  checked=$((checked + 1))
done
echo "Kernel re-check passed ($mode mode: $checked replayed, $skipped unchanged and skipped)."
