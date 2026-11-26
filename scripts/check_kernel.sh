#!/usr/bin/env bash
# Re-checks every module under Lab/ with leanchecker, one module at a time.
# `leanchecker Lab` matches every module whose name starts with `Lab` and replays them in
# parallel, each with its own copy of mathlib in memory, which can exhaust a GitHub runner.
# The root file Lab.lean only imports and declares nothing, so it is not replayed itself.
set -euo pipefail
mods=$(find Lab -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | sort)
for m in $mods; do
  echo "leanchecker: $m"
  lake env leanchecker "$m"
done
echo "Kernel re-check passed."
