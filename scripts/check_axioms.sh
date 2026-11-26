#!/usr/bin/env bash
# Fails if any `#print axioms` output in scripts/Axioms.lean names a non-standard axiom.
set -euo pipefail
out=$(lake env lean scripts/Axioms.lean 2>&1) || { echo "$out"; exit 1; }
echo "$out"
bad=$(echo "$out" | grep -oE "depends on axioms: \[[^]]*\]" | tr -d '[]' | sed 's/depends on axioms: //' \
      | tr ',' '\n' | sed 's/^ *//;s/ *$//' | grep -vxE 'propext|Classical.choice|Quot.sound|' || true)
if [ -n "$bad" ]; then echo "Non-standard axioms found:"; echo "$bad"; exit 1; fi
echo "Axiom audit passed."
