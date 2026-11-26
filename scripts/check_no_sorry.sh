#!/usr/bin/env bash
# Fails if a file under Lab/ contains `sorry`, unless it sits on a line marked `-- WIP`.
set -euo pipefail
hits=$(grep -rn --include='*.lean' -wE 'sorry|admit' Lab/ | grep -v -- '-- WIP' || true)
if [ -n "$hits" ]; then echo "Unfinished proofs found:"; echo "$hits"; exit 1; fi
echo "No sorry found."
