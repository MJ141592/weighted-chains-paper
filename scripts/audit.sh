#!/usr/bin/env bash
set -euo pipefail

if rg --pcre2 --glob '*.lean' \
  '^[[:space:]]*(?:@\[[^]]*\][[:space:]]*)*(?:(?:private|protected|public|noncomputable|local|scoped)[[:space:]]+)*(?:axiom|opaque|constants?|unsafe|partial)\b|\b(?:sorry|admit)\b|\b[A-Za-z0-9_]*decide[A-Za-z0-9_]*\b' \
  WeightedChains WeightedChains.lean; then
  echo "Forbidden proof escape hatch found." >&2
  exit 1
fi

# The root module intentionally follows paper order, but work-in-progress
# modules must not escape checking merely because they have not yet been added
# to that import tree.
while IFS= read -r source; do
  module="${source%.lean}"
  module="${module//\//.}"
  lake build "$module"
done < <(rg --files WeightedChains --glob '*.lean' | sort)

lake build
lake env lean -DwarningAsError=true scripts/AxiomAudit.lean
