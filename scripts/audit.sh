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

# The exhaustive kernel audit below can only see modules reachable from the
# root import. Fail if a source file compiles in isolation but is omitted from
# that transitive import closure.
if ! diff -u \
    <(rg --files WeightedChains --glob '*.lean' | sort) \
    <(lake env lean --deps WeightedChains.lean \
      | sed -nE 's#^.*/[.]lake/build/lib/lean/(WeightedChains/.*)[.]olean$#\1.lean#p' \
      | sort -u); then
  echo "A project module is missing from the WeightedChains root import closure." >&2
  exit 1
fi

lake env lean -DwarningAsError=true scripts/AxiomAudit.lean
