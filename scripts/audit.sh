#!/usr/bin/env bash
set -euo pipefail

project_sources() {
  find WeightedChains -type f -name '*.lean' -print | LC_ALL=C sort
}

lean_sources=(WeightedChains.lean)
while IFS= read -r source; do
  lean_sources+=("$source")
done < <(project_sources)

scan_status=0
grep -EnH \
  '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|public|noncomputable|local|scoped)[[:space:]]+)*(axiom|opaque|constants?|unsafe|partial)([^[:alnum:]_]|$)|(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|[[:alnum:]_]*decide[[:alnum:]_]*' \
  "${lean_sources[@]}" || scan_status=$?
if ((scan_status == 0)); then
  echo "Forbidden proof escape hatch found." >&2
  exit 1
elif ((scan_status != 1)); then
  echo "Unable to scan Lean sources for forbidden proof escape hatches." >&2
  exit "$scan_status"
fi

# The root module intentionally follows paper order, but work-in-progress
# modules must not escape checking merely because they have not yet been added
# to that import tree.
while IFS= read -r source; do
  module="${source%.lean}"
  module="${module//\//.}"
  lake build "$module"
done < <(project_sources)

lake build

# The exhaustive kernel audit below can only see modules reachable from the
# root import. Fail if a source file compiles in isolation but is omitted from
# that transitive import closure.
if ! diff -u \
    <(project_sources) \
    <(lake env lean --deps WeightedChains.lean \
      | sed -nE 's#^.*/[.]lake/build/lib/lean/(WeightedChains/.*)[.]olean$#\1.lean#p' \
      | sort -u); then
  echo "A project module is missing from the WeightedChains root import closure." >&2
  exit 1
fi

lake env lean -DwarningAsError=true scripts/AxiomAudit.lean
