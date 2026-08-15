#!/usr/bin/env bash
set -euo pipefail

blueprint_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$blueprint_root"

command -v lake >/dev/null
command -v python3 >/dev/null
command -v git >/dev/null

repository_root="$(git rev-parse --show-toplevel)"
dirty_sources="$(git -C "$repository_root" status --porcelain --untracked-files=normal -- . ':(exclude).conductor')"
if [[ -n "$dirty_sources" ]]; then
  if [[ "${CI:-}" == "true" ]]; then
    echo "Refusing to generate publication links from a dirty CI checkout." >&2
    exit 1
  fi
  echo "Warning: local source links target HEAD; commit changes before publishing this build." >&2
fi

if malformed_math="$(grep -RFn --include='*.lean' '`$' \
  "$blueprint_root/WeightedChainsBlueprint/Chapters")"; then
  printf '%s\n' "$malformed_math" >&2
  echo 'Malformed Verso inline math: use $`…`, not $`…`$.' >&2
  exit 1
fi

lake exe cache get
lake env lake build WeightedChainsBlueprint
lake env lake exe vbp build

site_dir="$blueprint_root/_out/site/html-multi"
manifest="$site_dir/-verso-data/blueprint-manifest.json"
source_commit="$(git rev-parse HEAD)"
test -d "$site_dir"
test -f "$manifest"

lake env lake exe vbp check --site "$site_dir"

python3 "$blueprint_root/scripts/generate-redirects.py" \
  --manifest "$manifest" \
  --links "$blueprint_root/links.json" \
  --semantic-review "$repository_root/SEMANTIC_REVIEW.md" \
  --site "$site_dir" \
  --expected-commit "$source_commit"

if [[ "${CI:-}" == "true" ]] && \
    [[ -n "$(git -C "$repository_root" status --porcelain --untracked-files=normal -- . ':(exclude).conductor')" ]]; then
  echo "The publication build changed source-controlled inputs." >&2
  exit 1
fi

echo "Blueprint site built at $site_dir"
