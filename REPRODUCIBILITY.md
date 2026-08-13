# Reproducing the Lean artifact

This document describes how to check the exact formal artifact associated with
*A generalisation of Sperner's theorem using weighted chain decomposition*.
The authoritative dependency versions are the checked-in `lean-toolchain` and
`lake-manifest.json`; do not replace them with newer versions and do not run
`lake update` while reproducing a release.

The build establishes that Lean accepts the formal declarations and that the
automated completeness and axiom policy passes. It does not, by itself,
establish that an informal paper statement and a Lean statement express the
same proposition. That correspondence is described in `FORMALIZATION.md` and
signed off item-by-item in `SEMANTIC_REVIEW.md`.

## Requirements

A clean build requires:

- a 64-bit Linux or macOS machine;
- Git, Bash, `ripgrep`, and Python 3;
- `elan`, the Lean version manager; and
- network access on the first run to obtain the pinned Lean toolchain and Lake
  dependencies.

CI uses the fixed `ubuntu-24.04` runner image. No TeX installation is needed to
check the Lean code or build the HTML blueprint. Precompiled mathlib files are
optional: they reduce the build time but do not change the pinned source
revision.

## Clean verification

Start from a fresh checkout of the release tag named by the paper or archive.
Until the canonical public URL and first release tag have been chosen, the
angle-bracketed values below are intentionally placeholders.

```sh
git clone <canonical-public-repository-url> weighted-chains-artifact
cd weighted-chains-artifact
git switch --detach <release-tag>
```

Record the exact source revision and resolved formal dependencies:

```sh
git rev-parse HEAD
cat lean-toolchain
lake env lean --version
lake exe cache get
git -C .lake/packages/mathlib rev-parse HEAD
```

The final command must print the `rev` of the `mathlib` package in
`lake-manifest.json`. Then run the publication checks in this order:

```sh
lake build
./scripts/audit.sh
./blueprint/scripts/build-site.sh
test -f blueprint/_out/site/html-multi/index.html
```

Every command must exit successfully. `scripts/audit.sh` deliberately repeats
some build work: it compiles every source module under `WeightedChains`, even if
a future draft is accidentally omitted from the root import, and then compiles
the root library and the kernel-dependency audit.

The generated site is at:

```text
blueprint/_out/site/html-multi/index.html
```

It is generated output and is not part of the source of record. Publication
releases package it separately from the source archive.

## What the audit checks

The automated policy has three layers:

1. The source scan rejects `sorry`, `admit`, project `axiom` or `constant`
   declarations, `opaque`, `unsafe`, `partial`, and the project's prohibited
   decision-procedure shortcuts.
2. Each formalisation module and the root `WeightedChains` library compile with
   warnings treated as errors, and every project source module is reachable
   from that root import.
3. `scripts/AxiomAudit.lean` asks Lean for the transitive axiom dependencies of
   the project theorems. It permits only Lean's standard `propext`,
   `Classical.choice`, and `Quot.sound`, inherited through mathlib, and rejects
   project declarations that introduce axioms or opaque constants.

The proof checker is the Lean kernel supplied by `lean-toolchain`. The formal
artifact depends on mathlib and its transitive packages at the exact Git
revisions in `lake-manifest.json`. The optional mathlib cache is an upstream
build cache for those pinned inputs; omit `lake exe cache get` if a full local
dependency build is required.

## Continuous integration and Pages safety

`.github/workflows/lean.yml` performs the root build and audit on pushes and
pull requests. `.github/workflows/blueprint-pages.yml` repeats those checks and
then builds and validates the blueprint. Both workflows pin their operating
system and third-party actions to exact revisions.

The blueprint is a nested Lake project. Its `lakefile.lean` pins the exact
Verso Blueprint Git revision, and its `lean-toolchain` pins the same Lean
release as the root project. `blueprint/scripts/build-site.sh` validates the
resolved nested manifest before generating the site; an unexpected dependency
resolution is therefore a build failure rather than a silent upgrade.

The blueprint workflow always uploads the validated site as a workflow
artifact, but it deploys nothing by default. Its deployment job runs only for
`main`, outside pull requests, when the repository variable `ENABLE_PAGES` is
set to the exact string `true`. Consequently the workflow is safe while the
repository is private or GitHub Pages is disabled.

## Frozen release evidence

For a semantic-version tag, `.github/workflows/release-artifact.yml` reruns the
complete verification and creates:

- a deterministic Git archive of the tracked source at the tagged commit;
- a generated Blueprint archive with sorted entries and normalized tar metadata;
- `provenance.json`, containing the tag, commit, Lean toolchain, mathlib
  revision, workflow run, and archive digests; and
- `SHA256SUMS` for independent integrity checking.

The workflow only uploads a temporary workflow artifact. It intentionally does
not create a tag, publish a GitHub release, change repository visibility, or
deposit anything externally. The human release procedure is in
`RELEASING.md`.
