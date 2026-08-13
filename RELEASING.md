# Publication release procedure

This is a human-operated checklist for freezing a paper-linked Lean artifact.
The release workflow builds reviewable files, but deliberately does not publish
a release or change GitHub, arXiv, journal, or Zenodo state.

## Required decisions before the first release

Do not guess publication metadata. Obtain and record all of the following from
the authors:

- the canonical public GitHub owner, repository name, and final URL;
- the artifact authors and contributors, their ordering, roles, and ORCIDs;
- the paper's authors and preferred citation, including an arXiv identifier or
  journal DOI when one exists;
- the software and paper-source licenses, after checking the target journal's
  policy;
- the public wording and scope of the semantic sign-off; and
- the initial artifact version.

In particular, no `LICENSE` or `CITATION.cff` can be finalized until these user
inputs arrive. The artifact authors need not be identical to the paper authors.
Any licensing split between Lean/software files and paper text or figures must
be explicit rather than inferred.

## One-time repository preparation

Before advertising permanent links:

1. Make the approved canonical repository public.
2. Replace provisional repository descriptions and contact details with the
   approved public metadata.
3. Add the agreed license file or files and a validated `CITATION.cff` with
   author names, ORCIDs, version, canonical URL, and preferred paper citation.
4. Configure `main` protection so the Lean and blueprint workflows are required
   and the designated semantic reviewer must approve correspondence changes.
5. In **Settings → Pages**, choose **GitHub Actions** as the source. Then create
   the repository Actions variable `ENABLE_PAGES` with value `true`. Merely
   enabling Pages is insufficient; the variable is the deliberate deployment
   gate.
6. Enable immutable releases in the repository settings before publishing the
   first final release.

These are external state changes and require explicit author or repository-owner
approval. They are not performed by any workflow in this repository.

## Prepare and verify a candidate

Choose a semantic version such as `v1.0.0`. The example is not a decision about
the actual first version. Ensure any version recorded in Lake, citation, site,
and archival metadata agrees with the chosen tag.

From a clean checkout of the candidate commit, run:

```sh
lake exe cache get
lake build
./scripts/audit.sh
./blueprint/scripts/build-site.sh
test -f blueprint/_out/site/html-multi/index.html
git status --short
```

The commands must succeed and the final status must contain no unexplained
tracked changes. Review all of the following at the exact candidate commit:

- `FORMALIZATION.md`, including every documented departure from the paper;
- the paper-to-Lean correspondence and its semantic-review record;
- `REPRODUCIBILITY.md` from a genuinely fresh checkout;
- the generated blueprint, including representative theorem, dependency, and
  commit-pinned source links; and
- the license and citation metadata approved above.

Merge through the protected `main` branch and wait for both required workflows
to pass. Record the candidate commit SHA.

## Tag and obtain immutable candidate files

Create an annotated tag at the reviewed commit. A signed tag is preferable when
the maintainers have an established signing setup.

```sh
release_tag=v1.0.0
candidate_commit=<reviewed-full-commit-sha>
git tag --annotate "$release_tag" "$candidate_commit" \
  --message "Weighted chains formal artifact $release_tag"
git push origin "refs/tags/$release_tag"
```

Pushing a tag matching `vMAJOR.MINOR.PATCH` starts the **Publication artifact**
workflow. It reruns the Lean build, audit, and blueprint build before creating
the source archive, site archive, provenance, and checksums. It does not create
a GitHub release.

Download the workflow artifact and verify it locally. For example:

```sh
gh run list --workflow release-artifact.yml --branch "$release_tag"
gh run download <run-id> --name "publication-artifacts-$release_tag" --dir release-files
cd release-files
sha256sum --check SHA256SUMS
```

On macOS, where GNU `sha256sum` is not installed by default, use
`shasum -a 256 -c SHA256SUMS` for the final command.

Also inspect `provenance.json` and confirm that its tag, commit, Lean toolchain,
mathlib revision, and workflow URL are the expected values. Rebuilding the
tagged source should follow `REPRODUCIBILITY.md` exactly.

## GitHub release

Create a draft release from the existing tag and attach all four candidate
files: the source archive, blueprint archive, `provenance.json`, and
`SHA256SUMS`. The release notes should state:

- the full source commit;
- the Lean toolchain and mathlib revision;
- the scope of the formalisation and semantic review;
- the exact reproduction command sequence;
- the version-specific archival DOI, if it has already been reserved; and
- any documented differences from the submitted paper.

Inspect the draft and every uploaded digest before publishing it. Once an
immutable release is published, never move its tag or replace its assets. A
correction requires a new semantic version.

## Zenodo and DOI policy

Choose one archival route and avoid duplicate records:

- **Pre-reserved manual deposit:** create a Zenodo software draft, reserve its
  version DOI, add the approved DOI to `CITATION.cff` before tagging, then upload
  the workflow's exact source archive, provenance, and checksums and publish the
  deposit with the GitHub release.
- **GitHub integration:** connect the approved public repository to Zenodo
  before publishing the GitHub release. After Zenodo ingests that release,
  verify its metadata and archive, then record the assigned DOI in the paper
  and in subsequent repository metadata.

Use the **version DOI** in the paper and arXiv record because it identifies the
exact checked artifact. Use the **concept DOI** only for a project-level link
that should resolve to the newest version. For later releases, create a new
version of the existing Zenodo record so the version DOI changes while the
concept DOI remains stable.

The Zenodo record must use the author-approved names, ordering, ORCIDs,
licenses, description, and related paper identifier. Confirm that its archived
file digest matches the released source archive.

## Paper and arXiv hand-off

Provide the paper authors with:

- the release tag and full commit SHA;
- the version-specific DOI;
- the permanent blueprint URL;
- the source archive name and SHA-256 digest; and
- the precise scope and date of semantic review.

The paper should link theorem markers to the stable per-result Blueprint routes,
not to `main` or moving GitHub line numbers. Because the hosted Blueprint is a
living site, the paper must also cite the version DOI and full release commit;
each published page then exposes source links pinned to that commit. The arXiv
submission can include the exact source archive, `SHA256SUMS`, and
`provenance.json` as ancillary files. Updating the manuscript itself remains a
separate author task.

## Final acceptance checklist

- The tag resolves to the reviewed commit and has never moved.
- Root build, audit, and blueprint workflows pass for that commit.
- The downloaded checksums verify.
- The GitHub release is final and immutable.
- The Pages site resolves representative theorem links at stable URLs.
- The release and Zenodo metadata contain the approved authors, ORCIDs,
  licenses, and paper relationship.
- The paper cites the version DOI and names the artifact version.
- The semantic reviewer has signed off on the correspondence for the released
  commit.
