# Weighted chains blueprint

This sidecar is the paper-to-Lean correspondence layer for the conventional
LaTeX manuscript in `../main.tex`. It uses Verso Blueprint to expose the paper
statements, exact Lean declarations, generated dependency graph, source-line
provenance, and explicit semantic-review state.

All entries currently say `semantic-review-pending`. A green Lean build checks
the associated formal declarations; it does not by itself assert that they are
faithful translations of the paper. The `direct`, `corrected`, `factored`, and
`encoding` tags make the intended correspondence visible for author review.

## Build

Install the Lean toolchain manager `elan`, then run from the repository root:

```sh
./blueprint/scripts/build-site.sh
```

The multi-page site is written to `blueprint/_out/site/html-multi`. The build
also validates every entry in `links.json` against Verso's preview manifest and
generates stable `/theorems/<slug>/` routes. Validation covers exact paper
numbering and source spans, coverage of every numbered LaTeX environment,
agreement with the semantic-review ledger, informal-block targets, and
commit-pinned GitHub line links for every associated Lean declaration. A local
build from a dirty worktree is useful for previewing, but its source URLs target
`HEAD`; only publish a clean committed CI or release build. The LaTeX helper in
`latex/lean-links.tex` is ready for a linked arXiv build but is intentionally
not included by `main.tex`.
