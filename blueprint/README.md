# Weighted chains blueprint

This directory links the LaTeX manuscript in `../main.tex` to its Lean
formalisation. It uses Verso Blueprint to present, for every definition, lemma
and theorem of the paper, the associated Lean declarations with their elaborated
signatures, the dependency graph, the manuscript lines where the statement
appears, and commit-pinned links to the Lean source.

## Build

Install the Lean toolchain manager `elan`, then run from the repository root:

```sh
./blueprint/scripts/build-site.sh
```

The multi-page site is written to `blueprint/_out/site/html-multi`. The build
also validates every entry in `links.json` against Verso's preview manifest and
generates stable `/theorems/<slug>/` routes. Validation covers exact paper
numbering and source spans, exact presence, uniqueness, and placement of every
PDF badge, informal-block targets, and commit-pinned GitHub line links for every
associated Lean declaration. Numbered LaTeX environments that have no blueprint
entry are reported as warnings. A local build from a dirty worktree is useful
for previewing, but its source URLs target `HEAD`; only publish a clean
committed CI or release build.

## How the paper and the blueprint are tied together

Nothing in the blueprint records line numbers of `../main.tex`, so ordinary
edits to the manuscript never require touching the blueprint. Each entry of
`links.json` is located in the paper by its label at build time:

- A numbered statement (`"numbered": true`) is the `theorem`, `definition`,
  `proposition` or `lemma` environment containing `\label{<label>}`.
- Any other statement is the text between the comment lines
  `% blueprint-begin: <label>` and `% blueprint-end: <label>`.

`scripts/paper_sources.py` (run automatically by `build-site.sh`) computes the
resulting line ranges and writes the Git-ignored module
`WeightedChainsBlueprint/PaperSources.lean`, which `Common.lean` consults in
`paperSource`. Run it once by hand before opening the blueprint in an editor,
or with `--check` to verify that `main.tex` and `links.json` agree. The chapter
files refer to paper statements only by label, for example
`source := paperSource "wc:lem:boolean-inner-weight" "Lemma 4.1"`.

To link a new paper statement: give its environment a `\label{wc:...}` (or wrap
the relevant text in `% blueprint-begin`/`% blueprint-end` markers), place a
`\leanblueprint{<slug>}` badge inside that range, add an entry to `links.json`,
and add a node with the same label to the relevant chapter under
`WeightedChainsBlueprint/Chapters/`. The badge macro itself is defined in the
preamble of `../main.tex`; put `\leanlinksfalse` after it for an unlinked
journal build.
