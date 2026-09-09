# Weighted chains

This repository contains the paper source and Lean 4 formalisation of *A
generalisation of Sperner's theorem using weighted chain decomposition*. The
formalisation is a standalone project built on mathlib; it is not intended for
direct inclusion in mathlib.

The publication has three complementary views:

- `main.tex` is the authoritative journal manuscript;
- `blueprint/` builds an interactive, theorem-level paper-to-Lean companion;
- `FORMALIZATION.md` records the detailed declaration map and the places where
  the Lean encoding is phrased differently from the paper.

The Lean kernel verifies the declarations linked by the Blueprint; where the
Lean encoding of a statement differs in form from the paper, the Blueprint
entry and `FORMALIZATION.md` say how.

## Lean formalisation

Install Lean through `elan`, then run:

```sh
lake exe cache get
lake build
./scripts/audit.sh
```

The project pins Lean 4.33.1 and the matching mathlib release, including the
exact transitive dependency graph in `lake-manifest.json`. Compiler warnings
are errors. The audit rejects incomplete or trust-expanding project
declarations, compiles every source module so an unimported draft cannot bypass
CI, requires every source module to belong to the root import closure, and
checks every theorem originating in a project module for nonstandard kernel
dependencies.

The source is arranged in the order of the paper:

- `Preliminaries`, `GoodChainResidues`, and `ResidueSymmetry`: the cube,
  separation, good chains, their unique distinguished residues, and reflection;
- `WeightedStrategy`, `WeightedUniqueness`, `UniquenessPropagation`, and
  `MainBound`: weighted double-counting and the equality/uniqueness machinery
  from Lemma 3.2;
- `DOne/` (umbrella import `WeightedChains.DOne`): the Section 4 recurrence and
  positivity proof, finite Boolean-chain model, layer incidence, reflection,
  the concrete positive weighted cover, and the resulting `d = 1` extremal
  cardinality and equality-classification theorems;
- `DTwo/` (umbrella import `WeightedChains.DTwo`): ternary types, trinomial
  coefficients and Pascal recurrence,
  type-orbit cardinalities, concrete/reflected basic chains, metachain
  uniformity, the corrected basic-chain sufficiency geometry, and the
  auxiliary, inner, and pointwise starting-weight recurrences with their
  positivity proofs, the concrete fractional cover, and the complete `d = 2`
  cardinality and uniqueness theorem;
- `MainTheorem`: the paper's unified extremal cardinality and equality
  classification theorem for `d = 1` or `d = 2`;
- `Asymptotics`: the conclusion's arbitrary-`d` limit theorem for the maximum
  density of a `k`-separated family;
- `Appendices/` (umbrella import `WeightedChains.Appendices`): the independent
  weighted proof of Sperner's theorem and the arbitrary-`d`, `n/2 ≤ k ≤ n`
  result, including the internally proved symmetric-chain decomposition and
  cuboid extension.

See `FORMALIZATION.md` for the full theorem map and design decisions.

## Interactive paper companion

Build the Blueprint and its stable per-result links with:

```sh
./blueprint/scripts/build-site.sh
```

The generated multi-page site is under `blueprint/_out/site/html-multi/`.
Publication links use `/theorems/<slug>/`, a stable redirect layer generated
from Verso's manifest rather than its internal page layout. The PDF link macro
`\leanblueprint` is defined in the preamble of `main.tex`, and the blueprint
finds each linked statement by its `\label` or `% blueprint-begin/end` markers
rather than by line number, so the manuscript can be edited freely (see
`blueprint/README.md`).

GitHub Pages deployment is intentionally gated by the repository variable
`ENABLE_PAGES=true`; the site can therefore be checked in CI before a canonical
public repository and Pages deployment are approved.

## LaTeX build

With a current TeX Live installation and `latexmk` on `PATH`, run:

```sh
latexmk -pdf main.tex
```

The Blueprint does not rewrite or preprocess the manuscript. `main.tex` is
self-contained: the `[Lean formalisation]` badges are produced by the
`\leanblueprint` macro in its preamble, and a journal build without them only
needs `\leanlinksfalse` after that macro's definition.
