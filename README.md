# Weighted chains (shared)

LaTeX source exported from the Overleaf project shared by `ijontichy1024@gmail.com`.

This repository also contains a Lean 4 formalisation of *A generalisation of
Sperner's theorem using weighted chain decomposition*. The formalisation is a
standalone downstream project built on mathlib; it is not intended for direct
inclusion in mathlib.

## Lean formalisation

Install Lean through `elan`, then run:

```sh
lake exe cache get
lake build
./scripts/audit.sh
```

The project pins the exact mathlib dependency graph in `lake-manifest.json` and
uses mathlib's matching toolchain from `lean-toolchain`. Compiler warnings are
errors. The audit rejects `sorry`, `admit`, and project declarations introduced
with `axiom`, `constant`, `opaque`, `unsafe`, or `partial`; it also compiles every source
module so an unimported draft cannot bypass CI.  Every imported theorem in the
project namespace is additionally checked for nonstandard axiom dependencies.

The source is arranged in the order of the paper:

- `Preliminaries`, `GoodChainResidues`, and `ResidueSymmetry`: the cube,
  separation, good chains, their unique distinguished residues, and reflection;
- `WeightedStrategy`, `WeightedUniqueness`, `UniquenessPropagation`, and
  `MainBound`: weighted double-counting and the equality/uniqueness machinery
  from Lemma 3.2;
- `DOne*`: the Section 4 recurrence and positivity proof, finite Boolean-chain
  model, layer incidence, reflection, the concrete positive weighted cover,
  and the resulting `d = 1` extremal cardinality and equality-classification
  theorems;
- `DTwo*`: ternary types, trinomial coefficients and Pascal recurrence,
  type-orbit cardinalities, concrete/reflected basic chains, metachain
  uniformity, the corrected basic-chain sufficiency geometry, and the
  auxiliary, inner, and pointwise starting-weight recurrences with their
  positivity proofs, the concrete fractional cover, and the complete `d = 2`
  cardinality and uniqueness theorem;
- `MainTheorem`: the paper's unified extremal cardinality and equality
  classification theorem for `d = 1` or `d = 2`;
- `SpernerAppendix`: the appendix's independent weighted symmetric-chain proof,
  including its exact stratum weights and equality classification for every
  dimension `n`;
- `LargeK`: Appendix 2 for arbitrary `d` and `n/2 ≤ k ≤ n`, including an
  internally proved symmetric-chain decomposition rather than assuming the
  cited external existence theorem.

See `FORMALIZATION.md` for the theorem map, design decisions, and current
status.

## LaTeX build

This workspace has TinyTeX installed at:

```sh
../TinyTeX/bin/universal-darwin/latexmk -pdf main.tex
```

From this repository directory, use:

```sh
PATH="../TinyTeX/bin/universal-darwin:$PATH" latexmk -pdf main.tex
```
