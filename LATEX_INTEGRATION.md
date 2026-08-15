# LaTeX integration

The 18 numbered mathematical environments in `main.tex` link to their stable
blueprint pages. The integration changes only link metadata and canonical
labels; it does not change mathematical prose or formulas.

The canonical labels and slugs are coordinated with `SEMANTIC_REVIEW.md`.
Existing labels are aliases: keep them alongside the new canonical labels so
existing `\ref` uses and external links continue to work.

## Preamble pattern

`main.tex` loads `xcolor`, `hyperref`, and the shared link helper after setting
the published blueprint origin. Do not put a trailing slash in
`\leanblueprintbase`.

```tex
\newcommand{\leanblueprintbase}{https://mj141592.github.io/weighted-chains-paper}
\input{blueprint/latex/lean-links.tex}
```

The helper enables links by default. Add `\leanlinksfalse` after the input for
a journal build that must suppress external theorem badges.

The URL contract is `/theorems/<slug>/`; it must remain stable even if the
underlying Lean declaration moves to another file. The theorem page, rather
than the PDF, should carry the versioned Git commit, declaration source link,
kernel/audit result, and semantic-review state.

Do not change the badge to `[Lean checked]`, `[Lean verified]`, or a check mark
until the corresponding row in `SEMANTIC_REVIEW.md` has a human reviewer,
review date, reviewed commit, and positive sign-off. Kernel checking alone is
not semantic correspondence review.

## Environment insertion pattern

Each canonical label appears immediately after `\begin{...}`. Existing labels
remain as aliases. Each badge appears immediately before the matching
`\end{...}` so the mathematical prose itself remains unchanged.

For an environment with an existing label:

```tex
\begin{theorem}
\label{wc:thm:main-theorem}
\label{the_main_theorem} % retained alias
% existing theorem text, unchanged
\leanblueprint{main-theorem}
\end{theorem}
```

For an environment without an existing label:

```tex
\begin{definition}[Chain]
\label{wc:def:chain}
% existing definition text, unchanged
\leanblueprint{chain}
\end{definition}
```

The canonical ID is a LaTeX label as well as the blueprint identity. The
visible link uses only its slug because all theorem pages share the same stable
route prefix.

## Exact insertion map

The source ranges below include the canonical labels and link badges. Later
LaTeX edits may shift them, so keep the Blueprint metadata and semantic-review
ledger synchronized with `main.tex`.

| # | Current environment | Current source | Canonical label to add | Existing label to retain | Badge to add before `\end` |
|---:|---|---|---|---|---|
| 1 | Theorem 1.1 | `main.tex:112-130` | `\label{wc:thm:main-theorem}` | `\label{the_main_theorem}` | `\leanblueprint{main-theorem}` |
| 2 | Definition 2.1 (Chain) | `main.tex:189-195` | `\label{wc:def:chain}` | — | `\leanblueprint{chain}` |
| 3 | Definition 2.2 (Chain width) | `main.tex:197-201` | `\label{wc:def:chain-width}` | — | `\leanblueprint{chain-width}` |
| 4 | Definition 2.3 (Saturated chain) | `main.tex:211-216` | `\label{wc:def:saturated-chain}` | `\label{saturated_definition}` | `\leanblueprint{saturated-chain}` |
| 5 | Definition 2.4 (Symmetric chain) | `main.tex:218-222` | `\label{wc:def:symmetric-chain}` | — | `\leanblueprint{symmetric-chain}` |
| 6 | Definition 2.5 (Layer) | `main.tex:230-237` | `\label{wc:def:layer}` | — | `\leanblueprint{layer}` |
| 7 | Definition 2.6 (Good chain) | `main.tex:243-248` | `\label{wc:def:good-chain}` | `\label{good_chain_definition}` | `\leanblueprint{good-chain}` |
| 8 | Definition 2.7 (Chain starting at an endpoint) | `main.tex:263-273` | `\label{wc:def:chain-start}` | — | `\leanblueprint{chain-start}` |
| 9 | Definition 2.8 (Cube sides) | `main.tex:277-281` | `\label{wc:def:cube-sides}` | — | `\leanblueprint{cube-sides}` |
| 10 | Definition 2.9 (Inner/outer layers) | `main.tex:284-288` | `\label{wc:def:inner-outer-layers}` | — | `\leanblueprint{inner-outer-layers}` |
| 11 | Definition 2.10 (Type) | `main.tex:300-308` | `\label{wc:def:type}` | — | `\leanblueprint{type}` |
| 12 | Proposition 3.1 | `main.tex:334-353` | `\label{wc:prop:good-chain-weighting}` | `\label{the_weights_assigning_proposition}` | `\leanblueprint{good-chain-weighting}` |
| 13 | Lemma 3.2 | `main.tex:367-374` | `\label{wc:lem:weighted-cover-implies-main}` | `\label{weights_imply_theorem_lemma}` | `\leanblueprint{weighted-cover-implies-main}` |
| 14 | Lemma 4.1 | `main.tex:519-526` | `\label{wc:lem:boolean-inner-weight}` | — | `\leanblueprint{boolean-inner-weight}` |
| 15 | Definition 5.1 (Basic chain) | `main.tex:609-613` | `\label{wc:def:basic-chain}` | — | `\leanblueprint{basic-chain}` |
| 16 | Lemma 5.2 | `main.tex:666-677` | `\label{wc:lem:basic-chains-suffice}` | `\label{positive_basic_enough_lemma}` | `\leanblueprint{basic-chains-suffice}` |
| 17 | Lemma 5.3 | `main.tex:764-768` | `\label{wc:lem:ternary-auxiliary-positive}` | — | `\leanblueprint{ternary-auxiliary-positive}` |
| 18 | Lemma 5.4 | `main.tex:824-831` | `\label{wc:lem:ternary-inner-weight}` | — | `\leanblueprint{ternary-inner-weight}` |

## Application and release checklist

- [x] Publish the blueprint at the configured HTTPS base URL and confirm all 18
      `/theorems/<slug>/` routes resolve without redirects to branch-relative
      source locations.
- [x] Add canonical labels without removing or renaming any existing labels.
- [x] Add exactly one `\leanblueprint{slug}` badge to each of the 18 numbered
      environments in the table.
- [x] Keep the badge wording neutral while semantic review is pending.
- [x] Build once with `\leanlinkstrue` and inspect every badge in the PDF.
- [x] Validate all 18 link annotations in the built PDF, not only in the HTML
      source.
- [x] Build once with `\leanlinksfalse` to ensure the journal-suppressed form
      has no broken spacing or blank paragraphs.
- [x] Verify existing `\ref{...}` calls still resolve through the retained
      aliases and new references resolve through canonical labels.
- [ ] Record the exact paper/artifact commit on every theorem page.
- [ ] Complete the semantic-review ledger before changing any badge to wording
      that implies reviewed equivalence.
- [ ] Archive the linked commit/tag used for the arXiv release so the theorem
      pages can continue to expose a frozen source target as well as the living
      repository.
