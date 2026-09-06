import Verso
import VersoManual
import VersoBlueprint
import WeightedChains
import WeightedChainsBlueprint.Common

open Verso.Genre
open Verso.Genre.Manual
open Informal
open WeightedChainsBlueprint

set_option verso.blueprint.autoDeps true

#doc (Manual) "Main result" =>

:::source_document "paper-source"
%%%
title := "A generalisation of Sperner's theorem using weighted chain decomposition"
kind := .text
%%%
:::

:::group "paper-introduction"
Definitions and results stated in the introduction of the paper.
:::

:::theorem "wc:thm:main-theorem" (parent := "paper-introduction") (lean := "WeightedChains.main_cardinality_and_uniqueness, WeightedChains.Cube.lowerResidueFinset_eq_upperResidueFinset_of_even") (autoDeps := true) (uses := "wc:def:k-separated") (priority := "high")
%%%
source := paperSource "wc:thm:main-theorem" "Theorem 1.1"
%%%

For $`1 < k \leq n` and $`d \in \{1,2\}`, every $`k`-separated family in
$`\{0,\ldots,d\}^n` has cardinality at most the lower middle rank-residue
family. Equality holds exactly for the lower or upper middle rank-residue
family; when $`nd` is even these two families agree.

The Lean theorem represents a family as a finite set and packages the
cardinality bound and the equality classification together.
:::

:::proof "wc:thm:main-theorem"
The declaration combines the independently constructed Boolean and ternary
weighted covers and their equality classifications. Its second associated
declaration proves the stated even-parity identification of the two extremal
families.
:::

:::definition "wc:def:k-separated" (parent := "paper-introduction") (lean := "WeightedChains.Cube.KSeparated") (autoDeps := true)
%%%
source := paperSource "wc:def:k-separated" "Introduction, definition of k-separation"
%%%

A family in the discrete cube is $`k`-separated when no two *distinct*
comparable members differ in at most $`k` coordinates.
:::

:::lemma_ "wc:lem:residue-families-separated" (parent := "paper-introduction") (lean := "WeightedChains.Cube.lowerResidueFamily_kSeparated, WeightedChains.Cube.upperResidueFamily_kSeparated") (autoDeps := true)
%%%
source := paperSource "wc:lem:residue-families-separated" "Remark after Theorem 1.1"
%%%

The lower and upper middle rank-residue families are $`k`-separated for every
alphabet parameter $`d`.
:::

:::proof "wc:lem:residue-families-separated"
For distinct comparable points, the positive rank difference is at most
$`dk` when at most $`k` coordinates change, so it cannot vanish modulo
$`dk+1`.
:::
