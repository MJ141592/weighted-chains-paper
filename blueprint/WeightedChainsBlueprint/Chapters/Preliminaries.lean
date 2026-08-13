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

#doc (Manual) "Preliminaries" =>

:::group "paper-preliminaries"
The discrete cube, its layers, and the chains used by the weighted-cover argument.
:::

:::definition "wc:def:chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain, WeightedChains.Chain.length") (autoDeps := true) (tags := "semantic-review-pending, direct, encoding, numbered")
%%%
source := paperSource "Definition 2.1" 184 188
%%%

A chain is a finite ordered sequence of cube vertices that is monotone in the
coordinatewise order. Its length is the number of vertices.

*Semantic review:* pending. *Correspondence:* direct and encoding. Lean stores
the ordered vertices as a nonempty `Fin`-indexed sequence.
:::

:::definition "wc:def:chain-width" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.width, WeightedChains.Cube.hammingDistance") (autoDeps := true) (tags := "semantic-review-pending, direct, encoding, numbered")
%%%
source := paperSource "Definition 2.2" 190 192
%%%

The width of a chain is the number of coordinates on which its first and last
vertices differ.

*Semantic review:* pending. *Correspondence:* direct and encoding. Lean uses
endpoint Hamming distance for the coordinate count.
:::

:::definition "wc:def:saturated-chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Saturated") (autoDeps := true) (tags := "semantic-review-pending, direct, encoding, numbered")
%%%
source := paperSource "Definition 2.3" 202 205
%%%

A chain is saturated when every consecutive step raises the rank by exactly
one.

*Semantic review:* pending. *Correspondence:* direct and encoding. Lean states
the equivalent rank-one condition at each adjacent step.
:::

:::definition "wc:def:symmetric-chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Symmetric, WeightedChains.Chain.symmetric_iff_endpoint") (autoDeps := true) (tags := "semantic-review-pending, direct, encoding, numbered")
%%%
source := paperSource "Definition 2.4" 207 209
%%%

A chain is symmetric when paired vertices from opposite ends have ranks
summing to $`nd`$. For saturated chains this is equivalent to the corresponding
endpoint equation.

*Semantic review:* pending. *Correspondence:* direct and encoding. Lean's
reverse finite-index convention implements the pairing from opposite ends.
:::

:::definition "wc:def:layer" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.rank, WeightedChains.Cube.layer") (autoDeps := true) (tags := "semantic-review-pending, direct, numbered")
%%%
source := paperSource "Definition 2.5" 217 222
%%%

The $`r`th layer is the set of cube vertices of rank $`r`.

*Semantic review:* pending. *Correspondence:* direct. Lean extends the bounded
paper definition harmlessly by making out-of-range natural-number layers empty.
:::

:::definition "wc:def:good-chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Good") (autoDeps := true) (tags := "semantic-review-pending, direct, encoding, numbered")
%%%
source := paperSource "Definition 2.6" 228 231
%%%

A good chain is saturated, has width at most $`k`, and is either symmetric or
has length exactly $`dk+1`.

*Semantic review:* pending. *Correspondence:* direct and encoding. The chain
structure and length convention are the finite encodings reviewed here.
:::

:::definition "wc:def:chain-start" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.StartsAtFirst, WeightedChains.Chain.StartsAtLast") (autoDeps := true) (tags := "semantic-review-pending, corrected, encoding, numbered")
%%%
source := paperSource "Definition 2.7" 246 254
%%%

A chain starts at an endpoint when that endpoint is at least as far from the
middle of the cube as the other endpoint.

*Semantic review:* pending. *Correspondence:* corrected and encoding. The
displayed inequalities in the manuscript are reversed relative to its
explanatory sentence and later arguments; Lean's two orientation predicates
follow the intended farther-endpoint condition.
:::

:::definition "wc:def:cube-sides" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.lowerSide, WeightedChains.Cube.upperSide") (autoDeps := true) (tags := "semantic-review-pending, direct, numbered")
%%%
source := paperSource "Definition 2.8" 258 260
%%%

The lower and upper sides consist respectively of vertices whose doubled rank
is at most or at least $`nd`.

*Semantic review:* pending. *Correspondence:* direct; doubled inequalities
avoid division and express the paper's half-rank boundaries exactly.
:::

:::definition "wc:def:inner-outer-layers" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.InnerLayer, WeightedChains.Cube.OuterLayer") (autoDeps := true) (tags := "semantic-review-pending, corrected, encoding, numbered")
%%%
source := paperSource "Definition 2.9" 263 265
%%%

A layer is inner when the saturated symmetric chain from rank $`r` to its
zero-based complementary rank $`nd-r` has length less than $`dk+1`; it is outer
otherwise.

*Semantic review:* pending. *Correspondence:* corrected and encoding. The
manuscript's $`nd+1-r` complementary index is off by one; the Lean predicate
uses the equivalent doubled-rank distance condition for $`nd-r`.
:::

:::definition "wc:def:type" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.typeOf, WeightedChains.Cube.sum_typeOf, WeightedChains.Ternary.TypeCounts, WeightedChains.Ternary.TypeCounts.ofVertex") (autoDeps := true) (tags := "semantic-review-pending, corrected, encoding, numbered")
%%%
source := paperSource "Definition 2.10" 277 283
%%%

The type of a point records, for each symbol $`j \in \{0,\ldots,d\}`$, the
number of coordinates equal to $`j`; these $`d+1` counts sum to $`n`.

*Semantic review:* pending. *Correspondence:* corrected and encoding. The
manuscript transposes the alphabet and dimension indices; Lean uses the intended
$`d+1`-component count function summing to $`n` and also provides a specialized
ternary structure.
:::

:::lemma_ "wc:lem:good-chain-residue-intersection" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Good.card_lowerResidueFinset_inter_vertices, WeightedChains.Chain.Good.card_upperResidueFinset_inter_vertices") (autoDeps := true) (tags := "semantic-review-pending, direct, unnumbered")
%%%
source := paperSource "Good-chain residue intersection" 233 244
%%%

Every good chain meets each of the lower and upper middle rank-residue families
in exactly one vertex.

*Semantic review:* pending. *Correspondence:* direct.
:::

:::proof "wc:lem:good-chain-residue-intersection"
Saturation supplies every rank in the relevant interval. Symmetry or full
length supplies existence of the required congruence class, while the width
bound gives uniqueness.
:::
