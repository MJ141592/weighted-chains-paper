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

:::definition "wc:def:chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain, WeightedChains.Chain.length") (autoDeps := true)
%%%
source := paperSource "wc:def:chain" "Definition 2.1"
%%%

A chain is a finite ordered sequence of cube vertices that is monotone in the
coordinatewise order. Its length is the number of vertices.

Lean stores the ordered vertices as a nonempty `Fin`-indexed sequence.
:::

:::definition "wc:def:chain-width" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.width, WeightedChains.Cube.hammingDistance") (autoDeps := true)
%%%
source := paperSource "wc:def:chain-width" "Definition 2.2"
%%%

The width of a chain is the number of coordinates on which its first and last
vertices differ.

Lean uses the Hamming distance between the endpoints for the coordinate count.
:::

:::definition "wc:def:saturated-chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Saturated") (autoDeps := true)
%%%
source := paperSource "wc:def:saturated-chain" "Definition 2.3"
%%%

A chain is saturated when every consecutive step raises the rank by exactly
one.

Lean states the equivalent rank-one condition at each adjacent step.
:::

:::definition "wc:def:symmetric-chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Symmetric, WeightedChains.Chain.symmetric_iff_endpoint") (autoDeps := true)
%%%
source := paperSource "wc:def:symmetric-chain" "Definition 2.4"
%%%

A chain is symmetric when paired vertices from opposite ends have ranks
summing to $`nd`. For saturated chains this is equivalent to the corresponding
endpoint equation.

Lean's reverse finite-index convention implements the pairing from opposite
ends.
:::

:::definition "wc:def:layer" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.rank, WeightedChains.Cube.layer") (autoDeps := true)
%%%
source := paperSource "wc:def:layer" "Definition 2.5"
%%%

The $`r`th layer is the set of cube vertices of rank $`r`.

Lean extends the definition by making out-of-range natural-number layers
empty.
:::

:::definition "wc:def:good-chain" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Good") (autoDeps := true)
%%%
source := paperSource "wc:def:good-chain" "Definition 2.6"
%%%

A good chain is saturated, has width at most $`k`, and is either symmetric or
has length exactly $`dk+1`.
:::

:::definition "wc:def:chain-start" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.StartsAtFirst, WeightedChains.Chain.StartsAtLast") (autoDeps := true)
%%%
source := paperSource "wc:def:chain-start" "Definition 2.7"
%%%

A chain starts at an endpoint when that endpoint is at least as far from the
middle of the cube as the other endpoint.

Lean provides one predicate for each orientation of the chain.
:::

:::definition "wc:def:cube-sides" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.lowerSide, WeightedChains.Cube.upperSide") (autoDeps := true)
%%%
source := paperSource "wc:def:cube-sides" "Definition 2.8"
%%%

The lower and upper sides consist respectively of vertices whose doubled rank
is at most or at least $`nd`.

Doubled inequalities avoid division and express the half-rank boundaries
exactly.
:::

:::definition "wc:def:inner-outer-layers" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.InnerLayer, WeightedChains.Cube.OuterLayer") (autoDeps := true)
%%%
source := paperSource "wc:def:inner-outer-layers" "Definition 2.9"
%%%

A layer is inner when the saturated symmetric chain from rank $`r` to its
zero-based complementary rank $`nd-r` has length less than $`dk+1`; it is outer
otherwise.

The Lean predicate uses the equivalent doubled-rank distance condition.
:::

:::definition "wc:def:type" (parent := "paper-preliminaries") (lean := "WeightedChains.Cube.typeOf, WeightedChains.Cube.sum_typeOf, WeightedChains.Ternary.TypeCounts, WeightedChains.Ternary.TypeCounts.ofVertex") (autoDeps := true)
%%%
source := paperSource "wc:def:type" "Definition 2.10"
%%%

The type of a point records, for each symbol $`j \in \{0,\ldots,d\}`, the
number of coordinates equal to $`j`; these $`d+1` counts sum to $`n`.

Lean uses the $`d+1`-component count function summing to $`n` and also
provides a specialised ternary structure.
:::

:::lemma_ "wc:lem:good-chain-residue-intersection" (parent := "paper-preliminaries") (lean := "WeightedChains.Chain.Good.card_lowerResidueFinset_inter_vertices, WeightedChains.Chain.Good.card_upperResidueFinset_inter_vertices") (autoDeps := true)
%%%
source := paperSource "wc:lem:good-chain-residue-intersection" "Good-chain residue intersection"
%%%

Every good chain meets each of the lower and upper middle rank-residue families
in exactly one vertex.
:::

:::proof "wc:lem:good-chain-residue-intersection"
Saturation supplies every rank in the relevant interval. Symmetry or full
length supplies existence of the required congruence class, while the width
bound gives uniqueness.
:::
