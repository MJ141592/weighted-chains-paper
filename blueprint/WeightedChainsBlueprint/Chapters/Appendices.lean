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

#doc (Manual) "Appendices" =>

:::group "paper-appendices"
The two appendix results, stated in prose rather than numbered environments.
:::

:::theorem "wc:thm:sperner-appendix" (parent := "paper-appendices") (lean := "WeightedChains.SpernerAppendix.cardinality_and_uniqueness, WeightedChains.SpernerAppendix.SymmetricChain.inducedWeight_eq_one, WeightedChains.SpernerAppendix.SymmetricChain.weight_le_one") (autoDeps := true)
%%%
source := paperSource "wc:thm:sperner-appendix" "Appendix: weighted Sperner theorem"
%%%

For every $`n`, the largest Boolean antichains are precisely the lower and upper
middle layers (which coincide when $`n` is even). The appendix's symmetric-chain
weighting has unit induced weight at every vertex and weights in $`(0,1]` under
the mathematically necessary small-dimension hypotheses.

Lean packages the final bound and the equality classification in one theorem.
:::

:::proof "wc:thm:sperner-appendix"
Exact layer incidence makes the chain weights telescope. Equality forces one
point on every positive middle chain, and connectedness of the two middle
layers gives the two extremal choices.
:::

:::theorem "wc:thm:large-k-appendix" (parent := "paper-appendices") (lean := "WeightedChains.LargeK.lowerResidueFinset_isMaximum, WeightedChains.LargeK.upperResidueFinset_isMaximum, WeightedChains.LargeK.kSeparated_card_le_lowerResidueFinset, WeightedChains.LargeK.deBruijnTengbergenKruyswijk, WeightedChains.LargeK.cuboid_lowerMiddleLayer_isMaximum, WeightedChains.LargeK.cuboid_upperMiddleLayer_isMaximum") (autoDeps := true)
%%%
source := paperSource "wc:thm:large-k-appendix" "Appendix: arbitrary d and large k"
%%%

For arbitrary $`d` in the exact large-separation range $`n\leq 2k`, the lower
and upper rank-residue families are maximum $`k`-separated families. More
generally, both central layers are maximum for cuboids with independently
varying coordinate bounds.

The natural-number condition $`n\leq2k` expresses the paper's $`n/2\leq k`;
Lean proves the de Bruijn--Tengbergen--Kruyswijk symmetric-chain
decomposition constructively for arbitrary products of finite chains.
:::

:::proof "wc:thm:large-k-appendix"
Split the coordinates into two blocks, decompose both smaller cubes into
symmetric chains, and bound each product of two chains by the smaller chain
length. The residue family attains every local bound.
:::
