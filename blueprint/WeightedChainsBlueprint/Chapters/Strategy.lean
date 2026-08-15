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

#doc (Manual) "Weighted-chain strategy" =>

:::group "paper-strategy"
The weighted-cover reduction and the concrete Boolean and ternary witnesses.
:::

:::proposition "wc:prop:good-chain-weighting" (parent := "paper-strategy") (lean := "WeightedChains.DOne.BooleanChain.indexedWeight, WeightedChains.DOne.BooleanChain.indexedWeight_pos, WeightedChains.DOne.BooleanChain.indexedInducedWeight_eq_one, WeightedChains.Ternary.BasicChain.indexedWeight, WeightedChains.Ternary.BasicChain.indexedWeight_nonneg, WeightedChains.Ternary.BasicChain.indexedInducedWeight_eq_one") (autoDeps := true) (tags := "semantic-review-pending, corrected, factored, encoding, numbered")
%%%
source := paperSource "Proposition 3.1" 334 353
%%%

For $`1<k\leq n` and $`d\in\{1,2\}`, the formalisation constructs a
nonnegative weighted family of good chains whose induced weight at every cube
vertex is one, together with the positivity required for the equality case.

*Semantic review:* pending. *Correspondence:* corrected, factored, and encoding.
The manuscript says “any $`n,k`”, while the positivity and uniqueness claim
needs $`1<k\leq n`. Lean packages the finite Boolean and ternary constructions
separately; the associated declarations are their concrete weight,
positivity/nonnegativity, and unit-induced-weight witnesses.
:::

:::proof "wc:prop:good-chain-weighting"
The Boolean construction distributes an explicit positive layer-start weight
over every good chain. The ternary construction distributes start-type totals
over basic good chains, with zero extension to the remaining good chains.
:::

:::lemma_ "wc:lem:weighted-cover-implies-main" (parent := "paper-strategy") (lean := "WeightedChains.Chain.kSeparated_card_le_lowerResidueFinset, WeightedChains.Chain.kSeparated_inter_vertices_card_eq_one_of_card_eq_lower, WeightedChains.UniquenessPropagation.finset_eq_of_positive_weight_outward_induction, WeightedChains.UniquenessPropagation.finset_eq_of_active_exact_one_outward_induction_except") (autoDeps := true) (tags := "semantic-review-pending, corrected, factored, encoding, numbered")
%%%
source := paperSource "Lemma 3.2" 367 374
%%%

A nonnegative unit weighted cover by good chains bounds every $`k`-separated
family by the lower rank-residue family. Under the stated positivity witnesses,
equality forces one point on each active chain and then forces one of the two
middle rank-residue families.

*Semantic review:* pending. *Correspondence:* corrected, factored, and encoding.
Lean separates finite double counting, equality on positive chains, and outward
uniqueness; its last step uses well-founded distance from the middle rather than
the manuscript's conflated absolute-layer index. The ternary theorem records
the exceptional middle point explicitly.
:::

:::proof "wc:lem:weighted-cover-implies-main"
Sum the unit induced weights over the candidate and exchange the finite sums.
Every good chain contributes at most one point. At equality each positive chain
contributes exactly one, after which the middle-layer choice propagates outward.
:::
