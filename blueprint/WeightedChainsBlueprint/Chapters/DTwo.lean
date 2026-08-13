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

#doc (Manual) "The ternary construction" =>

:::group "paper-ternary"
Basic ternary chains and their starting weights.
:::

:::definition "wc:def:basic-chain" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.BasicChain, WeightedChains.Ternary.BasicChain.toChain, WeightedChains.Ternary.BasicChain.toChain_saturated, WeightedChains.Ternary.BasicChain.toChain_length, WeightedChains.Ternary.BasicChain.toChain_width") (autoDeps := true) (tags := "semantic-review-pending, corrected, factored, encoding, numbered")
%%%
source := paperSource "Definition 5.1" 578 580
%%%

A ternary basic chain changes one coordinate completely from zero to two before
moving to the next coordinate. The constructive Lean structure records its
start and ordered changed coordinates and produces the corresponding saturated
generic chain.

*Semantic review:* pending. *Correspondence:* corrected, factored, and encoding.
The manuscript's final word “good” should be “basic”; Lean gives a constructive
$`d=2` encoding rather than an iff characterization of arbitrary chains.
:::

:::lemma_ "wc:lem:basic-chains-suffice" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.BasicChain.exists_singleton_good_of_rank_eq_dimension, WeightedChains.Ternary.BasicChain.exists_good_with_endpoint_avoiding_middle_of_lowerResidue, WeightedChains.Ternary.BasicChain.exists_closer_lowerResidue") (autoDeps := true) (tags := "semantic-review-pending, corrected, factored, encoding, numbered")
%%%
source := paperSource "Lemma 5.2" 633 642
%%%

Middle-layer singleton chains are basic. Every noncentral reference-family
vertex has a suitable basic good chain with it as an endpoint, and every vertex
outside the reference family has a basic good chain through it and a strictly
closer noncentral reference-family vertex.

*Semantic review:* pending. *Correspondence:* corrected, factored, and encoding.
The manuscript uses an undefined $`A` where $`A_1` is intended. Lean factors
the finite witness construction into three declarations and treats the
exceptional type $`(1,n-1,0)` by a containing-chain detour instead of the false
stronger assertion that such a chain always starts there.
:::

:::proof "wc:lem:basic-chains-suffice"
The construction splits by lower/upper symmetry, outer/inner type, and the
exceptional near-middle type. The three associated theorems expose the exact
witnesses needed by the weighted uniqueness argument.
:::

:::lemma_ "wc:lem:ternary-auxiliary-positive" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.auxiliaryWeight_pos_of_valid_lower, WeightedChains.Ternary.auxiliaryWeight_zero_zero") (autoDeps := true) (tags := "semantic-review-pending, corrected, numbered")
%%%
source := paperSource "Lemma 5.3" 729 731
%%%

For a valid lower ternary type other than $`(a,c)=(0,0)`, the auxiliary weight
$`U_n(a,c)` is positive. At $`(0,0)` it is zero.

*Semantic review:* pending. *Correspondence:* corrected. The printed lemma
includes $`(0,0)` and is therefore false; Lean proves positivity with this
necessary exception and separately proves the zero value.
:::

:::proof "wc:lem:ternary-auxiliary-positive"
The proof uses dimension induction and the ternary Pascal relation, with
separate boundary arguments. The origin is the unique zero exception.
:::

:::lemma_ "wc:lem:ternary-inner-weight" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.innerStartingWeight, WeightedChains.Ternary.extendedStartTypeWeight_eq_inner_of_lower_inner") (autoDeps := true) (tags := "semantic-review-pending, direct, factored, numbered")
%%%
source := paperSource "Lemma 5.4" 787 792
%%%

For a lower inner type $`(a,n-a-c,c)`, its starting weight is
$`U_n(a,c)-U_n(c+k,a-k)`.

*Semantic review:* pending. *Correspondence:* direct and factored. Lean
defines the displayed difference and separately identifies it with the
zero-extended start-type weight on the stated region.
:::

:::proof "wc:lem:ternary-inner-weight"
Induction along the inner diagonal cancels the neighboring upper and lower
outer contributions in the pointwise incidence recurrence.
:::
