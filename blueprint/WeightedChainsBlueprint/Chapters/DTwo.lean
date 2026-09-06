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

:::definition "wc:def:basic-chain" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.BasicChain, WeightedChains.Ternary.BasicChain.toChain, WeightedChains.Ternary.BasicChain.toChain_saturated, WeightedChains.Ternary.BasicChain.toChain_length, WeightedChains.Ternary.BasicChain.toChain_width") (autoDeps := true)
%%%
source := paperSource "wc:def:basic-chain" "Definition 5.1"
%%%

A ternary basic chain changes one coordinate completely from zero to two before
moving to the next coordinate. The constructive Lean structure records its
start and ordered changed coordinates and produces the corresponding saturated
generic chain.

Lean gives a constructive $`d=2` encoding rather than a characterisation of
arbitrary chains.
:::

:::lemma_ "wc:lem:basic-chains-suffice" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.BasicChain.exists_singleton_good_of_rank_eq_dimension, WeightedChains.Ternary.BasicChain.exists_good_with_endpoint_avoiding_middle_of_lowerResidue, WeightedChains.Ternary.BasicChain.exists_closer_lowerResidue") (autoDeps := true)
%%%
source := paperSource "wc:lem:basic-chains-suffice" "Lemma 5.2"
%%%

Middle-layer singleton chains are basic. Every noncentral reference-family
vertex has a suitable basic good chain with it as an endpoint, and every vertex
outside the reference family has a basic good chain through it and a strictly
closer noncentral reference-family vertex.

Lean factors the witness construction into three declarations and treats the
exceptional type $`(1,n-1,0)` through a containing chain rather than a chain
starting there.
:::

:::proof "wc:lem:basic-chains-suffice"
The construction splits by lower/upper symmetry, outer/inner type, and the
exceptional near-middle type. The three associated theorems expose the exact
witnesses needed by the weighted uniqueness argument.
:::

:::lemma_ "wc:lem:ternary-auxiliary-positive" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.auxiliaryWeight_pos_of_valid_lower, WeightedChains.Ternary.auxiliaryWeight_zero_zero") (autoDeps := true)
%%%
source := paperSource "wc:lem:ternary-auxiliary-positive" "Lemma 5.3"
%%%

For a valid lower ternary type other than $`(a,c)=(0,0)`, the auxiliary weight
$`U_n(a,c)` is positive. At $`(0,0)` it is zero.

Lean proves positivity away from the origin and separately proves the zero
value at $`(0,0)`.
:::

:::proof "wc:lem:ternary-auxiliary-positive"
The proof uses dimension induction and the ternary Pascal relation, with
separate boundary arguments. The origin is the unique zero exception.
:::

:::lemma_ "wc:lem:ternary-inner-weight" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.innerStartingWeight, WeightedChains.Ternary.extendedStartTypeWeight_eq_inner_of_lower_inner") (autoDeps := true)
%%%
source := paperSource "wc:lem:ternary-inner-weight" "Lemma 5.4"
%%%

For a lower inner type $`(a,n-a-c,c)`, its starting weight is
$`U_n(a,c)-U_n(c+k,a-k)`.

Lean defines the displayed difference and separately identifies it with the
zero-extended start-type weight on the stated region.
:::

:::proof "wc:lem:ternary-inner-weight"
Induction along the inner diagonal cancels the neighboring upper and lower
outer contributions in the pointwise incidence recurrence.
:::

:::lemma_ "wc:lem:ternary-inner-weight-positive" (parent := "paper-ternary") (lean := "WeightedChains.Ternary.innerStartingWeight_pos_of_valid_lower_inner") (autoDeps := true) (uses := "wc:lem:ternary-inner-weight")
%%%
source := paperSource "wc:lem:ternary-inner-weight-positive" "Lemma 5.5"
%%%

For $`k \le n` and a proper lower inner type $`(a,n-a-c,c)`, that is
$`0 \le a, c \le n`, $`0 < a+c \le n` and $`a-k < c \le a`, the starting
weight $`W_n(a,c)` is positive.

Lean proves the positivity of the difference $`U_n(a,c)-U_n(c+k,a-k)` that
Lemma 5.4 identifies with $`W_n(a,c)`, under the additional hypothesis
$`1 < k` of Theorem 1.1, which is needed on the diagonal inner types.
:::

:::proof "wc:lem:ternary-inner-weight-positive"
Induction on $`n` with base case $`n = k`, using the three-term dimension
recurrence for the inner difference and separate treatment of the edge cases
in which a neighbouring type is outer, improper, or empty.
:::
