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

#doc (Manual) "The Boolean construction" =>

:::group "paper-boolean"
The Boolean (dimension-one) starting-weight construction.
:::

:::lemma_ "wc:lem:boolean-inner-weight" (parent := "paper-boolean") (lean := "WeightedChains.DOne.innerWeight, WeightedChains.DOne.lowerStartingWeight_eq_innerWeight") (autoDeps := true)
%%%
source := paperSource "wc:lem:boolean-inner-weight" "Lemma 4.1"
%%%

For a lower inner Boolean layer $`a`, its starting weight is
$`U_n(a)-U_n(n-a-k)`.

Lean defines this difference as `innerWeight` and separately proves that the
lower starting weight equals it.
:::

:::proof "wc:lem:boolean-inner-weight"
The outer contributions on the two sides are identified with the auxiliary
weight and its reflected argument, and the defining incidence recurrence is
then rearranged.
:::

:::lemma_ "wc:lem:boolean-inner-weight-positive" (parent := "paper-boolean") (lean := "WeightedChains.DOne.innerWeight_pos") (autoDeps := true)
%%%
source := paperSource "wc:lem:boolean-inner-weight-positive" "Lemma 4.2"
%%%

For $`1<k\leq n` and a lower inner Boolean layer $`a`, that is
$`n-k<2a\leq n`, the difference $`U_n(a)-U_n(n-a-k)` is positive.

Lean states this as the positivity of `innerWeight`, the difference defined for
Lemma 4.1. The hypothesis $`1<k` is essential: for $`k=1` the central
difference can vanish.
:::

:::proof "wc:lem:boolean-inner-weight-positive"
Fix $`k` and induct on $`n` from the base case $`n=k`, where the reflected term
vanishes. In the inductive step the Pascal-type recurrence for the auxiliary
weight splits the difference into the two corresponding differences one
dimension lower; each is either positive by induction or vanishes because its
argument is the central or boundary layer.
:::
