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

:::lemma_ "wc:lem:boolean-inner-weight" (parent := "paper-boolean") (lean := "WeightedChains.DOne.innerWeight, WeightedChains.DOne.lowerStartingWeight_eq_innerWeight") (autoDeps := true) (tags := "semantic-review-pending, direct, factored, numbered")
%%%
source := paperSource "Lemma 4.1" 519 526
%%%

For a lower inner Boolean layer $`a`, its starting weight is
$`U_n(a)-U_n(n-a-k)`.

*Semantic review:* pending. *Correspondence:* direct and factored. Lean
defines this difference as `innerWeight` and separately proves that the actual
lower starting weight equals it. A later manuscript sentence incorrectly uses
$`a+k`; the numbered displayed statement and Lean both use $`n-a-k`.
:::

:::proof "wc:lem:boolean-inner-weight"
The outer contributions on the two sides are identified with the auxiliary
weight and its reflected argument, and the defining incidence recurrence is
then rearranged.
:::
