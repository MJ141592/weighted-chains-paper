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

#doc (Manual) "Conclusion" =>

:::group "paper-conclusion"
The general asymptotic result stated in the paper's discussion of further
research.
:::

:::theorem "wc:thm:asymptotic-density" (parent := "paper-conclusion") (lean := "WeightedChains.Asymptotics.maxKSeparatedCard_density_tendsto, WeightedChains.Asymptotics.maxKSeparatedCard") (autoDeps := true) (tags := "semantic-review-pending, direct, factored, encoding, unnumbered")
%%%
source := paperSource "Conclusion: asymptotic maximum density" 949 953
%%%

For fixed positive $`d` and $`k`, let $`A_{k,d}(n)` be the maximum cardinality
of a $`k`-separated family in $`\{0,\ldots,d\}^n`. Then

$`\displaystyle \frac{A_{k,d}(n)}{(d+1)^n}\longrightarrow
\frac{1}{dk+1}`.

*Semantic review:* pending. *Correspondence:* direct, factored, and encoded.
Lean defines the maximum over the finite collection of candidate finsets and
states the displayed $`o(1)` assertion as a real-valued `Tendsto` theorem.
The positive hypotheses make the manuscript's intended parameter domain
explicit.
:::

:::proof "wc:thm:asymptotic-density"
Split the coordinates into blocks of size $`k`. A saturated maximal chain in
one block has $`dk+1` vertices; it is the maximal-length higher-dimensional
analogue of a basic chain. Holding the other coordinates fixed produces the
required collection of full-length chains. Partition away the words whose
blocks all miss that chain; a separated family meets each remaining
block-chain in at most one point, while the exceptional proportion decays
geometrically. For the matching lower bound, the $`dk+1` rank-residue families
partition the cube and each is $`k`-separated. The full sequence follows by
keeping the finitely many possible remainders modulo $`k`.
:::
