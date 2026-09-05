# Equal-sided (d=3): status after the upgraded investigation

The unrestricted conjecture remains unresolved.  No equal-sided counterexample
was found, but no proof valid for every (n,k) was obtained either.  This is
consistent with the direct literature: the (k)-fold (M)-part Sperner
formulation is known in the range (Mle 2k), while the equal part-size case
outside that range is open.

The formal development now contains `WeightedChains/DThree.lean`.  It
specializes the Appendix-B theorem to (d=3), proving the cardinality bound
and maximality of both residue families whenever (nle 2k).  The first open
parameter pairs are (n=2k+1), beginning with `(n,k)=(5,2)`.

For the small in-range pair `((n,k)=(3,2))`, an explicit partition of
`{0,1,2,3}^3` into twelve good chains gives the cardinality bound (12).
An exhaustive finite check of all transversals of that partition leaves only
the rank-4 and rank-5 residue families.  The checked chain list is in
`.context/d3_proof_n3.py`; the computational certificate is research
evidence rather than a general Lean proof.

For larger open cases, exact fibre-LYM certificates prove

\[
(n,k)=(7,3),(9,4),(11,5),(14,2),
\]

and stable numerical certificates cover every first-open pair through
`k=12`.  Those certificates are recorded in `d3-investigation.md` and its
scratch directory.  They prove cardinality for the listed cases, including
against nonsymmetric families, but do not supply a uniform formula.

One important negative result is methodological: an exact weighted cover by
good chains already fails for `(d,n,k)=(3,4,3)`, by the six-type dual
potential recorded in `d3-investigation.md`.  Thus a general proof, if true,
must use fibre overcovers or another method.  This obstruction is not a
counterexample to the extremal conjecture.

## Two obstructions to tempting general proofs

The regular-fibre LYM relaxation is genuinely weaker than the integer problem.
For `(d,n,k)=(3,3,2)`, assign mass `21/25` to each vertex of types
`(0,1,2,0)` and `(0,2,1,0)`, and mass `3/5` to each vertex of types
`(1,0,1,1)` and `(1,1,0,1)`. Since the rank sizes of `C_4^2` are
`1,2,3,4,3,2,1`, every 2-coordinate fibre has Lubell mass exactly one
(coordinate symmetry checks all fibres), but the total mass is

\[
6\cdot\frac{21}{25}+12\cdot\frac35=\frac{306}{25}=12.24.
\]

The conjectured integer family has size 12 here, and an exact MILP gives
maximum 12 (maximum 11 when both residue families are excluded). Therefore
no proof using only these fibrewise LYM inequalities can be sharp in general:
the associated fractional packing number is already `306/25 > 12`. The exact
check is reproducible in `.context/d3_countersearch/fractional_obstruction_n3k2.py`.

The conflict graph is not perfect either. At the same parameters it contains
the induced 5-cycle

\[
(1,1,0),(1,2,1),(2,2,3),(3,3,3),(3,1,0),
\]

where consecutive pairs are comparable and differ in at most two coordinates,
while all nonconsecutive pairs are nonadjacent. Thus an ordinary
perfect-graph or clique-cover reduction cannot supply the missing theorem.

## A complete first-open case: `(d,n,k)=(3,5,2)`

The first genuinely open case can now be settled exactly.  A type-symmetric
fibre-LYM certificate assigns strictly positive rational weights to all 20
outside types (the full list and the exact Fraction verifier are in
`.context/d3_certificate_n5.md`).  Its weighted coverage is at least one on
all 56 global types, and its total weight is exactly 161, the size of the
residue family with ranks `0,7,14`.  Hence every 2-separated family has size
at most 161.

Positivity gives the equality case: a family of size 161 must attain equality
in every pair-fibre LYM inequality.  Exhaustive exact enumeration of
antichains in `[0,3]^2` shows that equality means a complete local rank level.
Pair transfers preserving the two-coordinate sum then connect every point in
a global rank level, so an extremal family is a union of global rank levels.
The separation condition and the cardinality force precisely ranks
`0,7,14` (or, after reflection, the complementary central residue).  Thus
the conjecture, including uniqueness, is proved for this first-open case.

## Broader method audit

We ran a 21-method audit covering variants of the paper's chain/weight
strategy, compression, entropy, LP, spectral, and coding-theoretic approaches.
The decisive outcomes were:

* Coordinate and rank shifts are not preservation operations (already
  `A={(1,0,0),(0,1,1)}` in `[0,3]^3`, `k=2`, is sent to a forbidden pair).
* Slice induction loses one unit of separation between slices; the resulting
  recurrence is too weak even at `(n,k)=(5,2)`.
* Product-chain, cyclic-chain, anti-basic-chain, and signed-weight variants
  either miss explicit vertices or have infeasible/non-positive weight LPs.
* Hoffman, Delsarte, theta, Fourier/Krawtchouk, and association-scheme bounds
  are unavailable or too weak: the graph is irregular and non-perfect, and
  the exact fibre LP has value `306/25` at `(3,3,2)`.
* Entropy/Shearer gives only `|B|≤4^(n-1)`, far above the target.
* Symmetry-reduced exact MWIS searches excluding both residue families give
  `37824<37825` at `(n,k)=(9,2)`, with analogous strict gaps at `n=10,11`.

These tests do not prove the unrestricted conjecture, but they narrow viable
routes to a genuinely new global inequality or a substantially more flexible
weighted-chain construction.

## Enlarging the chain set (new experiment)

The paper's `good` chains impose an artificial endpoint restriction: they must
be symmetric or have the full `3k+1` vertices.  I enumerated *all* saturated
chains whose endpoints differ in at most `k` coordinates, allowing every span
from 0 through `3k`.  The resulting type-orbit incidence LP is feasible with
total weight equal to the conjectured residue size in every tested case:

\[
(n,k)=(5,2),(6,2),(7,2),(8,2),(9,2),(7,3),
\]

giving totals `161,622,2415,9548,37825,2136`, respectively.  Thus the
endpoint obstruction for the original good-chain family is not fundamental;
shorter nonsymmetric chains repair it.  The remaining problem is to identify
and prove a positive recursive formula for these much larger chain weights.

Further enumeration confirms the same phenomenon at `(n,k)=(9,3)`: 49,762
chain orbits give an exact LP decomposition of total weight 30,927, matching
the residue construction.  This is currently the strongest computational lead
toward a (d=3) proof, but no general positivity or min-max theorem for this
enlarged chain family has yet been found.

For `k=2`, an integer type-orbit chain-partition LP also succeeds at
`n=5,6,7`, with exactly `161,622,2415` chains (48, 107, and 144 positive
type-orbits respectively).  This suggests that the desired construction may
be genuinely combinatorial rather than merely fractional; extracting its
recurrence is the current target.

The same enlarged-chain LP works beyond `d=3`: exact numerical solutions hit
the residue bound for `(d,n,k)=(4,5,2),(4,7,2),(5,5,2)`, with objectives
`391,9045,800` and positive supports.  This indicates that the endpoint
relaxation is not peculiar to the ternary case.

## Full-span fractional covers (stronger computational lead)

There is an important distinction between an exact decomposition
`A x = b` and the cover inequalities `A x >= b` needed for the cardinality
bound.  The latter are the relevant LP.  Re-running the orbit LP with only
full-span chains (exactly `dk+1` vertices, hence width exactly `k`) gives the
residue value in every tested case, including

* `d=3`: `k=2`, `n=5,...,11`, and `k=3`, `n=7,9,10`;
* `d=4`: `k=2`, `n=3,...,7,9`;
* `d=5`: `k=2`, `n=4,5`.

Thus the shorter nonsymmetric chains are useful for finding integral
partitions, but are not required for the fractional cardinality inequality
in the tested range.  Every full-span chain meets the residue family in
exactly one point, so the LP lower bound is automatic; the unresolved part is
an explicit fractional cover attaining that lower bound.

For `d=3,k=2`, a particularly small ansatz is already exact numerically:
only the two interleaving words `000111` and `010101`, together with
coordinate permutations and type-dependent starting weights, suffice for all
tested `n=5,...,11`.  Finding a closed positive recurrence for those weights
would give a plausible elegant proof of the first genuinely open infinite
subcase.  No such recurrence has yet been derived.

This should not be confused with a generic min--max theorem: the analogous
Saks--West semiantichain/unichain-covering conjecture for arbitrary product
posets is false (Bosek--Felsner--Knauer--Matecki, 2014).  Any proof here must
use the strong symmetry of equal chains in the cube.
