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
