# Equal-sided (d=3): status after the upgraded investigation

The unrestricted conjecture remains unresolved.  No equal-sided counterexample
was found, but no proof valid for every (n,k) was obtained either.  This is
consistent with the direct literature: the (k)-fold (M)-part Sperner
formulation is known in the range (Mle 2k), while the equal part-size case
outside that range is open.

The formal development now contains `WeightedChains/DThree.lean`.  It
specializes the Appendix-B theorem to (d=3), proving the cardinality bound
and maximality of both residue families whenever (nle 2k).  The first open
parameter pairs are (n=2k+1).

For the smallest open pair ((n,k)=(3,2)), an explicit partition of
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
