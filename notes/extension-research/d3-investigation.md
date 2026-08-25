# The equal-sided `d = 3` extension: investigation note

## Status

Let

\[
P_n=\{0,1,2,3\}^n,\qquad m=3k+1,
\]

and call \(B\subseteq P_n\) `k`-separated when no distinct comparable
\(x<y\) in \(B\) differ in at most \(k\) coordinates.  The conjectured
extremal families are

\[
A^- = \{x: |x|\equiv \lfloor 3n/2\rfloor\pmod m\},\qquad
A^+ = \{x: |x|\equiv \lceil 3n/2\rceil\pmod m\}.
\]

No counterexample to this conjecture was found.  The search produced a short
general reduction of the cardinality assertion to a coordinate-symmetric
linear inequality, exact rational proofs in several cases beyond Appendix B,
and a fairly rigid description of the first open case \(n=2k+1\).  It did
not produce a proof for all \((n,k)\), and the uniqueness assertion remains
even further out of reach.  Thus the current conclusion is strong positive
evidence and rigorous new partial results, not a proof of the full `d = 3`
case.

## A regular-fibre LYM reduction

For \(0\le r\le 3k\), put

\[
a_r=[q^r](1+q+q^2+q^3)^k.
\]

Fix a `k`-set \(S\subseteq[n]\) and a word \(z\) on its complement.  The
corresponding fibre is a copy of \(C_4^k\).  The intersection of a
`k`-separated family \(B\) with this fibre is an antichain, so normality of
the product of chains gives

\[
  \sum_{x\in B,\ x_{-S}=z}\frac{1}{a_{|x_S|}}\le 1. \tag{1}
\]

It follows that the conjectured cardinality bound is proved if one can find
nonnegative fibre weights \(\lambda(S,z)\) such that

\[
  \sum_{|S|=k}\frac{\lambda(S,x_{-S})}{a_{|x_S|}}\ge1
  \quad\text{for every }x\in P_n, \tag{2}
\]

with equality on \(A^-\).  Indeed, multiplying (1) by the fibre weights and
summing bounds \(|B|\) by \(\sum_{S,z}\lambda(S,z)\).  Every `k`-fibre meets
\(A^-\) in one complete local rank, because the local ranks
\(0,\ldots,3k\) are a complete residue system modulo \(3k+1\).  Equality in
(2) on \(A^-\) therefore forces

\[
  \sum_{S,z}\lambda(S,z)=|A^-|.
\]

Coordinate averaging lets us take \(\lambda\) to depend only on the outside
type \(z=(z_0,z_1,z_2,z_3)\).  If
\(t=(t_0,t_1,t_2,t_3)\) is the type of \(x\), condition (2) becomes the
finite inequality

\[
 \sum_{\substack{u\le t\\u_0+u_1+u_2+u_3=k}}
 \left(\prod_{i=0}^3\binom{t_i}{u_i}\right)
 \frac{\lambda(t-u)}{a_{u_1+2u_2+3u_3}}\ge1. \tag{3}
\]

This is a much smaller certificate than the all-good-chain linear program,
but it still proves the bound for arbitrary labelled families, not merely
coordinate-symmetric ones.

There is also a compact exponential-generating-function form.  Define

\[
K_k(X)=\sum_{|u|=k}\frac{X^u}{u!\,a_{u_1+2u_2+3u_3}},\qquad
\Lambda(X)=\sum_{|z|=n-k}\lambda(z)\frac{X^z}{z!}.
\]

Then (3) says coefficientwise

\[
  K_k\Lambda\ \ge\ \frac{(X_0+X_1+X_2+X_3)^n}{n!}, \tag{4}
\]

with equality on the monomials in the candidate rank residue.

## A closed certificate at `n = 2k`

The fibre method gives an especially short proof at the boundary of
Appendix B.  Use

\[
  \lambda(S,z)=\frac{a_{|z|}}{\binom{2k}{k}}.
\]

For a word \(x\), pair each `k`-set \(S\) with its complement.  If the two
local ranks are \(r,s\), the paired coverage is

\[
 \frac1{\binom{2k}{k}}
 \left(\frac{a_s}{a_r}+\frac{a_r}{a_s}\right)
 \ge \frac2{\binom{2k}{k}}.
\]

Summing over the complementary pairs gives coverage at least one.  At the
middle rank \(3k\), symmetry gives \(a_s=a_{3k-s}=a_r\), so equality holds.
This proves cardinality optimality at \(n=2k\).  The argument in fact works
with the local rank numbers of \(\{0,\ldots,d\}^k\) for every `d`.

## Exact results beyond Appendix B

The type system (3) was solved and then rationalised.  Exact arithmetic
checks nonnegativity of every weight, every coverage inequality, equality on
the candidate types, and the total weight.  This gives computer-assisted but
fully exact proofs of the cardinality assertion in the following cases:

| \(n\) | \(k\) | \(|A^-|\) | outside types | positive weights | certificate SHA-256 |
|---:|---:|---:|---:|---:|:---|
| 5 | 2 | 161 | 20 | 20 | `bef321e3115e10f9bfb6dd870d5f45f48827827778c24ed35a9efab8a8c93bbd` |
| 7 | 3 | 2,136 | 35 | 35 | `d67e725323b8c68d6924783478f697103c1d406d41a9cbae7fecc92f01db532c` |
| 9 | 4 | 30,286 | 56 | 53 | `4291640777cb9a355655029102574b988ac4ec94314675d416102aaad3e253b7` |
| 11 | 5 | 440,496 | 84 | 76 | `37ded3143ad2a5a768bab6283eb148c79591bef200135f9a6a05a84b199016c1` |
| 14 | 2 | 38,371,818 | 455 | 453 | `480581e02917f49d2a677919e48b6c7c65a1b74bc3af130b40062533faa1cced` |

All five cases are outside the range \(n\le2k\) of Appendix B.  The first
four entries are the first open dimension \(n=2k+1\) for their respective
values of `k`.
Stable floating-point certificates exist in every first-open case through
\(k=10\), and nominally through \(k=12\), although the last two quadratic
fits are less well-conditioned.  Broader numerical sweeps also found
certificates for `k = 2` through `n = 20` and again at `n = 25`, and for
`k = 3` through at least `n = 17`.  These floating-point sweeps are evidence
only.

Exact labelled maximum-independent-set calculations give optimum 161 for
\((n,k)=(5,2)\) and 622 for \((6,2)\).  If both prescribed families are
forbidden in the \((5,2)\) calculation, the optimum drops to 160.  Extensive
type-orbit, block-orbit, local-augmentation, and modular-code searches found
no larger family.

## Structure at the first open dimension

Let \(n=2k+1\), so that the lower candidate residue is zero.  In this case

\[
 A^-=L_0\cup L_{3k+1}\cup L_{6k+2};
\]

that is, the middle layer together with the bottom word and all \(2k+1\)
coatoms.  There is a natural candidate-tight starting weight

\[
  \lambda_0(z)=
  \frac{a_{-\operatorname{rk}(z)\bmod(3k+1)}}{\binom{2k+1}{k}}.
\]

Write \(\lambda=\lambda_0\mu\).  If \(x\) is a candidate word and \(Z\)
is the type of a uniformly random \((k+1)\)-subset of its coordinates, then
candidate tightness reduces exactly to

\[
  \mathbb E_x\mu(Z)=1. \tag{5}
\]

This exposes the candidate equations as multivariate-hypergeometric
averages.  Reliable numerical solutions through \(k=10\) can be chosen so
that, on each outside-rank residue, \(\mu\) is quadratic in the digit counts;
one convenient six-term form is

\[
 \mu(z)=\alpha_r+\beta_rz_1+\gamma_rz_2+\delta_rz_3
       +\varepsilon_r(z_1)_2+\phi_r(z_2)_2,
 \qquad r=\operatorname{rk}(z)\bmod(3k+1). \tag{6}
\]

The basis has a U-statistic explanation.  With \(N=2k+1\), population rank
\(R\), and population digit counts \(T_j\),

\[
 H_j(z)=\frac{2k+1}{k+1}(2\operatorname{rk}(z)-(3k+1)-j)z_j
\]

is an unbiased estimator of \((R-(3k+1))T_j\), after the harmless endpoint
convention for the two sample ranks just above \(3k+1\).  Analogous
quadratic statistics estimate \((R-(3k+1))(T_j)_2\).  Their expectations
therefore vanish on the central candidate slice.  The missing step is a
uniform choice of the residue-dependent coefficients in (6) for which every
outsider coverage is visibly at least one.

Several forced boundary values do have closed forms:

\[
\begin{aligned}
 \mu(k+1,0,0,0)&=1,\\
 \mu(k,1,0,0)=\mu(0,0,1,k)&=\frac{2k}{k+1},\\
 \mu(0,0,0,k+1)&=\frac1k,\\
 \mu(0,0,2,k-1)&=
 \frac{2(2k^3+k^2-2k+1)}{k(k+1)^2}.
\end{aligned} \tag{7}
\]

They force the observed optimal maximum deviation

\[
  \max_z\mu(z)-1=\frac{3k^3-5k+2}{k(k+1)^2}, \tag{8}
\]

which the quadratic linear program attains for every reliably checked
\(k\le10\).  This is a rational-in-`k` spine for a possible uniform proof,
but not yet the whole certificate.

## What failed, and why

- **Natural rank-only fibre weights.**  The weights \(\lambda_0\) are exact
  on the candidate but under-cover some outsider types (already by a factor
  `0.6` for \((n,k)=(5,2)\)).  Allowing arbitrary weights but requiring the
  final coverage to depend only on global rank is also infeasible.

- **Scalar degree elevation.**  Multiplying a certificate polynomial by
  \((X_0+X_1+X_2+X_3)/(n+1)\) preserves coverage, but multiplies its cost by
  four and over-covers the new candidate.  Coefficientwise thinning cannot
  repair this even in the first `4 -> 5` test for `k = 2`.

- **A product factor.**  A sharp certificate at \(2k+1\) cannot simply be
  multiplied by a positive exponential-generating-function factor to give
  the next dimensions; this fails already for \((k,n)=(2,6)\).

- **Disjoint `k`-blocks.**  Pairing complementary blocks gives the clean
  \(n=2k\) proof, but the corresponding noncentral phase inequalities fail.
  Coarser Latin/transversal relaxations can actually exceed the modular
  construction; the omitted constraints between coordinates in distinct
  blocks are essential.

- **Independent chain-product lifting.**  Suppose a short symmetric chain
  \(C\) has width `k` and take \(C\times C_4\).  A symmetric product chain
  through a corner uses `k + 1` coordinates, while a full good chain would
  have to discard all occurrences of an old active coordinate in a very
  short end segment.  A deficit count shows that, for every \(k\ge2\), at
  least one corner lies on no good chain contained in this product block.
  The smallest example is the width-two chain with transition word `01` and
  rank span two in \(C_4^2\).  Hence a valid induction would have to move
  weight between distinct old-chain blocks.

- **In fact, an exact good-chain cover need not exist at all.**  The first
  counterexample is already \((n,k,d)=(4,3,3)\), inside the easy cardinality
  range of Appendix B.  Here is a short dual certificate.  Give potential
  `+1` to the four types

  \[
    (4,0,0,0),\quad(3,0,1,0),\quad(0,1,0,3),\quad(0,0,0,4),
  \]

  potential `-1` to \((2,2,0,0)\) and \((0,0,2,2)\), and zero to every
  other type.  The total potential of the vertices is

  \[
    1+4+4+1-6-6=-2. \tag{9}
  \]

  Every good chain has nonnegative potential.  It contains at most one of
  the two negative types, since representatives of those types differ in all
  four coordinates.  Consider a chain through a lower negative vertex
  `0011`.  A symmetric good chain containing rank two must start there; to
  gain eight in at most three coordinates it must end at a vertex of type
  \((0,1,0,3)\), of potential `+1`.  A full chain has rank span nine.  If
  its bottom rank is zero, it contains `0000`; if its bottom rank is one,
  capacity forces its top to have type \((0,1,0,3)\); it cannot start at
  rank two because the three largest remaining coordinate capacities of
  `0011` sum to only eight.  Reflection handles the upper negative type.
  Hence a nonnegative exact weighted cover would express the negative total
  (9) as a nonnegative sum of chain potentials, a contradiction.

  This does not affect the extremal statement, which is true here by
  Appendix B.  It shows that the paper's exact weighted-decomposition
  sufficient condition cannot be the general `d = 3` proof.  The fibre
  certificates above are deliberately *over*covers away from the candidate,
  and so escape this obstruction.

- **The endpoint condition from the paper.**  At \(n=6k+2\), the candidate
  point \(1^n\) starts no good chain: `k` active coordinates have only `2k`
  upward capacity, less than the full span `3k`, while a symmetric chain from
  that point would be too long.  For the first case \((n,k)=(14,2)\), however,
  an exact punctured cover of cost \(|A^-|-1\) avoids \(1^{14}\).  It proves
  that every maximum family must contain this point (and, by reflection,
  \(2^{14}\)).  Thus the obstruction is to the paper's particular uniqueness
  propagation, not a counterexample to cardinality.

## Remaining lemma

The cleanest sufficient statement now is:

> For every \(n\ge2k\), there are nonnegative type weights
> \(\lambda(z_0,z_1,z_2,z_3)\), with \(z_0+z_1+z_2+z_3=n-k\), satisfying
> (3), with equality on all types in the lower central residue.

Appendix B handles \(n\le2k\), so this lemma would prove the cardinality
part of the equal-sided `d = 3` conjecture.  It is true in every exact and
numerical instance checked.  The first target should be \(n=2k+1\), using
(5)--(8).  Even after that, one needs either a genuinely multi-state lifting
argument or a direct all-`n` construction.  Finally, equality/uniqueness will
need a replacement for the positive-start condition, which genuinely fails
for `d = 3`.

## Reproducibility pointers

The main scratch programs and logs are under `.context/d3_countersearch/`:

- `exact_fiber_cover.py` constructs and checks the rational certificates;
- `scaled_fiber_feasibility.py` performs the stable general feasibility test;
- `first_open_poly_scaled.py` tests the first-open polynomial ansatz;
- `exact_fiber_n7_k3.log`, `exact_fiber_n9_k4.log`,
  `exact_fiber_n11_k5.log`, and `exact_fiber_n14_k2.log` record exact runs;
- `exact_punctured_n14_k2.py` records the punctured good-chain certificate.

All of these are research scratch files rather than changes to the paper.
