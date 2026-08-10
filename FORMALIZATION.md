# Formalisation roadmap

The goal is a kernel-checked Lean 4 proof of the paper with no `sorry`, `admit`,
custom axioms, opaque proof placeholders, or equality-by-computation shortcuts.
Only declarations which compile with complete proofs are added to the main
library.

## Repository and proof-engineering choices

- This is a standalone Lake project depending on mathlib. The checked-in
  `lake-manifest.json` gives reproducible dependency revisions and
  `lean-toolchain` matches mathlib exactly.
- Lean modules follow the mathematical order of the paper. Reusable elementary
  combinatorics stays separate from the `d = 1` and `d = 2` constructions.
- Definitions use finite types (`Fin n → Fin (d + 1)`) and `Finset`, so all
  cardinalities and weighted sums remain manifestly finite.
- General statements are proved at their natural level of generality. For
  example, the rank-residue families are `k`-separated for every `d`. Their
  unrestricted optimality is proved for `d ∈ {1, 2}`, and Appendix 2 proves
  optimality for arbitrary `d` in the range `n/2 ≤ k ≤ n`.
- CI builds with warnings as errors. `scripts/audit.sh` compiles every Lean
  source file (including modules not yet in the root import) and rejects proof
  escape hatches, custom constants/axioms, unsafe declarations, and
  decision-procedure proof shortcuts.
- `#print axioms` on the current declarations reports only Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound`, inherited through mathlib.
  `scripts/AxiomAudit.lean` checks this allowlist automatically for every
  theorem in the project namespace, while retaining named checks as a readable
  headline inventory. There are no axioms declared by this project.

## Paper-to-Lean map

| Paper item | Lean declaration | Status |
| --- | --- | --- |
| Hypercube, rank, layers | `Cube`, `Cube.rank`, `Cube.layer` | proved/defined |
| Type | `Cube.typeOf`, `Cube.sum_typeOf` | proved/defined |
| `k`-separated family | `Cube.KSeparated` | defined |
| Families `A₁`, `A₂` | `Cube.lowerResidueFamily`, `Cube.upperResidueFamily` | defined |
| `A₁`, `A₂` are separated | `Cube.lowerResidueFamily_kSeparated`, `Cube.upperResidueFamily_kSeparated` | proved for every `d` |
| Every good chain meets `A₁`, `A₂` exactly once | `Chain.Good.card_lowerResidueFinset_inter_vertices`, `Chain.Good.card_upperResidueFinset_inter_vertices` | proved for every `d` |
| `|A₁| = |A₂|` by reflection | `Cube.card_lowerResidueFinset_eq_card_upperResidueFinset` | proved |
| Chains, width, saturation, symmetry, good chains | namespace `Chain` | defined |
| Saturated-chain rank and length facts | `Chain.rank_vertex_eq`, `Chain.length_le_width_mul_add_one`, `Chain.symmetric_iff_endpoint` | proved |
| Corrected Boolean width/length equivalence | `Chain.width_eq_steps_of_saturated`, `Chain.length_eq_width_add_one_of_saturated` | proved |
| A separated family meets a good chain at most once | `Chain.card_inter_vertices_le_one` | proved (from the width condition) |
| Weighted double-counting in Lemma 3.2 | `WeightedCover.card_le_of_weighted_cover` | proved |
| Lemma 3.2, cardinality with the actual reference family | `Chain.kSeparated_card_le_lowerResidueFinset` | proved, conditional only on the weighted cover |
| Equality forces one point on each positive chain | `Chain.kSeparated_inter_vertices_card_eq_one_of_positive` | proved |
| Proposition 3.1, concrete weighted assignments and positivity geometry | `DOne.BooleanChain.indexedInducedWeight_eq_one`, `DOne.BooleanChain.indexedWeight_pos`, `Ternary.BasicChain.indexedInducedWeight_eq_one`, `Ternary.BasicChain.indexedWeight_nonneg`, and the `DOneEqualityPropagation`/`DTwoBasicSufficiency` witnesses | proved componentwise for `d = 1,2` |
| Outward uniqueness induction | `UniquenessPropagation.finset_eq_of_positive_weight_outward_induction` | proved |
| Connected two-middle-layer choice | `DOneMiddleUniqueness.inter_adjacentLayers_eq_lower_or_upper` | proved for the Boolean cube |
| Section 4, `U_n` definition and recurrence | `DOne.auxiliaryWeight`, `DOne.auxiliaryWeight_recurrence_ofNat` | proved |
| Section 4, Pascal identity for `U_n` | `DOne.auxiliaryWeight_succ` | proved |
| Section 4, positivity on outer layers | `DOne.auxiliaryWeightNat_pos` | proved |
| Section 4, inner-layer formula and positivity | `DOne.innerWeight`, `DOne.innerWeight_pos` | proved |
| Section 4, positivity of all lower starting weights | `DOne.lowerStartingWeight_pos` | proved |
| Section 4, reflected `W_n` recurrences | `DOne.startingWeight_recurrence_outer`, `DOne.startingWeight_recurrence_inner` | proved with zero-extension |
| Section 4, layer-total bookkeeping gives `binom n a` | `DOne.layerWeightTotal_eq_choose` | proved |
| Section 4, finite saturated chains and uniform incidence | `DOne.BooleanChain`, `DOne.BooleanChain.card_goodChainsStartingAtLayerThrough_eq_of_rank_eq` | proved |
| Section 4, Boolean layer size and exact chain/layer incidence | `DOne.card_booleanLayerFinset`, `DOne.BooleanChain.card_booleanLayerFinset_inter_vertices` | proved |
| Section 4, complement/reversal symmetry of represented chains | `DOne.BooleanChain.reflectEquiv`, `DOne.BooleanChain.inducedWeight_reflect` | proved |
| Section 4, explicit good-chain existence through every Boolean vertex | `DOne.BooleanChain.exists_good_containing` | proved |
| Section 4, distribute totals over individual chains and prove induced weight one | `DOne.BooleanChain.inducedWeight_eq_one`, `DOne.BooleanChain.indexedInducedWeight_eq_one` | proved |
| Main theorem, `d = 1` cardinality bound | `DOne.BooleanChain.kSeparated_card_le_lowerResidueFinset` | proved |
| Main theorem, `d = 1` equality forces exact-one on every good chain | `DOne.BooleanChain.inter_goodChain_card_eq_one_of_card_eq` | proved |
| Main theorem, `d = 1` central equality choice | `DOne.BooleanChain.middleLayer_subset_candidate_of_even`, `DOne.BooleanChain.inter_middleLayers_eq_lower_or_upper_of_odd` | proved |
| Main theorem, `d = 1` propagate a lower central choice outward | `DOne.BooleanChain.eq_lowerResidueFinset_of_card_eq_of_middle_agreement` | proved |
| Main theorem, complete `d = 1` bound and two-family equality classification | `DOne.BooleanChain.cardinality_and_uniqueness` | proved |
| Section 5, ternary type arithmetic and trinomial Pascal identity | `Ternary.TypeCounts`, `Ternary.extendedTrinomial_succ` | proved |
| Section 5, type-orbit cardinality and transitivity | `Ternary.card_typeFiber`, `Ternary.exists_coordinatePermutation_of_same_type` | proved |
| Section 5, concrete basic chains, exact type traces, and reflection | `Ternary.BasicChain`, `Ternary.BasicChain.reflectEquiv` | proved |
| Section 5, basic good-chain existence through every ternary vertex | `Ternary.BasicChain.exists_good_containing` | proved |
| Section 5, corrected `positive_basic_enough_lemma` geometry | `Ternary.BasicChain.exists_good_containing_avoiding_middle`, `Ternary.BasicChain.exists_closer_lowerResidue` | proved |
| Section 5, metachain type traces and incidence uniformity | `Ternary.BasicChain.type_vertexAt_eq_of_same_start_type`, `Ternary.BasicChain.card_goodChainsStartingAtTypeThrough_eq_of_same_type` | proved |
| Section 5, canonical start-type groups and equal distribution within a metachain | `Ternary.BasicChain.startGroup`, `Ternary.BasicChain.sum_distributedChainWeight_startGroup` | proved |
| Section 5, canonical group determines width and full type trace | `Ternary.BasicChain.width_eq_of_mem_startGroup`, `Ternary.BasicChain.type_vertexAt_eq_of_mem_startGroup` | proved |
| Section 5, reduce type-total weight to unit vertex weight | `Ternary.BasicChain.inducedWeight_eq_one_of_total_eq_trinomial` | proved |
| Section 5, one incidence per type and type-level double counting | `Ternary.BasicChain.card_typeFiber_inter_vertices_le_one`, `Ternary.BasicChain.totalInducedWeightOnType_eq_sum_if_visits` | proved |
| Section 5, regroup descriptor incidence by metachain start type | `Ternary.BasicChain.totalInducedWeightOnType_distributed_eq_sum_startTypes` | proved |
| Section 5, arithmetic classification of occupied canonical start types | `Ternary.BasicChain.mem_occupiedStartTypes_iff_arithmetic` | proved |
| Section 5, explicit alternating type trace for each canonical metachain | `Ternary.BasicChain.startGroupVisitsType_iff_canonicalTypeVisits` | proved |
| Section 5, finite triangular enumeration of occupied start types | `Ternary.BasicChain.occupiedStartTypes_eq_filter_arithmetic` | proved |
| Section 5, two-diagonal auxiliary incidence sum telescopes to the trinomial coefficient | `Ternary.auxiliaryIncidenceSum_eq_extendedTrinomial` | proved |
| Section 5, pair inner lower metachains with their full-width upper partners | `Ternary.canonicalStartWeightIncidenceSum_eq_auxiliaryIncidenceSum` | proved |
| Section 5, auxiliary `U_n(a,c)` definition and exact recursion | `Ternary.auxiliaryWeight`, `Ternary.auxiliaryWeight_recursion` | proved |
| Section 5, dimension-Pascal identity on valid lower types | `Ternary.auxiliaryWeightPascal_of_valid_lower` | proved, including ghost boundaries |
| Section 5, inner starting-weight difference and dimension recurrence | `Ternary.innerStartingWeight`, `Ternary.innerStartingWeight_succ_of_valid_inner` | proved |
| Section 5, corrected positivity of `U_n(a,c)` | `Ternary.auxiliaryWeight_pos_of_valid_lower` | proved away from `(0,0)` |
| Section 5, positivity of inner starting weights | `Ternary.innerStartingWeight_pos_of_valid_lower_inner` | proved |
| Section 5, full reflected start-type total and positivity | `Ternary.startTypeWeight`, `Ternary.startTypeWeight_pos` | proved |
| Section 5, the three pointwise `W_n(a,c)` recurrences | `Ternary.startTypeWeight_recurrence_lower_outer`, `Ternary.startTypeWeight_recurrence_lowest_lower_inner`, `Ternary.startTypeWeight_recurrence_lower_inner` | proved with integer zero-extension and corrected final sign |
| Section 5, concrete distributed weighting covers every ternary vertex | `Ternary.BasicChain.inducedWeight_startTypeTotal_eq_one` | proved |
| Main theorem, `d = 2` cardinality bound | `Ternary.BasicChain.kSeparated_card_le_lowerResidueFinset` | proved |
| Main theorem, `d = 2` exceptional-point-aware outward uniqueness | `Ternary.BasicChain.eq_lowerResidueFinset_of_card_eq` | proved |
| Main theorem, complete `d = 2` bound and equality classification | `Ternary.BasicChain.cardinality_and_uniqueness` | proved |
| Main theorem, unified statement for `d \in {1,2}` | `main_cardinality_and_uniqueness` | proved |
| Appendix: weighted proof of Sperner, including exact chain collection, local telescoping incidence, `(0,1]` weight range, and equality classification | `SpernerAppendix.SymmetricChain.indexEquivSymmetricChains`, `SpernerAppendix.SymmetricChain.weight_eq_choose_sub_previous_div_card`, `SpernerAppendix.SymmetricChain.inducedWeight_eq_one`, `SpernerAppendix.SymmetricChain.weight_le_one`, `SpernerAppendix.cardinality_and_uniqueness` | final bound/classification proved for every `n`; intermediate positive-weight statements carry their mathematically necessary small-`n` hypotheses |
| Appendix: arbitrary `d`, `n/2 ≤ k ≤ n` optimality of both `A₁` and `A₂` | `LargeK.lowerResidueFinset_eq_middleLayer`, `LargeK.kSeparated_card_le_lowerResidueFinset`, `LargeK.lowerResidueFinset_isMaximum`, `LargeK.upperResidueFinset_isMaximum` | proved internally, including the required symmetric-chain decomposition rather than assuming its existence |

## Clarifications exposed by formalisation

These points were exposed by translating the paper into typed statements. The
first three have been confirmed by the author; the remaining entries are
resolved by the formal proofs, and correction 25 also has the displayed
numerical counterexample.

1. `k`-separation must quantify over **distinct** comparable vertices. Without
   `x ≠ y`, no nonempty family is `k`-separated. Lean's definition makes this
   condition explicit.
2. The paper's definition of type has its parameters transposed. A point of
   `{0, ..., d}^n` has type `(t₀, ..., t_d)` with `∑ t_i = n`, not
   `(t₀, ..., t_n)` with sum `d`. Lean uses the former.
3. The sentence “For `d = 1`, a chain's width is `l` iff its length is `l + 1`”
   is false for arbitrary chains (for example, the two-vertex chain
   `000 ≤ 111`). It becomes correct for saturated chains and is proved in that
   form as `Chain.length_eq_width_add_one_of_saturated`.
4. In the inner-layer positivity argument for `d = 1`, the lemma gives
   `W_n(a) = U_n(a) - U_n(n-a-k)`, but the next paragraph says it suffices to
   prove `U_n(a) - U_n(a+k) > 0`. The induction that follows consistently uses
   `n-a-k`. The chain starting at upper layer `a+k` reflects to lower starting
   layer `n-a-k`, so `n-a-k` is the correct argument and is now formalised.
5. The sentence about an upper outer layer says
   `W_n(a) = W_n(n-a) = U_n(a)`. With `a` denoting the upper layer, the final
   term is `U_n(n-a)` by the same reflection.
6. The Section 5 definition of a basic chain ends “We call this chain good”.
   The new notion being defined there is **basic**, not good.
7. The displayed lower-outer range `c+k ≤ a ≤ c` is impossible for positive
   `k`. The recurrence and type triangle require `c+k ≤ a` together with
   `a+c ≤ n` (equivalently `a ≤ n-c`).
8. The outer-positivity paragraph reverses the lower-type inequality when it
   writes `a ≤ c ≤ n`; the lower half has `c ≤ a` (and validity also requires
   `a+c ≤ n`).
9. The stated ternary positivity lemma includes `(a,c)=(0,0)`, but the
   recurrence gives `U_n(0,0)=0` for every positive `n`. Positivity must exclude
   this exceptional all-ones type, consistently with its zero chain weight
   elsewhere in Section 5.
10. In the proof of the basic-chain sufficiency lemma, the “outer vertices”
    paragraph immediately calls a type satisfying `c<a-k` “lower inner”. That
    inequality describes a lower outer type.
11. In inner-positivity case `2.2°`, the first displayed difference writes
    `U_n(a-k,a+k)`. The preceding lemma and the cancellation on the following
    lines both require `U_n(a+k,a-k)`.
12. In the `n=k` outer-positivity calculation, the final numerator is
    `((a-c)(n-c)+a)`, not `((a-c)(n-c)+1)`. The same sentence also reverses
    the lower-type inequality: positivity uses `c ≤ a`.
13. In the Sperner appendix, the two extremal ranks must be
    `⌊n/2⌋` and `⌈n/2⌉`; they coincide when `2 ∣ n`, not when `2 ∤ n`.
14. In the appendix's incidence calculation, the symmetric chains capable of
    meeting `L_i` lie in `𝒞₀ ∪ ⋯ ∪ 𝒞ᵢ`, not the displayed intersection of
    those pairwise-disjoint strata.
15. The displayed general multinomial Pascal recurrence cumulatively lowers
    several arguments and is false.  Each summand should lower exactly one
    argument, alongside the term in which none is lowered; the ternary
    specialization is proved as `Ternary.trinomial_succ`.
16. Whether the exceptional lattice point `(d/2, …, d/2)` exists depends on
    the parity of `d`, not on the parity of `n`.
17. Coordinate reflection in the `d`-ary cube is `𝐝 - x`, where
    `𝐝 = (d, …, d)`, not the displayed `𝐧 - x`.
18. A symmetric ternary basic chain of width `w` runs between layers
    `L_(n-w)` and `L_(n+w)`, not `L_(n/2-w)` and `L_(n/2+w)`.
19. With the paper's zero-based layer indices, the rank complementary to `i`
    is `nd-i`; the preliminary inner-layer paragraph's `nd+1-i` is off by one.
20. In the uniqueness induction, `i` is introduced as distance from the
    middle but then used as an absolute layer index.  The Lean proof uses the
    well-founded distance functions in `DOneEqualityPropagation` and
    `DTwoUniqueness`, avoiding that index conflation.
21. All basic good chains do not form one orbit under coordinate permutation.
    The orbit/uniformity assertion is for a fixed canonical start type and
    trace, formalized by the start-group and metachain declarations.
22. The concluding displayed ternary extremal family should have ambient cube
    `{0,1,2}^n`, not `{0,…,d}^n`.
23. The lower-outer `W_n(a,c)` recurrence also holds on the boundary
    `c+k=a`; the printed strict range `c<a-k` omits it.
24. Immediately before that recurrence, the incidence difference should
    contain `W_n(a+1,c)`, as the labeled equation does, rather than
    `W_n(a+1,c-1)`.
25. The final term in the later-inner recurrence must be
    `-W_n(a-k+1,c+k)`, not `+W_n(a-k+1,c+k)`.  For
    `n=5, k=2, a=c=2`, the corrected recurrence and the defined weight both
    give `2`, whereas the printed plus-sign gives `10`.
26. In the parenthetical discussion of the first inner diagonal
    `c=a-k+1`, the type `(a-k+1,b-1,c+k)` lies on the upper **outer**
    boundary, not in the upper inner region.  It is the reflected endpoint of
    the symmetric metachain starting at `(a+1,b-1,c)`, so there is no separate
    canonical upper start group contributing another recurrence term.
27. In Lean's natural-number arithmetic, the paper's rational inequality
    `n/2 ≤ k` must be encoded as `n ≤ 2k`.  Writing `n / 2 ≤ k` with truncated
    division would be one unit too weak when `n` is odd.  Appendix 2 uses the
    exact former condition and the paper's floor/ceiling coordinate split.
28. The strategy section recalls that `A₁=A₂` “if `2 ∣ d`”.  While sufficient,
    this misses, for example, `d=1` with even `n`.  The exact condition in the
    main theorem is `2 ∣ nd`, and this is the condition formalised by
    `Cube.lowerResidueFinset_eq_upperResidueFinset_of_even`.

## Sources for the setup

The project layout follows the leanprover-community
[`LeanProject`](https://github.com/leanprover-community/LeanProject) template
for blueprint-driven standalone projects, while keeping the existing paper
source at the repository root. Dependency and cache handling follow mathlib's
[“Using mathlib4 as a dependency”](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
guide. `elan` and a project-specific pinned toolchain follow the
[Lean reference manual](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/).
