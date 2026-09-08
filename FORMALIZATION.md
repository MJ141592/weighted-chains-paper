# Formalisation notes

The formalisation is a kernel-checked Lean 4 proof of the paper with no `sorry`,
`admit`, custom axioms, opaque proof placeholders, or equality-by-computation
shortcuts. Only declarations which compile with complete proofs are part of the
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
  theorem originating in a project module, while retaining named checks as a
  readable headline inventory. Module provenance also covers private or
  accidentally root-namespaced declarations. There are no axioms declared by
  this project.

The interactive companion under `blueprint/` presents the 20 numbered paper
items and the main unnumbered results with kernel-checked signatures and
commit-pinned source links. Each of the 23 results linked directly from the PDF
notes there how its Lean encoding differs in form from the paper, where it does.

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
| Lower/upper sides and inner/outer layers | `Cube.lowerSide`, `Cube.upperSide`, `Cube.InnerLayer`, `Cube.OuterLayer` | defined; later proofs use equivalent arithmetic forms |
| Saturated-chain rank and length facts | `Chain.rank_vertex_eq`, `Chain.length_le_width_mul_add_one`, `Chain.symmetric_iff_endpoint` | proved |
| Boolean width/length equivalence for saturated chains | `Chain.width_eq_steps_of_saturated`, `Chain.length_eq_width_add_one_of_saturated` | proved |
| A separated family meets a good chain at most once | `Chain.card_inter_vertices_le_one` | proved (from the width condition) |
| Weighted double-counting in Lemma 3.2 | `WeightedCover.card_le_of_weighted_cover` | proved |
| Lemma 3.2, cardinality with the actual reference family | `Chain.kSeparated_card_le_lowerResidueFinset` | proved, conditional only on the weighted cover |
| Equality forces one point on each positive chain | `Chain.kSeparated_inter_vertices_card_eq_one_of_positive` | proved |
| Proposition 3.1, concrete weighted assignments and positivity geometry | `DOne.BooleanChain.indexedInducedWeight_eq_one`, `DOne.BooleanChain.indexedWeight_pos`, `Ternary.BasicChain.indexedInducedWeight_eq_one`, `Ternary.BasicChain.indexedWeight_nonneg`, and the `DOne.EqualityPropagation`/`DTwo.BasicSufficiency` witnesses | proved componentwise for `d = 1,2` |
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
| Section 5, basic-chain sufficiency (Lemma 5.2) geometry | `Ternary.BasicChain.exists_good_containing_avoiding_middle`, `Ternary.BasicChain.exists_closer_lowerResidue` | proved |
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
| Section 5, positivity of `U_n(a,c)` (Lemma 5.3) | `Ternary.auxiliaryWeight_pos_of_valid_lower` | proved |
| Section 5, positivity of inner starting weights (Lemma 5.5) | `Ternary.innerStartingWeight_pos_of_valid_lower_inner` | proved |
| Section 5, full reflected start-type total and positivity | `Ternary.startTypeWeight`, `Ternary.startTypeWeight_pos` | proved |
| Section 5, the three pointwise `W_n(a,c)` recurrences | `Ternary.startTypeWeight_recurrence_lower_outer`, `Ternary.startTypeWeight_recurrence_lowest_lower_inner`, `Ternary.startTypeWeight_recurrence_lower_inner` | proved with integer zero-extension |
| Section 5, concrete distributed weighting covers every ternary vertex | `Ternary.BasicChain.inducedWeight_startTypeTotal_eq_one` | proved |
| Main theorem, `d = 2` cardinality bound | `Ternary.BasicChain.kSeparated_card_le_lowerResidueFinset` | proved |
| Main theorem, `d = 2` exceptional-point-aware outward uniqueness | `Ternary.BasicChain.eq_lowerResidueFinset_of_card_eq` | proved |
| Main theorem, complete `d = 2` bound and equality classification | `Ternary.BasicChain.cardinality_and_uniqueness` | proved |
| Main theorem, unified statement for `d \in {1,2}` | `main_cardinality_and_uniqueness` | proved |
| Conclusion: arbitrary-`d` asymptotic maximum density | `Asymptotics.maxKSeparatedCard`, `Asymptotics.maxKSeparatedCard_density_tendsto` | proved for fixed positive `d,k`, along all natural dimensions |
| Appendix: weighted proof of Sperner, including exact chain collection, local telescoping incidence, `(0,1]` weight range, and equality classification | `SpernerAppendix.SymmetricChain.indexEquivSymmetricChains`, `SpernerAppendix.SymmetricChain.weight_eq_choose_sub_previous_div_card`, `SpernerAppendix.SymmetricChain.inducedWeight_eq_one`, `SpernerAppendix.SymmetricChain.weight_le_one`, `SpernerAppendix.cardinality_and_uniqueness` | final bound/classification proved for every `n`; intermediate positive-weight statements carry their mathematically necessary small-`n` hypotheses |
| Appendix: arbitrary `d`, `n/2 ≤ k ≤ n` optimality of both `A₁` and `A₂` | `LargeK.lowerResidueFinset_eq_middleLayer`, `LargeK.kSeparated_card_le_lowerResidueFinset`, `LargeK.lowerResidueFinset_isMaximum`, `LargeK.upperResidueFinset_isMaximum` | proved internally, including the required symmetric-chain decomposition rather than assuming its existence |

## Encoding notes

The Lean statements follow the paper. The points below are the places where the
formal statement is phrased differently from the manuscript, or carries a
hypothesis that the manuscript leaves implicit.

1. The paper's rational inequality `n/2 ≤ k` in Appendix B is encoded as
   `n ≤ 2k`, which is exact; writing `n / 2 ≤ k` with truncated natural-number
   division would be one unit too weak when `n` is odd.
2. The asymptotic result in the conclusion is proved as a real-valued limit
   along every natural dimension `n`. The recurrence
   `A(n+k) ≤ (d+1)^n + ((d+1)^k - (dk+1)) A(n)` is proved for every `n ≥ 0`,
   so the induction starts from the trivial bound `A(r) ≤ (d+1)^r` for the
   remainder `r = n mod k` rather than from the paper's base cases
   `k ≤ n ≤ 2k-1`; the two choices differ only by one step of the recurrence.
3. The uniqueness induction of Lemma 3.2 is carried out by well-founded
   induction on the distance from the middle of the cube
   (`DOne.EqualityPropagation`, `DTwo.Uniqueness`).
4. The Palomar `Challenge` statements avoid every project definition: the cube
   is `Fin n → Fin (d + 1)`, the rank is `∑ i, (x i : ℕ)`, comparability is
   `∀ i, x i ≤ y i`, the number of differing coordinates is a `Finset.filter`
   cardinality, and the residues `⌊nd/2⌋`, `⌈nd/2⌉` are written with
   natural-number division as `n * d / 2` and `n * d - n * d / 2`. The
   asymptotic statement characterises the maximum cardinality by an
   `IsGreatest` hypothesis rather than by a definition; `Solution.lean` shows
   the two formulations agree.

## Sources for the setup

The project layout follows the leanprover-community
[`LeanProject`](https://github.com/leanprover-community/LeanProject) template
for blueprint-driven standalone projects, while keeping the existing paper
source at the repository root. Dependency and cache handling follow mathlib's
[“Using mathlib4 as a dependency”](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
guide. `elan` and a project-specific pinned toolchain follow the
[Lean reference manual](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Managing-Toolchains-with-Elan/).
