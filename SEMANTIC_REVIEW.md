# Semantic correspondence review

This document is the sign-off surface for the correspondence between the 21
results linked from `main.tex` and the Lean formalisation: all 18 numbered
mathematical environments, the general asymptotic conclusion, and the two
appendix results. It deliberately excludes unnumbered claims and remarks that
do not carry a PDF link.

The manuscript source locations below were audited against `main.tex` in the
current source tree. Line numbers are navigation aids; the canonical IDs and
declaration names are the stable identifiers, and the final reviewed artifact
commit belongs in the ledger.

## What a sign-off means

Kernel checking and paper correspondence are separate claims:

- **Kernel status:** Lean has accepted the cited declarations. The repository
  audit rejects `sorry`, `admit`, project axioms, opaque proof placeholders,
  unsafe declarations, and partial declarations. It separately permits only
  Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axiom
  dependencies.
- **Semantic status:** a human reviewer has checked that the mathematical
  statement in the manuscript, including its definitions, hypotheses,
  quantifiers, conventions, and intended corrections, says what the cited Lean
  declaration says.

Kernel acceptance does **not** establish semantic correspondence. Every entry
in this document is therefore **pending semantic review** until its ledger row
is signed. Nothing below should be read as an author sign-off.

The correspondence categories are non-exclusive:

- **direct** — the intended paper statement has a direct Lean counterpart;
- **corrected** — Lean states an explicit correction or a necessary hypothesis
  absent or misstated in the current manuscript;
- **factored** — the paper item is represented by several Lean declarations;
- **encoding** — Lean uses a different finite/data representation whose
  intended equivalence requires human confirmation.

Canonical IDs use `wc:<kind>:<slug>`. Their stable blueprint route is
`/theorems/<slug>/`. Existing LaTeX labels remain aliases and must not be
removed.

## Correspondence records

### 1. Theorem 1.1 — main theorem

- **Canonical ID:** `wc:thm:main-theorem`
- **Stable route:** `/theorems/main-theorem/`
- **LaTeX source:** `main.tex:121-139`
- **Existing label alias:** `the_main_theorem`
- **Category:** corrected, encoding
- **Status:** pending semantic review
- **Primary Lean declaration:**
  `WeightedChains.main_cardinality_and_uniqueness`
  (`WeightedChains/MainTheorem.lean:19-42`)
- **Definitions/support:** `WeightedChains.Cube.KSeparated`
  (`WeightedChains/Preliminaries.lean:59-60`),
  `WeightedChains.Cube.lowerResidueFinset` and
  `WeightedChains.Cube.upperResidueFinset`
  (`WeightedChains/GoodChainResidues.lean:18-23`), and
  `WeightedChains.Cube.lowerResidueFinset_eq_upperResidueFinset_of_even`
  (`WeightedChains/ResidueParity.lean:40-47`).
- **Reviewer focus:** Lean represents a family by a `Finset`, which is
  equivalent in the finite cube. It makes the necessary `x != y` condition in
  `k`-separation explicit. Confirm that the bound plus the equality iff in Lean
  is exactly the manuscript's “unique largest families” assertion, including
  the `d = 2` coincidence and the hypotheses `1 < k <= n`.

### 2. Definition 2.1 — chain

- **Canonical ID:** `wc:def:chain`
- **Stable route:** `/theorems/chain/`
- **LaTeX source:** `main.tex:198-204`
- **Existing label alias:** none
- **Category:** direct, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Chain`
  (`WeightedChains/Preliminaries.lean:193-196`) and
  `WeightedChains.Chain.length`
  (`WeightedChains/Preliminaries.lean:203`).
- **Reviewer focus:** Lean stores a nonempty ordered sequence indexed by
  `Fin (steps + 1)` and calls `steps + 1` its length. Confirm that this is the
  paper's ordered chain notion, rather than an unordered set with an order
  inherited afterward.

### 3. Definition 2.2 — chain width

- **Canonical ID:** `wc:def:chain-width`
- **Stable route:** `/theorems/chain-width/`
- **LaTeX source:** `main.tex:206-210`
- **Existing label alias:** none
- **Category:** direct, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Chain.width`
  (`WeightedChains/Preliminaries.lean:224`) and
  `WeightedChains.Cube.hammingDistance`
  (`WeightedChains/Preliminaries.lean:38-39`).
- **Reviewer focus:** confirm that Hamming distance between the first and last
  vertices equals the number of endpoint coordinates satisfying strict
  inequality, using chain monotonicity.

### 4. Definition 2.3 — saturated chain

- **Canonical ID:** `wc:def:saturated-chain`
- **Stable route:** `/theorems/saturated-chain/`
- **LaTeX source:** `main.tex:220-225`
- **Existing label alias:** `saturated_definition`
- **Category:** direct, encoding
- **Status:** pending semantic review
- **Primary Lean declaration:** `WeightedChains.Chain.Saturated`
  (`WeightedChains/Preliminaries.lean:227-228`).
- **Reviewer focus:** Lean expresses saturation as rank increasing by one at
  every adjacent step. Confirm that, for comparable cube vertices, this is
  equivalent to changing exactly one coordinate by one as stated in the paper.

### 5. Definition 2.4 — symmetric chain

- **Canonical ID:** `wc:def:symmetric-chain`
- **Stable route:** `/theorems/symmetric-chain/`
- **LaTeX source:** `main.tex:227-231`
- **Existing label alias:** none
- **Category:** direct, encoding
- **Status:** pending semantic review
- **Primary Lean declaration:** `WeightedChains.Chain.Symmetric`
  (`WeightedChains/Preliminaries.lean:231-232`).
- **Supporting equivalence:** `WeightedChains.Chain.symmetric_iff_endpoint`
  (`WeightedChains/Preliminaries.lean:296-305`) for saturated chains.
- **Reviewer focus:** confirm the reverse-index convention in `Fin.rev` matches
  `x_i` paired with `x_{l+1-i}` in the manuscript.

### 6. Definition 2.5 — layer

- **Canonical ID:** `wc:def:layer`
- **Stable route:** `/theorems/layer/`
- **LaTeX source:** `main.tex:239-246`
- **Existing label alias:** none
- **Category:** direct
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Cube.rank`
  (`WeightedChains/Preliminaries.lean:20`) and
  `WeightedChains.Cube.layer`
  (`WeightedChains/Preliminaries.lean:23`).
- **Reviewer focus:** Lean defines a layer for every natural rank; layers
  outside `0 <= i <= nd` are simply empty. Confirm that this harmless extension
  agrees with the bounded paper definition.

### 7. Definition 2.6 — good chain

- **Canonical ID:** `wc:def:good-chain`
- **Stable route:** `/theorems/good-chain/`
- **LaTeX source:** `main.tex:252-257`
- **Existing label alias:** `good_chain_definition`
- **Category:** direct, encoding
- **Status:** pending semantic review
- **Primary Lean declaration:** `WeightedChains.Chain.Good`
  (`WeightedChains/Preliminaries.lean:246-247`).
- **Supporting consequences:**
  `WeightedChains.Chain.Good.card_lowerResidueFinset_inter_vertices`
  (`WeightedChains/GoodChainResidues.lean:152-163`) and
  `WeightedChains.Chain.Good.card_upperResidueFinset_inter_vertices`
  (`WeightedChains/GoodChainResidues.lean:166-177`).
- **Reviewer focus:** confirm the Lean disjunction “symmetric or length
  `d*k+1`” and the bound `width <= k` match the manuscript, including chains
  satisfying both alternatives.

### 8. Definition 2.7 — a chain starting at an endpoint

- **Canonical ID:** `wc:def:chain-start`
- **Stable route:** `/theorems/chain-start/`
- **LaTeX source:** `main.tex:272-282`
- **Existing label alias:** none
- **Category:** corrected, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Chain.StartsAtFirst`
  (`WeightedChains/Preliminaries.lean:236-237`) and
  `WeightedChains.Chain.StartsAtLast`
  (`WeightedChains/Preliminaries.lean:242-243`).
- **Reviewer focus:** the two displayed inequalities in the manuscript select
  the endpoint *closer* to the middle, while the explanatory sentence and all
  later uses select the endpoint *farther* from the middle. Lean implements the
  latter convention. Equality permits either orientation. This correction
  requires explicit author approval.

### 9. Definition 2.8 — lower and upper sides

- **Canonical ID:** `wc:def:cube-sides`
- **Stable route:** `/theorems/cube-sides/`
- **LaTeX source:** `main.tex:286-290`
- **Existing label alias:** none
- **Category:** direct
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Cube.lowerSide` and
  `WeightedChains.Cube.upperSide`
  (`WeightedChains/PaperDefinitions.lean:17-23`). These use doubled ranks to
  express comparison with `n*d/2` without fractions. In the ternary
  specialization, `WeightedChains.Ternary.rank_le_dimension_iff`
  (`WeightedChains/DTwo/Types.lean:67-71`) identifies the lower half with
  `twoCount x <= zeroCount x`.
- **Reviewer focus:** confirm the fraction-free comparisons at odd total rank.
  The two sides intentionally overlap on the middle layer when `n*d` is even.

### 10. Definition 2.9 — inner and outer layers

- **Canonical ID:** `wc:def:inner-outer-layers`
- **Stable route:** `/theorems/inner-outer-layers/`
- **LaTeX source:** `main.tex:293-297`
- **Existing label alias:** none
- **Category:** corrected, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Cube.InnerLayer` and
  `WeightedChains.Cube.OuterLayer`
  (`WeightedChains/PaperDefinitions.lean:25-36`), with complementarity proved
  by `WeightedChains.Cube.innerLayer_iff_not_outerLayer` (lines 38-40). The
  Boolean case split is also encoded by
  `WeightedChains.DOne.lowerStartingWeight`
  (`WeightedChains/DOne/AuxiliaryWeights.lean:382-383`) and exposed by
  `WeightedChains.DOne.lowerStartingWeight_eq_auxiliaryWeightNat`
  (`WeightedChains/DOne/LayerWeights.lean:80-84`) and
  `WeightedChains.DOne.lowerStartingWeight_eq_innerWeight`
  (`WeightedChains/DOne/LayerWeights.lean:97-100`). The ternary split is encoded
  by `WeightedChains.Ternary.startTypeWeight`
  (`WeightedChains/DTwo/StartingWeights.lean:49-59`) and the arithmetic
  equivalence `WeightedChains.Ternary.TypeCounts.rank_add_le_dimension_iff`
  (`WeightedChains/DTwo/Types.lean:148-152`).
- **Reviewer focus:** the rank complementary to zero-based layer `i` is
  `nd-i`, not the manuscript's `nd+1-i`. Confirm that the corrected length
  comparison yields the Boolean condition `n-k < 2a` and ternary inner
  condition `a < c+k`.

### 11. Definition 2.10 — type

- **Canonical ID:** `wc:def:type`
- **Stable route:** `/theorems/type/`
- **LaTeX source:** `main.tex:309-317`
- **Existing label alias:** none
- **Category:** direct, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Cube.typeOf`
  (`WeightedChains/Preliminaries.lean:30-31`) and
  `WeightedChains.Cube.sum_typeOf`
  (`WeightedChains/Preliminaries.lean:82-85`). The ternary record is
  `WeightedChains.Ternary.TypeCounts`
  (`WeightedChains/DTwo/Types.lean:91-95`) with
  `WeightedChains.Ternary.TypeCounts.ofVertex`
  (`WeightedChains/DTwo/Types.lean:100-104`).
- **Reviewer focus:** a point of `{0,...,d}^n` has `d+1` counts indexed by
  coordinate values, and those counts sum to `n`. Confirm that `typeOf` and the
  specialized ternary record encode this convention directly.

### 12. Proposition 3.1 — existence of a good-chain weighting

- **Canonical ID:** `wc:prop:good-chain-weighting`
- **Stable route:** `/theorems/good-chain-weighting/`
- **LaTeX source:** `main.tex:343-362`
- **Existing label alias:** `the_weights_assigning_proposition`
- **Category:** corrected, factored, encoding
- **Status:** pending semantic review
- **Boolean declarations:**
  `WeightedChains.DOne.BooleanChain.indexedChain`,
  `WeightedChains.DOne.BooleanChain.indexedWeight`,
  `WeightedChains.DOne.BooleanChain.indexedChain_good`,
  `WeightedChains.DOne.BooleanChain.indexedWeight_pos`, and
  `WeightedChains.DOne.BooleanChain.indexedInducedWeight_eq_one`
  (`WeightedChains/DOne/Weights.lean:992-1052`); chain existence is
  `WeightedChains.DOne.BooleanChain.exists_good_containing`
  (`WeightedChains/DOne/ChainExistence.lean:131-141`), with the directed
  uniqueness witnesses
  `WeightedChains.DOne.BooleanChain.exists_towardMiddle_witness_of_mem_lowerResidue`
  and
  `WeightedChains.DOne.BooleanChain.exists_towardMiddle_witness_of_not_mem_lowerResidue`
  (`WeightedChains/DOne/EqualityPropagation.lean:379-430`).
- **Ternary declarations:**
  `WeightedChains.Ternary.BasicChain.indexedChain`,
  `WeightedChains.Ternary.BasicChain.indexedWeight`,
  `WeightedChains.Ternary.BasicChain.indexedChain_good`,
  `WeightedChains.Ternary.BasicChain.indexedWeight_pos_of_start_ne_middle`,
  `WeightedChains.Ternary.BasicChain.indexedWeight_nonneg`, and
  `WeightedChains.Ternary.BasicChain.indexedInducedWeight_eq_one`
  (`WeightedChains/DTwo/Main.lean:25-99`); shortest singletons are supplied by
  `WeightedChains.Ternary.BasicChain.exists_singleton_good_of_rank_eq_dimension`
  (`WeightedChains/DTwo/BasicSufficiency.lean:154-188`); the two incidence
  witnesses are
  `WeightedChains.Ternary.BasicChain.exists_good_with_endpoint_avoiding_middle_of_lowerResidue`
  and `WeightedChains.Ternary.BasicChain.exists_closer_lowerResidue`
  (`WeightedChains/DTwo/BasicSufficiency.lean:545-625`).
- **Reviewer focus:** the current proposition omits the ambient assumptions
  `1 < k <= n`, which the positivity/uniqueness construction needs. Lean uses
  a finite indexed family of represented chains; for `d=2` it assigns weight
  only to basic good chains, equivalently extending by zero to the other good
  chains. Confirm that the component declarations jointly imply all five
  numbered conditions for both `d=1` and `d=2`.

### 13. Lemma 3.2 — weighted cover implies the bound and uniqueness

- **Canonical ID:** `wc:lem:weighted-cover-implies-main`
- **Stable route:** `/theorems/weighted-cover-implies-main/`
- **LaTeX source:** `main.tex:376-383`
- **Existing label alias:** `weights_imply_theorem_lemma`
- **Category:** corrected, factored, encoding
- **Status:** pending semantic review
- **Bound declarations:**
  `WeightedChains.WeightedCover.card_le_of_weighted_cover`
  (`WeightedChains/WeightedStrategy.lean:74-91`) and
  `WeightedChains.Chain.kSeparated_card_le_lowerResidueFinset`
  (`WeightedChains/MainBound.lean:21-33`).
- **Equality declarations:**
  `WeightedChains.Chain.kSeparated_inter_vertices_card_eq_one_of_card_eq_lower`
  (`WeightedChains/MainBound.lean:52-68`) and
  `WeightedChains.UniquenessPropagation.finset_eq_of_positive_weight_outward_induction`
  (`WeightedChains/UniquenessPropagation.lean:104-117`). The ternary
  exceptional-point variant is
  `WeightedChains.UniquenessPropagation.finset_eq_of_active_exact_one_outward_induction_except`
  (`WeightedChains/DTwo/Uniqueness.lean:25-112`).
- **Reviewer focus:** Lean factors the double-counting, exact-one consequence,
  and outward propagation. The manuscript's proof conflates distance from the
  middle with an absolute layer index; Lean replaces it by well-founded
  distance induction. Confirm that the corrected proof establishes precisely
  the lemma's advertised uniqueness implication.

### 14. Lemma 4.1 — Boolean inner starting weight

- **Canonical ID:** `wc:lem:boolean-inner-weight`
- **Stable route:** `/theorems/boolean-inner-weight/`
- **LaTeX source:** `main.tex:528-535`
- **Existing label alias:** none
- **Category:** direct, factored
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.DOne.innerWeight`
  (`WeightedChains/DOne/AuxiliaryWeights.lean:278-279`) and
  `WeightedChains.DOne.lowerStartingWeight_eq_innerWeight`
  (`WeightedChains/DOne/LayerWeights.lean:97-100`).
- **Reviewer focus:** the displayed lemma correctly uses
  `U_n(n-a-k)`. The prose immediately afterward incorrectly switches to
  `U_n(a+k)`; Lean consistently formalizes the displayed, reflection-corrected
  index. Confirm the paper's “lower inner” arithmetic matches the Lean branch.

### 15. Definition 5.1 — basic chain

- **Canonical ID:** `wc:def:basic-chain`
- **Stable route:** `/theorems/basic-chain/`
- **LaTeX source:** `main.tex:618-622`
- **Existing label alias:** none
- **Category:** factored, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Ternary.BasicChain`
  (`WeightedChains/DTwo/Chains.lean:22-26`) and
  `WeightedChains.Ternary.BasicChain.toChain`
  (`WeightedChains/DTwo/Chains.lean:128-131`). The constructed chain's length,
  saturation, and width are proved by
  `WeightedChains.Ternary.BasicChain.toChain_length`,
  `WeightedChains.Ternary.BasicChain.toChain_saturated`, and
  `WeightedChains.Ternary.BasicChain.toChain_width`
  (`WeightedChains/DTwo/Chains.lean:418`, `435-445`, `473-475`).
- **Reviewer focus:** Lean encodes an oriented basic chain by its starting vertex
  and an injective ordered list of zero coordinates, each changed
  `0 -> 1 -> 2`. No theorem currently states an iff between this descriptor
  and every generic chain satisfying the prose block condition; review that
  representation choice explicitly.

### 16. Lemma 5.2 — basic chains suffice

- **Canonical ID:** `wc:lem:basic-chains-suffice`
- **Stable route:** `/theorems/basic-chains-suffice/`
- **LaTeX source:** `main.tex:675-686`
- **Existing label alias:** `positive_basic_enough_lemma`
- **Category:** corrected, factored, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:**
  `WeightedChains.Ternary.BasicChain.exists_singleton_good_of_rank_eq_dimension`
  (`WeightedChains/DTwo/BasicSufficiency.lean:154-188`),
  `WeightedChains.Ternary.BasicChain.exists_good_with_endpoint_avoiding_middle_of_lowerResidue`
  (`WeightedChains/DTwo/BasicSufficiency.lean:545-583`), and
  `WeightedChains.Ternary.BasicChain.exists_closer_lowerResidue`
  (`WeightedChains/DTwo/BasicSufficiency.lean:589-625`). The exceptional
  `(1,n-1,0)` detour is
  `WeightedChains.Ternary.BasicChain.exists_good_containing_avoiding_middle_of_type_one_zero`
  (`WeightedChains/DTwo/BasicSufficiency.lean:296-393`).
- **Reviewer focus:** the manuscript writes undefined `A` where `A_1` is
  intended. Lean separates the central singleton, noncentral reference
  endpoints, and nonreference closer witnesses. For the exceptional type, the
  needed positive chain contains the vertex but does not start there. Confirm
  that this corrected factoring supplies exactly the relevant conditions of
  Proposition 3.1.

### 17. Lemma 5.3 — positivity of ternary auxiliary weights

- **Canonical ID:** `wc:lem:ternary-auxiliary-positive`
- **Stable route:** `/theorems/ternary-auxiliary-positive/`
- **LaTeX source:** `main.tex:773-777`
- **Existing label alias:** none
- **Category:** corrected
- **Status:** pending semantic review
- **Primary Lean declaration:**
  `WeightedChains.Ternary.auxiliaryWeight_pos_of_valid_lower`
  (`WeightedChains/DTwo/WeightPositivity.lean:278-300`), with the natural-index
  form `WeightedChains.Ternary.auxiliaryWeight_pos_of_valid_lower_nat`
  (`WeightedChains/DTwo/WeightPositivity.lean:171-274`).
- **Exceptional value:**
  `WeightedChains.Ternary.auxiliaryWeight_zero_zero`
  (`WeightedChains/DTwo/Weights.lean:156-170`).
- **Reviewer focus:** the printed statement includes `(a,c)=(0,0)`, but
  `U_n(0,0)=0` in every positive dimension. Lean adds
  `(a,c) != (0,0)`. This correction requires explicit author approval.

### 18. Lemma 5.4 — ternary inner starting weight

- **Canonical ID:** `wc:lem:ternary-inner-weight`
- **Stable route:** `/theorems/ternary-inner-weight/`
- **LaTeX source:** `main.tex:833-840`
- **Existing label alias:** none
- **Category:** direct, factored
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Ternary.innerStartingWeight`
  (`WeightedChains/DTwo/InnerWeights.lean:19-20`) and
  `WeightedChains.Ternary.extendedStartTypeWeight_eq_inner_of_lower_inner`
  (`WeightedChains/DTwo/StartingWeightRecurrences.lean:139-162`).
- **Reviewer focus:** confirm the lower-inner hypotheses correspond to
  `c <= a < c+k`, and that the shifted term is exactly `U_n(c+k,a-k)`. A later
  diagonal calculation in the manuscript reverses these arguments, but the
  numbered lemma itself and Lean use the stated order.

### 19. Conclusion — asymptotic maximum density

- **Canonical ID:** `wc:thm:asymptotic-density`
- **Stable route:** `/theorems/asymptotic-density/`
- **LaTeX source:** `main.tex:949-953`
- **Existing label alias:** none
- **Category:** direct, factored, encoding
- **Status:** pending semantic review
- **Primary Lean declarations:** `WeightedChains.Asymptotics.maxKSeparatedCard`
  and `WeightedChains.Asymptotics.maxKSeparatedCard_density_tendsto`
  (`WeightedChains/Asymptotics.lean:34-35`, `471-496`).
- **Reviewer focus:** Lean makes the implicit problem-domain assumptions
  `0 < d` and `0 < k` explicit, defines the extremal number as a maximum over
  finite candidate families, casts the normalized cardinality to the reals,
  and interprets the displayed `o(1)` assertion as convergence along all
  natural dimensions. The manuscript's stated base `n=k` plus step size `k`
  reaches only multiples of `k`; the Lean proof retains every remainder class
  modulo `k` and so proves the full displayed limit. Confirm that this
  reconstructed block-chain argument is the authors' intended proof.

### 20. Appendix A — weighted proof of Sperner's theorem

- **Canonical ID:** `wc:thm:sperner-appendix`
- **Stable route:** `/theorems/sperner-appendix/`
- **LaTeX source:** `main.tex:965-1044`
- **Existing label alias:** `appendix_sperner`
- **Category:** corrected, factored
- **Status:** pending semantic review
- **Primary Lean declarations:**
  `WeightedChains.SpernerAppendix.cardinality_and_uniqueness`,
  `WeightedChains.SpernerAppendix.SymmetricChain.inducedWeight_eq_one`, and
  `WeightedChains.SpernerAppendix.SymmetricChain.weight_le_one`
  (`WeightedChains/Appendices/Sperner.lean`).
- **Reviewer focus:** confirm the small-dimension handling and the final
  equality classification. Lean corrects the incidence sentence at
  `main.tex:1021`: the chain strata capable of meeting a layer form a union,
  not the displayed intersection.

### 21. Appendix B — arbitrary `d` and large `k`

- **Canonical ID:** `wc:thm:large-k-appendix`
- **Stable route:** `/theorems/large-k-appendix/`
- **LaTeX source:** `main.tex:1046-1064`
- **Existing label alias:** `appendix_large_k`
- **Category:** direct, factored
- **Status:** pending semantic review
- **Primary Lean declarations:**
  `WeightedChains.LargeK.lowerResidueFinset_isMaximum`,
  `WeightedChains.LargeK.upperResidueFinset_isMaximum`,
  `WeightedChains.LargeK.kSeparated_card_le_lowerResidueFinset`,
  `WeightedChains.LargeK.deBruijnTengbergenKruyswijk`,
  `WeightedChains.LargeK.cuboid_lowerMiddleLayer_isMaximum`, and
  `WeightedChains.LargeK.cuboid_upperMiddleLayer_isMaximum`
  (`WeightedChains/Appendices/LargeK.lean`).
- **Reviewer focus:** confirm that the natural-number hypothesis `n ≤ 2*k`
  exactly represents the paper's rational `n/2 ≤ k`, together with `k ≤ n`;
  that the result makes no uniqueness claim; and that the cuboid declarations
  faithfully capture the stated coordinate-dependent extension.

## Per-item sign-off ledger

Use a commit hash identifying the exact manuscript/formalisation revision that
was reviewed. An item is signed only after all applicable points in the final
checklist have been checked. `Pending` must not be interpreted as rejection; it
means no semantic sign-off is recorded in this repository yet.

| # | Canonical ID | State | Reviewer | Review date (YYYY-MM-DD) | Reviewed commit | Sign-off / notes |
|---:|---|---|---|---|---|---|
| 1 | `wc:thm:main-theorem` | Pending | — | — | — | — |
| 2 | `wc:def:chain` | Pending | — | — | — | — |
| 3 | `wc:def:chain-width` | Pending | — | — | — | — |
| 4 | `wc:def:saturated-chain` | Pending | — | — | — | — |
| 5 | `wc:def:symmetric-chain` | Pending | — | — | — | — |
| 6 | `wc:def:layer` | Pending | — | — | — | — |
| 7 | `wc:def:good-chain` | Pending | — | — | — | — |
| 8 | `wc:def:chain-start` | Pending | — | — | — | — |
| 9 | `wc:def:cube-sides` | Pending | — | — | — | — |
| 10 | `wc:def:inner-outer-layers` | Pending | — | — | — | — |
| 11 | `wc:def:type` | Pending | — | — | — | — |
| 12 | `wc:prop:good-chain-weighting` | Pending | — | — | — | — |
| 13 | `wc:lem:weighted-cover-implies-main` | Pending | — | — | — | — |
| 14 | `wc:lem:boolean-inner-weight` | Pending | — | — | — | — |
| 15 | `wc:def:basic-chain` | Pending | — | — | — | — |
| 16 | `wc:lem:basic-chains-suffice` | Pending | — | — | — | — |
| 17 | `wc:lem:ternary-auxiliary-positive` | Pending | — | — | — | — |
| 18 | `wc:lem:ternary-inner-weight` | Pending | — | — | — | — |
| 19 | `wc:thm:asymptotic-density` | Pending | — | — | — | — |
| 20 | `wc:thm:sperner-appendix` | Pending | — | — | — | — |
| 21 | `wc:thm:large-k-appendix` | Pending | — | — | — | — |

## Reviewer checklist

For each item before changing `Pending` to `Approved` or
`Approved with recorded correction`:

- [ ] Read the complete linked LaTeX statement or result at the reviewed commit.
- [ ] Resolve every cited fully qualified Lean declaration at that commit.
- [ ] Compare domains, hypotheses, quantifier order, equality/inequality
      direction, indexing, and boundary cases.
- [ ] Check all definitions on which the statement depends, rather than only
      comparing the top-level theorem names.
- [ ] For an **encoding** item, confirm that the Lean representation neither
      omits intended objects nor admits unintended ones.
- [ ] For a **factored** item, confirm that the cited declarations jointly imply
      the complete paper item.
- [ ] For a **corrected** item, approve the correction and ensure the manuscript
      is updated before presenting the correspondence as exact.
- [ ] Record reviewer name, ISO review date, full commit hash, disposition, and
      any caveat in the ledger.
- [ ] Ensure the published theorem page distinguishes “kernel checked” from
      “semantic correspondence reviewed.”
- [ ] Only after sign-off, enable any PDF marker that visually asserts reviewed
      correspondence (for example, a check mark).
