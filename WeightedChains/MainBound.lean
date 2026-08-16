import WeightedChains.GoodChainResidues
import WeightedChains.WeightedUniqueness

/-!
# The weighted-chain bound with the paper's reference families

These corollaries discharge the abstract `reference` hypothesis in the
weighted-cover strategy using the fact that every good chain contains exactly
one point of each distinguished residue family.
-/

namespace WeightedChains
namespace Chain

variable {n d k : ℕ} {ι : Type*} [Fintype ι]

/-- The cardinality conclusion of Lemma 3.2 with the paper's lower residue
family as the reference family. -/
theorem kSeparated_card_le_lowerResidueFinset
    (chains : ι → Chain n d) (weight : ι → ℝ) (candidate : Finset (Cube n d))
    (hgood : ∀ i, (chains i).Good k)
    (hcover : ∀ x,
      WeightedCover.inducedWeight (fun i ↦ (chains i).vertices) weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n d k).card := by
  apply kSeparated_card_le_of_weighted_chains chains weight
    (Cube.lowerResidueFinset n d k) candidate hgood hcover hnonnegative
  · intro i
    exact (hgood i).card_lowerResidueFinset_inter_vertices (chains i)
  · exact hcandidate

/-- The analogous bound using the upper residue family. -/
theorem kSeparated_card_le_upperResidueFinset
    (chains : ι → Chain n d) (weight : ι → ℝ) (candidate : Finset (Cube n d))
    (hgood : ∀ i, (chains i).Good k)
    (hcover : ∀ x,
      WeightedCover.inducedWeight (fun i ↦ (chains i).vertices) weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k) :
    candidate.card ≤ (Cube.upperResidueFinset n d k).card := by
  apply kSeparated_card_le_of_weighted_chains chains weight
    (Cube.upperResidueFinset n d k) candidate hgood hcover hnonnegative
  · intro i
    exact (hgood i).card_upperResidueFinset_inter_vertices (chains i)
  · exact hcandidate

/-- In the equality case, every positive-weight good chain meets the extremal
candidate exactly once; the lower reference-family hypothesis is automatic. -/
theorem kSeparated_inter_vertices_card_eq_one_of_card_eq_lower
    (chains : ι → Chain n d) (weight : ι → ℝ) (candidate : Finset (Cube n d))
    (hgood : ∀ i, (chains i).Good k)
    (hcover : ∀ x,
      WeightedCover.inducedWeight (fun i ↦ (chains i).vertices) weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n d k).card)
    {i : ι} (hpositive : 0 < weight i) :
    (candidate ∩ (chains i).vertices).card = 1 := by
  apply kSeparated_inter_vertices_card_eq_one_of_positive chains weight
    (Cube.lowerResidueFinset n d k) candidate hgood hcover hnonnegative
  · intro j
    exact (hgood j).card_lowerResidueFinset_inter_vertices (chains j)
  · exact hcandidate
  · exact hcard
  · exact hpositive

end Chain
end WeightedChains
