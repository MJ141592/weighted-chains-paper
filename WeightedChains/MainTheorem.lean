import WeightedChains.DOne.Uniqueness
import WeightedChains.DTwo.Uniqueness

/-!
# The main theorem

This module packages the separately constructed Boolean and ternary weighted
covers into the paper's single statement for `d ∈ {1,2}`.
-/

set_option autoImplicit false

namespace WeightedChains

/-- The paper's main cardinality and equality-classification theorem.  Every
`k`-separated family in dimension `d = 1` or `d = 2` is bounded by the lower
rank-residue family, and equality gives one of the two reflected residue
families.  When `d = 2` those two families coincide. -/
theorem main_cardinality_and_uniqueness
    (n k d : ℕ) (hk : 1 < k) (hkn : k ≤ n) (hd : d = 1 ∨ d = 2)
    (candidate : Finset (Cube n d))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n d k).card ∧
      (candidate.card = (Cube.lowerResidueFinset n d k).card ↔
        candidate = Cube.lowerResidueFinset n d k ∨
          candidate = Cube.upperResidueFinset n d k) := by
  rcases hd with rfl | rfl
  · obtain ⟨hbound, hequality⟩ :=
      DOne.BooleanChain.cardinality_and_uniqueness
        k n hk hkn candidate hcandidate
    exact ⟨hbound, hequality⟩
  · obtain ⟨hbound, hequality⟩ :=
      Ternary.BasicChain.cardinality_and_uniqueness
        k n hk hkn candidate hcandidate
    refine ⟨hbound, ?_⟩
    constructor
    · exact fun hcard => Or.inl (hequality.1 hcard)
    · rintro (rfl | rfl)
      · rfl
      · exact (Cube.card_lowerResidueFinset_eq_card_upperResidueFinset
          (n := n) (d := 2) (k := k)).symm

end WeightedChains
