import WeightedChains.GoodChainResidues

/-!
# Parity of the two middle residue families

When the total cube rank `n*d` is even the lower and upper middle ranks agree,
so the two reference families are literally equal.  When it is odd the two
middle ranks are adjacent.  These elementary facts are useful in the final
equality-case classification.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Cube

theorem lowerMiddleRank_eq_upperMiddleRank_of_even (n d : ℕ)
    (h : Even (n * d)) : lowerMiddleRank n d = upperMiddleRank n d := by
  rcases h with ⟨m, hm⟩
  have hhalf : lowerMiddleRank n d = m := by
    unfold lowerMiddleRank
    rw [hm]
    omega
  unfold upperMiddleRank
  rw [hhalf, hm]
  omega

theorem upperMiddleRank_eq_lowerMiddleRank_add_one_of_odd (n d : ℕ)
    (h : Odd (n * d)) : upperMiddleRank n d = lowerMiddleRank n d + 1 := by
  rcases h with ⟨m, hm⟩
  have hhalf : lowerMiddleRank n d = m := by
    unfold lowerMiddleRank
    rw [hm]
    omega
  unfold upperMiddleRank
  rw [hhalf, hm]
  omega

/-- For even total rank there is only one distinguished residue family. -/
theorem lowerResidueFinset_eq_upperResidueFinset_of_even
    (n d k : ℕ) (h : Even (n * d)) :
    lowerResidueFinset n d k = upperResidueFinset n d k := by
  apply Finset.ext
  intro x
  simp only [lowerResidueFinset, upperResidueFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [lowerMiddleRank_eq_upperMiddleRank_of_even n d h]

end Cube
end WeightedChains
