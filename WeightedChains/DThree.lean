import WeightedChains.Appendices.LargeK

/-!
# The equal-sided `d = 3` extension

The unrestricted `d = 3` conjecture is not proved here.  This file records
the strongest theorem currently available in the formal development: the
full cardinality statement in the Appendix-B range `n ≤ 2 * k`, specialized
to the four-level cube.  The first genuinely open parameters are therefore
outside this theorem.
-/

namespace WeightedChains

namespace DThree

/-/ In the Appendix-B range, every 2-separated family in `{0,1,2,3}^n` is
at most the lower rank-residue family. -/
theorem card_le_lower_residue
    (n k : ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n)
    (A : Finset (Cube n 3))
    (hA : Cube.KSeparated (A : Set (Cube n 3)) k) :
    A.card ≤ (Cube.lowerResidueFinset n 3 k).card := by
  exact LargeK.kSeparated_card_le_lowerResidueFinset
    n 3 k hhalf hkn A hA

/-/ The lower and upper residue constructions are themselves separated. -/
theorem lower_and_upper_separated (n k : ℕ) :
    Cube.KSeparated (Cube.lowerResidueFinset n 3 k : Set (Cube n 3)) k ∧
      Cube.KSeparated (Cube.upperResidueFinset n 3 k : Set (Cube n 3)) k := by
  exact ⟨LargeK.lowerResidueFinset_kSeparated n 3 k,
    LargeK.upperResidueFinset_kSeparated n 3 k⟩

/-/ Hence the lower residue family is maximum whenever `n ≤ 2*k`. -/
theorem lower_is_maximum
    (n k : ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n) :
    Cube.KSeparated (Cube.lowerResidueFinset n 3 k : Set (Cube n 3)) k ∧
      ∀ A : Finset (Cube n 3),
        Cube.KSeparated (A : Set (Cube n 3)) k →
          A.card ≤ (Cube.lowerResidueFinset n 3 k).card := by
  exact LargeK.lowerResidueFinset_isMaximum n 3 k hhalf hkn

/-/ The reflected upper residue family has the same maximum cardinality. -/
theorem upper_is_maximum
    (n k : ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n) :
    Cube.KSeparated (Cube.upperResidueFinset n 3 k : Set (Cube n 3)) k ∧
      ∀ A : Finset (Cube n 3),
        Cube.KSeparated (A : Set (Cube n 3)) k →
          A.card ≤ (Cube.upperResidueFinset n 3 k).card := by
  exact LargeK.upperResidueFinset_isMaximum n 3 k hhalf hkn

end DThree

end WeightedChains
