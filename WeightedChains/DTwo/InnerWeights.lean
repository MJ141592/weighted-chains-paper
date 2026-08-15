import WeightedChains.DTwo.WeightPascalLower

/-!
# The ternary inner starting-weight difference

For a lower inner type, Section 5 identifies its starting total with
`U_n(a,c) - U_n(c+k,a-k)`.  This file isolates that difference and proves the
dimension recurrence needed for its eventual positivity induction.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Ternary

/-- The paper's closed expression for the total weight starting at a lower
inner type.  Integer coordinates retain the zero-extension conventions of
`auxiliaryWeight`. -/
def innerStartingWeight (n k : ℕ) (a c : ℤ) : ℤ :=
  auxiliaryWeight n k a c - auxiliaryWeight n k (c + k) (a - k)

/-- The inner difference inherits a three-term dimension recurrence whenever
the auxiliary Pascal identity is available at the type and its reflected
shift. -/
theorem innerStartingWeight_succ_of_pascal {n k : ℕ} {a c : ℤ}
    (hmain : AuxiliaryWeightPascal n k a c)
    (hshift : AuxiliaryWeightPascal n k (c + k) (a - k)) :
    innerStartingWeight (n + 1) k a c =
      innerStartingWeight n k (a - 1) c + innerStartingWeight n k a c +
        innerStartingWeight n k a (c - 1) := by
  have ha : (a - 1) - k = a - k - 1 := by ring
  have hc : (c - 1) + k = c + k - 1 := by ring
  unfold innerStartingWeight AuxiliaryWeightPascal at *
  rw [ha, hc, hmain, hshift]
  ring

/-- On every valid natural lower inner type, the hypotheses of the preceding
recurrence follow from the lower-type Pascal theorem and the ghost-boundary
lemmas. -/
theorem innerStartingWeight_succ_of_valid_inner
    (n k a c : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (hca : c ≤ a) (hvalid : a + c ≤ n + 1) (hinner : a < c + k) :
    innerStartingWeight (n + 1) k a c =
      innerStartingWeight n k ((a : ℤ) - 1) c +
        innerStartingWeight n k a c +
          innerStartingWeight n k a ((c : ℤ) - 1) := by
  apply innerStartingWeight_succ_of_pascal
  · exact auxiliaryWeightPascal_of_valid_lower_nat n k a c hk hkn hca hvalid
  · by_cases hka : k ≤ a
    · have hlowerShift : a - k ≤ c + k := by omega
      have hvalidShift : (c + k) + (a - k) ≤ n + 1 := by omega
      have hpascal := auxiliaryWeightPascal_of_valid_lower_nat
        n k (c + k) (a - k) hk hkn hlowerShift hvalidShift
      simpa only [Nat.cast_add, Nat.cast_sub hka] using hpascal
    · apply auxiliaryWeightPascal_of_neg_right
      omega

/-- In the initial dimension `n=k`, the shifted term of every valid inner
type is outside the type triangle, so the inner expression is just `U_k`. -/
theorem innerStartingWeight_initial (k a c : ℕ) (_hk : 0 < k)
    (hvalid : a + c ≤ k) (hinner : a < c + k) :
    innerStartingWeight k k a c = auxiliaryWeight k k a c := by
  unfold innerStartingWeight
  have hka : a < k := by omega
  rw [auxiliaryWeight_eq_zero_of_neg_right (by
    omega : (a : ℤ) - k < 0)]
  omega

end Ternary
end WeightedChains
