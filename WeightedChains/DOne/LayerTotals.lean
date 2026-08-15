import WeightedChains.DOne.LayerWeights

/-!
# Total weight through Boolean layers

This file formalises the recursive bookkeeping paragraph in Section 4.  When
moving from lower layer `a-1` to `a`, chains starting at `a` enter, chains
starting at `a-k-1` leave, and (for an inner layer) chains starting from the
opposite side at `a+k` enter.  The recurrences for `W_n` make the resulting
total equal to the binomial layer size.
-/

set_option autoImplicit false

namespace WeightedChains
namespace DOne

/-- The layer-total determined by the entry/exit bookkeeping in Section 4.
The intended incidence interpretation is proved after individual chain
weights are constructed. -/
def layerWeightTotal (n k : ℕ) : ℕ → ℤ
  | 0 => startingWeight n k 0
  | a + 1 =>
      layerWeightTotal n k a + startingWeight n k (a + 1) -
          extendedStartingWeight n k (((a + 1 : ℕ) : ℤ) - (k : ℤ) - 1) +
        if n - k < 2 * (a + 1) then
          extendedStartingWeight n k (((a + 1 : ℕ) : ℤ) + (k : ℤ))
        else 0

theorem binomialDifference_succNat (n a : ℕ) :
    binomialDifference n ((a : ℤ) + 1) = (n.choose (a + 1) : ℤ) - n.choose a := by
  unfold binomialDifference
  have hpred : (a : ℤ) + 1 - 1 = (a : ℤ) := by omega
  have hsucc : (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) := by norm_num
  rw [hpred, hsucc, extendedChoose_ofNat, extendedChoose_ofNat]

/-- The bookkeeping total through every lower-side layer is its cardinality.
This is the formal version of “This ensures that the total weight ... through
`L_a` is `binom n a`” in Section 4. -/
theorem layerWeightTotal_eq_choose (n k a : ℕ) (hkn : k ≤ n)
    (hlower : 2 * a ≤ n) :
    layerWeightTotal n k a = n.choose a := by
  induction a with
  | zero =>
      have houter : 2 * 0 ≤ n - k := by omega
      rw [layerWeightTotal, startingWeight_recurrence_outer houter]
      have hnegative : -(k : ℤ) - 1 < 0 := by omega
      norm_num only [Nat.cast_zero, zero_sub]
      rw [extendedStartingWeight_of_neg hnegative]
      simp [binomialDifference, extendedChoose]
  | succ a ih =>
      have hprevLower : 2 * a ≤ n := by omega
      rw [layerWeightTotal, ih hprevLower]
      by_cases hinner : n - k < 2 * (a + 1)
      · rw [if_pos hinner,
          startingWeight_recurrence_inner hkn hinner hlower]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [binomialDifference_succNat]
        ring
      · have houter : 2 * (a + 1) ≤ n - k := by omega
        rw [if_neg hinner, startingWeight_recurrence_outer houter]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [binomialDifference_succNat]
        ring

end DOne
end WeightedChains
