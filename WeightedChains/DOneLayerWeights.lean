import WeightedChains.DOne

/-!
# Layer-indexed weights for `d = 1`

Section 4 first constructs the total weight of chains starting on the lower
side of the Boolean cube, then obtains the upper-side values by reflection.
This file packages that reflection and records the two recursive equations in
the paper's notation.  Distribution of these totals among individual chains
is handled separately.
-/

set_option autoImplicit false

namespace WeightedChains
namespace DOne

/-- The reflection orbit of a layer has a unique representative on the lower
side of the Boolean cube. -/
def lowerRepresentative (n a : ℕ) : ℕ := min a (n - a)

theorem lowerRepresentative_eq_self {n a : ℕ} (ha : 2 * a ≤ n) :
    lowerRepresentative n a = a := by
  unfold lowerRepresentative
  rw [min_eq_left]
  omega

theorem lowerRepresentative_reflect {n a : ℕ} (ha : a ≤ n) :
    lowerRepresentative n (n - a) = lowerRepresentative n a := by
  unfold lowerRepresentative
  have hsub : n - (n - a) = a := by omega
  rw [hsub, min_comm]

theorem lowerRepresentative_le_half {n a : ℕ} (ha : a ≤ n) :
    2 * lowerRepresentative n a ≤ n := by
  have hleft : lowerRepresentative n a ≤ a := min_le_left _ _
  have hright : lowerRepresentative n a ≤ n - a := min_le_right _ _
  omega

/-- The total weight `W_n(a)` at an arbitrary layer, obtained from the lower
side assignment by reflection. -/
def startingWeight (n k a : ℕ) : ℤ :=
  lowerStartingWeight n k (lowerRepresentative n a)

theorem startingWeight_eq_lower {n k a : ℕ} (ha : 2 * a ≤ n) :
    startingWeight n k a = lowerStartingWeight n k a := by
  rw [startingWeight, lowerRepresentative_eq_self ha]

theorem startingWeight_reflect {n k a : ℕ} (ha : a ≤ n) :
    startingWeight n k (n - a) = startingWeight n k a := by
  rw [startingWeight, startingWeight, lowerRepresentative_reflect ha]

theorem startingWeight_pos (k n a : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (ha : a ≤ n) :
    0 < startingWeight n k a := by
  exact lowerStartingWeight_pos k n (lowerRepresentative n a) hk hkn
    (lowerRepresentative_le_half ha)

/-- Extend `W_n` by zero outside the actual layer range. This makes the
boundary cases of the recursive equations uniform. -/
def extendedStartingWeight (n k : ℕ) (a : ℤ) : ℤ :=
  if 0 ≤ a ∧ a ≤ n then startingWeight n k a.toNat else 0

@[simp]
theorem extendedStartingWeight_ofNat {n k a : ℕ} (ha : a ≤ n) :
    extendedStartingWeight n k a = startingWeight n k a := by
  simp [extendedStartingWeight, ha]

@[simp]
theorem extendedStartingWeight_of_neg {n k : ℕ} {a : ℤ} (ha : a < 0) :
    extendedStartingWeight n k a = 0 := by
  simp [extendedStartingWeight, ha]

@[simp]
theorem extendedStartingWeight_of_gt {n k : ℕ} {a : ℤ} (ha : (n : ℤ) < a) :
    extendedStartingWeight n k a = 0 := by
  simp [extendedStartingWeight, ha]

/-- On a lower outer layer, `W_n(a)` is the auxiliary value `U_n(a)`. -/
theorem lowerStartingWeight_eq_auxiliaryWeightNat {n k a : ℕ}
    (houter : 2 * a ≤ n - k) :
    lowerStartingWeight n k a = auxiliaryWeightNat n k a := by
  rw [lowerStartingWeight, if_neg]
  omega

/-- Equation (4.1) for a lower outer layer. Negative predecessor indices are
represented by the integer-indexed extension of `U_n`. -/
theorem lowerStartingWeight_recurrence_outer {n k a : ℕ}
    (houter : 2 * a ≤ n - k) :
    lowerStartingWeight n k a =
      binomialDifference n a + auxiliaryWeight n k ((a : ℤ) - (k : ℤ) - 1) := by
  rw [lowerStartingWeight_eq_auxiliaryWeightNat houter]
  exact auxiliaryWeight_recurrence_ofNat n k a

/-- On a lower inner layer, `W_n(a)` is the difference of the two auxiliary
weights identified in the corrected form of the paper's lemma. -/
theorem lowerStartingWeight_eq_innerWeight {n k a : ℕ}
    (hinner : n - k < 2 * a) :
    lowerStartingWeight n k a = innerWeight n k a := by
  simp [lowerStartingWeight, hinner]

/-- Equation (4.2) after replacing both outer-layer terms by their auxiliary
weights.  The final index is `n-a-k`, as required by reflection. -/
theorem lowerStartingWeight_recurrence_inner {n k a : ℕ}
    (hinner : n - k < 2 * a) :
    lowerStartingWeight n k a =
      binomialDifference n a + auxiliaryWeight n k ((a : ℤ) - (k : ℤ) - 1) -
        auxiliaryWeight n k ((n : ℤ) - (a : ℤ) - (k : ℤ)) := by
  rw [lowerStartingWeight_eq_innerWeight hinner]
  unfold innerWeight
  rw [auxiliaryWeight_recurrence_ofNat]

/-- For a lower inner layer, the chains entering from the upper starting layer
`a+k` carry the reflected outer total `U_n(n-a-k)`. Both sides vanish when
`a+k` lies beyond the top of the cube. -/
theorem extendedStartingWeight_add_eq_auxiliaryWeight {n k a : ℕ}
    (hkn : k ≤ n) (hinner : n - k < 2 * a) :
    extendedStartingWeight n k ((a : ℤ) + (k : ℤ)) =
      auxiliaryWeight n k ((n : ℤ) - (a : ℤ) - (k : ℤ)) := by
  by_cases hsum : a + k ≤ n
  · have hsumInt : (a : ℤ) + (k : ℤ) = ((a + k : ℕ) : ℤ) := by norm_num
    have hindex : (n : ℤ) - (a : ℤ) - (k : ℤ) = ((n - (a + k) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hsum]
      push_cast
      ring
    have hrepresentative : lowerRepresentative n (a + k) = n - (a + k) := by
      unfold lowerRepresentative
      rw [min_eq_right]
      omega
    have houter : 2 * (n - (a + k)) ≤ n - k := by omega
    rw [hsumInt, extendedStartingWeight_ofNat hsum, startingWeight,
      hrepresentative, lowerStartingWeight_eq_auxiliaryWeightNat houter,
      hindex, auxiliaryWeight_ofNat]
  · have hsumNat : n < a + k := Nat.lt_of_not_ge hsum
    have hsumInt : (n : ℤ) < (a : ℤ) + (k : ℤ) := by exact_mod_cast hsumNat
    have hnegative : (n : ℤ) - (a : ℤ) - (k : ℤ) < 0 := by omega
    rw [extendedStartingWeight_of_gt hsumInt, auxiliaryWeight_of_neg n k hnegative]

/-- Looking `k+1` layers down from any lower-side layer still reaches an
outer layer (or leaves the cube), so its starting total is the corresponding
auxiliary weight. -/
theorem extendedStartingWeight_sub_eq_auxiliaryWeight {n k a : ℕ}
    (hlower : 2 * a ≤ n) :
    extendedStartingWeight n k ((a : ℤ) - (k : ℤ) - 1) =
      auxiliaryWeight n k ((a : ℤ) - (k : ℤ) - 1) := by
  by_cases hpred : k + 1 ≤ a
  · have hindex : (a : ℤ) - (k : ℤ) - 1 = ((a - (k + 1) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hpred]
      push_cast
      ring
    have hpredLayer : a - (k + 1) ≤ n := by omega
    have hpredHalf : 2 * (a - (k + 1)) ≤ n := by omega
    have hpredOuter : 2 * (a - (k + 1)) ≤ n - k := by omega
    rw [hindex, extendedStartingWeight_ofNat hpredLayer,
      startingWeight_eq_lower hpredHalf,
      lowerStartingWeight_eq_auxiliaryWeightNat hpredOuter,
      auxiliaryWeight_ofNat]
  · have hnegative : (a : ℤ) - (k : ℤ) - 1 < 0 := by
      have hpred' : a < k + 1 := Nat.lt_of_not_ge hpred
      exact_mod_cast (show (a : ℤ) - (k : ℤ) - 1 < 0 by omega)
    rw [extendedStartingWeight_of_neg hnegative,
      auxiliaryWeight_of_neg n k hnegative]

/-- The outer-layer recursion stated entirely in terms of the reflected layer
totals `W_n`. -/
theorem startingWeight_recurrence_outer {n k a : ℕ}
    (houter : 2 * a ≤ n - k) :
    startingWeight n k a =
      binomialDifference n a +
        extendedStartingWeight n k ((a : ℤ) - (k : ℤ) - 1) := by
  have hlower : 2 * a ≤ n := houter.trans (Nat.sub_le n k)
  rw [startingWeight_eq_lower hlower,
    lowerStartingWeight_recurrence_outer houter,
    extendedStartingWeight_sub_eq_auxiliaryWeight hlower]

/-- The inner-layer recursion stated exactly as Equation (4.2): compared with
the previous layer, chains start at `a`, leave at `a-k-1`, and enter from the
opposite side at `a+k`. -/
theorem startingWeight_recurrence_inner {n k a : ℕ}
    (hkn : k ≤ n) (hinner : n - k < 2 * a) (hlower : 2 * a ≤ n) :
    startingWeight n k a =
      binomialDifference n a +
          extendedStartingWeight n k ((a : ℤ) - (k : ℤ) - 1) -
        extendedStartingWeight n k ((a : ℤ) + (k : ℤ)) := by
  rw [startingWeight_eq_lower hlower,
    lowerStartingWeight_recurrence_inner hinner,
    extendedStartingWeight_sub_eq_auxiliaryWeight hlower,
    extendedStartingWeight_add_eq_auxiliaryWeight hkn hinner]

end DOne
end WeightedChains
