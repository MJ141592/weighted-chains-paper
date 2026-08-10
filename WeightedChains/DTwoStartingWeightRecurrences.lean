import WeightedChains.DTwoStartingWeights

/-!
# Pointwise recurrences for ternary starting weights

This module states the three recurrences displayed in Section 5 directly in
terms of the paper's total starting weight `W_n(a,c)`.  As in the paper, the
coordinates are extended by zero outside the type triangle.  The extension is
also useful for the shifted terms with negative coordinates which occur near
the boundary.

The lower-outer equation holds on the closed range `c + k ≤ a`, including the
boundary `c + k = a`.  At a strictly inner type, both reflected incoming terms
are subtracted.  Thus the final sign in the printed version of
`the_key_recursion_inner` must be `-`, in agreement with the cancellation in
the proof immediately following it.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary

/-- The type with `a` zero coordinates and `c` two coordinates. -/
def coordinateType (n a c : ℕ) (hvalid : a + c ≤ n) : TypeCounts n where
  zeros := a
  ones := n - a - c
  twos := c
  sum_eq := by omega

@[simp] theorem coordinateType_zeros (n a c : ℕ) (hvalid : a + c ≤ n) :
    (coordinateType n a c hvalid).zeros = a := rfl

@[simp] theorem coordinateType_twos (n a c : ℕ) (hvalid : a + c ≤ n) :
    (coordinateType n a c hvalid).twos = c := rfl

/-- The paper's `W_n(a,c)`, extended by zero outside the triangle of valid
types.  Inside the triangle this is exactly `startTypeWeight`, written in
coordinates rather than as a `TypeCounts` structure. -/
def extendedStartTypeWeight (n k : ℕ) (a c : ℤ) : ℤ :=
  if 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n then
    if c ≤ a then
      if c + k ≤ a then
        auxiliaryWeight n k a c
      else
        innerStartingWeight n k a c
    else
      if a + k ≤ c then
        auxiliaryWeight n k c a
      else
        innerStartingWeight n k c a
  else
    0

/-- On natural valid coordinates, the integer-indexed extension is the
`TypeCounts`-indexed starting total already used by the weighted cover. -/
@[simp]
theorem extendedStartTypeWeight_ofNat (n k a c : ℕ) (hvalid : a + c ≤ n) :
    extendedStartTypeWeight n k a c =
      startTypeWeight k (coordinateType n a c hvalid) := by
  have hvalidInt :
      0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) + (c : ℤ) ≤ n := by
    omega
  unfold extendedStartTypeWeight startTypeWeight
  rw [if_pos hvalidInt]
  simp only [coordinateType_zeros, coordinateType_twos]
  by_cases hlower : c ≤ a
  · have hlowerInt : (c : ℤ) ≤ a := by omega
    by_cases houter : c + k ≤ a
    · have houterInt : (c : ℤ) + (k : ℤ) ≤ a := by omega
      simp [hlower, hlowerInt, houter, houterInt]
    · have houterInt : ¬((c : ℤ) + (k : ℤ) ≤ a) := by omega
      simp [hlower, hlowerInt, houter, houterInt]
  · have hlowerInt : ¬((c : ℤ) ≤ a) := by omega
    by_cases houter : a + k ≤ c
    · have houterInt : (a : ℤ) + (k : ℤ) ≤ c := by omega
      simp [hlower, hlowerInt, houter, houterInt]
    · have houterInt : ¬((a : ℤ) + (k : ℤ) ≤ c) := by omega
      simp [hlower, hlowerInt, houter, houterInt]

@[simp]
theorem extendedStartTypeWeight_eq_zero_of_neg_left {n k : ℕ} {a c : ℤ}
    (ha : a < 0) : extendedStartTypeWeight n k a c = 0 := by
  simp [extendedStartTypeWeight, show ¬(0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n) by omega]

@[simp]
theorem extendedStartTypeWeight_eq_zero_of_neg_right {n k : ℕ} {a c : ℤ}
    (hc : c < 0) : extendedStartTypeWeight n k a c = 0 := by
  simp [extendedStartTypeWeight, show ¬(0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n) by omega]

@[simp]
theorem extendedStartTypeWeight_eq_zero_of_lt_add {n k : ℕ} {a c : ℤ}
    (h : (n : ℤ) < a + c) : extendedStartTypeWeight n k a c = 0 := by
  simp [extendedStartTypeWeight, show ¬(0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n) by omega]

/-- Every zero-extended lower-outer starting weight is the corresponding
auxiliary weight.  No validity hypothesis is needed: both sides vanish
outside the type triangle. -/
theorem extendedStartTypeWeight_eq_auxiliary_of_lower_outer
    {n k : ℕ} {a c : ℤ} (houter : c + k ≤ a) :
    extendedStartTypeWeight n k a c = auxiliaryWeight n k a c := by
  by_cases ha : a < 0
  · rw [extendedStartTypeWeight_eq_zero_of_neg_left ha,
      auxiliaryWeight_eq_zero_of_neg_left ha]
  by_cases hc : c < 0
  · rw [extendedStartTypeWeight_eq_zero_of_neg_right hc,
      auxiliaryWeight_eq_zero_of_neg_right hc]
  by_cases hsum : (n : ℤ) < a + c
  · rw [extendedStartTypeWeight_eq_zero_of_lt_add hsum,
      auxiliaryWeight_eq_zero_of_lt_add hsum]
  have hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n := by omega
  have hlower : c ≤ a := by omega
  simp [extendedStartTypeWeight, hvalid, hlower, houter]

/-- The reflected version of the preceding lower-outer identification. -/
theorem extendedStartTypeWeight_eq_auxiliary_of_upper_outer
    {n k : ℕ} {a c : ℤ} (houter : a + k ≤ c) :
    extendedStartTypeWeight n k a c = auxiliaryWeight n k c a := by
  by_cases ha : a < 0
  · rw [extendedStartTypeWeight_eq_zero_of_neg_left ha,
      auxiliaryWeight_eq_zero_of_neg_right ha]
  by_cases hc : c < 0
  · rw [extendedStartTypeWeight_eq_zero_of_neg_right hc,
      auxiliaryWeight_eq_zero_of_neg_left hc]
  by_cases hsum : (n : ℤ) < a + c
  · rw [extendedStartTypeWeight_eq_zero_of_lt_add hsum,
      auxiliaryWeight_eq_zero_of_lt_add (by omega : (n : ℤ) < c + a)]
  have hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n := by omega
  by_cases hlower : c ≤ a
  · have hac : a = c := by omega
    subst c
    simp [extendedStartTypeWeight, hvalid, houter]
  · simp [extendedStartTypeWeight, hvalid, hlower, houter]

/-- Every zero-extended lower-inner starting weight is the auxiliary
difference from Section 5. -/
theorem extendedStartTypeWeight_eq_inner_of_lower_inner
    {n k : ℕ} {a c : ℤ} (hlower : c ≤ a) (hinner : a < c + k) :
    extendedStartTypeWeight n k a c = innerStartingWeight n k a c := by
  by_cases ha : a < 0
  · rw [extendedStartTypeWeight_eq_zero_of_neg_left ha]
    unfold innerStartingWeight
    rw [auxiliaryWeight_eq_zero_of_neg_left ha,
      auxiliaryWeight_eq_zero_of_neg_right (by omega : a - k < 0)]
    ring
  by_cases hc : c < 0
  · rw [extendedStartTypeWeight_eq_zero_of_neg_right hc]
    unfold innerStartingWeight
    rw [auxiliaryWeight_eq_zero_of_neg_right hc,
      auxiliaryWeight_eq_zero_of_neg_right (by omega : a - k < 0)]
    ring
  by_cases hsum : (n : ℤ) < a + c
  · rw [extendedStartTypeWeight_eq_zero_of_lt_add hsum]
    unfold innerStartingWeight
    rw [auxiliaryWeight_eq_zero_of_lt_add hsum,
      auxiliaryWeight_eq_zero_of_lt_add (by omega : (n : ℤ) < (c + k) + (a - k))]
    ring
  have hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n := by omega
  have hnotOuter : ¬c + k ≤ a := by omega
  simp [extendedStartTypeWeight, hvalid, hlower, hnotOuter]

/-- Equation `the_key_recursive_equation`, with its corrected closed
lower-outer range `c + k ≤ a`. -/
theorem extendedStartTypeWeight_recurrence_lower_outer
    {n k : ℕ} {a c : ℤ}
    (hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n)
    (houter : c + k ≤ a) :
    extendedStartTypeWeight n k a c =
      extendedTrinomial n a c - extendedTrinomial n (a + 1) (c - 1) -
          extendedStartTypeWeight n k (a + 1) c +
        extendedStartTypeWeight n k (a + k + 1) (c - k) +
        extendedStartTypeWeight n k (a + k + 1) (c - k - 1) := by
  rw [extendedStartTypeWeight_eq_auxiliary_of_lower_outer houter,
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show c + k ≤ a + 1 by omega),
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show (c - k) + k ≤ a + k + 1 by omega),
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show (c - k - 1) + k ≤ a + k + 1 by omega)]
  exact auxiliaryWeight_recursion_of_valid hvalid

/-- Equation `the_key_recursion_lowest_inner`.  The equality
`c + k = a + 1` describes the first lower-inner diagonal. -/
theorem extendedStartTypeWeight_recurrence_lowest_lower_inner
    {n k : ℕ} {a c : ℤ}
    (hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n)
    (hlower : c ≤ a) (hlowest : c + k = a + 1) :
    extendedStartTypeWeight n k a c =
      extendedTrinomial n a c - extendedTrinomial n (a + 1) (c - 1) -
          extendedStartTypeWeight n k (a + 1) c +
        extendedStartTypeWeight n k (a + k + 1) (c - k) +
        extendedStartTypeWeight n k (a + k + 1) (c - k - 1) -
        extendedStartTypeWeight n k (a - k) (c + k) := by
  rw [extendedStartTypeWeight_eq_inner_of_lower_inner hlower (by omega),
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show c + k ≤ a + 1 by omega),
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show (c - k) + k ≤ a + k + 1 by omega),
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show (c - k - 1) + k ≤ a + k + 1 by omega),
    extendedStartTypeWeight_eq_auxiliary_of_upper_outer
      (show (a - k) + k ≤ c + k by omega)]
  unfold innerStartingWeight
  rw [auxiliaryWeight_recursion_of_valid hvalid]

/-- Corrected equation `the_key_recursion_inner` for all subsequent lower
inner diagonals.  Both upper-outer incoming totals occur with a minus sign. -/
theorem extendedStartTypeWeight_recurrence_lower_inner
    {n k : ℕ} {a c : ℤ}
    (hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n)
    (hlower : c ≤ a) (hstrictInner : a + 1 < c + k) :
    extendedStartTypeWeight n k a c =
      extendedTrinomial n a c - extendedTrinomial n (a + 1) (c - 1) -
          extendedStartTypeWeight n k (a + 1) c +
        extendedStartTypeWeight n k (a + k + 1) (c - k) +
        extendedStartTypeWeight n k (a + k + 1) (c - k - 1) -
        extendedStartTypeWeight n k (a - k) (c + k) -
        extendedStartTypeWeight n k (a - k + 1) (c + k) := by
  rw [extendedStartTypeWeight_eq_inner_of_lower_inner hlower (by omega),
    extendedStartTypeWeight_eq_inner_of_lower_inner
      (show c ≤ a + 1 by omega) (show a + 1 < c + k by omega),
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show (c - k) + k ≤ a + k + 1 by omega),
    extendedStartTypeWeight_eq_auxiliary_of_lower_outer
      (show (c - k - 1) + k ≤ a + k + 1 by omega),
    extendedStartTypeWeight_eq_auxiliary_of_upper_outer
      (show (a - k) + k ≤ c + k by omega),
    extendedStartTypeWeight_eq_auxiliary_of_upper_outer
      (show (a - k + 1) + k ≤ c + k by omega)]
  unfold innerStartingWeight
  rw [auxiliaryWeight_recursion_of_valid hvalid]
  ring_nf

/-- Natural-coordinate form of the lower-outer recurrence, with the left-hand
side stated using the `TypeCounts`-indexed total from the weighted cover. -/
theorem startTypeWeight_recurrence_lower_outer
    {n k a c : ℕ} (hvalid : a + c ≤ n) (houter : c + k ≤ a) :
    startTypeWeight k (coordinateType n a c hvalid) =
      extendedTrinomial n a c - extendedTrinomial n ((a : ℤ) + 1) ((c : ℤ) - 1) -
          extendedStartTypeWeight n k ((a : ℤ) + 1) c +
        extendedStartTypeWeight n k ((a : ℤ) + k + 1) ((c : ℤ) - k) +
        extendedStartTypeWeight n k ((a : ℤ) + k + 1) ((c : ℤ) - k - 1) := by
  have hvalidInt :
      0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) + (c : ℤ) ≤ n := by
    omega
  have houterInt : (c : ℤ) + (k : ℤ) ≤ a := by omega
  rw [← extendedStartTypeWeight_ofNat n k a c hvalid]
  exact extendedStartTypeWeight_recurrence_lower_outer hvalidInt houterInt

/-- Natural-coordinate form of the first lower-inner recurrence. -/
theorem startTypeWeight_recurrence_lowest_lower_inner
    {n k a c : ℕ} (hvalid : a + c ≤ n) (hlower : c ≤ a)
    (hlowest : c + k = a + 1) :
    startTypeWeight k (coordinateType n a c hvalid) =
      extendedTrinomial n a c - extendedTrinomial n ((a : ℤ) + 1) ((c : ℤ) - 1) -
          extendedStartTypeWeight n k ((a : ℤ) + 1) c +
        extendedStartTypeWeight n k ((a : ℤ) + k + 1) ((c : ℤ) - k) +
        extendedStartTypeWeight n k ((a : ℤ) + k + 1) ((c : ℤ) - k - 1) -
        extendedStartTypeWeight n k ((a : ℤ) - k) ((c : ℤ) + k) := by
  have hvalidInt :
      0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) + (c : ℤ) ≤ n := by
    omega
  have hlowerInt : (c : ℤ) ≤ a := by omega
  have hlowestInt : (c : ℤ) + (k : ℤ) = a + 1 := by omega
  rw [← extendedStartTypeWeight_ofNat n k a c hvalid]
  exact extendedStartTypeWeight_recurrence_lowest_lower_inner
    hvalidInt hlowerInt hlowestInt

/-- Natural-coordinate form of the corrected recurrence on every later
lower-inner diagonal. -/
theorem startTypeWeight_recurrence_lower_inner
    {n k a c : ℕ} (hvalid : a + c ≤ n) (hlower : c ≤ a)
    (hstrictInner : a + 1 < c + k) :
    startTypeWeight k (coordinateType n a c hvalid) =
      extendedTrinomial n a c - extendedTrinomial n ((a : ℤ) + 1) ((c : ℤ) - 1) -
          extendedStartTypeWeight n k ((a : ℤ) + 1) c +
        extendedStartTypeWeight n k ((a : ℤ) + k + 1) ((c : ℤ) - k) +
        extendedStartTypeWeight n k ((a : ℤ) + k + 1) ((c : ℤ) - k - 1) -
        extendedStartTypeWeight n k ((a : ℤ) - k) ((c : ℤ) + k) -
        extendedStartTypeWeight n k ((a : ℤ) - k + 1) ((c : ℤ) + k) := by
  have hvalidInt :
      0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) + (c : ℤ) ≤ n := by
    omega
  have hlowerInt : (c : ℤ) ≤ a := by omega
  have hstrictInnerInt : (a : ℤ) + 1 < (c : ℤ) + k := by omega
  rw [← extendedStartTypeWeight_ofNat n k a c hvalid]
  exact extendedStartTypeWeight_recurrence_lower_inner
    hvalidInt hlowerInt hstrictInnerInt

end Ternary
end WeightedChains
