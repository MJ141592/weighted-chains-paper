import WeightedChains.DTwo.Weights

/-!
# Boundary cases of the ternary dimension recurrence

The paper claims a three-term Pascal identity for the auxiliary weights.
Before the interior induction can be carried out, it must also be available at
the zero-extended “ghost” coordinates reached by the defining recurrence.
This file proves all genuinely invalid cases and the distinguished base point;
the nonnegative `c = 0` edge is proved in `DTwo.Weights`.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Ternary

/-- The desired dimension recurrence, packaged as a predicate so its boundary
and interior cases can be accumulated without duplicating the formula. -/
def AuxiliaryWeightPascal (n k : ℕ) (a c : ℤ) : Prop :=
  auxiliaryWeight (n + 1) k a c =
    auxiliaryWeight n k (a - 1) c + auxiliaryWeight n k a c +
      auxiliaryWeight n k a (c - 1)

theorem auxiliaryWeightPascal_of_neg_left {n k : ℕ} {a c : ℤ} (ha : a < 0) :
    AuxiliaryWeightPascal n k a c := by
  unfold AuxiliaryWeightPascal
  rw [auxiliaryWeight_eq_zero_of_neg_left ha,
    auxiliaryWeight_eq_zero_of_neg_left ha,
    auxiliaryWeight_eq_zero_of_neg_left (by omega : a - 1 < 0),
    auxiliaryWeight_eq_zero_of_neg_left ha]
  norm_num

theorem auxiliaryWeightPascal_of_neg_right {n k : ℕ} {a c : ℤ} (hc : c < 0) :
    AuxiliaryWeightPascal n k a c := by
  unfold AuxiliaryWeightPascal
  rw [auxiliaryWeight_eq_zero_of_neg_right hc,
    auxiliaryWeight_eq_zero_of_neg_right hc,
    auxiliaryWeight_eq_zero_of_neg_right hc,
    auxiliaryWeight_eq_zero_of_neg_right (by omega : c - 1 < 0)]
  norm_num

theorem auxiliaryWeightPascal_of_above_triangle {n k : ℕ} {a c : ℤ}
    (h : (n + 1 : ℕ) < a + c) : AuxiliaryWeightPascal n k a c := by
  unfold AuxiliaryWeightPascal
  rw [auxiliaryWeight_eq_zero_of_lt_add h,
    auxiliaryWeight_eq_zero_of_lt_add (by omega : (n : ℤ) < (a - 1) + c),
    auxiliaryWeight_eq_zero_of_lt_add (by omega : (n : ℤ) < a + c),
    auxiliaryWeight_eq_zero_of_lt_add (by omega : (n : ℤ) < a + (c - 1))]
  norm_num

/-- The Pascal identity holds at the exceptional base point of dimension
`n+1`: only the preceding dimension's base value survives. -/
theorem auxiliaryWeightPascal_at_dimension_zero (n k : ℕ) :
    AuxiliaryWeightPascal n k (n + 1) 0 := by
  unfold AuxiliaryWeightPascal
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_sub_cancel_right, zero_sub]
  have habove : (n : ℤ) < ((n : ℤ) + 1) + 0 := by omega
  rw [show auxiliaryWeight (n + 1) k (n + 1) 0 = 1 by
      simpa using auxiliaryWeight_dimension_zero (n + 1) k,
    auxiliaryWeight_dimension_zero n k,
    auxiliaryWeight_eq_zero_of_lt_add habove,
    auxiliaryWeight_eq_zero_of_neg_right (by norm_num : (-1 : ℤ) < 0)]
  norm_num

/-- The already-established `c = 0` edge expressed through the common
Pascal predicate. -/
theorem auxiliaryWeightPascal_zero_right (n k a : ℕ) (hn : 0 < n) (hk : 0 < k)
    (ha : 0 < a) (han : a ≤ n + 1) :
    AuxiliaryWeightPascal n k a 0 := by
  exact auxiliaryWeight_succ_zero_right n k a hn hk ha han

/-- At `(0,0)` the identity also holds in every positive preceding
dimension.  The hypothesis is essential: the identity fails from dimension
zero to one because `(0,0)` itself is the dimension-zero base point. -/
theorem auxiliaryWeightPascal_zero_zero (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    AuxiliaryWeightPascal n k 0 0 := by
  unfold AuxiliaryWeightPascal
  norm_num only [Nat.cast_zero, zero_sub]
  rw [auxiliaryWeight_zero_zero (n + 1) k (by omega) hk,
    auxiliaryWeight_eq_zero_of_neg_left (by norm_num : (-1 : ℤ) < 0),
    auxiliaryWeight_zero_zero n k hn hk,
    auxiliaryWeight_eq_zero_of_neg_right (by norm_num : (-1 : ℤ) < 0)]
  norm_num

end Ternary
end WeightedChains
