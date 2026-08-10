import WeightedChains.DTwo

/-!
# The auxiliary ternary weight recurrence

This file formalises the zero-extended auxiliary quantity `U_n(a,c)` from
Section 5.  The first type coordinate is the recursion parameter: every
recursive call has a strictly larger first coordinate, so the valid triangle
`0 ≤ a`, `0 ≤ c`, `a + c ≤ n` makes the recursion finite.
-/

set_option autoImplicit false

namespace WeightedChains

namespace Ternary

private theorem recursionCoordinate_lt {n : ℕ} {a c : ℤ}
    (hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n)
    (hnotBase : ¬(a = n ∧ c = 0)) : a < n := by
  by_contra h
  have hna : (n : ℤ) ≤ a := Int.le_of_not_gt h
  have hae : a = n := by omega
  have hce : c = 0 := by omega
  exact hnotBase ⟨hae, hce⟩

private theorem recursionMeasure_decreases {n : ℕ} {a r : ℤ}
    (ha : 0 ≤ a) (han : a < n) (hr : 0 < r) :
    n - (a + r).toNat < n - a.toNat := by
  have hr0 : 0 ≤ r := hr.le
  rw [Int.toNat_add ha hr0]
  have han' : a.toNat < n := (Int.toNat_lt ha).2 han
  have hr' : 0 < r.toNat := by omega
  omega

/-- The paper's auxiliary `U_n(a,c)`, extended by zero outside the triangle of
valid ternary types.  The parameter `k` is the prescribed chain width.

The definition is meaningful for every `n` and `k`; the paper only uses it
under `k ≤ n`. -/
def auxiliaryWeight (n k : ℕ) (a c : ℤ) : ℤ :=
  if _hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n then
    if a = n ∧ c = 0 then
      1
    else
      extendedTrinomial n a c - extendedTrinomial n (a + 1) (c - 1) -
          auxiliaryWeight n k (a + 1) c +
        auxiliaryWeight n k (a + k + 1) (c - k) +
        auxiliaryWeight n k (a + k + 1) (c - k - 1)
  else
    0
termination_by n - a.toNat
decreasing_by
  · have hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n := by assumption
    have hnotBase : ¬(a = n ∧ c = 0) := by assumption
    have han := recursionCoordinate_lt hvalid hnotBase
    exact recursionMeasure_decreases hvalid.1 han (by norm_num)
  · have hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n := by assumption
    have hnotBase : ¬(a = n ∧ c = 0) := by assumption
    have han := recursionCoordinate_lt hvalid hnotBase
    simpa only [add_assoc] using recursionMeasure_decreases hvalid.1 han
      (show (0 : ℤ) < k + 1 by omega)

  · have hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n := by assumption
    have hnotBase : ¬(a = n ∧ c = 0) := by assumption
    have han := recursionCoordinate_lt hvalid hnotBase
    simpa only [add_assoc] using recursionMeasure_decreases hvalid.1 han
      (show (0 : ℤ) < k + 1 by omega)

@[simp]
theorem auxiliaryWeight_eq_zero_of_neg_left {n k : ℕ} {a c : ℤ} (ha : a < 0) :
    auxiliaryWeight n k a c = 0 := by
  have hinvalid : ¬(0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n) := by omega
  rw [auxiliaryWeight.eq_1, dif_neg hinvalid]

@[simp]
theorem auxiliaryWeight_eq_zero_of_neg_right {n k : ℕ} {a c : ℤ} (hc : c < 0) :
    auxiliaryWeight n k a c = 0 := by
  have hinvalid : ¬(0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n) := by omega
  rw [auxiliaryWeight.eq_1, dif_neg hinvalid]

@[simp]
theorem auxiliaryWeight_eq_zero_of_lt_add {n k : ℕ} {a c : ℤ}
    (h : (n : ℤ) < a + c) : auxiliaryWeight n k a c = 0 := by
  have hinvalid : ¬(0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n) := by omega
  rw [auxiliaryWeight.eq_1, dif_neg hinvalid]

@[simp]
theorem auxiliaryWeight_dimension_zero (n k : ℕ) :
    auxiliaryWeight n k n 0 = 1 := by
  rw [auxiliaryWeight]
  simp

/-- The defining equation for `U_n` at every valid non-base type. -/
theorem auxiliaryWeight_recursion {n k : ℕ} {a c : ℤ}
    (hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n)
    (hnotBase : ¬(a = n ∧ c = 0)) :
    auxiliaryWeight n k a c =
      extendedTrinomial n a c - extendedTrinomial n (a + 1) (c - 1) -
          auxiliaryWeight n k (a + 1) c +
        auxiliaryWeight n k (a + k + 1) (c - k) +
        auxiliaryWeight n k (a + k + 1) (c - k - 1) := by
  rw [auxiliaryWeight]
  simp only [dif_pos hvalid, if_neg hnotBase]

/-- At the special point `(n,0)`, the recursively displayed expression is
also `1`; this is occasionally more convenient than separating the base case
in later inductions. -/
theorem auxiliaryWeight_recursion_at_dimension_zero (n k : ℕ) :
    extendedTrinomial n n 0 - extendedTrinomial n (n + 1) (-1) -
          auxiliaryWeight n k (n + 1) 0 +
        auxiliaryWeight n k (n + k + 1) (-k) +
        auxiliaryWeight n k (n + k + 1) (-k - 1) = 1 := by
  have hneg : -(k : ℤ) - 1 < 0 := by omega
  rw [auxiliaryWeight_eq_zero_of_neg_right hneg]
  norm_num [extendedTrinomial, trinomial]

/-- Along the edge `c = 0`, the auxiliary weight has the closed form used in
the paper's outer-positivity proof.  The assumption `0 < k` makes both jump
terms in the recurrence vanish. -/
theorem auxiliaryWeight_zero_right (n k a : ℕ) (hk : 0 < k) (ha : 0 < a)
    (han : a ≤ n) : auxiliaryWeight n k a 0 = (n - 1).choose (a - 1) := by
  induction han using Nat.decreasingInduction with
  | self =>
      simp [auxiliaryWeight_dimension_zero]
  | of_succ a han ih =>
      have ha' : 0 < a := by omega
      have hvalid : 0 ≤ (a : ℤ) ∧ 0 ≤ (0 : ℤ) ∧ (a : ℤ) + 0 ≤ n := by
        constructor <;> omega
      have hnotBase : ¬((a : ℤ) = n ∧ (0 : ℤ) = 0) := by omega
      have hnegJump : (0 : ℤ) - k < 0 := by omega
      have hnegJumpPred : (0 : ℤ) - k - 1 < 0 := by omega
      rw [auxiliaryWeight_recursion hvalid hnotBase,
        auxiliaryWeight_eq_zero_of_neg_right hnegJump,
        auxiliaryWeight_eq_zero_of_neg_right hnegJumpPred]
      norm_num [extendedTrinomial, trinomial]
      have ih' : auxiliaryWeight n k ((a : ℤ) + 1) 0 = (n - 1).choose a := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using ih (by omega)
      rw [ih']
      have hnpos : 0 < n := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha')
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
      simp only [Nat.succ_sub_one]
      rw [Nat.choose_succ_succ]
      norm_num

/-- The edge weights are positive away from the exceptional type `(0,n,0)`. -/
theorem auxiliaryWeight_zero_right_pos (n k a : ℕ) (hk : 0 < k) (ha : 0 < a)
    (han : a ≤ n) : 0 < auxiliaryWeight n k a 0 := by
  rw [auxiliaryWeight_zero_right n k a hk ha han]
  exact_mod_cast Nat.choose_pos (by omega : a - 1 ≤ n - 1)

/-- The exceptional lower type `(0,n,0)` has weight zero in every positive
dimension. -/
@[simp]
theorem auxiliaryWeight_zero_zero (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    auxiliaryWeight n k 0 0 = 0 := by
  have hvalid : 0 ≤ (0 : ℤ) ∧ 0 ≤ (0 : ℤ) ∧ (0 : ℤ) + 0 ≤ n := by
    constructor <;> omega
  have hnotBase : ¬((0 : ℤ) = n ∧ (0 : ℤ) = 0) := by omega
  have hnegJump : (0 : ℤ) - k < 0 := by omega
  have hnegJumpPred : (0 : ℤ) - k - 1 < 0 := by omega
  rw [auxiliaryWeight_recursion hvalid hnotBase,
    auxiliaryWeight_eq_zero_of_neg_right hnegJump,
    auxiliaryWeight_eq_zero_of_neg_right hnegJumpPred]
  norm_num only [zero_add, add_zero, zero_sub]
  have hOne := auxiliaryWeight_zero_right n k 1 hk (by omega) (by omega)
  norm_num at hOne
  rw [hOne]
  norm_num [extendedTrinomial, trinomial]

/-- The dimension-Pascal identity on the edge `c = 0`.  This is one of the
boundary cases needed for the full identity claimed in Section 5. -/
theorem auxiliaryWeight_succ_zero_right (n k a : ℕ) (hn : 0 < n) (hk : 0 < k)
    (ha : 0 < a) (han : a ≤ n + 1) :
    auxiliaryWeight (n + 1) k a 0 =
      auxiliaryWeight n k (a - 1) 0 + auxiliaryWeight n k a 0 +
        auxiliaryWeight n k a (-1) := by
  rw [auxiliaryWeight_eq_zero_of_neg_right (by norm_num : (-1 : ℤ) < 0),
    auxiliaryWeight_zero_right (n + 1) k a hk ha han]
  have hcastPred : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
  rw [← hcastPred]
  by_cases htop : a = n + 1
  · subst a
    simp only [Nat.add_sub_cancel]
    rw [auxiliaryWeight_dimension_zero]
    have hinvalid : (n : ℤ) < (n + 1 : ℕ) + 0 := by omega
    rw [auxiliaryWeight_eq_zero_of_lt_add hinvalid]
    norm_num
  have han' : a ≤ n := by omega
  by_cases hone : a = 1
  · subst a
    norm_num only [Nat.cast_one, Nat.one_sub]
    rw [auxiliaryWeight_zero_zero n k hn hk]
    have hOne := auxiliaryWeight_zero_right n k 1 hk (by omega) han'
    norm_num at hOne
    rw [hOne]
    norm_num
  have htwo : 2 ≤ a := by omega
  rw [auxiliaryWeight_zero_right n k (a - 1) hk (by omega) (by omega),
    auxiliaryWeight_zero_right n k a hk ha han']
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := by
    exact ⟨a - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact_mod_cast Nat.choose_succ_succ n' a'

end Ternary

end WeightedChains
