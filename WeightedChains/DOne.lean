import WeightedChains.WeightedStrategy

/-!
# Assigning weights for `d = 1`

This file follows Section 4 of the paper.  We first formalise the auxiliary
quantity `U_n(a)`.  It is convenient to define it by the finite expansion of
the paper's recurrence; the recurrence itself is then a theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace WeightedChains
namespace DOne

/-- The binomial coefficient extended by zero to negative lower indices. -/
def extendedChoose (n : ℕ) (a : ℤ) : ℤ :=
  if 0 ≤ a then (n.choose a.toNat : ℤ) else 0

@[simp]
theorem extendedChoose_ofNat (n a : ℕ) : extendedChoose n a = n.choose a := by
  simp [extendedChoose]

@[simp]
theorem extendedChoose_of_neg (n : ℕ) {a : ℤ} (ha : a < 0) : extendedChoose n a = 0 := by
  simp [extendedChoose, ha]

theorem extendedChoose_succ (n : ℕ) (a : ℤ) :
    extendedChoose (n + 1) a = extendedChoose n a + extendedChoose n (a - 1) := by
  by_cases ha : a < 0
  · have hapred : a - 1 < 0 := by omega
    simp [extendedChoose_of_neg _ ha, extendedChoose_of_neg _ hapred]
  · have hanonnegative : 0 ≤ a := le_of_not_gt ha
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hanonnegative
    cases b with
    | zero => simp [extendedChoose]
    | succ b =>
        have hb : (0 : ℤ) ≤ (b : ℤ) + 1 := by positivity
        norm_num [extendedChoose, Nat.choose_succ_succ, Nat.succ_eq_add_one, add_comm, hb]

/-- The adjacent-layer difference `C(n,a) - C(n,a-1)`, with binomial
coefficients outside their natural range interpreted as zero. -/
def binomialDifference (n : ℕ) (a : ℤ) : ℤ :=
  extendedChoose n a - extendedChoose n (a - 1)

@[simp]
theorem binomialDifference_of_neg (n : ℕ) {a : ℤ} (ha : a < 0) :
    binomialDifference n a = 0 := by
  have hapred : a - 1 < 0 := by omega
  simp [binomialDifference, extendedChoose_of_neg n ha, extendedChoose_of_neg n hapred]

theorem binomialDifference_succ (n : ℕ) (a : ℤ) :
    binomialDifference (n + 1) a =
      binomialDifference n a + binomialDifference n (a - 1) := by
  simp only [binomialDifference, extendedChoose_succ]
  ring

theorem choose_pred_lt_choose (n a : ℕ) (ha : 0 < a) (hhalf : 2 * a ≤ n) :
    n.choose (a - 1) < n.choose a := by
  have hpred_le : a - 1 ≤ n := by omega
  have hpred_pos : 0 < n.choose (a - 1) := Nat.choose_pos hpred_le
  have hfactor : a < n - (a - 1) := by omega
  have hchoose := Nat.choose_succ_right_eq n (a - 1)
  have haeq : a - 1 + 1 = a := by omega
  rw [haeq] at hchoose
  have hproduct : n.choose (a - 1) * a < n.choose a * a := by
    calc
      n.choose (a - 1) * a < n.choose (a - 1) * (n - (a - 1)) :=
        Nat.mul_lt_mul_of_pos_left hfactor hpred_pos
      _ = n.choose a * a := hchoose.symm
  exact (Nat.mul_lt_mul_right ha).mp hproduct

theorem binomialDifference_ofNat_pos (n a : ℕ) (hhalf : 2 * a ≤ n) :
    0 < binomialDifference n a := by
  cases a with
  | zero => simp [binomialDifference, extendedChoose]
  | succ a =>
      have hchoose := choose_pred_lt_choose n (a + 1) (by omega) hhalf
      simp only [binomialDifference, extendedChoose_ofNat]
      norm_num at hchoose ⊢
      exact_mod_cast hchoose

theorem binomialDifference_nonneg_of_le_half (n a : ℕ) (z : ℤ)
    (hz : z ≤ a) (hhalf : 2 * a ≤ n) :
    0 ≤ binomialDifference n z := by
  by_cases hzneg : z < 0
  · have hzpred : z - 1 < 0 := by omega
    simp [binomialDifference, extendedChoose_of_neg n hzneg, extendedChoose_of_neg n hzpred]
  · have hznonneg : 0 ≤ z := le_of_not_gt hzneg
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hznonneg
    exact (binomialDifference_ofNat_pos n b (by exact_mod_cast (by omega : 2 * (b : ℤ) ≤ n))).le

/-- The paper's `U_n(a)` for a natural layer index.  The summands unfold the
recurrence in jumps of `k + 1`; terms with negative indices vanish. -/
def auxiliaryWeightNat (n k a : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (a / (k + 1) + 1),
    binomialDifference n ((a : ℤ) - ((j * (k + 1) : ℕ) : ℤ))

theorem auxiliaryWeightNat_eq_longSum (n k a : ℕ) :
    auxiliaryWeightNat n k a =
      ∑ j ∈ Finset.range (a + 1),
        binomialDifference n ((a : ℤ) - ((j * (k + 1) : ℕ) : ℤ)) := by
  unfold auxiliaryWeightNat
  apply Finset.sum_subset
  · apply Finset.range_mono
    exact Nat.add_le_add_right (Nat.div_le_self a (k + 1)) 1
  · intro j hjlong hjshort
    simp only [Finset.mem_range] at hjlong hjshort
    have hquotient : a / (k + 1) < j := by omega
    have hproduct : a < j * (k + 1) :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < k + 1)).mp hquotient
    have hproduct' : (a : ℤ) < (j * (k + 1) : ℕ) := by exact_mod_cast hproduct
    have hindex : (a : ℤ) - ((j * (k + 1) : ℕ) : ℤ) < 0 := by
      omega
    have hpred : (a : ℤ) - ((j * (k + 1) : ℕ) : ℤ) - 1 < 0 := by omega
    have hindex' : (a : ℤ) - (j : ℤ) * ((k : ℤ) + 1) < 0 := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hindex
    have hpred' : (a : ℤ) - (j : ℤ) * ((k : ℤ) + 1) - 1 < 0 := by omega
    have hnotindex : ¬(j : ℤ) * ((k : ℤ) + 1) ≤ a := by omega
    have hnotpred : ¬(1 : ℤ) ≤ (a : ℤ) - (j : ℤ) * ((k : ℤ) + 1) := by omega
    simp [binomialDifference, extendedChoose, hnotindex, hnotpred]

/-- The paper extends `U_n(a)` by zero for negative `a`. -/
def auxiliaryWeight (n k : ℕ) (a : ℤ) : ℤ :=
  if a < 0 then 0 else auxiliaryWeightNat n k a.toNat

@[simp]
theorem auxiliaryWeight_of_neg (n k : ℕ) {a : ℤ} (ha : a < 0) :
    auxiliaryWeight n k a = 0 := by
  simp [auxiliaryWeight, ha]

@[simp]
theorem auxiliaryWeight_ofNat (n k a : ℕ) :
    auxiliaryWeight n k a = auxiliaryWeightNat n k a := by
  simp [auxiliaryWeight]

/-- Equation (4.3) defining `U_n` in the paper. -/
theorem auxiliaryWeightNat_recurrence (n k a : ℕ) :
    auxiliaryWeightNat n k a =
      binomialDifference n a +
        if k + 1 ≤ a then auxiliaryWeightNat n k (a - (k + 1)) else 0 := by
  unfold auxiliaryWeightNat
  rw [Finset.sum_range_succ']
  by_cases hka : k + 1 ≤ a
  · rw [if_pos hka]
    have hdiv : a / (k + 1) = (a - (k + 1)) / (k + 1) + 1 :=
      Nat.div_eq_sub_div (by omega) hka
    rw [hdiv]
    rw [add_comm]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j _hj
      apply congrArg (binomialDifference n)
      rw [Nat.cast_sub hka]
      push_cast
      ring
  · rw [if_neg hka]
    have halt : a < k + 1 := Nat.lt_of_not_ge hka
    have hdiv : a / (k + 1) = 0 := Nat.div_eq_of_lt halt
    simp [hdiv]

/-- Pascal's identity for the auxiliary weights, as used in the induction on
`n` in Section 4. -/
theorem auxiliaryWeightNat_succ (n k a : ℕ) :
    auxiliaryWeightNat (n + 1) k a =
      auxiliaryWeightNat n k a + if a = 0 then 0 else auxiliaryWeightNat n k (a - 1) := by
  cases a with
  | zero => simp [auxiliaryWeightNat, binomialDifference, extendedChoose]
  | succ a =>
      rw [if_neg (by omega : a + 1 ≠ 0)]
      have hsecond :
          (∑ j ∈ Finset.range (a + 1 + 1),
              binomialDifference n
                (((a + 1 : ℕ) : ℤ) - ((j * (k + 1) : ℕ) : ℤ) - 1)) =
            auxiliaryWeightNat n k a := by
        rw [auxiliaryWeightNat_eq_longSum, Finset.sum_range_succ]
        have hmul : a + 1 ≤ (a + 1) * (k + 1) := by
          simpa only [Nat.mul_one] using
            Nat.mul_le_mul_left (a + 1) (Nat.succ_le_succ (Nat.zero_le k))
        have hmul' : (((a + 1 : ℕ) : ℤ)) ≤ ((((a + 1) * (k + 1) : ℕ) : ℤ)) := by
          exact_mod_cast hmul
        have hlast :
            (((a + 1 : ℕ) : ℤ) - ((((a + 1) * (k + 1) : ℕ) : ℤ)) - 1) < 0 := by
          omega
        rw [binomialDifference_of_neg n hlast, add_zero]
        apply Finset.sum_congr rfl
        intro j _hj
        apply congrArg (binomialDifference n)
        push_cast
        ring
      calc
        auxiliaryWeightNat (n + 1) k (a + 1) =
            ∑ j ∈ Finset.range (a + 1 + 1),
              binomialDifference (n + 1)
                (((a + 1 : ℕ) : ℤ) - ((j * (k + 1) : ℕ) : ℤ)) :=
          auxiliaryWeightNat_eq_longSum (n + 1) k (a + 1)
        _ = ∑ j ∈ Finset.range (a + 1 + 1),
              (binomialDifference n
                  (((a + 1 : ℕ) : ℤ) - ((j * (k + 1) : ℕ) : ℤ)) +
                binomialDifference n
                  (((a + 1 : ℕ) : ℤ) - ((j * (k + 1) : ℕ) : ℤ) - 1)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact binomialDifference_succ n _
        _ = (∑ j ∈ Finset.range (a + 1 + 1),
                binomialDifference n
                  (((a + 1 : ℕ) : ℤ) - ((j * (k + 1) : ℕ) : ℤ)) +
              ∑ j ∈ Finset.range (a + 1 + 1),
                binomialDifference n
                  (((a + 1 : ℕ) : ℤ) - ((j * (k + 1) : ℕ) : ℤ) - 1)) := by
          rw [Finset.sum_add_distrib]
        _ = auxiliaryWeightNat n k (a + 1) + auxiliaryWeightNat n k a := by
          rw [← auxiliaryWeightNat_eq_longSum n k (a + 1), hsecond]

theorem auxiliaryWeight_sub (n k a : ℕ) :
    auxiliaryWeight n k ((a : ℤ) - (k : ℤ) - 1) =
      if k + 1 ≤ a then auxiliaryWeightNat n k (a - (k + 1)) else 0 := by
  by_cases hka : k + 1 ≤ a
  · rw [if_pos hka]
    have hka' : ((k + 1 : ℕ) : ℤ) ≤ (a : ℤ) := by exact_mod_cast hka
    have hnonnegative : (0 : ℤ) ≤ (a : ℤ) - (k : ℤ) - 1 := by
      push_cast at hka'
      omega
    have htoNat : ((a : ℤ) - (k : ℤ) - 1).toNat = a - (k + 1) := by omega
    have hnotnegative : ¬(a : ℤ) - (k : ℤ) < 1 := by omega
    simp [auxiliaryWeight, hnotnegative, htoNat]
  · rw [if_neg hka]
    have hka' : (a : ℤ) < ((k + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.lt_of_not_ge hka
    have hnegative : (a : ℤ) - (k : ℤ) - 1 < 0 := by
      push_cast at hka'
      omega
    simp [auxiliaryWeight, hnegative]

/-- The recurrence for `U_n(a)` in the paper's integer-indexed notation. -/
theorem auxiliaryWeight_recurrence_ofNat (n k a : ℕ) :
    auxiliaryWeight n k a =
      binomialDifference n a + auxiliaryWeight n k ((a : ℤ) - (k : ℤ) - 1) := by
  rw [auxiliaryWeight_ofNat, auxiliaryWeightNat_recurrence, auxiliaryWeight_sub]

/-- Pascal's identity with the paper's extension `U_n(a) = 0` for `a < 0`. -/
theorem auxiliaryWeight_succ (n k : ℕ) (a : ℤ) :
    auxiliaryWeight (n + 1) k a =
      auxiliaryWeight n k a + auxiliaryWeight n k (a - 1) := by
  by_cases ha : a < 0
  · have hapred : a - 1 < 0 := by omega
    simp [auxiliaryWeight_of_neg _ _ ha, auxiliaryWeight_of_neg _ _ hapred]
  · have hanonnegative : 0 ≤ a := le_of_not_gt ha
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hanonnegative
    cases b with
    | zero =>
        simp [auxiliaryWeightNat_succ, auxiliaryWeight]
    | succ b =>
        rw [auxiliaryWeight_ofNat, auxiliaryWeight_ofNat, auxiliaryWeightNat_succ]
        rw [if_neg (by omega : b + 1 ≠ 0)]
        have hpred : (((b + 1 : ℕ) : ℤ) - 1) = (b : ℤ) := by omega
        rw [hpred, auxiliaryWeight_ofNat]
        simp

/-- The auxiliary weights are positive on the lower half of the Boolean cube. -/
theorem auxiliaryWeightNat_pos (n k a : ℕ) (hhalf : 2 * a ≤ n) :
    0 < auxiliaryWeightNat n k a := by
  apply Finset.sum_pos'
  · intro j hj
    apply binomialDifference_nonneg_of_le_half n a
    · have hnonnegative : 0 ≤ (j * (k + 1) : ℤ) := by positivity
      omega
    · exact hhalf
  · refine ⟨0, by simp, ?_⟩
    simpa using binomialDifference_ofNat_pos n a hhalf

/-- The total weight assigned to chains starting at a lower inner layer `a`.
The reflected upper starting layer is `n - a - k`, explaining the index which
is used throughout the induction in the paper. -/
def innerWeight (n k a : ℕ) : ℤ :=
  auxiliaryWeight n k a - auxiliaryWeight n k ((n : ℤ) - (a : ℤ) - (k : ℤ))

theorem innerWeight_succ (n k a : ℕ) (ha : 0 < a) :
    innerWeight (n + 1) k a = innerWeight n k a + innerWeight n k (a - 1) := by
  have hpred : (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    norm_num
  have hupperPred :
      ((n + 1 : ℕ) : ℤ) - (a : ℤ) - (k : ℤ) - 1 =
        (n : ℤ) - (a : ℤ) - (k : ℤ) := by
    push_cast
    ring
  have hupper :
      ((n + 1 : ℕ) : ℤ) - (a : ℤ) - (k : ℤ) =
        (n : ℤ) - ((a - 1 : ℕ) : ℤ) - (k : ℤ) := by
    rw [← hpred]
    push_cast
    ring
  unfold innerWeight
  rw [auxiliaryWeight_succ n k (a : ℤ),
    auxiliaryWeight_succ n k ((n + 1 : ℕ) - (a : ℤ) - (k : ℤ))]
  rw [hpred, hupperPred, hupper]
  ring

theorem binomialDifference_eq_zero_of_center (n a : ℕ) (hcenter : n + 1 = 2 * a) :
    binomialDifference n a = 0 := by
  have ha : 0 < a := by omega
  have hale : a ≤ n := by omega
  have hsymmetric := Nat.choose_symm hale
  have hcomplement : n - a = a - 1 := by omega
  rw [hcomplement] at hsymmetric
  have hpred : (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    norm_num
  rw [binomialDifference, hpred, extendedChoose_ofNat, extendedChoose_ofNat]
  exact sub_eq_zero.mpr (by exact_mod_cast hsymmetric.symm)

theorem innerWeight_eq_zero_of_center (n k a : ℕ) (hcenter : n + 1 = 2 * a) :
    innerWeight n k a = 0 := by
  have hrecurrence := auxiliaryWeight_recurrence_ofNat n k a
  rw [binomialDifference_eq_zero_of_center n a hcenter, zero_add] at hrecurrence
  have hcomplement :
      (n : ℤ) - (a : ℤ) - (k : ℤ) = (a : ℤ) - (k : ℤ) - 1 := by
    have hcenter' : (n : ℤ) + 1 = 2 * (a : ℤ) := by exact_mod_cast hcenter
    omega
  unfold innerWeight
  rw [hcomplement, hrecurrence, sub_self]

theorem innerWeight_pred_eq_zero_of_boundary (n k a : ℕ) (ha : 0 < a) (hnk : k ≤ n)
    (hboundary : n - k = 2 * a - 2) :
    innerWeight n k (a - 1) = 0 := by
  have hboundary' : (n : ℤ) - (k : ℤ) = 2 * (a : ℤ) - 2 := by
    calc
      (n : ℤ) - (k : ℤ) = ((n - k : ℕ) : ℤ) := (Nat.cast_sub hnk).symm
      _ = ((2 * a - 2 : ℕ) : ℤ) := by exact_mod_cast hboundary
      _ = 2 * (a : ℤ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ 2 * a)]
        push_cast
        rfl
  have hcomplement :
      (n : ℤ) - ((a - 1 : ℕ) : ℤ) - (k : ℤ) = ((a - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    omega
  unfold innerWeight
  rw [hcomplement, sub_self]

/-- Positivity of the weights assigned to lower inner layers in Section 4.

The hypothesis `1 < k` is essential: the main theorem deliberately excludes
`k = 1`, where uniqueness fails and the corresponding central weight can be
zero.
-/
theorem innerWeight_pos (k n a : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hinner : n - k < 2 * a) (hlower : 2 * a ≤ n) :
    0 < innerWeight n k a := by
  induction n, hkn using Nat.le_induction generalizing a with
  | base =>
      have ha : 0 < a := by omega
      have ha' : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
      have hnegative : (k : ℤ) - (a : ℤ) - (k : ℤ) < 0 := by omega
      unfold innerWeight
      rw [auxiliaryWeight_ofNat, auxiliaryWeight_of_neg k k hnegative, sub_zero]
      exact auxiliaryWeightNat_pos k k a hlower
  | succ n hkn ih =>
      have ha : 0 < a := by omega
      rw [innerWeight_succ n k a ha]
      by_cases hcenter : 2 * a = n + 1
      · rw [innerWeight_eq_zero_of_center n k a hcenter.symm, zero_add]
        apply ih (a - 1)
        · omega
        · omega
      · have hlower' : 2 * a ≤ n := by omega
        by_cases hpredInner : n - k < 2 * (a - 1)
        · have hfirst : 0 < innerWeight n k a := ih a (by omega) hlower'
          have hsecond : 0 < innerWeight n k (a - 1) := ih (a - 1) hpredInner (by omega)
          omega
        · have hboundary : n - k = 2 * a - 2 := by omega
          rw [innerWeight_pred_eq_zero_of_boundary n k a ha hkn hboundary, add_zero]
          exact ih a (by omega) hlower'

/-- Total weight assigned to chains starting at a lower layer. Outer layers use
`U_n(a)` directly; inner layers subtract the contribution of chains starting
at the reflected upper outer layer. -/
def lowerStartingWeight (n k a : ℕ) : ℤ :=
  if n - k < 2 * a then innerWeight n k a else auxiliaryWeightNat n k a

theorem lowerStartingWeight_pos (k n a : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hlower : 2 * a ≤ n) :
    0 < lowerStartingWeight n k a := by
  by_cases hinner : n - k < 2 * a
  · rw [lowerStartingWeight, if_pos hinner]
    exact innerWeight_pos k n a hk hkn hinner hlower
  · rw [lowerStartingWeight, if_neg hinner]
    exact auxiliaryWeightNat_pos n k a hlower

end DOne
end WeightedChains
