import WeightedChains.DTwoWeightPascal

/-!
# The auxiliary-weight Pascal identity on lower ternary types

This file proves the dimension recurrence for every lower type in the valid
triangle.  The proof follows the defining recurrence from right to left in
the first type coordinate.  Its induction hypothesis is therefore available
at each of the three forward coordinates occurring in that recurrence.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Ternary

/-- The displayed recursive expression also computes the distinguished base
point.  This lets later algebra use one equation uniformly on the full valid
triangle. -/
theorem auxiliaryWeight_recursion_of_valid {n k : ℕ} {a c : ℤ}
    (hvalid : 0 ≤ a ∧ 0 ≤ c ∧ a + c ≤ n) :
    auxiliaryWeight n k a c =
      extendedTrinomial n a c - extendedTrinomial n (a + 1) (c - 1) -
          auxiliaryWeight n k (a + 1) c +
        auxiliaryWeight n k (a + k + 1) (c - k) +
        auxiliaryWeight n k (a + k + 1) (c - k - 1) := by
  by_cases hbase : a = n ∧ c = 0
  · rw [hbase.1, hbase.2, auxiliaryWeight_dimension_zero]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub] using
      (auxiliaryWeight_recursion_at_dimension_zero n k).symm
  · exact auxiliaryWeight_recursion hvalid hbase

/-- One step above the valid triangle, the displayed recursion is still a
true equation: all six terms vanish by zero extension.  This is the ghost
boundary needed when Pascal induction reaches `a + c = n + 1`. -/
theorem auxiliaryWeight_recursion_of_add_eq_succ {n k : ℕ} {a c : ℤ}
    (hadd : a + c = n + 1) :
    auxiliaryWeight n k a c =
      extendedTrinomial n a c - extendedTrinomial n (a + 1) (c - 1) -
          auxiliaryWeight n k (a + 1) c +
        auxiliaryWeight n k (a + k + 1) (c - k) +
        auxiliaryWeight n k (a + k + 1) (c - k - 1) := by
  rw [auxiliaryWeight_eq_zero_of_lt_add (by omega),
    extendedTrinomial_eq_zero_of_lt_add (by omega),
    extendedTrinomial_eq_zero_of_lt_add (by omega),
    auxiliaryWeight_eq_zero_of_lt_add (by omega),
    auxiliaryWeight_eq_zero_of_lt_add (by omega),
    auxiliaryWeight_eq_zero_of_lt_add (by omega)]
  norm_num

/-- The dimension-Pascal identity for natural lower types.  This is the
induction engine for the integer-indexed paper statement below. -/
theorem auxiliaryWeightPascal_of_valid_lower_nat (n k a c : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) (hca : c ≤ a) (hac : a + c ≤ n + 1) :
    AuxiliaryWeightPascal n k a c := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have main : ∀ d : ℕ, ∀ a c : ℕ,
      n + 1 - a = d → c ≤ a → a + c ≤ n + 1 →
        AuxiliaryWeightPascal n k a c := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro a c hd hca hac
        by_cases hc0 : c = 0
        · subst c
          by_cases ha0 : a = 0
          · subst a
            exact auxiliaryWeightPascal_zero_zero n k hn hk
          · exact auxiliaryWeightPascal_zero_right n k a hn hk
              (Nat.pos_of_ne_zero ha0) hac
        have hc : 0 < c := Nat.pos_of_ne_zero hc0
        have ha : 0 < a := lt_of_lt_of_le hc hca
        have hlhsValid :
            0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) + c ≤ n + 1 := by
          constructor <;> omega
        have hlhsNotBase : ¬((a : ℤ) = n + 1 ∧ (c : ℤ) = 0) := by omega
        have hpredValid :
            0 ≤ (a : ℤ) - 1 ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) - 1 + c ≤ n := by
          constructor <;> omega
        by_cases htop : a + c = n + 1
        · have hlastValid :
              0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) - 1 ∧
                (a : ℤ) + (c - 1) ≤ n := by
            constructor <;> omega
          have hPnext : AuxiliaryWeightPascal n k ((a : ℤ) + 1) c :=
            auxiliaryWeightPascal_of_above_triangle (by omega)
          have hPjump :
              AuxiliaryWeightPascal n k ((a : ℤ) + k + 1) ((c : ℤ) - k) :=
            auxiliaryWeightPascal_of_above_triangle (by omega)
          have hPjumpPred :
              AuxiliaryWeightPascal n k ((a : ℤ) + k + 1) ((c : ℤ) - k - 1) := by
            by_cases hneg : (c : ℤ) - k - 1 < 0
            · exact auxiliaryWeightPascal_of_neg_right hneg
            · have hck : k + 1 ≤ c := by omega
              have hcoord : a + k + 1 + (c - k - 1) = n + 1 := by omega
              have hdist : n + 1 - (a + k + 1) < d := by omega
              have hnat := ih (n + 1 - (a + k + 1)) hdist
                (a + k + 1) (c - k - 1) rfl (by omega) (by omega)
              norm_num only [Nat.cast_add, Nat.cast_one] at hnat
              rw [show ((c - k - 1 : ℕ) : ℤ) = (c : ℤ) - k - 1 by omega] at hnat
              exact hnat
          unfold AuxiliaryWeightPascal at hPnext hPjump hPjumpPred ⊢
          rw [auxiliaryWeight_recursion hlhsValid hlhsNotBase,
            auxiliaryWeight_recursion_of_valid hpredValid,
            auxiliaryWeight_recursion_of_add_eq_succ
              (show (a : ℤ) + c = n + 1 by omega),
            auxiliaryWeight_recursion_of_valid hlastValid,
            extendedTrinomial_succ, extendedTrinomial_succ,
            hPnext, hPjump, hPjumpPred]
          ring_nf
        · have hinterior : a + c ≤ n := by omega
          have hmidValid :
              0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) + c ≤ n := by
            constructor <;> omega
          have hlastValid :
              0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) - 1 ∧
                (a : ℤ) + (c - 1) ≤ n := by
            constructor <;> omega
          have hPnext : AuxiliaryWeightPascal n k ((a : ℤ) + 1) c := by
            have hdist : n + 1 - (a + 1) < d := by omega
            have hnat := ih (n + 1 - (a + 1)) hdist
              (a + 1) c rfl (by omega) (by omega)
            simpa only [Nat.cast_add, Nat.cast_one] using hnat
          have hPjump :
              AuxiliaryWeightPascal n k ((a : ℤ) + k + 1) ((c : ℤ) - k) := by
            by_cases hneg : (c : ℤ) - k < 0
            · exact auxiliaryWeightPascal_of_neg_right hneg
            · have hkc : k ≤ c := by omega
              have hdist : n + 1 - (a + k + 1) < d := by omega
              have hnat := ih (n + 1 - (a + k + 1)) hdist
                (a + k + 1) (c - k) rfl (by omega) (by omega)
              simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hkc] using hnat
          have hPjumpPred :
              AuxiliaryWeightPascal n k ((a : ℤ) + k + 1) ((c : ℤ) - k - 1) := by
            by_cases hneg : (c : ℤ) - k - 1 < 0
            · exact auxiliaryWeightPascal_of_neg_right hneg
            · have hck : k + 1 ≤ c := by omega
              have hdist : n + 1 - (a + k + 1) < d := by omega
              have hnat := ih (n + 1 - (a + k + 1)) hdist
                (a + k + 1) (c - k - 1) rfl (by omega) (by omega)
              norm_num only [Nat.cast_add, Nat.cast_one] at hnat
              rw [show ((c - k - 1 : ℕ) : ℤ) = (c : ℤ) - k - 1 by omega] at hnat
              exact hnat
          unfold AuxiliaryWeightPascal at hPnext hPjump hPjumpPred ⊢
          rw [auxiliaryWeight_recursion hlhsValid hlhsNotBase,
            auxiliaryWeight_recursion_of_valid hpredValid,
            auxiliaryWeight_recursion_of_valid hmidValid,
            auxiliaryWeight_recursion_of_valid hlastValid,
            extendedTrinomial_succ, extendedTrinomial_succ,
            hPnext, hPjump, hPjumpPred]
          ring_nf
  exact main (n + 1 - a) a c rfl hca hac

/-- The paper's full auxiliary-weight dimension recurrence on every valid
lower type. -/
theorem auxiliaryWeightPascal_of_valid_lower {n k : ℕ} {a c : ℤ}
    (hk : 0 < k) (hkn : k ≤ n) (hc : 0 ≤ c) (hca : c ≤ a)
    (hac : a + c ≤ n + 1) : AuxiliaryWeightPascal n k a c := by
  have ha : 0 ≤ a := hc.trans hca
  rw [← Int.toNat_of_nonneg ha, ← Int.toNat_of_nonneg hc] at hca hac ⊢
  exact auxiliaryWeightPascal_of_valid_lower_nat n k a.toNat c.toNat hk hkn
    (by exact_mod_cast hca) (by exact_mod_cast hac)

end Ternary
end WeightedChains
