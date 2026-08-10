import WeightedChains.DTwoInnerWeights
import WeightedChains.DTwoWeightPositivity

/-!
# Positivity of the ternary inner starting weights

For a lower inner type, Section 5 expresses the total starting weight as
`U_n(a,c) - U_n(c+k,a-k)`.  This file proves that the difference is positive
away from the exceptional all-ones type.  The proof follows the paper's
induction on the dimension, with the diagonal and lowest-inner-type
cancellations made explicit.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Ternary

/-- The inner difference vanishes at the exceptional all-ones type. -/
@[simp]
theorem innerStartingWeight_zero_zero (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    innerStartingWeight n k 0 0 = 0 := by
  unfold innerStartingWeight
  rw [auxiliaryWeight_zero_zero n k hn hk,
    auxiliaryWeight_eq_zero_of_neg_right (by omega : (0 : ℤ) - k < 0)]
  norm_num

/-- The inner difference is zero when its two displayed auxiliary weights
are both above the valid type triangle. -/
theorem innerStartingWeight_eq_zero_of_lt_add {n k : ℕ} {a c : ℤ}
    (h : (n : ℤ) < a + c) : innerStartingWeight n k a c = 0 := by
  unfold innerStartingWeight
  rw [auxiliaryWeight_eq_zero_of_lt_add h,
    auxiliaryWeight_eq_zero_of_lt_add (show
      (n : ℤ) < (c + k) + (a - k) by omega)]
  norm_num

/-- On the lower-outer boundary `a = c+k`, the two terms in the formal inner
difference coincide. -/
theorem innerStartingWeight_eq_zero_of_outer_boundary
    (n k a c : ℕ) (hboundary : a = c + k) :
    innerStartingWeight n k a c = 0 := by
  have hfirst : (c : ℤ) + k = a := by exact_mod_cast hboundary.symm
  have hsecond : (a : ℤ) - k = c := by omega
  unfold innerStartingWeight
  rw [hfirst, hsecond, sub_self]

/-- At a diagonal type, the first two terms of the dimension recurrence
cancel.  This is the algebraic content of case 2.2 in the paper (with the
corrected shifted coordinate order `U(a+k,a-k)`). -/
private theorem innerStartingWeight_pred_diagonal_add_self_eq_zero
    (n k a : ℕ) (ha : 0 < a) (hvalid : 2 * a ≤ n + 1) :
    innerStartingWeight n k ((a : ℤ) - 1) a +
        innerStartingWeight n k a a = 0 := by
  have htype :
      0 ≤ (a : ℤ) - 1 ∧ 0 ≤ (a : ℤ) ∧
        ((a : ℤ) - 1) + a ≤ n := by
    constructor <;> omega
  have hrec := auxiliaryWeight_recursion_of_valid (n := n) (k := k) htype
  have hcomm := extendedTrinomial_comm n ((a : ℤ) - 1) a
  unfold innerStartingWeight
  rw [hrec, hcomm]
  ring_nf

/-- Positivity of the total starting weight at every genuine lower inner
type.  The origin `(0,0)` is excluded because it represents the singleton
all-ones chain and has weight zero.  The hypothesis `1 < k` is essential on
diagonal inner types, exactly as in the paper's main theorem. -/
theorem innerStartingWeight_pos_of_valid_lower_inner_nat
    (k n a c : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hca : c ≤ a) (hvalid : a + c ≤ n) (hinner : a < c + k)
    (hne : (a, c) ≠ (0, 0)) :
    0 < innerStartingWeight n k a c := by
  induction n, hkn using Nat.le_induction generalizing a c with
  | base =>
      rw [innerStartingWeight_initial k a c (by omega) hvalid hinner]
      exact auxiliaryWeight_initial_pos k a c hca hvalid hne
  | succ n hkn ih =>
      have hrec := innerStartingWeight_succ_of_valid_inner
        n k a c (by omega) hkn hca hvalid hinner
      by_cases hc0 : c = 0
      · subst c
        have ha : 0 < a := by
          simp only [Prod.mk.injEq, and_true, ne_eq] at hne
          omega
        have hak : a < k := by omega
        have hmiddle : 0 < innerStartingWeight n k a 0 := by
          apply ih a 0
          · omega
          · omega
          · omega
          · intro heq
            have : a = 0 := congrArg Prod.fst heq
            omega
        have hfirst :
            0 ≤ innerStartingWeight n k ((a : ℤ) - 1) 0 := by
          by_cases ha1 : a = 1
          · subst a
            norm_num
            rw [innerStartingWeight_zero_zero n k (by omega) (by omega)]
          · have haPredCast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
            rw [← haPredCast]
            exact (ih (a - 1) 0 (by omega) (by omega) (by omega) (by
              intro heq
              have : a - 1 = 0 := congrArg Prod.fst heq
              omega)).le
        have hlast : innerStartingWeight n k a (-1) = 0 := by
          unfold innerStartingWeight
          rw [auxiliaryWeight_eq_zero_of_neg_right (by norm_num : (-1 : ℤ) < 0),
            auxiliaryWeight_eq_zero_of_neg_right (by omega : (a : ℤ) - k < 0)]
          norm_num
        norm_num only [Nat.cast_zero, zero_sub] at hrec ⊢
        rw [hrec, hlast]
        omega
      by_cases hdiag : c = a
      · subst c
        have ha : 0 < a := by omega
        have hcancel := innerStartingWeight_pred_diagonal_add_self_eq_zero
          n k a ha (by omega)
        have haPredCast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
        have hlast : 0 < innerStartingWeight n k a ((a : ℤ) - 1) := by
          rw [← haPredCast]
          apply ih a (a - 1)
          · omega
          · omega
          · omega
          · intro heq
            have : a = 0 := congrArg Prod.fst heq
            omega
        rw [hrec]
        omega
      · have hc : 0 < c := Nat.pos_of_ne_zero hc0
        have hstrict : c < a := lt_of_le_of_ne hca hdiag
        have haPredCast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
        have hcPredCast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
        have hfirst : 0 < innerStartingWeight n k ((a : ℤ) - 1) c := by
          rw [← haPredCast]
          apply ih (a - 1) c
          · omega
          · omega
          · omega
          · intro heq
            have : c = 0 := congrArg Prod.snd heq
            omega
        have hmiddle : 0 ≤ innerStartingWeight n k a c := by
          by_cases hvalidPred : a + c ≤ n
          · exact (ih a c hca hvalidPred hinner hne).le
          · rw [innerStartingWeight_eq_zero_of_lt_add (by omega)]
        have hlast : 0 ≤ innerStartingWeight n k a ((c : ℤ) - 1) := by
          by_cases hboundary : a + 1 = c + k
          · rw [← hcPredCast]
            rw [innerStartingWeight_eq_zero_of_outer_boundary n k a (c - 1) (by
              omega)]
          · have hinnerPred : a < (c - 1) + k := by omega
            rw [← hcPredCast]
            exact (ih a (c - 1) (by omega) (by omega) hinnerPred (by
              intro heq
              have : a = 0 := congrArg Prod.fst heq
              omega)).le
        rw [hrec]
        omega

/-- The corrected Section 5 inner-positivity theorem in the paper's
integer-coordinate notation. -/
theorem innerStartingWeight_pos_of_valid_lower_inner {k n : ℕ} {a c : ℤ}
    (hk : 1 < k) (hkn : k ≤ n) (hc : 0 ≤ c) (hca : c ≤ a)
    (hvalid : a + c ≤ n) (hinner : a < c + k)
    (hne : (a, c) ≠ (0, 0)) :
    0 < innerStartingWeight n k a c := by
  have ha : 0 ≤ a := hc.trans hca
  have haCast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
  have hcCast : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc
  have hcaNat : c.toNat ≤ a.toNat := by
    exact_mod_cast (show (c.toNat : ℤ) ≤ a.toNat by
      simpa only [haCast, hcCast] using hca)
  have hvalidNat : a.toNat + c.toNat ≤ n := by
    exact_mod_cast (show (a.toNat : ℤ) + c.toNat ≤ n by
      simpa only [haCast, hcCast] using hvalid)
  have hinnerNat : a.toNat < c.toNat + k := by
    exact_mod_cast (show (a.toNat : ℤ) < c.toNat + k by
      simpa only [haCast, hcCast] using hinner)
  have hneNat : (a.toNat, c.toNat) ≠ (0, 0) := by
    intro heq
    apply hne
    have haZero : a.toNat = 0 := congrArg Prod.fst heq
    have hcZero : c.toNat = 0 := congrArg Prod.snd heq
    apply Prod.ext
    · exact haCast ▸ congrArg Int.ofNat haZero
    · exact hcCast ▸ congrArg Int.ofNat hcZero
  have hpos := innerStartingWeight_pos_of_valid_lower_inner_nat
    k n a.toNat c.toNat hk hkn hcaNat hvalidNat hinnerNat hneNat
  simpa only [haCast, hcCast] using hpos

end Ternary
end WeightedChains
