import WeightedChains.DTwoWeightPascalLower

/-!
# Positivity of the auxiliary ternary weights

This file proves the corrected form of the outer-weight positivity lemma from
Section 5.  The point `(a,c) = (0,0)` must be excluded: in every positive
dimension its auxiliary weight is zero.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Ternary

/-- The closed form for `U_n(a,c)` in the initial dimension `n = k`, away
from the edge `c = 0`. -/
private def initialWeightClosedForm (n a c : ℕ) : ℤ :=
  (n.choose c : ℤ) * ((n - c - 1).choose (a - 1) : ℤ) -
    (n.choose (c - 1) : ℤ) * ((n - c).choose a : ℤ)

/-- The elementary adjacent-term identity behind the closed form in the
initial dimension. -/
private theorem initialWeightClosedForm_add_succ (n a c : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hac : a + c ≤ n) :
    initialWeightClosedForm n a c + initialWeightClosedForm n (a + 1) c =
      (trinomial n a c : ℤ) - (trinomial n (a + 1) (c - 1) : ℤ) := by
  have hcn : c ≤ n := by omega
  have hsubPos : 0 < n - c := by omega
  have hsub : n - c = (n - c - 1) + 1 := by omega
  have haSucc : a = (a - 1) + 1 := by omega
  have hcPred : c = (c - 1) + 1 := by omega
  have hpredSub : n - (c - 1) = (n - c) + 1 := by omega
  have hchooseA := Nat.choose_succ_succ (n - c - 1) (a - 1)
  simp only [Nat.succ_eq_add_one, ← hsub, ← haSucc] at hchooseA
  have hchooseB := Nat.choose_succ_succ (n - c) a
  simp only [Nat.succ_eq_add_one, ← hpredSub] at hchooseB
  rw [trinomial_comm n a c, trinomial_comm n (a + 1) (c - 1)]
  simp only [trinomial, initialWeightClosedForm]
  rw [hchooseB, hchooseA]
  push_cast
  ring

/-- At the initial dimension `n = k`, every valid nonexceptional lower type
with `c > 0` has the paper's closed form. -/
private theorem auxiliaryWeight_initial_closedForm (n a c : ℕ)
    (hc : 0 < c) (hca : c ≤ a) (hac : a + c ≤ n) :
    auxiliaryWeight n n a c = initialWeightClosedForm n a c := by
  have ha : 0 < a := lt_of_lt_of_le hc hca
  have hbound : a ≤ n - c := by omega
  induction hbound using Nat.decreasingInduction with
  | self =>
      have hvalid :
          0 ≤ ((n - c : ℕ) : ℤ) ∧ 0 ≤ (c : ℤ) ∧
            ((n - c : ℕ) : ℤ) + c ≤ n := by
        constructor <;> omega
      have hnotBase : ¬(((n - c : ℕ) : ℤ) = n ∧ (c : ℤ) = 0) := by omega
      have hcLt : c < n := by omega
      have hnegJump : (c : ℤ) - n < 0 := by omega
      have hnegJumpPred : (c : ℤ) - n - 1 < 0 := by omega
      have habove : (n : ℤ) < ((n - c : ℕ) : ℤ) + 1 + c := by omega
      rw [auxiliaryWeight_recursion hvalid hnotBase,
        auxiliaryWeight_eq_zero_of_lt_add habove,
        auxiliaryWeight_eq_zero_of_neg_right hnegJump,
        auxiliaryWeight_eq_zero_of_neg_right hnegJumpPred]
      have hstep := initialWeightClosedForm_add_succ n (n - c) c
        (by omega) hc (by omega)
      have hnext : initialWeightClosedForm n (n - c + 1) c = 0 := by
        have hchooseA : (n - c - 1).choose (n - c) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have hchooseB : (n - c).choose (n - c + 1) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp [initialWeightClosedForm, hchooseA]
      rw [hnext, add_zero] at hstep
      have haCast : (((n - c) + 1 : ℕ) : ℤ) = ((n - c : ℕ) : ℤ) + 1 := by
        omega
      have hcCast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
      rw [← haCast, ← hcCast, extendedTrinomial_ofNat]
      simpa only [extendedTrinomial_ofNat, sub_zero, add_zero] using hstep.symm
  | of_succ a han ih =>
      have ha' : 0 < a := by omega
      have hac' : a + c ≤ n := by omega
      have hvalid :
          0 ≤ (a : ℤ) ∧ 0 ≤ (c : ℤ) ∧ (a : ℤ) + c ≤ n := by
        constructor <;> omega
      have hnotBase : ¬((a : ℤ) = n ∧ (c : ℤ) = 0) := by omega
      have hcLt : c < n := by omega
      have hnegJump : (c : ℤ) - n < 0 := by omega
      have hnegJumpPred : (c : ℤ) - n - 1 < 0 := by omega
      rw [auxiliaryWeight_recursion hvalid hnotBase,
        auxiliaryWeight_eq_zero_of_neg_right hnegJump,
        auxiliaryWeight_eq_zero_of_neg_right hnegJumpPred]
      have ih' : auxiliaryWeight n n ((a : ℤ) + 1) c =
          initialWeightClosedForm n (a + 1) c := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          ih (by omega) (by omega) (by omega)
      rw [ih']
      have hstep := initialWeightClosedForm_add_succ n a c ha' hc hac'
      have haCast : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by omega
      have hcCast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
      rw [← haCast, ← hcCast, extendedTrinomial_ofNat, extendedTrinomial_ofNat]
      omega

/-- The initial-dimension closed form is strictly positive on a genuine
lower type. -/
private theorem initialWeightClosedForm_pos (n a c : ℕ)
    (hc : 0 < c) (hca : c ≤ a) (hac : a + c ≤ n) :
    0 < initialWeightClosedForm n a c := by
  have ha : 0 < a := lt_of_lt_of_le hc hca
  have hcn : c ≤ n := by omega
  have hsubPos : 0 < n - c := by omega
  have hsub : n - c = (n - c - 1) + 1 := by omega
  have haSucc : a = (a - 1) + 1 := by omega
  have hcSucc : c = (c - 1) + 1 := by omega
  have hcSub : n - (c - 1) = n - c + 1 := by omega
  have hchooseC := Nat.choose_succ_right_eq n (c - 1)
  simp only [← hcSucc, hcSub] at hchooseC
  have hchooseA := Nat.add_one_mul_choose_eq (n - c - 1) (a - 1)
  simp only [← hsub, ← haSucc] at hchooseA
  let left : ℕ := n.choose c * (n - c - 1).choose (a - 1)
  let right : ℕ := n.choose (c - 1) * (n - c).choose a
  let small : ℕ := c * (n - c)
  let large : ℕ := a * (n - c + 1)
  have hcross : left * small = right * large := by
    dsimp only [left, right, small, large]
    calc
      n.choose c * (n - c - 1).choose (a - 1) * (c * (n - c)) =
          (n.choose c * c) *
            ((n - c) * (n - c - 1).choose (a - 1)) := by ring
      _ = (n.choose (c - 1) * (n - c + 1)) *
            ((n - c).choose a * a) := by rw [hchooseC, hchooseA]
      _ = (n.choose (c - 1) * (n - c).choose a) *
            (a * (n - c + 1)) := by ring
  have hright : 0 < right := by
    dsimp only [right]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hsmall : 0 < small := by
    dsimp only [small]
    exact Nat.mul_pos hc hsubPos
  have hsmallLarge : small < large := by
    dsimp only [small, large]
    calc
      c * (n - c) ≤ a * (n - c) := Nat.mul_le_mul_right (n - c) hca
      _ < a * (n - c + 1) := by nlinarith
  have hscaled : right * small < left * small := by
    calc
      right * small < right * large := (Nat.mul_lt_mul_left hright).2 hsmallLarge
      _ = left * small := hcross.symm
  have hrightLeft : right < left := by
    exact (Nat.mul_lt_mul_right hsmall).mp hscaled
  unfold initialWeightClosedForm
  exact sub_pos.mpr (by exact_mod_cast hrightLeft)

/-- Positivity in the base dimension `n = k`.  The exceptional origin is
excluded explicitly. -/
theorem auxiliaryWeight_initial_pos (n a c : ℕ)
    (hca : c ≤ a) (hac : a + c ≤ n) (hne : (a, c) ≠ (0, 0)) :
    0 < auxiliaryWeight n n a c := by
  by_cases hc0 : c = 0
  · subst c
    have ha : 0 < a := by
      simp only [Prod.mk.injEq, and_true, ne_eq] at hne
      omega
    exact auxiliaryWeight_zero_right_pos n n a (by omega) ha (by omega)
  · have hc : 0 < c := Nat.pos_of_ne_zero hc0
    rw [auxiliaryWeight_initial_closedForm n a c hc hca hac]
    exact initialWeightClosedForm_pos n a c hc hca hac

/-- Corrected lower-type positivity for natural coordinates.  The origin is
the unique exception in positive dimension. -/
theorem auxiliaryWeight_pos_of_valid_lower_nat (k n a c : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) (hca : c ≤ a) (hac : a + c ≤ n)
    (hne : (a, c) ≠ (0, 0)) :
    0 < auxiliaryWeight n k a c := by
  induction n, hkn using Nat.le_induction generalizing a c with
  | base =>
      exact auxiliaryWeight_initial_pos k a c hca hac hne
  | succ n hkn ih =>
      by_cases hc0 : c = 0
      · subst c
        have ha : 0 < a := by
          simp only [Prod.mk.injEq, and_true, ne_eq] at hne
          omega
        exact auxiliaryWeight_zero_right_pos (n + 1) k a hk ha (by omega)
      have hc : 0 < c := Nat.pos_of_ne_zero hc0
      have ha : 0 < a := lt_of_lt_of_le hc hca
      have hpascal := auxiliaryWeightPascal_of_valid_lower
        (n := n) (k := k) (a := (a : ℤ)) (c := (c : ℤ)) hk hkn
        (by omega) (by exact_mod_cast hca) (by exact_mod_cast hac)
      unfold AuxiliaryWeightPascal at hpascal
      by_cases hdiag : c = a
      · subst c
        have hpredValid :
            0 ≤ (a : ℤ) - 1 ∧ 0 ≤ (a : ℤ) ∧
              ((a : ℤ) - 1) + a ≤ n := by
          constructor <;> omega
        have hpredNotBase : ¬((a : ℤ) - 1 = n ∧ (a : ℤ) = 0) := by omega
        have hrec := auxiliaryWeight_recursion (k := k) hpredValid hpredNotBase
        have htri :
            extendedTrinomial n ((a : ℤ) - 1) a =
              extendedTrinomial n a ((a : ℤ) - 1) :=
          extendedTrinomial_comm n ((a : ℤ) - 1) a
        have haPredCast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
        have hlast : 0 < auxiliaryWeight n k a ((a : ℤ) - 1) := by
          rw [← haPredCast]
          apply ih a (a - 1)
          · omega
          · omega
          · intro heq
            have : a = 0 := congrArg Prod.fst heq
            omega
        have hjump : 0 ≤ auxiliaryWeight n k ((a : ℤ) + k) ((a : ℤ) - k) := by
          by_cases hneg : (a : ℤ) - k < 0
          · rw [auxiliaryWeight_eq_zero_of_neg_right hneg]
          by_cases habove : (n : ℤ) < ((a : ℤ) + k) + ((a : ℤ) - k)
          · rw [auxiliaryWeight_eq_zero_of_lt_add habove]
          have hkA : k ≤ a := by omega
          have hcast : ((a - k : ℕ) : ℤ) = (a : ℤ) - k := by omega
          have htwoZ : (2 : ℤ) * a ≤ n := by omega
          have htwo : 2 * a ≤ n := by exact_mod_cast htwoZ
          have hsum : (a + k) + (a - k) ≤ n := by omega
          rw [← hcast]
          exact (ih (a + k) (a - k) (by omega) hsum (by
            intro heq
            have : a + k = 0 := congrArg Prod.fst heq
            omega)).le
        have hjumpPred :
            0 ≤ auxiliaryWeight n k ((a : ℤ) + k) ((a : ℤ) - k - 1) := by
          by_cases hneg : (a : ℤ) - k - 1 < 0
          · rw [auxiliaryWeight_eq_zero_of_neg_right hneg]
          have hkA : k + 1 ≤ a := by omega
          have hcast : ((a - k - 1 : ℕ) : ℤ) = (a : ℤ) - k - 1 := by omega
          have hdecomp : (a - k - 1) + (k + 1) = a := by omega
          have hsum : (a + k) + (a - k - 1) ≤ n := by omega
          rw [← hcast]
          exact (ih (a + k) (a - k - 1) (by omega) hsum (by
            intro heq
            have : a + k = 0 := congrArg Prod.fst heq
            omega)).le
        rw [htri] at hrec
        ring_nf at hrec hpascal
        rw [Nat.add_comm 1 n] at hpascal
        have hpredCoord : (-1 : ℤ) + a = (a : ℤ) - 1 := by ring
        have hjumpPredCoord : (a : ℤ) - 1 - k = (a : ℤ) - k - 1 := by ring
        rw [hpredCoord] at hrec hpascal
        rw [hjumpPredCoord] at hrec
        omega

      · have hstrict : c < a := lt_of_le_of_ne hca hdiag
        have haPredCast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
        have hcPredCast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
        have hfirst : 0 < auxiliaryWeight n k ((a : ℤ) - 1) c := by
          rw [← haPredCast]
          apply ih (a - 1) c
          · omega
          · omega
          · intro heq
            have : c = 0 := congrArg Prod.snd heq
            omega
        have hlast : 0 < auxiliaryWeight n k a ((c : ℤ) - 1) := by
          rw [← hcPredCast]
          apply ih a (c - 1)
          · omega
          · omega
          · intro heq
            have : a = 0 := congrArg Prod.fst heq
            omega
        have hmiddle : 0 ≤ auxiliaryWeight n k a c := by
          by_cases hacn : a + c ≤ n
          · exact (ih a c hca hacn hne).le
          · have habove : (n : ℤ) < (a : ℤ) + c := by omega
            rw [auxiliaryWeight_eq_zero_of_lt_add habove]
        omega

/-- The corrected Section 5 lower-type positivity theorem.  The paper's
statement must exclude `(a,c) = (0,0)`, whose weight is zero in every
positive dimension. -/
theorem auxiliaryWeight_pos_of_valid_lower {k n : ℕ} {a c : ℤ}
    (hk : 0 < k) (hkn : k ≤ n) (hc : 0 ≤ c) (hca : c ≤ a)
    (hac : a + c ≤ n) (hne : (a, c) ≠ (0, 0)) :
    0 < auxiliaryWeight n k a c := by
  have ha : 0 ≤ a := hc.trans hca
  have haCast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
  have hcCast : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc
  have hcaNat : c.toNat ≤ a.toNat := by
    exact_mod_cast (show (c.toNat : ℤ) ≤ a.toNat by simpa [haCast, hcCast] using hca)
  have hacNat : a.toNat + c.toNat ≤ n := by
    exact_mod_cast (show (a.toNat : ℤ) + c.toNat ≤ n by
      simpa [haCast, hcCast] using hac)
  have hneNat : (a.toNat, c.toNat) ≠ (0, 0) := by
    intro heq
    apply hne
    have haZero : a.toNat = 0 := congrArg Prod.fst heq
    have hcZero : c.toNat = 0 := congrArg Prod.snd heq
    apply Prod.ext
    · exact haCast ▸ congrArg Int.ofNat haZero
    · exact hcCast ▸ congrArg Int.ofNat hcZero
  have hpos := auxiliaryWeight_pos_of_valid_lower_nat k n a.toNat c.toNat
    hk hkn hcaNat hacNat hneNat
  simpa only [haCast, hcCast] using hpos

end Ternary
end WeightedChains
