import WeightedChains.DTwo.FiniteTypes

/-!
# The telescoping auxiliary incidence sum

For a lower target type `(a,c)`, pairing an inner symmetric metachain with
the corresponding full-width metachain leaves the auxiliary total `U` of
their common raw start.  The possible raw starts form the two alternating
diagonals below.  This file proves that their sum is exactly the trinomial
coefficient, by the local telescoping recurrence used in Section 5.
-/

set_option autoImplicit false

open scoped BigOperators

namespace WeightedChains
namespace Ternary

/-- Auxiliary totals at the even vertices of all possible raw starts through
a target coordinate pair. -/
def evenAuxiliaryIncidenceSum (n k : ℕ) (a c : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1),
    auxiliaryWeight n k (a + i) (c - i)

/-- Auxiliary totals at the odd vertices of all possible raw starts through
a target coordinate pair. -/
def oddAuxiliaryIncidenceSum (n k : ℕ) (a c : ℤ) : ℤ :=
  ∑ i ∈ Finset.range k,
    auxiliaryWeight n k (a + i + 1) (c - i)

/-- The full two-diagonal auxiliary incidence sum. -/
def auxiliaryIncidenceSum (n k : ℕ) (a c : ℤ) : ℤ :=
  evenAuxiliaryIncidenceSum n k a c + oddAuxiliaryIncidenceSum n k a c

private theorem evenAuxiliaryIncidenceSum_sub
    (n k : ℕ) (a c : ℤ) :
    evenAuxiliaryIncidenceSum n k a c -
        evenAuxiliaryIncidenceSum n k (a + 1) (c - 1) =
      auxiliaryWeight n k a c -
        auxiliaryWeight n k (a + k + 1) (c - k - 1) := by
  let middle : ℤ := ∑ i ∈ Finset.range k,
    auxiliaryWeight n k (a + (i + 1)) (c - (i + 1))
  have hleft : evenAuxiliaryIncidenceSum n k a c =
      auxiliaryWeight n k a c + middle := by
    unfold evenAuxiliaryIncidenceSum
    rw [Finset.sum_range_succ']
    have hsum : (∑ i ∈ Finset.range k,
        auxiliaryWeight n k (a + ((i + 1 : ℕ) : ℤ))
          (c - ((i + 1 : ℕ) : ℤ))) = middle := by
      rfl
    rw [hsum]
    norm_num
    ring
  have hright : evenAuxiliaryIncidenceSum n k (a + 1) (c - 1) =
      middle + auxiliaryWeight n k (a + k + 1) (c - k - 1) := by
    unfold evenAuxiliaryIncidenceSum
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _hi
      congr 1 <;> ring
    · congr 1 <;> ring
  rw [hleft, hright]
  ring

private theorem oddAuxiliaryIncidenceSum_sub
    (n k : ℕ) (a c : ℤ) :
    oddAuxiliaryIncidenceSum n k a c -
        oddAuxiliaryIncidenceSum n k (a + 1) (c - 1) =
      auxiliaryWeight n k (a + 1) c -
        auxiliaryWeight n k (a + k + 1) (c - k) := by
  cases k with
  | zero => simp [oddAuxiliaryIncidenceSum]
  | succ k =>
      let middle : ℤ := ∑ i ∈ Finset.range k,
        auxiliaryWeight n (k + 1) (a + (i + 1) + 1) (c - (i + 1))
      have hleft : oddAuxiliaryIncidenceSum n (k + 1) a c =
          auxiliaryWeight n (k + 1) (a + 1) c + middle := by
        unfold oddAuxiliaryIncidenceSum
        rw [Finset.sum_range_succ']
        have hsum : (∑ i ∈ Finset.range k,
            auxiliaryWeight n (k + 1)
              (a + ((i + 1 : ℕ) : ℤ) + 1)
              (c - ((i + 1 : ℕ) : ℤ))) = middle := by
          rfl
        rw [hsum]
        norm_num
        ring
      have hright : oddAuxiliaryIncidenceSum n (k + 1) (a + 1) (c - 1) =
          middle + auxiliaryWeight n (k + 1)
            (a + (k + 1) + 1) (c - (k + 1)) := by
        unfold oddAuxiliaryIncidenceSum
        rw [Finset.sum_range_succ]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _hi
          congr 1 <;> ring
        · congr 1 <;> ring
      rw [hleft, hright]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

/-- Moving one step down the fixed-`a+c` diagonal leaves precisely the four
boundary auxiliary terms in the paper's key recurrence. -/
theorem auxiliaryIncidenceSum_sub
    (n k : ℕ) (a c : ℤ) :
    auxiliaryIncidenceSum n k a c -
        auxiliaryIncidenceSum n k (a + 1) (c - 1) =
      auxiliaryWeight n k a c + auxiliaryWeight n k (a + 1) c -
        auxiliaryWeight n k (a + k + 1) (c - k) -
          auxiliaryWeight n k (a + k + 1) (c - k - 1) := by
  unfold auxiliaryIncidenceSum
  rw [show
    evenAuxiliaryIncidenceSum n k a c + oddAuxiliaryIncidenceSum n k a c -
        (evenAuxiliaryIncidenceSum n k (a + 1) (c - 1) +
          oddAuxiliaryIncidenceSum n k (a + 1) (c - 1)) =
      (evenAuxiliaryIncidenceSum n k a c -
        evenAuxiliaryIncidenceSum n k (a + 1) (c - 1)) +
      (oddAuxiliaryIncidenceSum n k a c -
        oddAuxiliaryIncidenceSum n k (a + 1) (c - 1)) by ring,
    evenAuxiliaryIncidenceSum_sub, oddAuxiliaryIncidenceSum_sub]
  ring

@[simp]
theorem auxiliaryIncidenceSum_eq_zero_of_neg_right
    (n k : ℕ) {a c : ℤ} (hc : c < 0) :
    auxiliaryIncidenceSum n k a c = 0 := by
  unfold auxiliaryIncidenceSum evenAuxiliaryIncidenceSum
    oddAuxiliaryIncidenceSum
  have heven : ∑ i ∈ Finset.range (k + 1),
      auxiliaryWeight n k (a + i) (c - i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact auxiliaryWeight_eq_zero_of_neg_right (by omega)
  have hodd : ∑ i ∈ Finset.range k,
      auxiliaryWeight n k (a + i + 1) (c - i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact auxiliaryWeight_eq_zero_of_neg_right (by omega)
  rw [heven, hodd, add_zero]

/-- The two-diagonal auxiliary incidence sum equals the size of every valid
ternary type. -/
theorem auxiliaryIncidenceSum_eq_extendedTrinomial
    (n k a c : ℕ) (hvalid : a + c ≤ n) :
    auxiliaryIncidenceSum n k a c = extendedTrinomial n a c := by
  induction c generalizing a with
  | zero =>
      have hdiff := auxiliaryIncidenceSum_sub n k (a : ℤ) 0
      have hnegative : auxiliaryIncidenceSum n k ((a : ℤ) + 1) (-1) = 0 :=
        auxiliaryIncidenceSum_eq_zero_of_neg_right n k (by omega)
      have hrec := auxiliaryWeight_recursion_of_valid
        (n := n) (k := k) (a := (a : ℤ)) (c := 0) (by
          constructor <;> omega)
      norm_num only [Nat.cast_zero, zero_sub] at hdiff hrec ⊢
      rw [hnegative] at hdiff
      rw [extendedTrinomial_eq_zero_of_neg_right (by omega : (-1 : ℤ) < 0)] at hrec
      omega
  | succ c ih =>
      have hvalidPred : (a + 1) + c ≤ n := by omega
      have hih := ih (a + 1) hvalidPred
      have hdiff := auxiliaryIncidenceSum_sub n k (a : ℤ) (c + 1)
      have hrec := auxiliaryWeight_recursion_of_valid
        (n := n) (k := k) (a := (a : ℤ)) (c := (c + 1 : ℕ)) (by
          constructor <;> omega)
      norm_num only [Nat.cast_add, Nat.cast_one] at hdiff hrec
      rw [show (c : ℤ) + 1 - 1 = c by ring] at hdiff hrec
      have hih' : auxiliaryIncidenceSum n k ((a : ℤ) + 1) c =
          extendedTrinomial n ((a : ℤ) + 1) c := by
        simpa only [Nat.cast_add, Nat.cast_one] using hih
      rw [hih'] at hdiff
      norm_num only [Nat.cast_add, Nat.cast_one] at ⊢
      omega

end Ternary
end WeightedChains
