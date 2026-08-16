import WeightedChains.DTwo.TraceCoordinates

/-!
# Finite enumeration of ternary types

Dimension-indexed ternary type triples form a finite type.  An explicit
embedding into the pair of bounded zero and two counts supplies the `Fintype`
instance used to rewrite the remaining cover calculation as a sum over the
finite triangular type diagram.
-/

noncomputable section

namespace WeightedChains
namespace Ternary
namespace TypeCounts

theorem zeros_le {n : ℕ} (t : TypeCounts n) : t.zeros ≤ n := by
  have hsum := t.sum_eq
  omega

theorem twos_le {n : ℕ} (t : TypeCounts n) : t.twos ≤ n := by
  have hsum := t.sum_eq
  omega

private def finiteCode (n : ℕ) (t : TypeCounts n) :
    Fin (n + 1) × Fin (n + 1) :=
  (⟨t.zeros, Nat.lt_succ_of_le t.zeros_le⟩,
    ⟨t.twos, Nat.lt_succ_of_le t.twos_le⟩)

private theorem finiteCode_injective (n : ℕ) :
    Function.Injective (finiteCode n) := by
  intro s t h
  have hzero : s.zeros = t.zeros := by
    exact congrArg (fun p : Fin (n + 1) × Fin (n + 1) ↦ (p.1 : ℕ)) h
  have htwo : s.twos = t.twos := by
    exact congrArg (fun p : Fin (n + 1) × Fin (n + 1) ↦ (p.2 : ℕ)) h
  apply TypeCounts.ext
  · exact hzero
  · have hs := s.sum_eq
    have ht := t.sum_eq
    omega
  · exact htwo

noncomputable instance (n : ℕ) : Fintype (TypeCounts n) :=
  Fintype.ofInjective (finiteCode n) (finiteCode_injective n)

noncomputable instance (n : ℕ) : DecidableEq (TypeCounts n) :=
  Classical.decEq _

end TypeCounts

namespace BasicChain

/-- The descriptor-derived occupied labels are exactly the lower types and
the upper types strictly beyond the width boundary. -/
theorem occupiedStartTypes_eq_filter_arithmetic (n k : ℕ) (hk : 0 < k) :
    occupiedStartTypes n k =
      Finset.univ.filter fun t : TypeCounts n ↦
        t.twos ≤ t.zeros ∨ t.zeros + k < t.twos := by
  ext t
  rw [mem_occupiedStartTypes_iff_arithmetic k hk]
  simp

end BasicChain
end Ternary
end WeightedChains
