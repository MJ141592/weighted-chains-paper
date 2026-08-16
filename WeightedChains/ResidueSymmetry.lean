import WeightedChains.GoodChainResidues

/-!
# Reflection symmetry of the distinguished residue families

Coordinatewise reflection in the middle of the cube exchanges the paper's
lower and upper residue families.  In particular, the two candidate extremal
families have equal cardinality.
-/

namespace WeightedChains
namespace Cube

/-- Reflect every coordinate by `j ↦ d-j`. -/
def reflect {n d : ℕ} (x : Cube n d) : Cube n d := fun i ↦ (x i).rev

@[simp]
theorem reflect_apply {n d : ℕ} (x : Cube n d) (i : Fin n) :
    (reflect x i : ℕ) = d - (x i : ℕ) := by
  simp [reflect, Fin.val_rev]

@[simp]
theorem reflect_reflect {n d : ℕ} (x : Cube n d) : reflect (reflect x) = x := by
  funext i
  simp [reflect]

/-- Reflection complements the rank around `n*d`. -/
theorem rank_reflect {n d : ℕ} (x : Cube n d) :
    rank (reflect x) = n * d - rank x := by
  unfold rank
  simp only [reflect_apply]
  rw [Finset.sum_tsub_distrib]
  · simp
  · intro i _hi
    exact Nat.le_of_lt_succ (x i).isLt

/-- Coordinatewise reflection as an involutive equivalence of the cube. -/
def reflectEquiv (n d : ℕ) : Cube n d ≃ Cube n d where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect

theorem reflect_mem_upperResidueFinset_iff {n d k : ℕ} (x : Cube n d) :
    reflect x ∈ upperResidueFinset n d k ↔ x ∈ lowerResidueFinset n d k := by
  simp only [mem_upperResidueFinset_iff, mem_lowerResidueFinset_iff,
    upperResidueFamily, lowerResidueFamily, residueFamily, Set.mem_ofPred_eq]
  have hlower : lowerMiddleRank n d ≤ n * d := by
    unfold lowerMiddleRank
    omega
  have hupper : upperMiddleRank n d ≤ n * d := by
    unfold upperMiddleRank
    omega
  constructor
  · intro h
    have hsub := (Nat.ModEq.refl (n * d)).sub (rank_le (reflect x)) hupper h
    have hleft : n * d - rank (reflect x) = rank x := by
      rw [rank_reflect]
      have := rank_le x
      omega
    have hright : n * d - upperMiddleRank n d = lowerMiddleRank n d := by
      unfold upperMiddleRank
      omega
    rwa [hleft, hright] at hsub
  · intro h
    have hsub := (Nat.ModEq.refl (n * d)).sub (rank_le x) hlower h
    simpa only [rank_reflect, upperMiddleRank] using hsub

/-- Reflection restricts to an equivalence between the two distinguished
finite residue families. -/
def lowerUpperResidueEquiv (n d k : ℕ) :
    {x // x ∈ lowerResidueFinset n d k} ≃ {x // x ∈ upperResidueFinset n d k} where
  toFun x := ⟨reflect x.1,
    (reflect_mem_upperResidueFinset_iff (n := n) (d := d) (k := k) x.1).2 x.property⟩
  invFun x := ⟨reflect x.1, by
    rw [← reflect_mem_upperResidueFinset_iff (n := n) (d := d) (k := k), reflect_reflect]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact reflect_reflect x.1
  right_inv x := by
    apply Subtype.ext
    exact reflect_reflect x.1

/-- The two candidate extremal families in the paper have the same size. -/
theorem card_lowerResidueFinset_eq_card_upperResidueFinset (n d k : ℕ) :
    (lowerResidueFinset n d k).card = (upperResidueFinset n d k).card := by
  simpa using Fintype.card_congr (lowerUpperResidueEquiv n d k)

end Cube
end WeightedChains
