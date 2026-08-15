import WeightedChains.Preliminaries

/-!
# Finite cuboids

This file supplies the coordinate-dependent version of the discrete cube used
in the final remark of Appendix 2. A cuboid with side bounds `bounds` is the
product `\prod i, {0, ..., bounds i}`.
-/

set_option autoImplicit false

namespace WeightedChains

/-- The finite cuboid `\prod i, {0, ..., bounds i}`. -/
abbrev Cuboid {n : ℕ} (bounds : Fin n → ℕ) :=
  (i : Fin n) → Fin (bounds i + 1)

namespace Cuboid

/-- The sum of the coordinate bounds, which is the maximum cuboid rank. -/
def totalRank {n : ℕ} (bounds : Fin n → ℕ) : ℕ :=
  ∑ i, bounds i

/-- The rank of a cuboid vertex is the sum of its coordinates. -/
def rank {n : ℕ} {bounds : Fin n → ℕ} (x : Cuboid bounds) : ℕ :=
  ∑ i, (x i : ℕ)

/-- The coordinates on which two cuboid vertices differ. -/
def differingCoordinates {n : ℕ} {bounds : Fin n → ℕ}
    (x y : Cuboid bounds) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i ≠ y i

/-- Hamming distance in a cuboid: the number of differing coordinates. -/
def hammingDistance {n : ℕ} {bounds : Fin n → ℕ}
    (x y : Cuboid bounds) : ℕ :=
  (differingCoordinates x y).card

/-- Cuboid version of the paper's `k`-separation condition. -/
def KSeparated {n : ℕ} {bounds : Fin n → ℕ}
    (A : Set (Cuboid bounds)) (k : ℕ) : Prop :=
  ∀ {x y : Cuboid bounds},
    x ∈ A → y ∈ A → x ≤ y → x ≠ y → k < hammingDistance x y

/-- The lower central rank of a cuboid. -/
def lowerMiddleRank {n : ℕ} (bounds : Fin n → ℕ) : ℕ :=
  totalRank bounds / 2

/-- The upper central rank of a cuboid. -/
def upperMiddleRank {n : ℕ} (bounds : Fin n → ℕ) : ℕ :=
  totalRank bounds - lowerMiddleRank bounds

/-- The lower central layer of a cuboid. -/
def lowerMiddleLayerFinset {n : ℕ} (bounds : Fin n → ℕ) :
    Finset (Cuboid bounds) :=
  Finset.univ.filter fun x ↦ rank x = lowerMiddleRank bounds

/-- The upper central layer of a cuboid. -/
def upperMiddleLayerFinset {n : ℕ} (bounds : Fin n → ℕ) :
    Finset (Cuboid bounds) :=
  Finset.univ.filter fun x ↦ rank x = upperMiddleRank bounds

theorem rank_le {n : ℕ} {bounds : Fin n → ℕ} (x : Cuboid bounds) :
    rank x ≤ totalRank bounds := by
  unfold rank totalRank
  apply Finset.sum_le_sum
  intro i _hi
  exact Nat.le_of_lt_succ (x i).isLt

theorem rank_mono {n : ℕ} {bounds : Fin n → ℕ} {x y : Cuboid bounds}
    (hxy : x ≤ y) : rank x ≤ rank y := by
  unfold rank
  apply Finset.sum_le_sum
  intro i _hi
  exact hxy i

theorem rank_strictMono {n : ℕ} {bounds : Fin n → ℕ} {x y : Cuboid bounds}
    (hxy : x ≤ y) (hne : x ≠ y) : rank x < rank y := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    apply hne
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  unfold rank
  apply Finset.sum_lt_sum
  · intro j _hj
    exact hxy j
  · refine ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hxy i) ?_⟩
    intro hval
    exact hi (Fin.ext hval)

/-- Every fixed-rank layer is `k`-separated, for every `k`. -/
theorem layer_kSeparated {n k r : ℕ} {bounds : Fin n → ℕ} :
    KSeparated ({x : Cuboid bounds | rank x = r} : Set (Cuboid bounds)) k := by
  intro x y hx hy hxy hne
  have hlt := rank_strictMono hxy hne
  simp only [Set.mem_ofPred_eq] at hx hy
  omega

theorem lowerMiddleLayerFinset_kSeparated {n : ℕ} (bounds : Fin n → ℕ) (k : ℕ) :
    KSeparated (lowerMiddleLayerFinset bounds : Set (Cuboid bounds)) k := by
  intro x y hx hy hxy hne
  apply layer_kSeparated (r := lowerMiddleRank bounds)
  · simpa [lowerMiddleLayerFinset] using hx
  · simpa [lowerMiddleLayerFinset] using hy
  · exact hxy
  · exact hne

theorem upperMiddleLayerFinset_kSeparated {n : ℕ} (bounds : Fin n → ℕ) (k : ℕ) :
    KSeparated (upperMiddleLayerFinset bounds : Set (Cuboid bounds)) k := by
  intro x y hx hy hxy hne
  apply layer_kSeparated (r := upperMiddleRank bounds)
  · simpa [upperMiddleLayerFinset] using hx
  · simpa [upperMiddleLayerFinset] using hy
  · exact hxy
  · exact hne

/-- Coordinatewise reflection in the centre of a cuboid. -/
def reflect {n : ℕ} {bounds : Fin n → ℕ} (x : Cuboid bounds) : Cuboid bounds :=
  fun i ↦ (x i).rev

@[simp]
theorem reflect_apply {n : ℕ} {bounds : Fin n → ℕ}
    (x : Cuboid bounds) (i : Fin n) :
    (reflect x i : ℕ) = bounds i - (x i : ℕ) := by
  simp [reflect, Fin.val_rev]

@[simp]
theorem reflect_reflect {n : ℕ} {bounds : Fin n → ℕ} (x : Cuboid bounds) :
    reflect (reflect x) = x := by
  funext i
  simp [reflect]

theorem rank_reflect {n : ℕ} {bounds : Fin n → ℕ} (x : Cuboid bounds) :
    rank (reflect x) = totalRank bounds - rank x := by
  unfold rank totalRank
  simp only [reflect_apply]
  rw [Finset.sum_tsub_distrib]
  intro i _hi
  exact Nat.le_of_lt_succ (x i).isLt

/-- Reflection is an involutive equivalence of the cuboid. -/
def reflectEquiv {n : ℕ} (bounds : Fin n → ℕ) : Cuboid bounds ≃ Cuboid bounds where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect

/-- Reflection identifies the lower and upper central layers. -/
def lowerUpperMiddleEquiv {n : ℕ} (bounds : Fin n → ℕ) :
    {x // x ∈ lowerMiddleLayerFinset bounds} ≃
      {x // x ∈ upperMiddleLayerFinset bounds} where
  toFun x := ⟨reflect x.1, by
    simp only [upperMiddleLayerFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rank_reflect]
    have hx : rank x.1 = lowerMiddleRank bounds := by
      simpa [lowerMiddleLayerFinset] using x.2
    rw [hx]
    unfold upperMiddleRank lowerMiddleRank
    omega⟩
  invFun x := ⟨reflect x.1, by
    simp only [lowerMiddleLayerFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rank_reflect]
    have hx : rank x.1 = upperMiddleRank bounds := by
      simpa [upperMiddleLayerFinset] using x.2
    rw [hx]
    unfold upperMiddleRank lowerMiddleRank
    omega⟩
  left_inv x := by
    apply Subtype.ext
    exact reflect_reflect x.1
  right_inv x := by
    apply Subtype.ext
    exact reflect_reflect x.1

theorem card_lowerMiddleLayer_eq_card_upperMiddleLayer
    {n : ℕ} (bounds : Fin n → ℕ) :
    (lowerMiddleLayerFinset bounds).card = (upperMiddleLayerFinset bounds).card := by
  simpa using Fintype.card_congr (lowerUpperMiddleEquiv bounds)

end Cuboid
end WeightedChains
