import WeightedChains.DOne.MiddleUniqueness

/-!
# Finite layers of the Boolean cube

The `a`-th Boolean layer is identified with the `a`-element subsets of the
coordinate set.  Its cardinality is therefore `n.choose a`.
-/

set_option autoImplicit false

namespace WeightedChains
namespace DOne

open DOneMiddleUniqueness

/-- The finite set of Boolean vertices of rank `a`. -/
def booleanLayerFinset (n a : ℕ) : Finset (Cube n 1) :=
  ((Finset.univ : Finset (Fin n)).powersetCard a).image ofFinset

@[simp]
theorem mem_booleanLayerFinset_iff {n a : ℕ} {x : Cube n 1} :
    x ∈ booleanLayerFinset n a ↔ Cube.rank x = a := by
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hx
    rw [← hsx]
    exact rank_ofFinset s |>.trans (Finset.mem_powersetCard.mp hs).2
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨ones x, ?_, ofFinset_ones x⟩
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, (rank_eq_card_ones x).symm.trans hx⟩

theorem coe_booleanLayerFinset (n a : ℕ) :
    (booleanLayerFinset n a : Set (Cube n 1)) = Cube.layer n 1 a := by
  ext x
  exact mem_booleanLayerFinset_iff

/-- The usual binomial formula for a Boolean layer. -/
@[simp]
theorem card_booleanLayerFinset (n a : ℕ) :
    (booleanLayerFinset n a).card = n.choose a := by
  unfold booleanLayerFinset
  have hinjective : Function.Injective (@ofFinset n) := by
    intro s t hst
    exact (cubeEquivFinset n).symm.injective hst
  rw [Finset.card_image_of_injective _ hinjective, Finset.card_powersetCard]
  simp

theorem booleanLayerFinset_nonempty_iff (n a : ℕ) :
    (booleanLayerFinset n a).Nonempty ↔ a ≤ n := by
  constructor
  · intro hnonempty
    have hpositive : 0 < n.choose a := by
      rw [← card_booleanLayerFinset]
      exact Finset.card_pos.mpr hnonempty
    by_contra hle
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hle)] at hpositive
    exact Nat.lt_irrefl 0 hpositive
  · intro hle
    apply Finset.card_pos.mp
    rw [card_booleanLayerFinset]
    exact Nat.choose_pos hle

end DOne
end WeightedChains
