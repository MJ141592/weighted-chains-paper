import WeightedChains.ResidueSymmetry

/-!
# Reflection of finite cube families

Coordinate reflection acts on finite vertex families, reverses the cube order,
and preserves Hamming distance and `k`-separation.  This lets equality-case
arguments for the lower reference family be transported to the upper one.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Cube

/-- Pointwise reflection of a finite cube family. -/
def reflectFinset {n d : ℕ} (s : Finset (Cube n d)) : Finset (Cube n d) :=
  s.map (reflectEquiv n d).toEmbedding

@[simp]
theorem mem_reflectFinset_iff {n d : ℕ} {s : Finset (Cube n d)} {x : Cube n d} :
    x ∈ reflectFinset s ↔ reflect x ∈ s := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    change reflect y = x at hxy
    rw [← hxy, reflect_reflect]
    exact hy
  · intro hx
    apply Finset.mem_map.mpr
    exact ⟨reflect x, hx, reflect_reflect x⟩

@[simp]
theorem card_reflectFinset {n d : ℕ} (s : Finset (Cube n d)) :
    (reflectFinset s).card = s.card := by
  simp [reflectFinset]

@[simp]
theorem reflectFinset_reflectFinset {n d : ℕ} (s : Finset (Cube n d)) :
    reflectFinset (reflectFinset s) = s := by
  ext x
  simp

theorem reflect_anti {n d : ℕ} {x y : Cube n d} (hxy : x ≤ y) :
    reflect y ≤ reflect x := by
  intro i
  exact Fin.rev_le_rev.mpr (hxy i)

@[simp]
theorem differingCoordinates_reflect {n d : ℕ} (x y : Cube n d) :
    differingCoordinates (reflect x) (reflect y) = differingCoordinates x y := by
  ext i
  simp only [differingCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
  change ((x i).rev ≠ (y i).rev) ↔ x i ≠ y i
  exact not_congr Fin.rev_inj

@[simp]
theorem hammingDistance_reflect {n d : ℕ} (x y : Cube n d) :
    hammingDistance (reflect x) (reflect y) = hammingDistance x y := by
  rw [hammingDistance, hammingDistance, differingCoordinates_reflect]

/-- Reflection preserves `k`-separation. -/
theorem kSeparated_reflectFinset {n d k : ℕ} {s : Finset (Cube n d)}
    (hs : KSeparated (s : Set (Cube n d)) k) :
    KSeparated (reflectFinset s : Set (Cube n d)) k := by
  intro x y hx hy hxy hne
  have hx' : reflect x ∈ s := mem_reflectFinset_iff.mp hx
  have hy' : reflect y ∈ s := mem_reflectFinset_iff.mp hy
  have hne' : reflect y ≠ reflect x := by
    intro h
    exact hne ((reflectEquiv n d).injective h |>.symm)
  have h := hs hy' hx' (reflect_anti hxy) hne'
  rw [hammingDistance_reflect, hammingDistance_comm] at h
  exact h

/-- The reflected lower reference family is the upper reference family. -/
theorem reflectFinset_lowerResidueFinset (n d k : ℕ) :
    reflectFinset (lowerResidueFinset n d k) = upperResidueFinset n d k := by
  ext x
  rw [mem_reflectFinset_iff, mem_lowerResidueFinset_iff,
    mem_upperResidueFinset_iff]
  have h := reflect_mem_upperResidueFinset_iff
    (n := n) (d := d) (k := k) (reflect x)
  simpa using h.symm

/-- The reflected upper reference family is the lower reference family. -/
theorem reflectFinset_upperResidueFinset (n d k : ℕ) :
    reflectFinset (upperResidueFinset n d k) = lowerResidueFinset n d k := by
  rw [← reflectFinset_reflectFinset (lowerResidueFinset n d k),
    reflectFinset_lowerResidueFinset]

end Cube
end WeightedChains
