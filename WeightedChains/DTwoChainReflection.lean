import WeightedChains.DTwoChainExistence
import WeightedChains.ResidueSymmetry

/-!
# Reflection of basic ternary chains

Coordinatewise reflection `0 ↔ 2` reverses the order on the ternary cube.
Reading the selected coordinates of a basic chain in reverse order therefore
produces another basic chain whose vertices are the reflected vertices of the
old chain in reverse time.  This file packages that operation as an
involutive equivalence and records its incidence and goodness covariance.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

/-- The selected coordinates of a basic chain, read from last to first. -/
def reverseCoordinate (B : BasicChain n) : Fin B.width ↪ Fin n where
  toFun i := B.coordinate i.rev
  inj' := B.coordinate.injective.comp Fin.rev_injective

@[simp]
theorem reverseCoordinate_apply (B : BasicChain n) (i : Fin B.width) :
    B.reverseCoordinate i = B.coordinate i.rev := rfl

/-- At a selected coordinate, completion is exactly the displayed time
inequality for its coordinate-list index. -/
theorem reachedTwo_coordinate_iff (B : BasicChain n) (t : ℕ) (j : Fin B.width) :
    B.reachedTwo t (B.coordinate j) ↔ 2 * ((j : ℕ) + 1) ≤ t := by
  constructor
  · rintro ⟨i, hi, ht⟩
    have hij : i = j := B.coordinate.injective hi
    simpa only [hij] using ht
  · intro ht
    exact ⟨j, rfl, ht⟩

/-- At a selected coordinate, the first change is exactly the displayed time
inequality for its coordinate-list index. -/
theorem reachedOne_coordinate_iff (B : BasicChain n) (t : ℕ) (j : Fin B.width) :
    B.reachedOne t (B.coordinate j) ↔ 2 * (j : ℕ) + 1 ≤ t := by
  constructor
  · rintro ⟨i, hi, ht⟩
    have hij : i = j := B.coordinate.injective hi
    simpa only [hij] using ht
  · intro ht
    exact ⟨j, rfl, ht⟩

/-- Complement every vertex of a basic chain and reverse its order. -/
def reflect (B : BasicChain n) : BasicChain n where
  width := B.width
  start := Cube.reflect B.toChain.last
  coordinate := B.reverseCoordinate
  start_coordinate := by
    intro i
    have hmem : B.coordinate i.rev ∈ B.initialSegment B.width := by
      rw [B.mem_initialSegment_iff]
      exact ⟨i.rev, i.rev.isLt, rfl⟩
    have hlast : B.toChain.last (B.coordinate i.rev) = 2 := by
      rw [B.toChain_last, evenVertex, if_pos hmem]
    change (B.toChain.last (B.coordinate i.rev)).rev = 0
    simp [hlast]

@[simp]
theorem reflect_width (B : BasicChain n) : B.reflect.width = B.width := rfl

@[simp]
theorem reflect_start (B : BasicChain n) :
    B.reflect.start = Cube.reflect B.toChain.last := rfl

@[simp]
theorem reflect_coordinate (B : BasicChain n) (i : Fin B.width) :
    B.reflect.coordinate i = B.coordinate i.rev := rfl

/-- A reflected basic chain visits the pointwise reflections of the original
vertices in reverse time. -/
theorem vertexAt_reflect (B : BasicChain n) (t : ℕ) (ht : t ≤ 2 * B.width) :
    B.reflect.vertexAt t = Cube.reflect (B.vertexAt (2 * B.width - t)) := by
  funext q
  change B.reflect.vertexAt t q = (B.vertexAt (2 * B.width - t) q).rev
  by_cases hselected : ∃ j : Fin B.width, B.coordinate j = q
  · obtain ⟨j, rfl⟩ := hselected
    have hnewTwo :
        B.reflect.reachedTwo t (B.coordinate j) ↔
          2 * ((j.rev : ℕ) + 1) ≤ t := by
      simpa only [reflect_coordinate, Fin.rev_rev] using
        B.reflect.reachedTwo_coordinate_iff t j.rev
    have hnewOne :
        B.reflect.reachedOne t (B.coordinate j) ↔
          2 * (j.rev : ℕ) + 1 ≤ t := by
      simpa only [reflect_coordinate, Fin.rev_rev] using
        B.reflect.reachedOne_coordinate_iff t j.rev
    have holdTwo :
        B.reachedTwo (2 * B.width - t) (B.coordinate j) ↔
          2 * ((j : ℕ) + 1) ≤ 2 * B.width - t :=
      B.reachedTwo_coordinate_iff (2 * B.width - t) j
    have holdOne :
        B.reachedOne (2 * B.width - t) (B.coordinate j) ↔
          2 * (j : ℕ) + 1 ≤ 2 * B.width - t :=
      B.reachedOne_coordinate_iff (2 * B.width - t) j
    by_cases hn2 : B.reflect.reachedTwo t (B.coordinate j)
    · have hn2' := hnewTwo.mp hn2
      have ho1 : ¬B.reachedOne (2 * B.width - t) (B.coordinate j) := by
        rw [holdOne]
        simp only [Fin.val_rev] at hn2'
        omega
      have ho2 : ¬B.reachedTwo (2 * B.width - t) (B.coordinate j) := by
        intro h
        exact ho1 (B.reachedTwo_implies_reachedOne h)
      have hnewValue : B.reflect.vertexAt t (B.coordinate j) = 2 := by
        simp [vertexAt, hn2]
      have holdValue : B.vertexAt (2 * B.width - t) (B.coordinate j) = 0 := by
        rw [vertexAt, if_neg ho2, if_neg ho1, B.start_coordinate]
      rw [hnewValue, holdValue]
      rfl
    · by_cases hn1 : B.reflect.reachedOne t (B.coordinate j)
      · have hn2' := hnewTwo.not.mp hn2
        have hn1' := hnewOne.mp hn1
        have ho1 : B.reachedOne (2 * B.width - t) (B.coordinate j) := by
          rw [holdOne]
          simp only [Fin.val_rev] at hn2' hn1'
          omega
        have ho2 : ¬B.reachedTwo (2 * B.width - t) (B.coordinate j) := by
          rw [holdTwo]
          simp only [Fin.val_rev] at hn2' hn1'
          omega
        have hnewValue : B.reflect.vertexAt t (B.coordinate j) = 1 := by
          rw [vertexAt, if_neg hn2, if_pos hn1]
        have holdValue : B.vertexAt (2 * B.width - t) (B.coordinate j) = 1 := by
          rw [vertexAt, if_neg ho2, if_pos ho1]
        rw [hnewValue, holdValue]
        rfl
      · have hn1' := hnewOne.not.mp hn1
        have ho2 : B.reachedTwo (2 * B.width - t) (B.coordinate j) := by
          rw [holdTwo]
          simp only [Fin.val_rev] at hn1'
          omega
        have hnewValue : B.reflect.vertexAt t (B.coordinate j) = 0 := by
          rw [vertexAt, if_neg hn2, if_neg hn1]
          have hstart := B.reflect.start_coordinate j.rev
          change B.reflect.start (B.coordinate j.rev.rev) = 0 at hstart
          simpa only [Fin.rev_rev] using hstart
        have holdValue : B.vertexAt (2 * B.width - t) (B.coordinate j) = 2 := by
          rw [vertexAt, if_pos ho2]
        rw [hnewValue, holdValue]
        rfl
  · have holdTwo : ¬B.reachedTwo (2 * B.width - t) q := by
      rintro ⟨j, hj, _ht⟩
      exact hselected ⟨j, hj⟩
    have holdOne : ¬B.reachedOne (2 * B.width - t) q := by
      rintro ⟨j, hj, _ht⟩
      exact hselected ⟨j, hj⟩
    have hnewTwo : ¬B.reflect.reachedTwo t q := by
      rintro ⟨j, hj, _ht⟩
      apply hselected
      change B.coordinate j.rev = q at hj
      exact ⟨j.rev, hj⟩
    have hnewOne : ¬B.reflect.reachedOne t q := by
      rintro ⟨j, hj, _ht⟩
      apply hselected
      change B.coordinate j.rev = q at hj
      exact ⟨j.rev, hj⟩
    have hnotmem : q ∉ B.initialSegment B.width := by
      intro hmem
      obtain ⟨j, _hj, hjq⟩ := (B.mem_initialSegment_iff B.width q).mp hmem
      exact hselected ⟨j, hjq⟩
    have hlast : B.toChain.last q = B.start q := by
      rw [B.toChain_last, evenVertex, if_neg hnotmem]
    have hnewValue : B.reflect.vertexAt t q = B.reflect.start q := by
      rw [vertexAt, if_neg hnewTwo, if_neg hnewOne]
    have holdValue : B.vertexAt (2 * B.width - t) q = B.start q := by
      rw [vertexAt, if_neg holdTwo, if_neg holdOne]
    rw [hnewValue, reflect_start, holdValue]
    change (B.toChain.last q).rev = (B.start q).rev
    rw [hlast]

/-- Finite-index form of `vertexAt_reflect`, matching the represented chain's
index type exactly. -/
theorem vertexAt_reflect_fin (B : BasicChain n) (i : Fin (2 * B.width + 1)) :
    B.reflect.vertexAt i = Cube.reflect (B.vertexAt i.rev) := by
  have hrev : 2 * B.width - (i : ℕ) = (i.rev : ℕ) := by
    simp only [Fin.val_rev]
    omega
  rw [B.vertexAt_reflect i (Nat.le_of_lt_succ i.isLt), hrev]

/-- The represented-chain form of the pointwise reflection identity. -/
theorem toChain_vertex_reflect (B : BasicChain n) (i : Fin (2 * B.width + 1)) :
    B.reflect.toChain.vertex i = Cube.reflect (B.toChain.vertex i.rev) :=
  B.vertexAt_reflect_fin i

/-- The reflected chain starts at the reflection of the old last vertex. -/
@[simp]
theorem toChain_first_reflect (B : BasicChain n) :
    B.reflect.toChain.first = Cube.reflect B.toChain.last := by
  rw [B.reflect.toChain_first, reflect_start]

/-- The reflected chain ends at the reflection of the old first vertex. -/
@[simp]
theorem toChain_last_reflect (B : BasicChain n) :
    B.reflect.toChain.last = Cube.reflect B.start := by
  change B.reflect.vertexAt (2 * B.width) = Cube.reflect B.start
  rw [B.vertexAt_reflect (2 * B.width) le_rfl, Nat.sub_self]
  have hzero := B.toChain_first
  change B.vertexAt 0 = B.start at hzero
  rw [hzero]

/-- Reflecting and reversing a basic-chain descriptor twice returns the
original descriptor. -/
@[simp]
theorem reflect_reflect (B : BasicChain n) : B.reflect.reflect = B := by
  apply BasicChain.ext
  · rfl
  · change Cube.reflect B.reflect.toChain.last = B.start
    rw [B.toChain_last_reflect, Cube.reflect_reflect]
  · apply heq_of_eq
    apply DFunLike.ext _ _
    intro i
    change B.coordinate i.rev.rev = B.coordinate i
    rw [Fin.rev_rev]

/-- Reflection and time reversal as an involutive equivalence of finite basic
chain descriptors. -/
def reflectEquiv (n : ℕ) : BasicChain n ≃ BasicChain n where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect

/-- Membership covariance for the finset of represented vertices. -/
theorem mem_vertices_reflect_iff (B : BasicChain n) (x : Cube n 2) :
    x ∈ B.reflect.toChain.vertices ↔ Cube.reflect x ∈ B.toChain.vertices := by
  rw [Chain.mem_vertices_iff, Chain.mem_vertices_iff]
  change
    (∃ i : Fin (2 * B.width + 1), B.reflect.vertexAt i = x) ↔
      ∃ i : Fin (2 * B.width + 1), B.vertexAt i = Cube.reflect x
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i.rev, ?_⟩
    have hreflected := congrArg Cube.reflect hi
    rw [B.vertexAt_reflect_fin, Cube.reflect_reflect] at hreflected
    simpa only [Fin.rev_rev] using hreflected
  · rintro ⟨i, hi⟩
    refine ⟨i.rev, ?_⟩
    rw [B.vertexAt_reflect_fin, Fin.rev_rev, hi, Cube.reflect_reflect]

/-- As finsets, the reflected chain's vertices are precisely the pointwise
reflections of the old chain's vertices. -/
theorem vertices_reflect (B : BasicChain n) :
    B.reflect.toChain.vertices = B.toChain.vertices.image Cube.reflect := by
  ext x
  rw [B.mem_vertices_reflect_iff]
  constructor
  · intro hx
    rw [Finset.mem_image]
    exact ⟨Cube.reflect x, hx, Cube.reflect_reflect x⟩
  · rw [Finset.mem_image]
    rintro ⟨y, hy, hyx⟩
    rw [← hyx, Cube.reflect_reflect]
    exact hy

/-- Reflection preserves the descriptor width. -/
@[simp]
theorem toChain_width_reflect (B : BasicChain n) :
    B.reflect.toChain.width = B.toChain.width := by
  rw [B.reflect.toChain_width, B.toChain_width, reflect_width]

/-- Reflection preserves the represented-chain length. -/
@[simp]
theorem toChain_length_reflect (B : BasicChain n) :
    B.reflect.toChain.length = B.toChain.length := by
  rw [B.reflect.toChain_length, B.toChain_length, reflect_width]

/-- Reflection and reversal preserve chain symmetry. -/
theorem toChain_symmetric_reflect_iff (B : BasicChain n) :
    B.reflect.toChain.Symmetric ↔ B.toChain.Symmetric := by
  rw [Chain.symmetric_iff_endpoint B.reflect.toChain B.reflect.toChain_saturated,
    Chain.symmetric_iff_endpoint B.toChain B.toChain_saturated,
    B.toChain_first_reflect, B.toChain_last_reflect, B.toChain_first,
    Cube.rank_reflect, Cube.rank_reflect]
  have hfirst := Cube.rank_le B.start
  have hlast := Cube.rank_le B.toChain.last
  omega

/-- Reflection and reversal preserve the paper's predicate of being a good
chain, for every separation parameter. -/
theorem toChain_good_reflect_iff (B : BasicChain n) (k : ℕ) :
    B.reflect.toChain.Good k ↔ B.toChain.Good k := by
  simp only [Chain.Good, B.reflect.toChain_saturated, B.toChain_saturated,
    true_and, B.toChain_width_reflect, B.toChain_length_reflect,
    B.toChain_symmetric_reflect_iff]

/-- Every ternary vertex is an endpoint of some basic good chain.  Lower-half
vertices are initial endpoints; for an upper-half vertex, construct a chain
from its lower-half reflection and reverse it. -/
theorem exists_good_with_endpoint (x : Cube n 2) (k : ℕ) :
    ∃ B : BasicChain n,
      B.toChain.Good k ∧ (B.toChain.first = x ∨ B.toChain.last = x) := by
  by_cases hlower : Cube.rank x ≤ n
  · obtain ⟨B, hstart, hgood⟩ := exists_good_starting_at_of_rank_le x k hlower
    refine ⟨B, hgood, Or.inl ?_⟩
    rw [B.toChain_first, hstart]
  · have hreflectLower : Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      have hrank := Cube.rank_le x
      omega
    obtain ⟨B, hstart, hgood⟩ :=
      exists_good_starting_at_of_rank_le (Cube.reflect x) k hreflectLower
    refine ⟨B.reflect, (B.toChain_good_reflect_iff k).mpr hgood, Or.inr ?_⟩
    rw [B.toChain_last_reflect, hstart, Cube.reflect_reflect]

/-- In particular, every ternary vertex lies on a represented basic good
chain. -/
theorem exists_good_containing (x : Cube n 2) (k : ℕ) :
    ∃ B : BasicChain n, x ∈ B.toChain.vertices ∧ B.toChain.Good k := by
  obtain ⟨B, hgood, hfirst | hlast⟩ := exists_good_with_endpoint x k
  · refine ⟨B, ?_, hgood⟩
    rw [Chain.mem_vertices_iff]
    exact ⟨0, by simpa only [Chain.first] using hfirst⟩
  · refine ⟨B, ?_, hgood⟩
    rw [Chain.mem_vertices_iff]
    exact ⟨Fin.last B.toChain.steps, by simpa only [Chain.last] using hlast⟩

end BasicChain
end Ternary
end WeightedChains
