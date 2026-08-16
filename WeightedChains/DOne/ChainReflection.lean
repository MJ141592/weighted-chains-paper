import WeightedChains.DOne.Chains
import WeightedChains.ResidueSymmetry

/-!
# Reflection of represented Boolean chains

Coordinatewise Boolean complementation reverses the order on the Boolean
cube.  Reversing a represented chain at the same time gives another
represented chain: its initial support is the complement of the old final
support, and its additions are the old additions in reverse order.

This file records that operation as an involutive equivalence and proves the
incidence and goodness covariance needed to transfer the Section 4 weighted
cover calculation from the lower half of the cube to the upper half.
-/

noncomputable section

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n : ℕ}

/-- The coordinates changed by a represented Boolean chain. -/
def changed (C : BooleanChain n) : Finset (Fin n) :=
  Finset.univ.map C.addition

/-- The final support of a represented Boolean chain. -/
def finalSupport (C : BooleanChain n) : Finset (Fin n) :=
  C.start ∪ C.changed

theorem mem_finalSupport_iff (C : BooleanChain n) (x : Fin n) :
    x ∈ C.finalSupport ↔ x ∈ C.start ∨ ∃ j : Fin C.steps, C.addition j = x := by
  simp [finalSupport, changed]

@[simp]
theorem finalSupport_eq_support_last (C : BooleanChain n) :
    C.finalSupport = C.support (Fin.last C.steps) := by
  simp [finalSupport, changed, support, added_last]

/-- The old additions, read from last to first. -/
def reverseAddition (C : BooleanChain n) : Fin C.steps ↪ Fin n where
  toFun i := C.addition i.rev
  inj' := C.addition.injective.comp Fin.rev_injective

@[simp]
theorem reverseAddition_apply (C : BooleanChain n) (i : Fin C.steps) :
    C.reverseAddition i = C.addition i.rev := rfl

@[simp]
theorem univ_map_reverseAddition (C : BooleanChain n) :
    Finset.univ.map C.reverseAddition = C.changed := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, changed]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.rev, by simp⟩

/-- Complement every vertex of a represented Boolean chain and reverse its
order. -/
def reflect (C : BooleanChain n) : BooleanChain n where
  steps := C.steps
  start := Finset.univ \ C.finalSupport
  addition := C.reverseAddition
  fresh := by
    rw [univ_map_reverseAddition]
    rw [Finset.disjoint_left]
    intro x hx hchanged
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right C.start hchanged)

@[simp]
theorem reflect_steps (C : BooleanChain n) : C.reflect.steps = C.steps := rfl

@[simp]
theorem reflect_start (C : BooleanChain n) :
    C.reflect.start = Finset.univ \ C.finalSupport := rfl

@[simp]
theorem reflect_addition (C : BooleanChain n) (i : Fin C.steps) :
    C.reflect.addition i = C.addition i.rev := rfl

/-- Membership in the coordinates added before time `i`, expressed using the
original addition index. -/
theorem mem_added_iff (C : BooleanChain n) (i : Fin (C.steps + 1)) (x : Fin n) :
    x ∈ C.added i ↔
      ∃ j : Fin C.steps, (j : ℕ) < i ∧ C.addition j = x := by
  constructor
  · intro hx
    obtain ⟨j, _hj, hjx⟩ := Finset.mem_map.mp hx
    refine ⟨C.prefixEmbedding i j, j.isLt, hjx⟩
  · rintro ⟨j, hj, rfl⟩
    rw [added]
    apply Finset.mem_map.mpr
    let q : Fin i := ⟨j, hj⟩
    exact ⟨q, Finset.mem_univ q, rfl⟩

theorem mem_reflect_added_iff (C : BooleanChain n)
    (i : Fin (C.steps + 1)) (x : Fin n) :
    x ∈ C.reflect.added i ↔
      ∃ j : Fin C.steps, (j : ℕ) < i ∧ C.addition j.rev = x := by
  constructor
  · intro hx
    obtain ⟨j, hj, hjx⟩ := (mem_added_iff C.reflect i x).mp hx
    refine ⟨j, hj, ?_⟩
    change C.addition j.rev = x at hjx
    exact hjx
  · rintro ⟨j, hj, hjx⟩
    apply (mem_added_iff C.reflect i x).mpr
    refine ⟨j, hj, ?_⟩
    change C.addition j.rev = x
    exact hjx

/-- The reflected support at time `i` is the complement of the old support
at the reverse time. -/
theorem support_reflect (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    C.reflect.support i = Finset.univ \ C.support i.rev := by
  ext x
  simp only [support, reflect_start, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  rw [mem_reflect_added_iff, mem_added_iff]
  constructor
  · rintro (houtside | ⟨j, hj, hjx⟩)
    · intro hxold
      apply houtside
      rw [mem_finalSupport_iff]
      rcases hxold with hxstart | ⟨q, _hq, hqx⟩
      · exact Or.inl hxstart
      · exact Or.inr ⟨q, hqx⟩
    · rintro (hxstart | ⟨q, hq, hqx⟩)
      · exact (Finset.disjoint_left.mp C.fresh hxstart)
          (Finset.mem_map.mpr
            ⟨j.rev, Finset.mem_univ _, by simpa [changed] using hjx⟩)
      · have hinjective : j.rev = q := C.addition.injective (hjx.trans hqx.symm)
        have hqlt : (q : ℕ) < i.rev := hq
        rw [← hinjective] at hqlt
        simp only [Fin.val_rev] at hqlt
        omega
  · intro hnotold
    by_cases hxchanged : x ∈ C.changed
    · right
      obtain ⟨q, _hq, hqx⟩ := Finset.mem_map.mp hxchanged
      let j : Fin C.steps := q.rev
      refine ⟨j, ?_, ?_⟩
      · have hnotprefix : ¬((q : ℕ) < i.rev) := by
          intro hqprefix
          apply hnotold
          exact Or.inr ⟨q, hqprefix, hqx⟩
        change (q.rev : ℕ) < i
        simp only [Fin.val_rev] at hnotprefix ⊢
        omega
      · simpa [j] using hqx
    · left
      intro hfinal
      rw [mem_finalSupport_iff] at hfinal
      rcases hfinal with hxstart | ⟨q, hqx⟩
      · exact hnotold (Or.inl hxstart)
      · exact hxchanged (Finset.mem_map.mpr ⟨q, Finset.mem_univ _, hqx⟩)

/-- Pointwise form: reflection complements the old vertex at reverse time. -/
theorem vertex_reflect (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    C.reflect.vertex i = Cube.reflect (C.vertex i.rev) := by
  funext x
  by_cases hx : x ∈ C.support i.rev
  · have hxnot : x ∉ C.reflect.support i := by
      rw [support_reflect]
      simp [hx]
    simp [vertex, cubeOfFinset, Cube.reflect, hx, hxnot]
  · have hxnew : x ∈ C.reflect.support i := by
      rw [support_reflect]
      simp [hx]
    simp [vertex, cubeOfFinset, Cube.reflect, hx, hxnew]

@[simp]
theorem card_changed (C : BooleanChain n) : C.changed.card = C.steps := by
  simp [changed]

@[simp]
theorem card_finalSupport (C : BooleanChain n) :
    C.finalSupport.card = C.start.card + C.steps := by
  unfold finalSupport changed
  rw [Finset.card_union_of_disjoint C.fresh]
  simp

/-- The new lower endpoint is the complement of the old upper endpoint. -/
@[simp]
theorem card_reflect_start (C : BooleanChain n) :
    C.reflect.start.card = n - (C.start.card + C.steps) := by
  rw [reflect_start, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

theorem endpointRank_le' (C : BooleanChain n) : C.start.card + C.steps ≤ n := by
  rw [← C.card_finalSupport]
  simpa using Finset.card_le_univ C.finalSupport

/-- The new upper endpoint is the complement of the old lower endpoint. -/
@[simp]
theorem reflect_endpointRank (C : BooleanChain n) :
    C.reflect.start.card + C.reflect.steps = n - C.start.card := by
  rw [card_reflect_start, reflect_steps]
  have := C.endpointRank_le'
  omega

@[simp]
theorem finalSupport_reflect (C : BooleanChain n) :
    C.reflect.finalSupport = Finset.univ \ C.start := by
  rw [finalSupport_eq_support_last]
  change C.reflect.support (Fin.last C.steps) = Finset.univ \ C.start
  rw [support_reflect]
  simp

/-- Complementing and reversing twice recovers the original chain data. -/
@[simp]
theorem reflect_reflect (C : BooleanChain n) : C.reflect.reflect = C := by
  apply BooleanChain.ext
  · rfl
  · change Finset.univ \ C.reflect.finalSupport = C.start
    rw [finalSupport_reflect]
    simp
  · apply heq_of_eq
    apply Function.Embedding.ext
    intro i
    change C.addition i.rev.rev = C.addition i
    apply congrArg C.addition
    exact Fin.rev_rev i

/-- Complement-and-reverse as an involutive equivalence on represented
Boolean chains. -/
def reflectEquiv (n : ℕ) : BooleanChain n ≃ BooleanChain n where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect

@[simp]
theorem reflectEquiv_apply (C : BooleanChain n) : reflectEquiv n C = C.reflect := rfl

/-- Reflection complements rank at reverse time. -/
theorem rank_vertex_reflect (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    Cube.rank (C.reflect.vertex i) = n - Cube.rank (C.vertex i.rev) := by
  rw [vertex_reflect, Cube.rank_reflect]
  simp

/-- Incidence is transported exactly by Boolean complementation. -/
theorem reflect_mem_vertices_iff (C : BooleanChain n) (x : Cube n 1) :
    Cube.reflect x ∈ C.reflect.toChain.vertices ↔ x ∈ C.toChain.vertices := by
  rw [Chain.mem_vertices_iff, Chain.mem_vertices_iff]
  constructor
  · rintro ⟨i, hi⟩
    let j : Fin (C.steps + 1) := ⟨i, i.isLt⟩
    have hi' : C.reflect.vertex j = Cube.reflect x := hi
    refine ⟨j.rev, ?_⟩
    apply (Cube.reflectEquiv n 1).injective
    exact (C.vertex_reflect j).symm.trans hi'
  · rintro ⟨i, hi⟩
    let j : Fin (C.steps + 1) := ⟨i, i.isLt⟩
    have hi' : C.vertex j = x := hi
    refine ⟨j.rev, ?_⟩
    change C.reflect.vertex j.rev = Cube.reflect x
    rw [C.vertex_reflect j.rev, Fin.rev_rev, hi']

theorem mem_reflect_vertices_iff (C : BooleanChain n) (x : Cube n 1) :
    x ∈ C.reflect.toChain.vertices ↔ Cube.reflect x ∈ C.toChain.vertices := by
  simpa using C.reflect_mem_vertices_iff (Cube.reflect x)

/-- The represented-chain finset is carried to the reflected represented
chain finset by the cube reflection equivalence. -/
theorem image_vertices_reflect (C : BooleanChain n) :
    C.toChain.vertices.image Cube.reflect = C.reflect.toChain.vertices := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (C.reflect_mem_vertices_iff y).mpr hy
  · intro hx
    refine ⟨Cube.reflect x, (C.mem_reflect_vertices_iff x).mp hx, ?_⟩
    simp

/-- Complement-and-reverse preserves the paper's goodness condition. -/
theorem good_reflect_iff (C : BooleanChain n) (k : ℕ) :
    C.reflect.toChain.Good k ↔ C.toChain.Good k := by
  rw [good_toChain_iff, good_toChain_iff]
  simp only [reflect_steps, card_reflect_start]
  have hend := C.endpointRank_le'
  constructor
  · rintro ⟨hwidth, hsym | hfull⟩
    · exact ⟨hwidth, Or.inl (by omega)⟩
    · exact ⟨hwidth, Or.inr hfull⟩
  · rintro ⟨hwidth, hsym | hfull⟩
    · exact ⟨hwidth, Or.inl (by omega)⟩
    · exact ⟨hwidth, Or.inr hfull⟩

@[simp]
theorem width_reflect (C : BooleanChain n) :
    C.reflect.toChain.width = C.toChain.width := by
  simp

@[simp]
theorem length_reflect (C : BooleanChain n) :
    C.reflect.toChain.length = C.toChain.length := by
  simp

/-- Doubling a rank and measuring from the middle is unchanged when the rank
is complemented in `n`. -/
theorem dist_two_complement {a n : ℕ} (ha : a ≤ n) :
    (2 * (n - a)).dist n = (2 * a).dist n := by
  by_cases hlow : 2 * a ≤ n
  · have hhigh : n ≤ 2 * (n - a) := by omega
    rw [Nat.dist_eq_sub_of_le_right hhigh, Nat.dist_eq_sub_of_le hlow]
    omega
  · have hhigh : n ≤ 2 * a := by omega
    have hlow' : 2 * (n - a) ≤ n := by omega
    rw [Nat.dist_eq_sub_of_le hlow', Nat.dist_eq_sub_of_le_right hhigh]
    omega

/-- A paper-oriented start layer is complemented under chain reflection. -/
theorem startsAtLayer_reflect_iff (C : BooleanChain n) (a : ℕ) (ha : a ≤ n) :
    C.reflect.StartsAtLayer (n - a) ↔ C.StartsAtLayer a := by
  have hfirst : C.start.card ≤ n := by
    simpa using Finset.card_le_univ C.start
  have hlast := C.endpointRank_le'
  have hendpoint : n - (C.start.card + C.steps) + C.steps = n - C.start.card := by
    omega
  unfold StartsAtLayer
  simp only [reflect_steps, card_reflect_start]
  rw [hendpoint, dist_two_complement hfirst, dist_two_complement hlast]
  constructor <;> rintro (h | h)
  · right
    exact ⟨h.1, by omega⟩
  · left
    exact ⟨h.1, by omega⟩
  · right
    exact ⟨h.1, by omega⟩
  · left
    exact ⟨h.1, by omega⟩

/-- A rank-`a` incidence is carried to a rank-`n-a` incidence. -/
theorem reflect_rank_incidence_iff (C : BooleanChain n) (x : Cube n 1)
    (a : ℕ) (hx : Cube.rank x = a) :
    (Cube.reflect x ∈ C.reflect.toChain.vertices ∧
        Cube.rank (Cube.reflect x) = n - a) ↔
      x ∈ C.toChain.vertices := by
  rw [C.reflect_mem_vertices_iff]
  simp [Cube.rank_reflect, hx]

/-- Any reflection-invariant weighting of the represented chains induces a
reflection-invariant weighting of the Boolean cube.  This packages the
change-of-variables argument needed by the concrete Section 4 weights. -/
theorem inducedWeight_reflect (weight : BooleanChain n → ℝ)
    (hweight : ∀ C, weight C.reflect = weight C) (x : Cube n 1) :
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        weight (Cube.reflect x) =
      WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        weight x := by
  let summand := fun y : Cube n 1 ↦ fun C : BooleanChain n ↦
    if y ∈ C.toChain.vertices then weight C else 0
  calc
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        weight (Cube.reflect x) = ∑ C, summand (Cube.reflect x) C := rfl
    _ = ∑ C, summand (Cube.reflect x) (reflectEquiv n C) :=
      (Equiv.sum_comp (reflectEquiv n) (summand (Cube.reflect x))).symm
    _ = ∑ C, summand x C := by
      apply Fintype.sum_congr
      intro C
      change (if Cube.reflect x ∈ C.reflect.toChain.vertices then
          weight C.reflect else 0) =
        if x ∈ C.toChain.vertices then weight C else 0
      have hreflect := C.reflect_mem_vertices_iff x
      by_cases hxmem : x ∈ C.toChain.vertices
      · have hreflectmem := hreflect.mpr hxmem
        simp [hxmem, hreflectmem, hweight]
      · have hreflectmem : Cube.reflect x ∉ C.reflect.toChain.vertices :=
          fun h ↦ hxmem (hreflect.mp h)
        simp [hxmem, hreflectmem]
    _ = WeightedCover.inducedWeight
        (fun C : BooleanChain n ↦ C.toChain.vertices) weight x := rfl

end BooleanChain
end DOne
end WeightedChains
