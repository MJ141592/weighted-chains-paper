import WeightedChains.DTwo.Metachains
import WeightedChains.WeightedStrategy

/-!
# From ternary type totals to vertex weights

Section 5 assigns weights type by type.  Coordinate symmetry then turns the
required total weight `\binom{n}{a,c}` on a type into induced weight one at
each vertex of that type.  This file supplies that argument independently of
the later recursive construction of the starting-type totals.
-/

open scoped BigOperators

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

/-- A coordinate-invariant weighting of basic-chain descriptors induces a
coordinate-invariant weighting of ternary vertices. -/
theorem inducedWeight_reindex (weight : BasicChain n → ℝ)
    (hweight : ∀ B e, weight (B.reindex e) = weight B)
    (e : Equiv.Perm (Fin n)) (x : Cube n 2) :
    WeightedCover.inducedWeight (fun B : BasicChain n ↦ B.toChain.vertices)
        weight (permuteVertex e x) =
      WeightedCover.inducedWeight (fun B : BasicChain n ↦ B.toChain.vertices)
        weight x := by
  let summand := fun y : Cube n 2 ↦ fun B : BasicChain n ↦
    if y ∈ B.toChain.vertices then weight B else 0
  calc
    WeightedCover.inducedWeight (fun B : BasicChain n ↦ B.toChain.vertices)
        weight (permuteVertex e x) = ∑ B, summand (permuteVertex e x) B := rfl
    _ = ∑ B, summand (permuteVertex e x) (reindexEquiv e B) :=
      (Equiv.sum_comp (reindexEquiv e) (summand (permuteVertex e x))).symm
    _ = ∑ B, summand x B := by
      apply Fintype.sum_congr
      intro B
      change (if permuteVertex e x ∈ (B.reindex e).toChain.vertices then
          weight (B.reindex e) else 0) =
        if x ∈ B.toChain.vertices then weight B else 0
      have hmem := B.mem_vertices_reindex_iff e x
      by_cases hxmem : x ∈ B.toChain.vertices
      · have hpermuted := hmem.mpr hxmem
        simp [hxmem, hpermuted, hweight]
      · have hpermuted : permuteVertex e x ∉ (B.reindex e).toChain.vertices :=
          fun h ↦ hxmem (hmem.mp h)
        simp [hxmem, hpermuted]
    _ = WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices) weight x := rfl

/-- The induced weight depends only on the ternary type whenever chain
weights are invariant under coordinate permutations. -/
theorem inducedWeight_eq_of_same_type (weight : BasicChain n → ℝ)
    (hweight : ∀ B e, weight (B.reindex e) = weight B)
    {x y : Cube n 2}
    (hzero : zeroCount x = zeroCount y) (htwo : twoCount x = twoCount y) :
    WeightedCover.inducedWeight (fun B : BasicChain n ↦ B.toChain.vertices)
        weight x =
      WeightedCover.inducedWeight (fun B : BasicChain n ↦ B.toChain.vertices)
        weight y := by
  obtain ⟨e, he⟩ := exists_coordinatePermutation_of_same_type hzero htwo
  have hexy : permuteVertex e x = y := by
    funext q
    obtain ⟨i, rfl⟩ := e.surjective q
    rw [permuteVertex_apply]
    exact (he i).symm
  rw [← hexy]
  exact (inducedWeight_reindex weight hweight e x).symm

/-- Sum of induced weights over all vertices of type `(a,n-a-c,c)`. -/
def totalInducedWeightOnType (n a c : ℕ) (weight : BasicChain n → ℝ) : ℝ :=
  ∑ x ∈ typeFiber n a c,
    WeightedCover.inducedWeight (fun B : BasicChain n ↦ B.toChain.vertices) weight x

/-- For a coordinate-invariant chain weighting, the total on a type is its
cardinality times the common induced weight at any chosen vertex of that
type. -/
theorem totalInducedWeightOnType_eq_card_mul
    (weight : BasicChain n → ℝ)
    (hweight : ∀ B e, weight (B.reindex e) = weight B)
    (a c : ℕ) {x : Cube n 2}
    (hxzero : zeroCount x = a) (hxtwo : twoCount x = c) :
    totalInducedWeightOnType n a c weight =
      ((typeFiber n a c).card : ℝ) *
        WeightedCover.inducedWeight
          (fun B : BasicChain n ↦ B.toChain.vertices) weight x := by
  unfold totalInducedWeightOnType
  calc
    ∑ y ∈ typeFiber n a c,
        WeightedCover.inducedWeight
          (fun B : BasicChain n ↦ B.toChain.vertices) weight y =
      ∑ _y ∈ typeFiber n a c,
        WeightedCover.inducedWeight
          (fun B : BasicChain n ↦ B.toChain.vertices) weight x := by
        apply Finset.sum_congr rfl
        intro y hy
        obtain ⟨hyzero, hytwo⟩ := mem_typeFiber.mp hy
        exact inducedWeight_eq_of_same_type weight hweight
          (hyzero.trans hxzero.symm) (hytwo.trans hxtwo.symm)
    _ = ((typeFiber n a c).card : ℝ) *
        WeightedCover.inducedWeight
          (fun B : BasicChain n ↦ B.toChain.vertices) weight x := by simp

/-- If the assigned chain weights total the trinomial coefficient on a type,
then every vertex of that type has induced weight one. -/
theorem inducedWeight_eq_one_of_total_eq_trinomial
    (weight : BasicChain n → ℝ)
    (hweight : ∀ B e, weight (B.reindex e) = weight B)
    (a c : ℕ) {x : Cube n 2}
    (hxzero : zeroCount x = a) (hxtwo : twoCount x = c)
    (htotal : totalInducedWeightOnType n a c weight = (trinomial n a c : ℝ)) :
    WeightedCover.inducedWeight (fun B : BasicChain n ↦ B.toChain.vertices)
      weight x = 1 := by
  have hxmem : x ∈ typeFiber n a c := mem_typeFiber.mpr ⟨hxzero, hxtwo⟩
  have hcardpos : (0 : ℝ) < (typeFiber n a c).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, hxmem⟩
  rw [totalInducedWeightOnType_eq_card_mul weight hweight a c hxzero hxtwo,
    ← card_typeFiber] at htotal
  nlinarith

end BasicChain
end Ternary
end WeightedChains
