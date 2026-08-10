import WeightedChains.WeightedStrategy

/-!
# Equality cases for weighted covers

This file formalises the abstract part of the uniqueness argument in Lemma 3.2.
If a family attains the weighted-cover bound, then it meets every block of
positive weight exactly once.  The final lemmas record the two local
propagation steps used in the paper's induction towards the outside layers.
-/

set_option autoImplicit false

open scoped BigOperators

namespace WeightedChains
namespace WeightedCover

variable {α ι : Type*} [Fintype ι] [DecidableEq α]

/-- Equality in the weighted incidence bound forces every positive-weight
block to be used.  This is the numerical heart of the uniqueness argument. -/
theorem inter_card_eq_one_of_positive_of_weighted_sum_eq
    (weight : ι → ℝ) (B : Finset α) (blocks : ι → Finset α)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hatMostOne : ∀ i, (B ∩ blocks i).card ≤ 1)
    (hsum : ∑ i, weight i * ((B ∩ blocks i).card : ℝ) = ∑ i, weight i)
    {i : ι} (hpositive : 0 < weight i) :
    (B ∩ blocks i).card = 1 := by
  have hterm_le : ∀ j, weight j * ((B ∩ blocks j).card : ℝ) ≤ weight j := by
    intro j
    have hcard : ((B ∩ blocks j).card : ℝ) ≤ 1 := by
      exact_mod_cast hatMostOne j
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hcard (hnonnegative j)
  by_contra hne
  have hle := hatMostOne i
  have hzero : (B ∩ blocks i).card = 0 := by omega
  have hstrict : weight i * ((B ∩ blocks i).card : ℝ) < weight i := by
    rw [hzero]
    simpa using hpositive
  have hsum_lt :
      (∑ j, weight j * ((B ∩ blocks j).card : ℝ)) < ∑ j, weight j := by
    exact Finset.sum_lt_sum (fun j _hj ↦ hterm_le j)
      ⟨i, Finset.mem_univ i, hstrict⟩
  exact (ne_of_lt hsum_lt) hsum

/-- An extremal family meets every positive-weight block exactly once. -/
theorem inter_card_eq_one_of_positive_of_card_eq
    (blocks : ι → Finset α) (weight : ι → ℝ) (A B : Finset α)
    (hcover : ∀ x, inducedWeight blocks weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hA : ∀ i, (A ∩ blocks i).card = 1)
    (hB : ∀ i, (B ∩ blocks i).card ≤ 1)
    (hcard : B.card = A.card) {i : ι} (hpositive : 0 < weight i) :
    (B ∩ blocks i).card = 1 := by
  apply inter_card_eq_one_of_positive_of_weighted_sum_eq
    weight B blocks hnonnegative hB
  calc
    ∑ j, weight j * ((B ∩ blocks j).card : ℝ) =
        ∑ x ∈ B, inducedWeight blocks weight x :=
      (sum_inducedWeight blocks weight B).symm
    _ = (B.card : ℝ) := by simp [hcover]
    _ = (A.card : ℝ) := by rw [hcard]
    _ = ∑ j, weight j :=
      (sum_weight_eq_card blocks weight A hcover hA).symm
  exact hpositive

/-- If every block has positive weight, equality forces the extremal family to
meet every block exactly once. -/
theorem inter_card_eq_one_of_card_eq
    (blocks : ι → Finset α) (weight : ι → ℝ) (A B : Finset α)
    (hcover : ∀ x, inducedWeight blocks weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hpositive : ∀ i, 0 < weight i)
    (hA : ∀ i, (A ∩ blocks i).card = 1)
    (hB : ∀ i, (B ∩ blocks i).card ≤ 1)
    (hcard : B.card = A.card) (i : ι) :
    (B ∩ blocks i).card = 1 :=
  inter_card_eq_one_of_positive_of_card_eq blocks weight A B hcover hnonnegative
    hA hB hcard (hpositive i)

/-- In a block met exactly once, membership of one point excludes every other
point of the block.  This is the first local propagation step in Lemma 3.2. -/
theorem not_mem_of_mem_of_inter_card_eq_one {B C : Finset α} {x y : α}
    (hone : (B ∩ C).card = 1) (hxB : x ∈ B) (hxC : x ∈ C)
    (hyC : y ∈ C) (hxy : y ≠ x) :
    y ∉ B := by
  intro hyB
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
  have hx : x ∈ B ∩ C := Finset.mem_inter.mpr ⟨hxB, hxC⟩
  have hy : y ∈ B ∩ C := Finset.mem_inter.mpr ⟨hyB, hyC⟩
  rw [hz] at hx hy
  simp only [Finset.mem_singleton] at hx hy
  exact hxy (hy.trans hx.symm)

/-- If a block is met exactly once and every point other than `x` is absent,
then `x` is present.  This is the second local propagation step in Lemma 3.2. -/
theorem mem_of_other_points_not_mem_of_inter_card_eq_one
    {B C : Finset α} {x : α} (hone : (B ∩ C).card = 1)
    (hother : ∀ y ∈ C, y ≠ x → y ∉ B) :
    x ∈ B := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
  have hzmem : z ∈ B ∩ C := by simp [hz]
  have hzB : z ∈ B := (Finset.mem_inter.mp hzmem).1
  have hzC : z ∈ C := (Finset.mem_inter.mp hzmem).2
  by_contra hxB
  have hzx : z ≠ x := by
    intro h
    exact hxB (h ▸ hzB)
  exact hother z hzC hzx hzB

/-- A convenient equivalence combining the two local propagation steps. -/
theorem mem_iff_other_points_not_mem_of_inter_card_eq_one
    {B C : Finset α} {x : α} (hone : (B ∩ C).card = 1) (hxC : x ∈ C) :
    x ∈ B ↔ ∀ y ∈ C, y ≠ x → y ∉ B := by
  constructor
  · intro hxB y hyC hyx
    exact not_mem_of_mem_of_inter_card_eq_one hone hxB hxC hyC hyx
  · exact mem_of_other_points_not_mem_of_inter_card_eq_one hone

/-- A positive singleton block forces its point into any extremal family. -/
theorem mem_of_positive_singleton_of_card_eq
    (blocks : ι → Finset α) (weight : ι → ℝ) (A B : Finset α)
    (hcover : ∀ x, inducedWeight blocks weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hA : ∀ i, (A ∩ blocks i).card = 1)
    (hB : ∀ i, (B ∩ blocks i).card ≤ 1)
    (hcard : B.card = A.card) {i : ι} {x : α}
    (hpositive : 0 < weight i) (hblock : blocks i = {x}) :
    x ∈ B := by
  have hone := inter_card_eq_one_of_positive_of_card_eq blocks weight A B hcover
    hnonnegative hA hB hcard hpositive
  by_contra hx
  simp [hblock, hx] at hone

end WeightedCover

namespace Chain

variable {n d k : ℕ} {ι : Type*} [Fintype ι]

/-- Equality in the weighted-chain bound forces an extremal separated family
to meet every positive-weight good chain exactly once. -/
theorem kSeparated_inter_vertices_card_eq_one_of_positive
    (chains : ι → Chain n d) (weight : ι → ℝ)
    (reference candidate : Finset (Cube n d))
    (hgood : ∀ i, (chains i).Good k)
    (hcover : ∀ x,
      WeightedCover.inducedWeight (fun i ↦ (chains i).vertices) weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hreference : ∀ i, (reference ∩ (chains i).vertices).card = 1)
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k)
    (hcard : candidate.card = reference.card) {i : ι} (hpositive : 0 < weight i) :
    (candidate ∩ (chains i).vertices).card = 1 := by
  apply WeightedCover.inter_card_eq_one_of_positive_of_card_eq
    (fun j ↦ (chains j).vertices) weight reference candidate hcover hnonnegative
    hreference _ hcard hpositive
  intro j
  exact (chains j).card_inter_vertices_le_one candidate k hcandidate (hgood j).2.1

end Chain
end WeightedChains
