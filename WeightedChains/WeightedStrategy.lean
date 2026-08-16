import WeightedChains.Preliminaries

/-!
# The proof strategy: weighted chains

This file formalises the weighted double-counting argument in Section 3.  It is
stated for an arbitrary finite family of blocks, so the bookkeeping theorem is
independent of the later constructions of good chains for `d = 1` and `d = 2`.
-/

open scoped BigOperators

namespace WeightedChains
namespace WeightedCover

variable {α ι : Type*} [Fintype ι] [DecidableEq α]

/-- The weight induced at a point by all blocks containing it. -/
def inducedWeight (blocks : ι → Finset α) (weight : ι → ℝ) (x : α) : ℝ :=
  ∑ i, if x ∈ blocks i then weight i else 0

/-- Exchange the two finite sums in the weighted incidence relation. -/
theorem sum_inducedWeight (blocks : ι → Finset α) (weight : ι → ℝ) (s : Finset α) :
    ∑ x ∈ s, inducedWeight blocks weight x =
      ∑ i, weight i * ((s ∩ blocks i).card : ℝ) := by
  simp only [inducedWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  simp [mul_comm]

omit [DecidableEq α] in
/-- If a real-valued function is constant on a nonempty finite set and its
sum is the cardinality of that set, then its common value is one. This is the
last averaging step in the layer-symmetric chain constructions. -/
theorem eq_one_on_of_constant_of_sum (f : α → ℝ) (s : Finset α)
    (hnonempty : s.Nonempty)
    (hconstant : ∀ x ∈ s, ∀ y ∈ s, f x = f y)
    (hsum : ∑ x ∈ s, f x = s.card) {x : α} (hx : x ∈ s) :
    f x = 1 := by
  have hsumConstant : ∑ y ∈ s, f y = (s.card : ℝ) * f x := by
    calc
      ∑ y ∈ s, f y = ∑ _y ∈ s, f x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hconstant y hy x hx
      _ = (s.card : ℝ) * f x := by simp
  have hcardPositive : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hnonempty
  rw [hsum] at hsumConstant
  nlinarith

/-- If every point has induced weight one and every block meets `s` exactly
once, then the total block weight is the cardinality of `s`. -/
theorem sum_weight_eq_card (blocks : ι → Finset α) (weight : ι → ℝ)
    (s : Finset α) (hcover : ∀ x, inducedWeight blocks weight x = 1)
    (hone : ∀ i, (s ∩ blocks i).card = 1) :
    ∑ i, weight i = (s.card : ℝ) := by
  calc
    ∑ i, weight i = ∑ i, weight i * ((s ∩ blocks i).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hone i]
      norm_num
    _ = ∑ x ∈ s, inducedWeight blocks weight x :=
      (sum_inducedWeight blocks weight s).symm
    _ = (s.card : ℝ) := by simp [hcover]

/-- The non-uniqueness part of Lemma 3.2 (`weights_imply_theorem_lemma`): a
nonnegative fractional cover by blocks which meet `A` exactly once bounds every
family `B` meeting each block at most once. -/
theorem card_le_of_weighted_cover (blocks : ι → Finset α) (weight : ι → ℝ)
    (A B : Finset α) (hcover : ∀ x, inducedWeight blocks weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hA : ∀ i, (A ∩ blocks i).card = 1)
    (hB : ∀ i, (B ∩ blocks i).card ≤ 1) :
    B.card ≤ A.card := by
  have hreal : (B.card : ℝ) ≤ (A.card : ℝ) := by
    calc
      (B.card : ℝ) = ∑ x ∈ B, inducedWeight blocks weight x := by simp [hcover]
      _ = ∑ i, weight i * ((B ∩ blocks i).card : ℝ) :=
        sum_inducedWeight blocks weight B
      _ ≤ ∑ i, weight i := by
        apply Finset.sum_le_sum
        intro i _hi
        have hcard : ((B ∩ blocks i).card : ℝ) ≤ 1 := by exact_mod_cast hB i
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hcard (hnonnegative i)
      _ = (A.card : ℝ) := sum_weight_eq_card blocks weight A hcover hA
  exact_mod_cast hreal

end WeightedCover

namespace Chain

variable {n d k : ℕ} {ι : Type*} [Fintype ι]

/-- The cardinality bound in Lemma 3.2 specialised to a finite weighted family
of good chains. The later `d = 1` and `d = 2` sections are responsible for
constructing data satisfying `hcover`, `hnonnegative`, and `hreference`. -/
theorem kSeparated_card_le_of_weighted_chains (chains : ι → Chain n d)
    (weight : ι → ℝ) (reference candidate : Finset (Cube n d))
    (hgood : ∀ i, (chains i).Good k)
    (hcover : ∀ x, WeightedCover.inducedWeight (fun i ↦ (chains i).vertices) weight x = 1)
    (hnonnegative : ∀ i, 0 ≤ weight i)
    (hreference : ∀ i, (reference ∩ (chains i).vertices).card = 1)
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k) :
    candidate.card ≤ reference.card := by
  apply WeightedCover.card_le_of_weighted_cover
    (fun i ↦ (chains i).vertices) weight reference candidate hcover hnonnegative hreference
  intro i
  exact (chains i).card_inter_vertices_le_one candidate k hcandidate (hgood i).2.1

end Chain
end WeightedChains
