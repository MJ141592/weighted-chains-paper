import WeightedChains.DTwoWeightReflection
import WeightedChains.MainBound

/-!
# The weighted-chain bound for the ternary cube

The concrete Section 5 weighting now discharges every hypothesis of the
abstract weighted-cover argument.  The unique zero-weight good descriptor is
the all-ones singleton; all other good basic chains have positive weight.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

/-- The finite index type containing exactly the good ternary basic-chain
descriptors. -/
abbrev GoodIndex (n k : ℕ) := {B : BasicChain n // B.IsGood k}

/-- The represented chain carried by a good descriptor index. -/
def indexedChain {n k : ℕ} (i : GoodIndex n k) : Chain n 2 := i.1.toChain

/-- The concrete distributed weight restricted to good descriptors. -/
def indexedWeight (n k : ℕ) (i : GoodIndex n k) : ℝ :=
  distributedChainWeight (startTypeTotal k) k i.1

theorem indexedChain_good {n k : ℕ} (i : GoodIndex n k) :
    (indexedChain i).Good k :=
  (i.1.isGood_iff k).1 i.2

theorem indexedWeight_pos_of_start_ne_middle
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n) (i : GoodIndex n k)
    (hne : i.1.start ≠ middleVertex n) :
    0 < indexedWeight n k i := by
  apply distributedStartTypeWeight_pos i.1 k hk hkn
  · exact (i.1.isGood_iff k).1 i.2
  · exact hne

theorem indexedWeight_nonneg
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n) (i : GoodIndex n k) :
    0 ≤ indexedWeight n k i := by
  by_cases hne : i.1.start ≠ middleVertex n
  · exact (indexedWeight_pos_of_start_ne_middle k n hk hkn i hne).le
  · have hstart : i.1.start = middleVertex n := not_ne_iff.mp hne
    have hn : 0 < n := by omega
    have hcanonical : i.1.canonicalStartType = allOnesType n :=
      (i.1.canonicalStartType_eq_allOnesType_iff).2 hstart
    unfold indexedWeight distributedChainWeight
    rw [if_pos i.2, hcanonical,
      startTypeTotal_allOnesType n k hn hk.le]
    positivity

/-- Removing the zero-weight non-good descriptors from the ambient finite
type does not change induced weights. -/
theorem indexedInducedWeight_eq (n k : ℕ) (x : Cube n 2) :
    WeightedCover.inducedWeight
        (fun i : GoodIndex n k ↦ (indexedChain i).vertices)
        (indexedWeight n k) x =
      WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) x := by
  let goodFinset := (Finset.univ : Finset (BasicChain n)).filter
    fun B ↦ B.IsGood k
  let term := fun B : BasicChain n ↦
    if x ∈ B.toChain.vertices then
      distributedChainWeight (startTypeTotal k) k B else 0
  calc
    WeightedCover.inducedWeight
        (fun i : GoodIndex n k ↦ (indexedChain i).vertices)
        (indexedWeight n k) x =
      ∑ i : GoodIndex n k, term i.1 := rfl
    _ = ∑ B ∈ goodFinset, term B := by
      symm
      apply Finset.sum_subtype (p := fun B : BasicChain n ↦ B.IsGood k)
      intro B
      simp [goodFinset]
    _ = ∑ B : BasicChain n, term B := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro B _hB hnot
      have hbad : ¬B.IsGood k := by
        simpa [goodFinset] using hnot
      simp [term, distributedChainWeight, hbad]
    _ = WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) x := rfl

/-- The actual finite family of good basic chains covers every ternary
vertex with total induced weight one. -/
theorem indexedInducedWeight_eq_one
    (k n : ℕ) (hk : 0 < k) (x : Cube n 2) :
    WeightedCover.inducedWeight
        (fun i : GoodIndex n k ↦ (indexedChain i).vertices)
        (indexedWeight n k) x = 1 := by
  rw [indexedInducedWeight_eq]
  exact inducedWeight_startTypeTotal_eq_one n k hk x

/-- Every `k`-separated ternary family is no larger than the lower
distinguished residue family. -/
theorem kSeparated_card_le_lowerResidueFinset
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 2))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 2)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n 2 k).card := by
  apply Chain.kSeparated_card_le_lowerResidueFinset
    (fun i : GoodIndex n k ↦ indexedChain i) (indexedWeight n k) candidate
  · exact indexedChain_good
  · exact indexedInducedWeight_eq_one k n hk.le
  · exact indexedWeight_nonneg k n hk hkn
  · exact hcandidate

/-- Equivalent upper-reference form of the ternary bound. -/
theorem kSeparated_card_le_upperResidueFinset
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 2))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 2)) k) :
    candidate.card ≤ (Cube.upperResidueFinset n 2 k).card := by
  rw [← Cube.card_lowerResidueFinset_eq_card_upperResidueFinset]
  exact kSeparated_card_le_lowerResidueFinset
    k n hk hkn candidate hcandidate

/-- Equality forces every positive indexed good chain to meet the candidate
exactly once. -/
theorem inter_indexedChain_card_eq_one_of_card_eq
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 2))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 2)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 2 k).card)
    (i : GoodIndex n k) (hne : i.1.start ≠ middleVertex n) :
    (candidate ∩ (indexedChain i).vertices).card = 1 := by
  apply Chain.kSeparated_inter_vertices_card_eq_one_of_card_eq_lower
    (fun j : GoodIndex n k ↦ indexedChain j) (indexedWeight n k) candidate
  · exact indexedChain_good
  · exact indexedInducedWeight_eq_one k n hk.le
  · exact indexedWeight_nonneg k n hk hkn
  · exact hcandidate
  · exact hcard
  · exact indexedWeight_pos_of_start_ne_middle k n hk hkn i hne

/-- Descriptor-level equality case: every good chain avoiding the all-ones
point is met exactly once. -/
theorem inter_goodChain_card_eq_one_of_card_eq
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 2))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 2)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 2 k).card)
    (B : BasicChain n) (hgood : B.toChain.Good k)
    (havoid : middleVertex n ∉ B.toChain.vertices) :
    (candidate ∩ B.toChain.vertices).card = 1 := by
  have hstartNe : B.start ≠ middleVertex n := by
    intro h
    apply havoid
    rw [← h, Chain.mem_vertices_iff]
    exact ⟨0, B.toChain_first⟩
  exact inter_indexedChain_card_eq_one_of_card_eq
    k n hk hkn candidate hcandidate hcard
      ⟨B, (B.isGood_iff k).2 hgood⟩ hstartNe

end BasicChain
end Ternary
end WeightedChains
