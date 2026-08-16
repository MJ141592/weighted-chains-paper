import WeightedChains.DOne.Weights
import WeightedChains.MainBound

/-!
# The weighted-chain theorem for the Boolean cube

The concrete Section 4 weights now discharge every hypothesis of the abstract
weighted strategy.  Thus the paper's extremal cardinality bound for `d = 1`
is no longer conditional on the existence of weights.
-/

namespace WeightedChains
namespace DOne
namespace BooleanChain

/-- The main cardinality bound for the Boolean cube: every `k`-separated
family is no larger than the lower distinguished residue family. -/
theorem kSeparated_card_le_lowerResidueFinset
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n 1 k).card := by
  apply Chain.kSeparated_card_le_lowerResidueFinset
    (fun i : GoodIndex n k ↦ indexedChain i) (indexedWeight n k) candidate
  · exact indexedChain_good
  · intro x
    exact indexedInducedWeight_eq_one k n hk.le hkn x
  · exact indexedWeight_nonneg k n hk hkn
  · exact hcandidate

/-- The equivalent upper-reference version of the Boolean bound. -/
theorem kSeparated_card_le_upperResidueFinset
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k) :
    candidate.card ≤ (Cube.upperResidueFinset n 1 k).card := by
  rw [← Cube.card_lowerResidueFinset_eq_card_upperResidueFinset]
  exact kSeparated_card_le_lowerResidueFinset k n hk hkn candidate hcandidate

/-- Equality in the Boolean bound forces an extremal family to meet every
positive weighted chain from the concrete family exactly once. -/
theorem inter_indexedChain_card_eq_one_of_card_eq
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 1 k).card)
    (i : GoodIndex n k) :
    (candidate ∩ (indexedChain i).vertices).card = 1 := by
  apply Chain.kSeparated_inter_vertices_card_eq_one_of_card_eq_lower
    (fun j : GoodIndex n k ↦ indexedChain j) (indexedWeight n k) candidate
  · exact indexedChain_good
  · intro x
    exact indexedInducedWeight_eq_one k n hk.le hkn x
  · exact indexedWeight_nonneg k n hk hkn
  · exact hcandidate
  · exact hcard
  · exact indexedWeight_pos k n hk hkn i

/-- Descriptor-level form of the equality case: every represented good
Boolean chain is met exactly once. -/
theorem inter_goodChain_card_eq_one_of_card_eq
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 1 k).card)
    (C : BooleanChain n) (hgood : C.IsGood k) :
    (candidate ∩ C.toChain.vertices).card = 1 := by
  exact inter_indexedChain_card_eq_one_of_card_eq k n hk hkn candidate
    hcandidate hcard ⟨C, hgood⟩

end BooleanChain
end DOne
end WeightedChains
