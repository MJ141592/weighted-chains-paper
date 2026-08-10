import WeightedChains.DOneMain
import WeightedChains.DOneMiddleChainWitnesses

/-!
# The middle layer in the Boolean equality case

This file proves the first, central step of the equality analysis for `d = 1`.
When the dimension is even, every extremal family contains the unique middle
layer.  When the dimension is odd, its restriction to the two middle layers is
one of those layers in its entirety.

The bridge from weighted equality to layer structure is completely explicit:
we construct represented zero-step chains at middle vertices and represented
one-step chains along every comparable edge between the two middle layers.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n : ℕ}

/-- In even dimension, equality in the Boolean bound forces the whole middle
layer into the candidate family. -/
theorem middleLayer_subset_candidate_of_even
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 1 k).card)
    (heven : Even n) :
    Cube.layer n 1 (n / 2) ⊆ (candidate : Set (Cube n 1)) := by
  intro x hx
  have hxrank : Cube.rank x = n / 2 := hx
  let C := singletonChain x
  have hgood : C.IsGood k := by
    exact singletonChain_isGood_of_even x k heven hxrank
  have hinter := inter_goodChain_card_eq_one_of_card_eq
    k n hk hkn candidate hcandidate hcard C hgood
  have hvertices : C.toChain.vertices = {x} := by simp [C]
  rw [hvertices] at hinter
  change x ∈ candidate
  by_contra hxnot
  have hempty : candidate ∩ {x} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzCandidate : z ∈ candidate := (Finset.mem_inter.mp hz).1
    have hzx : z = x := Finset.mem_singleton.mp (Finset.mem_inter.mp hz).2
    exact hxnot (hzx ▸ hzCandidate)
  rw [hempty] at hinter
  simp at hinter

/-- In odd dimension, equality in the Boolean bound forces the candidate's
restriction to the two middle layers to be one complete middle layer. -/
theorem inter_middleLayers_eq_lower_or_upper_of_odd
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 1 k).card)
    (hodd : Odd n) :
    (candidate : Set (Cube n 1)) ∩
        DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) =
          Cube.layer n 1 (n / 2) ∨
      (candidate : Set (Cube n 1)) ∩
        DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) =
          Cube.layer n 1 (n / 2 + 1) := by
  apply DOneMiddleUniqueness.inter_adjacentLayers_eq_lower_or_upper
  · exact (Nat.div_le_self n 2).trans (by omega)
  · intro x y hx hy hxy
    obtain ⟨C, hsteps, hfirst, hlast⟩ :=
      exists_oneStepChain_of_adjacent hx hy hxy
    have hgood : C.IsGood k := by
      exact oneStepChain_isGood_of_odd C k (by omega) hodd hsteps (by
        rw [hfirst, hx])
    have hinter := inter_goodChain_card_eq_one_of_card_eq
      k n hk hkn candidate hcandidate hcard C hgood
    have hvertices : C.toChain.vertices = {x, y} := by
      rw [vertices_eq_pair_of_steps_eq_one C hsteps, hfirst, hlast]
    rw [hvertices] at hinter
    apply mem_iff_not_mem_of_inter_pair_card_eq_one candidate
    · intro hEq
      have hrankEq := congrArg Cube.rank hEq
      rw [hx, hy] at hrankEq
      omega
    · exact hinter

end BooleanChain
end DOne
end WeightedChains
