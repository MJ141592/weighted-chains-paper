import WeightedChains.DOne.EqualityMiddle
import WeightedChains.DOne.EqualityPropagation
import WeightedChains.ResidueParity
import WeightedChains.ReflectedFinsets

/-!
# Classification of extremal families in the Boolean cube

This file completes the equality analysis for `d = 1`.  The middle-layer
argument first determines which of the lower and upper residue families an
extremal family agrees with at the centre of the cube.  Equality propagation
then determines the family everywhere.  The upper choice is reduced to the
lower choice by coordinate reflection.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n k : ℕ}

/-- Two consecutive natural numbers are not congruent modulo `k + 1` when
`k` is positive. -/
private theorem not_modEq_succ (hk : 0 < k) (r : ℕ) :
    ¬ r + 1 ≡ r [MOD k + 1] := by
  intro h
  have hdiv : k + 1 ∣ (r + 1) - r :=
    (Nat.modEq_iff_dvd' (Nat.le_succ r)).mp h.symm
  have hle : k + 1 ≤ (r + 1) - r := Nat.le_of_dvd (by omega) hdiv
  omega

/-- On the two middle ranks in odd dimension, membership in the lower
residue family is exactly membership in the lower of the two layers. -/
theorem mem_lowerResidueFinset_iff_rank_eq_lowerMiddle_of_odd
    (hk : 0 < k) (hodd : Odd n) (x : Cube n 1)
    (hx : Cube.rank x = Cube.lowerMiddleRank n 1 ∨
      Cube.rank x = Cube.upperMiddleRank n 1) :
    x ∈ Cube.lowerResidueFinset n 1 k ↔
      Cube.rank x = Cube.lowerMiddleRank n 1 := by
  have hmiddle : Cube.upperMiddleRank n 1 =
      Cube.lowerMiddleRank n 1 + 1 := by
    apply Cube.upperMiddleRank_eq_lowerMiddleRank_add_one_of_odd
    simpa using hodd
  rcases hx with hx | hx
  · constructor
    · intro _h
      exact hx
    · intro _h
      simp only [Cube.lowerResidueFinset, Finset.mem_filter,
        Finset.mem_univ, true_and, one_mul]
      rw [hx]
  · constructor
    · intro h
      have hmod : Cube.rank x ≡ Cube.lowerMiddleRank n 1 [MOD k + 1] := by
        simpa only [Cube.lowerResidueFinset, Finset.mem_filter,
          Finset.mem_univ, true_and, one_mul] using h
      rw [hx, hmiddle] at hmod
      exact False.elim ((not_modEq_succ hk (Cube.lowerMiddleRank n 1)) hmod)
    · intro h
      rw [hx, hmiddle] at h
      omega

/-- On the two middle ranks in odd dimension, membership in the upper
residue family is exactly membership in the upper of the two layers. -/
theorem mem_upperResidueFinset_iff_rank_eq_upperMiddle_of_odd
    (hk : 0 < k) (hodd : Odd n) (x : Cube n 1)
    (hx : Cube.rank x = Cube.lowerMiddleRank n 1 ∨
      Cube.rank x = Cube.upperMiddleRank n 1) :
    x ∈ Cube.upperResidueFinset n 1 k ↔
      Cube.rank x = Cube.upperMiddleRank n 1 := by
  have hmiddle : Cube.upperMiddleRank n 1 =
      Cube.lowerMiddleRank n 1 + 1 := by
    apply Cube.upperMiddleRank_eq_lowerMiddleRank_add_one_of_odd
    simpa using hodd
  rcases hx with hx | hx
  · constructor
    · intro h
      have hmod : Cube.rank x ≡ Cube.upperMiddleRank n 1 [MOD k + 1] := by
        simpa only [Cube.upperResidueFinset, Finset.mem_filter,
          Finset.mem_univ, true_and, one_mul] using h
      rw [hx, hmiddle] at hmod
      exact False.elim ((not_modEq_succ hk (Cube.lowerMiddleRank n 1)) hmod.symm)
    · intro h
      rw [hx, hmiddle] at h
      omega
  · constructor
    · intro _h
      exact hx
    · intro _h
      simp only [Cube.upperResidueFinset, Finset.mem_filter,
        Finset.mem_univ, true_and, one_mul]
      rw [hx]

/-- The upper-family form of equality propagation, obtained from the lower
form by reflecting the candidate family. -/
theorem eq_upperResidueFinset_of_card_eq_of_middle_agreement
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 1 k).card)
    (hmiddle : ∀ x : Cube n 1, Cube.middleDistance x ≤ 1 →
      (x ∈ candidate ↔ x ∈ Cube.upperResidueFinset n 1 k)) :
    candidate = Cube.upperResidueFinset n 1 k := by
  let reflected := Cube.reflectFinset candidate
  have hreflectedSeparated :
      Cube.KSeparated (reflected : Set (Cube n 1)) k := by
    exact Cube.kSeparated_reflectFinset hcandidate
  have hreflectedCard :
      reflected.card = (Cube.lowerResidueFinset n 1 k).card := by
    simpa [reflected] using hcard
  have hreflectedMiddle : ∀ x : Cube n 1, Cube.middleDistance x ≤ 1 →
      (x ∈ reflected ↔ x ∈ Cube.lowerResidueFinset n 1 k) := by
    intro x hx
    rw [show x ∈ reflected ↔ Cube.reflect x ∈ candidate by
      simp [reflected]]
    have hxReflect : Cube.middleDistance (Cube.reflect x) ≤ 1 := by
      rw [middleDistance_reflect]
      exact hx
    rw [hmiddle (Cube.reflect x) hxReflect]
    rw [← Cube.mem_reflectFinset_iff]
    rw [Cube.reflectFinset_upperResidueFinset]
  have hreflectedEq : reflected = Cube.lowerResidueFinset n 1 k :=
    eq_lowerResidueFinset_of_card_eq_of_middle_agreement
      k n hk hkn reflected hreflectedSeparated hreflectedCard hreflectedMiddle
  have hreflect := congrArg Cube.reflectFinset hreflectedEq
  dsimp [reflected] at hreflect
  rw [Cube.reflectFinset_reflectFinset,
    Cube.reflectFinset_lowerResidueFinset] at hreflect
  exact hreflect

/-- If an odd-dimensional extremal family chooses the lower middle layer,
then it agrees with the lower residue family on both middle ranks. -/
private theorem middle_agreement_lower_of_inter_eq_lower
    (hk : 0 < k) (hodd : Odd n) (candidate : Finset (Cube n 1))
    (hchoice : (candidate : Set (Cube n 1)) ∩
        DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) =
          Cube.layer n 1 (n / 2)) :
    ∀ x : Cube n 1, Cube.middleDistance x ≤ 1 →
      (x ∈ candidate ↔ x ∈ Cube.lowerResidueFinset n 1 k) := by
  intro x hxMiddle
  have hxRanks := (middleDistance_le_one_iff_rank_eq_middle x).mp hxMiddle
  have hupper : Cube.upperMiddleRank n 1 = n / 2 + 1 := by
    calc
      Cube.upperMiddleRank n 1 = Cube.lowerMiddleRank n 1 + 1 := by
        apply Cube.upperMiddleRank_eq_lowerMiddleRank_add_one_of_odd
        simpa using hodd
      _ = n / 2 + 1 := by simp [Cube.lowerMiddleRank]
  have hxAdjacent :
      x ∈ DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) := by
    change Cube.rank x = n / 2 ∨ Cube.rank x = n / 2 + 1
    rcases hxRanks with hx | hx
    · left
      simpa [Cube.lowerMiddleRank] using hx
    · right
      simpa [hupper] using hx
  have hcandidateIff : x ∈ candidate ↔ Cube.rank x = n / 2 := by
    have hmem := Set.ext_iff.mp hchoice x
    change (x ∈ candidate ∧
      x ∈ DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2)) ↔
        Cube.rank x = n / 2 at hmem
    exact ⟨fun hx ↦ hmem.mp ⟨hx, hxAdjacent⟩,
      fun hx ↦ (hmem.mpr hx).1⟩
  have hreferenceIff :=
    mem_lowerResidueFinset_iff_rank_eq_lowerMiddle_of_odd hk hodd x hxRanks
  rw [show Cube.lowerMiddleRank n 1 = n / 2 by simp [Cube.lowerMiddleRank]] at hreferenceIff
  exact hcandidateIff.trans hreferenceIff.symm

/-- If an odd-dimensional extremal family chooses the upper middle layer,
then it agrees with the upper residue family on both middle ranks. -/
private theorem middle_agreement_upper_of_inter_eq_upper
    (hk : 0 < k) (hodd : Odd n) (candidate : Finset (Cube n 1))
    (hchoice : (candidate : Set (Cube n 1)) ∩
        DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) =
          Cube.layer n 1 (n / 2 + 1)) :
    ∀ x : Cube n 1, Cube.middleDistance x ≤ 1 →
      (x ∈ candidate ↔ x ∈ Cube.upperResidueFinset n 1 k) := by
  intro x hxMiddle
  have hxRanks := (middleDistance_le_one_iff_rank_eq_middle x).mp hxMiddle
  have hupper : Cube.upperMiddleRank n 1 = n / 2 + 1 := by
    calc
      Cube.upperMiddleRank n 1 = Cube.lowerMiddleRank n 1 + 1 := by
        apply Cube.upperMiddleRank_eq_lowerMiddleRank_add_one_of_odd
        simpa using hodd
      _ = n / 2 + 1 := by simp [Cube.lowerMiddleRank]
  have hxAdjacent :
      x ∈ DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) := by
    change Cube.rank x = n / 2 ∨ Cube.rank x = n / 2 + 1
    rcases hxRanks with hx | hx
    · left
      simpa [Cube.lowerMiddleRank] using hx
    · right
      simpa [hupper] using hx
  have hcandidateIff : x ∈ candidate ↔ Cube.rank x = n / 2 + 1 := by
    have hmem := Set.ext_iff.mp hchoice x
    change (x ∈ candidate ∧
      x ∈ DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2)) ↔
        Cube.rank x = n / 2 + 1 at hmem
    exact ⟨fun hx ↦ hmem.mp ⟨hx, hxAdjacent⟩,
      fun hx ↦ (hmem.mpr hx).1⟩
  have hreferenceIff :=
    mem_upperResidueFinset_iff_rank_eq_upperMiddle_of_odd hk hodd x hxRanks
  rw [hupper] at hreferenceIff
  exact hcandidateIff.trans hreferenceIff.symm

/-- Classification of equality in the Boolean-cube bound: every extremal
`k`-separated family is one of the two distinguished residue families. -/
theorem eq_lowerResidueFinset_or_eq_upperResidueFinset_of_card_eq
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 1 k).card) :
    candidate = Cube.lowerResidueFinset n 1 k ∨
      candidate = Cube.upperResidueFinset n 1 k := by
  rcases Nat.even_or_odd n with heven | hodd
  · left
    have hmiddleSubset := middleLayer_subset_candidate_of_even
      k n hk hkn candidate hcandidate hcard heven
    apply eq_lowerResidueFinset_of_card_eq_of_middle_agreement
      k n hk hkn candidate hcandidate hcard
    intro x hxMiddle
    have hevenTotal : Even (n * 1) := by simpa using heven
    have hmiddleRanks := (middleDistance_le_one_iff_rank_eq_middle x).mp hxMiddle
    have hrank : Cube.rank x = n / 2 := by
      rcases hmiddleRanks with hx | hx
      · simpa [Cube.lowerMiddleRank] using hx
      · rw [← Cube.lowerMiddleRank_eq_upperMiddleRank_of_even n 1 hevenTotal] at hx
        simpa [Cube.lowerMiddleRank] using hx
    have hxcandidate : x ∈ candidate := hmiddleSubset (by
      change Cube.rank x = n / 2
      exact hrank)
    have hxreference : x ∈ Cube.lowerResidueFinset n 1 k := by
      simp only [Cube.lowerResidueFinset, Finset.mem_filter,
        Finset.mem_univ, true_and, one_mul]
      rw [hrank]
      rw [show Cube.lowerMiddleRank n 1 = n / 2 by simp [Cube.lowerMiddleRank]]
    exact iff_of_true hxcandidate hxreference
  · obtain hchoice | hchoice :=
      inter_middleLayers_eq_lower_or_upper_of_odd
        k n hk hkn candidate hcandidate hcard hodd
    · left
      apply eq_lowerResidueFinset_of_card_eq_of_middle_agreement
        k n hk hkn candidate hcandidate hcard
      exact middle_agreement_lower_of_inter_eq_lower hk.le hodd candidate hchoice
    · right
      apply eq_upperResidueFinset_of_card_eq_of_middle_agreement
        k n hk hkn candidate hcandidate hcard
      exact middle_agreement_upper_of_inter_eq_upper hk.le hodd candidate hchoice

/-- Equality in the Boolean cardinality bound holds exactly for the two
distinguished residue families. -/
theorem card_eq_lowerResidueFinset_iff_eq_lower_or_upper
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k) :
    candidate.card = (Cube.lowerResidueFinset n 1 k).card ↔
      candidate = Cube.lowerResidueFinset n 1 k ∨
        candidate = Cube.upperResidueFinset n 1 k := by
  constructor
  · exact eq_lowerResidueFinset_or_eq_upperResidueFinset_of_card_eq
      k n hk hkn candidate hcandidate
  · rintro (rfl | rfl)
    · rfl
    · exact (Cube.card_lowerResidueFinset_eq_card_upperResidueFinset
        (n := n) (d := 1) (k := k)).symm

/-- The complete `d = 1` conclusion of the paper: the lower residue family
gives the cardinality bound, and equality characterises precisely the lower
and upper residue families. -/
theorem cardinality_and_uniqueness
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n 1 k).card ∧
      (candidate.card = (Cube.lowerResidueFinset n 1 k).card ↔
        candidate = Cube.lowerResidueFinset n 1 k ∨
          candidate = Cube.upperResidueFinset n 1 k) := by
  exact ⟨kSeparated_card_le_lowerResidueFinset
      k n hk hkn candidate hcandidate,
    card_eq_lowerResidueFinset_iff_eq_lower_or_upper
      k n hk hkn candidate hcandidate⟩

end BooleanChain
end DOne
end WeightedChains
