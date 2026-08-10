import WeightedChains.DTwoStartGroups
import WeightedChains.DTwoMetachains

/-!
# Uniform type traces inside canonical ternary start groups

The paper's metachains are indexed by their endpoint farther from the middle.
This file shows that this canonical label determines both the width and the
initial type of every good basic-chain descriptor in the group. Consequently
all descriptors in one start group visit the same type at every time.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

/-- The first endpoint is at least as far from the middle as the last exactly
when the width is zero or the chain's rank midpoint is in the lower half. -/
theorem startsAtFirst_iff (B : BasicChain n) :
    B.toChain.StartsAtFirst ↔
      (B.width : ℕ) = 0 ∨ Cube.rank B.start + B.width ≤ n := by
  unfold Chain.StartsAtFirst Cube.middleDistance
  simp only [B.rank_toChain_first, B.rank_toChain_last]
  have hlastBound : Cube.rank B.start + 2 * B.width ≤ 2 * n := by
    have h := Cube.rank_le B.toChain.last
    rw [B.rank_toChain_last] at h
    omega
  by_cases hwidth : (B.width : ℕ) = 0
  · simp [hwidth]
  rw [or_iff_right hwidth]
  by_cases hlastLower : Cube.rank B.start + 2 * B.width ≤ n
  · have hfirstLower : Cube.rank B.start ≤ n := by omega
    rw [Nat.dist_eq_sub_of_le (by omega), Nat.dist_eq_sub_of_le (by omega)]
    omega
  · have hlastUpper : n ≤ Cube.rank B.start + 2 * B.width := by omega
    by_cases hfirstUpper : n ≤ Cube.rank B.start
    · rw [Nat.dist_eq_sub_of_le_right (by omega),
        Nat.dist_eq_sub_of_le_right (by omega)]
      omega
    · have hfirstLower : Cube.rank B.start ≤ n := by omega
      rw [Nat.dist_eq_sub_of_le_right (by omega),
        Nat.dist_eq_sub_of_le (by omega)]
      omega

/-- The width determined by a canonical start type. -/
def canonicalWidth (k : ℕ) (t : TypeCounts n) : ℕ :=
  if t.twos ≤ t.zeros then min k (t.zeros - t.twos) else k

private theorem start_rank_add_width_eq_dimension_of_symmetric
    (B : BasicChain n)
    (hsymmetric : zeroCount B.start = twoCount B.start + B.width) :
    Cube.rank B.start + B.width = n := by
  have hrank := rank_add_zeroCount B.start
  omega

/-- A good chain canonically starting at its first endpoint has a lower
canonical start type. -/
theorem canonicalStartType_twos_le_zeros_of_first_of_good
    (B : BasicChain n) (k : ℕ) (hk : 0 < k)
    (hfirst : B.toChain.StartsAtFirst) (hgood : B.toChain.Good k) :
    B.canonicalStartType.twos ≤ B.canonicalStartType.zeros := by
  rw [B.canonicalStartType_eq_first hfirst, B.toChain_first]
  change twoCount B.start ≤ zeroCount B.start
  obtain ⟨_hwidth, hsymm | hfull⟩ := (B.toChain_good_iff k).1 hgood
  · omega
  · have hwidthPositive : 0 < (B.width : ℕ) := by omega
    have hmidpoint := (B.startsAtFirst_iff).1 hfirst
    rcases hmidpoint with hzero | hmidpoint
    · omega
    · have hrank := rank_add_zeroCount B.start
      omega

/-- If a good chain's last endpoint is its unique farther endpoint, the chain
has the full prescribed width. -/
theorem width_eq_k_of_not_startsAtFirst_of_good
    (B : BasicChain n) (k : ℕ)
    (hfirst : ¬B.toChain.StartsAtFirst) (hgood : B.toChain.Good k) :
    (B.width : ℕ) = k := by
  obtain ⟨_hwidth, hsymm | hfull⟩ := (B.toChain_good_iff k).1 hgood
  · exfalso
    apply hfirst
    apply (B.startsAtFirst_iff).2
    right
    exact (start_rank_add_width_eq_dimension_of_symmetric B hsymm).le
  · exact hfull

/-- A good chain canonically starting at its last endpoint has a strictly
upper canonical start type. -/
theorem canonicalStartType_zeros_lt_twos_of_not_first_of_good
    (B : BasicChain n) (k : ℕ) (hk : 0 < k)
    (hfirst : ¬B.toChain.StartsAtFirst) (hgood : B.toChain.Good k) :
    B.canonicalStartType.zeros < B.canonicalStartType.twos := by
  have hwidth : (B.width : ℕ) = k :=
    width_eq_k_of_not_startsAtFirst_of_good B k hfirst hgood
  have hwidthPositive : 0 < (B.width : ℕ) := by omega
  have hmidpoint : ¬(Cube.rank B.start + B.width ≤ n) := by
    intro h
    exact hfirst ((B.startsAtFirst_iff).2 (Or.inr h))
  have hrank := rank_add_zeroCount B.start
  have hzeroLast := B.zeroCount_evenVertex B.width le_rfl
  have htwoLast := B.twoCount_evenVertex B.width le_rfl
  rw [← B.toChain_last] at hzeroLast htwoLast
  rw [B.canonicalStartType_eq_last hfirst]
  change zeroCount B.toChain.last < twoCount B.toChain.last
  omega

/-- The canonical start label determines the descriptor width. -/
theorem width_eq_canonicalWidth_of_good
    (B : BasicChain n) (k : ℕ) (hk : 0 < k)
    (hgood : B.toChain.Good k) :
    (B.width : ℕ) = canonicalWidth k B.canonicalStartType := by
  by_cases hfirst : B.toChain.StartsAtFirst
  · have hcanonical : B.canonicalStartType =
        TypeCounts.ofVertex B.start := by
      simpa only [B.toChain_first] using B.canonicalStartType_eq_first hfirst
    obtain ⟨hwidthLe, hsymm | hfull⟩ := (B.toChain_good_iff k).1 hgood
    · have hdiff : zeroCount B.start - twoCount B.start = B.width := by omega
      rw [canonicalWidth, hcanonical]
      simp only [TypeCounts.ofVertex]
      change (B.width : ℕ) =
        if twoCount B.start ≤ zeroCount B.start then
          min k (zeroCount B.start - twoCount B.start) else k
      rw [if_pos (by omega), hdiff, min_eq_right hwidthLe]
    · have hlower :=
        canonicalStartType_twos_le_zeros_of_first_of_good B k hk hfirst hgood
      have hmidpoint := (B.startsAtFirst_iff).1 hfirst
      have hwidthPositive : 0 < (B.width : ℕ) := by omega
      rcases hmidpoint with hzero | hmidpoint
      · omega
      · have hrank := rank_add_zeroCount B.start
        have hkdiff : k ≤ zeroCount B.start - twoCount B.start := by omega
        rw [canonicalWidth, if_pos hlower, hcanonical]
        simp only [TypeCounts.ofVertex]
        change (B.width : ℕ) = min k (zeroCount B.start - twoCount B.start)
        rw [hfull, min_eq_left hkdiff]
  · have hwidth := width_eq_k_of_not_startsAtFirst_of_good B k hfirst hgood
    have hupper :=
      canonicalStartType_zeros_lt_twos_of_not_first_of_good B k hk hfirst hgood
    rw [canonicalWidth, if_neg (Nat.not_le_of_lt hupper)]
    exact hwidth

/-- Descriptors in one canonical start group have the same width. -/
theorem width_eq_of_mem_startGroup
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n)
    {B C : BasicChain n} (hB : B ∈ startGroup n k t)
    (hC : C ∈ startGroup n k t) :
    (B.width : ℕ) = C.width := by
  obtain ⟨hBgood, hBtype⟩ := (mem_startGroup_iff B k t).1 hB
  obtain ⟨hCgood, hCtype⟩ := (mem_startGroup_iff C k t).1 hC
  rw [B.width_eq_canonicalWidth_of_good k hk hBgood,
    C.width_eq_canonicalWidth_of_good k hk hCgood, hBtype, hCtype]

/-- Descriptors in one canonical start group have the same raw initial
ternary type. -/
theorem type_start_eq_of_mem_startGroup
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n)
    {B C : BasicChain n} (hB : B ∈ startGroup n k t)
    (hC : C ∈ startGroup n k t) :
    TypeCounts.ofVertex B.start = TypeCounts.ofVertex C.start := by
  obtain ⟨hBgood, hBtype⟩ := (mem_startGroup_iff B k t).1 hB
  obtain ⟨hCgood, hCtype⟩ := (mem_startGroup_iff C k t).1 hC
  have hwidth := width_eq_of_mem_startGroup k hk t hB hC
  by_cases hBfirst : B.toChain.StartsAtFirst
  · by_cases hCfirst : C.toChain.StartsAtFirst
    · calc
        TypeCounts.ofVertex B.start = B.canonicalStartType := by
          rw [B.canonicalStartType_eq_first hBfirst, B.toChain_first]
        _ = t := hBtype
        _ = C.canonicalStartType := hCtype.symm
        _ = TypeCounts.ofVertex C.start := by
          rw [C.canonicalStartType_eq_first hCfirst, C.toChain_first]
    · have hBlower :=
        canonicalStartType_twos_le_zeros_of_first_of_good
          B k hk hBfirst hBgood
      have hCupper :=
        canonicalStartType_zeros_lt_twos_of_not_first_of_good
          C k hk hCfirst hCgood
      rw [hBtype] at hBlower
      rw [hCtype] at hCupper
      omega
  · by_cases hCfirst : C.toChain.StartsAtFirst
    · have hBupper :=
        canonicalStartType_zeros_lt_twos_of_not_first_of_good
          B k hk hBfirst hBgood
      have hClower :=
        canonicalStartType_twos_le_zeros_of_first_of_good
          C k hk hCfirst hCgood
      rw [hBtype] at hBupper
      rw [hCtype] at hClower
      omega
    · have hlastType : TypeCounts.ofVertex B.toChain.last =
          TypeCounts.ofVertex C.toChain.last := by
        calc
          TypeCounts.ofVertex B.toChain.last = B.canonicalStartType := by
            rw [B.canonicalStartType_eq_last hBfirst]
          _ = t := hBtype
          _ = C.canonicalStartType := hCtype.symm
          _ = TypeCounts.ofVertex C.toChain.last := by
            rw [C.canonicalStartType_eq_last hCfirst]
      have hzeroLast := congrArg TypeCounts.zeros hlastType
      have htwoLast := congrArg TypeCounts.twos hlastType
      change zeroCount B.toChain.last = zeroCount C.toChain.last at hzeroLast
      change twoCount B.toChain.last = twoCount C.toChain.last at htwoLast
      have hBzero := B.zeroCount_evenVertex B.width le_rfl
      have hCzero := C.zeroCount_evenVertex C.width le_rfl
      have hBtwo := B.twoCount_evenVertex B.width le_rfl
      have hCtwo := C.twoCount_evenVertex C.width le_rfl
      rw [← B.toChain_last] at hBzero hBtwo
      rw [← C.toChain_last] at hCzero hCtwo
      have hBbound := B.width_le_zeroCount
      have hCbound := C.width_le_zeroCount
      apply typeCounts_eq_of_zeroCount_eq_twoCount_eq
      · omega
      · omega

/-- All descriptors in one canonical start group visit the same type at each
common time. -/
theorem type_vertexAt_eq_of_mem_startGroup
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n)
    {B C : BasicChain n} (hB : B ∈ startGroup n k t)
    (hC : C ∈ startGroup n k t) (i : ℕ)
    (hi : i ≤ 2 * B.width) :
    TypeCounts.ofVertex (B.vertexAt i) =
      TypeCounts.ofVertex (C.vertexAt i) := by
  have hwidthNat := width_eq_of_mem_startGroup k hk t hB hC
  have hwidth : B.width = C.width := Fin.ext hwidthNat
  have hstart := type_start_eq_of_mem_startGroup k hk t hB hC
  apply B.type_vertexAt_eq_of_same_start_type C hwidth
  · exact congrArg TypeCounts.zeros hstart
  · exact congrArg TypeCounts.twos hstart
  · exact hi

end BasicChain
end Ternary
end WeightedChains
