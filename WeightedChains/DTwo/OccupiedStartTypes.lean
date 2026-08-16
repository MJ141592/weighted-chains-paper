import WeightedChains.DTwo.GroupedIncidence

/-!
# Arithmetic description of occupied ternary start types

Every lower ternary type labels a canonical metachain.  On the upper side,
only types more than `k` coordinate blocks beyond the middle are canonical
starts; the boundary at distance exactly `k` belongs to a symmetric chain
whose canonical label is its lower endpoint.
-/

noncomputable section

namespace WeightedChains
namespace Ternary

/-- Every valid dimension-indexed ternary type is represented by a cube
vertex. -/
theorem exists_vertex_of_typeCounts {n : ℕ} (t : TypeCounts n) :
    ∃ x : Cube n 2, TypeCounts.ofVertex x = t := by
  have hvalid : t.zeros + t.twos ≤ n := by
    have hsum := t.sum_eq
    omega
  have hpositive : 0 < (typeFiber n t.zeros t.twos).card := by
    rw [card_typeFiber]
    exact trinomial_pos hvalid
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  refine ⟨x, ?_⟩
  obtain ⟨hzero, htwo⟩ := mem_typeFiber.mp hx
  apply TypeCounts.ext
  · exact hzero
  · change oneCount x = t.ones
    have hxsum := zeroCount_add_oneCount_add_twoCount x
    have htsum := t.sum_eq
    omega
  · exact htwo

namespace BasicChain

variable {n : ℕ}

/-- A canonical last endpoint lies strictly more than `k` blocks above the
middle. -/
theorem canonicalStartType_zeros_add_k_lt_twos_of_not_first_of_good
    (B : BasicChain n) (k : ℕ) (_hk : 0 < k)
    (hfirst : ¬B.toChain.StartsAtFirst) (hgood : B.toChain.Good k) :
    B.canonicalStartType.zeros + k < B.canonicalStartType.twos := by
  have hwidth : (B.width : ℕ) = k :=
    width_eq_k_of_not_startsAtFirst_of_good B k hfirst hgood
  have hmidpoint : ¬(Cube.rank B.start + B.width ≤ n) := by
    intro h
    exact hfirst ((B.startsAtFirst_iff).2 (Or.inr h))
  have hrank := rank_add_zeroCount B.start
  have hzeroLast := B.zeroCount_evenVertex B.width le_rfl
  have htwoLast := B.twoCount_evenVertex B.width le_rfl
  have hwidthBound := B.width_le_zeroCount
  rw [← B.toChain_last] at hzeroLast htwoLast
  rw [B.canonicalStartType_eq_last hfirst]
  change zeroCount B.toChain.last + k < twoCount B.toChain.last
  omega

/-- A lower canonical type is occupied by its symmetric chain when inner and
by a full-width chain when outer. -/
theorem startGroup_nonempty_of_lower
    (k : ℕ) (_hk : 0 < k) (t : TypeCounts n)
    (hlower : t.twos ≤ t.zeros) :
    (startGroup n k t).Nonempty := by
  obtain ⟨x, hxType⟩ := exists_vertex_of_typeCounts t
  have hxLower : twoCount x ≤ zeroCount x := by
    have hzero := congrArg TypeCounts.zeros hxType
    have htwo := congrArg TypeCounts.twos hxType
    change zeroCount x = t.zeros at hzero
    change twoCount x = t.twos at htwo
    omega
  by_cases houter : twoCount x + k ≤ zeroCount x
  · obtain ⟨B, hstart, hwidth, hgood⟩ :=
      exists_good_width_eq x k (by omega)
    have hfirst : B.toChain.StartsAtFirst := by
      apply (B.startsAtFirst_iff).2
      right
      have hrank := rank_add_zeroCount B.start
      rw [hstart] at hrank
      rw [hstart, hwidth]
      omega
    refine ⟨B, (mem_startGroup_iff B k t).2 ⟨hgood, ?_⟩⟩
    rw [B.canonicalStartType_eq_first hfirst, B.toChain_first, hstart, hxType]
  · obtain ⟨B, hstart, hwidth, hsymm⟩ :=
      exists_symmetric_starting_at x hxLower
    have hsymmEq : zeroCount B.start = twoCount B.start + B.width :=
      (B.toChain_symmetric_iff).1 hsymm
    have hgood : B.toChain.Good k := by
      rw [B.toChain_good_iff]
      refine ⟨?_, Or.inl hsymmEq⟩
      rw [hwidth]
      omega
    have hfirst : B.toChain.StartsAtFirst := by
      apply (B.startsAtFirst_iff).2
      right
      have hrank := rank_add_zeroCount B.start
      omega
    refine ⟨B, (mem_startGroup_iff B k t).2 ⟨hgood, ?_⟩⟩
    rw [B.canonicalStartType_eq_first hfirst, B.toChain_first, hstart, hxType]

/-- An upper type strictly beyond the width-`k` boundary is occupied by a
full-width chain whose last endpoint has that type. -/
theorem startGroup_nonempty_of_upper_outer
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n)
    (hupper : t.zeros + k < t.twos) :
    (startGroup n k t).Nonempty := by
  have hktwo : k ≤ t.twos := by omega
  let s : TypeCounts n :=
    { zeros := t.zeros + k
      ones := t.ones
      twos := t.twos - k
      sum_eq := by
        have hsum := t.sum_eq
        omega }
  obtain ⟨x, hxType⟩ := exists_vertex_of_typeCounts s
  have hkzero : k ≤ zeroCount x := by
    have hzero := congrArg TypeCounts.zeros hxType
    change zeroCount x = t.zeros + k at hzero
    omega
  obtain ⟨B, hstart, hwidth, hgood⟩ := exists_good_width_eq x k hkzero
  have hnotFirst : ¬B.toChain.StartsAtFirst := by
    intro hfirst
    rcases (B.startsAtFirst_iff).1 hfirst with hzeroWidth | hmidpoint
    · omega
    · have hrank := rank_add_zeroCount B.start
      have hzero := congrArg TypeCounts.zeros hxType
      have htwo := congrArg TypeCounts.twos hxType
      change zeroCount x = t.zeros + k at hzero
      change twoCount x = t.twos - k at htwo
      rw [hstart] at hrank
      rw [hstart] at hmidpoint
      rw [hwidth] at hmidpoint
      omega
  refine ⟨B, (mem_startGroup_iff B k t).2 ⟨hgood, ?_⟩⟩
  rw [B.canonicalStartType_eq_last hnotFirst]
  have hzero := congrArg TypeCounts.zeros hxType
  have htwo := congrArg TypeCounts.twos hxType
  change zeroCount x = t.zeros + k at hzero
  change twoCount x = t.twos - k at htwo
  have hzeroLast := B.zeroCount_evenVertex B.width le_rfl
  have htwoLast := B.twoCount_evenVertex B.width le_rfl
  rw [← B.toChain_last] at hzeroLast htwoLast
  have hstartZero : zeroCount B.start = t.zeros + k := by rw [hstart, hzero]
  have hstartTwo : twoCount B.start = t.twos - k := by rw [hstart, htwo]
  apply TypeCounts.ext
  · change zeroCount B.toChain.last = t.zeros
    omega
  · change oneCount B.toChain.last = t.ones
    have hlastSum := zeroCount_add_oneCount_add_twoCount B.toChain.last
    have htypeSum := t.sum_eq
    omega
  · change twoCount B.toChain.last = t.twos
    omega

/-- Exact arithmetic description of the occupied canonical start types. -/
theorem mem_occupiedStartTypes_iff_arithmetic
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n) :
    t ∈ occupiedStartTypes n k ↔
      t.twos ≤ t.zeros ∨ t.zeros + k < t.twos := by
  rw [mem_occupiedStartTypes_iff]
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨hgood, htype⟩ := (mem_startGroup_iff B k t).1 hB
    by_cases hfirst : B.toChain.StartsAtFirst
    · left
      have hlower := canonicalStartType_twos_le_zeros_of_first_of_good
        B k hk hfirst hgood
      simpa only [htype] using hlower
    · right
      have hupper :=
        canonicalStartType_zeros_add_k_lt_twos_of_not_first_of_good
          B k hk hfirst hgood
      simpa only [htype] using hupper
  · rintro (hlower | hupper)
    · exact startGroup_nonempty_of_lower k hk t hlower
    · exact startGroup_nonempty_of_upper_outer k hk t hupper

end BasicChain
end Ternary
end WeightedChains
