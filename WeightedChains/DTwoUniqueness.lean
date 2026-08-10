import WeightedChains.DTwoMain
import WeightedChains.UniquenessPropagation

/-!
# Uniqueness of the extremal ternary family

The all-ones singleton is the sole zero-weight good descriptor.  We therefore
run the paper's outward induction on every other vertex and recover membership
of the exceptional point from equality of cardinalities at the end.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains

namespace UniquenessPropagation

variable {α ι : Type*} [DecidableEq α]

/-- Outward exact-one propagation with one exceptional reference point.  Once
all other memberships agree, equal cardinalities force agreement at the
exceptional point too. -/
theorem finset_eq_of_active_exact_one_outward_induction_except
    (blocks : ι → Finset α) (active : ι → Prop)
    (reference candidate : Finset α) (distance : α → ℕ) (exceptional : α)
    (hexact : ∀ i, active i → (candidate ∩ blocks i).card = 1)
    (hcard : candidate.card = reference.card)
    (hexceptional : exceptional ∈ reference)
    (hbase : ∀ x, x ≠ exceptional → distance x = 0 →
      (x ∈ candidate ↔ x ∈ reference))
    (hreference : ∀ x, x ∈ reference → x ≠ exceptional →
      0 < distance x →
      ∃ i, active i ∧ x ∈ blocks i ∧
        ∀ y ∈ blocks i, y ≠ x →
          distance y < distance x ∧ y ∉ reference)
    (hnonreference : ∀ x, x ∉ reference → 0 < distance x →
      ∃ i, active i ∧ x ∈ blocks i ∧
        ∃ y ∈ blocks i, y ∈ reference ∧ y ≠ exceptional ∧
          distance y < distance x) :
    candidate = reference := by
  have hagree : ∀ m : ℕ, ∀ x : α, x ≠ exceptional → distance x = m →
      (x ∈ candidate ↔ x ∈ reference) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hxExceptional hxDistance
      by_cases hm : m = 0
      · apply hbase x hxExceptional
        omega
      · have hxPositive : 0 < distance x := by omega
        by_cases hxReference : x ∈ reference
        · simp only [hxReference, iff_true]
          obtain ⟨i, hiActive, hxBlock, hother⟩ :=
            hreference x hxReference hxExceptional hxPositive
          refine (WeightedCover.mem_iff_other_points_not_mem_of_inter_card_eq_one
            (hexact i hiActive) hxBlock).2 ?_
          intro y hyBlock hyx
          obtain ⟨hyDistance, hyReference⟩ := hother y hyBlock hyx
          have hyExceptional : y ≠ exceptional := by
            intro hy
            subst y
            exact hyReference hexceptional
          have hyAgree : y ∈ candidate ↔ y ∈ reference := by
            apply ih (distance y)
            · omega
            · exact hyExceptional
            · rfl
          intro hyCandidate
          exact hyReference (hyAgree.1 hyCandidate)
        · simp only [hxReference, iff_false]
          obtain ⟨i, hiActive, hxBlock, y, hyBlock, hyReference,
            hyExceptional, hyDistance⟩ :=
            hnonreference x hxReference hxPositive
          have hyAgree : y ∈ candidate ↔ y ∈ reference := by
            apply ih (distance y)
            · omega
            · exact hyExceptional
            · rfl
          have hyCandidate : y ∈ candidate := hyAgree.2 hyReference
          have hxy : x ≠ y := by
            intro hxy
            subst y
            omega
          exact WeightedCover.not_mem_of_mem_of_inter_card_eq_one
            (hexact i hiActive) hyCandidate hyBlock hxBlock hxy
  have herase : candidate.erase exceptional = reference.erase exceptional := by
    ext x
    by_cases hx : x = exceptional
    · subst x
      simp
    · rw [Finset.mem_erase, Finset.mem_erase]
      constructor
      · rintro ⟨_hx, hcandidate⟩
        exact ⟨hx, (hagree (distance x) x hx rfl).1 hcandidate⟩
      · rintro ⟨_hx, hreference⟩
        exact ⟨hx, (hagree (distance x) x hx rfl).2 hreference⟩
  have hexceptionalCandidate : exceptional ∈ candidate := by
    by_contra hnot
    have hcandidateErase : (candidate.erase exceptional).card = candidate.card :=
      congrArg Finset.card (Finset.erase_eq_self.mpr hnot)
    have hreferenceErase : (reference.erase exceptional).card + 1 =
        reference.card := Finset.card_erase_add_one hexceptional
    have heraseCard := congrArg Finset.card herase
    omega
  apply Finset.ext
  intro x
  by_cases hx : x = exceptional
  · subst x
    simp [hexceptionalCandidate, hexceptional]
  · exact hagree (distance x) x hx rfl

end UniquenessPropagation

namespace Ternary
namespace BasicChain

variable {n k : ℕ}

/-- Oriented form of the reference endpoint construction: below the middle
the reference point is the first endpoint, and above it is the last. -/
private theorem exists_good_with_oriented_endpoint_avoiding_middle
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (_hkn : k ≤ n)
    (hxResidue : x ∈ Cube.lowerResidueFinset n 2 k)
    (hxNe : x ≠ middleVertex n) :
    ∃ B : BasicChain n,
      B.toChain.Good k ∧ middleVertex n ∉ B.toChain.vertices ∧
        ((Cube.rank x ≤ n ∧ B.toChain.first = x) ∨
          (n ≤ Cube.rank x ∧ B.toChain.last = x)) := by
  by_cases hlower : Cube.rank x ≤ n
  · obtain ⟨B, hstart, hgood, havoid⟩ :=
      exists_good_starting_at_avoiding_middle_of_lower_regular
        x k hk ((rank_le_dimension_iff x).1 hlower) hxNe
        (regular_counts_of_mem_lowerResidue x k hk hxResidue)
    exact ⟨B, hgood, havoid, Or.inl ⟨hlower, by rw [B.toChain_first, hstart]⟩⟩
  · have hreflectLower : Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      have hrank := Cube.rank_le x
      omega
    have hreflectResidue : Cube.reflect x ∈
        Cube.lowerResidueFinset n 2 k :=
      (reflect_mem_lowerResidueFinset_iff x k).2 hxResidue
    have hreflectNe : Cube.reflect x ≠ middleVertex n := by
      intro h
      apply hxNe
      calc
        x = Cube.reflect (Cube.reflect x) := (Cube.reflect_reflect x).symm
        _ = Cube.reflect (middleVertex n) := congrArg Cube.reflect h
        _ = middleVertex n := reflect_middleVertex n
    obtain ⟨B, hstart, hgood, havoid⟩ :=
      exists_good_starting_at_avoiding_middle_of_lower_regular
        (Cube.reflect x) k hk
        ((rank_le_dimension_iff (Cube.reflect x)).1 hreflectLower)
        hreflectNe
        (regular_counts_of_mem_lowerResidue
          (Cube.reflect x) k hk hreflectResidue)
    refine ⟨B.reflect, (B.toChain_good_reflect_iff k).2 hgood, ?_,
      Or.inr ⟨by omega, ?_⟩⟩
    · intro hmiddle
      rw [B.mem_vertices_reflect_iff, reflect_middleVertex] at hmiddle
      exact havoid hmiddle
    · rw [B.toChain_last_reflect, hstart, Cube.reflect_reflect]

/-- On the lower side, every other point of the short good chain beginning
at a noncentral reference point is strictly closer to the middle. -/
private theorem other_vertex_closer_of_lower_reference_first
    (x : Cube n 2) (k : ℕ) (hxResidue : x ∈ Cube.lowerResidueFinset n 2 k)
    (hxLower : Cube.rank x ≤ n) (hxPositive : 0 < Cube.middleDistance x)
    (B : BasicChain n) (hgood : B.toChain.Good k)
    (hfirst : B.toChain.first = x) {y : Cube n 2}
    (hy : y ∈ B.toChain.vertices) (hyx : y ≠ x) :
    Cube.middleDistance y < Cube.middleDistance x := by
  have hxRankLt : Cube.rank x < n := by
    have hxRankNe : Cube.rank x ≠ n := by
      intro h
      apply (Nat.ne_of_gt hxPositive)
      unfold Cube.middleDistance
      rw [h]
      rw [show n * 2 = 2 * n by omega, Nat.dist_self]
    omega
  have hxMod := mem_lowerResidueFinset_iff_rank_modEq.1 hxResidue
  have hgap : Cube.rank x + (2 * k + 1) ≤ n :=
    hxMod.add_le_of_lt hxRankLt
  have hwidth : (B.width : ℕ) ≤ k := by
    simpa only [B.toChain_width] using hgood.2.1
  rw [Chain.mem_vertices_iff] at hy
  obtain ⟨j, hj⟩ := hy
  change B.vertexAt j = y at hj
  have hjBound : (j : ℕ) ≤ 2 * B.width := by
    have hjLt := j.isLt
    simp only [B.toChain_steps] at hjLt
    omega
  have hjPositive : 0 < (j : ℕ) := by
    by_contra hnot
    have hjValZero : (j : ℕ) = 0 := Nat.eq_zero_of_not_pos hnot
    have hjZero : j = 0 := Fin.ext hjValZero
    subst j
    apply hyx
    calc
      y = B.vertexAt 0 := hj.symm
      _ = B.toChain.first := rfl
      _ = x := hfirst
  have hstart : B.start = x := B.toChain_first.symm.trans hfirst
  have hyRank : Cube.rank y = Cube.rank x + (j : ℕ) := by
    rw [← hj, B.rank_vertexAt (j : ℕ) hjBound, hstart]
  apply middleDistance_lt_of_rank_lt_rank_le_dimension
  · omega
  · omega

/-- Oriented endpoint form, with the upper case reduced to the preceding
lower statement by reflection. -/
private theorem other_vertex_closer_of_oriented_reference_endpoint
    (x : Cube n 2) (k : ℕ) (hxResidue : x ∈ Cube.lowerResidueFinset n 2 k)
    (hxPositive : 0 < Cube.middleDistance x) (B : BasicChain n)
    (hgood : B.toChain.Good k)
    (horiented : (Cube.rank x ≤ n ∧ B.toChain.first = x) ∨
      (n ≤ Cube.rank x ∧ B.toChain.last = x))
    {y : Cube n 2} (hy : y ∈ B.toChain.vertices) (hyx : y ≠ x) :
    Cube.middleDistance y < Cube.middleDistance x := by
  rcases horiented with ⟨hxLower, hfirst⟩ | ⟨hxUpper, hlast⟩
  · exact other_vertex_closer_of_lower_reference_first
      x k hxResidue hxLower hxPositive B hgood hfirst hy hyx
  · have hreflectResidue : Cube.reflect x ∈
        Cube.lowerResidueFinset n 2 k :=
      (reflect_mem_lowerResidueFinset_iff x k).2 hxResidue
    have hreflectLower : Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      have hxBound := Cube.rank_le x
      omega
    have hreflectPositive : 0 < Cube.middleDistance (Cube.reflect x) := by
      simpa only [middleDistance_reflect] using hxPositive
    have hreflectFirst : B.reflect.toChain.first = Cube.reflect x := by
      rw [B.toChain_first_reflect, hlast]
    have hyReflect : Cube.reflect y ∈ B.reflect.toChain.vertices := by
      rw [B.mem_vertices_reflect_iff, Cube.reflect_reflect]
      exact hy
    have hyxReflect : Cube.reflect y ≠ Cube.reflect x := by
      intro h
      apply hyx
      have := congrArg Cube.reflect h
      simpa using this
    have hcloser := other_vertex_closer_of_lower_reference_first
      (Cube.reflect x) k hreflectResidue hreflectLower hreflectPositive
      B.reflect ((B.toChain_good_reflect_iff k).2 hgood) hreflectFirst
      hyReflect hyxReflect
    simpa only [middleDistance_reflect] using hcloser

/-- Every extremal `k`-separated ternary family is the distinguished rank
residue family. -/
theorem eq_lowerResidueFinset_of_card_eq
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 2))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 2)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 2 k).card) :
    candidate = Cube.lowerResidueFinset n 2 k := by
  apply UniquenessPropagation.finset_eq_of_active_exact_one_outward_induction_except
    (fun B : BasicChain n ↦ B.toChain.vertices)
    (fun B : BasicChain n ↦
      B.toChain.Good k ∧ middleVertex n ∉ B.toChain.vertices)
    (Cube.lowerResidueFinset n 2 k) candidate Cube.middleDistance
    (middleVertex n)
  · intro B hactive
    exact inter_goodChain_card_eq_one_of_card_eq
      k n hk hkn candidate hcandidate hcard B hactive.1 hactive.2
  · exact hcard
  · rw [mem_lowerResidueFinset_iff_rank_modEq, rank_middleVertex]
  · intro x hxNe hxDistance
    have hxRank : Cube.rank x = n := by
      unfold Cube.middleDistance at hxDistance
      unfold Nat.dist at hxDistance
      omega
    have hxReference : x ∈ Cube.lowerResidueFinset n 2 k := by
      rw [mem_lowerResidueFinset_iff_rank_modEq, hxRank]
    obtain ⟨B, hstart, _hwidth, hvertices, hgood⟩ :=
      exists_singleton_good_of_rank_eq_dimension x k hxRank
    have havoid : middleVertex n ∉ B.toChain.vertices := by
      rw [hvertices]
      simpa only [Finset.mem_singleton] using Ne.symm hxNe
    have hone := inter_goodChain_card_eq_one_of_card_eq
      k n hk hkn candidate hcandidate hcard B hgood havoid
    have hxCandidate : x ∈ candidate := by
      by_contra hnot
      rw [hvertices] at hone
      simp [hnot] at hone
    exact iff_of_true hxCandidate hxReference
  · intro x hxReference hxNe hxPositive
    obtain ⟨B, hgood, havoid, horiented⟩ :=
      exists_good_with_oriented_endpoint_avoiding_middle
        x k hk hkn hxReference hxNe
    have hxMem : x ∈ B.toChain.vertices := by
      rcases horiented with ⟨_hxLower, hfirst⟩ | ⟨_hxUpper, hlast⟩
      · rw [Chain.mem_vertices_iff]
        exact ⟨0, hfirst⟩
      · rw [Chain.mem_vertices_iff]
        exact ⟨Fin.last B.toChain.steps, hlast⟩
    refine ⟨B, ⟨hgood, havoid⟩, hxMem, ?_⟩
    intro y hyMem hyx
    refine ⟨other_vertex_closer_of_oriented_reference_endpoint
      x k hxReference hxPositive B hgood horiented hyMem hyx, ?_⟩
    have honeReference :=
      hgood.card_lowerResidueFinset_inter_vertices B.toChain
    exact WeightedCover.not_mem_of_mem_of_inter_card_eq_one
      honeReference hxReference hxMem hyMem hyx
  · intro x hxReference hxPositive
    obtain ⟨B, y, hxMem, hyMem, hyReference, hyNe, hyCloser, hgood⟩ :=
      exists_closer_lowerResidue x k hk hkn hxReference
    have hmiddleReference : middleVertex n ∈
        Cube.lowerResidueFinset n 2 k := by
      rw [mem_lowerResidueFinset_iff_rank_modEq, rank_middleVertex]
    have havoid : middleVertex n ∉ B.toChain.vertices := by
      intro hmiddleMem
      have honeReference :=
        hgood.card_lowerResidueFinset_inter_vertices B.toChain
      have hnotMiddleReference :=
        WeightedCover.not_mem_of_mem_of_inter_card_eq_one
          honeReference hyReference hyMem hmiddleMem (Ne.symm hyNe)
      exact hnotMiddleReference hmiddleReference
    exact ⟨B, ⟨hgood, havoid⟩, hxMem,
      y, hyMem, hyReference, hyNe, hyCloser⟩

/-- Equality in the ternary cardinality bound is equivalent to being the
distinguished residue family. -/
theorem card_eq_lowerResidueFinset_iff_eq_lowerResidueFinset
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 2))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 2)) k) :
    candidate.card = (Cube.lowerResidueFinset n 2 k).card ↔
      candidate = Cube.lowerResidueFinset n 2 k := by
  constructor
  · exact eq_lowerResidueFinset_of_card_eq
      k n hk hkn candidate hcandidate
  · intro h
    rw [h]

/-- Full `d = 2` conclusion: the cardinality bound and uniqueness of its
equality case. -/
theorem cardinality_and_uniqueness
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 2))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 2)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n 2 k).card ∧
      (candidate.card = (Cube.lowerResidueFinset n 2 k).card ↔
        candidate = Cube.lowerResidueFinset n 2 k) := by
  exact ⟨kSeparated_card_le_lowerResidueFinset
      k n hk hkn candidate hcandidate,
    card_eq_lowerResidueFinset_iff_eq_lowerResidueFinset
      k n hk hkn candidate hcandidate⟩

end BasicChain
end Ternary
end WeightedChains
