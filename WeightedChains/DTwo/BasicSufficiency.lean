import WeightedChains.DTwo.ChainReflection
import WeightedChains.DTwo.Metachains

/-!
# Basic ternary chains suffice for the Section 5 geometry

This file formalises the geometric part of the paper's
`positive_basic_enough_lemma`.  The key observation is an exact description
of when a represented basic chain can contain the exceptional all-ones
vertex.  Away from the single type `(1,n-1,0)`, the canonical chain starting
at a lower vertex avoids the all-ones point.  For that remaining type, the
paper's width-two detour from type `(2,n-2,0)` gives the required chain; this
is precisely where the standing assumption `1 < k` is used.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

/-- A ternary vertex with no zero or two coordinates is the all-ones
vertex. -/
theorem eq_middleVertex_of_zeroCount_eq_zero_of_twoCount_eq_zero
    (x : Cube n 2) (hzero : zeroCount x = 0) (htwo : twoCount x = 0) :
    x = middleVertex n := by
  have hzeroCoordinates : zeroCoordinates x = ∅ :=
    Finset.card_eq_zero.mp (by simpa using hzero)
  have htwoCoordinates : twoCoordinates x = ∅ :=
    Finset.card_eq_zero.mp (by simpa using htwo)
  rw [← vertexOfCoordinatePair_zero_twoCoordinates x]
  funext i
  simp [vertexOfCoordinatePair, middleVertex, hzeroCoordinates, htwoCoordinates]

@[simp]
theorem reflect_middleVertex (n : ℕ) :
    Cube.reflect (middleVertex n) = middleVertex n := by
  funext i
  apply Fin.ext
  simp [middleVertex]

@[simp]
theorem rank_middleVertex (n : ℕ) :
    Cube.rank (middleVertex n) = n := by
  rw [rank_eq_oneCount_add_two_mul_twoCount]
  simp

@[simp]
theorem mem_lowerResidueFinset_iff_rank_modEq {x : Cube n 2} {k : ℕ} :
    x ∈ Cube.lowerResidueFinset n 2 k ↔
      Cube.rank x ≡ n [MOD 2 * k + 1] := by
  simp [Cube.lowerResidueFinset, Cube.lowerMiddleRank]

/-- In the ternary cube, moving strictly upwards while staying at or below
rank `n` moves strictly closer to the middle. -/
theorem middleDistance_lt_of_rank_lt_rank_le_dimension
    {x y : Cube n 2} (hxy : Cube.rank x < Cube.rank y)
    (hy : Cube.rank y ≤ n) :
    Cube.middleDistance y < Cube.middleDistance x := by
  unfold Cube.middleDistance
  rw [Nat.dist_eq_sub_of_le (by omega), Nat.dist_eq_sub_of_le (by omega)]
  omega

/-- Reflection fixes distance from the middle in the ternary cube. -/
@[simp]
theorem middleDistance_reflect (x : Cube n 2) :
    Cube.middleDistance (Cube.reflect x) = Cube.middleDistance x := by
  unfold Cube.middleDistance
  rw [Cube.rank_reflect]
  have hrank := Cube.rank_le x
  unfold Nat.dist
  omega

/-- Since the ternary cube has integral middle rank `n`, its lower residue
family is invariant under coordinatewise reflection. -/
@[simp]
theorem reflect_mem_lowerResidueFinset_iff (x : Cube n 2) (k : ℕ) :
    Cube.reflect x ∈ Cube.lowerResidueFinset n 2 k ↔
      x ∈ Cube.lowerResidueFinset n 2 k := by
  have hmiddle : n * 2 - n = n := by omega
  constructor
  · intro hx
    have hxUpper : Cube.reflect x ∈ Cube.upperResidueFinset n 2 k := by
      simpa [Cube.upperResidueFinset, Cube.lowerResidueFinset,
        Cube.upperMiddleRank, Cube.lowerMiddleRank, hmiddle] using hx
    exact (Cube.reflect_mem_upperResidueFinset_iff x).mp hxUpper
  · intro hx
    have hxUpper : Cube.reflect x ∈ Cube.upperResidueFinset n 2 k :=
      (Cube.reflect_mem_upperResidueFinset_iff x).mpr hx
    simpa [Cube.upperResidueFinset, Cube.lowerResidueFinset,
      Cube.upperMiddleRank, Cube.lowerMiddleRank, hmiddle] using hxUpper

/-- If a basic chain contains the all-ones point, its initial type and width
are forced.  There are only two possibilities: the all-ones singleton, or a
width-one chain starting at type `(1,n-1,0)`.

The converse is also true, but this one-way classification is the form used
by all avoidance arguments below. -/
theorem start_counts_of_middleVertex_mem (B : BasicChain n)
    (hmiddle : middleVertex n ∈ B.toChain.vertices) :
    (zeroCount B.start = 0 ∧ twoCount B.start = 0 ∧ (B.width : ℕ) = 0) ∨
      (zeroCount B.start = 1 ∧ twoCount B.start = 0 ∧ (B.width : ℕ) = 1) := by
  rw [Chain.mem_vertices_iff] at hmiddle
  obtain ⟨t, ht⟩ := hmiddle
  change B.vertexAt t = middleVertex n at ht
  have htBound : (t : ℕ) ≤ 2 * B.width := by
    have := t.isLt
    simpa only [B.toChain_steps] using Nat.le_of_lt_succ this
  obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' (t : ℕ)
  · have hiWidth : i ≤ B.width := by omega
    have hvertex : B.evenVertex i = middleVertex n := by
      rw [← B.vertexAt_even i, ← hi]
      exact ht
    have hzero := congrArg zeroCount hvertex
    have htwo := congrArg twoCount hvertex
    rw [B.zeroCount_evenVertex i hiWidth, zeroCount_middleVertex] at hzero
    rw [B.twoCount_evenVertex i hiWidth, twoCount_middleVertex] at htwo
    have hwidth := B.width_le_zeroCount
    left
    omega
  · have hiWidth : i < B.width := by omega
    have hvertex : B.oddVertex i hiWidth = middleVertex n := by
      rw [← B.vertexAt_odd i hiWidth, ← hi]
      exact ht
    have hzero := congrArg zeroCount hvertex
    have htwo := congrArg twoCount hvertex
    rw [B.zeroCount_oddVertex i hiWidth, zeroCount_middleVertex] at hzero
    rw [B.twoCount_oddVertex i hiWidth, twoCount_middleVertex] at htwo
    have hwidth := B.width_le_zeroCount
    right
    omega

/-- A convenient avoidance criterion extracted from
`start_counts_of_middleVertex_mem`. -/
theorem middleVertex_not_mem_of_start_counts (B : BasicChain n)
    (hsingleton : ¬(zeroCount B.start = 0 ∧ twoCount B.start = 0 ∧
      (B.width : ℕ) = 0))
    (honeStep : ¬(zeroCount B.start = 1 ∧ twoCount B.start = 0 ∧
      (B.width : ℕ) = 1)) :
    middleVertex n ∉ B.toChain.vertices := by
  intro hmiddle
  rcases B.start_counts_of_middleVertex_mem hmiddle with h | h
  · exact hsingleton h
  · exact honeStep h

/-- Every vertex in the middle layer is represented by a width-zero basic
good chain.  Thus the paper's assertion that its singleton chains are basic
holds for every middle-layer vertex, not only for the exceptional all-ones
point. -/
theorem exists_singleton_good_of_rank_eq_dimension (x : Cube n 2) (k : ℕ)
    (hmiddle : Cube.rank x = n) :
    ∃ B : BasicChain n,
      B.start = x ∧ (B.width : ℕ) = 0 ∧ B.toChain.vertices = {x} ∧
        B.toChain.Good k := by
  let B := ofStartWidth x 0 (by omega)
  refine ⟨B, rfl, rfl, ?_, ?_⟩
  · ext y
    rw [Chain.mem_vertices_iff]
    constructor
    · rintro ⟨i, hi⟩
      have hiZero : (i : ℕ) = 0 := by
        have := i.isLt
        change (i : ℕ) < 2 * B.width + 1 at this
        simp only [B, ofStartWidth_width] at this
        omega
      have hiIndex : i = 0 := Fin.ext hiZero
      subst i
      simp only [Finset.mem_singleton]
      calc
        y = B.toChain.vertex 0 := hi.symm
        _ = B.toChain.first := rfl
        _ = B.start := B.toChain_first
        _ = x := rfl
    · intro hy
      simp only [Finset.mem_singleton] at hy
      subst y
      refine ⟨⟨0, by simp [B]⟩, ?_⟩
      change B.toChain.first = x
      rw [B.toChain_first]
      rfl
  · rw [B.toChain_good_iff]
    refine ⟨by simp [B], Or.inl ?_⟩
    change zeroCount x = twoCount x + 0
    exact (rank_eq_dimension_iff x).mp hmiddle

/-- Let a good ternary chain begin at a lower vertex `x` outside the
distinguished residue family.  Its unique residue representative lies
strictly closer to the middle.  In the symmetric case we choose rank `n`;
in the full-length case modularity and the `2k` available steps force the
representative to occur between `x` and rank `n`.

The final hypothesis excludes the all-ones point from the chain and hence
also from the chosen representative. -/
theorem exists_closer_lowerResidue_of_good_starting_lower
    (B : BasicChain n) (x : Cube n 2) (k : ℕ)
    (hlower : Cube.rank x ≤ n) (hfirst : B.toChain.first = x)
    (hgood : B.toChain.Good k)
    (hxResidue : x ∉ Cube.lowerResidueFinset n 2 k)
    (havoid : middleVertex n ∉ B.toChain.vertices) :
    ∃ y : Cube n 2,
      y ∈ B.toChain.vertices ∧ y ∈ Cube.lowerResidueFinset n 2 k ∧
        y ≠ middleVertex n ∧ Cube.middleDistance y < Cube.middleDistance x := by
  rcases hgood.2.2 with hsymm | hlength
  · obtain ⟨i, hiRank⟩ :=
      Chain.exists_vertex_rank_eq_lowerMiddle_of_symmetric
        B.toChain hgood.1 hsymm
    let y := B.toChain.vertex i
    have hyRank : Cube.rank y = n := by
      simpa [y, Cube.lowerMiddleRank] using hiRank
    have hyMem : y ∈ B.toChain.vertices :=
      (Chain.mem_vertices_iff B.toChain y).2 ⟨i, rfl⟩
    have hyResidue : y ∈ Cube.lowerResidueFinset n 2 k := by
      rw [mem_lowerResidueFinset_iff_rank_modEq, hyRank]
    have hxRankNe : Cube.rank x ≠ n := by
      intro hxRank
      apply hxResidue
      rw [mem_lowerResidueFinset_iff_rank_modEq, hxRank]
    have hxRankLt : Cube.rank x < Cube.rank y := by omega
    exact ⟨y, hyMem, hyResidue, fun h ↦ havoid (h ▸ hyMem),
      middleDistance_lt_of_rank_lt_rank_le_dimension hxRankLt (by omega)⟩
  · obtain ⟨y, hyMem, hyResidue⟩ :=
      hgood.exists_mem_lowerResidueFinset B.toChain
    obtain ⟨i, hi⟩ := (Chain.mem_vertices_iff B.toChain y).mp hyMem
    have hxy : x ≤ y := by
      rw [← hfirst, Chain.first, ← hi]
      exact B.toChain.monotone_vertex (Fin.zero_le i)
    have hxyNe : x ≠ y := by
      intro hxyEq
      apply hxResidue
      rwa [hxyEq]
    have hRankLt : Cube.rank x < Cube.rank y :=
      Cube.rank_strictMono hxy hxyNe
    have hiLe : (i : ℕ) ≤ B.toChain.steps := by
      have := i.isLt
      omega
    have hsteps : B.toChain.steps = 2 * k := by
      unfold Chain.length at hlength
      omega
    have hyRankEq := Chain.rank_vertex_eq B.toChain hgood.1 i
    rw [hi, hfirst] at hyRankEq
    have hyRankUpper : Cube.rank y ≤ Cube.rank x + 2 * k := by omega
    have hyRankLtMiddlePlusModulus : Cube.rank y < n + (2 * k + 1) := by
      omega
    have hyMod : Cube.rank y ≡ n [MOD 2 * k + 1] :=
      mem_lowerResidueFinset_iff_rank_modEq.mp hyResidue
    have hyRankLe : Cube.rank y ≤ n :=
      hyMod.le_of_lt_add hyRankLtMiddlePlusModulus
    exact ⟨y, hyMem, hyResidue, fun h ↦ havoid (h ▸ hyMem),
      middleDistance_lt_of_rank_lt_rank_le_dimension hRankLt hyRankLe⟩

/-- The lower-half construction away from the exceptional type
`(1,n-1,0)`.  Outer vertices use width `k`; inner vertices use their
symmetric width.  The incidence classification proves that both choices
avoid the all-ones point. -/
theorem exists_good_starting_at_avoiding_middle_of_lower_regular
    (x : Cube n 2) (k : ℕ) (hk : 1 < k)
    (hlower : twoCount x ≤ zeroCount x)
    (hne : x ≠ middleVertex n)
    (hregular : zeroCount x ≠ 1 ∨ twoCount x ≠ 0) :
    ∃ B : BasicChain n,
      B.start = x ∧ B.toChain.Good k ∧ middleVertex n ∉ B.toChain.vertices := by
  by_cases houter : twoCount x + k ≤ zeroCount x
  · obtain ⟨B, hstart, hwidth, hgood⟩ := exists_good_width_eq x k (by omega)
    refine ⟨B, hstart, hgood, ?_⟩
    apply B.middleVertex_not_mem_of_start_counts
    · rintro ⟨_hzero, _htwo, hwidthZero⟩
      omega
    · rintro ⟨_hzero, _htwo, hwidthOne⟩
      omega
  · obtain ⟨B, hstart, hwidth, hsymm⟩ :=
      exists_symmetric_starting_at x hlower
    have hgood : B.toChain.Good k := by
      rw [B.toChain_good_iff]
      refine ⟨?_, Or.inl ((B.toChain_symmetric_iff).mp hsymm)⟩
      simpa only [hwidth] using
        (show zeroCount x - twoCount x ≤ k by omega)
    refine ⟨B, hstart, hgood, ?_⟩
    apply B.middleVertex_not_mem_of_start_counts
    · rintro ⟨hzero, htwo, _hwidthZero⟩
      apply hne
      apply eq_middleVertex_of_zeroCount_eq_zero_of_twoCount_eq_zero x
      · simpa only [hstart] using hzero
      · simpa only [hstart] using htwo
    · rintro ⟨hzero, htwo, _hwidthOne⟩
      exact hregular.elim
        (fun h ↦ h (by simpa only [hstart] using hzero))
        (fun h ↦ h (by simpa only [hstart] using htwo))

/-- The explicit width-two detour for the sole exceptional lower type
`(1,n-1,0)`.  Its first intermediate vertex is `x`, and its middle-layer
vertex has type `(1,n-2,1)`, so the chain avoids the all-ones point. -/
theorem exists_good_containing_avoiding_middle_of_type_one_zero
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hzero : zeroCount x = 1) (htwo : twoCount x = 0) :
    ∃ B : BasicChain n,
      x ∈ B.toChain.vertices ∧ B.toChain.Good k ∧
        middleVertex n ∉ B.toChain.vertices ∧ B.toChain.Symmetric := by
  classical
  have hn : 2 ≤ n := by omega
  have hpNonempty : (zeroCoordinates x).Nonempty := by
    rw [← Finset.card_pos, card_zeroCoordinates, hzero]
    norm_num
  obtain ⟨p, hp⟩ := hpNonempty
  have hxp : x p = 0 := by simpa [zeroCoordinates] using hp
  have hqExists : ∃ q : Fin n, x q ≠ 0 := by
    by_contra h
    have hAll : ∀ q : Fin n, x q = 0 := by
      intro q
      exact not_ne_iff.mp (not_exists.mp h q)
    have hzeroAll : zeroCoordinates x = Finset.univ := by
      ext q
      simp [zeroCoordinates, hAll q]
    have : zeroCount x = n := by
      rw [← card_zeroCoordinates, hzeroAll, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨q, hxqZero⟩ := hqExists
  have hqNotTwo : x q ≠ 2 := by
    intro hxqTwo
    have hq : q ∈ twoCoordinates x := by simp [twoCoordinates, hxqTwo]
    have hpositive : 0 < twoCount x := by
      rw [← card_twoCoordinates]
      exact Finset.card_pos.mpr ⟨q, hq⟩
    omega
  have hxq : x q = 1 := by
    apply Fin.ext
    have hbound : (x q : ℕ) ≤ 2 := by omega
    interval_cases hvalue : (x q : ℕ)
    · exact (hxqZero (Fin.ext hvalue)).elim
    · simp
    · exact (hqNotTwo (Fin.ext hvalue)).elim
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hxqZero hxp
  let z : Cube n 2 := Function.update x q 0
  have hzeroCoordinatesZ : zeroCoordinates z = insert q (zeroCoordinates x) := by
    ext r
    by_cases hrq : r = q
    · subst r
      simp [zeroCoordinates, z, hxqZero]
    · simp [zeroCoordinates, z, hrq]
  have htwoCoordinatesZ : twoCoordinates z = twoCoordinates x := by
    ext r
    by_cases hrq : r = q
    · subst r
      simp [twoCoordinates, z, hxq]
    · simp [twoCoordinates, z, hrq]
  have hzeroZ : zeroCount z = 2 := by
    rw [← card_zeroCoordinates, hzeroCoordinatesZ,
      Finset.card_insert_of_notMem (by simpa [zeroCoordinates] using hxqZero),
      card_zeroCoordinates, hzero]
  have htwoZ : twoCount z = 0 := by
    rw [← card_twoCoordinates, htwoCoordinatesZ, card_twoCoordinates, htwo]
  let coordinate : Fin 2 ↪ Fin n :=
    ⟨fun i ↦ if (i : ℕ) = 0 then q else p, by
      intro i j hij
      apply Fin.ext
      fin_cases i <;> fin_cases j <;> simp_all⟩
  have hcoordinateZero (i : Fin 2) : z (coordinate i) = 0 := by
    fin_cases i
    · simp [coordinate, z]
    · simp [coordinate, z, hpq, hxp]
  let B : BasicChain n :=
    { width := ⟨2, by omega⟩
      start := z
      coordinate := coordinate
      start_coordinate := hcoordinateZero }
  have hodd : B.oddVertex 0 (by simp [B]) = x := by
    funext r
    by_cases hrq : r = q
    · subst r
      simp [B, coordinate, oddVertex, hxq]
    · simp [B, coordinate, oddVertex, evenVertex, initialSegment, z,
        hrq]
  have hxMem : x ∈ B.toChain.vertices := by
    rw [Chain.mem_vertices_iff]
    refine ⟨⟨1, by simp [B]⟩, ?_⟩
    change B.vertexAt 1 = x
    rw [show 1 = 2 * 0 + 1 by norm_num, B.vertexAt_odd 0 (by simp [B]), hodd]
  have hsymm : B.toChain.Symmetric := by
    rw [B.toChain_symmetric_iff]
    simp [B, hzeroZ, htwoZ]
  have hgood : B.toChain.Good k := by
    rw [B.toChain_good_iff]
    exact ⟨by simp [B]; omega, Or.inl ((B.toChain_symmetric_iff).mp hsymm)⟩
  refine ⟨B, hxMem, hgood, ?_, hsymm⟩
  apply B.middleVertex_not_mem_of_start_counts
  · simp [B, hzeroZ]
  · simp [B, hzeroZ]

/-- Every lower-half vertex other than the all-ones point starts, or in the
single exceptional type lies on, a basic good chain avoiding that point. -/
theorem exists_good_containing_avoiding_middle_of_lower
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hlower : twoCount x ≤ zeroCount x) (hne : x ≠ middleVertex n) :
    ∃ B : BasicChain n,
      x ∈ B.toChain.vertices ∧ B.toChain.Good k ∧
        middleVertex n ∉ B.toChain.vertices := by
  by_cases hzero : zeroCount x = 1
  · by_cases htwo : twoCount x = 0
    · obtain ⟨B, hx, hgood, havoid, _hsymm⟩ :=
        exists_good_containing_avoiding_middle_of_type_one_zero
          x k hk hkn hzero htwo
      exact ⟨B, hx, hgood, havoid⟩
    · obtain ⟨B, hstart, hgood, havoid⟩ :=
        exists_good_starting_at_avoiding_middle_of_lower_regular
          x k hk hlower hne (Or.inr htwo)
      refine ⟨B, ?_, hgood, havoid⟩
      rw [Chain.mem_vertices_iff]
      refine ⟨0, ?_⟩
      change B.toChain.first = x
      rw [B.toChain_first, hstart]
  · obtain ⟨B, hstart, hgood, havoid⟩ :=
      exists_good_starting_at_avoiding_middle_of_lower_regular
        x k hk hlower hne (Or.inl hzero)
    refine ⟨B, ?_, hgood, havoid⟩
    rw [Chain.mem_vertices_iff]
    refine ⟨0, ?_⟩
    change B.toChain.first = x
    rw [B.toChain_first, hstart]

/-- Precise nonreference witness in the lower half: a vertex outside the
paper's residue family shares a basic good chain with a noncentral reference
vertex which is strictly closer to the middle. -/
theorem exists_closer_lowerResidue_of_lower
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hlower : twoCount x ≤ zeroCount x)
    (hxResidue : x ∉ Cube.lowerResidueFinset n 2 k) :
    ∃ (B : BasicChain n) (y : Cube n 2),
      x ∈ B.toChain.vertices ∧ y ∈ B.toChain.vertices ∧
        y ∈ Cube.lowerResidueFinset n 2 k ∧ y ≠ middleVertex n ∧
          Cube.middleDistance y < Cube.middleDistance x ∧ B.toChain.Good k := by
  have hxNe : x ≠ middleVertex n := by
    intro hx
    apply hxResidue
    subst x
    rw [mem_lowerResidueFinset_iff_rank_modEq, rank_middleVertex]
  by_cases hzero : zeroCount x = 1
  · by_cases htwo : twoCount x = 0
    · obtain ⟨B, hxMem, hgood, havoid, hsymm⟩ :=
        exists_good_containing_avoiding_middle_of_type_one_zero
          x k hk hkn hzero htwo
      obtain ⟨i, hiRank⟩ :=
        Chain.exists_vertex_rank_eq_lowerMiddle_of_symmetric
          B.toChain hgood.1 hsymm
      let y := B.toChain.vertex i
      have hyRank : Cube.rank y = n := by
        simpa [y, Cube.lowerMiddleRank] using hiRank
      have hyMem : y ∈ B.toChain.vertices :=
        (Chain.mem_vertices_iff B.toChain y).2 ⟨i, rfl⟩
      have hyResidue : y ∈ Cube.lowerResidueFinset n 2 k := by
        rw [mem_lowerResidueFinset_iff_rank_modEq, hyRank]
      have hxRankEquation := rank_add_zeroCount x
      rw [hzero, htwo] at hxRankEquation
      have hxRankLt : Cube.rank x < Cube.rank y := by omega
      exact ⟨B, y, hxMem, hyMem, hyResidue,
        fun h ↦ havoid (h ▸ hyMem),
        middleDistance_lt_of_rank_lt_rank_le_dimension hxRankLt (by omega), hgood⟩
    · obtain ⟨B, hstart, hgood, havoid⟩ :=
        exists_good_starting_at_avoiding_middle_of_lower_regular
          x k hk hlower hxNe (Or.inr htwo)
      have hfirst : B.toChain.first = x := by rw [B.toChain_first, hstart]
      obtain ⟨y, hyMem, hyResidue, hyNe, hyCloser⟩ :=
        exists_closer_lowerResidue_of_good_starting_lower
          B x k ((rank_le_dimension_iff x).2 hlower) hfirst
          hgood hxResidue havoid
      have hxMem : x ∈ B.toChain.vertices := by
        rw [Chain.mem_vertices_iff]
        exact ⟨0, by simpa only [Chain.first] using hfirst⟩
      exact ⟨B, y, hxMem, hyMem, hyResidue, hyNe, hyCloser, hgood⟩
  · obtain ⟨B, hstart, hgood, havoid⟩ :=
      exists_good_starting_at_avoiding_middle_of_lower_regular
        x k hk hlower hxNe (Or.inl hzero)
    have hfirst : B.toChain.first = x := by rw [B.toChain_first, hstart]
    obtain ⟨y, hyMem, hyResidue, hyNe, hyCloser⟩ :=
      exists_closer_lowerResidue_of_good_starting_lower
        B x k ((rank_le_dimension_iff x).2 hlower) hfirst
        hgood hxResidue havoid
    have hxMem : x ∈ B.toChain.vertices := by
      rw [Chain.mem_vertices_iff]
      exact ⟨0, by simpa only [Chain.first] using hfirst⟩
    exact ⟨B, y, hxMem, hyMem, hyResidue, hyNe, hyCloser, hgood⟩

/-- Corrected geometric core of Section 5: under the theorem's assumptions,
every ternary vertex except `(1,...,1)` lies on a basic good chain which does
not contain `(1,...,1)`.

Upper-half vertices are handled by reflecting the lower-half construction. -/
theorem exists_good_containing_avoiding_middle
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hne : x ≠ middleVertex n) :
    ∃ B : BasicChain n,
      x ∈ B.toChain.vertices ∧ B.toChain.Good k ∧
        middleVertex n ∉ B.toChain.vertices := by
  by_cases hlower : Cube.rank x ≤ n
  · exact exists_good_containing_avoiding_middle_of_lower x k hk hkn
      ((rank_le_dimension_iff x).mp hlower) hne
  · have hreflectLower : Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      have hrank := Cube.rank_le x
      omega
    have hreflectNe : Cube.reflect x ≠ middleVertex n := by
      intro h
      apply hne
      calc
        x = Cube.reflect (Cube.reflect x) := (Cube.reflect_reflect x).symm
        _ = Cube.reflect (middleVertex n) := congrArg Cube.reflect h
        _ = middleVertex n := reflect_middleVertex n
    obtain ⟨B, hx, hgood, havoid⟩ :=
      exists_good_containing_avoiding_middle_of_lower
        (Cube.reflect x) k hk hkn
        ((rank_le_dimension_iff (Cube.reflect x)).mp hreflectLower) hreflectNe
    refine ⟨B.reflect, ?_, (B.toChain_good_reflect_iff k).mpr hgood, ?_⟩
    · rw [B.mem_vertices_reflect_iff]
      exact hx
    · intro hmiddle
      rw [B.mem_vertices_reflect_iff, reflect_middleVertex] at hmiddle
      exact havoid hmiddle

/-- A point of the reference residue family cannot have the exceptional
lower type `(1,n-1,0)` when `k>1`. -/
theorem regular_counts_of_mem_lowerResidue
    (x : Cube n 2) (k : ℕ) (hk : 1 < k)
    (hxResidue : x ∈ Cube.lowerResidueFinset n 2 k) :
    zeroCount x ≠ 1 ∨ twoCount x ≠ 0 := by
  by_cases hzero : zeroCount x = 1
  · right
    intro htwo
    have hrank := rank_add_zeroCount x
    rw [hzero, htwo] at hrank
    have hmod := mem_lowerResidueFinset_iff_rank_modEq.mp hxResidue
    have hgap : Cube.rank x + (2 * k + 1) ≤ n :=
      hmod.add_le_of_lt (by omega)
    omega
  · exact Or.inl hzero

/-- Reference-family assertion of the corrected Section 5 lemma.  Every
noncentral reference vertex is an endpoint of a basic good chain avoiding
the all-ones point.  For an upper vertex the endpoint is the last vertex of
the reflected lower construction. -/
theorem exists_good_with_endpoint_avoiding_middle_of_lowerResidue
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (_hkn : k ≤ n)
    (hxResidue : x ∈ Cube.lowerResidueFinset n 2 k)
    (hxNe : x ≠ middleVertex n) :
    ∃ B : BasicChain n,
      B.toChain.Good k ∧ middleVertex n ∉ B.toChain.vertices ∧
        (B.toChain.first = x ∨ B.toChain.last = x) := by
  by_cases hlower : Cube.rank x ≤ n
  · obtain ⟨B, hstart, hgood, havoid⟩ :=
      exists_good_starting_at_avoiding_middle_of_lower_regular
        x k hk ((rank_le_dimension_iff x).mp hlower) hxNe
        (regular_counts_of_mem_lowerResidue x k hk hxResidue)
    exact ⟨B, hgood, havoid, Or.inl (by rw [B.toChain_first, hstart])⟩
  · have hreflectLower : Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      have hrank := Cube.rank_le x
      omega
    have hreflectResidue :
        Cube.reflect x ∈ Cube.lowerResidueFinset n 2 k :=
      (reflect_mem_lowerResidueFinset_iff x k).mpr hxResidue
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
        ((rank_le_dimension_iff (Cube.reflect x)).mp hreflectLower)
        hreflectNe
        (regular_counts_of_mem_lowerResidue
          (Cube.reflect x) k hk hreflectResidue)
    refine ⟨B.reflect, (B.toChain_good_reflect_iff k).mpr hgood, ?_, Or.inr ?_⟩
    · intro hmiddle
      rw [B.mem_vertices_reflect_iff, reflect_middleVertex] at hmiddle
      exact havoid hmiddle
    · rw [B.toChain_last_reflect, hstart, Cube.reflect_reflect]

/-- Full nonreference assertion of the corrected
`positive_basic_enough_lemma`: every point outside the distinguished residue
family shares a basic good chain with a noncentral member of that family
which is strictly closer to the middle of the cube. -/
theorem exists_closer_lowerResidue
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hxResidue : x ∉ Cube.lowerResidueFinset n 2 k) :
    ∃ (B : BasicChain n) (y : Cube n 2),
      x ∈ B.toChain.vertices ∧ y ∈ B.toChain.vertices ∧
        y ∈ Cube.lowerResidueFinset n 2 k ∧ y ≠ middleVertex n ∧
          Cube.middleDistance y < Cube.middleDistance x ∧ B.toChain.Good k := by
  by_cases hlower : Cube.rank x ≤ n
  · exact exists_closer_lowerResidue_of_lower x k hk hkn
      ((rank_le_dimension_iff x).mp hlower) hxResidue
  · have hreflectLower : Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      have hrank := Cube.rank_le x
      omega
    have hxReflectResidue :
        Cube.reflect x ∉ Cube.lowerResidueFinset n 2 k := by
      intro h
      exact hxResidue ((reflect_mem_lowerResidueFinset_iff x k).mp h)
    obtain ⟨B, y, hxMem, hyMem, hyResidue, hyNe, hyCloser, hgood⟩ :=
      exists_closer_lowerResidue_of_lower
        (Cube.reflect x) k hk hkn
        ((rank_le_dimension_iff (Cube.reflect x)).mp hreflectLower)
        hxReflectResidue
    refine ⟨B.reflect, Cube.reflect y, ?_, ?_, ?_, ?_, ?_,
      (B.toChain_good_reflect_iff k).mpr hgood⟩
    · rw [B.mem_vertices_reflect_iff]
      exact hxMem
    · rw [B.mem_vertices_reflect_iff, Cube.reflect_reflect]
      exact hyMem
    · exact (reflect_mem_lowerResidueFinset_iff y k).mpr hyResidue
    · intro h
      apply hyNe
      calc
        y = Cube.reflect (Cube.reflect y) := (Cube.reflect_reflect y).symm
        _ = Cube.reflect (middleVertex n) := congrArg Cube.reflect h
        _ = middleVertex n := reflect_middleVertex n
    · simpa only [middleDistance_reflect] using hyCloser

/-- Every nonexceptional vertex therefore shares such a chain with a
nonexceptional member of the paper's reference residue family.  This is the
incidence part of the last two assertions of
`positive_basic_enough_lemma`; the sharper rank-distance comparison is
separated from it so it can be proved from the explicit type-by-type
construction. -/
theorem exists_good_with_noncentral_lowerResidue
    (x : Cube n 2) (k : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (hne : x ≠ middleVertex n) :
    ∃ (B : BasicChain n) (y : Cube n 2),
      x ∈ B.toChain.vertices ∧ y ∈ B.toChain.vertices ∧
        y ∈ Cube.lowerResidueFinset n 2 k ∧ y ≠ middleVertex n ∧
          B.toChain.Good k := by
  obtain ⟨B, hx, hgood, havoid⟩ :=
    exists_good_containing_avoiding_middle x k hk hkn hne
  obtain ⟨y, hy, hyResidue⟩ := hgood.exists_mem_lowerResidueFinset B.toChain
  exact ⟨B, y, hx, hy, hyResidue, fun h ↦ havoid (h ▸ hy), hgood⟩

end BasicChain
end Ternary
end WeightedChains
