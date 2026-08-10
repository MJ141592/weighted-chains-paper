import WeightedChains.DTwo
import WeightedChains.DTwoOrbits

/-!
# Basic ternary chains

A finite representation of the basic chains from Section 5.  Each descriptor
contains an ordered, injective list of coordinates which are initially zero;
the chain changes each selected coordinate `0 → 1 → 2` before moving to
the next coordinate.
-/

set_option autoImplicit false

namespace WeightedChains

namespace Ternary

/-- A finite descriptor for an oriented basic chain in `{0,1,2}^n`.
`width` coordinates are changed, in the order given by `coordinate`. -/
@[ext]
structure BasicChain (n : ℕ) where
  width : Fin (n + 1)
  start : Cube n 2
  coordinate : Fin width ↪ Fin n
  start_coordinate : ∀ i, start (coordinate i) = 0

private def BasicChain.finiteCode (n : ℕ) (B : BasicChain n) :
    Σ w : Fin (n + 1), Cube n 2 × (Fin w ↪ Fin n) :=
  ⟨B.width, B.start, B.coordinate⟩

private theorem BasicChain.finiteCode_injective (n : ℕ) :
    Function.Injective (BasicChain.finiteCode n) := by
  intro B C h
  cases B
  cases C
  cases h
  rfl

noncomputable instance (n : ℕ) : Fintype (BasicChain n) :=
  Fintype.ofInjective (BasicChain.finiteCode n) (BasicChain.finiteCode_injective n)

namespace BasicChain

variable {n : ℕ}

/-- Coordinates among the first `i` entries of the ordered coordinate list. -/
def initialSegment (B : BasicChain n) (i : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin B.width ↦ (j : ℕ) < i).image B.coordinate

@[simp]
theorem mem_initialSegment_iff (B : BasicChain n) (i : ℕ) (q : Fin n) :
    q ∈ B.initialSegment i ↔ ∃ j : Fin B.width, (j : ℕ) < i ∧ B.coordinate j = q := by
  simp [initialSegment]

theorem card_initialSegment (B : BasicChain n) {i : ℕ} (hi : i ≤ B.width) :
    (B.initialSegment i).card = i := by
  rw [initialSegment, Finset.card_image_of_injective _ B.coordinate.injective,
    Fin.card_filter_val_lt, min_eq_right hi]

theorem initialSegment_subset_zeroCoordinates (B : BasicChain n) (i : ℕ) :
    B.initialSegment i ⊆ zeroCoordinates B.start := by
  intro q hq
  rw [mem_initialSegment_iff] at hq
  rcases hq with ⟨j, _hj, rfl⟩
  simp [zeroCoordinates, B.start_coordinate j]

/-- By time `t`, coordinate `q` has completed its two changes. -/
def reachedTwo (B : BasicChain n) (t : ℕ) (q : Fin n) : Prop :=
  ∃ j : Fin B.width, B.coordinate j = q ∧ 2 * ((j : ℕ) + 1) ≤ t

/-- By time `t`, coordinate `q` has made at least its first change. -/
def reachedOne (B : BasicChain n) (t : ℕ) (q : Fin n) : Prop :=
  ∃ j : Fin B.width, B.coordinate j = q ∧ 2 * (j : ℕ) + 1 ≤ t

theorem reachedTwo_implies_reachedOne (B : BasicChain n) {t : ℕ} {q : Fin n}
    (h : B.reachedTwo t q) : B.reachedOne t q := by
  rcases h with ⟨j, hj, ht⟩
  exact ⟨j, hj, by omega⟩

theorem reachedTwo_mono (B : BasicChain n) {s t : ℕ} (hst : s ≤ t) {q : Fin n}
    (h : B.reachedTwo s q) : B.reachedTwo t q := by
  rcases h with ⟨j, hj, hs⟩
  exact ⟨j, hj, hs.trans hst⟩

theorem reachedOne_mono (B : BasicChain n) {s t : ℕ} (hst : s ≤ t) {q : Fin n}
    (h : B.reachedOne s q) : B.reachedOne t q := by
  rcases h with ⟨j, hj, hs⟩
  exact ⟨j, hj, hs.trans hst⟩

/-- The vertex after `t` individual rank steps. -/
noncomputable def vertexAt (B : BasicChain n) (t : ℕ) : Cube n 2 := by
  classical
  exact fun q ↦ if B.reachedTwo t q then 2 else if B.reachedOne t q then 1 else B.start q

theorem vertexAt_mono (B : BasicChain n) : Monotone B.vertexAt := by
  intro s t hst q
  by_cases hs2 : B.reachedTwo s q
  · have ht2 : B.reachedTwo t q := B.reachedTwo_mono hst hs2
    simp only [vertexAt, if_pos hs2, if_pos ht2]
    exact le_rfl
  · by_cases hs1 : B.reachedOne s q
    · have ht1 : B.reachedOne t q := B.reachedOne_mono hst hs1
      by_cases ht2 : B.reachedTwo t q
      · simp only [vertexAt, if_neg hs2, if_pos hs1, if_pos ht2]
        change (1 : ℕ) ≤ 2
        omega
      · simp only [vertexAt, if_neg hs2, if_pos hs1, if_neg ht2, if_pos ht1]
        exact le_rfl
    · by_cases ht2 : B.reachedTwo t q
      · obtain ⟨j, hj, _ht⟩ := ht2
        have hstart : B.start q = 0 := by rw [← hj]; exact B.start_coordinate j
        have hsource : B.vertexAt s q = 0 := by
          simp [vertexAt, hs2, hs1, hstart]
        rw [hsource]
        exact Fin.zero_le _
      · by_cases ht1 : B.reachedOne t q
        · obtain ⟨j, hj, _ht⟩ := ht1
          have hstart : B.start q = 0 := by rw [← hj]; exact B.start_coordinate j
          have hsource : B.vertexAt s q = 0 := by
            simp [vertexAt, hs2, hs1, hstart]
          rw [hsource]
          exact Fin.zero_le _
        · simp only [vertexAt, if_neg hs2, if_neg hs1, if_neg ht2, if_neg ht1]
          exact le_rfl

/-- The associated generic chain has `2 * width + 1` vertices. -/
noncomputable def toChain (B : BasicChain n) : Chain n 2 where
  steps := 2 * B.width
  vertex t := B.vertexAt t
  monotone_vertex := fun {_i _j} hij ↦ B.vertexAt_mono (by exact_mod_cast hij)

/-- A completed-block vertex, after the first `i` selected coordinates have
been changed all the way to two. -/
def evenVertex (B : BasicChain n) (i : ℕ) : Cube n 2 :=
  fun q ↦ if q ∈ B.initialSegment i then 2 else B.start q

/-- The intermediate vertex in block `i`, where the current coordinate is
one and all earlier selected coordinates are two. -/
def oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) : Cube n 2 :=
  fun q ↦ if q = B.coordinate ⟨i, hi⟩ then 1 else B.evenVertex i q

theorem coordinate_not_mem_initialSegment (B : BasicChain n) (i : ℕ)
    (hi : i < B.width) : B.coordinate ⟨i, hi⟩ ∉ B.initialSegment i := by
  rw [mem_initialSegment_iff]
  rintro ⟨j, hj, heq⟩
  have hji : j = ⟨i, hi⟩ := B.coordinate.injective heq
  have hval : (j : ℕ) = i := congrArg Fin.val hji
  omega

theorem zeroCoordinates_evenVertex (B : BasicChain n) (i : ℕ) :
    zeroCoordinates (B.evenVertex i) = zeroCoordinates B.start \ B.initialSegment i := by
  ext q
  by_cases hq : q ∈ B.initialSegment i
  · have hvalue : B.evenVertex i q = 2 := by rw [evenVertex, if_pos hq]
    simp only [zeroCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, hvalue, hq, not_true_eq_false, and_false]
    constructor
    · intro h
      have hval := congrArg Fin.val h
      norm_num at hval
    · intro h
      contradiction
  · have hvalue : B.evenVertex i q = B.start q := by rw [evenVertex, if_neg hq]
    simp only [zeroCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, hvalue, hq, not_false_eq_true, and_true]

theorem twoCoordinates_evenVertex (B : BasicChain n) (i : ℕ) :
    twoCoordinates (B.evenVertex i) = twoCoordinates B.start ∪ B.initialSegment i := by
  ext q
  by_cases hq : q ∈ B.initialSegment i
  · have hvalue : B.evenVertex i q = 2 := by rw [evenVertex, if_pos hq]
    simp only [twoCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, hvalue, hq, or_true]
  · have hvalue : B.evenVertex i q = B.start q := by rw [evenVertex, if_neg hq]
    simp only [twoCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, hvalue, hq, or_false]

theorem zeroCount_evenVertex (B : BasicChain n) (i : ℕ) (hi : i ≤ B.width) :
    zeroCount (B.evenVertex i) = zeroCount B.start - i := by
  change (zeroCoordinates (B.evenVertex i)).card = (zeroCoordinates B.start).card - i
  rw [B.zeroCoordinates_evenVertex, Finset.card_sdiff_of_subset
    (B.initialSegment_subset_zeroCoordinates i), B.card_initialSegment hi]

theorem twoCount_evenVertex (B : BasicChain n) (i : ℕ) (hi : i ≤ B.width) :
    twoCount (B.evenVertex i) = twoCount B.start + i := by
  change (twoCoordinates (B.evenVertex i)).card = (twoCoordinates B.start).card + i
  rw [B.twoCoordinates_evenVertex, Finset.card_union_of_disjoint, B.card_initialSegment hi]
  exact Finset.disjoint_of_subset_right (B.initialSegment_subset_zeroCoordinates i)
    (disjoint_zeroCoordinates_twoCoordinates B.start).symm

theorem oneCount_evenVertex (B : BasicChain n) (i : ℕ) (hi : i ≤ B.width) :
    oneCount (B.evenVertex i) = oneCount B.start := by
  have hstart := zeroCount_add_oneCount_add_twoCount B.start
  have heven := zeroCount_add_oneCount_add_twoCount (B.evenVertex i)
  rw [B.zeroCount_evenVertex i hi, B.twoCount_evenVertex i hi] at heven
  have hzero : i ≤ zeroCount B.start := by
    rw [← B.card_initialSegment hi]
    exact Finset.card_le_card (B.initialSegment_subset_zeroCoordinates i)
  omega

theorem type_evenVertex (B : BasicChain n) (i : ℕ) (hi : i ≤ B.width) :
    TypeCounts.ofVertex (B.evenVertex i) =
      (TypeCounts.ofVertex B.start).evenStep i (by
        simpa only [TypeCounts.ofVertex] using
          (show i ≤ zeroCount B.start from by
            rw [← B.card_initialSegment hi]
            exact Finset.card_le_card (B.initialSegment_subset_zeroCoordinates i))) := by
  apply TypeCounts.ext
  · exact B.zeroCount_evenVertex i hi
  · exact B.oneCount_evenVertex i hi
  · exact B.twoCount_evenVertex i hi

theorem zeroCoordinates_oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    zeroCoordinates (B.oddVertex i hi) =
      zeroCoordinates B.start \ (insert (B.coordinate ⟨i, hi⟩) (B.initialSegment i)) := by
  ext q
  by_cases hcurrent : q = B.coordinate ⟨i, hi⟩
  · subst q
    have hvalue : B.oddVertex i hi (B.coordinate ⟨i, hi⟩) = 1 := by
      rw [oddVertex, if_pos rfl]
    simp only [zeroCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_insert, hvalue, true_or, not_true_eq_false, and_false]
    norm_num
  · have hvalue : B.oddVertex i hi q = B.evenVertex i q := by
      rw [oddVertex, if_neg hcurrent]
    rw [show q ∈ zeroCoordinates (B.oddVertex i hi) ↔
        q ∈ zeroCoordinates (B.evenVertex i) by
      simp only [zeroCoordinates, Finset.mem_filter, Finset.mem_univ, true_and, hvalue]]
    rw [B.zeroCoordinates_evenVertex i]
    simp only [Finset.mem_sdiff, Finset.mem_insert, hcurrent, false_or]

theorem twoCoordinates_oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    twoCoordinates (B.oddVertex i hi) =
      twoCoordinates B.start ∪ B.initialSegment i := by
  ext q
  by_cases hcurrent : q = B.coordinate ⟨i, hi⟩
  · subst q
    have hnot := B.coordinate_not_mem_initialSegment i hi
    have hstart := B.start_coordinate ⟨i, hi⟩
    have hvalue : B.oddVertex i hi (B.coordinate ⟨i, hi⟩) = 1 := by
      rw [oddVertex, if_pos rfl]
    simp only [twoCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, hvalue, hnot, or_false, hstart]
    constructor <;> intro h
    · have hval := congrArg Fin.val h
      norm_num at hval
    · have hval := congrArg Fin.val h
      norm_num at hval
  · have hvalue : B.oddVertex i hi q = B.evenVertex i q := by
      rw [oddVertex, if_neg hcurrent]
    rw [show q ∈ twoCoordinates (B.oddVertex i hi) ↔
        q ∈ twoCoordinates (B.evenVertex i) by
      simp only [twoCoordinates, Finset.mem_filter, Finset.mem_univ, true_and, hvalue]]
    exact Finset.ext_iff.mp (B.twoCoordinates_evenVertex i) q

theorem zeroCount_oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    zeroCount (B.oddVertex i hi) = zeroCount B.start - (i + 1) := by
  change (zeroCoordinates (B.oddVertex i hi)).card =
    (zeroCoordinates B.start).card - (i + 1)
  rw [B.zeroCoordinates_oddVertex i hi, Finset.card_sdiff_of_subset]
  · rw [Finset.card_insert_of_notMem (B.coordinate_not_mem_initialSegment i hi),
      B.card_initialSegment (Nat.le_of_lt hi)]
  · intro q hq
    simp only [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · simpa [zeroCoordinates] using B.start_coordinate ⟨i, hi⟩
    · exact B.initialSegment_subset_zeroCoordinates i hq

theorem twoCount_oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    twoCount (B.oddVertex i hi) = twoCount B.start + i := by
  change (twoCoordinates (B.oddVertex i hi)).card = (twoCoordinates B.start).card + i
  rw [B.twoCoordinates_oddVertex i hi, Finset.card_union_of_disjoint,
    B.card_initialSegment (Nat.le_of_lt hi)]
  exact Finset.disjoint_of_subset_right (B.initialSegment_subset_zeroCoordinates i)
    (disjoint_zeroCoordinates_twoCoordinates B.start).symm

theorem oneCount_oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    oneCount (B.oddVertex i hi) = oneCount B.start + 1 := by
  have hstart := zeroCount_add_oneCount_add_twoCount B.start
  have hodd := zeroCount_add_oneCount_add_twoCount (B.oddVertex i hi)
  rw [B.zeroCount_oddVertex i hi, B.twoCount_oddVertex i hi] at hodd
  have hzero : i + 1 ≤ zeroCount B.start := by
    have hsubset := B.initialSegment_subset_zeroCoordinates (i + 1)
    have hcard := Finset.card_le_card hsubset
    rw [B.card_initialSegment (Nat.succ_le_iff.mpr hi)] at hcard
    exact hcard
  omega

theorem type_oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    TypeCounts.ofVertex (B.oddVertex i hi) =
      (TypeCounts.ofVertex B.start).oddStep i (by
        simpa only [TypeCounts.ofVertex] using
          (show i < zeroCount B.start from by
            change i < (zeroCoordinates B.start).card
            have hsubset := B.initialSegment_subset_zeroCoordinates (i + 1)
            have hcard := Finset.card_le_card hsubset
            rw [B.card_initialSegment (Nat.succ_le_iff.mpr hi)] at hcard
            exact Nat.lt_of_succ_le hcard)) := by
  apply TypeCounts.ext
  · exact B.zeroCount_oddVertex i hi
  · exact B.oneCount_oddVertex i hi
  · exact B.twoCount_oddVertex i hi

theorem reachedTwo_even_iff (B : BasicChain n) (i : ℕ) (q : Fin n) :
    B.reachedTwo (2 * i) q ↔ q ∈ B.initialSegment i := by
  constructor
  · rintro ⟨j, rfl, hj⟩
    rw [mem_initialSegment_iff]
    exact ⟨j, by omega, rfl⟩
  · rw [mem_initialSegment_iff]
    rintro ⟨j, hj, rfl⟩
    exact ⟨j, rfl, by omega⟩

theorem reachedTwo_odd_iff (B : BasicChain n) (i : ℕ) (q : Fin n) :
    B.reachedTwo (2 * i + 1) q ↔ q ∈ B.initialSegment i := by
  constructor
  · rintro ⟨j, rfl, hj⟩
    rw [mem_initialSegment_iff]
    exact ⟨j, by omega, rfl⟩
  · rw [mem_initialSegment_iff]
    rintro ⟨j, hj, rfl⟩
    exact ⟨j, rfl, by omega⟩

theorem reachedOne_odd_iff (B : BasicChain n) (i : ℕ) (hi : i < B.width) (q : Fin n) :
    B.reachedOne (2 * i + 1) q ↔
      q ∈ B.initialSegment i ∨ q = B.coordinate ⟨i, hi⟩ := by
  constructor
  · rintro ⟨j, rfl, hj⟩
    by_cases hji : (j : ℕ) < i
    · exact Or.inl ((B.mem_initialSegment_iff i _).mpr ⟨j, hji, rfl⟩)
    · right
      have hij : i ≤ (j : ℕ) := Nat.le_of_not_gt hji
      have hji' : (j : ℕ) ≤ i := by omega
      apply congrArg B.coordinate
      apply Fin.ext
      exact Nat.le_antisymm hji' hij
  · rintro (hprefix | rfl)
    · rw [mem_initialSegment_iff] at hprefix
      rcases hprefix with ⟨j, hj, rfl⟩
      exact ⟨j, rfl, by omega⟩
    · exact ⟨⟨i, hi⟩, rfl, le_rfl⟩

theorem vertexAt_even (B : BasicChain n) (i : ℕ) :
    B.vertexAt (2 * i) = B.evenVertex i := by
  funext q
  by_cases hp : q ∈ B.initialSegment i
  · simp [vertexAt, evenVertex, hp, (B.reachedTwo_even_iff i q).mpr hp]
  · have hn2 : ¬B.reachedTwo (2 * i) q := (B.reachedTwo_even_iff i q).not.mpr hp
    have hn1 : ¬B.reachedOne (2 * i) q := by
      intro h1
      rcases h1 with ⟨j, hj, ht⟩
      apply hn2
      exact ⟨j, hj, by omega⟩
    simp [vertexAt, evenVertex, hp, hn2, hn1]

theorem vertexAt_odd (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    B.vertexAt (2 * i + 1) = B.oddVertex i hi := by
  funext q
  by_cases hp : q ∈ B.initialSegment i
  · have h2 := (B.reachedTwo_odd_iff i q).mpr hp
    have hne : q ≠ B.coordinate ⟨i, hi⟩ := by
      intro hq
      rw [mem_initialSegment_iff] at hp
      rcases hp with ⟨j, hj, hjq⟩
      have : j = ⟨i, hi⟩ := B.coordinate.injective (hjq.trans hq)
      have hji : (j : ℕ) = i := congrArg Fin.val this
      omega
    simp [vertexAt, oddVertex, evenVertex, hp, h2, hne]
  · have hn2 : ¬B.reachedTwo (2 * i + 1) q := (B.reachedTwo_odd_iff i q).not.mpr hp
    by_cases hq : q = B.coordinate ⟨i, hi⟩
    · have h1 := (B.reachedOne_odd_iff i hi q).mpr (Or.inr hq)
      subst q
      simp [vertexAt, hn2, h1, oddVertex]
    · have hn1 : ¬B.reachedOne (2 * i + 1) q := by
        rw [B.reachedOne_odd_iff i hi q]
        exact not_or_intro hp hq
      simp [vertexAt, oddVertex, evenVertex, hp, hn2, hn1, hq]

theorem rank_evenVertex (B : BasicChain n) (i : ℕ) (hi : i ≤ B.width) :
    Cube.rank (B.evenVertex i) = Cube.rank B.start + 2 * i := by
  calc
    Cube.rank (B.evenVertex i) = (TypeCounts.ofVertex (B.evenVertex i)).rank :=
      (TypeCounts.rank_ofVertex (B.evenVertex i)).symm
    _ = ((TypeCounts.ofVertex B.start).evenStep i _).rank := by
      rw [B.type_evenVertex i hi]
    _ = (TypeCounts.ofVertex B.start).rank + 2 * i :=
      TypeCounts.evenStep_rank (TypeCounts.ofVertex B.start) i _
    _ = Cube.rank B.start + 2 * i := by rw [TypeCounts.rank_ofVertex]

theorem rank_oddVertex (B : BasicChain n) (i : ℕ) (hi : i < B.width) :
    Cube.rank (B.oddVertex i hi) = Cube.rank B.start + (2 * i + 1) := by
  calc
    Cube.rank (B.oddVertex i hi) = (TypeCounts.ofVertex (B.oddVertex i hi)).rank :=
      (TypeCounts.rank_ofVertex (B.oddVertex i hi)).symm
    _ = ((TypeCounts.ofVertex B.start).oddStep i _).rank := by
      rw [B.type_oddVertex i hi]
    _ = (TypeCounts.ofVertex B.start).rank + (2 * i + 1) :=
      TypeCounts.oddStep_rank (TypeCounts.ofVertex B.start) i _
    _ = Cube.rank B.start + (2 * i + 1) := by rw [TypeCounts.rank_ofVertex]

/-- At every time represented by the descriptor, the rank has increased by
exactly the time parameter. -/
theorem rank_vertexAt (B : BasicChain n) (t : ℕ) (ht : t ≤ 2 * B.width) :
    Cube.rank (B.vertexAt t) = Cube.rank B.start + t := by
  obtain ⟨i, hit | hit⟩ := Nat.even_or_odd' t
  · subst t
    have hi : i ≤ B.width := by omega
    rw [B.vertexAt_even i, B.rank_evenVertex i hi]
  · subst t
    have hi : i < B.width := by omega
    rw [B.vertexAt_odd i hi, B.rank_oddVertex i hi]

@[simp]
theorem toChain_steps (B : BasicChain n) : B.toChain.steps = 2 * B.width := rfl

@[simp]
theorem toChain_length (B : BasicChain n) : B.toChain.length = 2 * B.width + 1 := rfl

@[simp]
theorem toChain_first (B : BasicChain n) : B.toChain.first = B.start := by
  rw [Chain.first, show B.toChain.vertex 0 = B.vertexAt 0 from rfl,
    B.vertexAt_even 0]
  funext q
  simp [evenVertex, initialSegment]

@[simp]
theorem toChain_last (B : BasicChain n) :
    B.toChain.last = B.evenVertex B.width := by
  change B.vertexAt (2 * B.width) = B.evenVertex B.width
  exact B.vertexAt_even B.width

/-- Every represented basic chain is saturated: it makes one rank-one move
at each of its `2 * width` steps. -/
theorem toChain_saturated (B : BasicChain n) : B.toChain.Saturated := by
  intro i
  have hi : (i : ℕ) < 2 * B.width := by
    simpa only [B.toChain_steps] using i.isLt
  change Cube.rank (B.vertexAt i.castSucc) + 1 = Cube.rank (B.vertexAt i.succ)
  rw [B.rank_vertexAt i.castSucc (by
      simpa only [Fin.val_castSucc] using Nat.le_of_lt hi),
    B.rank_vertexAt i.succ (by
      simpa only [Fin.val_succ, Nat.succ_le_iff] using hi)]
  simp only [Fin.val_castSucc, Fin.val_succ]
  omega

theorem differingCoordinates_start_evenVertex (B : BasicChain n) (i : ℕ) :
    Cube.differingCoordinates B.start (B.evenVertex i) = B.initialSegment i := by
  ext q
  by_cases hq : q ∈ B.initialSegment i
  · have hzero : B.start q = 0 := by
      rcases (B.mem_initialSegment_iff i q).mp hq with ⟨j, _hj, heq⟩
      rw [← heq]
      exact B.start_coordinate j
    have hvalue : B.evenVertex i q = 2 := by rw [evenVertex, if_pos hq]
    simp only [Cube.differingCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      hvalue, hq, iff_true]
    intro heq
    have hval := congrArg Fin.val (hzero.symm.trans heq)
    norm_num at hval
  · have hvalue : B.evenVertex i q = B.start q := by rw [evenVertex, if_neg hq]
    simp only [Cube.differingCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      hvalue, hq, iff_false]
    exact not_ne_iff.mpr rfl

theorem hammingDistance_start_evenVertex (B : BasicChain n) (i : ℕ)
    (hi : i ≤ B.width) :
    Cube.hammingDistance B.start (B.evenVertex i) = i := by
  rw [Cube.hammingDistance, B.differingCoordinates_start_evenVertex i,
    B.card_initialSegment hi]

@[simp]
theorem toChain_width (B : BasicChain n) : B.toChain.width = B.width := by
  rw [Chain.width, B.toChain_first, B.toChain_last,
    B.hammingDistance_start_evenVertex B.width le_rfl]

@[simp]
theorem rank_toChain_first (B : BasicChain n) :
    Cube.rank B.toChain.first = Cube.rank B.start := by rw [B.toChain_first]

@[simp]
theorem rank_toChain_last (B : BasicChain n) :
    Cube.rank B.toChain.last = Cube.rank B.start + 2 * B.width := by
  rw [B.toChain_last, B.rank_evenVertex B.width le_rfl]

/-- A basic chain is symmetric precisely when the selected coordinates
account for the excess of zeros over twos in its initial type. -/
theorem toChain_symmetric_iff (B : BasicChain n) :
    B.toChain.Symmetric ↔ zeroCount B.start = twoCount B.start + B.width := by
  rw [Chain.symmetric_iff_endpoint B.toChain B.toChain_saturated,
    B.rank_toChain_first, B.rank_toChain_last]
  have htype := rank_add_zeroCount B.start
  omega

/-- Exact descriptor-level characterization of the good basic chains from
Section 5. -/
theorem toChain_good_iff (B : BasicChain n) (k : ℕ) :
    B.toChain.Good k ↔
      B.width ≤ k ∧
        (zeroCount B.start = twoCount B.start + B.width ∨ B.width = k) := by
  rw [Chain.Good, B.toChain_width, B.toChain_symmetric_iff, B.toChain_length]
  simp only [B.toChain_saturated, true_and]
  constructor
  · rintro ⟨hwidth, hsym | hlength⟩
    · exact ⟨hwidth, Or.inl hsym⟩
    · exact ⟨hwidth, Or.inr (by omega)⟩
  · rintro ⟨hwidth, hsym | hwidthEq⟩
    · exact ⟨hwidth, Or.inl hsym⟩
    · exact ⟨hwidth, Or.inr (by omega)⟩

theorem width_le_zeroCount (B : BasicChain n) : B.width ≤ zeroCount B.start := by
  change (B.width : ℕ) ≤ (zeroCoordinates B.start).card
  rw [← B.card_initialSegment le_rfl]
  exact Finset.card_le_card (B.initialSegment_subset_zeroCoordinates B.width)

theorem type_toChain_last (B : BasicChain n) :
    TypeCounts.ofVertex B.toChain.last =
      (TypeCounts.ofVertex B.start).evenStep B.width (by
        simpa only [TypeCounts.ofVertex] using B.width_le_zeroCount) := by
  rw [B.toChain_last]
  exact B.type_evenVertex B.width le_rfl

/-- In the symmetric case the terminal type is obtained by interchanging
the zero and two entries of the initial type. -/
theorem type_toChain_last_eq_reflect (B : BasicChain n)
    (hsymmetric : B.toChain.Symmetric) :
    TypeCounts.ofVertex B.toChain.last = (TypeCounts.ofVertex B.start).reflect := by
  rw [B.type_toChain_last]
  have hwidth := B.toChain_symmetric_iff.mp hsymmetric
  apply TypeCounts.ext <;>
    simp only [TypeCounts.evenStep, TypeCounts.reflect, TypeCounts.ofVertex] <;>
    omega

end BasicChain

/-- Relabel the coordinates of a ternary vertex by a permutation. -/
def permuteVertex {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Cube n 2) : Cube n 2 :=
  fun q ↦ x (e.symm q)

@[simp]
theorem permuteVertex_apply {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Cube n 2)
    (q : Fin n) : permuteVertex e x (e q) = x q := by
  simp [permuteVertex]

theorem zeroCoordinates_permuteVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : Cube n 2) :
    zeroCoordinates (permuteVertex e x) = (zeroCoordinates x).image e := by
  ext q
  constructor
  · intro hq
    rw [zeroCoordinates] at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [Finset.mem_image]
    exact ⟨e.symm q, by
      simp only [zeroCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hq, e.apply_symm_apply q⟩
  · rw [Finset.mem_image]
    rintro ⟨p, hp, rfl⟩
    simp only [zeroCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simpa [permuteVertex] using hp

theorem twoCoordinates_permuteVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : Cube n 2) :
    twoCoordinates (permuteVertex e x) = (twoCoordinates x).image e := by
  ext q
  constructor
  · intro hq
    rw [twoCoordinates] at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [Finset.mem_image]
    exact ⟨e.symm q, by
      simp only [twoCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hq, e.apply_symm_apply q⟩
  · rw [Finset.mem_image]
    rintro ⟨p, hp, rfl⟩
    simp only [twoCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simpa [permuteVertex] using hp

@[simp]
theorem zeroCount_permuteVertex {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Cube n 2) :
    zeroCount (permuteVertex e x) = zeroCount x := by
  change (zeroCoordinates (permuteVertex e x)).card = (zeroCoordinates x).card
  rw [zeroCoordinates_permuteVertex, Finset.card_image_of_injective _ e.injective]

@[simp]
theorem twoCount_permuteVertex {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Cube n 2) :
    twoCount (permuteVertex e x) = twoCount x := by
  change (twoCoordinates (permuteVertex e x)).card = (twoCoordinates x).card
  rw [twoCoordinates_permuteVertex, Finset.card_image_of_injective _ e.injective]

namespace BasicChain

variable {n : ℕ}

/-- Coordinate permutations act on basic-chain descriptors by relabeling
their initial vertex and every selected coordinate. -/
def reindex (B : BasicChain n) (e : Equiv.Perm (Fin n)) : BasicChain n where
  width := B.width
  start := permuteVertex e B.start
  coordinate :=
    ⟨fun i ↦ e (B.coordinate i), fun {_i _j} hij ↦
      B.coordinate.injective (e.injective hij)⟩
  start_coordinate := by
    intro i
    change B.start (e.symm (e (B.coordinate i))) = 0
    rw [e.symm_apply_apply]
    exact B.start_coordinate i

@[simp]
theorem reindex_width (B : BasicChain n) (e : Equiv.Perm (Fin n)) :
    (B.reindex e).width = B.width := rfl

@[simp]
theorem reindex_start (B : BasicChain n) (e : Equiv.Perm (Fin n)) :
    (B.reindex e).start = permuteVertex e B.start := rfl

@[simp]
theorem reindex_coordinate (B : BasicChain n) (e : Equiv.Perm (Fin n))
    (i : Fin B.width) :
    (B.reindex e).coordinate i = e (B.coordinate i) := rfl

@[simp]
theorem reachedTwo_reindex_apply (B : BasicChain n) (e : Equiv.Perm (Fin n))
    (t : ℕ) (q : Fin n) :
    (B.reindex e).reachedTwo t (e q) ↔ B.reachedTwo t q := by
  constructor
  · rintro ⟨j, hj, ht⟩
    refine ⟨j, ?_, ht⟩
    change e (B.coordinate j) = e q at hj
    exact e.injective hj
  · rintro ⟨j, hj, ht⟩
    refine ⟨j, ?_, ht⟩
    change e (B.coordinate j) = e q
    exact congrArg e hj

@[simp]
theorem reachedOne_reindex_apply (B : BasicChain n) (e : Equiv.Perm (Fin n))
    (t : ℕ) (q : Fin n) :
    (B.reindex e).reachedOne t (e q) ↔ B.reachedOne t q := by
  constructor
  · rintro ⟨j, hj, ht⟩
    refine ⟨j, ?_, ht⟩
    change e (B.coordinate j) = e q at hj
    exact e.injective hj
  · rintro ⟨j, hj, ht⟩
    refine ⟨j, ?_, ht⟩
    change e (B.coordinate j) = e q
    exact congrArg e hj

/-- Relabeling a descriptor relabels every vertex of its chain at the same
time parameter. -/
theorem vertexAt_reindex_apply (B : BasicChain n) (e : Equiv.Perm (Fin n))
    (t : ℕ) (q : Fin n) :
    (B.reindex e).vertexAt t (e q) = B.vertexAt t q := by
  by_cases htwo : B.reachedTwo t q
  · have htwo' : (B.reindex e).reachedTwo t (e q) :=
      (B.reachedTwo_reindex_apply e t q).mpr htwo
    simp [vertexAt, htwo, htwo']
  · have htwo' : ¬(B.reindex e).reachedTwo t (e q) := by
      rw [B.reachedTwo_reindex_apply e t q]
      exact htwo
    by_cases hone : B.reachedOne t q
    · have hone' : (B.reindex e).reachedOne t (e q) :=
        (B.reachedOne_reindex_apply e t q).mpr hone
      simp [vertexAt, htwo, htwo', hone, hone']
    · have hone' : ¬(B.reindex e).reachedOne t (e q) := by
        rw [B.reachedOne_reindex_apply e t q]
        exact hone
      simp [vertexAt, htwo, htwo', hone, hone', permuteVertex]

theorem vertexAt_reindex (B : BasicChain n) (e : Equiv.Perm (Fin n)) (t : ℕ) :
    (B.reindex e).vertexAt t = permuteVertex e (B.vertexAt t) := by
  funext q
  simpa [permuteVertex] using B.vertexAt_reindex_apply e t (e.symm q)

@[simp]
theorem reindex_symm_reindex (B : BasicChain n) (e : Equiv.Perm (Fin n)) :
    (B.reindex e).reindex e.symm = B := by
  apply BasicChain.ext
  · rfl
  · funext q
    simp [reindex, permuteVertex]
  · apply heq_of_eq
    apply DFunLike.ext _ _
    intro i
    change e.symm (e (B.coordinate i)) = B.coordinate i
    exact e.symm_apply_apply (B.coordinate i)

/-- Relabeling by a coordinate permutation is an equivalence of the finite
type of basic-chain descriptors. -/
def reindexEquiv (e : Equiv.Perm (Fin n)) : BasicChain n ≃ BasicChain n where
  toFun B := B.reindex e
  invFun B := B.reindex e.symm
  left_inv B := B.reindex_symm_reindex e
  right_inv B := B.reindex_symm_reindex e.symm

theorem toChain_good_reindex_iff (B : BasicChain n) (e : Equiv.Perm (Fin n)) (k : ℕ) :
    (B.reindex e).toChain.Good k ↔ B.toChain.Good k := by
  rw [(B.reindex e).toChain_good_iff k, B.toChain_good_iff]
  simp only [reindex_width, reindex_start, zeroCount_permuteVertex,
    twoCount_permuteVertex]

end BasicChain

end Ternary

end WeightedChains
