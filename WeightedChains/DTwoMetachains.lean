import WeightedChains.DTwoChainExistence

/-!
# Ternary metachains

Section 5 groups together basic chains of a fixed width whose initial vertices
have the same type.  The results below justify that grouping: at each time all
such chains pass through the same ternary type.  We also isolate the exceptional
singleton chain through `(1, ..., 1)`.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary

/-- The distinguished middle vertex `(1, ..., 1)`. -/
def middleVertex (n : ℕ) : Cube n 2 := fun _ ↦ 1

@[simp]
theorem middleVertex_apply (n : ℕ) (i : Fin n) : middleVertex n i = 1 := rfl

@[simp]
theorem zeroCount_middleVertex (n : ℕ) : zeroCount (middleVertex n) = 0 := by
  simp [zeroCount, Cube.typeOf, middleVertex]

@[simp]
theorem oneCount_middleVertex (n : ℕ) : oneCount (middleVertex n) = n := by
  simp [oneCount, Cube.typeOf, middleVertex]

@[simp]
theorem twoCount_middleVertex (n : ℕ) : twoCount (middleVertex n) = 0 := by
  simp [twoCount, Cube.typeOf, middleVertex]

namespace BasicChain

variable {n : ℕ}

/-- Equality of zero and two counts is enough to identify a ternary type. -/
theorem typeCounts_eq_of_zeroCount_eq_twoCount_eq {x y : Cube n 2}
    (hzero : zeroCount x = zeroCount y) (htwo : twoCount x = twoCount y) :
    TypeCounts.ofVertex x = TypeCounts.ofVertex y := by
  apply TypeCounts.ext
  · exact hzero
  · have hx := zeroCount_add_oneCount_add_twoCount x
    have hy := zeroCount_add_oneCount_add_twoCount y
    change oneCount x = oneCount y
    omega
  · exact htwo

/-- Basic chains of the same width and initial type pass through the same type
at every common time.  This is the precise descriptor-level form of the
paper's metachain observation. -/
theorem type_vertexAt_eq_of_same_start_type (B C : BasicChain n)
    (hwidth : B.width = C.width)
    (hzero : zeroCount B.start = zeroCount C.start)
    (htwo : twoCount B.start = twoCount C.start)
    (t : ℕ) (ht : t ≤ 2 * B.width) :
    TypeCounts.ofVertex (B.vertexAt t) = TypeCounts.ofVertex (C.vertexAt t) := by
  obtain ⟨i, hit | hit⟩ := Nat.even_or_odd' t
  · subst t
    have hiB : i ≤ B.width := by omega
    have hiC : i ≤ C.width := by omega
    rw [B.vertexAt_even, C.vertexAt_even]
    apply typeCounts_eq_of_zeroCount_eq_twoCount_eq
    · rw [B.zeroCount_evenVertex i hiB, C.zeroCount_evenVertex i hiC, hzero]
    · rw [B.twoCount_evenVertex i hiB, C.twoCount_evenVertex i hiC, htwo]
  · subst t
    have hiB : i < B.width := by omega
    have hiC : i < C.width := by omega
    rw [B.vertexAt_odd i hiB, C.vertexAt_odd i hiC]
    apply typeCounts_eq_of_zeroCount_eq_twoCount_eq
    · rw [B.zeroCount_oddVertex i hiB, C.zeroCount_oddVertex i hiC, hzero]
    · rw [B.twoCount_oddVertex i hiB, C.twoCount_oddVertex i hiC, htwo]

/-- Reindexing transports incidence in the represented chain. -/
theorem mem_vertices_reindex_iff (B : BasicChain n) (e : Equiv.Perm (Fin n))
    (x : Cube n 2) :
    permuteVertex e x ∈ (B.reindex e).toChain.vertices ↔
      x ∈ B.toChain.vertices := by
  rw [Chain.mem_vertices_iff, Chain.mem_vertices_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, (show Function.Injective (permuteVertex e) from ?_) ?_⟩
    · intro u v huv
      funext q
      have h := congrFun huv (e q)
      simpa using h
    · exact (B.vertexAt_reindex e i).symm.trans hi
  · rintro ⟨i, hi⟩
    refine ⟨i, (B.vertexAt_reindex e i).trans ?_⟩
    exact congrArg (permuteVertex e) hi

/-- Basic good chains in the metachain starting at type `(a,n-a-c,c)` which
pass through a specified vertex. -/
def goodChainsStartingAtTypeThrough (n k a c : ℕ) (x : Cube n 2) :
    Finset (BasicChain n) :=
  Finset.univ.filter fun B ↦
    B.width ≤ k ∧
      (zeroCount B.start = twoCount B.start + B.width ∨ B.width = k) ∧
        zeroCount B.start = a ∧ twoCount B.start = c ∧ x ∈ B.toChain.vertices

@[simp]
theorem mem_goodChainsStartingAtTypeThrough_iff
    (B : BasicChain n) (k a c : ℕ) (x : Cube n 2) :
    B ∈ goodChainsStartingAtTypeThrough n k a c x ↔
      B.toChain.Good k ∧ zeroCount B.start = a ∧ twoCount B.start = c ∧
        x ∈ B.toChain.vertices := by
  rw [goodChainsStartingAtTypeThrough, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, B.toChain_good_iff]
  tauto

/-- Within a fixed ternary type, metachain incidence is uniform.  This is the
finite symmetry statement needed to pass from total type weight to weight one
at each individual vertex. -/
theorem card_goodChainsStartingAtTypeThrough_eq_of_same_type
    (n k a c : ℕ) {x y : Cube n 2}
    (hzero : zeroCount x = zeroCount y) (htwo : twoCount x = twoCount y) :
    (goodChainsStartingAtTypeThrough n k a c x).card =
      (goodChainsStartingAtTypeThrough n k a c y).card := by
  obtain ⟨e, he⟩ := exists_coordinatePermutation_of_same_type hzero htwo
  have hexy : permuteVertex e x = y := by
    funext q
    obtain ⟨i, rfl⟩ := e.surjective q
    rw [permuteVertex_apply]
    exact (he i).symm
  apply Finset.card_equiv (reindexEquiv e)
  intro B
  rw [mem_goodChainsStartingAtTypeThrough_iff,
    mem_goodChainsStartingAtTypeThrough_iff]
  have hvertices := B.mem_vertices_reindex_iff e x
  rw [hexy] at hvertices
  constructor
  · rintro ⟨hgood, hstartZero, hstartTwo, hmem⟩
    exact ⟨(B.toChain_good_reindex_iff e k).mpr hgood,
      by simpa [reindexEquiv] using hstartZero,
      by simpa [reindexEquiv] using hstartTwo, hvertices.mpr hmem⟩
  · rintro ⟨hgood, hstartZero, hstartTwo, hmem⟩
    exact ⟨(B.toChain_good_reindex_iff e k).mp hgood,
      by simpa [reindexEquiv] using hstartZero,
      by simpa [reindexEquiv] using hstartTwo, hvertices.mp hmem⟩

/-- The canonical zero-width basic chain at `(1, ..., 1)`. -/
def middleSingleton (n : ℕ) : BasicChain n :=
  ofStartWidth (middleVertex n) 0 (by simp)

@[simp]
theorem middleSingleton_start (n : ℕ) :
    (middleSingleton n).start = middleVertex n := rfl

@[simp]
theorem middleSingleton_width (n : ℕ) :
    ((middleSingleton n).width : ℕ) = 0 := rfl

@[simp]
theorem middleSingleton_length (n : ℕ) :
    (middleSingleton n).toChain.length = 1 := by
  simp [middleSingleton]

theorem middleSingleton_good (n k : ℕ) :
    (middleSingleton n).toChain.Good k := by
  rw [(middleSingleton n).toChain_good_iff]
  simp [middleSingleton]

/-- Any basic chain starting at `(1, ..., 1)` has width zero, so the
exceptional singleton is forced rather than merely chosen. -/
theorem width_eq_zero_of_start_eq_middleVertex (B : BasicChain n)
    (hstart : B.start = middleVertex n) : (B.width : ℕ) = 0 := by
  have hwidth := B.width_le_zeroCount
  rw [hstart, zeroCount_middleVertex] at hwidth
  omega

theorem length_eq_one_of_start_eq_middleVertex (B : BasicChain n)
    (hstart : B.start = middleVertex n) : B.toChain.length = 1 := by
  rw [B.toChain_length, width_eq_zero_of_start_eq_middleVertex B hstart]

end BasicChain
end Ternary
end WeightedChains
