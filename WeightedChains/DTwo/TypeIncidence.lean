import WeightedChains.DTwo.TypeWeights

/-!
# Incidence of basic chains with ternary types

A saturated chain meets a fixed ternary type at most once, since all vertices
of that type have the same rank.  This file records that fact and rewrites the
total induced weight on a type as a finite sum over the incident basic-chain
descriptors.  It is the double-counting bridge between metachain start totals
and the pointwise weighted cover in Section 5.
-/

open scoped BigOperators

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

/-- The vertex map of a basic-chain descriptor is injective. -/
theorem toChain_vertex_injective (B : BasicChain n) :
    Function.Injective B.toChain.vertex := by
  intro i j hij
  have hrank := congrArg Cube.rank hij
  rw [Chain.rank_vertex_eq B.toChain B.toChain_saturated i,
    Chain.rank_vertex_eq B.toChain B.toChain_saturated j] at hrank
  apply Fin.ext
  omega

/-- Two ternary vertices with the same zero and two counts have the same
rank. -/
theorem rank_eq_of_zeroCount_eq_twoCount_eq {x y : Cube n 2}
    (hzero : zeroCount x = zeroCount y)
    (htwo : twoCount x = twoCount y) :
    Cube.rank x = Cube.rank y := by
  have hx := rank_add_zeroCount x
  have hy := rank_add_zeroCount y
  omega

/-- A basic chain contains at most one vertex of any fixed ternary type. -/
theorem card_typeFiber_inter_vertices_le_one
    (B : BasicChain n) (a c : ℕ) :
    ((typeFiber n a c) ∩ B.toChain.vertices).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  obtain ⟨hxType, hxVertices⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyType, hyVertices⟩ := Finset.mem_inter.mp hy
  obtain ⟨hxZero, hxTwo⟩ := mem_typeFiber.mp hxType
  obtain ⟨hyZero, hyTwo⟩ := mem_typeFiber.mp hyType
  obtain ⟨i, hi⟩ := (Chain.mem_vertices_iff B.toChain x).mp hxVertices
  obtain ⟨j, hj⟩ := (Chain.mem_vertices_iff B.toChain y).mp hyVertices
  have hrank : Cube.rank (B.toChain.vertex i) =
      Cube.rank (B.toChain.vertex j) := by
    rw [hi, hj]
    exact rank_eq_of_zeroCount_eq_twoCount_eq
      (hxZero.trans hyZero.symm) (hxTwo.trans hyTwo.symm)
  have hij : i = j := by
    apply Fin.ext
    rw [Chain.rank_vertex_eq B.toChain B.toChain_saturated i,
      Chain.rank_vertex_eq B.toChain B.toChain_saturated j] at hrank
    omega
  rw [← hi, ← hj, hij]

/-- A basic chain visits a type when its vertex finset has nonempty
intersection with the corresponding type fiber. -/
def VisitsType (B : BasicChain n) (a c : ℕ) : Prop :=
  ((typeFiber n a c) ∩ B.toChain.vertices).Nonempty

instance decidableVisitsType (B : BasicChain n) (a c : ℕ) :
    Decidable (B.VisitsType a c) := by
  unfold VisitsType
  infer_instance

theorem visitsType_iff_exists_vertex (B : BasicChain n) (a c : ℕ) :
    B.VisitsType a c ↔
      ∃ i : Fin (B.toChain.steps + 1),
        zeroCount (B.toChain.vertex i) = a ∧
          twoCount (B.toChain.vertex i) = c := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hxType, hxVertices⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxZero, hxTwo⟩ := mem_typeFiber.mp hxType
    obtain ⟨i, hi⟩ := (Chain.mem_vertices_iff B.toChain x).mp hxVertices
    refine ⟨i, ?_, ?_⟩
    · simpa only [hi] using hxZero
    · simpa only [hi] using hxTwo
  · rintro ⟨i, hiZero, hiTwo⟩
    refine ⟨B.toChain.vertex i, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact mem_typeFiber.mpr ⟨hiZero, hiTwo⟩
    · exact (Chain.mem_vertices_iff B.toChain _).mpr ⟨i, rfl⟩

/-- Because incidence is at most one, visiting a type is equivalent to the
intersection cardinality being exactly one. -/
theorem card_typeFiber_inter_vertices_eq_one_iff
    (B : BasicChain n) (a c : ℕ) :
    ((typeFiber n a c) ∩ B.toChain.vertices).card = 1 ↔
      B.VisitsType a c := by
  constructor
  · intro hcard
    exact Finset.card_pos.mp (by omega)
  · intro hnonempty
    have hpositive : 0 < ((typeFiber n a c) ∩ B.toChain.vertices).card :=
      Finset.card_pos.mpr hnonempty
    have hle := card_typeFiber_inter_vertices_le_one B a c
    omega

/-- The incidence cardinality is the indicator of `VisitsType`. -/
theorem card_typeFiber_inter_vertices_eq_indicator
    (B : BasicChain n) (a c : ℕ) :
    ((typeFiber n a c) ∩ B.toChain.vertices).card =
      if B.VisitsType a c then 1 else 0 := by
  by_cases hvisit : B.VisitsType a c
  · rw [if_pos hvisit]
    exact (card_typeFiber_inter_vertices_eq_one_iff B a c).2 hvisit
  · rw [if_neg hvisit]
    exact Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hvisit)

/-- Double-count the total induced weight on a ternary type by basic-chain
descriptors. -/
theorem totalInducedWeightOnType_eq_sum_incidence
    (weight : BasicChain n → ℝ) (a c : ℕ) :
    totalInducedWeightOnType n a c weight =
      ∑ B : BasicChain n,
        weight B * (((typeFiber n a c) ∩ B.toChain.vertices).card : ℝ) := by
  exact WeightedCover.sum_inducedWeight
    (fun B : BasicChain n ↦ B.toChain.vertices) weight (typeFiber n a c)

/-- Indicator form of the same double count: only descriptors visiting the
target type contribute. -/
theorem totalInducedWeightOnType_eq_sum_if_visits
    (weight : BasicChain n → ℝ) (a c : ℕ) :
    totalInducedWeightOnType n a c weight =
      ∑ B : BasicChain n, if B.VisitsType a c then weight B else 0 := by
  rw [totalInducedWeightOnType_eq_sum_incidence]
  apply Finset.sum_congr rfl
  intro B _hB
  rw [card_typeFiber_inter_vertices_eq_indicator]
  by_cases hvisit : B.VisitsType a c <;> simp [hvisit]

end BasicChain
end Ternary
end WeightedChains
