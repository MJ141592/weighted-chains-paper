import WeightedChains.DOneChains
import WeightedChains.DOneLayers

/-!
# Rank incidence of represented Boolean chains

A represented saturated Boolean chain contains one vertex at every rank
between its endpoint ranks, and no vertices at other ranks.  This supplies the
finite layer-intersection formula used when summing individual chain weights.
-/

set_option autoImplicit false

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n : ℕ}

theorem exists_vertex_rank_iff (C : BooleanChain n) (a : ℕ) :
    (∃ i, Cube.rank (C.vertex i) = a) ↔
      C.start.card ≤ a ∧ a ≤ C.start.card + C.steps := by
  constructor
  · rintro ⟨i, hi⟩
    rw [C.rank_vertex i] at hi
    omega
  · rintro ⟨hlower, hupper⟩
    have hi : a - C.start.card < C.steps + 1 := by omega
    let i : Fin (C.steps + 1) := ⟨a - C.start.card, hi⟩
    refine ⟨i, ?_⟩
    rw [C.rank_vertex i]
    change C.start.card + (a - C.start.card) = a
    omega

theorem booleanLayerFinset_inter_vertices_eq_singleton
    (C : BooleanChain n) (a : ℕ)
    (hlower : C.start.card ≤ a) (hupper : a ≤ C.start.card + C.steps) :
    booleanLayerFinset n a ∩ C.toChain.vertices =
      {C.vertex ⟨a - C.start.card, by omega⟩} := by
  let i : Fin (C.steps + 1) := ⟨a - C.start.card, by omega⟩
  change booleanLayerFinset n a ∩ C.toChain.vertices = {C.vertex i}
  ext x
  simp only [Finset.mem_inter, mem_booleanLayerFinset_iff,
    Chain.mem_vertices_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hxRank, j, rfl⟩
    apply congrArg C.vertex
    apply Fin.ext
    change Cube.rank (C.vertex j) = a at hxRank
    rw [C.rank_vertex j] at hxRank
    change (j : ℕ) = a - C.start.card
    omega
  · rintro rfl
    refine ⟨?_, i, rfl⟩
    rw [C.rank_vertex]
    change C.start.card + (a - C.start.card) = a
    omega

theorem booleanLayerFinset_inter_vertices_eq_empty
    (C : BooleanChain n) (a : ℕ)
    (houtside : ¬(C.start.card ≤ a ∧ a ≤ C.start.card + C.steps)) :
    booleanLayerFinset n a ∩ C.toChain.vertices = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hxRank : Cube.rank x = a := mem_booleanLayerFinset_iff.mp (Finset.mem_inter.mp hx).1
  obtain ⟨i, rfl⟩ :=
    (Chain.mem_vertices_iff C.toChain x).mp (Finset.mem_inter.mp hx).2
  apply houtside
  rw [Chain.rank_vertex_eq C.toChain C.saturated_toChain i,
    C.rank_toChain_first] at hxRank
  have hi : (i : ℕ) < C.steps + 1 := by
    exact i.isLt
  omega

/-- A represented chain meets a rank layer exactly once precisely when the
rank lies in its endpoint interval. -/
theorem card_booleanLayerFinset_inter_vertices (C : BooleanChain n) (a : ℕ) :
    (booleanLayerFinset n a ∩ C.toChain.vertices).card =
      if C.start.card ≤ a ∧ a ≤ C.start.card + C.steps then 1 else 0 := by
  split_ifs with hinside
  · rw [C.booleanLayerFinset_inter_vertices_eq_singleton a hinside.1 hinside.2]
    simp
  · rw [C.booleanLayerFinset_inter_vertices_eq_empty a hinside]
    simp

end BooleanChain
end DOne
end WeightedChains
