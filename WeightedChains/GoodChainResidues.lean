import WeightedChains.Preliminaries

/-!
# Residue representatives on good chains

The proof strategy uses the fact that every good chain contains exactly one
point of each of the paper's two distinguished rank-residue families.  This
file proves that assertion for every alphabet bound `d`.
-/

namespace WeightedChains

namespace Cube

/-- Finite version of the paper's lower residue family. -/
def lowerResidueFinset (n d k : ℕ) : Finset (Cube n d) :=
  Finset.univ.filter fun x ↦ rank x ≡ lowerMiddleRank n d [MOD d * k + 1]

/-- Finite version of the paper's upper residue family. -/
def upperResidueFinset (n d k : ℕ) : Finset (Cube n d) :=
  Finset.univ.filter fun x ↦ rank x ≡ upperMiddleRank n d [MOD d * k + 1]

@[simp]
theorem mem_lowerResidueFinset_iff {n d k : ℕ} {x : Cube n d} :
    x ∈ lowerResidueFinset n d k ↔ x ∈ lowerResidueFamily n d k := by
  simp [lowerResidueFinset, lowerResidueFamily, residueFamily]

@[simp]
theorem mem_upperResidueFinset_iff {n d k : ℕ} {x : Cube n d} :
    x ∈ upperResidueFinset n d k ↔ x ∈ upperResidueFamily n d k := by
  simp [upperResidueFinset, upperResidueFamily, residueFamily]

end Cube

namespace Chain

variable {n d k : ℕ}

/-- Among `M` consecutive natural numbers there is an offset below `M` which
has any prescribed residue modulo `M`. -/
private theorem exists_offset_modEq (start target M : ℕ) (hM : 0 < M) :
    ∃ i < M, start + i ≡ target [MOD M] := by
  let q := start % M
  let r := target % M
  refine ⟨(r + M - q) % M, Nat.mod_lt _ hM, ?_⟩
  unfold Nat.ModEq
  have hq : q < M := Nat.mod_lt _ hM
  have hr : r < M := Nat.mod_lt _ hM
  by_cases hqr : q ≤ r
  · have hdelta : r - q < M := by omega
    have hinner : (r + M - q) % M = r - q := by
      rw [show r + M - q = (r - q) + M by omega]
      simp [Nat.mod_eq_of_lt hdelta]
    change (start + (r + M - q) % M) % M = r
    rw [hinner, Nat.add_mod]
    change (q + (r - q) % M) % M = r
    rw [Nat.mod_eq_of_lt hdelta, Nat.add_sub_of_le hqr, Nat.mod_eq_of_lt hr]
  · have hdelta : r + M - q < M := by omega
    have hinner : (r + M - q) % M = r + M - q := Nat.mod_eq_of_lt hdelta
    change (start + (r + M - q) % M) % M = r
    rw [hinner, Nat.add_mod]
    change (q + (r + M - q) % M) % M = r
    rw [Nat.mod_eq_of_lt hdelta]
    rw [show q + (r + M - q) = r + M by omega]
    simp [Nat.mod_eq_of_lt hr]

/-- A saturated chain whose length is exactly a modulus visits every residue
class of ranks modulo that modulus. -/
theorem exists_vertex_rank_modEq_of_length (C : Chain n d) (hsaturated : C.Saturated)
    (M target : ℕ) (hM : 0 < M) (hlength : C.length = M) :
    ∃ i, Cube.rank (C.vertex i) ≡ target [MOD M] := by
  obtain ⟨i, hiM, hi⟩ := exists_offset_modEq (Cube.rank C.first) target M hM
  have hibound : i < C.steps + 1 := by
    rw [← length, hlength]
    exact hiM
  refine ⟨⟨i, hibound⟩, ?_⟩
  rw [rank_vertex_eq C hsaturated]
  exact hi

/-- Every rank between the endpoints of a saturated chain occurs at a unique
step; only existence is needed here. -/
theorem exists_vertex_rank_eq_of_between (C : Chain n d) (hsaturated : C.Saturated)
    (r : ℕ) (hfirst : Cube.rank C.first ≤ r) (hlast : r ≤ Cube.rank C.last) :
    ∃ i, Cube.rank (C.vertex i) = r := by
  have hrange : r - Cube.rank C.first < C.steps + 1 := by
    rw [rank_last_eq C hsaturated] at hlast
    omega
  refine ⟨⟨r - Cube.rank C.first, hrange⟩, ?_⟩
  rw [rank_vertex_eq C hsaturated]
  change Cube.rank C.first + (r - Cube.rank C.first) = r
  omega

theorem exists_vertex_rank_eq_lowerMiddle_of_symmetric (C : Chain n d)
    (hsaturated : C.Saturated) (hsymmetric : C.Symmetric) :
    ∃ i, Cube.rank (C.vertex i) = Cube.lowerMiddleRank n d := by
  have hendpoints := (symmetric_iff_endpoint C hsaturated).mp hsymmetric
  have hrankOrder : Cube.rank C.first ≤ Cube.rank C.last :=
    Cube.rank_mono C.first_le_last
  apply exists_vertex_rank_eq_of_between C hsaturated
  · unfold Cube.lowerMiddleRank
    omega
  · unfold Cube.lowerMiddleRank
    omega

theorem exists_vertex_rank_eq_upperMiddle_of_symmetric (C : Chain n d)
    (hsaturated : C.Saturated) (hsymmetric : C.Symmetric) :
    ∃ i, Cube.rank (C.vertex i) = Cube.upperMiddleRank n d := by
  have hendpoints := (symmetric_iff_endpoint C hsaturated).mp hsymmetric
  have hrankOrder : Cube.rank C.first ≤ Cube.rank C.last :=
    Cube.rank_mono C.first_le_last
  apply exists_vertex_rank_eq_of_between C hsaturated
  · unfold Cube.upperMiddleRank Cube.lowerMiddleRank
    omega
  · unfold Cube.upperMiddleRank Cube.lowerMiddleRank
    omega

/-- Every good chain contains a vertex in the lower distinguished residue
family. -/
theorem Good.exists_mem_lowerResidueFinset (C : Chain n d) (hgood : C.Good k) :
    ∃ x ∈ C.vertices, x ∈ Cube.lowerResidueFinset n d k := by
  rcases hgood.2.2 with hsymmetric | hlength
  · obtain ⟨i, hi⟩ :=
      exists_vertex_rank_eq_lowerMiddle_of_symmetric C hgood.1 hsymmetric
    refine ⟨C.vertex i, (mem_vertices_iff C _).2 ⟨i, rfl⟩, ?_⟩
    simp only [Cube.lowerResidueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi ▸ Nat.ModEq.rfl
  · obtain ⟨i, hi⟩ := exists_vertex_rank_modEq_of_length C hgood.1
      (d * k + 1) (Cube.lowerMiddleRank n d) (by omega) hlength
    refine ⟨C.vertex i, (mem_vertices_iff C _).2 ⟨i, rfl⟩, ?_⟩
    simp only [Cube.lowerResidueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi

/-- Every good chain contains a vertex in the upper distinguished residue
family. -/
theorem Good.exists_mem_upperResidueFinset (C : Chain n d) (hgood : C.Good k) :
    ∃ x ∈ C.vertices, x ∈ Cube.upperResidueFinset n d k := by
  rcases hgood.2.2 with hsymmetric | hlength
  · obtain ⟨i, hi⟩ :=
      exists_vertex_rank_eq_upperMiddle_of_symmetric C hgood.1 hsymmetric
    refine ⟨C.vertex i, (mem_vertices_iff C _).2 ⟨i, rfl⟩, ?_⟩
    simp only [Cube.upperResidueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi ▸ Nat.ModEq.rfl
  · obtain ⟨i, hi⟩ := exists_vertex_rank_modEq_of_length C hgood.1
      (d * k + 1) (Cube.upperMiddleRank n d) (by omega) hlength
    refine ⟨C.vertex i, (mem_vertices_iff C _).2 ⟨i, rfl⟩, ?_⟩
    simp only [Cube.upperResidueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi

/-- A good chain contains exactly one point of the lower residue family. -/
theorem Good.card_lowerResidueFinset_inter_vertices (C : Chain n d) (hgood : C.Good k) :
    (Cube.lowerResidueFinset n d k ∩ C.vertices).card = 1 := by
  apply Nat.le_antisymm
  · apply card_inter_vertices_le_one C (Cube.lowerResidueFinset n d k) k
    · intro x y hx hy hxy hne
      exact Cube.lowerResidueFamily_kSeparated n d k
        (Cube.mem_lowerResidueFinset_iff.mp hx)
        (Cube.mem_lowerResidueFinset_iff.mp hy) hxy hne
    · exact hgood.2.1
  · rw [Finset.one_le_card]
    obtain ⟨x, hxC, hxA⟩ := hgood.exists_mem_lowerResidueFinset C
    exact ⟨x, Finset.mem_inter.mpr ⟨hxA, hxC⟩⟩

/-- A good chain contains exactly one point of the upper residue family. -/
theorem Good.card_upperResidueFinset_inter_vertices (C : Chain n d) (hgood : C.Good k) :
    (Cube.upperResidueFinset n d k ∩ C.vertices).card = 1 := by
  apply Nat.le_antisymm
  · apply card_inter_vertices_le_one C (Cube.upperResidueFinset n d k) k
    · intro x y hx hy hxy hne
      exact Cube.upperResidueFamily_kSeparated n d k
        (Cube.mem_upperResidueFinset_iff.mp hx)
        (Cube.mem_upperResidueFinset_iff.mp hy) hxy hne
    · exact hgood.2.1
  · rw [Finset.one_le_card]
    obtain ⟨x, hxC, hxA⟩ := hgood.exists_mem_upperResidueFinset C
    exact ⟨x, Finset.mem_inter.mpr ⟨hxA, hxC⟩⟩

end Chain
end WeightedChains
