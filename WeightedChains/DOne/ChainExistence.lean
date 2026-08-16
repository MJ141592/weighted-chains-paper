import WeightedChains.DOne.ChainReflection

/-!
# Existence of represented good Boolean chains

Every Boolean vertex starts a suitable chain toward the middle on the lower
side, and by reflection every upper vertex is the terminal endpoint of one.
These explicit descriptors are used by the equality-case propagation proof.
-/

noncomputable section

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n : ℕ}

/-- Coordinates which are still zero at `x` and may therefore be added to a
represented Boolean chain. -/
def availableCoordinates (x : Cube n 1) : Finset (Fin n) :=
  Finset.univ \ finsetOfCube x

@[simp]
theorem card_availableCoordinates (x : Cube n 1) :
    (availableCoordinates x).card = n - Cube.rank x := by
  rw [availableCoordinates, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, card_finsetOfCube]

/-- Enumerate `w` fresh coordinates of `x`. -/
def freshCoordinateEmbedding (x : Cube n 1) (w : ℕ)
    (hw : Cube.rank x + w ≤ n) : Fin w ↪ Fin n := by
  let available := availableCoordinates x
  have hw' : w ≤ available.card := by
    rw [show available.card = n - Cube.rank x by
      simp [available, card_availableCoordinates x]]
    omega
  let enumerate : Fin available.card ≃ ↑available :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe available)).symm
  exact (Fin.castLEEmb hw').trans
    (enumerate.toEmbedding.trans (Function.Embedding.subtype _))

@[simp]
theorem freshCoordinateEmbedding_mem (x : Cube n 1) (w : ℕ)
    (hw : Cube.rank x + w ≤ n) (i : Fin w) :
    freshCoordinateEmbedding x w hw i ∈ availableCoordinates x := by
  simp [freshCoordinateEmbedding]

/-- The represented saturated chain starting at `x` and adding `w` selected
zero coordinates. -/
def ofStartWidth (x : Cube n 1) (w : ℕ) (hw : Cube.rank x + w ≤ n) :
    BooleanChain n where
  steps := ⟨w, by omega⟩
  start := finsetOfCube x
  addition := freshCoordinateEmbedding x w hw
  fresh := by
    rw [Finset.disjoint_left]
    intro q hqStart hqImage
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hqImage
    have havailable := freshCoordinateEmbedding_mem x w hw i
    exact (Finset.mem_sdiff.mp havailable).2 hqStart

@[simp]
theorem ofStartWidth_steps (x : Cube n 1) (w : ℕ)
    (hw : Cube.rank x + w ≤ n) : (ofStartWidth x w hw).steps = w := rfl

@[simp]
theorem ofStartWidth_start (x : Cube n 1) (w : ℕ)
    (hw : Cube.rank x + w ≤ n) :
    (ofStartWidth x w hw).start = finsetOfCube x := rfl

@[simp]
theorem ofStartWidth_first (x : Cube n 1) (w : ℕ)
    (hw : Cube.rank x + w ≤ n) :
    (ofStartWidth x w hw).toChain.first = x := by
  rw [(ofStartWidth x w hw).toChain_first, ofStartWidth_start,
    cubeOfFinset_finsetOfCube]

/-- Every lower-half Boolean vertex is the first endpoint of a represented
good chain directed toward the middle.  Outer vertices use width `k`; inner
vertices use the symmetric width `n - 2 rank(x)`. -/
theorem exists_good_with_first (x : Cube n 1) (k : ℕ)
    (hlower : 2 * Cube.rank x ≤ n) :
    ∃ C : BooleanChain n, C.toChain.first = x ∧ C.toChain.Good k := by
  by_cases houter : 2 * Cube.rank x + k ≤ n
  · have hbound : Cube.rank x + k ≤ n := by omega
    let C := ofStartWidth x k hbound
    refine ⟨C, ofStartWidth_first x k hbound, ?_⟩
    rw [C.good_toChain_iff]
    exact ⟨le_rfl, Or.inr rfl⟩
  · let w := n - 2 * Cube.rank x
    have hbound : Cube.rank x + w ≤ n := by
      dsimp [w]
      omega
    let C := ofStartWidth x w hbound
    refine ⟨C, ofStartWidth_first x w hbound, ?_⟩
    rw [C.good_toChain_iff]
    constructor
    · change w ≤ k
      dsimp [w]
      omega
    · left
      change 2 * (finsetOfCube x).card + w = n
      rw [card_finsetOfCube]
      dsimp [w]
      omega

/-- Every upper-half Boolean vertex is the last endpoint of a represented
good chain, obtained by reflecting the lower construction. -/
theorem exists_good_with_last (x : Cube n 1) (k : ℕ)
    (hupper : n ≤ 2 * Cube.rank x) :
    ∃ C : BooleanChain n, C.toChain.last = x ∧ C.toChain.Good k := by
  have hreflectLower : 2 * Cube.rank (Cube.reflect x) ≤ n := by
    rw [Cube.rank_reflect]
    have hrank := Cube.rank_le x
    omega
  obtain ⟨C, hfirst, hgood⟩ := exists_good_with_first (Cube.reflect x) k hreflectLower
  refine ⟨C.reflect, ?_, (C.good_reflect_iff k).mpr hgood⟩
  rw [show C.reflect.toChain.last = Cube.reflect C.toChain.first by
      change C.reflect.vertex (Fin.last C.steps) = Cube.reflect (C.vertex 0)
      rw [C.vertex_reflect]
      congr 1
      apply congrArg C.vertex
      apply Fin.ext
      simp]
  rw [hfirst, Cube.reflect_reflect]

/-- Every Boolean vertex lies on a represented good chain. -/
theorem exists_good_containing (x : Cube n 1) (k : ℕ) :
    ∃ C : BooleanChain n, x ∈ C.toChain.vertices ∧ C.toChain.Good k := by
  by_cases hlower : 2 * Cube.rank x ≤ n
  · obtain ⟨C, hfirst, hgood⟩ := exists_good_with_first x k hlower
    refine ⟨C, ?_, hgood⟩
    rw [Chain.mem_vertices_iff]
    exact ⟨0, hfirst⟩
  · obtain ⟨C, hlast, hgood⟩ := exists_good_with_last x k (by omega)
    refine ⟨C, ?_, hgood⟩
    rw [Chain.mem_vertices_iff]
    exact ⟨Fin.last C.steps, hlast⟩

end BooleanChain
end DOne
end WeightedChains
