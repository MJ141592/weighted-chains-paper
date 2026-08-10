import WeightedChains.Preliminaries
import WeightedChains.MiddleLayerUniqueness

/-!
# The Boolean cube and the middle-layer uniqueness graph

This file identifies a vertex of `Cube n 1` with the finite set of coordinates
on which it is one.  Under this identification, rank is cardinality and the
coordinatewise order is subset inclusion.  We then transport the connected
adjacent-layer uniqueness theorem back to the paper's cube notation.
-/

set_option autoImplicit false

open scoped BigOperators

namespace WeightedChains
namespace DOneMiddleUniqueness

/-- The set of coordinates equal to one in a Boolean-cube vertex. -/
def ones {n : ℕ} (x : Cube n 1) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i = 1

@[simp]
theorem mem_ones {n : ℕ} (x : Cube n 1) (i : Fin n) :
    i ∈ ones x ↔ x i = 1 := by
  simp [ones]

/-- The Boolean-cube vertex which is one precisely on `s`. -/
def ofFinset {n : ℕ} (s : Finset (Fin n)) : Cube n 1 :=
  fun i ↦ if i ∈ s then 1 else 0

@[simp]
theorem ofFinset_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    ofFinset s i = if i ∈ s then 1 else 0 :=
  rfl

private theorem fin_two_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  have ha := a.isLt
  omega

@[simp]
theorem ones_ofFinset {n : ℕ} (s : Finset (Fin n)) :
    ones (ofFinset s) = s := by
  ext i
  simp [ones, ofFinset]

@[simp]
theorem ofFinset_ones {n : ℕ} (x : Cube n 1) :
    ofFinset (ones x) = x := by
  funext i
  rcases fin_two_eq_zero_or_one (x i) with hi | hi
  · simp [ones, ofFinset, hi]
  · simp [ones, ofFinset, hi]

/-- The canonical equivalence between Boolean-cube vertices and subsets of
the coordinate set. -/
def cubeEquivFinset (n : ℕ) : Cube n 1 ≃ Finset (Fin n) where
  toFun := ones
  invFun := ofFinset
  left_inv := ofFinset_ones
  right_inv := ones_ofFinset

@[simp]
theorem cubeEquivFinset_apply {n : ℕ} (x : Cube n 1) :
    cubeEquivFinset n x = ones x :=
  rfl

@[simp]
theorem cubeEquivFinset_symm_apply {n : ℕ} (s : Finset (Fin n)) :
    (cubeEquivFinset n).symm s = ofFinset s :=
  rfl

/-- In the Boolean cube, rank is the number of coordinates equal to one. -/
theorem rank_eq_card_ones {n : ℕ} (x : Cube n 1) :
    Cube.rank x = (ones x).card := by
  unfold Cube.rank
  calc
    ∑ i, (x i : ℕ) = ∑ i, if x i = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rcases fin_two_eq_zero_or_one (x i) with hi | hi
      · simp [hi]
      · simp [hi]
    _ = (ones x).card := by simp [ones]

@[simp]
theorem rank_ofFinset {n : ℕ} (s : Finset (Fin n)) :
    Cube.rank (ofFinset s) = s.card := by
  rw [rank_eq_card_ones, ones_ofFinset]

/-- Coordinatewise comparison in the Boolean cube is subset inclusion of the
one-coordinate sets. -/
theorem le_iff_ones_subset {n : ℕ} {x y : Cube n 1} :
    x ≤ y ↔ ones x ⊆ ones y := by
  constructor
  · intro hxy i hi
    have hxi : x i = 1 := (mem_ones x i).mp hi
    have hyi : y i = 1 := by
      have hle := hxy i
      rcases fin_two_eq_zero_or_one (y i) with hyi | hyi
      · simp [hxi, hyi] at hle
      · exact hyi
    exact (mem_ones y i).mpr hyi
  · intro hsubset i
    rcases fin_two_eq_zero_or_one (x i) with hxi | hxi
    · simp [hxi]
    · have hmem : i ∈ ones y := hsubset ((mem_ones x i).mpr hxi)
      have hyi : y i = 1 := (mem_ones y i).mp hmem
      simp [hxi, hyi]

/-- The preceding equivalence as an order isomorphism. -/
def cubeOrderIsoFinset (n : ℕ) : Cube n 1 ≃o Finset (Fin n) where
  toEquiv := cubeEquivFinset n
  map_rel_iff' := le_iff_ones_subset.symm

/-- Boolean-cube vertices in ranks `r` and `r + 1`. -/
def CubeAdjacentLayerVertex (n r : ℕ) :=
  {x : Cube n 1 // Cube.rank x = r ∨ Cube.rank x = r + 1}

/-- The lower rank inside `CubeAdjacentLayerVertex`. -/
def cubeLowerLayer (n r : ℕ) : Set (CubeAdjacentLayerVertex n r) :=
  {x | Cube.rank x.1 = r}

/-- The upper rank inside `CubeAdjacentLayerVertex`. -/
def cubeUpperLayer (n r : ℕ) : Set (CubeAdjacentLayerVertex n r) :=
  {x | Cube.rank x.1 = r + 1}

/-- The rank-preserving equivalence between the two adjacent cube layers and
the corresponding adjacent layers of the finite-set lattice. -/
def cubeAdjacentLayerEquiv (n r : ℕ) :
    CubeAdjacentLayerVertex n r ≃
      MiddleLayerUniqueness.AdjacentLayerVertex n r where
  toFun x := by
    refine ⟨ones x.1, ?_⟩
    rcases x.2 with hx | hx
    · exact Or.inl ((rank_eq_card_ones x.1).symm.trans hx)
    · exact Or.inr ((rank_eq_card_ones x.1).symm.trans hx)
  invFun s := by
    refine ⟨ofFinset s.1, ?_⟩
    rcases s.2 with hs | hs
    · exact Or.inl ((rank_ofFinset s.1).trans hs)
    · exact Or.inr ((rank_ofFinset s.1).trans hs)
  left_inv x := by
    apply Subtype.ext
    exact ofFinset_ones x.1
  right_inv s := by
    apply Subtype.ext
    exact ones_ofFinset s.1

/-- The adjacent-layer incidence graph, transported to Boolean-cube
vertices. -/
def cubeAdjacentLayerGraph (n r : ℕ) : SimpleGraph (CubeAdjacentLayerVertex n r) :=
  (MiddleLayerUniqueness.adjacentLayerGraph n r).comap (cubeAdjacentLayerEquiv n r)

/-- The transported graph is isomorphic to the finite-set incidence graph. -/
def cubeAdjacentLayerGraphIso (n r : ℕ) :
    cubeAdjacentLayerGraph n r ≃g MiddleLayerUniqueness.adjacentLayerGraph n r where
  toEquiv := cubeAdjacentLayerEquiv n r
  map_rel_iff' := Iff.rfl

theorem cubeAdjacentLayerGraph_connected {n r : ℕ} (hr : r ≤ n) :
    (cubeAdjacentLayerGraph n r).Connected :=
  (cubeAdjacentLayerGraphIso n r).connected_iff.mpr
    (MiddleLayerUniqueness.adjacentLayerGraph_connected hr)

/-- Edges of the transported graph are precisely comparable pairs with one
endpoint in rank `r` and the other in rank `r + 1`. -/
theorem cubeAdjacentLayerGraph_adj_iff {n r : ℕ}
    {x y : CubeAdjacentLayerVertex n r} :
    (cubeAdjacentLayerGraph n r).Adj x y ↔
      (Cube.rank x.1 = r ∧ Cube.rank y.1 = r + 1 ∧ x.1 ≤ y.1) ∨
      (Cube.rank y.1 = r ∧ Cube.rank x.1 = r + 1 ∧ y.1 ≤ x.1) := by
  change ones x.1 ⊂ ones y.1 ∨ ones y.1 ⊂ ones x.1 ↔ _
  constructor
  · rintro (hxy | hyx)
    · left
      have hcard := Finset.card_lt_card hxy
      have hrank : Cube.rank x.1 < Cube.rank y.1 := by
        rw [rank_eq_card_ones, rank_eq_card_ones]
        exact hcard
      rcases x.2 with hx | hx <;> rcases y.2 with hy | hy
      · omega
      · exact ⟨hx, hy, le_iff_ones_subset.mpr hxy.le⟩
      · omega
      · omega
    · right
      have hcard := Finset.card_lt_card hyx
      have hrank : Cube.rank y.1 < Cube.rank x.1 := by
        rw [rank_eq_card_ones, rank_eq_card_ones]
        exact hcard
      rcases x.2 with hx | hx <;> rcases y.2 with hy | hy
      · omega
      · omega
      · exact ⟨hy, hx, le_iff_ones_subset.mpr hyx.le⟩
      · omega
  · rintro (⟨hx, hy, hxy⟩ | ⟨hy, hx, hyx⟩)
    · left
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨le_iff_ones_subset.mp hxy, ?_⟩
      intro hEq
      have hcard := congrArg Finset.card hEq
      rw [← rank_eq_card_ones, ← rank_eq_card_ones, hx, hy] at hcard
      omega
    · right
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨le_iff_ones_subset.mp hyx, ?_⟩
      intro hEq
      have hcard := congrArg Finset.card hEq
      rw [← rank_eq_card_ones, ← rank_eq_card_ones, hy, hx] at hcard
      omega

theorem cubeAdjacentLayerGraph_isBipartiteWith (n r : ℕ) :
    (cubeAdjacentLayerGraph n r).IsBipartiteWith
      (cubeLowerLayer n r) (cubeUpperLayer n r) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hxLower hxUpper
    change Cube.rank x.1 = r at hxLower
    change Cube.rank x.1 = r + 1 at hxUpper
    omega
  · intro x y hxy
    rw [cubeAdjacentLayerGraph_adj_iff] at hxy
    rcases hxy with ⟨hx, hy, _hle⟩ | ⟨hy, hx, _hle⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩

theorem cubeLowerLayer_union_cubeUpperLayer (n r : ℕ) :
    cubeLowerLayer n r ∪ cubeUpperLayer n r = Set.univ := by
  ext x
  change (Cube.rank x.1 = r ∨ Cube.rank x.1 = r + 1) ↔ True
  simpa using x.2

/-- A choice of exactly one endpoint of every comparable rank-`r` to
rank-`r+1` edge is one of those two complete layers. -/
theorem cubeAdjacentLayer_choice_eq_lower_or_upper {n r : ℕ} (hr : r ≤ n)
    {A : Set (CubeAdjacentLayerVertex n r)}
    (hexact : ∀ {x y : CubeAdjacentLayerVertex n r},
      Cube.rank x.1 = r → Cube.rank y.1 = r + 1 → x.1 ≤ y.1 →
        (x ∈ A ↔ y ∉ A)) :
    A = cubeLowerLayer n r ∨ A = cubeUpperLayer n r := by
  apply MiddleLayerUniqueness.eq_left_or_eq_right
    (cubeAdjacentLayerGraph_connected hr)
    (cubeAdjacentLayerGraph_isBipartiteWith n r)
    (cubeLowerLayer_union_cubeUpperLayer n r)
  intro x y hxy
  rw [cubeAdjacentLayerGraph_adj_iff] at hxy
  rcases hxy with ⟨hx, hy, hle⟩ | ⟨hy, hx, hle⟩
  · exact hexact hx hy hle
  · have h := hexact hy hx hle
    tauto

/-- The union of two adjacent layers in the original cube type. -/
def cubeAdjacentLayers (n r : ℕ) : Set (Cube n 1) :=
  Cube.layer n 1 r ∪ Cube.layer n 1 (r + 1)

/-- Original-cube formulation of the middle-layer graph step: if a family
selects exactly one endpoint of every comparable edge from rank `r` to rank
`r + 1`, then its restriction to those ranks is one whole layer. -/
theorem inter_adjacentLayers_eq_lower_or_upper {n r : ℕ} (hr : r ≤ n)
    (A : Set (Cube n 1))
    (hexact : ∀ {x y : Cube n 1},
      Cube.rank x = r → Cube.rank y = r + 1 → x ≤ y →
        (x ∈ A ↔ y ∉ A)) :
    A ∩ cubeAdjacentLayers n r = Cube.layer n 1 r ∨
      A ∩ cubeAdjacentLayers n r = Cube.layer n 1 (r + 1) := by
  let restricted : Set (CubeAdjacentLayerVertex n r) := {x | x.1 ∈ A}
  have hchoice := cubeAdjacentLayer_choice_eq_lower_or_upper hr (A := restricted) (by
    intro x y hx hy hxy
    exact hexact hx hy hxy)
  rcases hchoice with hlower | hupper
  · left
    ext x
    change (x ∈ A ∧ (Cube.rank x = r ∨ Cube.rank x = r + 1)) ↔ Cube.rank x = r
    constructor
    · rintro ⟨hxA, hxRanks⟩
      let xs : CubeAdjacentLayerVertex n r := ⟨x, hxRanks⟩
      have hxsA : xs ∈ restricted := hxA
      have hxsLower : xs ∈ cubeLowerLayer n r := by
        rw [← hlower]
        exact hxsA
      exact hxsLower
    · intro hx
      let xs : CubeAdjacentLayerVertex n r := ⟨x, Or.inl hx⟩
      have hxsLower : xs ∈ cubeLowerLayer n r := hx
      have hxsA : xs ∈ restricted := by
        rw [hlower]
        exact hxsLower
      exact ⟨hxsA, Or.inl hx⟩
  · right
    ext x
    change (x ∈ A ∧ (Cube.rank x = r ∨ Cube.rank x = r + 1)) ↔
      Cube.rank x = r + 1
    constructor
    · rintro ⟨hxA, hxRanks⟩
      let xs : CubeAdjacentLayerVertex n r := ⟨x, hxRanks⟩
      have hxsA : xs ∈ restricted := hxA
      have hxsUpper : xs ∈ cubeUpperLayer n r := by
        rw [← hupper]
        exact hxsA
      exact hxsUpper
    · intro hx
      let xs : CubeAdjacentLayerVertex n r := ⟨x, Or.inr hx⟩
      have hxsUpper : xs ∈ cubeUpperLayer n r := hx
      have hxsA : xs ∈ restricted := by
        rw [hupper]
        exact hxsUpper
      exact ⟨hxsA, Or.inr hx⟩

end DOneMiddleUniqueness
end WeightedChains
