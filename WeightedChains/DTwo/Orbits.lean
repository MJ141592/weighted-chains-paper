import WeightedChains.DTwo.Types

/-!
# Coordinate orbits in the ternary cube

The coordinate-permutation orbit of a ternary vertex is determined by its
zero and two coordinate counts.  This file counts those orbits by the
trinomial coefficient used in Section 5 of the paper.
-/

namespace WeightedChains

namespace Ternary

/-- The coordinates on which a ternary vertex is zero. -/
def zeroCoordinates {n : ℕ} (x : Cube n 2) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i = 0

/-- The coordinates on which a ternary vertex is two. -/
def twoCoordinates {n : ℕ} (x : Cube n 2) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i = 2

@[simp]
theorem card_zeroCoordinates {n : ℕ} (x : Cube n 2) :
    (zeroCoordinates x).card = zeroCount x := rfl

@[simp]
theorem card_twoCoordinates {n : ℕ} (x : Cube n 2) :
    (twoCoordinates x).card = twoCount x := rfl

theorem disjoint_zeroCoordinates_twoCoordinates {n : ℕ} (x : Cube n 2) :
    Disjoint (zeroCoordinates x) (twoCoordinates x) := by
  rw [Finset.disjoint_left]
  intro i hi0 hi2
  simp only [zeroCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hi0
  simp only [twoCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hi2
  have hzeroTwo : (0 : Fin 3) = 2 := hi0.symm.trans hi2
  have := congrArg Fin.val hzeroTwo
  norm_num at this

/-- Ternary vertices having `a` zero coordinates and `c` two coordinates. -/
def typeFiber (n a c : ℕ) : Finset (Cube n 2) :=
  Finset.univ.filter fun x ↦ zeroCount x = a ∧ twoCount x = c

@[simp]
theorem mem_typeFiber {n a c : ℕ} {x : Cube n 2} :
    x ∈ typeFiber n a c ↔ zeroCount x = a ∧ twoCount x = c := by
  simp [typeFiber]

/-- A pair consists of an `a`-element zero set and a `c`-element two set
chosen from its complement. -/
def coordinatePairs (n a c : ℕ) :
    Finset (Σ _zeroSet : Finset (Fin n), Finset (Fin n)) :=
  (Finset.univ.powersetCard a).sigma fun zeroSet ↦
    (Finset.univ \ zeroSet).powersetCard c

@[simp]
theorem mem_coordinatePairs {n a c : ℕ}
    {p : Σ _zeroSet : Finset (Fin n), Finset (Fin n)} :
    p ∈ coordinatePairs n a c ↔
      p.1.card = a ∧ p.2 ⊆ Finset.univ \ p.1 ∧ p.2.card = c := by
  simp [coordinatePairs]

theorem card_coordinatePairs (n a c : ℕ) :
    (coordinatePairs n a c).card = trinomial n a c := by
  rw [coordinatePairs, Finset.card_sigma]
  calc
    ∑ zeroSet ∈ Finset.univ.powersetCard a,
        ((Finset.univ \ zeroSet).powersetCard c).card =
        ∑ _zeroSet ∈ Finset.univ.powersetCard a, (n - a).choose c := by
      apply Finset.sum_congr rfl
      intro zeroSet hzeroSet
      rw [Finset.card_powersetCard]
      have hcard := (Finset.mem_powersetCard.mp hzeroSet).2
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ zeroSet), Finset.card_univ,
        Fintype.card_fin, hcard]
    _ = trinomial n a c := by
      simp [Finset.card_powersetCard, trinomial]

/-- Recover a ternary vertex from its disjoint zero and two coordinate sets. -/
def vertexOfCoordinatePair {n : ℕ}
    (p : Σ _zeroSet : Finset (Fin n), Finset (Fin n)) : Cube n 2 :=
  fun i ↦ if i ∈ p.1 then 0 else if i ∈ p.2 then 2 else 1

theorem zeroCoordinates_vertexOfCoordinatePair {n : ℕ}
    (p : Σ _zeroSet : Finset (Fin n), Finset (Fin n))
    (_hdisjoint : p.2 ⊆ Finset.univ \ p.1) :
    zeroCoordinates (vertexOfCoordinatePair p) = p.1 := by
  ext i
  by_cases hi0 : i ∈ p.1
  · simp [zeroCoordinates, vertexOfCoordinatePair, hi0]
  · by_cases hi2 : i ∈ p.2
    · simp [zeroCoordinates, vertexOfCoordinatePair, hi0, hi2]
    · simp [zeroCoordinates, vertexOfCoordinatePair, hi0, hi2]

theorem twoCoordinates_vertexOfCoordinatePair {n : ℕ}
    (p : Σ _zeroSet : Finset (Fin n), Finset (Fin n))
    (hdisjoint : p.2 ⊆ Finset.univ \ p.1) :
    twoCoordinates (vertexOfCoordinatePair p) = p.2 := by
  ext i
  by_cases hi0 : i ∈ p.1
  · have hi2 : i ∉ p.2 := by
      intro hi2
      exact (Finset.mem_sdiff.mp (hdisjoint hi2)).2 hi0
    simp [twoCoordinates, vertexOfCoordinatePair, hi0, hi2]
  · by_cases hi2 : i ∈ p.2
    · simp [twoCoordinates, vertexOfCoordinatePair, hi0, hi2]
    · simp [twoCoordinates, vertexOfCoordinatePair, hi0, hi2]

theorem vertexOfCoordinatePair_zero_twoCoordinates {n : ℕ} (x : Cube n 2) :
    vertexOfCoordinatePair ⟨zeroCoordinates x, twoCoordinates x⟩ = x := by
  funext i
  apply Fin.ext
  have hbound : (x i : ℕ) ≤ 2 := by omega
  interval_cases hxi : (x i : ℕ)
  · have hx : x i = 0 := Fin.ext hxi
    simp [vertexOfCoordinatePair, zeroCoordinates, hx]
  · have hx : x i = 1 := Fin.ext hxi
    simp [vertexOfCoordinatePair, zeroCoordinates, twoCoordinates, hx]
  · have hx : x i = 2 := Fin.ext hxi
    simp [vertexOfCoordinatePair, zeroCoordinates, twoCoordinates, hx]

/-- The fiber of a ternary type is equivalent to choosing its disjoint zero
and two coordinate sets. -/
def typeFiberEquivCoordinatePairs (n a c : ℕ) :
    ↑(typeFiber n a c) ≃ ↑(coordinatePairs n a c) where
  toFun x := ⟨⟨zeroCoordinates x, twoCoordinates x⟩, by
    rw [mem_coordinatePairs]
    have hx := (mem_typeFiber.mp x.property)
    refine ⟨by simpa using hx.1, ?_, by simpa using hx.2⟩
    intro i hi2
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hi0
    exact Finset.disjoint_left.mp (disjoint_zeroCoordinates_twoCoordinates x.val) hi0 hi2⟩
  invFun p := ⟨vertexOfCoordinatePair p, by
    rw [mem_typeFiber]
    have hp := mem_coordinatePairs.mp p.property
    change (zeroCoordinates (vertexOfCoordinatePair p.val)).card = a ∧
      (twoCoordinates (vertexOfCoordinatePair p.val)).card = c
    rw [zeroCoordinates_vertexOfCoordinatePair p.val hp.2.1,
      twoCoordinates_vertexOfCoordinatePair p.val hp.2.1]
    exact ⟨hp.1, hp.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact vertexOfCoordinatePair_zero_twoCoordinates x.val
  right_inv p := by
    apply Subtype.ext
    apply Sigma.ext
    · exact zeroCoordinates_vertexOfCoordinatePair p.val
        (mem_coordinatePairs.mp p.property).2.1
    · exact heq_of_eq (twoCoordinates_vertexOfCoordinatePair p.val
        (mem_coordinatePairs.mp p.property).2.1)

/-- The number of vertices of type `(a, n-a-c, c)` is the paper's
coefficient `\binom{n}{a,c}`.  The statement also covers invalid types, when
both sides are zero. -/
theorem card_typeFiber (n a c : ℕ) :
    (typeFiber n a c).card = trinomial n a c := by
  rw [← card_coordinatePairs]
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (typeFiberEquivCoordinatePairs n a c)

/-- The coordinates of a fixed value `j`.  These are the three pieces that
coordinate permutations may independently match. -/
abbrev coordinateFiber {n : ℕ} (x : Cube n 2) (j : Fin 3) :=
  {i : Fin n // x i = j}

theorem card_coordinateFiber {n : ℕ} (x : Cube n 2) (j : Fin 3) :
    Fintype.card (coordinateFiber x j) = Cube.typeOf x j := by
  rw [Fintype.card_subtype]
  rfl

/-- Labeling a coordinate by its value and remembering the coordinate itself
is equivalent to the original coordinate type. -/
def sigmaCoordinateFiberEquiv {n : ℕ} (x : Cube n 2) :
    (Σ j : Fin 3, coordinateFiber x j) ≃ Fin n where
  toFun p := p.2
  invFun i := ⟨x i, i, rfl⟩
  left_inv p := by
    rcases p with ⟨j, ⟨i, hi⟩⟩
    dsimp
    subst j
    rfl
  right_inv _i := rfl

/-- Equal zero and two counts imply equality of the complete ternary types;
the one count follows because all three counts sum to `n`. -/
theorem typeOf_eq_of_zeroCount_eq_twoCount_eq {n : ℕ} {x y : Cube n 2}
    (hzero : zeroCount x = zeroCount y) (htwo : twoCount x = twoCount y) :
    ∀ j : Fin 3, Cube.typeOf x j = Cube.typeOf y j := by
  intro j
  have hbound : (j : ℕ) ≤ 2 := by omega
  interval_cases hj : (j : ℕ)
  · have hj' : j = 0 := Fin.ext hj
    subst j
    exact hzero
  · have hj' : j = 1 := Fin.ext hj
    subst j
    have hx := zeroCount_add_oneCount_add_twoCount x
    have hy := zeroCount_add_oneCount_add_twoCount y
    change oneCount x = oneCount y
    omega
  · have hj' : j = 2 := Fin.ext hj
    subst j
    exact htwo

/-- An equivalence between corresponding coordinate-value fibers of vertices
of the same type. -/
noncomputable def coordinateFiberEquivOfTypeEq {n : ℕ} (x y : Cube n 2)
    (htype : ∀ j : Fin 3, Cube.typeOf x j = Cube.typeOf y j) (j : Fin 3) :
    coordinateFiber x j ≃ coordinateFiber y j :=
  Fintype.equivOfCardEq <| by
    rw [card_coordinateFiber, card_coordinateFiber, htype j]

/-- A coordinate permutation carrying `x` to `y`, assembled independently
on the zero, one, and two coordinate fibers. -/
noncomputable def coordinatePermutationOfTypeEq {n : ℕ} (x y : Cube n 2)
    (htype : ∀ j : Fin 3, Cube.typeOf x j = Cube.typeOf y j) : Equiv.Perm (Fin n) :=
  (sigmaCoordinateFiberEquiv x).symm |>.trans <|
    (Equiv.sigmaCongrRight (coordinateFiberEquivOfTypeEq x y htype)).trans
      (sigmaCoordinateFiberEquiv y)

theorem coordinatePermutationOfTypeEq_apply {n : ℕ} (x y : Cube n 2)
    (htype : ∀ j : Fin 3, Cube.typeOf x j = Cube.typeOf y j) (i : Fin n) :
    y (coordinatePermutationOfTypeEq x y htype i) = x i := by
  change y ((coordinateFiberEquivOfTypeEq x y htype (x i)) ⟨i, rfl⟩) = x i
  exact (coordinateFiberEquivOfTypeEq x y htype (x i) ⟨i, rfl⟩).property

/-- Coordinate permutations act transitively on every ternary type fiber. -/
theorem exists_coordinatePermutation_of_same_type {n : ℕ} {x y : Cube n 2}
    (hzero : zeroCount x = zeroCount y) (htwo : twoCount x = twoCount y) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, y (e i) = x i := by
  let htype := typeOf_eq_of_zeroCount_eq_twoCount_eq hzero htwo
  exact ⟨coordinatePermutationOfTypeEq x y htype,
    coordinatePermutationOfTypeEq_apply x y htype⟩

end Ternary

end WeightedChains
