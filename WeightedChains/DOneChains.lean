import WeightedChains.DOne

/-!
# Concrete saturated chains in the Boolean cube

This file supplies a finite representation of the saturated chains used in
Section 4.  A chain is described by its initial support together with an
ordered list of fresh coordinates.  The list is represented by an embedding,
which makes both finiteness and the absence of repeated coordinate changes
explicit.
-/

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace WeightedChains
namespace DOne

/-- The Boolean-cube vertex whose support is `s`. -/
def cubeOfFinset {n : ℕ} (s : Finset (Fin n)) : Cube n 1 :=
  fun i ↦ if i ∈ s then 1 else 0

@[simp]
theorem cubeOfFinset_apply_eq_one {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    cubeOfFinset s i = 1 ↔ i ∈ s := by
  simp [cubeOfFinset]

@[simp]
theorem cubeOfFinset_apply_eq_zero {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    cubeOfFinset s i = 0 ↔ i ∉ s := by
  simp [cubeOfFinset]

theorem cubeOfFinset_mono {n : ℕ} {s t : Finset (Fin n)} (hst : s ⊆ t) :
    cubeOfFinset s ≤ cubeOfFinset t := by
  intro i
  by_cases hi : i ∈ s
  · simp [cubeOfFinset, hi, hst hi]
  · simp [cubeOfFinset, hi]

@[simp]
theorem rank_cubeOfFinset {n : ℕ} (s : Finset (Fin n)) :
    Cube.rank (cubeOfFinset s) = s.card := by
  classical
  unfold Cube.rank cubeOfFinset
  calc
    ∑ i, ((if i ∈ s then 1 else 0 : Fin 2) : ℕ) =
        ∑ i, if i ∈ s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      split <;> rfl
    _ = s.card := by simp

/-- Finite data for a saturated chain in `{0,1}^n`.

`addition j` is the coordinate changed at the `j`-th step.  The embedding
prevents repetitions, while `fresh` says none of these coordinates was
already present at the first vertex.
-/
structure BooleanChain (n : ℕ) where
  steps : Fin (n + 1)
  start : Finset (Fin n)
  addition : Fin steps ↪ Fin n
  fresh : Disjoint start (Finset.univ.map addition)
  deriving DecidableEq, Fintype

namespace BooleanChain

variable {n : ℕ}

@[ext]
theorem ext {C D : BooleanChain n} (hsteps : C.steps = D.steps)
    (hstart : C.start = D.start) (haddition : HEq C.addition D.addition) : C = D := by
  cases C
  cases D
  simp_all

/-- The canonical embedding of the indices before time `i` into all step
indices. -/
def prefixEmbedding (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    Fin i ↪ Fin C.steps where
  toFun j := ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)⟩
  inj' a b h := by
    apply Fin.ext
    exact congrArg (fun z : Fin C.steps ↦ z.val) h

/-- The embedding which enumerates the coordinates changed before time `i`. -/
def prefixAddition (C : BooleanChain n) (i : Fin (C.steps + 1)) : Fin i ↪ Fin n where
  toFun j := C.addition (C.prefixEmbedding i j)
  inj' := C.addition.injective.comp (C.prefixEmbedding i).injective

/-- Coordinates which have been changed strictly before time `i`. -/
def added (C : BooleanChain n) (i : Fin (C.steps + 1)) : Finset (Fin n) :=
  Finset.univ.map (C.prefixAddition i)

/-- The support at time `i`. -/
def support (C : BooleanChain n) (i : Fin (C.steps + 1)) : Finset (Fin n) :=
  C.start ∪ C.added i

/-- The Boolean vertex at time `i`. -/
def vertex (C : BooleanChain n) (i : Fin (C.steps + 1)) : Cube n 1 :=
  cubeOfFinset (C.support i)

@[simp]
theorem card_added (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    (C.added i).card = i := by
  simp [added]

theorem added_subset_all (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    C.added i ⊆ Finset.univ.map C.addition := by
  intro x hx
  simp only [added, Finset.mem_map] at hx ⊢
  obtain ⟨j, _hj, rfl⟩ := hx
  exact ⟨C.prefixEmbedding i j, Finset.mem_univ _, rfl⟩

theorem disjoint_start_added (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    Disjoint C.start (C.added i) :=
  C.fresh.mono_right (C.added_subset_all i)

theorem added_mono (C : BooleanChain n) {i j : Fin (C.steps + 1)} (hij : i ≤ j) :
    C.added i ⊆ C.added j := by
  intro x hx
  simp only [added, Finset.mem_map] at hx ⊢
  obtain ⟨a, _ha, rfl⟩ := hx
  let b : Fin j := ⟨a, lt_of_lt_of_le a.isLt hij⟩
  refine ⟨b, Finset.mem_univ _, ?_⟩
  apply congrArg C.addition
  apply Fin.ext
  rfl

theorem support_mono (C : BooleanChain n) {i j : Fin (C.steps + 1)} (hij : i ≤ j) :
    C.support i ⊆ C.support j := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ hx
  · exact Finset.mem_union_right _ (C.added_mono hij hx)

theorem vertex_mono (C : BooleanChain n) : Monotone C.vertex := by
  intro i j hij
  exact cubeOfFinset_mono (C.support_mono hij)

@[simp]
theorem card_support (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    (C.support i).card = C.start.card + i := by
  rw [support, Finset.card_union_of_disjoint (C.disjoint_start_added i), card_added]

@[simp]
theorem rank_vertex (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    Cube.rank (C.vertex i) = C.start.card + i := by
  simp [vertex]

theorem vertex_injective (C : BooleanChain n) : Function.Injective C.vertex := by
  intro i j hij
  have hrank := congrArg Cube.rank hij
  rw [C.rank_vertex i, C.rank_vertex j] at hrank
  apply Fin.ext
  exact Nat.add_left_cancel hrank

@[simp]
theorem support_zero (C : BooleanChain n) : C.support 0 = C.start := by
  have hadded : C.added 0 = ∅ := Finset.card_eq_zero.mp (by simp)
  simp [support, hadded]

@[simp]
theorem added_last (C : BooleanChain n) :
    C.added (Fin.last C.steps) = Finset.univ.map C.addition := by
  apply Finset.Subset.antisymm (C.added_subset_all (Fin.last C.steps))
  intro x hx
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hx
  apply Finset.mem_map.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  apply congrArg C.addition
  apply Fin.ext
  rfl

/-- The generic chain represented by the finite Boolean-chain data. -/
def toChain (C : BooleanChain n) : Chain n 1 where
  steps := C.steps
  vertex := C.vertex
  monotone_vertex := C.vertex_mono

@[simp]
theorem toChain_vertex (C : BooleanChain n) (i : Fin (C.steps + 1)) :
    C.toChain.vertex i = C.vertex i := rfl

@[simp]
theorem toChain_first (C : BooleanChain n) :
    C.toChain.first = cubeOfFinset C.start := by
  change C.vertex 0 = cubeOfFinset C.start
  unfold vertex
  rw [support_zero]

@[simp]
theorem rank_toChain_first (C : BooleanChain n) :
    Cube.rank C.toChain.first = C.start.card := by
  simp

@[simp]
theorem rank_toChain_last (C : BooleanChain n) :
    Cube.rank C.toChain.last = C.start.card + C.steps := by
  change Cube.rank (C.vertex (Fin.last C.steps)) = C.start.card + C.steps
  exact C.rank_vertex (Fin.last C.steps)

/-- Every represented Boolean chain is saturated. -/
theorem saturated_toChain (C : BooleanChain n) : C.toChain.Saturated := by
  change ∀ i : Fin C.steps,
    Cube.rank (C.vertex i.castSucc) + 1 = Cube.rank (C.vertex i.succ)
  intro i
  rw [rank_vertex, rank_vertex, Nat.add_assoc]
  rfl

@[simp]
theorem toChain_length (C : BooleanChain n) : C.toChain.length = C.steps + 1 := rfl

@[simp]
theorem card_toChain_vertices (C : BooleanChain n) :
    C.toChain.vertices.card = C.steps + 1 := by
  unfold Chain.vertices
  change (Finset.univ.image C.vertex).card = C.steps + 1
  rw [Finset.card_image_of_injective Finset.univ C.vertex_injective]
  simp

theorem hammingDistance_cubeOfFinset_union_of_disjoint
    (s t : Finset (Fin n)) (hst : Disjoint s t) :
    Cube.hammingDistance (cubeOfFinset s) (cubeOfFinset (s ∪ t)) = t.card := by
  unfold Cube.hammingDistance Cube.differingCoordinates
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hdisjoint := Finset.disjoint_left.mp hst
  by_cases hx : x ∈ s
  · have hxnot : x ∉ t := hdisjoint hx
    simp [cubeOfFinset, hx, hxnot]
  · simp [cubeOfFinset, hx]

@[simp]
theorem width_toChain (C : BooleanChain n) : C.toChain.width = C.steps := by
  unfold Chain.width
  rw [toChain_first]
  change Cube.hammingDistance (cubeOfFinset C.start)
    (cubeOfFinset (C.support (Fin.last C.steps))) = C.steps
  rw [support, added_last,
    hammingDistance_cubeOfFinset_union_of_disjoint C.start
      (Finset.univ.map C.addition) C.fresh]
  simp

/-- Endpoint symmetry for represented Boolean chains, expressed purely in
terms of the starting support and the number of changed coordinates. -/
theorem symmetric_toChain_iff (C : BooleanChain n) :
    C.toChain.Symmetric ↔ 2 * C.start.card + C.steps = n := by
  rw [Chain.symmetric_iff_endpoint C.toChain C.saturated_toChain]
  simp only [rank_toChain_first, rank_toChain_last, Nat.mul_one]
  omega

/-- The paper's goodness condition has a direct arithmetic form for the
finite Boolean-chain representation. -/
theorem good_toChain_iff (C : BooleanChain n) (k : ℕ) :
    C.toChain.Good k ↔
      C.steps ≤ k ∧ (2 * C.start.card + C.steps = n ∨ C.steps = k) := by
  unfold Chain.Good
  rw [width_toChain, symmetric_toChain_iff, toChain_length]
  simp only [Nat.one_mul]
  constructor
  · rintro ⟨_saturated, hwidth, hsym | hlength⟩
    · exact ⟨hwidth, Or.inl hsym⟩
    · exact ⟨hwidth, Or.inr (Nat.add_right_cancel hlength)⟩
  · rintro ⟨hwidth, hsym | hsteps⟩
    · exact ⟨C.saturated_toChain, hwidth, Or.inl hsym⟩
    · exact ⟨C.saturated_toChain, hwidth, Or.inr (congrArg (fun a ↦ a + 1) hsteps)⟩

/-- Relabel the coordinates of a Boolean chain. -/
def permute (C : BooleanChain n) (e : Equiv.Perm (Fin n)) : BooleanChain n where
  steps := C.steps
  start := C.start.map e.toEmbedding
  addition := C.addition.trans e.toEmbedding
  fresh := by
    rw [← Finset.map_map]
    exact (Finset.disjoint_map e.toEmbedding).mpr C.fresh

@[simp]
theorem permute_steps (C : BooleanChain n) (e : Equiv.Perm (Fin n)) :
    (C.permute e).steps = C.steps := rfl

@[simp]
theorem permute_start_card (C : BooleanChain n) (e : Equiv.Perm (Fin n)) :
    (C.permute e).start.card = C.start.card := by
  simp [permute]

theorem added_permute (C : BooleanChain n) (e : Equiv.Perm (Fin n))
    (i : Fin (C.steps + 1)) :
    (C.permute e).added i = (C.added i).map e.toEmbedding := by
  unfold added
  rw [Finset.map_map]
  congr 1

theorem support_permute (C : BooleanChain n) (e : Equiv.Perm (Fin n))
    (i : Fin (C.steps + 1)) :
    (C.permute e).support i = (C.support i).map e.toEmbedding := by
  unfold support
  rw [added_permute, Finset.map_union]
  rfl

/-- The coordinate permutation induced on Boolean-cube vertices. -/
def cubePermEquiv (e : Equiv.Perm (Fin n)) : Cube n 1 ≃ Cube n 1 where
  toFun x i := x (e.symm i)
  invFun x i := x (e i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

theorem cubePermEquiv_cubeOfFinset (e : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    cubePermEquiv e (cubeOfFinset s) = cubeOfFinset (s.map e.toEmbedding) := by
  funext i
  simp [cubePermEquiv, cubeOfFinset]

theorem vertex_permute (C : BooleanChain n) (e : Equiv.Perm (Fin n))
    (i : Fin (C.steps + 1)) :
    (C.permute e).vertex i = cubePermEquiv e (C.vertex i) := by
  change cubeOfFinset ((C.permute e).support i) =
    cubePermEquiv e (cubeOfFinset (C.support i))
  rw [support_permute]
  exact (cubePermEquiv_cubeOfFinset e (C.support i)).symm

theorem first_permute (C : BooleanChain n) (e : Equiv.Perm (Fin n)) :
    (C.permute e).toChain.first = cubePermEquiv e C.toChain.first := by
  change (C.permute e).vertex 0 = cubePermEquiv e (C.vertex 0)
  exact C.vertex_permute e 0

theorem permute_symm_permute (C : BooleanChain n) (e : Equiv.Perm (Fin n)) :
    (C.permute e).permute e.symm = C := by
  apply BooleanChain.ext
  · rfl
  · simp [permute, Finset.map_map]
  · apply heq_of_eq
    apply Function.Embedding.ext
    intro i
    change e.symm (e (C.addition i)) = C.addition i
    exact e.symm_apply_apply _

/-- Coordinate relabelling is an equivalence of the finite chain data. -/
def permuteEquiv (e : Equiv.Perm (Fin n)) : BooleanChain n ≃ BooleanChain n where
  toFun C := C.permute e
  invFun C := C.permute e.symm
  left_inv C := C.permute_symm_permute e
  right_inv C := C.permute_symm_permute e.symm

@[simp]
theorem permuteEquiv_apply (e : Equiv.Perm (Fin n)) (C : BooleanChain n) :
    permuteEquiv e C = C.permute e := rfl

theorem good_permute_iff (C : BooleanChain n) (e : Equiv.Perm (Fin n)) (k : ℕ) :
    (C.permute e).toChain.Good k ↔ C.toChain.Good k := by
  rw [good_toChain_iff, good_toChain_iff]
  simp

/-- The support of an arbitrary Boolean-cube vertex. -/
def finsetOfCube (x : Cube n 1) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i = 1

@[simp]
theorem cubeOfFinset_finsetOfCube (x : Cube n 1) :
    cubeOfFinset (finsetOfCube x) = x := by
  funext i
  by_cases hi : x i = 1
  · simp [cubeOfFinset, finsetOfCube, hi]
  · have hzero : x i = 0 := by
      generalize hxi : x i = z
      fin_cases z
      · rfl
      · exact (hi hxi).elim
    simp [cubeOfFinset, finsetOfCube, hzero]

@[simp]
theorem card_finsetOfCube (x : Cube n 1) :
    (finsetOfCube x).card = Cube.rank x := by
  rw [← rank_cubeOfFinset, cubeOfFinset_finsetOfCube]

/-- Coordinate permutations act transitively on each rank of the Boolean
cube. -/
theorem exists_cubePermEquiv_eq_of_rank_eq {x y : Cube n 1}
    (hxy : Cube.rank x = Cube.rank y) :
    ∃ e : Equiv.Perm (Fin n), cubePermEquiv e x = y := by
  have hcard : (finsetOfCube x).card = (finsetOfCube y).card := by
    simpa using hxy
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq
    (finsetOfCube x) (finsetOfCube y) hcard
  refine ⟨e, ?_⟩
  rw [← cubeOfFinset_finsetOfCube x, cubePermEquiv_cubeOfFinset, he,
    cubeOfFinset_finsetOfCube]

theorem mem_vertices_permute_iff (C : BooleanChain n) (e : Equiv.Perm (Fin n))
    (x : Cube n 1) :
    cubePermEquiv e x ∈ (C.permute e).toChain.vertices ↔
      x ∈ C.toChain.vertices := by
  rw [Chain.mem_vertices_iff, Chain.mem_vertices_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, (cubePermEquiv e).injective ?_⟩
    exact (C.vertex_permute e i).symm.trans hi
  · rintro ⟨i, hi⟩
    refine ⟨i, C.vertex_permute e i |>.trans ?_⟩
    exact congrArg (cubePermEquiv e) hi

/-- A layer at which the paper regards `C` as starting.  The endpoint farther
from the middle is a starting endpoint; for a symmetric chain both reflected
endpoint layers satisfy this predicate. -/
def StartsAtLayer (C : BooleanChain n) (a : ℕ) : Prop :=
  (((2 * (C.start.card + C.steps)).dist n ≤ (2 * C.start.card).dist n) ∧
      C.start.card = a) ∨
    (((2 * C.start.card).dist n ≤ (2 * (C.start.card + C.steps)).dist n) ∧
      C.start.card + C.steps = a)

instance decidableStartsAtLayer (C : BooleanChain n) (a : ℕ) :
    Decidable (C.StartsAtLayer a) := by
  unfold StartsAtLayer
  infer_instance

theorem startsAtLayer_iff (C : BooleanChain n) (a : ℕ) :
    C.StartsAtLayer a ↔
      (C.toChain.StartsAtFirst ∧ Cube.rank C.toChain.first = a) ∨
      (C.toChain.StartsAtLast ∧ Cube.rank C.toChain.last = a) := by
  unfold StartsAtLayer Chain.StartsAtFirst Chain.StartsAtLast Cube.middleDistance
  simp only [rank_toChain_first, rank_toChain_last, Nat.mul_one]

theorem startsAtLayer_permute_iff (C : BooleanChain n) (e : Equiv.Perm (Fin n))
    (a : ℕ) : (C.permute e).StartsAtLayer a ↔ C.StartsAtLayer a := by
  simp [StartsAtLayer]

/-- The represented good chains which start at layer `a` in the paper's
endpoint orientation and pass through `x`. -/
def goodChainsStartingAtLayerThrough (n k a : ℕ) (x : Cube n 1) :
    Finset (BooleanChain n) :=
  Finset.univ.filter fun C ↦
    C.steps ≤ k ∧ (2 * C.start.card + C.steps = n ∨ C.steps = k) ∧
      C.StartsAtLayer a ∧ x ∈ C.toChain.vertices

theorem mem_goodChainsStartingAtLayerThrough_iff
    (C : BooleanChain n) (k a : ℕ) (x : Cube n 1) :
    C ∈ goodChainsStartingAtLayerThrough n k a x ↔
      C.toChain.Good k ∧ C.StartsAtLayer a ∧ x ∈ C.toChain.vertices := by
  rw [goodChainsStartingAtLayerThrough, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, good_toChain_iff]
  tauto

/-- Uniform incidence in the exact family of paper-oriented good chains
starting at a fixed layer. -/
theorem card_goodChainsStartingAtLayerThrough_eq_of_rank_eq
    (n k a : ℕ) {x y : Cube n 1} (hxy : Cube.rank x = Cube.rank y) :
    (goodChainsStartingAtLayerThrough n k a x).card =
      (goodChainsStartingAtLayerThrough n k a y).card := by
  obtain ⟨e, he⟩ := exists_cubePermEquiv_eq_of_rank_eq hxy
  apply Finset.card_equiv (permuteEquiv e)
  intro C
  simp only [goodChainsStartingAtLayerThrough, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hvertices := C.mem_vertices_permute_iff e x
  rw [he] at hvertices
  constructor
  · rintro ⟨hsteps, hgood, hstart, hmem⟩
    exact ⟨by simpa using hsteps, by simpa using hgood,
      (C.startsAtLayer_permute_iff e a).mpr hstart, hvertices.mpr hmem⟩
  · rintro ⟨hsteps, hgood, hstart, hmem⟩
    exact ⟨by simpa using hsteps, by simpa using hgood,
      (C.startsAtLayer_permute_iff e a).mp hstart, hvertices.mp hmem⟩

/-- Good represented chains with lower endpoint in layer `a` which pass
through `x`.  For chains whose paper orientation starts at the upper endpoint,
the reflected version uses the last rank instead. -/
def goodLowerEndpointChainsThrough (n k a : ℕ) (x : Cube n 1) :
    Finset (BooleanChain n) :=
  Finset.univ.filter fun C ↦
    C.start.card = a ∧ C.steps ≤ k ∧
      (2 * C.start.card + C.steps = n ∨ C.steps = k) ∧
      x ∈ C.toChain.vertices

theorem mem_goodLowerEndpointChainsThrough_iff
    (C : BooleanChain n) (k a : ℕ) (x : Cube n 1) :
    C ∈ goodLowerEndpointChainsThrough n k a x ↔
      C.start.card = a ∧ C.toChain.Good k ∧ x ∈ C.toChain.vertices := by
  rw [goodLowerEndpointChainsThrough, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, good_toChain_iff]
  tauto

/-- Good represented chains whose first vertex is exactly `x`. -/
def goodChainsWithFirst (n k : ℕ) (x : Cube n 1) : Finset (BooleanChain n) :=
  Finset.univ.filter fun C ↦
    C.steps ≤ k ∧ (2 * C.start.card + C.steps = n ∨ C.steps = k) ∧
      C.toChain.first = x

theorem mem_goodChainsWithFirst_iff (C : BooleanChain n) (k : ℕ) (x : Cube n 1) :
    C ∈ goodChainsWithFirst n k x ↔ C.toChain.Good k ∧ C.toChain.first = x := by
  rw [goodChainsWithFirst, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, good_toChain_iff]
  tauto

/-- The same number of represented good chains has first vertex `x` as has
first vertex `y`, whenever `x` and `y` lie in the same layer. -/
theorem card_goodChainsWithFirst_eq_of_rank_eq
    (n k : ℕ) {x y : Cube n 1} (hxy : Cube.rank x = Cube.rank y) :
    (goodChainsWithFirst n k x).card = (goodChainsWithFirst n k y).card := by
  obtain ⟨e, he⟩ := exists_cubePermEquiv_eq_of_rank_eq hxy
  apply Finset.card_equiv (permuteEquiv e)
  intro C
  simp only [goodChainsWithFirst, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hsteps, hgood, hfirst⟩
    refine ⟨by simpa using hsteps, by simpa using hgood, ?_⟩
    change (C.permute e).toChain.first = y
    rw [C.first_permute e, hfirst, he]
  · rintro ⟨hsteps, hgood, hfirst⟩
    refine ⟨by simpa using hsteps, by simpa using hgood, ?_⟩
    change (C.permute e).toChain.first = y at hfirst
    apply (cubePermEquiv e).injective
    exact (C.first_permute e).symm.trans (hfirst.trans he.symm)

/-- The number of good saturated chains with a fixed lower endpoint layer
passing through a vertex depends only on the vertex's rank.  This is the
coordinate-permutation uniformity used in Section 4. -/
theorem card_goodLowerEndpointChainsThrough_eq_of_rank_eq
    (n k a : ℕ) {x y : Cube n 1} (hxy : Cube.rank x = Cube.rank y) :
    (goodLowerEndpointChainsThrough n k a x).card =
      (goodLowerEndpointChainsThrough n k a y).card := by
  obtain ⟨e, he⟩ := exists_cubePermEquiv_eq_of_rank_eq hxy
  apply Finset.card_equiv (permuteEquiv e)
  intro C
  simp only [goodLowerEndpointChainsThrough, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hvertices := C.mem_vertices_permute_iff e x
  rw [he] at hvertices
  constructor
  · rintro ⟨hstart, hsteps, hgood, hmem⟩
    exact ⟨by simpa using hstart, by simpa using hsteps, by simpa using hgood,
      hvertices.mpr hmem⟩
  · rintro ⟨hstart, hsteps, hgood, hmem⟩
    exact ⟨by simpa using hstart, by simpa using hsteps, by simpa using hgood,
      hvertices.mp hmem⟩

end BooleanChain
end DOne
end WeightedChains
