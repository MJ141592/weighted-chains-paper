import Mathlib

/-!
# Preliminaries

Definitions from Section 2 of *A generalisation of Sperner's theorem using
weighted chain decomposition*.
-/

namespace WeightedChains

/-- The discrete cube `{0, ..., d}^n`. -/
abbrev Cube (n d : ℕ) := Fin n → Fin (d + 1)

namespace Cube

/-- The layer (or rank) of a vertex: the sum of its coordinates. -/
def rank {n d : ℕ} (x : Cube n d) : ℕ := ∑ i, (x i : ℕ)

/-- The `r`-th diagonal layer of the cube. -/
def layer (n d r : ℕ) : Set (Cube n d) := {x | rank x = r}

/-- The type of a vertex: `typeOf x j` counts coordinates equal to `j`.

The paper's displayed indices are transposed at this point: for
`x ∈ {0, ..., d}^n`, the intended type has `d + 1` entries summing to `n`.
-/
def typeOf {n d : ℕ} (x : Cube n d) (j : Fin (d + 1)) : ℕ :=
  (Finset.univ.filter fun i ↦ x i = j).card

/-- The coordinates on which two vertices differ. -/
def differingCoordinates {n d : ℕ} (x y : Cube n d) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i ≠ y i

/-- The number of coordinates on which two vertices differ (the Hamming distance). -/
def hammingDistance {n d : ℕ} (x y : Cube n d) : ℕ :=
  (differingCoordinates x y).card

theorem hammingDistance_comm {n d : ℕ} (x y : Cube n d) :
    hammingDistance x y = hammingDistance y x := by
  unfold hammingDistance differingCoordinates
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  exact ne_comm

/-- Twice the distance of a vertex's rank from the middle of the cube.

Using twice the distance avoids fractions when `n * d` is odd.
-/
def middleDistance {n d : ℕ} (x : Cube n d) : ℕ :=
  (2 * rank x).dist (n * d)

/-- A family is `k`-separated when distinct comparable members differ in more
than `k` coordinates. The distinctness condition is implicit in the paper and
is necessary for the definition to generalise antichains. -/
def KSeparated {n d : ℕ} (A : Set (Cube n d)) (k : ℕ) : Prop :=
  ∀ {x y : Cube n d}, x ∈ A → y ∈ A → x ≤ y → x ≠ y → k < hammingDistance x y

/-- The congruence-class families appearing in the main theorem. -/
def residueFamily (n d k r : ℕ) : Set (Cube n d) :=
  {x | rank x ≡ r [MOD d * k + 1]}

/-- The lower of the one or two middle ranks. -/
def lowerMiddleRank (n d : ℕ) : ℕ := n * d / 2

/-- The upper of the one or two middle ranks. -/
def upperMiddleRank (n d : ℕ) : ℕ := n * d - lowerMiddleRank n d

/-- The paper's family `A₁`. -/
def lowerResidueFamily (n d k : ℕ) : Set (Cube n d) :=
  residueFamily n d k (lowerMiddleRank n d)

/-- The paper's family `A₂`. -/
def upperResidueFamily (n d k : ℕ) : Set (Cube n d) :=
  residueFamily n d k (upperMiddleRank n d)

variable {n d : ℕ}

theorem sum_typeOf (x : Cube n d) : ∑ j, typeOf x j = n := by
  simp only [typeOf, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem rank_le (x : Cube n d) : rank x ≤ n * d := by
  unfold rank
  calc
    ∑ i, (x i : ℕ) ≤ ∑ _i : Fin n, d := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Nat.le_of_lt_succ (x i).isLt
    _ = n * d := by simp

theorem rank_mono {x y : Cube n d} (hxy : x ≤ y) : rank x ≤ rank y := by
  unfold rank
  apply Finset.sum_le_sum
  intro i _hi
  exact hxy i

theorem rank_strictMono {x y : Cube n d} (hxy : x ≤ y) (hne : x ≠ y) :
    rank x < rank y := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    apply hne
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  unfold rank
  apply Finset.sum_lt_sum
  · intro j _hj
    exact hxy j
  · refine ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hxy i) ?_⟩
    intro hval
    exact hi (Fin.ext hval)

theorem rank_sub_le_hammingDistance_mul (x y : Cube n d) (hxy : x ≤ y) :
    rank y - rank x ≤ hammingDistance x y * d := by
  calc
    rank y - rank x = ∑ i, ((y i : ℕ) - (x i : ℕ)) := by
      rw [Finset.sum_tsub_distrib]
      · rfl
      · intro i _hi
        exact hxy i
    _ ≤ ∑ i : Fin n, if x i ≠ y i then d else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      split_ifs with hi
      · exact (Nat.sub_le (y i : ℕ) (x i : ℕ)).trans (Nat.le_of_lt_succ (y i).isLt)
      · have heq : x i = y i := not_ne_iff.mp hi
        rw [heq, Nat.sub_self]
    _ = hammingDistance x y * d := by
      simp [hammingDistance, differingCoordinates, Finset.sum_ite]

/-- In the Boolean cube, the rank difference between comparable vertices is
exactly their Hamming distance. -/
theorem rank_sub_eq_hammingDistance (x y : Cube n 1) (hxy : x ≤ y) :
    rank y - rank x = hammingDistance x y := by
  calc
    rank y - rank x = ∑ i, ((y i : ℕ) - (x i : ℕ)) := by
      rw [Finset.sum_tsub_distrib]
      · rfl
      · intro i _hi
        exact hxy i
    _ = ∑ i : Fin n, if x i ≠ y i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      split_ifs with hi
      · have hval : (x i : ℕ) ≠ (y i : ℕ) := by
          intro h
          exact hi (Fin.ext h)
        have hx : (x i : ℕ) < 2 := (x i).isLt
        have hy : (y i : ℕ) < 2 := (y i).isLt
        have hle : (x i : ℕ) ≤ (y i : ℕ) := hxy i
        omega
      · have heq : x i = y i := not_ne_iff.mp hi
        rw [heq]
        exact Nat.sub_self _
    _ = hammingDistance x y := by
      simp [hammingDistance, differingCoordinates, Finset.sum_ite]

/-- The congruence-class families in the paper are `k`-separated for every
alphabet bound `d`; the restriction `d ∈ {1, 2}` is needed for optimality, not
for this elementary direction. -/
theorem residueFamily_kSeparated (n d k r : ℕ) :
    KSeparated (residueFamily n d k r) k := by
  intro x y hx hy hxy hne
  by_contra h
  have hdist : hammingDistance x y ≤ k := Nat.le_of_not_gt h
  have hrank : rank x < rank y := rank_strictMono hxy hne
  have hmod : rank x ≡ rank y [MOD d * k + 1] := hx.trans hy.symm
  have hdiv : d * k + 1 ∣ rank y - rank x := hmod.dvd'
  have hpositive : 0 < rank y - rank x := Nat.sub_pos_of_lt hrank
  have hlower : d * k + 1 ≤ rank y - rank x := Nat.le_of_dvd hpositive hdiv
  have hupper : rank y - rank x ≤ k * d :=
    (rank_sub_le_hammingDistance_mul x y hxy).trans (Nat.mul_le_mul_right d hdist)
  have himpossible : d * k + 1 ≤ k * d := hlower.trans hupper
  have : k * d + 1 ≤ k * d := by simpa only [Nat.mul_comm d k] using himpossible
  omega

theorem lowerResidueFamily_kSeparated (n d k : ℕ) :
    KSeparated (lowerResidueFamily n d k) k :=
  residueFamily_kSeparated n d k (lowerMiddleRank n d)

theorem upperResidueFamily_kSeparated (n d k : ℕ) :
    KSeparated (upperResidueFamily n d k) k :=
  residueFamily_kSeparated n d k (upperMiddleRank n d)

end Cube

/-- A nonempty finite chain, represented in its monotone order. `steps + 1`
is the paper's chain length. -/
structure Chain (n d : ℕ) where
  /-- One less than the number of vertices. -/ steps : ℕ
  /-- The vertices, indexed in chain order. -/ vertex : Fin (steps + 1) → Cube n d
  /-- Vertices increase in the coordinatewise cube order. -/ monotone_vertex : Monotone vertex

namespace Chain

variable {n d : ℕ}

/-- The number of vertices in a chain. -/
def length (C : Chain n d) : ℕ := C.steps + 1

/-- The first (least) vertex of a chain. -/
def first (C : Chain n d) : Cube n d := C.vertex 0

/-- The last (greatest) vertex of a chain. -/
def last (C : Chain n d) : Cube n d := C.vertex (Fin.last C.steps)

/-- Membership in a chain. -/
def Mem (x : Cube n d) (C : Chain n d) : Prop := x ∈ Set.range C.vertex

instance : Membership (Chain n d) (Cube n d) := ⟨Mem⟩

/-- The finset of vertices in a chain. -/
def vertices (C : Chain n d) : Finset (Cube n d) := Finset.univ.image C.vertex

theorem mem_vertices_iff (C : Chain n d) (x : Cube n d) :
    x ∈ C.vertices ↔ ∃ i, C.vertex i = x := by
  simp [vertices]

/-- The number of coordinates that change between the chain's endpoints. -/
def width (C : Chain n d) : ℕ := Cube.hammingDistance C.first C.last

/-- Consecutive vertices of a saturated chain increase in rank by one. -/
def Saturated (C : Chain n d) : Prop :=
  ∀ i : Fin C.steps, Cube.rank (C.vertex i.castSucc) + 1 = Cube.rank (C.vertex i.succ)

/-- Equidistant vertices from the two ends have complementary ranks. -/
def Symmetric (C : Chain n d) : Prop :=
  ∀ i, Cube.rank (C.vertex i) + Cube.rank (C.vertex i.rev) = n * d

/-- A chain starts at its first endpoint when that endpoint is no closer to the
middle of the cube than its last endpoint. -/
def StartsAtFirst (C : Chain n d) : Prop :=
  Cube.middleDistance C.last ≤ Cube.middleDistance C.first

/-- A chain starts at its last endpoint when that endpoint is no closer to the
middle of the cube than its first endpoint. Equality permits both orientations,
as in the paper. -/
def StartsAtLast (C : Chain n d) : Prop :=
  Cube.middleDistance C.first ≤ Cube.middleDistance C.last

/-- The good chains from Section 2. -/
def Good (C : Chain n d) (k : ℕ) : Prop :=
  C.Saturated ∧ C.width ≤ k ∧ (C.Symmetric ∨ C.length = d * k + 1)

theorem first_le_last (C : Chain n d) : C.first ≤ C.last :=
  C.monotone_vertex (Fin.zero_le (Fin.last C.steps))

/-- Along a saturated chain, the rank is the initial rank plus the index. -/
theorem rank_vertex_eq (C : Chain n d) (hsaturated : C.Saturated)
    (i : Fin (C.steps + 1)) :
    Cube.rank (C.vertex i) = Cube.rank C.first + i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      calc
        Cube.rank (C.vertex i.succ) = Cube.rank (C.vertex i.castSucc) + 1 :=
          (hsaturated i).symm
        _ = Cube.rank C.first + (i.castSucc : ℕ) + 1 := by rw [ih]
        _ = Cube.rank C.first + i.succ := by
          simp only [Fin.val_castSucc, Fin.val_succ]
          rw [Nat.add_assoc]

theorem rank_last_eq (C : Chain n d) (hsaturated : C.Saturated) :
    Cube.rank C.last = Cube.rank C.first + C.steps := by
  simpa only [last, Fin.val_last] using rank_vertex_eq C hsaturated (Fin.last C.steps)

/-- A saturated chain of width `w` has at most `d * w + 1` vertices. -/
theorem length_le_width_mul_add_one (C : Chain n d) (hsaturated : C.Saturated) :
    C.length ≤ d * C.width + 1 := by
  have hrank := Cube.rank_sub_le_hammingDistance_mul C.first C.last C.first_le_last
  rw [rank_last_eq C hsaturated] at hrank
  simp only [Nat.add_sub_cancel_left] at hrank
  have hrank' := Nat.add_le_add_right hrank 1
  simpa only [length, width, Nat.mul_comm] using hrank'

/-- A saturated Boolean chain changes one new coordinate at each step, so its
width is exactly its number of steps. This is the corrected form of the
width/length assertion in Section 2 of the paper. -/
theorem width_eq_steps_of_saturated (C : Chain n 1) (hsaturated : C.Saturated) :
    C.width = C.steps := by
  rw [width, ← Cube.rank_sub_eq_hammingDistance C.first C.last C.first_le_last]
  rw [rank_last_eq C hsaturated]
  exact Nat.add_sub_cancel_left _ _

/-- Equivalently, a saturated Boolean chain has length `width + 1`. -/
theorem length_eq_width_add_one_of_saturated (C : Chain n 1) (hsaturated : C.Saturated) :
    C.length = C.width + 1 := by
  rw [length, width_eq_steps_of_saturated C hsaturated]

/-- For saturated chains, the paper's pointwise symmetry condition is
equivalent to the endpoint ranks adding to `n * d`. -/
theorem symmetric_iff_endpoint (C : Chain n d) (hsaturated : C.Saturated) :
    C.Symmetric ↔ Cube.rank C.first + Cube.rank C.last = n * d := by
  constructor
  · intro hsymmetric
    simpa only [Symmetric, first, last, Fin.rev_zero] using hsymmetric 0
  · intro hendpoints i
    rw [rank_vertex_eq C hsaturated i, rank_vertex_eq C hsaturated i.rev]
    rw [rank_last_eq C hsaturated] at hendpoints
    rw [Fin.val_rev]
    omega

theorem hammingDistance_vertex_le_width (C : Chain n d) (i j : Fin (C.steps + 1)) :
    Cube.hammingDistance (C.vertex i) (C.vertex j) ≤ C.width := by
  wlog hij : i ≤ j generalizing i j
  · rw [Cube.hammingDistance_comm]
    exact this j i (le_of_not_ge hij)
  change (Cube.differingCoordinates (C.vertex i) (C.vertex j)).card ≤
    (Cube.differingCoordinates C.first C.last).card
  apply Finset.card_le_card
  intro a ha
  simp only [Cube.differingCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  intro hendpoints
  have hfirst_i : C.first a ≤ C.vertex i a := C.monotone_vertex (Fin.zero_le i) a
  have hi_last : C.vertex i a ≤ C.last a := C.monotone_vertex (Fin.le_last i) a
  have hfirst_j : C.first a ≤ C.vertex j a := C.monotone_vertex (Fin.zero_le j) a
  have hj_last : C.vertex j a ≤ C.last a := C.monotone_vertex (Fin.le_last j) a
  have hi_eq : C.vertex i a = C.first a := by
    apply le_antisymm
    · simpa only [hendpoints] using hi_last
    · exact hfirst_i
  have hj_eq : C.vertex j a = C.first a := by
    apply le_antisymm
    · simpa only [hendpoints] using hj_last
    · exact hfirst_j
  exact ha (hi_eq.trans hj_eq.symm)

/-- A `k`-separated family meets a chain of width at most `k` in at most one
vertex. This is the chain observation used throughout Section 3. -/
theorem card_inter_vertices_le_one (C : Chain n d) (A : Finset (Cube n d)) (k : ℕ)
    (hseparated : Cube.KSeparated (A : Set (Cube n d)) k) (hwidth : C.width ≤ k) :
    (A ∩ C.vertices).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rcases (mem_vertices_iff C x).mp (Finset.mem_inter.mp hx).2 with ⟨i, rfl⟩
  rcases (mem_vertices_iff C y).mp (Finset.mem_inter.mp hy).2 with ⟨j, rfl⟩
  have hxi : C.vertex i ∈ A := (Finset.mem_inter.mp hx).1
  have hyj : C.vertex j ∈ A := (Finset.mem_inter.mp hy).1
  rcases le_total i j with hij | hji
  · by_contra hne
    have hfar := hseparated hxi hyj (C.monotone_vertex hij) hne
    have hnear := (hammingDistance_vertex_le_width C i j).trans hwidth
    omega
  · by_contra hne
    have hfar := hseparated hyj hxi (C.monotone_vertex hji) (Ne.symm hne)
    have hnear := (hammingDistance_vertex_le_width C j i).trans hwidth
    omega

end Chain

end WeightedChains
