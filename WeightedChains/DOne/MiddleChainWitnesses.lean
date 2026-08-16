import WeightedChains.DOne.Weights
import WeightedChains.DOne.MiddleUniqueness
import WeightedChains.DOne.ChainExistence

/-!
# Explicit Boolean chains at the middle layers

This file contains the zero-step and one-step represented Boolean chains used
in equality arguments.  It deliberately sits below `DOne.Main`: constructing
the witnesses and identifying their vertices does not depend on the Boolean
cardinality bound that they later help to sharpen.
-/

noncomputable section

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n : ℕ}

/-- The represented chain consisting of a single Boolean vertex. -/
def singletonChain (x : Cube n 1) : BooleanChain n :=
  ofStartWidth x 0 (by simpa using Cube.rank_le x)

@[simp]
theorem singletonChain_steps (x : Cube n 1) :
    ((singletonChain x).steps : ℕ) = 0 :=
  rfl

@[simp]
theorem singletonChain_first (x : Cube n 1) :
    (singletonChain x).toChain.first = x := by
  simp [singletonChain]

/-- A singleton descriptor has exactly the specified vertex. -/
@[simp]
theorem singletonChain_vertices (x : Cube n 1) :
    (singletonChain x).toChain.vertices = {x} := by
  ext y
  rw [Chain.mem_vertices_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    have hsteps : (singletonChain x).toChain.steps = 0 := rfl
    have hi : i = 0 := by
      have hival : (i : ℕ) = 0 := by
        have hilimit := i.isLt
        omega
      apply Fin.ext
      simpa [hsteps] using hival
    rw [hi]
    change (singletonChain x).toChain.first = x
    exact singletonChain_first x
  · intro hy
    subst y
    refine ⟨0, ?_⟩
    change (singletonChain x).toChain.first = x
    exact singletonChain_first x

/-- In even dimension, a zero-step descriptor at rank `n / 2` is good. -/
theorem singletonChain_isGood_of_even (x : Cube n 1) (k : ℕ)
    (heven : Even n) (hx : Cube.rank x = n / 2) :
    (singletonChain x).IsGood k := by
  unfold IsGood
  constructor
  · change (0 : ℕ) ≤ k
    omega
  · left
    change 2 * (finsetOfCube x).card + 0 = n
    rw [card_finsetOfCube, hx]
    simpa using Nat.two_mul_div_two_of_even heven

/-- A one-step represented chain obtained by adjoining one fresh coordinate
to a finite Boolean support. -/
def insertChain (s : Finset (Fin n)) (q : Fin n) (hq : q ∉ s) : BooleanChain n where
  steps := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_of_lt q.isLt)⟩
  start := s
  addition :=
    { toFun := fun _ ↦ q
      inj' := fun a b _ ↦ Subsingleton.elim a b }
  fresh := by
    rw [Finset.disjoint_left]
    intro z hzStart hzAddition
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hzAddition
    obtain ⟨i, rfl⟩ := hzAddition
    exact hq hzStart

@[simp]
theorem insertChain_steps (s : Finset (Fin n)) (q : Fin n) (hq : q ∉ s) :
    ((insertChain s q hq).steps : ℕ) = 1 :=
  rfl

@[simp]
theorem insertChain_first (s : Finset (Fin n)) (q : Fin n) (hq : q ∉ s) :
    (insertChain s q hq).toChain.first = cubeOfFinset s := by
  rw [(insertChain s q hq).toChain_first]
  rfl

@[simp]
theorem insertChain_support_last (s : Finset (Fin n)) (q : Fin n) (hq : q ∉ s) :
    (insertChain s q hq).support (Fin.last (insertChain s q hq).steps) =
      insert q s := by
  rw [support, added_last]
  ext z
  simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro (hz | ⟨i, hi⟩)
    · exact Or.inr hz
    · left
      change q = z at hi
      exact hi.symm
  · rintro (hzq | hz)
    · right
      have hpositive : 0 < ((insertChain s q hq).steps : ℕ) := by
        rw [insertChain_steps]
        omega
      let i : Fin (insertChain s q hq).steps := ⟨0, hpositive⟩
      refine ⟨i, ?_⟩
      change q = z
      exact hzq.symm
    · exact Or.inl hz

@[simp]
theorem insertChain_last (s : Finset (Fin n)) (q : Fin n) (hq : q ∉ s) :
    (insertChain s q hq).toChain.last = cubeOfFinset (insert q s) := by
  change cubeOfFinset
      ((insertChain s q hq).support (Fin.last (insertChain s q hq).steps)) = _
  rw [insertChain_support_last]

/-- The support of an upper Boolean neighbour is obtained by inserting one
coordinate into the support of the lower neighbour. -/
theorem exists_insert_finsetOfCube_eq_of_adjacent {x y : Cube n 1} {r : ℕ}
    (hx : Cube.rank x = r) (hy : Cube.rank y = r + 1) (hxy : x ≤ y) :
    ∃ q : Fin n, q ∉ finsetOfCube x ∧
      finsetOfCube y = insert q (finsetOfCube x) := by
  have hsubset : finsetOfCube x ⊆ finsetOfCube y := by
    simpa only [finsetOfCube, DOneMiddleUniqueness.ones] using
      (DOneMiddleUniqueness.le_iff_ones_subset.mp hxy)
  have hcard : (finsetOfCube x).card < (finsetOfCube y).card := by
    rw [card_finsetOfCube, card_finsetOfCube, hx, hy]
    omega
  obtain ⟨q, hqy, hqnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨q, hqnot, ?_⟩
  have hinsert : insert q (finsetOfCube x) ⊆ finsetOfCube y :=
    Finset.insert_subset hqy hsubset
  have heq : insert q (finsetOfCube x) = finsetOfCube y := by
    apply Finset.eq_of_subset_of_card_le hinsert
    rw [Finset.card_insert_of_notMem hqnot, card_finsetOfCube,
      card_finsetOfCube, hx, hy]
  exact heq.symm

/-- Every comparable pair in adjacent Boolean layers is the pair of endpoints
of an explicit represented one-step chain. -/
theorem exists_oneStepChain_of_adjacent {x y : Cube n 1} {r : ℕ}
    (hx : Cube.rank x = r) (hy : Cube.rank y = r + 1) (hxy : x ≤ y) :
    ∃ C : BooleanChain n,
      (C.steps : ℕ) = 1 ∧ C.toChain.first = x ∧ C.toChain.last = y := by
  obtain ⟨q, hqnot, hsupport⟩ :=
    exists_insert_finsetOfCube_eq_of_adjacent hx hy hxy
  let C := insertChain (finsetOfCube x) q hqnot
  refine ⟨C, by simp [C], ?_, ?_⟩
  · exact (insertChain_first (finsetOfCube x) q hqnot).trans
      (cubeOfFinset_finsetOfCube x)
  · rw [show C.toChain.last = cubeOfFinset (insert q (finsetOfCube x)) by simp [C]]
    rw [← hsupport, cubeOfFinset_finsetOfCube]

/-- A represented one-step chain contains exactly its two endpoints. -/
theorem vertices_eq_pair_of_steps_eq_one (C : BooleanChain n)
    (hsteps : (C.steps : ℕ) = 1) :
    C.toChain.vertices = {C.toChain.first, C.toChain.last} := by
  ext z
  rw [Chain.mem_vertices_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
      have hilimit : (i : ℕ) < (C.steps : ℕ) + 1 := i.isLt
      rw [hsteps] at hilimit
      omega
    rcases hi with hi | hi
    · have hieq : i = 0 := Fin.ext hi
      rw [hieq]
      exact Or.inl rfl
    · have hieq : i = Fin.last C.steps := by
        apply Fin.ext
        change (i : ℕ) = (C.steps : ℕ)
        omega
      rw [hieq]
      exact Or.inr rfl
  · intro hz
    rcases hz with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨Fin.last C.steps, rfl⟩

/-- In odd dimension, every one-step chain between the two middle layers is
good (it is symmetric about the half-integral middle rank). -/
theorem oneStepChain_isGood_of_odd (C : BooleanChain n) (k : ℕ)
    (hk : 0 < k) (hodd : Odd n) (hsteps : (C.steps : ℕ) = 1)
    (hfirst : Cube.rank C.toChain.first = n / 2) :
    C.IsGood k := by
  unfold IsGood
  constructor
  · rw [hsteps]
    omega
  · left
    calc
      2 * C.start.card + (C.steps : ℕ) = 2 * (n / 2) + 1 := by
        rw [← C.rank_toChain_first, hfirst, hsteps]
      _ = n := Nat.two_mul_div_two_add_one_of_odd hodd

/-- A finite family which meets a two-point set exactly once contains one
point precisely when it omits the other. -/
theorem mem_iff_not_mem_of_inter_pair_card_eq_one
    (candidate : Finset (Cube n 1)) {x y : Cube n 1} (hxy : x ≠ y)
    (hcard : (candidate ∩ {x, y}).card = 1) :
    x ∈ candidate ↔ y ∉ candidate := by
  by_cases hx : x ∈ candidate <;> by_cases hy : y ∈ candidate <;>
    simp [hx, hy, hxy] at hcard ⊢

end BooleanChain
end DOne
end WeightedChains
