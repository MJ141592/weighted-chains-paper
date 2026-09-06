import Mathlib

/-!
# Comparator challenge

The statement of the main theorem of *A generalisation of Sperner's theorem
using weighted chain decomposition*, together with every definition it
mentions, in a module whose transitive import closure is Lean core and mathlib
only.

The definitions below are copied verbatim from the project modules
`WeightedChains.Preliminaries` and `WeightedChains.GoodChainResidues`, and the
theorem statement from `WeightedChains.MainTheorem`, so that the corresponding
declarations of the solution environment are the same declarations.

See `comparator.json` for the [Comparator](https://github.com/leanprover/comparator)
configuration and `Solution.lean` for the proved counterpart.
-/

namespace WeightedChains

/-- The discrete cube `{0, ..., d}^n`. -/
abbrev Cube (n d : ℕ) := Fin n → Fin (d + 1)

namespace Cube

/-- The layer (or rank) of a vertex: the sum of its coordinates. -/
def rank {n d : ℕ} (x : Cube n d) : ℕ := ∑ i, (x i : ℕ)

/-- The coordinates on which two vertices differ. -/
def differingCoordinates {n d : ℕ} (x y : Cube n d) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ x i ≠ y i

/-- The number of coordinates on which two vertices differ (the Hamming distance). -/
def hammingDistance {n d : ℕ} (x y : Cube n d) : ℕ :=
  (differingCoordinates x y).card

/-- A family is `k`-separated when distinct comparable members differ in more
than `k` coordinates. The distinctness condition is implicit in the paper and
is necessary for the definition to generalise antichains. -/
def KSeparated {n d : ℕ} (A : Set (Cube n d)) (k : ℕ) : Prop :=
  ∀ {x y : Cube n d}, x ∈ A → y ∈ A → x ≤ y → x ≠ y → k < hammingDistance x y

/-- The lower of the one or two middle ranks. -/
def lowerMiddleRank (n d : ℕ) : ℕ := n * d / 2

/-- The upper of the one or two middle ranks. -/
def upperMiddleRank (n d : ℕ) : ℕ := n * d - lowerMiddleRank n d

/-- Finite version of the paper's lower residue family: the vertices whose rank
is congruent to the lower middle rank modulo `d * k + 1`. -/
def lowerResidueFinset (n d k : ℕ) : Finset (Cube n d) :=
  Finset.univ.filter fun x ↦ rank x ≡ lowerMiddleRank n d [MOD d * k + 1]

/-- Finite version of the paper's upper residue family: the vertices whose rank
is congruent to the upper middle rank modulo `d * k + 1`. -/
def upperResidueFinset (n d k : ℕ) : Finset (Cube n d) :=
  Finset.univ.filter fun x ↦ rank x ≡ upperMiddleRank n d [MOD d * k + 1]

end Cube

/-- The paper's main cardinality and equality-classification theorem.  Every
`k`-separated family in dimension `d = 1` or `d = 2` is bounded by the lower
rank-residue family, and equality gives one of the two reflected residue
families.  When `d = 2` those two families coincide. -/
theorem main_cardinality_and_uniqueness
    (n k d : ℕ) (hk : 1 < k) (hkn : k ≤ n) (hd : d = 1 ∨ d = 2)
    (candidate : Finset (Cube n d))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n d k).card ∧
      (candidate.card = (Cube.lowerResidueFinset n d k).card ↔
        candidate = Cube.lowerResidueFinset n d k ∨
          candidate = Cube.upperResidueFinset n d k) :=
  sorry

end WeightedChains
