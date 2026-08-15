import WeightedChains.DOne.Main
import WeightedChains.DOne.ChainExistence
import WeightedChains.UniquenessPropagation
import WeightedChains.GoodChainResidues
import WeightedChains.ResidueSymmetry

/-!
# Equality propagation in the Boolean cube

After the choice on the middle layer (or the two middle layers), exact-one
incidence with every represented good chain determines all remaining layers.
The induction order first moves outwards from the middle and, within one
distance shell, treats nonmembers of the lower residue family before members.
This second tie-break is needed for symmetric chains, whose two endpoints can
be equally far from the middle.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n k : ℕ}

/-- A represented good chain directed from a lower-side vertex towards the
middle.  In an outer layer it has full width `k`; in an inner layer it is the
unique symmetric rank interval beginning at `x`. -/
def towardMiddleFromBelow (x : Cube n 1) (k : ℕ)
    (hlower : 2 * Cube.rank x ≤ n) : BooleanChain n :=
  if houter : 2 * Cube.rank x + k ≤ n then
    ofStartWidth x k (by omega)
  else
    ofStartWidth x (n - 2 * Cube.rank x) (by omega)

@[simp]
theorem towardMiddleFromBelow_first (x : Cube n 1) (k : ℕ)
    (hlower : 2 * Cube.rank x ≤ n) :
    (towardMiddleFromBelow x k hlower).toChain.first = x := by
  unfold towardMiddleFromBelow
  split_ifs with houter <;> apply ofStartWidth_first

theorem towardMiddleFromBelow_steps_le (x : Cube n 1) (k : ℕ)
    (hlower : 2 * Cube.rank x ≤ n) :
    (towardMiddleFromBelow x k hlower).steps ≤ k := by
  unfold towardMiddleFromBelow
  split_ifs with houter
  · simp
  · simp
    omega

theorem towardMiddleFromBelow_starting_condition (x : Cube n 1) (k : ℕ)
    (hlower : 2 * Cube.rank x ≤ n) :
    2 * (towardMiddleFromBelow x k hlower).start.card +
        (towardMiddleFromBelow x k hlower).steps ≤ n := by
  unfold towardMiddleFromBelow
  split_ifs with houter
  · simpa using houter
  · simp
    omega

theorem towardMiddleFromBelow_good (x : Cube n 1) (k : ℕ)
    (hlower : 2 * Cube.rank x ≤ n) :
    (towardMiddleFromBelow x k hlower).toChain.Good k := by
  rw [(towardMiddleFromBelow x k hlower).good_toChain_iff]
  refine ⟨towardMiddleFromBelow_steps_le x k hlower, ?_⟩
  unfold towardMiddleFromBelow
  split_ifs with houter
  · exact Or.inr (by simp)
  · left
    simp
    omega

/-- Every vertex of a Boolean chain whose first endpoint is paper-oriented
towards the middle is no farther from the middle than that endpoint. -/
theorem middleDistance_vertex_le_of_starting_condition (C : BooleanChain n)
    (hlower : 2 * C.start.card ≤ n)
    (hstart : 2 * C.start.card + C.steps ≤ n)
    (i : Fin (C.steps + 1)) :
    Cube.middleDistance (C.vertex i) ≤ Cube.middleDistance C.toChain.first := by
  unfold Cube.middleDistance
  simp only [Nat.mul_one, C.rank_vertex, C.rank_toChain_first]
  rw [Nat.dist_eq_sub_of_le hlower]
  have hi : (i : ℕ) ≤ C.steps := by omega
  by_cases hside : 2 * (C.start.card + (i : ℕ)) ≤ n
  · rw [Nat.dist_eq_sub_of_le hside]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

theorem towardMiddleFromBelow_middleDistance_vertex_le
    (x : Cube n 1) (k : ℕ) (hlower : 2 * Cube.rank x ≤ n)
    (i : Fin ((towardMiddleFromBelow x k hlower).steps + 1)) :
    Cube.middleDistance ((towardMiddleFromBelow x k hlower).vertex i) ≤
      Cube.middleDistance x := by
  calc
    Cube.middleDistance ((towardMiddleFromBelow x k hlower).vertex i) ≤
        Cube.middleDistance (towardMiddleFromBelow x k hlower).toChain.first :=
      middleDistance_vertex_le_of_starting_condition
        (towardMiddleFromBelow x k hlower)
        (by
          rw [← (towardMiddleFromBelow x k hlower).rank_toChain_first,
            towardMiddleFromBelow_first]
          exact hlower)
        (towardMiddleFromBelow_starting_condition x k hlower) i
    _ = Cube.middleDistance x := by
      rw [towardMiddleFromBelow_first]

/-- Coordinate reflection preserves distance from the middle in the Boolean
cube. -/
theorem middleDistance_reflect (x : Cube n 1) :
    Cube.middleDistance (Cube.reflect x) = Cube.middleDistance x := by
  unfold Cube.middleDistance
  rw [Cube.rank_reflect]
  simp only [Nat.mul_one]
  exact dist_two_complement (by simpa using Cube.rank_le x)

/-- The upper-side version of `towardMiddleFromBelow`, obtained by reversing
and complementing its lower-side construction. -/
def towardMiddleFromAbove (x : Cube n 1) (k : ℕ)
    (hupper : n ≤ 2 * Cube.rank x) : BooleanChain n :=
  let xr := Cube.reflect x
  let hlower : 2 * Cube.rank xr ≤ n := by
    rw [Cube.rank_reflect]
    have hrank := Cube.rank_le x
    simp only [Nat.mul_one]
    omega
  (towardMiddleFromBelow xr k hlower).reflect

@[simp]
theorem towardMiddleFromAbove_last (x : Cube n 1) (k : ℕ)
    (hupper : n ≤ 2 * Cube.rank x) :
    (towardMiddleFromAbove x k hupper).toChain.last = x := by
  unfold towardMiddleFromAbove
  let hlower : 2 * Cube.rank (Cube.reflect x) ≤ n := by
    rw [Cube.rank_reflect]
    have hrank := Cube.rank_le x
    simp only [Nat.mul_one]
    omega
  let C := towardMiddleFromBelow (Cube.reflect x) k hlower
  change C.reflect.vertex (Fin.last C.steps) = x
  rw [C.vertex_reflect]
  have hrev : (Fin.last C.steps).rev = (0 : Fin (C.steps + 1)) := by
    apply Fin.ext
    simp
  rw [hrev]
  change Cube.reflect C.toChain.first = x
  rw [towardMiddleFromBelow_first, Cube.reflect_reflect]

theorem towardMiddleFromAbove_good (x : Cube n 1) (k : ℕ)
    (hupper : n ≤ 2 * Cube.rank x) :
    (towardMiddleFromAbove x k hupper).toChain.Good k := by
  unfold towardMiddleFromAbove
  rw [good_reflect_iff]
  apply towardMiddleFromBelow_good

theorem towardMiddleFromAbove_middleDistance_vertex_le
    (x : Cube n 1) (k : ℕ) (hupper : n ≤ 2 * Cube.rank x)
    (i : Fin ((towardMiddleFromAbove x k hupper).steps + 1)) :
    Cube.middleDistance ((towardMiddleFromAbove x k hupper).vertex i) ≤
      Cube.middleDistance x := by
  unfold towardMiddleFromAbove at i ⊢
  let xr := Cube.reflect x
  let hlower : 2 * Cube.rank xr ≤ n := by
    dsimp [xr]
    rw [Cube.rank_reflect]
    have hrank := Cube.rank_le x
    simp only [Nat.mul_one]
    omega
  let C := towardMiddleFromBelow xr k hlower
  change Cube.middleDistance (C.reflect.vertex i) ≤ Cube.middleDistance x
  rw [show C.reflect.vertex i = Cube.reflect (C.vertex i.rev) from C.vertex_reflect i,
    middleDistance_reflect]
  calc
    Cube.middleDistance (C.vertex i.rev) ≤ Cube.middleDistance xr :=
      towardMiddleFromBelow_middleDistance_vertex_le xr k hlower i.rev
    _ = Cube.middleDistance x := middleDistance_reflect x

/-- The selected directed good chain through an arbitrary Boolean vertex. -/
def towardMiddle (x : Cube n 1) (k : ℕ) : BooleanChain n :=
  if hlower : 2 * Cube.rank x ≤ n then
    towardMiddleFromBelow x k hlower
  else
    towardMiddleFromAbove x k (by omega)

theorem towardMiddle_good (x : Cube n 1) (k : ℕ) :
    (towardMiddle x k).toChain.Good k := by
  unfold towardMiddle
  split_ifs with hlower
  · exact towardMiddleFromBelow_good x k hlower
  · exact towardMiddleFromAbove_good x k (by omega)

theorem mem_towardMiddle_vertices (x : Cube n 1) (k : ℕ) :
    x ∈ (towardMiddle x k).toChain.vertices := by
  unfold towardMiddle
  split_ifs with hlower
  · let C := towardMiddleFromBelow x k hlower
    change x ∈ C.toChain.vertices
    have hfirst : C.toChain.first = x := towardMiddleFromBelow_first x k hlower
    rw [Chain.mem_vertices_iff]
    exact ⟨0, hfirst⟩
  · have hupper : n ≤ 2 * Cube.rank x := by omega
    let C := towardMiddleFromAbove x k hupper
    change x ∈ C.toChain.vertices
    have hlast : C.toChain.last = x := towardMiddleFromAbove_last x k hupper
    rw [Chain.mem_vertices_iff]
    exact ⟨Fin.last C.steps, hlast⟩

theorem towardMiddle_middleDistance_le_of_mem (x : Cube n 1) (k : ℕ)
    {y : Cube n 1} (hy : y ∈ (towardMiddle x k).toChain.vertices) :
    Cube.middleDistance y ≤ Cube.middleDistance x := by
  unfold towardMiddle at hy
  split_ifs at hy with hlower
  · rw [Chain.mem_vertices_iff] at hy
    obtain ⟨i, rfl⟩ := hy
    exact towardMiddleFromBelow_middleDistance_vertex_le x k hlower i
  · rw [Chain.mem_vertices_iff] at hy
    obtain ⟨i, rfl⟩ := hy
    exact towardMiddleFromAbove_middleDistance_vertex_le x k (by omega) i

/-- Two vertices of one represented chain have rank distance at most the
chain's number of steps. -/
theorem rank_dist_le_steps_of_mem_vertices (C : BooleanChain n)
    {x y : Cube n 1} (hx : x ∈ C.toChain.vertices)
    (hy : y ∈ C.toChain.vertices) :
    (Cube.rank x).dist (Cube.rank y) ≤ C.steps := by
  rw [Chain.mem_vertices_iff] at hx hy
  change (∃ i : Fin (C.steps + 1), C.vertex i = x) at hx
  change (∃ i : Fin (C.steps + 1), C.vertex i = y) at hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  rw [C.rank_vertex, C.rank_vertex]
  have hi : (i : ℕ) ≤ C.steps := by omega
  have hj : (j : ℕ) ≤ C.steps := by omega
  rw [Nat.dist_add_add_left]
  unfold Nat.dist
  omega

/-- A noncentral lower-residue vertex cannot be tied in middle-distance to a
non-residue vertex less than `k + 1` ranks away.  This is the arithmetic fact
which makes the strict outward witness in the paper valid even for symmetric
chains. -/
theorem middleDistance_ne_of_lowerResidue_of_not_mem
    (hk : 0 < k) {x y : Cube n 1}
    (hxcentral : 1 < Cube.middleDistance x)
    (hx : x ∉ Cube.lowerResidueFinset n 1 k)
    (hy : y ∈ Cube.lowerResidueFinset n 1 k)
    (hrank : (Cube.rank x).dist (Cube.rank y) ≤ k) :
    Cube.middleDistance y ≠ Cube.middleDistance x := by
  intro heq
  have hxRank := Cube.rank_le x
  have hyRank := Cube.rank_le y
  have hyMod : Cube.rank y ≡ n / 2 [MOD k + 1] := by
    simpa [Cube.lowerResidueFinset, Cube.lowerMiddleRank] using hy
  have hxMod : ¬Cube.rank x ≡ n / 2 [MOD k + 1] := by
    simpa [Cube.lowerResidueFinset, Cube.lowerMiddleRank] using hx
  have hrankNe : Cube.rank x ≠ Cube.rank y := by
    intro h
    apply hxMod
    rw [h]
    exact hyMod
  have hmiddleEq :
      (2 * Cube.rank y).dist n = (2 * Cube.rank x).dist n := by
    simpa [Cube.middleDistance] using heq
  by_cases hyLower : 2 * Cube.rank y ≤ n
  · rw [Nat.dist_eq_sub_of_le hyLower] at hmiddleEq
    by_cases hxLower : 2 * Cube.rank x ≤ n
    · rw [Nat.dist_eq_sub_of_le hxLower] at hmiddleEq
      exact hrankNe (by omega)
    · rw [Nat.dist_eq_sub_of_le_right (by omega)] at hmiddleEq
      have hyBelow : Cube.rank y ≤ n / 2 := by omega
      have hyNotMiddle : Cube.rank y ≠ n / 2 := by
        intro hym
        have hyCentral : Cube.middleDistance y ≤ 1 := by
          unfold Cube.middleDistance
          simp only [Nat.mul_one, hym]
          have hhalf : 2 * (n / 2) ≤ n := by omega
          rw [Nat.dist_eq_sub_of_le hhalf]
          omega
        rw [← heq] at hxcentral
        omega
      have hpositive : 0 < n / 2 - Cube.rank y := by omega
      have hdiv : k + 1 ∣ n / 2 - Cube.rank y := hyMod.dvd'
      have hlower : k + 1 ≤ n / 2 - Cube.rank y :=
        Nat.le_of_dvd hpositive hdiv
      rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega : Cube.rank y ≤ Cube.rank x)] at hrank
      omega
  · have hyUpper : n ≤ 2 * Cube.rank y := by omega
    rw [Nat.dist_eq_sub_of_le_right hyUpper] at hmiddleEq
    by_cases hxUpper : n ≤ 2 * Cube.rank x
    · rw [Nat.dist_eq_sub_of_le_right hxUpper] at hmiddleEq
      exact hrankNe (by omega)
    · rw [Nat.dist_eq_sub_of_le (by omega)] at hmiddleEq
      have hyAbove : n / 2 ≤ Cube.rank y := by omega
      have hyNotMiddle : Cube.rank y ≠ n / 2 := by
        intro hym
        omega
      have hpositive : 0 < Cube.rank y - n / 2 := by omega
      have hdiv : k + 1 ∣ Cube.rank y - n / 2 := hyMod.symm.dvd'
      have hlower : k + 1 ≤ Cube.rank y - n / 2 :=
        Nat.le_of_dvd hpositive hdiv
      rw [Nat.dist_eq_sub_of_le (by omega : Cube.rank x ≤ Cube.rank y)] at hrank
      omega

/-- In the Boolean cube, `middleDistance ≤ 1` is exactly the middle layer
when `n` is even and exactly the two adjacent middle layers when `n` is odd. -/
theorem middleDistance_le_one_iff_rank_eq_middle (x : Cube n 1) :
    Cube.middleDistance x ≤ 1 ↔
      Cube.rank x = Cube.lowerMiddleRank n 1 ∨
        Cube.rank x = Cube.upperMiddleRank n 1 := by
  have hrank : Cube.rank x ≤ n := by simpa using Cube.rank_le x
  unfold Cube.middleDistance Cube.lowerMiddleRank Cube.upperMiddleRank
  simp only [Cube.lowerMiddleRank, Nat.mul_one]
  constructor
  · intro hmiddle
    by_cases hlower : 2 * Cube.rank x ≤ n
    · rw [Nat.dist_eq_sub_of_le hlower] at hmiddle
      left
      omega
    · rw [Nat.dist_eq_sub_of_le_right (by omega)] at hmiddle
      right
      omega
  · rintro (hlower | hupper)
    · rw [hlower]
      have hhalf : 2 * (n / 2) ≤ n := by omega
      rw [Nat.dist_eq_sub_of_le hhalf]
      omega
    · rw [hupper]
      by_cases hevenSide : 2 * (n - n / 2) ≤ n
      · rw [Nat.dist_eq_sub_of_le hevenSide]
        omega
      · rw [Nat.dist_eq_sub_of_le_right (by omega)]
        omega

/-- The induction order: the central layer(s) have distance zero; outside
them, distance from the middle is primary and lower-residue membership is the
secondary bit. -/
def lowerResiduePropagationDistance (n k : ℕ) (x : Cube n 1) : ℕ :=
  if Cube.middleDistance x ≤ 1 then 0
  else 2 * Cube.middleDistance x +
    if x ∈ Cube.lowerResidueFinset n 1 k then 1 else 0

theorem lowerResiduePropagationDistance_eq_zero_of_middle
    {x : Cube n 1} (hx : Cube.middleDistance x ≤ 1) :
    lowerResiduePropagationDistance n k x = 0 := by
  simp [lowerResiduePropagationDistance, hx]

theorem middleDistance_gt_one_of_propagationDistance_pos
    {x : Cube n 1} (hx : 0 < lowerResiduePropagationDistance n k x) :
    1 < Cube.middleDistance x := by
  by_contra hmiddle
  have hle : Cube.middleDistance x ≤ 1 := by omega
  rw [lowerResiduePropagationDistance_eq_zero_of_middle hle] at hx
  omega

theorem lowerResiduePropagationDistance_lt_of_middleDistance_lt
    {x y : Cube n 1} (hxoutside : 1 < Cube.middleDistance x)
    (hyx : Cube.middleDistance y < Cube.middleDistance x) :
    lowerResiduePropagationDistance n k y <
      lowerResiduePropagationDistance n k x := by
  unfold lowerResiduePropagationDistance
  split_ifs with hyMiddle hxMiddle hyResidue hxResidue <;> omega

theorem lowerResiduePropagationDistance_lt_of_tie
    {x y : Cube n 1} (houtside : 1 < Cube.middleDistance x)
    (htie : Cube.middleDistance y = Cube.middleDistance x)
    (hx : x ∈ Cube.lowerResidueFinset n 1 k)
    (hy : y ∉ Cube.lowerResidueFinset n 1 k) :
    lowerResiduePropagationDistance n k y <
      lowerResiduePropagationDistance n k x := by
  simp [lowerResiduePropagationDistance, hx, hy, htie, not_le_of_gt houtside]

/-- A directed good-chain witness for a member of the lower residue family:
all its other vertices occur earlier in the propagation order and are outside
the reference family. -/
theorem exists_towardMiddle_witness_of_mem_lowerResidue
    (x : Cube n 1) (hx : x ∈ Cube.lowerResidueFinset n 1 k)
    (hpositive : 0 < lowerResiduePropagationDistance n k x) :
    ∃ C : BooleanChain n,
      C.toChain.Good k ∧ x ∈ C.toChain.vertices ∧
      ∀ y ∈ C.toChain.vertices, y ≠ x →
        lowerResiduePropagationDistance n k y <
            lowerResiduePropagationDistance n k x ∧
          y ∉ Cube.lowerResidueFinset n 1 k := by
  let C := towardMiddle x k
  refine ⟨C, towardMiddle_good x k, mem_towardMiddle_vertices x k, ?_⟩
  intro y hyC hyx
  have hreferenceCard :=
    (towardMiddle_good x k).card_lowerResidueFinset_inter_vertices C.toChain
  have hyNotReference : y ∉ Cube.lowerResidueFinset n 1 k := by
    exact WeightedCover.not_mem_of_mem_of_inter_card_eq_one
      hreferenceCard hx (mem_towardMiddle_vertices x k) hyC hyx
  refine ⟨?_, hyNotReference⟩
  have hle := towardMiddle_middleDistance_le_of_mem x k hyC
  rcases hle.eq_or_lt with htie | hlt
  · exact lowerResiduePropagationDistance_lt_of_tie
      (middleDistance_gt_one_of_propagationDistance_pos hpositive) htie hx hyNotReference
  · exact lowerResiduePropagationDistance_lt_of_middleDistance_lt
      (middleDistance_gt_one_of_propagationDistance_pos hpositive) hlt

/-- A directed good-chain witness for a nonmember of the lower residue
family: the chain's unique reference vertex is strictly closer to the middle,
and hence occurs earlier in the propagation order. -/
theorem exists_towardMiddle_witness_of_not_mem_lowerResidue
    (hk : 0 < k) (x : Cube n 1)
    (hx : x ∉ Cube.lowerResidueFinset n 1 k)
    (hpositive : 0 < lowerResiduePropagationDistance n k x) :
    ∃ C : BooleanChain n,
      C.toChain.Good k ∧ x ∈ C.toChain.vertices ∧
      ∃ y ∈ C.toChain.vertices,
        y ∈ Cube.lowerResidueFinset n 1 k ∧
        lowerResiduePropagationDistance n k y <
          lowerResiduePropagationDistance n k x := by
  let C := towardMiddle x k
  have hgood : C.toChain.Good k := towardMiddle_good x k
  obtain ⟨y, hyC, hyReference⟩ := hgood.exists_mem_lowerResidueFinset C.toChain
  refine ⟨C, hgood, mem_towardMiddle_vertices x k, y, hyC, hyReference, ?_⟩
  have hle : Cube.middleDistance y ≤ Cube.middleDistance x :=
    towardMiddle_middleDistance_le_of_mem x k hyC
  have hne : Cube.middleDistance y ≠ Cube.middleDistance x := by
    apply middleDistance_ne_of_lowerResidue_of_not_mem hk
      (middleDistance_gt_one_of_propagationDistance_pos hpositive) hx hyReference
    exact (rank_dist_le_steps_of_mem_vertices C
      (mem_towardMiddle_vertices x k) hyC).trans (by simpa using hgood.2.1)
  exact lowerResiduePropagationDistance_lt_of_middleDistance_lt
    (middleDistance_gt_one_of_propagationDistance_pos hpositive)
    (lt_of_le_of_ne hle hne)

/-- Exact-one incidence with all represented good Boolean chains propagates
agreement on the middle layer(s) to the entire cube. -/
theorem eq_lowerResidueFinset_of_exact_one_of_middle_agreement
    (hk : 0 < k) (candidate : Finset (Cube n 1))
    (hexact : ∀ C : BooleanChain n, C.toChain.Good k →
      (candidate ∩ C.toChain.vertices).card = 1)
    (hmiddle : ∀ x : Cube n 1, Cube.middleDistance x ≤ 1 →
      (x ∈ candidate ↔ x ∈ Cube.lowerResidueFinset n 1 k)) :
    candidate = Cube.lowerResidueFinset n 1 k := by
  apply UniquenessPropagation.finset_eq_of_exact_one_outward_induction
    (fun i : GoodIndex n k ↦ i.1.toChain.vertices)
    (Cube.lowerResidueFinset n 1 k) candidate
    (lowerResiduePropagationDistance n k)
  · intro i
    exact hexact i.1 ((i.1.isGood_iff k).mp i.2)
  · intro x hzero
    apply hmiddle x
    by_contra houtside
    have hgt : 1 < Cube.middleDistance x := by omega
    rw [lowerResiduePropagationDistance] at hzero
    simp [not_le_of_gt hgt] at hzero
    omega
  · intro x hx hpositive
    obtain ⟨C, _hgood, hxC, hother⟩ :=
      exists_towardMiddle_witness_of_mem_lowerResidue x hx hpositive
    exact ⟨⟨C, (C.isGood_iff k).mpr _hgood⟩, hxC, hother⟩
  · intro x hx hpositive
    obtain ⟨C, _hgood, hxC, y, hyC, hyReference, hyDistance⟩ :=
      exists_towardMiddle_witness_of_not_mem_lowerResidue hk x hx hpositive
    exact ⟨⟨C, (C.isGood_iff k).mpr _hgood⟩, hxC, y, hyC,
      hyReference, hyDistance⟩

/-- Rank-form version of the propagation theorem.  Its hypothesis says
directly that the candidate makes the lower-family choice on the middle
rank(s). -/
theorem eq_lowerResidueFinset_of_exact_one_of_middle_rank_agreement
    (hk : 0 < k) (candidate : Finset (Cube n 1))
    (hexact : ∀ C : BooleanChain n, C.toChain.Good k →
      (candidate ∩ C.toChain.vertices).card = 1)
    (hmiddle : ∀ x : Cube n 1,
      (Cube.rank x = Cube.lowerMiddleRank n 1 ∨
        Cube.rank x = Cube.upperMiddleRank n 1) →
      (x ∈ candidate ↔ x ∈ Cube.lowerResidueFinset n 1 k)) :
    candidate = Cube.lowerResidueFinset n 1 k := by
  apply eq_lowerResidueFinset_of_exact_one_of_middle_agreement hk candidate hexact
  intro x hx
  exact hmiddle x ((middleDistance_le_one_iff_rank_eq_middle x).mp hx)

/-- Equality in the Boolean weighted-chain bound, together with the lower
middle-layer choice, forces the lower residue family. -/
theorem eq_lowerResidueFinset_of_card_eq_of_middle_agreement
    (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (candidate : Finset (Cube n 1))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n 1)) k)
    (hcard : candidate.card = (Cube.lowerResidueFinset n 1 k).card)
    (hmiddle : ∀ x : Cube n 1, Cube.middleDistance x ≤ 1 →
      (x ∈ candidate ↔ x ∈ Cube.lowerResidueFinset n 1 k)) :
    candidate = Cube.lowerResidueFinset n 1 k := by
  apply eq_lowerResidueFinset_of_exact_one_of_middle_agreement hk.le candidate
  · intro C hgood
    exact inter_goodChain_card_eq_one_of_card_eq k n hk hkn candidate
      hcandidate hcard C ((C.isGood_iff k).2 hgood)
  · exact hmiddle

end BooleanChain
end DOne
end WeightedChains
