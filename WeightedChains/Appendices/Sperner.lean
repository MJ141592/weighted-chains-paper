import WeightedChains.DOne.MiddleChainWitnesses
import WeightedChains.WeightedUniqueness

/-!
# Appendix 1: the weighted symmetric-chain proof of Sperner's theorem

This file packages Appendix 1 as the specialization `d = 1`, `k = n` of the
weighted-chain construction.  In this specialization the good represented
Boolean chains are exactly the saturated symmetric chains.  Their weights are
positive (away from the two elementary dimensions), every Boolean vertex has
total incident weight one, and an antichain meets each chain at most once.

The final theorem includes the elementary dimensions `n = 0, 1` and states
both Sperner's cardinality bound and the appendix's classification of equality.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace SpernerAppendix

open DOne

variable {n : ℕ}

/-- A family of subsets of `[n]` is an antichain when comparable members are
equal.  Boolean-cube vertices are the indicator functions of those subsets. -/
def Antichain {n : ℕ} (A : Set (Cube n 1)) : Prop :=
  ∀ ⦃x y : Cube n 1⦄, x ∈ A → y ∈ A → x ≤ y → x = y

/-- Every Hamming distance in the `n`-dimensional cube is at most `n`. -/
theorem hammingDistance_le (x y : Cube n 1) : Cube.hammingDistance x y ≤ n := by
  simpa [Cube.hammingDistance] using
    Finset.card_le_univ (Cube.differingCoordinates x y)

/-- The appendix's antichain condition is exactly `n`-separation. -/
theorem antichain_iff_nSeparated {A : Set (Cube n 1)} :
    Antichain A ↔ Cube.KSeparated A n := by
  constructor
  · intro hA x y hx hy hxy hne
    exact False.elim (hne (hA hx hy hxy))
  · intro hA x y hx hy hxy
    by_contra hne
    have hfar := hA hx hy hxy hne
    exact (Nat.not_lt_of_ge (hammingDistance_le x y)) hfar

/-- The lower middle layer, denoted `A₁` in the appendix. -/
def lowerMiddleLayer (n : ℕ) : Finset (Cube n 1) :=
  DOne.booleanLayerFinset n (n / 2)

/-- The upper middle layer, denoted `A₂` in the appendix. -/
def upperMiddleLayer (n : ℕ) : Finset (Cube n 1) :=
  DOne.booleanLayerFinset n (n - n / 2)

@[simp]
theorem mem_lowerMiddleLayer_iff {x : Cube n 1} :
    x ∈ lowerMiddleLayer n ↔ Cube.rank x = n / 2 := by
  exact DOne.mem_booleanLayerFinset_iff

@[simp]
theorem mem_upperMiddleLayer_iff {x : Cube n 1} :
    x ∈ upperMiddleLayer n ↔ Cube.rank x = n - n / 2 := by
  exact DOne.mem_booleanLayerFinset_iff

@[simp]
theorem card_lowerMiddleLayer (n : ℕ) :
    (lowerMiddleLayer n).card = n.choose (n / 2) := by
  simp [lowerMiddleLayer]

@[simp]
theorem card_upperMiddleLayer (n : ℕ) :
    (upperMiddleLayer n).card = n.choose (n / 2) := by
  rw [upperMiddleLayer, DOne.card_booleanLayerFinset]
  exact Nat.choose_symm (Nat.div_le_self n 2)

/-- Any single rank layer is an antichain. -/
theorem antichain_booleanLayerFinset (n r : ℕ) :
    Antichain (DOne.booleanLayerFinset n r : Set (Cube n 1)) := by
  intro x y hx hy hxy
  by_contra hne
  have hstrict := Cube.rank_strictMono hxy hne
  have hxrank := DOne.mem_booleanLayerFinset_iff.mp hx
  have hyrank := DOne.mem_booleanLayerFinset_iff.mp hy
  omega

theorem antichain_lowerMiddleLayer (n : ℕ) :
    Antichain (lowerMiddleLayer n : Set (Cube n 1)) :=
  antichain_booleanLayerFinset n (n / 2)

theorem antichain_upperMiddleLayer (n : ℕ) :
    Antichain (upperMiddleLayer n : Set (Cube n 1)) :=
  antichain_booleanLayerFinset n (n - n / 2)

/-- With modulus `n + 1`, the lower residue family consists of just the lower
middle rank. -/
theorem lowerResidueFinset_self_eq_lowerMiddleLayer (n : ℕ) :
    Cube.lowerResidueFinset n 1 n = lowerMiddleLayer n := by
  ext x
  simp only [Cube.lowerResidueFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Cube.lowerMiddleRank, Nat.one_mul, Nat.mul_one,
    mem_lowerMiddleLayer_iff]
  unfold Nat.ModEq
  have hx : Cube.rank x < n + 1 := by
    have hxle : Cube.rank x ≤ n := by
      simpa only [Nat.mul_one] using Cube.rank_le x
    omega
  have hm : n / 2 < n + 1 := by omega
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hm]

/-- With modulus `n + 1`, the upper residue family consists of just the upper
middle rank. -/
theorem upperResidueFinset_self_eq_upperMiddleLayer (n : ℕ) :
    Cube.upperResidueFinset n 1 n = upperMiddleLayer n := by
  ext x
  simp only [Cube.upperResidueFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Cube.upperMiddleRank, Cube.lowerMiddleRank, Nat.one_mul,
    Nat.mul_one, mem_upperMiddleLayer_iff]
  unfold Nat.ModEq
  have hx : Cube.rank x < n + 1 := by
    have hxle : Cube.rank x ≤ n := by
      simpa only [Nat.mul_one] using Cube.rank_le x
    omega
  have hm : n - n / 2 < n + 1 := by omega
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hm]

namespace SymmetricChain

open DOne.BooleanChain

/-- At `k = n`, the represented good chains are precisely the appendix's
saturated symmetric chains. -/
theorem isGood_self_iff_symmetric (C : DOne.BooleanChain n) :
    C.IsGood n ↔ C.toChain.Symmetric := by
  rw [C.symmetric_toChain_iff]
  constructor
  · rintro ⟨_hsteps, hsym | hfull⟩
    · exact hsym
    · have hend := C.endpointRank_le
      omega
  · intro hsym
    exact ⟨Nat.le_of_lt_succ C.steps.isLt, Or.inl hsym⟩

/-- The appendix convention `binom n (-1) = 0`. -/
def previousLayerCard (n a : ℕ) : ℕ :=
  if a = 0 then 0 else n.choose (a - 1)

/-- The finite collection `𝒞ᵢ` of symmetric chains whose least member has
rank `i`. -/
def stratum (n i : ℕ) : Finset (DOne.BooleanChain n) :=
  DOne.BooleanChain.startGroup n n i

/-- A symmetric chain's canonical start is its least endpoint. -/
theorem canonicalStart_eq_start_of_symmetric (C : DOne.BooleanChain n)
    (hsymmetric : C.toChain.Symmetric) :
    C.canonicalStart = C.start.card := by
  rw [C.canonicalStart_eq_ite, if_pos]
  exact Or.inr ((C.symmetric_toChain_iff).mp hsymmetric).le

/-- Membership in `𝒞ᵢ` is exactly symmetry together with least rank `i`. -/
theorem mem_stratum_iff (C : DOne.BooleanChain n) (i : ℕ) :
    C ∈ stratum n i ↔ C.toChain.Symmetric ∧ C.start.card = i := by
  rw [stratum, DOne.BooleanChain.mem_startGroup_iff]
  constructor
  · rintro ⟨hgood, hstart⟩
    have hsym := (isGood_self_iff_symmetric C).mp hgood
    exact ⟨hsym, (canonicalStart_eq_start_of_symmetric C hsym).symm.trans hstart⟩
  · rintro ⟨hsym, hstart⟩
    exact ⟨(isGood_self_iff_symmetric C).mpr hsym,
      (canonicalStart_eq_start_of_symmetric C hsym).trans hstart⟩

private theorem auxiliaryWeightNat_self_eq_binomialDifference
    (n a : ℕ) (ha : a ≤ n) :
    DOne.auxiliaryWeightNat n n a = DOne.binomialDifference n a := by
  unfold DOne.auxiliaryWeightNat
  have hdiv : a / (n + 1) = 0 := Nat.div_eq_of_lt (by omega)
  simp [hdiv]

private theorem startingWeight_self_eq_binomialDifference
    (n a : ℕ) (hhalf : 2 * a ≤ n) :
    DOne.startingWeight n n a = DOne.binomialDifference n a := by
  rw [DOne.startingWeight_eq_lower hhalf]
  by_cases ha : a = 0
  · subst a
    rw [DOne.lowerStartingWeight, if_neg (by simp)]
    exact auxiliaryWeightNat_self_eq_binomialDifference n 0 (Nat.zero_le n)
  · rw [DOne.lowerStartingWeight, if_pos (by omega)]
    unfold DOne.innerWeight
    have hnegative : (n : ℤ) - (a : ℤ) - (n : ℤ) < 0 := by
      have hapositive : (0 : ℤ) < (a : ℤ) := by
        exact_mod_cast Nat.pos_of_ne_zero ha
      omega
    rw [DOne.auxiliaryWeight_ofNat,
      DOne.auxiliaryWeight_of_neg n n hnegative, sub_zero]
    exact auxiliaryWeightNat_self_eq_binomialDifference n a (by omega)

private theorem binomialDifference_eq_choose_sub_previous (n a : ℕ) :
    DOne.binomialDifference n a =
      (n.choose a : ℤ) - (previousLayerCard n a : ℤ) := by
  cases a with
  | zero => simp [DOne.binomialDifference, DOne.extendedChoose, previousLayerCard]
  | succ a =>
      simp only [DOne.binomialDifference, previousLayerCard, Nat.succ_ne_zero,
        if_false, DOne.extendedChoose_ofNat]
      have hpred : ((a + 1 : ℕ) : ℤ) - 1 = (a : ℤ) := by omega
      rw [hpred, DOne.extendedChoose_ofNat]
      simp

/-- The finite index type of all represented symmetric chains. -/
abbrev Index (n : ℕ) := DOne.BooleanChain.GoodIndex n n

/-- The appendix index type is exactly the subtype of represented Boolean
chains which are symmetric. -/
def indexEquivSymmetricChains (n : ℕ) :
    Index n ≃ {C : DOne.BooleanChain n // C.toChain.Symmetric} where
  toFun i := ⟨i.1, (isGood_self_iff_symmetric i.1).mp i.2⟩
  invFun C := ⟨C.1, (isGood_self_iff_symmetric C.1).mpr C.2⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv C := by
    apply Subtype.ext
    rfl

/-- The symmetric chain belonging to an appendix chain index. -/
def chain (i : Index n) : Chain n 1 := DOne.BooleanChain.indexedChain i

/-- The appendix weight on an indexed symmetric chain. -/
def weight (n : ℕ) (i : Index n) : ℝ :=
  DOne.BooleanChain.indexedWeight n n i

theorem chain_saturated (i : Index n) : (chain i).Saturated :=
  i.1.saturated_toChain

theorem chain_symmetric (i : Index n) : (chain i).Symmetric :=
  (isGood_self_iff_symmetric i.1).mp i.2

/-- The inherited weight is exactly the appendix formula
`(binom n i - binom n (i-1)) / |𝒞ᵢ|`. -/
theorem weight_eq_choose_sub_previous_div_card (i : Index n) :
    weight n i =
      (((n.choose i.1.start.card : ℤ) -
          (previousLayerCard n i.1.start.card : ℤ) : ℤ) : ℝ) /
        (stratum n i.1.start.card).card := by
  unfold weight DOne.BooleanChain.indexedWeight DOne.BooleanChain.chainWeight
  rw [if_pos i.2]
  unfold DOne.BooleanChain.startGroupChainWeight
  have hsym := chain_symmetric i
  rw [canonicalStart_eq_start_of_symmetric i.1 hsym]
  have hhalf : 2 * i.1.start.card ≤ n := by
    have := (i.1.symmetric_toChain_iff).mp hsym
    omega
  rw [startingWeight_self_eq_binomialDifference n i.1.start.card hhalf,
    binomialDifference_eq_choose_sub_previous]
  rfl

/-- Consequently, the total weight assigned to `𝒞ᵢ` is the adjacent
binomial-layer difference used in the appendix's telescoping sum. -/
theorem sum_weight_stratum (i : ℕ) (hi : 2 * i ≤ n) :
    ∑ C ∈ stratum n i, DOne.BooleanChain.chainWeight n n C =
      (((n.choose i : ℤ) - (previousLayerCard n i : ℤ) : ℤ) : ℝ) := by
  rw [stratum, DOne.BooleanChain.sum_chainWeight_startGroup
    (DOne.BooleanChain.startGroup_nonempty_lower n i hi)]
  rw [startingWeight_self_eq_binomialDifference n i hi,
    binomialDifference_eq_choose_sub_previous]

/-- The appendix weights are positive in the non-elementary dimensions. -/
theorem weight_pos (hn : 2 ≤ n) (i : Index n) : 0 < weight n i := by
  exact DOne.BooleanChain.indexedWeight_pos n n (by omega) le_rfl i

/-- The adjacent binomial differences telescope to the size of the final
layer, with the appendix convention at rank zero. -/
private theorem sum_choose_sub_previous (n r : ℕ) :
    ∑ a ∈ Finset.range (r + 1),
        ((((n.choose a : ℤ) - (previousLayerCard n a : ℤ) : ℤ) : ℝ)) =
      (n.choose r : ℝ) := by
  induction r with
  | zero => simp [previousLayerCard]
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [previousLayerCard, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      push_cast
      ring

/-- In the lower half of the cube, the appendix's stratum totals telescope to
the cardinality of the rank layer. -/
private theorem actualLayerWeightTotal_self_eq_choose_of_lower
    (n r : ℕ) (hn : 0 < n) (hr : 2 * r ≤ n) :
    DOne.BooleanChain.actualLayerWeightTotal n n r = (n.choose r : ℝ) := by
  rw [DOne.BooleanChain.actualLayerWeightTotal_eq_sum_startGroupIncidentWeight]
  have hterm (a : ℕ) (ha : a ≤ n) :
      DOne.BooleanChain.startGroupIncidentWeight n n a r =
        if a ≤ r then (DOne.startingWeight n n a : ℝ) else 0 := by
    by_cases halower : 2 * a ≤ n
    · rw [DOne.BooleanChain.startGroupIncidentWeight_lower hn halower]
      by_cases har : a ≤ r
      · have hpasses : a ≤ r ∧ r ≤ min (a + n) (n - a) := by
          refine ⟨har, ?_⟩
          rw [le_min_iff]
          constructor <;> omega
        rw [if_pos hpasses, if_pos har]
      · have hnotpasses : ¬(a ≤ r ∧ r ≤ min (a + n) (n - a)) := by
          exact fun h ↦ har h.1
        rw [if_neg hnotpasses, if_neg har]
    · have hupper : n < 2 * a := by omega
      have hinner : 2 * a ≤ n + n := by omega
      have har : ¬a ≤ r := by omega
      rw [DOne.BooleanChain.startGroupIncidentWeight_upper_inner hn hupper hinner,
        if_neg har]
  calc
    (∑ a ∈ Finset.range (n + 1),
        DOne.BooleanChain.startGroupIncidentWeight n n a r) =
        ∑ a ∈ Finset.range (n + 1),
          if a ≤ r then (DOne.startingWeight n n a : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply hterm a
      have := Finset.mem_range.mp ha
      omega
    _ = ∑ a ∈ Finset.range (r + 1),
          (DOne.startingWeight n n a : ℝ) := by
      symm
      calc
        (∑ a ∈ Finset.range (r + 1),
            (DOne.startingWeight n n a : ℝ)) =
            ∑ a ∈ Finset.range (r + 1),
              if a ≤ r then (DOne.startingWeight n n a : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [if_pos]
          exact Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        _ = ∑ a ∈ Finset.range (n + 1),
              if a ≤ r then (DOne.startingWeight n n a : ℝ) else 0 := by
          apply Finset.sum_subset
          · intro a ha
            have ha' := Finset.mem_range.mp ha
            apply Finset.mem_range.mpr
            omega
          · intro a _ha hnot
            have har : ¬a ≤ r := by
              intro har
              exact hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le har))
            rw [if_neg har]
    _ = ∑ a ∈ Finset.range (r + 1),
          ((((n.choose a : ℤ) - (previousLayerCard n a : ℤ) : ℤ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have halower : 2 * a ≤ n := by
        have har := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        omega
      rw [startingWeight_self_eq_binomialDifference n a halower,
        binomialDifference_eq_choose_sub_previous]
    _ = (n.choose r : ℝ) := sum_choose_sub_previous n r

/-- The lower-half unit-incidence statement obtained directly from the
appendix's telescoping stratum calculation and coordinate uniformity. -/
private theorem ambientInducedWeight_eq_one_of_lower (n : ℕ) (hn : 0 < n)
    (x : Cube n 1) (hlower : 2 * Cube.rank x ≤ n) :
    WeightedCover.inducedWeight
      (fun C : DOne.BooleanChain n ↦ C.toChain.vertices)
      (DOne.BooleanChain.chainWeight n n) x = 1 := by
  apply DOne.BooleanChain.inducedWeight_eq_one_of_actualLayerWeightTotal_eq_choose
    n n (Cube.rank x) (by simpa using Cube.rank_le x) rfl
  exact actualLayerWeightTotal_self_eq_choose_of_lower n (Cube.rank x) hn hlower

/-- The total weight of symmetric chains through any Boolean vertex is one:
this is the weighted incidence claim in Appendix 1. -/
theorem inducedWeight_eq_one (hn : 0 < n) (x : Cube n 1) :
    WeightedCover.inducedWeight (fun i : Index n ↦ (chain i).vertices)
      (weight n) x = 1 := by
  unfold chain weight
  rw [DOne.BooleanChain.indexedInducedWeight_eq]
  by_cases hlower : 2 * Cube.rank x ≤ n
  · exact ambientInducedWeight_eq_one_of_lower n hn x hlower
  · have hrankLe : Cube.rank x ≤ n := by
      simpa using Cube.rank_le x
    have hreflectLower : 2 * Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      omega
    rw [← DOne.BooleanChain.inducedChainWeight_reflect n n hn x]
    exact ambientInducedWeight_eq_one_of_lower n hn (Cube.reflect x) hreflectLower

/-- The appendix's weights take values in `(0, 1]` in every non-elementary
dimension, as stated in the paper. -/
theorem weight_le_one (hn : 2 ≤ n) (i : Index n) : weight n i ≤ 1 := by
  let x := (chain i).first
  have hx : x ∈ (chain i).vertices := by
    apply (Chain.mem_vertices_iff (chain i) x).mpr
    exact ⟨0, rfl⟩
  have hle : weight n i ≤
      WeightedCover.inducedWeight (fun j : Index n ↦ (chain j).vertices)
        (weight n) x := by
    unfold WeightedCover.inducedWeight
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Index n)))
      (f := fun j : Index n ↦ if x ∈ (chain j).vertices then weight n j else 0)
      (fun j _hj ↦ by
        by_cases hj : x ∈ (chain j).vertices
        · rw [if_pos hj]
          exact (weight_pos hn j).le
        · rw [if_neg hj])
      (Finset.mem_univ i)
    simpa [hx] using hsingle
  calc
    weight n i ≤
        WeightedCover.inducedWeight (fun j : Index n ↦ (chain j).vertices)
          (weight n) x := hle
    _ = 1 := inducedWeight_eq_one (by omega) x

/-- An antichain meets every symmetric chain in at most one vertex. -/
theorem inter_card_le_one (A : Finset (Cube n 1))
    (hA : Antichain (A : Set (Cube n 1))) (i : Index n) :
    (A ∩ (chain i).vertices).card ≤ 1 := by
  apply Chain.card_inter_vertices_le_one (chain i) A n
  · exact antichain_iff_nSeparated.mp hA
  · exact (DOne.BooleanChain.indexedChain_good i).2.1

/-- Every symmetric chain contains exactly one member of the lower middle
layer. -/
theorem lowerMiddleLayer_inter_card_eq_one (i : Index n) :
    (lowerMiddleLayer n ∩ (chain i).vertices).card = 1 := by
  change (DOne.booleanLayerFinset n (n / 2) ∩ i.1.toChain.vertices).card = 1
  rw [i.1.card_booleanLayerFinset_inter_vertices, if_pos]
  have hsym := (i.1.symmetric_toChain_iff).mp (chain_symmetric i)
  constructor <;> omega

/-- In an equality case, every positive-weight symmetric chain is met exactly
once, as asserted in the appendix. -/
theorem inter_card_eq_one_of_extremal (hn : 2 ≤ n)
    (A : Finset (Cube n 1)) (hA : Antichain (A : Set (Cube n 1)))
    (hcard : A.card = (lowerMiddleLayer n).card) (i : Index n) :
    (A ∩ (chain i).vertices).card = 1 := by
  apply WeightedCover.inter_card_eq_one_of_positive_of_card_eq
    (fun j : Index n ↦ (chain j).vertices) (weight n)
    (lowerMiddleLayer n) A
  · exact inducedWeight_eq_one (by omega)
  · intro j
    exact (weight_pos hn j).le
  · exact lowerMiddleLayer_inter_card_eq_one
  · exact inter_card_le_one A hA
  · exact hcard
  · exact weight_pos hn i

end SymmetricChain

/-- The weighted symmetric-chain argument gives Sperner's bound in every
non-elementary dimension. -/
theorem card_le_lowerMiddleLayer_of_two_le (hn : 2 ≤ n)
    (A : Finset (Cube n 1)) (hA : Antichain (A : Set (Cube n 1))) :
    A.card ≤ (lowerMiddleLayer n).card := by
  apply WeightedCover.card_le_of_weighted_cover
    (fun i : SymmetricChain.Index n ↦ (SymmetricChain.chain i).vertices)
    (SymmetricChain.weight n) (lowerMiddleLayer n) A
  · exact SymmetricChain.inducedWeight_eq_one (by omega)
  · intro i
    exact (SymmetricChain.weight_pos hn i).le
  · exact SymmetricChain.lowerMiddleLayer_inter_card_eq_one
  · exact SymmetricChain.inter_card_le_one A hA

/-- Equality in the non-elementary weighted bound gives exactly one of the
two middle layers.  The proof is the appendix's central-chain argument:
singleton symmetric chains settle the even case, while one-step symmetric
chains and connectedness of the adjacent-layer graph settle the odd case. -/
theorem eq_lower_or_upper_of_card_eq_of_two_le (hn : 2 ≤ n)
    (A : Finset (Cube n 1)) (hA : Antichain (A : Set (Cube n 1)))
    (hcard : A.card = (lowerMiddleLayer n).card) :
    A = lowerMiddleLayer n ∨ A = upperMiddleLayer n := by
  rcases Nat.even_or_odd n with heven | hodd
  · left
    have hsubset : lowerMiddleLayer n ⊆ A := by
      intro x hx
      have hxrank : Cube.rank x = n / 2 := mem_lowerMiddleLayer_iff.mp hx
      let C := DOne.BooleanChain.singletonChain x
      have hgood : C.IsGood n :=
        DOne.BooleanChain.singletonChain_isGood_of_even x n heven hxrank
      let i : SymmetricChain.Index n := ⟨C, hgood⟩
      have hinter :=
        SymmetricChain.inter_card_eq_one_of_extremal hn A hA hcard i
      have hvertices : (SymmetricChain.chain i).vertices = {x} := by
        change C.toChain.vertices = {x}
        simp [C]
      rw [hvertices] at hinter
      by_contra hxnot
      simp [hxnot] at hinter
    exact (Finset.eq_of_subset_of_card_le hsubset hcard.le).symm
  · have hchoice :=
      DOneMiddleUniqueness.inter_adjacentLayers_eq_lower_or_upper
        (A := (A : Set (Cube n 1)))
        (r := n / 2) (n := n) (Nat.div_le_self n 2) (by
          intro x y hx hy hxy
          obtain ⟨C, hsteps, hfirst, hlast⟩ :=
            DOne.BooleanChain.exists_oneStepChain_of_adjacent hx hy hxy
          have hgood : C.IsGood n :=
            DOne.BooleanChain.oneStepChain_isGood_of_odd C n (by omega)
              hodd hsteps (by rw [hfirst, hx])
          let i : SymmetricChain.Index n := ⟨C, hgood⟩
          have hinter :=
            SymmetricChain.inter_card_eq_one_of_extremal hn A hA hcard i
          have hvertices : (SymmetricChain.chain i).vertices = {x, y} := by
            change C.toChain.vertices = {x, y}
            rw [DOne.BooleanChain.vertices_eq_pair_of_steps_eq_one C hsteps,
              hfirst, hlast]
          rw [hvertices] at hinter
          apply DOne.BooleanChain.mem_iff_not_mem_of_inter_pair_card_eq_one A
          · intro hxyEq
            have hrankEq := congrArg Cube.rank hxyEq
            rw [hx, hy] at hrankEq
            omega
          · exact hinter)
    have hmiddle : n - n / 2 = n / 2 + 1 := by
      have hparity := Nat.two_mul_div_two_add_one_of_odd hodd
      omega
    rcases hchoice with hlower | hupper
    · left
      have hsubset : lowerMiddleLayer n ⊆ A := by
        intro x hx
        have hxrank : Cube.rank x = n / 2 := mem_lowerMiddleLayer_iff.mp hx
        have hxinter : x ∈ (A : Set (Cube n 1)) ∩
            DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) := by
          rw [hlower]
          exact hxrank
        exact hxinter.1
      exact (Finset.eq_of_subset_of_card_le hsubset hcard.le).symm
    · right
      have hsubset : upperMiddleLayer n ⊆ A := by
        intro x hx
        have hxrank : Cube.rank x = n / 2 + 1 := by
          rw [← hmiddle]
          exact mem_upperMiddleLayer_iff.mp hx
        have hxinter : x ∈ (A : Set (Cube n 1)) ∩
            DOneMiddleUniqueness.cubeAdjacentLayers n (n / 2) := by
          rw [hupper]
          exact hxrank
        exact hxinter.1
      apply (Finset.eq_of_subset_of_card_le hsubset ?_).symm
      rw [hcard, card_lowerMiddleLayer, card_upperMiddleLayer]

/-- Every antichain in dimension at most one has cardinality at most one. -/
private theorem card_le_one_of_le_one {n : ℕ} (hn : n ≤ 1)
    (A : Finset (Cube n 1)) (hA : Antichain (A : Set (Cube n 1))) :
    A.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact Subsingleton.elim x y
  · by_cases hxy : x 0 ≤ y 0
    · apply hA hx hy
      intro i
      exact Fin.cases hxy (fun j ↦ Fin.elim0 j) i
    · symm
      apply hA hy hx
      intro i
      exact Fin.cases (le_of_not_ge hxy) (fun j ↦ Fin.elim0 j) i

/-- A one-element finset containing `x` is the singleton `{x}`. -/
private theorem eq_singleton_of_card_eq_one_of_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α}
    (hcard : A.card = 1) (hx : x ∈ A) : A = {x} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  exact ⟨hx, fun y hy ↦ by
    have hle : A.card ≤ 1 := hcard.le
    exact (Finset.card_le_one.mp hle) y hy x hx⟩

/-- In dimensions zero and one, a cardinality-one family is one of the middle
layers. -/
private theorem eq_middleLayer_of_le_one_of_card_eq_one {n : ℕ} (hn : n ≤ 1)
    (A : Finset (Cube n 1)) (hcard : A.card = 1) :
    A = lowerMiddleLayer n ∨ A = upperMiddleLayer n := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  have hAeq : A = {x} := eq_singleton_of_card_eq_one_of_mem hcard hx
  have hrank := Cube.rank_le x
  simp only [Nat.mul_one] at hrank
  have hlowerCard : (lowerMiddleLayer n).card = 1 := by
    rw [card_lowerMiddleLayer]
    interval_cases n <;> simp_all
  have hupperCard : (upperMiddleLayer n).card = 1 := by
    rw [card_upperMiddleLayer]
    interval_cases n <;> simp_all
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · left
    have hxLower : x ∈ lowerMiddleLayer 0 := by
      rw [mem_lowerMiddleLayer_iff]
      simpa using hrank
    rw [hAeq]
    exact (eq_singleton_of_card_eq_one_of_mem hlowerCard hxLower).symm
  · have hxrank : Cube.rank x = 0 ∨ Cube.rank x = 1 := by omega
    rcases hxrank with hxrank | hxrank
    · left
      have hxLower : x ∈ lowerMiddleLayer 1 := by
        rw [mem_lowerMiddleLayer_iff]
        simpa using hxrank
      rw [hAeq]
      exact (eq_singleton_of_card_eq_one_of_mem hlowerCard hxLower).symm
    · right
      have hxUpper : x ∈ upperMiddleLayer 1 := by
        rw [mem_upperMiddleLayer_iff]
        simpa using hxrank
      rw [hAeq]
      exact (eq_singleton_of_card_eq_one_of_mem hupperCard hxUpper).symm

/-- **Sperner's theorem, with uniqueness.**  Every antichain in the Boolean
cube has at most `n.choose (n / 2)` members.  Equality holds exactly for the
lower or upper middle layer (which coincide when `n` is even). -/
theorem cardinality_and_uniqueness (n : ℕ) (A : Finset (Cube n 1))
    (hA : Antichain (A : Set (Cube n 1))) :
    A.card ≤ n.choose (n / 2) ∧
      (A.card = n.choose (n / 2) ↔
        A = lowerMiddleLayer n ∨ A = upperMiddleLayer n) := by
  by_cases hn : 2 ≤ n
  · constructor
    · simpa only [card_lowerMiddleLayer] using
        card_le_lowerMiddleLayer_of_two_le hn A hA
    · constructor
      · intro hcard
        apply eq_lower_or_upper_of_card_eq_of_two_le hn A hA
        simpa only [card_lowerMiddleLayer] using hcard
      · rintro (rfl | rfl)
        · exact card_lowerMiddleLayer n
        · exact card_upperMiddleLayer n
  · have hnle : n ≤ 1 := by omega
    have hchoose : n.choose (n / 2) = 1 := by
      interval_cases n <;> simp_all
    rw [hchoose]
    constructor
    · exact card_le_one_of_le_one hnle A hA
    · constructor
      · exact eq_middleLayer_of_le_one_of_card_eq_one hnle A
      · rintro (rfl | rfl)
        · rw [card_lowerMiddleLayer, hchoose]
        · rw [card_upperMiddleLayer, hchoose]

end SpernerAppendix
end WeightedChains
