import WeightedChains.DTwo.InnerWeightPositivity
import WeightedChains.DTwo.BasicSufficiency
import WeightedChains.DTwo.Metachains
import WeightedChains.DTwo.StartGroups

/-!
# Total weights attached to ternary canonical start types

Section 5 assigns an integer total `W` to each metachain before dividing it
among the basic chains in that metachain.  On a lower outer type this is the
auxiliary weight `U`; on a lower inner type it is the corrected difference
`U(a,c) - U(c+k,a-k)`.  Upper types receive the weight of their reflection.

This file packages that case distinction on `TypeCounts`, proves reflection
symmetry and positivity, and transfers positivity through the finite equal
division in `BasicChain.distributedChainWeight`.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary

/-- The type `(0,n,0)` of the distinguished all-ones vertex. -/
def allOnesType (n : ℕ) : TypeCounts n where
  zeros := 0
  ones := n
  twos := 0
  sum_eq := by omega

@[simp] theorem allOnesType_zeros (n : ℕ) : (allOnesType n).zeros = 0 := rfl
@[simp] theorem allOnesType_ones (n : ℕ) : (allOnesType n).ones = n := rfl
@[simp] theorem allOnesType_twos (n : ℕ) : (allOnesType n).twos = 0 := rfl

@[simp]
theorem allOnesType_reflect (n : ℕ) : (allOnesType n).reflect = allOnesType n := by
  rfl

@[simp]
theorem ofVertex_middleVertex (n : ℕ) :
    TypeCounts.ofVertex (middleVertex n) = allOnesType n := by
  apply TypeCounts.ext <;> simp [TypeCounts.ofVertex]

/-- The paper's total starting weight `W` for a ternary type.  The lower
representative of a reflection pair is used.  Its outer region is
`c+k ≤ a`; the remaining lower types are inner. -/
def startTypeWeight {n : ℕ} (k : ℕ) (t : TypeCounts n) : ℤ :=
  if t.twos ≤ t.zeros then
    if t.twos + k ≤ t.zeros then
      auxiliaryWeight n k t.zeros t.twos
    else
      innerStartingWeight n k t.zeros t.twos
  else
    if t.zeros + k ≤ t.twos then
      auxiliaryWeight n k t.twos t.zeros
    else
      innerStartingWeight n k t.twos t.zeros

/-- Upper and lower canonical start types have the same total weight. -/
@[simp]
theorem startTypeWeight_reflect {n k : ℕ} (t : TypeCounts n) :
    startTypeWeight k t.reflect = startTypeWeight k t := by
  by_cases htc : t.twos ≤ t.zeros
  · by_cases hct : t.zeros ≤ t.twos
    · have heq : t.zeros = t.twos := Nat.le_antisymm hct htc
      simp [startTypeWeight, heq]
    · simp [startTypeWeight, htc, hct]
      by_cases houter : t.twos + k ≤ t.zeros <;> simp [houter]
  · have hct : t.zeros ≤ t.twos := Nat.le_of_lt (Nat.lt_of_not_ge htc)
    simp [startTypeWeight, htc, hct]
    by_cases houter : t.zeros + k ≤ t.twos <;> simp [houter]

/-- The all-ones type is precisely the type whose zero and two entries both
vanish. -/
theorem eq_allOnesType_iff {n : ℕ} (t : TypeCounts n) :
    t = allOnesType n ↔ t.zeros = 0 ∧ t.twos = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hzero, htwo⟩
    apply TypeCounts.ext
    · simpa using hzero
    · have hsum := t.sum_eq
      simp only [hzero, htwo, zero_add, add_zero] at hsum
      simpa using hsum
    · simpa using htwo

/-- The exceptional type has starting total zero. -/
@[simp]
theorem startTypeWeight_allOnesType (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    startTypeWeight k (allOnesType n) = 0 := by
  simp [startTypeWeight, show ¬k ≤ 0 by omega,
    innerStartingWeight_zero_zero n k hn hk]

/-- Every valid nonexceptional ternary type has positive total starting
weight.  Validity is intrinsic in `TypeCounts`; the proof reduces upper
types to their lower reflected coordinates. -/
theorem startTypeWeight_pos {n k : ℕ} (t : TypeCounts n)
    (hk : 1 < k) (hkn : k ≤ n) (hne : t ≠ allOnesType n) :
    0 < startTypeWeight k t := by
  have hvalid : t.zeros + t.twos ≤ n := by
    have hsum := t.sum_eq
    omega
  have hpairs : (t.zeros, t.twos) ≠ (0, 0) := by
    intro hpair
    apply hne
    apply (eq_allOnesType_iff t).2
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  unfold startTypeWeight
  by_cases hlower : t.twos ≤ t.zeros
  · rw [if_pos hlower]
    by_cases houter : t.twos + k ≤ t.zeros
    · rw [if_pos houter]
      exact auxiliaryWeight_pos_of_valid_lower_nat
        k n t.zeros t.twos (by omega) hkn hlower hvalid hpairs
    · rw [if_neg houter]
      exact innerStartingWeight_pos_of_valid_lower_inner_nat
        k n t.zeros t.twos hk hkn hlower hvalid (by omega) hpairs
  · rw [if_neg hlower]
    have hupper : t.zeros ≤ t.twos := by omega
    have hvalid' : t.twos + t.zeros ≤ n := by omega
    have hpairs' : (t.twos, t.zeros) ≠ (0, 0) := by
      intro hpair
      apply hpairs
      apply Prod.ext
      · exact congrArg Prod.snd hpair
      · exact congrArg Prod.fst hpair
    by_cases houter : t.zeros + k ≤ t.twos
    · rw [if_pos houter]
      exact auxiliaryWeight_pos_of_valid_lower_nat
        k n t.twos t.zeros (by omega) hkn hupper hvalid' hpairs'
    · rw [if_neg houter]
      exact innerStartingWeight_pos_of_valid_lower_inner_nat
        k n t.twos t.zeros hk hkn hupper hvalid' (by omega) hpairs'

/-- The real-valued form of `startTypeWeight`, suitable for distribution
among the finite basic-chain start group. -/
def startTypeTotal {n : ℕ} (k : ℕ) (t : TypeCounts n) : ℝ :=
  startTypeWeight k t

@[simp]
theorem startTypeTotal_reflect {n k : ℕ} (t : TypeCounts n) :
    startTypeTotal k t.reflect = startTypeTotal k t := by
  simp [startTypeTotal]

@[simp]
theorem startTypeTotal_allOnesType (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    startTypeTotal k (allOnesType n) = 0 := by
  simp [startTypeTotal, startTypeWeight_allOnesType n k hn hk]

theorem startTypeTotal_pos {n k : ℕ} (t : TypeCounts n)
    (hk : 1 < k) (hkn : k ≤ n) (hne : t ≠ allOnesType n) :
    0 < startTypeTotal k t := by
  unfold startTypeTotal
  exact_mod_cast startTypeWeight_pos t hk hkn hne

namespace BasicChain

variable {n : ℕ}

/-- A canonical start type is the all-ones type exactly when the basic
descriptor starts at the all-ones vertex.  Its width is then necessarily
zero, so this is precisely the exceptional singleton descriptor. -/
theorem canonicalStartType_eq_allOnesType_iff (B : BasicChain n) :
    B.canonicalStartType = allOnesType n ↔ B.start = middleVertex n := by
  constructor
  · intro htype
    unfold canonicalStartType at htype
    split at htype
    · have hfirstType : TypeCounts.ofVertex B.start = allOnesType n := by
        simpa only [B.toChain_first] using htype
      apply eq_middleVertex_of_zeroCount_eq_zero_of_twoCount_eq_zero
      · have hzero := congrArg TypeCounts.zeros hfirstType
        simpa only [TypeCounts.ofVertex, allOnesType_zeros] using hzero
      · have htwo := congrArg TypeCounts.twos hfirstType
        simpa only [TypeCounts.ofVertex, allOnesType_twos] using htwo
    · rename_i hlastFarther
      have hlastType : TypeCounts.ofVertex B.toChain.last = allOnesType n := htype
      have hlastRank : Cube.rank B.toChain.last = n := by
        rw [← TypeCounts.rank_ofVertex, hlastType]
        simp [TypeCounts.rank, allOnesType]
      have hlastDistance : Cube.middleDistance B.toChain.last = 0 := by
        unfold Cube.middleDistance
        rw [hlastRank]
        simp [Nat.mul_comm]
      exact (hlastFarther (by rw [hlastDistance]; exact Nat.zero_le _)).elim
  · intro hstart
    have hwidth := B.width_eq_zero_of_start_eq_middleVertex hstart
    have hfirst : B.toChain.first = middleVertex n := by
      rw [B.toChain_first, hstart]
    have hlast : B.toChain.last = middleVertex n := by
      have hwidthFin : B.width = 0 := Fin.ext hwidth
      rw [B.toChain_last, hwidthFin]
      have hevenZero : B.evenVertex 0 = B.start := by
        funext q
        simp [evenVertex, initialSegment]
      change B.evenVertex 0 = middleVertex n
      rw [hevenZero, hstart]
    unfold canonicalStartType
    rw [hfirst, hlast, if_pos le_rfl, ofVertex_middleVertex]

/-- Under the theorem hypotheses, every good basic chain except the
all-ones singleton receives positive distributed weight. -/
theorem distributedStartTypeWeight_pos (B : BasicChain n) (k : ℕ)
    (hk : 1 < k) (hkn : k ≤ n) (hgood : B.toChain.Good k)
    (hne : B.start ≠ middleVertex n) :
    0 < distributedChainWeight (startTypeTotal k) k B := by
  apply distributedChainWeight_pos_of_good (startTypeTotal k) k B hgood
  apply startTypeTotal_pos B.canonicalStartType hk hkn
  intro htype
  exact hne ((B.canonicalStartType_eq_allOnesType_iff).1 htype)

end BasicChain
end Ternary
end WeightedChains
