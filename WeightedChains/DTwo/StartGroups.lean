import WeightedChains.DTwo.ChainReflection

/-!
# Canonical start-type groups for basic ternary chains

Section 5 first assigns a total weight to every type from which basic good
chains start, and only afterwards divides that total equally among the
individual chains in the corresponding metachain.  This file isolates that
finite bookkeeping.  The endpoint farther from the middle is the canonical
paper start; in the symmetric tie the lower (first) endpoint is used.
-/

open scoped BigOperators

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

/-- The decidable arithmetic form of goodness for a basic-chain
descriptor. -/
def IsGood (B : BasicChain n) (k : ℕ) : Prop :=
  B.width ≤ k ∧
    (zeroCount B.start = twoCount B.start + B.width ∨ B.width = k)

instance decidableIsGood (B : BasicChain n) (k : ℕ) :
    Decidable (B.IsGood k) := by
  unfold IsGood
  infer_instance

theorem isGood_iff (B : BasicChain n) (k : ℕ) :
    B.IsGood k ↔ B.toChain.Good k := by
  exact (B.toChain_good_iff k).symm

/-- Coordinate permutations preserve the number of one coordinates. -/
@[simp]
theorem oneCount_permuteVertex (e : Equiv.Perm (Fin n)) (x : Cube n 2) :
    oneCount (permuteVertex e x) = oneCount x := by
  have hpermuted := zeroCount_add_oneCount_add_twoCount (permuteVertex e x)
  have horiginal := zeroCount_add_oneCount_add_twoCount x
  simp only [zeroCount_permuteVertex, twoCount_permuteVertex] at hpermuted
  omega

/-- Coordinate permutations preserve ternary rank. -/
@[simp]
theorem rank_permuteVertex (e : Equiv.Perm (Fin n)) (x : Cube n 2) :
    Cube.rank (permuteVertex e x) = Cube.rank x := by
  rw [rank_eq_oneCount_add_two_mul_twoCount,
    rank_eq_oneCount_add_two_mul_twoCount]
  simp

/-- Reindexing a descriptor reindexes its first endpoint. -/
@[simp]
theorem toChain_first_reindex (B : BasicChain n) (e : Equiv.Perm (Fin n)) :
    (B.reindex e).toChain.first = permuteVertex e B.toChain.first := by
  rw [(B.reindex e).toChain_first, B.toChain_first, reindex_start]

/-- Reindexing a descriptor reindexes its last endpoint. -/
@[simp]
theorem toChain_last_reindex (B : BasicChain n) (e : Equiv.Perm (Fin n)) :
    (B.reindex e).toChain.last = permuteVertex e B.toChain.last := by
  change (B.reindex e).vertexAt (2 * (B.reindex e).width) =
    permuteVertex e (B.vertexAt (2 * B.width))
  simpa only [reindex_width] using B.vertexAt_reindex e (2 * B.width)

/-- Coordinate reindexing does not change which endpoint is farther from the
middle. -/
theorem startsAtFirst_reindex_iff (B : BasicChain n)
    (e : Equiv.Perm (Fin n)) :
    (B.reindex e).toChain.StartsAtFirst ↔ B.toChain.StartsAtFirst := by
  unfold Chain.StartsAtFirst Cube.middleDistance
  rw [toChain_first_reindex, toChain_last_reindex,
    rank_permuteVertex, rank_permuteVertex]

/-- The endpoint type used by the paper to label the starting metachain.
The endpoint farther from the middle is selected, with the first endpoint
chosen when the distances are equal. -/
def canonicalStartType (B : BasicChain n) : TypeCounts n :=
  if Cube.middleDistance B.toChain.last ≤
      Cube.middleDistance B.toChain.first then
    TypeCounts.ofVertex B.toChain.first
  else
    TypeCounts.ofVertex B.toChain.last

theorem canonicalStartType_eq_first (B : BasicChain n)
    (hfirst : B.toChain.StartsAtFirst) :
    B.canonicalStartType = TypeCounts.ofVertex B.toChain.first := by
  change Cube.middleDistance B.toChain.last ≤
    Cube.middleDistance B.toChain.first at hfirst
  rw [canonicalStartType, if_pos hfirst]

theorem canonicalStartType_eq_last (B : BasicChain n)
    (hfirst : ¬B.toChain.StartsAtFirst) :
    B.canonicalStartType = TypeCounts.ofVertex B.toChain.last := by
  change ¬Cube.middleDistance B.toChain.last ≤
    Cube.middleDistance B.toChain.first at hfirst
  rw [canonicalStartType, if_neg hfirst]

/-- A coordinate permutation does not change the canonical start type. -/
@[simp]
theorem canonicalStartType_reindex (B : BasicChain n)
    (e : Equiv.Perm (Fin n)) :
    (B.reindex e).canonicalStartType = B.canonicalStartType := by
  have hofVertex (x : Cube n 2) :
      TypeCounts.ofVertex (permuteVertex e x) = TypeCounts.ofVertex x := by
    apply TypeCounts.ext
    · exact zeroCount_permuteVertex e x
    · exact oneCount_permuteVertex e x
    · exact twoCount_permuteVertex e x
  unfold canonicalStartType
  rw [toChain_first_reindex, toChain_last_reindex,
    show Cube.middleDistance (permuteVertex e B.toChain.last) =
        Cube.middleDistance B.toChain.last by
      unfold Cube.middleDistance
      rw [rank_permuteVertex],
    show Cube.middleDistance (permuteVertex e B.toChain.first) =
        Cube.middleDistance B.toChain.first by
      unfold Cube.middleDistance
      rw [rank_permuteVertex]]
  split <;> apply hofVertex

theorem isGood_reindex_iff (B : BasicChain n)
    (e : Equiv.Perm (Fin n)) (k : ℕ) :
    (B.reindex e).IsGood k ↔ B.IsGood k := by
  rw [(B.reindex e).isGood_iff, B.isGood_iff,
    B.toChain_good_reindex_iff]

/-- The finite group of good basic-chain descriptors with canonical start
type `t`. -/
def startGroup (n k : ℕ) (t : TypeCounts n) : Finset (BasicChain n) := by
  classical
  exact Finset.univ.filter fun B ↦
    B.IsGood k ∧ B.canonicalStartType = t

@[simp]
theorem mem_startGroup_iff (B : BasicChain n) (k : ℕ) (t : TypeCounts n) :
    B ∈ startGroup n k t ↔
      B.toChain.Good k ∧ B.canonicalStartType = t := by
  classical
  simp [startGroup, B.isGood_iff]

@[simp]
theorem mem_startGroup_canonicalStartType_iff (B : BasicChain n) (k : ℕ) :
    B ∈ startGroup n k B.canonicalStartType ↔ B.toChain.Good k := by
  simp

theorem startGroup_nonempty_of_good (B : BasicChain n) (k : ℕ)
    (hgood : B.toChain.Good k) :
    (startGroup n k B.canonicalStartType).Nonempty :=
  ⟨B, (mem_startGroup_canonicalStartType_iff B k).2 hgood⟩

theorem startGroup_disjoint {k : ℕ} {s t : TypeCounts n} (hst : s ≠ t) :
    Disjoint (startGroup n k s) (startGroup n k t) := by
  rw [Finset.disjoint_left]
  intro B hBs hBt
  have hs := (mem_startGroup_iff B k s).1 hBs |>.2
  have ht := (mem_startGroup_iff B k t).1 hBt |>.2
  exact hst (hs.symm.trans ht)

/-- Divide a prescribed total start-type weight equally among all good basic
chains in that canonical start group.  Non-good descriptors remain in the
finite index type with weight zero. -/
def distributedChainWeight (total : TypeCounts n → ℝ) (k : ℕ)
    (B : BasicChain n) : ℝ :=
  if B.IsGood k then
    total B.canonicalStartType /
      (startGroup n k B.canonicalStartType).card
  else
    0

theorem distributedChainWeight_of_mem_startGroup
    (total : TypeCounts n → ℝ) {k : ℕ} {t : TypeCounts n}
    {B : BasicChain n} (hB : B ∈ startGroup n k t) :
    distributedChainWeight total k B =
      total t / (startGroup n k t).card := by
  have hdata := (mem_startGroup_iff B k t).1 hB
  rw [distributedChainWeight, if_pos (B.isGood_iff k |>.2 hdata.1), hdata.2]

/-- Equal division recovers exactly the prescribed type total whenever the
start group is occupied. -/
theorem sum_distributedChainWeight_startGroup
    (total : TypeCounts n → ℝ) {k : ℕ} {t : TypeCounts n}
    (ht : (startGroup n k t).Nonempty) :
    ∑ B ∈ startGroup n k t, distributedChainWeight total k B = total t := by
  calc
    ∑ B ∈ startGroup n k t, distributedChainWeight total k B =
        ∑ _B ∈ startGroup n k t,
          total t / (startGroup n k t).card := by
      apply Finset.sum_congr rfl
      intro B hB
      exact distributedChainWeight_of_mem_startGroup total hB
    _ = ((startGroup n k t).card : ℝ) *
        (total t / (startGroup n k t).card) := by simp
    _ = total t := by
      have hcard : ((startGroup n k t).card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr ht
      field_simp

/-- The distributed weight is invariant under coordinate permutations. -/
@[simp]
theorem distributedChainWeight_reindex
    (total : TypeCounts n → ℝ) (k : ℕ)
    (B : BasicChain n) (e : Equiv.Perm (Fin n)) :
    distributedChainWeight total k (B.reindex e) =
      distributedChainWeight total k B := by
  unfold distributedChainWeight
  rw [canonicalStartType_reindex]
  exact if_congr (B.isGood_reindex_iff e k) rfl rfl

/-- Positivity of an occupied start-type total gives positivity of every good
descriptor in that group. -/
theorem distributedChainWeight_pos_of_good
    (total : TypeCounts n → ℝ) (k : ℕ) (B : BasicChain n)
    (hgood : B.toChain.Good k) (htotal : 0 < total B.canonicalStartType) :
    0 < distributedChainWeight total k B := by
  rw [distributedChainWeight, if_pos (B.isGood_iff k |>.2 hgood)]
  exact div_pos htotal (by
    exact_mod_cast Finset.card_pos.mpr
      (B.startGroup_nonempty_of_good k hgood))

end BasicChain
end Ternary
end WeightedChains
