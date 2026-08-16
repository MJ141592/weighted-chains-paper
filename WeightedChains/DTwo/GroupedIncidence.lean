import WeightedChains.DTwo.StartGroupTraces
import WeightedChains.DTwo.TypeIncidence
import WeightedChains.DTwo.StartingWeights

/-!
# Regrouping ternary incidence by metachain

The descriptor-level induced-weight sum can be partitioned by canonical start
type.  Uniformity of start-group traces then says that a whole metachain either
visits a target type or misses it.  Thus an incident metachain contributes
exactly its prescribed start-type total.
-/

open scoped BigOperators

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

local instance typeCountsDecidableEq (m : ℕ) :
    DecidableEq (TypeCounts m) := Classical.decEq _

/-- The finite set of good basic-chain descriptors. -/
def goodDescriptors (n k : ℕ) : Finset (BasicChain n) :=
  Finset.univ.filter fun B ↦ B.IsGood k

@[simp]
theorem mem_goodDescriptors_iff (B : BasicChain n) (k : ℕ) :
    B ∈ goodDescriptors n k ↔ B.toChain.Good k := by
  simp [goodDescriptors, B.isGood_iff]

/-- Canonical start types for which the good start group is occupied. -/
def occupiedStartTypes (n k : ℕ) : Finset (TypeCounts n) := by
  classical
  exact (goodDescriptors n k).image canonicalStartType

theorem mem_occupiedStartTypes_iff (t : TypeCounts n) (k : ℕ) :
    t ∈ occupiedStartTypes n k ↔ (startGroup n k t).Nonempty := by
  classical
  constructor
  · rw [occupiedStartTypes, Finset.mem_image]
    rintro ⟨B, hBgood, hBt⟩
    refine ⟨B, (mem_startGroup_iff B k t).2 ⟨?_, hBt⟩⟩
    exact (mem_goodDescriptors_iff B k).1 hBgood
  · rintro ⟨B, hB⟩
    obtain ⟨hBgood, hBt⟩ := (mem_startGroup_iff B k t).1 hB
    rw [occupiedStartTypes, Finset.mem_image]
    exact ⟨B, (mem_goodDescriptors_iff B k).2 hBgood, hBt⟩

theorem goodDescriptorFiber_eq_startGroup (k : ℕ) (t : TypeCounts n) :
    (goodDescriptors n k).filter (fun B ↦ B.canonicalStartType = t) =
      startGroup n k t := by
  classical
  ext B
  simp only [Finset.mem_filter]
  rw [mem_goodDescriptors_iff, mem_startGroup_iff]

/-- Any finite sum over good descriptors may be regrouped by canonical start
type. -/
theorem sum_goodDescriptors_eq_sum_startGroups
    (k : ℕ) (f : BasicChain n → ℝ) :
    ∑ B ∈ goodDescriptors n k, f B =
      ∑ t ∈ occupiedStartTypes n k,
        ∑ B ∈ startGroup n k t, f B := by
  classical
  symm
  calc
    ∑ t ∈ occupiedStartTypes n k,
        ∑ B ∈ startGroup n k t, f B =
      ∑ t ∈ occupiedStartTypes n k,
        ∑ B ∈ (goodDescriptors n k).filter
          (fun B ↦ B.canonicalStartType = t), f B := by
            apply Finset.sum_congr rfl
            intro t _ht
            rw [goodDescriptorFiber_eq_startGroup]
    _ = ∑ B ∈ goodDescriptors n k, f B := by
      apply Finset.sum_fiberwise_of_maps_to
      intro B hB
      exact Finset.mem_image.mpr ⟨B, hB, rfl⟩

/-- Type incidence transports between any two descriptors in the same
canonical start group. -/
theorem visitsType_of_mem_startGroup
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n) (a c : ℕ)
    {B C : BasicChain n} (hB : B ∈ startGroup n k t)
    (hC : C ∈ startGroup n k t) :
    B.VisitsType a c → C.VisitsType a c := by
  rw [B.visitsType_iff_exists_vertex, C.visitsType_iff_exists_vertex]
  rintro ⟨i, hiZero, hiTwo⟩
  have hwidthNat := width_eq_of_mem_startGroup k hk t hB hC
  have hwidth : B.width = C.width := Fin.ext hwidthNat
  have hsteps : B.toChain.steps + 1 = C.toChain.steps + 1 := by
    simp [hwidth]
  let j : Fin (C.toChain.steps + 1) := Fin.cast hsteps i
  have hiBound : (i : ℕ) ≤ 2 * B.width := by
    have hiLt := i.isLt
    simp only [B.toChain_steps] at hiLt
    omega
  have htype := type_vertexAt_eq_of_mem_startGroup
    k hk t hB hC (i : ℕ) hiBound
  have hzero := congrArg TypeCounts.zeros htype
  have htwo := congrArg TypeCounts.twos htype
  refine ⟨j, ?_, ?_⟩
  · change zeroCount (C.vertexAt (j : ℕ)) = a
    have hiZero' : zeroCount (B.vertexAt (i : ℕ)) = a := hiZero
    have hzero' : zeroCount (B.vertexAt (i : ℕ)) =
        zeroCount (C.vertexAt (i : ℕ)) := hzero
    have hj : (j : ℕ) = (i : ℕ) := rfl
    rw [hj]
    exact hzero'.symm.trans hiZero'
  · change twoCount (C.vertexAt (j : ℕ)) = c
    have hiTwo' : twoCount (B.vertexAt (i : ℕ)) = c := hiTwo
    have htwo' : twoCount (B.vertexAt (i : ℕ)) =
        twoCount (C.vertexAt (i : ℕ)) := htwo
    have hj : (j : ℕ) = (i : ℕ) := rfl
    rw [hj]
    exact htwo'.symm.trans hiTwo'

theorem visitsType_iff_of_mem_startGroup
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n) (a c : ℕ)
    {B C : BasicChain n} (hB : B ∈ startGroup n k t)
    (hC : C ∈ startGroup n k t) :
    B.VisitsType a c ↔ C.VisitsType a c :=
  ⟨visitsType_of_mem_startGroup k hk t a c hB hC,
    visitsType_of_mem_startGroup k hk t a c hC hB⟩

/-- A canonical start group visits a target type when one (equivalently,
every) descriptor in it does. -/
def StartGroupVisitsType (n k : ℕ) (t : TypeCounts n) (a c : ℕ) : Prop :=
  ∃ B ∈ startGroup n k t, B.VisitsType a c

instance decidableStartGroupVisitsType
    (n k : ℕ) (t : TypeCounts n) (a c : ℕ) :
    Decidable (StartGroupVisitsType n k t a c) := by
  unfold StartGroupVisitsType
  infer_instance

theorem sum_distributedChainWeight_startGroup_if_visits
    (total : TypeCounts n → ℝ) (k : ℕ) (hk : 0 < k)
    (t : TypeCounts n) (a c : ℕ)
    (ht : (startGroup n k t).Nonempty) :
    ∑ B ∈ startGroup n k t,
        (if B.VisitsType a c then distributedChainWeight total k B else 0) =
      if StartGroupVisitsType n k t a c then total t else 0 := by
  by_cases hvisit : StartGroupVisitsType n k t a c
  · rw [if_pos hvisit]
    obtain ⟨C, hC, hCvisit⟩ := hvisit
    calc
      ∑ B ∈ startGroup n k t,
          (if B.VisitsType a c then distributedChainWeight total k B else 0) =
        ∑ B ∈ startGroup n k t, distributedChainWeight total k B := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [if_pos ((visitsType_iff_of_mem_startGroup
            k hk t a c hB hC).2 hCvisit)]
      _ = total t := sum_distributedChainWeight_startGroup total ht
  · rw [if_neg hvisit]
    apply Finset.sum_eq_zero
    intro B hB
    rw [if_neg]
    intro hBvisit
    exact hvisit ⟨B, hB, hBvisit⟩

/-- The total induced weight on a target type is the sum of the prescribed
totals of exactly those occupied metachains which visit it. -/
theorem totalInducedWeightOnType_distributed_eq_sum_startTypes
    (total : TypeCounts n → ℝ) (k : ℕ) (hk : 0 < k)
    (a c : ℕ) :
    totalInducedWeightOnType n a c (distributedChainWeight total k) =
      ∑ t ∈ occupiedStartTypes n k,
        if StartGroupVisitsType n k t a c then total t else 0 := by
  rw [totalInducedWeightOnType_eq_sum_if_visits]
  calc
    ∑ B : BasicChain n,
        (if B.VisitsType a c then distributedChainWeight total k B else 0) =
      ∑ B ∈ goodDescriptors n k,
        (if B.VisitsType a c then distributedChainWeight total k B else 0) := by
          rw [goodDescriptors]
          simp only [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro B _hB
          by_cases hgood : B.IsGood k
          · simp [hgood]
          · simp [hgood, distributedChainWeight]
    _ = ∑ t ∈ occupiedStartTypes n k,
        ∑ B ∈ startGroup n k t,
          (if B.VisitsType a c then distributedChainWeight total k B else 0) :=
      sum_goodDescriptors_eq_sum_startGroups k _
    _ = ∑ t ∈ occupiedStartTypes n k,
        if StartGroupVisitsType n k t a c then total t else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply sum_distributedChainWeight_startGroup_if_visits total k hk t a c
      exact (mem_occupiedStartTypes_iff t k).1 ht

end BasicChain
end Ternary
end WeightedChains
