import WeightedChains.DTwoOccupiedStartTypes

/-!
# Arithmetic traces of canonical ternary metachains

The types visited by a basic chain have the alternating coordinate pattern
displayed in Section 5.  This file expresses that pattern without dependent
proof arguments and then shows that the canonical start label alone determines
the resulting incidence relation.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary

/-- The alternating even/odd type trace of a basic chain with the displayed
raw initial zero count, two count, and width. -/
def TraceCoordinates
    (startZeros startTwos width targetZeros targetTwos : ℕ) : Prop :=
  (∃ i : Fin (width + 1),
      targetZeros + i = startZeros ∧ targetTwos = startTwos + i) ∨
    (∃ i : Fin width,
      targetZeros + i + 1 = startZeros ∧ targetTwos = startTwos + i)

instance decidableTraceCoordinates
    (startZeros startTwos width targetZeros targetTwos : ℕ) :
    Decidable (TraceCoordinates startZeros startTwos width targetZeros targetTwos) := by
  unfold TraceCoordinates
  infer_instance

namespace BasicChain

variable {n : ℕ}

/-- Descriptor incidence is exactly the alternating arithmetic trace of its
raw initial type. -/
theorem visitsType_iff_traceCoordinates
    (B : BasicChain n) (a c : ℕ) :
    B.VisitsType a c ↔
      TraceCoordinates (zeroCount B.start) (twoCount B.start) B.width a c := by
  rw [B.visitsType_iff_exists_vertex]
  constructor
  · rintro ⟨j, hjZero, hjTwo⟩
    have hjBound : (j : ℕ) ≤ 2 * B.width := by
      have hjLt := j.isLt
      simp only [B.toChain_steps] at hjLt
      omega
    obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' (j : ℕ)
    · left
      have hiWidth : i ≤ B.width := by omega
      let q : Fin (B.width + 1) := ⟨i, by omega⟩
      refine ⟨q, ?_, ?_⟩
      · change zeroCount (B.vertexAt (j : ℕ)) = a at hjZero
        rw [hi, B.vertexAt_even,
          B.zeroCount_evenVertex i hiWidth] at hjZero
        dsimp [q]
        have hiStart : i ≤ zeroCount B.start :=
          hiWidth.trans B.width_le_zeroCount
        omega
      · change twoCount (B.vertexAt (j : ℕ)) = c at hjTwo
        rw [hi, B.vertexAt_even,
          B.twoCount_evenVertex i hiWidth] at hjTwo
        simpa only [q] using hjTwo.symm
    · right
      have hiWidth : i < B.width := by omega
      let q : Fin B.width := ⟨i, hiWidth⟩
      refine ⟨q, ?_, ?_⟩
      · change zeroCount (B.vertexAt (j : ℕ)) = a at hjZero
        rw [hi, B.vertexAt_odd i hiWidth,
          B.zeroCount_oddVertex i hiWidth] at hjZero
        dsimp [q]
        have hiStart : i + 1 ≤ zeroCount B.start := by
          exact (Nat.succ_le_iff.mpr hiWidth).trans B.width_le_zeroCount
        omega
      · change twoCount (B.vertexAt (j : ℕ)) = c at hjTwo
        rw [hi, B.vertexAt_odd i hiWidth,
          B.twoCount_oddVertex i hiWidth] at hjTwo
        simpa only [q] using hjTwo.symm
  · rintro (heven | hodd)
    · obtain ⟨i, hiZero, hiTwo⟩ := heven
      let j : Fin (B.toChain.steps + 1) :=
        ⟨2 * (i : ℕ), by
          simp only [B.toChain_steps]
          have hi := i.isLt
          omega⟩
      refine ⟨j, ?_, ?_⟩
      · change zeroCount (B.vertexAt (j : ℕ)) = a
        rw [show (j : ℕ) = 2 * (i : ℕ) by rfl, B.vertexAt_even,
          B.zeroCount_evenVertex (i : ℕ) (by omega)]
        have hiStart : (i : ℕ) ≤ zeroCount B.start :=
          (Nat.le_of_lt_succ i.isLt).trans B.width_le_zeroCount
        omega
      · change twoCount (B.vertexAt (j : ℕ)) = c
        rw [show (j : ℕ) = 2 * (i : ℕ) by rfl, B.vertexAt_even,
          B.twoCount_evenVertex (i : ℕ) (by omega)]
        omega
    · obtain ⟨i, hiZero, hiTwo⟩ := hodd
      let j : Fin (B.toChain.steps + 1) :=
        ⟨2 * (i : ℕ) + 1, by
          simp only [B.toChain_steps]
          have hi := i.isLt
          omega⟩
      refine ⟨j, ?_, ?_⟩
      · change zeroCount (B.vertexAt (j : ℕ)) = a
        rw [show (j : ℕ) = 2 * (i : ℕ) + 1 by rfl,
          B.vertexAt_odd (i : ℕ) i.isLt,
          B.zeroCount_oddVertex (i : ℕ) i.isLt]
        have hiStart : (i : ℕ) + 1 ≤ zeroCount B.start :=
          (Nat.succ_le_iff.mpr i.isLt).trans B.width_le_zeroCount
        omega
      · change twoCount (B.vertexAt (j : ℕ)) = c
        rw [show (j : ℕ) = 2 * (i : ℕ) + 1 by rfl,
          B.vertexAt_odd (i : ℕ) i.isLt,
          B.twoCount_oddVertex (i : ℕ) i.isLt]
        omega

end BasicChain

/-- Raw initial zero count determined by a canonical start label. -/
def canonicalRawZeros {n : ℕ} (k : ℕ) (t : TypeCounts n) : ℕ :=
  if t.twos ≤ t.zeros then t.zeros else t.zeros + k

/-- Raw initial two count determined by a canonical start label. -/
def canonicalRawTwos {n : ℕ} (k : ℕ) (t : TypeCounts n) : ℕ :=
  if t.twos ≤ t.zeros then t.twos else t.twos - k

/-- The type-level incidence relation for the canonical metachain labelled
by `t`. -/
def CanonicalTypeVisits {n : ℕ} (k : ℕ) (t : TypeCounts n)
    (a c : ℕ) : Prop :=
  TraceCoordinates (canonicalRawZeros k t) (canonicalRawTwos k t)
    (BasicChain.canonicalWidth k t) a c

instance decidableCanonicalTypeVisits {n : ℕ} (k : ℕ)
    (t : TypeCounts n) (a c : ℕ) : Decidable (CanonicalTypeVisits k t a c) := by
  unfold CanonicalTypeVisits
  infer_instance

namespace BasicChain

/-- A descriptor in a canonical start group has the raw initial counts
specified by its group label. -/
theorem start_counts_eq_canonicalRaw_of_mem_startGroup
    {n k : ℕ} (hk : 0 < k) (t : TypeCounts n) {B : BasicChain n}
    (hB : B ∈ startGroup n k t) :
    zeroCount B.start = canonicalRawZeros k t ∧
      twoCount B.start = canonicalRawTwos k t := by
  obtain ⟨hgood, htype⟩ := (mem_startGroup_iff B k t).1 hB
  by_cases hlower : t.twos ≤ t.zeros
  · have hfirst : B.toChain.StartsAtFirst := by
      by_contra hnot
      have hupper :=
        canonicalStartType_zeros_add_k_lt_twos_of_not_first_of_good
          B k hk hnot hgood
      rw [htype] at hupper
      omega
    have hstartType : TypeCounts.ofVertex B.start = t := by
      calc
        TypeCounts.ofVertex B.start = B.canonicalStartType := by
          rw [B.canonicalStartType_eq_first hfirst, B.toChain_first]
        _ = t := htype
    have hzero := congrArg TypeCounts.zeros hstartType
    have htwo := congrArg TypeCounts.twos hstartType
    change zeroCount B.start = t.zeros at hzero
    change twoCount B.start = t.twos at htwo
    simpa [canonicalRawZeros, canonicalRawTwos, hlower] using And.intro hzero htwo
  · have hnotFirst : ¬B.toChain.StartsAtFirst := by
      intro hfirst
      have hlower' := canonicalStartType_twos_le_zeros_of_first_of_good
        B k hk hfirst hgood
      rw [htype] at hlower'
      exact hlower hlower'
    have hwidth : (B.width : ℕ) = k :=
      width_eq_k_of_not_startsAtFirst_of_good B k hnotFirst hgood
    have hlastType : TypeCounts.ofVertex B.toChain.last = t := by
      rw [← htype, B.canonicalStartType_eq_last hnotFirst]
    have hzeroLast := congrArg TypeCounts.zeros hlastType
    have htwoLast := congrArg TypeCounts.twos hlastType
    change zeroCount B.toChain.last = t.zeros at hzeroLast
    change twoCount B.toChain.last = t.twos at htwoLast
    have hzeroFormula := B.zeroCount_evenVertex B.width le_rfl
    have htwoFormula := B.twoCount_evenVertex B.width le_rfl
    rw [← B.toChain_last] at hzeroFormula htwoFormula
    have hbound := B.width_le_zeroCount
    have hkTwo : k ≤ t.twos := by omega
    constructor
    · rw [canonicalRawZeros, if_neg hlower]
      omega
    · rw [canonicalRawTwos, if_neg hlower]
      omega

/-- For every occupied canonical group, descriptor incidence agrees with the
pure arithmetic relation `CanonicalTypeVisits`. -/
theorem visitsType_iff_canonicalTypeVisits_of_mem_startGroup
    {n k : ℕ} (hk : 0 < k) (t : TypeCounts n) (a c : ℕ)
    {B : BasicChain n} (hB : B ∈ startGroup n k t) :
    B.VisitsType a c ↔ CanonicalTypeVisits k t a c := by
  rw [B.visitsType_iff_traceCoordinates]
  obtain ⟨hzero, htwo⟩ :=
    start_counts_eq_canonicalRaw_of_mem_startGroup hk t hB
  have hwidth := width_eq_canonicalWidth_of_good B k hk
    ((mem_startGroup_iff B k t).1 hB).1
  have htype := ((mem_startGroup_iff B k t).1 hB).2
  rw [hzero, htwo, hwidth, htype]
  rfl

/-- Group incidence itself has the same arithmetic characterisation. -/
theorem startGroupVisitsType_iff_canonicalTypeVisits
    {n k : ℕ} (hk : 0 < k) (t : TypeCounts n) (a c : ℕ)
    (ht : (startGroup n k t).Nonempty) :
    StartGroupVisitsType n k t a c ↔ CanonicalTypeVisits k t a c := by
  obtain ⟨B, hB⟩ := ht
  constructor
  · rintro ⟨C, hC, hCvisit⟩
    exact (visitsType_iff_canonicalTypeVisits_of_mem_startGroup
      hk t a c hC).1 hCvisit
  · intro hvisit
    exact ⟨B, hB,
      (visitsType_iff_canonicalTypeVisits_of_mem_startGroup
        hk t a c hB).2 hvisit⟩

/-- The concrete distributed weighting reduces the cover calculation to a
fully arithmetic finite sum over canonical type traces. -/
theorem totalInducedWeightOnType_startTypeTotal_eq_arithmetic_sum
    {n k : ℕ} (hk : 0 < k) (a c : ℕ) :
    totalInducedWeightOnType n a c
        (distributedChainWeight (startTypeTotal k) k) =
      ∑ t ∈ occupiedStartTypes n k,
        if CanonicalTypeVisits k t a c then startTypeTotal k t else 0 := by
  rw [totalInducedWeightOnType_distributed_eq_sum_startTypes
    (startTypeTotal k) k hk a c]
  apply Finset.sum_congr rfl
  intro t ht
  have hnonempty := (mem_occupiedStartTypes_iff t k).1 ht
  have hiff := startGroupVisitsType_iff_canonicalTypeVisits
    hk t a c hnonempty
  by_cases hvisit : CanonicalTypeVisits k t a c
  · have hgroup := hiff.2 hvisit
    simp [hvisit, hgroup]
  · have hgroup : ¬StartGroupVisitsType n k t a c := by
      intro h
      exact hvisit (hiff.1 h)
    simp [hvisit, hgroup]

end BasicChain
end Ternary
end WeightedChains
