import WeightedChains.DTwo.AuxiliaryIncidenceSum

/-!
# Canonical ternary incidence as the two auxiliary diagonals

For a lower target type, every incident lower canonical metachain has a
unique even or odd raw start on one of two diagonals.  An inner lower
metachain is paired with the full-width upper metachain having the same raw
start.  Their starting totals add to the auxiliary weight of that raw start.

This file makes that pairing finite and explicit.  It is the bookkeeping
bridge between the canonical start-type sum and the telescoping identity for
`auxiliaryIncidenceSum`.
-/

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace WeightedChains
namespace Ternary

/-- Even positions on the raw-start diagonal which have nonnegative second
coordinate. -/
abbrev EvenTraceIndex (k c : ℕ) :=
  {i : Fin (k + 1) // (i : ℕ) ≤ c}

/-- Odd positions on the raw-start diagonal which define a valid ternary
type. -/
abbrev OddTraceIndex (n k a c : ℕ) :=
  {i : Fin k // (i : ℕ) ≤ c ∧ a + c + 1 ≤ n}

/-- Even raw starts whose full-width chain has an upper canonical label. -/
abbrev EvenUpperTraceIndex (k a c : ℕ) :=
  {i : EvenTraceIndex k c //
    k ≤ a + (i : ℕ) ∧ a + (i : ℕ) < c - (i : ℕ) + k}

/-- Odd raw starts whose full-width chain has an upper canonical label. -/
abbrev OddUpperTraceIndex (n k a c : ℕ) :=
  {i : OddTraceIndex n k a c //
    k ≤ a + (i : ℕ) + 1 ∧
      a + (i : ℕ) + 1 < c - (i : ℕ) + k}

/-- The lower canonical label of an even raw start through `(a,c)`. -/
def lowerEvenStartType (n k a c : ℕ) (hvalid : a + c ≤ n)
    (i : EvenTraceIndex k c) : TypeCounts n where
  zeros := a + (i : ℕ)
  ones := n - (a + c)
  twos := c - (i : ℕ)
  sum_eq := by omega

/-- The lower canonical label of an odd raw start through `(a,c)`. -/
def lowerOddStartType (n k a c : ℕ)
    (i : OddTraceIndex n k a c) : TypeCounts n where
  zeros := a + (i : ℕ) + 1
  ones := n - (a + c + 1)
  twos := c - (i : ℕ)
  sum_eq := by omega

/-- The upper canonical label of the full-width chain paired with an inner
even lower raw start. -/
def upperEvenStartType (n k a c : ℕ) (hvalid : a + c ≤ n)
    (i : EvenUpperTraceIndex k a c) : TypeCounts n where
  zeros := a + (i : ℕ) - k
  ones := n - (a + c)
  twos := c - (i : ℕ) + k
  sum_eq := by omega

/-- The upper canonical label of the full-width chain paired with an inner
odd lower raw start. -/
def upperOddStartType (n k a c : ℕ)
    (i : OddUpperTraceIndex n k a c) : TypeCounts n where
  zeros := a + (i : ℕ) + 1 - k
  ones := n - (a + c + 1)
  twos := c - (i : ℕ) + k
  sum_eq := by
    have hic : (i : ℕ) ≤ c := i.1.2.1
    have hdim : a + c + 1 ≤ n := i.1.2.2
    have hk : k ≤ a + (i : ℕ) + 1 := i.2.1
    omega

@[simp] theorem lowerEvenStartType_zeros (n k a c : ℕ)
    (hvalid : a + c ≤ n) (i : EvenTraceIndex k c) :
    (lowerEvenStartType n k a c hvalid i).zeros = a + (i : ℕ) := rfl

@[simp] theorem lowerEvenStartType_twos (n k a c : ℕ)
    (hvalid : a + c ≤ n) (i : EvenTraceIndex k c) :
    (lowerEvenStartType n k a c hvalid i).twos = c - (i : ℕ) := rfl

@[simp] theorem lowerOddStartType_zeros (n k a c : ℕ)
    (i : OddTraceIndex n k a c) :
    (lowerOddStartType n k a c i).zeros = a + (i : ℕ) + 1 := rfl

@[simp] theorem lowerOddStartType_twos (n k a c : ℕ)
    (i : OddTraceIndex n k a c) :
    (lowerOddStartType n k a c i).twos = c - (i : ℕ) := rfl

@[simp] theorem upperEvenStartType_zeros (n k a c : ℕ)
    (hvalid : a + c ≤ n) (i : EvenUpperTraceIndex k a c) :
    (upperEvenStartType n k a c hvalid i).zeros =
      a + (i : ℕ) - k := rfl

@[simp] theorem upperEvenStartType_twos (n k a c : ℕ)
    (hvalid : a + c ≤ n) (i : EvenUpperTraceIndex k a c) :
    (upperEvenStartType n k a c hvalid i).twos =
      c - (i : ℕ) + k := rfl

@[simp] theorem upperOddStartType_zeros (n k a c : ℕ)
    (i : OddUpperTraceIndex n k a c) :
    (upperOddStartType n k a c i).zeros =
      a + (i : ℕ) + 1 - k := rfl

@[simp] theorem upperOddStartType_twos (n k a c : ℕ)
    (i : OddUpperTraceIndex n k a c) :
    (upperOddStartType n k a c i).twos =
      c - (i : ℕ) + k := rfl

private theorem lowerEvenStartType_lower
    (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a)
    (i : EvenTraceIndex k c) :
    (lowerEvenStartType n k a c hvalid i).twos ≤
      (lowerEvenStartType n k a c hvalid i).zeros := by
  simp only [lowerEvenStartType_twos, lowerEvenStartType_zeros]
  omega

private theorem lowerOddStartType_lower
    (n k a c : ℕ) (hca : c ≤ a) (i : OddTraceIndex n k a c) :
    (lowerOddStartType n k a c i).twos ≤
      (lowerOddStartType n k a c i).zeros := by
  simp only [lowerOddStartType_twos, lowerOddStartType_zeros]
  omega

private theorem lowerEvenStartType_visits
    (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a)
    (i : EvenTraceIndex k c) :
    CanonicalTypeVisits k (lowerEvenStartType n k a c hvalid i) a c := by
  have hlower := lowerEvenStartType_lower n k a c hvalid hca i
  unfold CanonicalTypeVisits canonicalRawZeros canonicalRawTwos
    BasicChain.canonicalWidth TraceCoordinates
  rw [if_pos hlower, if_pos hlower, if_pos hlower]
  left
  have hiDiff : (i : ℕ) ≤
      (lowerEvenStartType n k a c hvalid i).zeros -
        (lowerEvenStartType n k a c hvalid i).twos := by
    simp only [lowerEvenStartType_zeros, lowerEvenStartType_twos]
    omega
  let j : Fin (min k
      ((lowerEvenStartType n k a c hvalid i).zeros -
        (lowerEvenStartType n k a c hvalid i).twos) + 1) :=
    ⟨i, by simp only [Nat.lt_add_one_iff]; apply le_min <;> omega⟩
  refine ⟨j, ?_, ?_⟩
  · simp only [lowerEvenStartType_zeros]
    dsimp [j]
  · simp only [lowerEvenStartType_twos]
    dsimp [j]
    omega

private theorem lowerOddStartType_visits
    (n k a c : ℕ) (hca : c ≤ a) (i : OddTraceIndex n k a c) :
    CanonicalTypeVisits k (lowerOddStartType n k a c i) a c := by
  have hlower := lowerOddStartType_lower n k a c hca i
  unfold CanonicalTypeVisits canonicalRawZeros canonicalRawTwos
    BasicChain.canonicalWidth TraceCoordinates
  rw [if_pos hlower, if_pos hlower, if_pos hlower]
  right
  have hiDiff : (i : ℕ) <
      (lowerOddStartType n k a c i).zeros -
        (lowerOddStartType n k a c i).twos := by
    simp only [lowerOddStartType_zeros, lowerOddStartType_twos]
    omega
  let j : Fin (min k
      ((lowerOddStartType n k a c i).zeros -
        (lowerOddStartType n k a c i).twos)) :=
    ⟨i, lt_min i.1.isLt hiDiff⟩
  refine ⟨j, ?_, ?_⟩
  · simp only [lowerOddStartType_zeros]
    dsimp [j]
  · simp only [lowerOddStartType_twos]
    dsimp [j]
    omega

private theorem upperEvenStartType_upper
    (n k a c : ℕ) (hvalid : a + c ≤ n)
    (i : EvenUpperTraceIndex k a c) :
    (upperEvenStartType n k a c hvalid i).zeros + k <
      (upperEvenStartType n k a c hvalid i).twos := by
  simp only [upperEvenStartType_zeros, upperEvenStartType_twos]
  omega

private theorem upperOddStartType_upper
    (n k a c : ℕ) (i : OddUpperTraceIndex n k a c) :
    (upperOddStartType n k a c i).zeros + k <
      (upperOddStartType n k a c i).twos := by
  simp only [upperOddStartType_zeros, upperOddStartType_twos]
  omega

private theorem upperEvenStartType_visits
    (n k a c : ℕ) (hvalid : a + c ≤ n)
    (i : EvenUpperTraceIndex k a c) :
    CanonicalTypeVisits k (upperEvenStartType n k a c hvalid i) a c := by
  have hupper := upperEvenStartType_upper n k a c hvalid i
  have hnotLower : ¬(upperEvenStartType n k a c hvalid i).twos ≤
      (upperEvenStartType n k a c hvalid i).zeros := by omega
  unfold CanonicalTypeVisits canonicalRawZeros canonicalRawTwos
    BasicChain.canonicalWidth TraceCoordinates
  rw [if_neg hnotLower, if_neg hnotLower, if_neg hnotLower]
  left
  let j : Fin (k + 1) := ⟨i, i.1.1.isLt⟩
  refine ⟨j, ?_, ?_⟩
  · simp only [upperEvenStartType_zeros]
    dsimp [j]
    omega
  · simp only [upperEvenStartType_twos]
    dsimp [j]
    omega

private theorem upperOddStartType_visits
    (n k a c : ℕ) (i : OddUpperTraceIndex n k a c) :
    CanonicalTypeVisits k (upperOddStartType n k a c i) a c := by
  have hupper := upperOddStartType_upper n k a c i
  have hnotLower : ¬(upperOddStartType n k a c i).twos ≤
      (upperOddStartType n k a c i).zeros := by omega
  unfold CanonicalTypeVisits canonicalRawZeros canonicalRawTwos
    BasicChain.canonicalWidth TraceCoordinates
  rw [if_neg hnotLower, if_neg hnotLower, if_neg hnotLower]
  right
  let j : Fin k := ⟨i, i.1.1.isLt⟩
  refine ⟨j, ?_, ?_⟩
  · simp only [upperOddStartType_zeros]
    dsimp [j]
    omega
  · simp only [upperOddStartType_twos]
    dsimp [j]
    omega

/-- Lower canonical labels incident with a fixed target. -/
abbrev LowerVisitedType (n k a c : ℕ) :=
  {t : TypeCounts n // t.twos ≤ t.zeros ∧ CanonicalTypeVisits k t a c}

/-- Upper occupied canonical labels incident with a fixed target. -/
abbrev UpperVisitedType (n k a c : ℕ) :=
  {t : TypeCounts n //
    t.zeros + k < t.twos ∧ CanonicalTypeVisits k t a c}

/-- Package the two lower raw-start diagonals as incident canonical labels. -/
def lowerTraceType (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    EvenTraceIndex k c ⊕ OddTraceIndex n k a c →
      LowerVisitedType n k a c
  | .inl i => ⟨lowerEvenStartType n k a c hvalid i,
      lowerEvenStartType_lower n k a c hvalid hca i,
      lowerEvenStartType_visits n k a c hvalid hca i⟩
  | .inr i => ⟨lowerOddStartType n k a c i,
      lowerOddStartType_lower n k a c hca i,
      lowerOddStartType_visits n k a c hca i⟩

private theorem lowerTraceType_injective
    (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    Function.Injective (lowerTraceType n k a c hvalid hca) := by
  intro x y hxy
  have htype := congrArg Subtype.val hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          have hzero := congrArg TypeCounts.zeros htype
          simp only [lowerTraceType, lowerEvenStartType_zeros] at hzero
          congr 1
          apply Subtype.ext
          apply Fin.ext
          omega
      | inr j =>
          have hzero := congrArg TypeCounts.zeros htype
          have htwo := congrArg TypeCounts.twos htype
          simp only [lowerTraceType, lowerEvenStartType_zeros,
            lowerOddStartType_zeros] at hzero
          simp only [lowerTraceType, lowerEvenStartType_twos,
            lowerOddStartType_twos] at htwo
          exfalso
          omega
  | inr i =>
      cases y with
      | inl j =>
          have hzero := congrArg TypeCounts.zeros htype
          have htwo := congrArg TypeCounts.twos htype
          simp only [lowerTraceType, lowerOddStartType_zeros,
            lowerEvenStartType_zeros] at hzero
          simp only [lowerTraceType, lowerOddStartType_twos,
            lowerEvenStartType_twos] at htwo
          exfalso
          omega
      | inr j =>
          have hzero := congrArg TypeCounts.zeros htype
          simp only [lowerTraceType, lowerOddStartType_zeros] at hzero
          congr 1
          apply Subtype.ext
          apply Fin.ext
          omega

private theorem lowerTraceType_surjective
    (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    Function.Surjective (lowerTraceType n k a c hvalid hca) := by
  rintro ⟨t, hlower, hvisit⟩
  unfold CanonicalTypeVisits canonicalRawZeros canonicalRawTwos
    BasicChain.canonicalWidth at hvisit
  rw [if_pos hlower, if_pos hlower, if_pos hlower] at hvisit
  rcases hvisit with heven | hodd
  · obtain ⟨j, hjZero, hjTwo⟩ := heven
    have hjk : (j : ℕ) ≤ k := by
      have hjBound := j.isLt
      omega
    have hjc : (j : ℕ) ≤ c := by omega
    let i : EvenTraceIndex k c :=
      ⟨⟨j, by omega⟩, hjc⟩
    refine ⟨Sum.inl i, ?_⟩
    apply Subtype.ext
    apply TypeCounts.ext
    · simp only [lowerTraceType, lowerEvenStartType_zeros]
      dsimp [i]
      omega
    · simp only [lowerTraceType, lowerEvenStartType]
      have hsum := t.sum_eq
      omega
    · simp only [lowerTraceType, lowerEvenStartType_twos]
      dsimp [i]
      omega
  · obtain ⟨j, hjZero, hjTwo⟩ := hodd
    have hjk : (j : ℕ) < k := by
      have hjBound := j.isLt
      omega
    have hjc : (j : ℕ) ≤ c := by omega
    have hdimension : a + c + 1 ≤ n := by
      have hsum := t.sum_eq
      omega
    let i : OddTraceIndex n k a c :=
      ⟨⟨j, hjk⟩, hjc, hdimension⟩
    refine ⟨Sum.inr i, ?_⟩
    apply Subtype.ext
    apply TypeCounts.ext
    · simp only [lowerTraceType, lowerOddStartType_zeros]
      dsimp [i]
      omega
    · simp only [lowerTraceType, lowerOddStartType]
      have hsum := t.sum_eq
      omega
    · simp only [lowerTraceType, lowerOddStartType_twos]
      dsimp [i]
      omega

/-- Incident lower canonical labels are exactly the disjoint union of the
even and odd raw-start diagonals. -/
def lowerTraceEquiv (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    EvenTraceIndex k c ⊕ OddTraceIndex n k a c ≃
      LowerVisitedType n k a c :=
  Equiv.ofBijective (lowerTraceType n k a c hvalid hca)
    ⟨lowerTraceType_injective n k a c hvalid hca,
      lowerTraceType_surjective n k a c hvalid hca⟩

/-- Package the upper partners of inner raw starts as incident canonical
labels. -/
def upperTraceType (n k a c : ℕ) (hvalid : a + c ≤ n) :
    EvenUpperTraceIndex k a c ⊕ OddUpperTraceIndex n k a c →
      UpperVisitedType n k a c
  | .inl i => ⟨upperEvenStartType n k a c hvalid i,
      upperEvenStartType_upper n k a c hvalid i,
      upperEvenStartType_visits n k a c hvalid i⟩
  | .inr i => ⟨upperOddStartType n k a c i,
      upperOddStartType_upper n k a c i,
      upperOddStartType_visits n k a c i⟩

private theorem upperTraceType_injective
    (n k a c : ℕ) (hvalid : a + c ≤ n) :
    Function.Injective (upperTraceType n k a c hvalid) := by
  intro x y hxy
  have htype := congrArg Subtype.val hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          have htwo := congrArg TypeCounts.twos htype
          simp only [upperTraceType, upperEvenStartType_twos] at htwo
          congr 1
          apply Subtype.ext
          apply Subtype.ext
          apply Fin.ext
          omega
      | inr j =>
          have hzero := congrArg TypeCounts.zeros htype
          have htwo := congrArg TypeCounts.twos htype
          simp only [upperTraceType, upperEvenStartType_zeros,
            upperOddStartType_zeros] at hzero
          simp only [upperTraceType, upperEvenStartType_twos,
            upperOddStartType_twos] at htwo
          have hiK : k ≤ a + (i : ℕ) := i.2.1
          have hjK : k ≤ a + (j : ℕ) + 1 := j.2.1
          exfalso
          omega
  | inr i =>
      cases y with
      | inl j =>
          have hzero := congrArg TypeCounts.zeros htype
          have htwo := congrArg TypeCounts.twos htype
          simp only [upperTraceType, upperOddStartType_zeros,
            upperEvenStartType_zeros] at hzero
          simp only [upperTraceType, upperOddStartType_twos,
            upperEvenStartType_twos] at htwo
          have hiK : k ≤ a + (i : ℕ) + 1 := i.2.1
          have hjK : k ≤ a + (j : ℕ) := j.2.1
          exfalso
          omega
      | inr j =>
          have htwo := congrArg TypeCounts.twos htype
          simp only [upperTraceType, upperOddStartType_twos] at htwo
          congr 1
          apply Subtype.ext
          apply Subtype.ext
          apply Fin.ext
          omega

private theorem upperTraceType_surjective
    (n k a c : ℕ) (hvalid : a + c ≤ n) :
    Function.Surjective (upperTraceType n k a c hvalid) := by
  rintro ⟨t, hupper, hvisit⟩
  have hnotLower : ¬t.twos ≤ t.zeros := by omega
  have hktwo : k ≤ t.twos := by omega
  unfold CanonicalTypeVisits canonicalRawZeros canonicalRawTwos
    BasicChain.canonicalWidth at hvisit
  rw [if_neg hnotLower, if_neg hnotLower, if_neg hnotLower] at hvisit
  rcases hvisit with heven | hodd
  · obtain ⟨j, hjZero, hjTwo⟩ := heven
    have hjc : (j : ℕ) ≤ c := by omega
    have hkStart : k ≤ a + (j : ℕ) := by omega
    have hinner : a + (j : ℕ) < c - (j : ℕ) + k := by omega
    let base : EvenTraceIndex k c := ⟨j, hjc⟩
    let i : EvenUpperTraceIndex k a c := ⟨base, hkStart, hinner⟩
    refine ⟨Sum.inl i, ?_⟩
    apply Subtype.ext
    apply TypeCounts.ext
    · simp only [upperTraceType, upperEvenStartType_zeros]
      dsimp [i, base]
      omega
    · simp only [upperTraceType, upperEvenStartType]
      have hsum := t.sum_eq
      omega
    · simp only [upperTraceType, upperEvenStartType_twos]
      dsimp [i, base]
      omega
  · obtain ⟨j, hjZero, hjTwo⟩ := hodd
    have hjc : (j : ℕ) ≤ c := by omega
    have hkStart : k ≤ a + (j : ℕ) + 1 := by omega
    have hinner : a + (j : ℕ) + 1 < c - (j : ℕ) + k := by omega
    have hdimension : a + c + 1 ≤ n := by
      have hsum := t.sum_eq
      omega
    let base : OddTraceIndex n k a c :=
      ⟨j, hjc, hdimension⟩
    let i : OddUpperTraceIndex n k a c := ⟨base, hkStart, hinner⟩
    refine ⟨Sum.inr i, ?_⟩
    apply Subtype.ext
    apply TypeCounts.ext
    · simp only [upperTraceType, upperOddStartType_zeros]
      dsimp [i, base]
      omega
    · simp only [upperTraceType, upperOddStartType]
      have hsum := t.sum_eq
      omega
    · simp only [upperTraceType, upperOddStartType_twos]
      dsimp [i, base]
      omega

/-- Incident upper occupied canonical labels are exactly the full-width
partners of the inner positions on the two raw-start diagonals. -/
def upperTraceEquiv (n k a c : ℕ) (hvalid : a + c ≤ n) :
    EvenUpperTraceIndex k a c ⊕ OddUpperTraceIndex n k a c ≃
      UpperVisitedType n k a c :=
  Equiv.ofBijective (upperTraceType n k a c hvalid)
    ⟨upperTraceType_injective n k a c hvalid,
      upperTraceType_surjective n k a c hvalid⟩

/-- Integer starting total contributed by all occupied canonical labels which
visit a target type. -/
def canonicalStartWeightIncidenceSum (n k a c : ℕ) : ℤ :=
  ∑ t ∈ BasicChain.occupiedStartTypes n k,
    if CanonicalTypeVisits k t a c then startTypeWeight k t else 0

private theorem canonicalStartWeightIncidenceSum_eq_lower_add_upper
    (n k a c : ℕ) (hk : 0 < k) :
    canonicalStartWeightIncidenceSum n k a c =
      (∑ t : LowerVisitedType n k a c, startTypeWeight k t.1) +
        ∑ t : UpperVisitedType n k a c, startTypeWeight k t.1 := by
  unfold canonicalStartWeightIncidenceSum
  rw [BasicChain.occupiedStartTypes_eq_filter_arithmetic n k hk,
    Finset.sum_filter]
  have hsplit :
      (∑ t : TypeCounts n,
          if (t.twos ≤ t.zeros ∨ t.zeros + k < t.twos) then
            (if CanonicalTypeVisits k t a c then startTypeWeight k t else 0)
          else 0) =
        (∑ t : TypeCounts n,
          if t.twos ≤ t.zeros ∧ CanonicalTypeVisits k t a c then
            startTypeWeight k t else 0) +
        ∑ t : TypeCounts n,
          if t.zeros + k < t.twos ∧ CanonicalTypeVisits k t a c then
            startTypeWeight k t else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    by_cases hvisit : CanonicalTypeVisits k t a c
    · by_cases hlower : t.twos ≤ t.zeros
      · have hnotUpper : ¬t.zeros + k < t.twos := by omega
        simp [hvisit, hlower, hnotUpper]
      · simp [hvisit, hlower]
    · simp [hvisit]
  rw [hsplit]
  congr 1
  · calc
      (∑ t : TypeCounts n,
          if t.twos ≤ t.zeros ∧ CanonicalTypeVisits k t a c then
            startTypeWeight k t else 0) =
          ∑ t ∈ Finset.univ.filter (fun t : TypeCounts n ↦
            t.twos ≤ t.zeros ∧ CanonicalTypeVisits k t a c),
              startTypeWeight k t :=
        (Finset.sum_filter _ _).symm
      _ = ∑ t : LowerVisitedType n k a c, startTypeWeight k t.1 := by
        apply Finset.sum_subtype
        intro t
        simp
  · calc
      (∑ t : TypeCounts n,
          if t.zeros + k < t.twos ∧ CanonicalTypeVisits k t a c then
            startTypeWeight k t else 0) =
          ∑ t ∈ Finset.univ.filter (fun t : TypeCounts n ↦
            t.zeros + k < t.twos ∧ CanonicalTypeVisits k t a c),
              startTypeWeight k t :=
        (Finset.sum_filter _ _).symm
      _ = ∑ t : UpperVisitedType n k a c, startTypeWeight k t.1 := by
        apply Finset.sum_subtype
        intro t
        simp

/-- Reindex the canonical incidence total by the four explicit trace-index
types, before pairing their weights. -/
theorem canonicalStartWeightIncidenceSum_eq_trace_sums
    (n k a c : ℕ) (hk : 0 < k) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    canonicalStartWeightIncidenceSum n k a c =
      (∑ i : EvenTraceIndex k c,
          startTypeWeight k (lowerEvenStartType n k a c hvalid i)) +
      (∑ i : OddTraceIndex n k a c,
          startTypeWeight k (lowerOddStartType n k a c i)) +
      ((∑ i : EvenUpperTraceIndex k a c,
          startTypeWeight k (upperEvenStartType n k a c hvalid i)) +
      ∑ i : OddUpperTraceIndex n k a c,
          startTypeWeight k (upperOddStartType n k a c i)) := by
  rw [canonicalStartWeightIncidenceSum_eq_lower_add_upper n k a c hk]
  rw [← (Equiv.sum_comp (lowerTraceEquiv n k a c hvalid hca)
    (fun t : LowerVisitedType n k a c ↦ startTypeWeight k t.1))]
  rw [← (Equiv.sum_comp (upperTraceEquiv n k a c hvalid)
    (fun t : UpperVisitedType n k a c ↦ startTypeWeight k t.1))]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl

/-- Auxiliary weight of an even raw start. -/
def evenRawAuxiliaryWeight (n k a c : ℕ) (i : EvenTraceIndex k c) : ℤ :=
  auxiliaryWeight n k (a + (i : ℕ)) (c - (i : ℕ))

/-- Correction term paired with an even inner raw start.  Integer subtraction
is intentional: it also covers starts with fewer than `k` zero coordinates,
where the correction vanishes by zero extension. -/
def evenShiftedAuxiliaryWeight
    (n k a c : ℕ) (i : EvenTraceIndex k c) : ℤ :=
  auxiliaryWeight n k
    ((c - (i : ℕ) : ℕ) + k)
    ((a + (i : ℕ) : ℕ) - (k : ℤ))

/-- Auxiliary weight of an odd raw start. -/
def oddRawAuxiliaryWeight
    (n k a c : ℕ) (i : OddTraceIndex n k a c) : ℤ :=
  auxiliaryWeight n k (a + (i : ℕ) + 1) (c - (i : ℕ))

/-- Correction term paired with an odd inner raw start. -/
def oddShiftedAuxiliaryWeight
    (n k a c : ℕ) (i : OddTraceIndex n k a c) : ℤ :=
  auxiliaryWeight n k
    ((c - (i : ℕ) : ℕ) + k)
    ((a + (i : ℕ) + 1 : ℕ) - (k : ℤ))

private theorem lowerEvenStartType_weight
    (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a)
    (i : EvenTraceIndex k c) :
    startTypeWeight k (lowerEvenStartType n k a c hvalid i) =
      if c - (i : ℕ) + k ≤ a + (i : ℕ) then
        evenRawAuxiliaryWeight n k a c i
      else
        evenRawAuxiliaryWeight n k a c i -
          evenShiftedAuxiliaryWeight n k a c i := by
  have hlower := lowerEvenStartType_lower n k a c hvalid hca i
  unfold startTypeWeight
  rw [if_pos hlower]
  simp only [lowerEvenStartType_zeros, lowerEvenStartType_twos]
  by_cases houter : c - (i : ℕ) + k ≤ a + (i : ℕ)
  · rw [if_pos houter]
    unfold evenRawAuxiliaryWeight
    norm_num only [Nat.cast_add, Nat.cast_sub i.2]
    rw [if_pos houter]
  · rw [if_neg houter]
    unfold evenRawAuxiliaryWeight evenShiftedAuxiliaryWeight
      innerStartingWeight
    norm_num only [Nat.cast_add, Nat.cast_sub i.2]
    rw [if_neg houter]

private theorem lowerOddStartType_weight
    (n k a c : ℕ) (hca : c ≤ a) (i : OddTraceIndex n k a c) :
    startTypeWeight k (lowerOddStartType n k a c i) =
      if c - (i : ℕ) + k ≤ a + (i : ℕ) + 1 then
        oddRawAuxiliaryWeight n k a c i
      else
        oddRawAuxiliaryWeight n k a c i -
          oddShiftedAuxiliaryWeight n k a c i := by
  have hlower := lowerOddStartType_lower n k a c hca i
  unfold startTypeWeight
  rw [if_pos hlower]
  simp only [lowerOddStartType_zeros, lowerOddStartType_twos]
  by_cases houter : c - (i : ℕ) + k ≤ a + (i : ℕ) + 1
  · rw [if_pos houter]
    unfold oddRawAuxiliaryWeight
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_sub i.2.1]
    rw [if_pos houter]
  · rw [if_neg houter]
    unfold oddRawAuxiliaryWeight oddShiftedAuxiliaryWeight
      innerStartingWeight
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_sub i.2.1]
    rw [if_neg houter]

private theorem upperEvenStartType_weight
    (n k a c : ℕ) (hvalid : a + c ≤ n)
    (i : EvenUpperTraceIndex k a c) :
    startTypeWeight k (upperEvenStartType n k a c hvalid i) =
      evenShiftedAuxiliaryWeight n k a c i.1 := by
  have hupper := upperEvenStartType_upper n k a c hvalid i
  have hnotLower : ¬(upperEvenStartType n k a c hvalid i).twos ≤
      (upperEvenStartType n k a c hvalid i).zeros := by omega
  have houter : (upperEvenStartType n k a c hvalid i).zeros + k ≤
      (upperEvenStartType n k a c hvalid i).twos := hupper.le
  unfold startTypeWeight
  rw [if_neg hnotLower, if_pos houter]
  unfold evenShiftedAuxiliaryWeight
  simp only [upperEvenStartType_twos, upperEvenStartType_zeros,
    Nat.cast_add, Nat.cast_sub i.2.1]

private theorem upperOddStartType_weight
    (n k a c : ℕ) (i : OddUpperTraceIndex n k a c) :
    startTypeWeight k (upperOddStartType n k a c i) =
      oddShiftedAuxiliaryWeight n k a c i.1 := by
  have hupper := upperOddStartType_upper n k a c i
  have hnotLower : ¬(upperOddStartType n k a c i).twos ≤
      (upperOddStartType n k a c i).zeros := by omega
  have houter : (upperOddStartType n k a c i).zeros + k ≤
      (upperOddStartType n k a c i).twos := hupper.le
  unfold startTypeWeight
  rw [if_neg hnotLower, if_pos houter]
  unfold oddShiftedAuxiliaryWeight
  simp only [upperOddStartType_twos, upperOddStartType_zeros,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub i.2.1]

private theorem evenTraceWeights_pair
    (n k a c : ℕ) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    (∑ i : EvenTraceIndex k c,
        startTypeWeight k (lowerEvenStartType n k a c hvalid i)) +
      (∑ i : EvenUpperTraceIndex k a c,
        startTypeWeight k (upperEvenStartType n k a c hvalid i)) =
      ∑ i : EvenTraceIndex k c, evenRawAuxiliaryWeight n k a c i := by
  have hupperSum :
      (∑ i : EvenUpperTraceIndex k a c,
          startTypeWeight k (upperEvenStartType n k a c hvalid i)) =
        ∑ i : EvenTraceIndex k c,
          if k ≤ a + (i : ℕ) ∧
              a + (i : ℕ) < c - (i : ℕ) + k then
            evenShiftedAuxiliaryWeight n k a c i else 0 := by
    calc
      (∑ i : EvenUpperTraceIndex k a c,
          startTypeWeight k (upperEvenStartType n k a c hvalid i)) =
          ∑ i : EvenUpperTraceIndex k a c,
            evenShiftedAuxiliaryWeight n k a c i.1 := by
        apply Fintype.sum_congr
        intro i
        exact upperEvenStartType_weight n k a c hvalid i
      _ = ∑ i ∈ Finset.univ.filter (fun i : EvenTraceIndex k c ↦
          k ≤ a + (i : ℕ) ∧
            a + (i : ℕ) < c - (i : ℕ) + k),
          evenShiftedAuxiliaryWeight n k a c i := by
        symm
        apply Finset.sum_subtype
        intro i
        simp
      _ = ∑ i : EvenTraceIndex k c,
          if k ≤ a + (i : ℕ) ∧
              a + (i : ℕ) < c - (i : ℕ) + k then
            evenShiftedAuxiliaryWeight n k a c i else 0 :=
        Finset.sum_filter _ _
  rw [hupperSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lowerEvenStartType_weight n k a c hvalid hca i]
  by_cases houter : c - (i : ℕ) + k ≤ a + (i : ℕ)
  · have hnotPartner : ¬(k ≤ a + (i : ℕ) ∧
        a + (i : ℕ) < c - (i : ℕ) + k) := by omega
    simp [houter, hnotPartner]
  · by_cases hkStart : k ≤ a + (i : ℕ)
    · have hpartner : k ≤ a + (i : ℕ) ∧
          a + (i : ℕ) < c - (i : ℕ) + k := by omega
      simp [houter, hpartner]
    · have hnegative : ((a + (i : ℕ) : ℕ) : ℤ) - k < 0 := by
        apply sub_neg.mpr
        exact_mod_cast Nat.lt_of_not_ge hkStart
      have hshift : evenShiftedAuxiliaryWeight n k a c i = 0 := by
        unfold evenShiftedAuxiliaryWeight
        exact auxiliaryWeight_eq_zero_of_neg_right hnegative
      simp [houter, hkStart, hshift]

private theorem oddTraceWeights_pair
    (n k a c : ℕ) (hca : c ≤ a) :
    (∑ i : OddTraceIndex n k a c,
        startTypeWeight k (lowerOddStartType n k a c i)) +
      (∑ i : OddUpperTraceIndex n k a c,
        startTypeWeight k (upperOddStartType n k a c i)) =
      ∑ i : OddTraceIndex n k a c, oddRawAuxiliaryWeight n k a c i := by
  have hupperSum :
      (∑ i : OddUpperTraceIndex n k a c,
          startTypeWeight k (upperOddStartType n k a c i)) =
        ∑ i : OddTraceIndex n k a c,
          if k ≤ a + (i : ℕ) + 1 ∧
              a + (i : ℕ) + 1 < c - (i : ℕ) + k then
            oddShiftedAuxiliaryWeight n k a c i else 0 := by
    calc
      (∑ i : OddUpperTraceIndex n k a c,
          startTypeWeight k (upperOddStartType n k a c i)) =
          ∑ i : OddUpperTraceIndex n k a c,
            oddShiftedAuxiliaryWeight n k a c i.1 := by
        apply Fintype.sum_congr
        intro i
        exact upperOddStartType_weight n k a c i
      _ = ∑ i ∈ Finset.univ.filter (fun i : OddTraceIndex n k a c ↦
          k ≤ a + (i : ℕ) + 1 ∧
            a + (i : ℕ) + 1 < c - (i : ℕ) + k),
          oddShiftedAuxiliaryWeight n k a c i := by
        symm
        apply Finset.sum_subtype
        intro i
        simp
      _ = ∑ i : OddTraceIndex n k a c,
          if k ≤ a + (i : ℕ) + 1 ∧
              a + (i : ℕ) + 1 < c - (i : ℕ) + k then
            oddShiftedAuxiliaryWeight n k a c i else 0 :=
        Finset.sum_filter _ _
  rw [hupperSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lowerOddStartType_weight n k a c hca i]
  by_cases houter : c - (i : ℕ) + k ≤ a + (i : ℕ) + 1
  · have hnotPartner : ¬(k ≤ a + (i : ℕ) + 1 ∧
        a + (i : ℕ) + 1 < c - (i : ℕ) + k) := by omega
    simp [houter, hnotPartner]
  · by_cases hkStart : k ≤ a + (i : ℕ) + 1
    · have hpartner : k ≤ a + (i : ℕ) + 1 ∧
          a + (i : ℕ) + 1 < c - (i : ℕ) + k := by omega
      simp [houter, hpartner]
    · have hnegative : ((a + (i : ℕ) + 1 : ℕ) : ℤ) - k < 0 := by
        apply sub_neg.mpr
        exact_mod_cast Nat.lt_of_not_ge hkStart
      have hshift : oddShiftedAuxiliaryWeight n k a c i = 0 := by
        unfold oddShiftedAuxiliaryWeight
        exact auxiliaryWeight_eq_zero_of_neg_right hnegative
      simp [houter, hkStart, hshift]

private theorem sum_evenRawAuxiliaryWeight_eq
    (n k a c : ℕ) :
    (∑ i : EvenTraceIndex k c, evenRawAuxiliaryWeight n k a c i) =
      evenAuxiliaryIncidenceSum n k a c := by
  let f : Fin (k + 1) → ℤ := fun i ↦
    auxiliaryWeight n k ((a : ℤ) + (i : ℕ))
      ((c : ℤ) - (i : ℕ))
  calc
    (∑ i : EvenTraceIndex k c, evenRawAuxiliaryWeight n k a c i) =
        ∑ i : EvenTraceIndex k c, f i := by
      apply Fintype.sum_congr
      intro i
      unfold evenRawAuxiliaryWeight f
      norm_num only [Nat.cast_add, Nat.cast_sub i.2]
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin (k + 1) ↦
          (i : ℕ) ≤ c), f i := by
      symm
      apply Finset.sum_subtype
      intro i
      simp
    _ = ∑ i : Fin (k + 1), f i := by
      apply Finset.sum_filter_of_ne
      intro i _hi hne
      by_contra hic
      apply hne
      unfold f
      apply auxiliaryWeight_eq_zero_of_neg_right
      omega
    _ = evenAuxiliaryIncidenceSum n k a c := by
      unfold f evenAuxiliaryIncidenceSum
      rw [Finset.sum_range]

private theorem sum_oddRawAuxiliaryWeight_eq
    (n k a c : ℕ) :
    (∑ i : OddTraceIndex n k a c, oddRawAuxiliaryWeight n k a c i) =
      oddAuxiliaryIncidenceSum n k a c := by
  let f : Fin k → ℤ := fun i ↦
    auxiliaryWeight n k ((a : ℤ) + (i : ℕ) + 1)
      ((c : ℤ) - (i : ℕ))
  calc
    (∑ i : OddTraceIndex n k a c, oddRawAuxiliaryWeight n k a c i) =
        ∑ i : OddTraceIndex n k a c, f i := by
      apply Fintype.sum_congr
      intro i
      unfold oddRawAuxiliaryWeight f
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_sub i.2.1]
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin k ↦
          (i : ℕ) ≤ c ∧ a + c + 1 ≤ n), f i := by
      symm
      apply Finset.sum_subtype
      intro i
      simp
    _ = ∑ i : Fin k, f i := by
      apply Finset.sum_filter_of_ne
      intro i _hi hne
      by_contra hcondition
      by_cases hic : (i : ℕ) ≤ c
      · have hdimension : n < a + c + 1 := by omega
        apply hne
        unfold f
        apply auxiliaryWeight_eq_zero_of_lt_add
        omega
      · apply hne
        unfold f
        apply auxiliaryWeight_eq_zero_of_neg_right
        omega
    _ = oddAuxiliaryIncidenceSum n k a c := by
      unfold f oddAuxiliaryIncidenceSum
      rw [Finset.sum_range]

/-- For every valid lower target, the finite sum over occupied canonical
start types is exactly the paper's two-diagonal auxiliary incidence sum. -/
theorem canonicalStartWeightIncidenceSum_eq_auxiliaryIncidenceSum
    (n k a c : ℕ) (hk : 0 < k) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    canonicalStartWeightIncidenceSum n k a c =
      auxiliaryIncidenceSum n k a c := by
  rw [canonicalStartWeightIncidenceSum_eq_trace_sums
    n k a c hk hvalid hca]
  rw [show
    (∑ i : EvenTraceIndex k c,
        startTypeWeight k (lowerEvenStartType n k a c hvalid i)) +
      (∑ i : OddTraceIndex n k a c,
        startTypeWeight k (lowerOddStartType n k a c i)) +
      ((∑ i : EvenUpperTraceIndex k a c,
        startTypeWeight k (upperEvenStartType n k a c hvalid i)) +
      ∑ i : OddUpperTraceIndex n k a c,
        startTypeWeight k (upperOddStartType n k a c i)) =
      ((∑ i : EvenTraceIndex k c,
        startTypeWeight k (lowerEvenStartType n k a c hvalid i)) +
      ∑ i : EvenUpperTraceIndex k a c,
        startTypeWeight k (upperEvenStartType n k a c hvalid i)) +
      ((∑ i : OddTraceIndex n k a c,
        startTypeWeight k (lowerOddStartType n k a c i)) +
      ∑ i : OddUpperTraceIndex n k a c,
        startTypeWeight k (upperOddStartType n k a c i)) by ring,
    evenTraceWeights_pair n k a c hvalid hca,
    oddTraceWeights_pair n k a c hca,
    sum_evenRawAuxiliaryWeight_eq,
    sum_oddRawAuxiliaryWeight_eq]
  rfl

namespace BasicChain

/-- The concrete distributed weighting has exactly the required total on
every valid lower ternary type. -/
theorem totalInducedWeightOnType_startTypeTotal_eq_trinomial_of_lower
    (n k a c : ℕ) (hk : 0 < k) (hvalid : a + c ≤ n) (hca : c ≤ a) :
    totalInducedWeightOnType n a c
        (distributedChainWeight (startTypeTotal k) k) =
      (trinomial n a c : ℝ) := by
  rw [totalInducedWeightOnType_startTypeTotal_eq_arithmetic_sum hk a c]
  have hcanonical :=
    canonicalStartWeightIncidenceSum_eq_auxiliaryIncidenceSum
      n k a c hk hvalid hca
  have hauxiliary :=
    auxiliaryIncidenceSum_eq_extendedTrinomial n k a c hvalid
  have hinteger : canonicalStartWeightIncidenceSum n k a c =
      (trinomial n a c : ℤ) := by
    rw [hcanonical, hauxiliary, extendedTrinomial_ofNat]
  unfold startTypeTotal
  exact_mod_cast hinteger

end BasicChain

end Ternary
end WeightedChains
