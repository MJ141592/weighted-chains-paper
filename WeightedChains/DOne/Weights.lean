import WeightedChains.DOne.Chains
import WeightedChains.DOne.LayerTotals
import WeightedChains.DOne.Incidence
import WeightedChains.DOne.CanonicalChain
import WeightedChains.DOne.ChainReflection

/-!
# Distributing the Boolean layer totals among individual chains

Section 4 first specifies a total weight `W_n(a)` for chains starting at a
layer.  This file turns those totals into weights on the finite chain model.
Symmetric chains have two equally distant endpoints; to keep the chain family
a genuine partition, their lower endpoint is chosen as the canonical start.
-/

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace WeightedChains
namespace DOne
namespace BooleanChain

variable {n : ℕ}

/-- The decidable arithmetic form of goodness for a represented Boolean
chain. -/
def IsGood (C : BooleanChain n) (k : ℕ) : Prop :=
  C.steps ≤ k ∧ (2 * C.start.card + C.steps = n ∨ C.steps = k)

instance decidableIsGood (C : BooleanChain n) (k : ℕ) : Decidable (C.IsGood k) := by
  unfold IsGood
  infer_instance

theorem isGood_iff (C : BooleanChain n) (k : ℕ) :
    C.IsGood k ↔ C.toChain.Good k := by
  exact (C.good_toChain_iff k).symm

/-- The canonical paper-start layer of a represented chain.  The endpoint
farther from the middle is selected.  In the equality case, which includes
symmetric chains, the first (lower) endpoint is selected. -/
def canonicalStart (C : BooleanChain n) : ℕ :=
  if (2 * (C.start.card + C.steps)).dist n ≤ (2 * C.start.card).dist n then
    C.start.card
  else
    C.start.card + C.steps

theorem endpointRank_le (C : BooleanChain n) : C.start.card + C.steps ≤ n := by
  calc
    C.start.card + C.steps = (C.support (Fin.last C.steps)).card :=
      (C.card_support (Fin.last C.steps)).symm
    _ ≤ n := by simpa using Finset.card_le_univ (C.support (Fin.last C.steps))

theorem endpoint_distance_le_iff (C : BooleanChain n) :
    (2 * (C.start.card + C.steps)).dist n ≤ (2 * C.start.card).dist n ↔
      (C.steps : ℕ) = 0 ∨ 2 * C.start.card + C.steps ≤ n := by
  have hend := C.endpointRank_le
  have hpq : 2 * C.start.card ≤ 2 * (C.start.card + C.steps) := by omega
  by_cases hsteps : (C.steps : ℕ) = 0
  · simp [hsteps]
  · rw [or_iff_right hsteps]
    by_cases hlast : 2 * (C.start.card + C.steps) ≤ n
    · rw [Nat.dist_eq_sub_of_le hlast,
        Nat.dist_eq_sub_of_le (hpq.trans hlast)]
      omega
    · have hnlast : n ≤ 2 * (C.start.card + C.steps) := by omega
      by_cases hfirst : n ≤ 2 * C.start.card
      · rw [Nat.dist_eq_sub_of_le_right hnlast,
          Nat.dist_eq_sub_of_le_right hfirst]
        omega
      · have hfirst' : 2 * C.start.card ≤ n := by omega
        rw [Nat.dist_eq_sub_of_le_right hnlast,
          Nat.dist_eq_sub_of_le hfirst']
        omega

theorem canonicalStart_eq_ite (C : BooleanChain n) :
    C.canonicalStart =
      if (C.steps : ℕ) = 0 ∨ 2 * C.start.card + C.steps ≤ n then C.start.card
      else C.start.card + C.steps := by
  unfold canonicalStart
  exact if_congr C.endpoint_distance_le_iff rfl rfl

theorem canonicalStart_eq_first_of_startsAtFirst (C : BooleanChain n)
    (hfirst : C.toChain.StartsAtFirst) :
    C.canonicalStart = C.start.card := by
  rw [canonicalStart, if_pos]
  simpa [Chain.StartsAtFirst, Cube.middleDistance] using hfirst

theorem canonicalStart_eq_last_of_not_startsAtFirst (C : BooleanChain n)
    (hfirst : ¬C.toChain.StartsAtFirst) :
    C.canonicalStart = C.start.card + C.steps := by
  rw [canonicalStart, if_neg]
  simpa [Chain.StartsAtFirst, Cube.middleDistance] using hfirst

theorem canonicalStart_le (C : BooleanChain n) : C.canonicalStart ≤ n := by
  have hsupport := C.endpointRank_le
  unfold canonicalStart
  split_ifs <;> omega

theorem isGood_permute_iff (C : BooleanChain n) (e : Equiv.Perm (Fin n)) (k : ℕ) :
    (C.permute e).IsGood k ↔ C.IsGood k := by
  simp [IsGood]

@[simp]
theorem canonicalStart_permute (C : BooleanChain n) (e : Equiv.Perm (Fin n)) :
    (C.permute e).canonicalStart = C.canonicalStart := by
  simp [canonicalStart]

/-- The finite group of good chains assigned the canonical start label `a`.
These groups, unlike the endpoint relation `StartsAtLayer`, do not count a
symmetric chain twice. -/
def startGroup (n k a : ℕ) : Finset (BooleanChain n) :=
  Finset.univ.filter fun C ↦ C.IsGood k ∧ C.canonicalStart = a

theorem mem_startGroup_iff (C : BooleanChain n) (k a : ℕ) :
    C ∈ startGroup n k a ↔ C.IsGood k ∧ C.canonicalStart = a := by
  simp [startGroup]

theorem mem_startGroup_canonicalStart_iff (C : BooleanChain n) (k : ℕ) :
    C ∈ startGroup n k C.canonicalStart ↔ C.IsGood k := by
  simp [mem_startGroup_iff]

theorem startGroup_nonempty_of_isGood (C : BooleanChain n) (k : ℕ)
    (hgood : C.IsGood k) :
    (startGroup n k C.canonicalStart).Nonempty :=
  ⟨C, (mem_startGroup_canonicalStart_iff C k).mpr hgood⟩

theorem startGroup_disjoint {k a b : ℕ} (hab : a ≠ b) :
    Disjoint (startGroup n k a) (startGroup n k b) := by
  rw [Finset.disjoint_left]
  intro C hCa hCb
  have ha := (mem_startGroup_iff C k a).mp hCa |>.2
  have hb := (mem_startGroup_iff C k b).mp hCb |>.2
  exact hab (ha.symm.trans hb)

/-- All chains in an occupied lower-side start group have the same rank
interval. -/
theorem endpoints_of_mem_startGroup_lower {k a : ℕ} (hk : 0 < k)
    (ha : 2 * a ≤ n) {C : BooleanChain n} (hC : C ∈ startGroup n k a) :
    C.start.card = a ∧
      C.start.card + C.steps = min (a + k) (n - a) := by
  have hdata := (mem_startGroup_iff C k a).mp hC
  rcases hdata.1 with ⟨hstepsLe, hsym | hfull⟩
  · have hcondition : (C.steps : ℕ) = 0 ∨
        2 * C.start.card + C.steps ≤ n := Or.inr (by omega)
    have hlabel := hdata.2
    rw [C.canonicalStart_eq_ite, if_pos hcondition] at hlabel
    refine ⟨hlabel, ?_⟩
    rw [min_eq_right (by omega : n - a ≤ a + k)]
    omega
  · have hstepsPos : 0 < (C.steps : ℕ) := by omega
    by_cases hcondition : 2 * C.start.card + C.steps ≤ n
    · have hlabel := hdata.2
      rw [C.canonicalStart_eq_ite, if_pos (Or.inr hcondition)] at hlabel
      refine ⟨hlabel, ?_⟩
      rw [min_eq_left (by omega : a + k ≤ n - a)]
      omega
    · have hlabel := hdata.2
      have hcondition' : ¬((C.steps : ℕ) = 0 ∨
          2 * C.start.card + C.steps ≤ n) := by omega
      rw [C.canonicalStart_eq_ite, if_neg hcondition'] at hlabel
      omega

/-- An occupied upper-side canonical group is necessarily an outer full-width
group, and its interval is `[a-k,a]`. -/
theorem endpoints_of_mem_startGroup_upper {k a : ℕ} (hk : 0 < k)
    (ha : n < 2 * a) {C : BooleanChain n} (hC : C ∈ startGroup n k a) :
    n + k < 2 * a ∧ C.start.card = a - k ∧ C.start.card + C.steps = a := by
  have hdata := (mem_startGroup_iff C k a).mp hC
  rcases hdata.1 with ⟨hstepsLe, hsym | hfull⟩
  · have hcondition : (C.steps : ℕ) = 0 ∨
        2 * C.start.card + C.steps ≤ n := Or.inr (by omega)
    have hlabel := hdata.2
    rw [C.canonicalStart_eq_ite, if_pos hcondition] at hlabel
    omega
  · have hstepsPos : 0 < (C.steps : ℕ) := by omega
    by_cases hcondition : 2 * C.start.card + C.steps ≤ n
    · have hlabel := hdata.2
      rw [C.canonicalStart_eq_ite, if_pos (Or.inr hcondition)] at hlabel
      omega
    · have hlabel := hdata.2
      have hcondition' : ¬((C.steps : ℕ) = 0 ∨
          2 * C.start.card + C.steps ≤ n) := by omega
      rw [C.canonicalStart_eq_ite, if_neg hcondition'] at hlabel
      exact ⟨by omega, by omega, by omega⟩

/-- Every lower-side layer labels an occupied canonical start group. -/
theorem startGroup_nonempty_lower (k a : ℕ) (ha : 2 * a ≤ n) :
    (startGroup n k a).Nonempty := by
  by_cases houter : 2 * a + k ≤ n
  · have hbound : a + k ≤ n := by omega
    let C := intervalChain n a k hbound
    refine ⟨C, (mem_startGroup_iff C k a).mpr ⟨?_, ?_⟩⟩
    · exact ⟨by simp [C], Or.inr (by simp [C])⟩
    · rw [C.canonicalStart_eq_ite]
      simp [C, houter]
  · have hbound : a + (n - 2 * a) ≤ n := by omega
    have hwidth : n - 2 * a ≤ k := by omega
    let C := intervalChain n a (n - 2 * a) hbound
    refine ⟨C, (mem_startGroup_iff C k a).mpr ⟨?_, ?_⟩⟩
    · refine ⟨by simpa [C] using hwidth, Or.inl ?_⟩
      simp [C]
      omega
    · rw [C.canonicalStart_eq_ite]
      have hcondition : (C.steps : ℕ) = 0 ∨
          2 * C.start.card + C.steps ≤ n := by
        right
        simp only [C, intervalChain_steps, intervalChain_start_card]
        omega
      rw [if_pos hcondition]
      simp [C]

/-- Every genuinely upper outer label has an occupied canonical start group. -/
theorem startGroup_nonempty_upper {k a : ℕ} (hk : 0 < k) (ha : a ≤ n)
    (houter : n + k < 2 * a) :
    (startGroup n k a).Nonempty := by
  have hka : k ≤ a := by omega
  have hbound : (a - k) + k ≤ n := by omega
  let C := intervalChain n (a - k) k hbound
  refine ⟨C, (mem_startGroup_iff C k a).mpr ⟨?_, ?_⟩⟩
  · exact ⟨by simp [C], Or.inr (by simp [C])⟩
  · rw [C.canonicalStart_eq_ite]
    have hcondition : ¬((C.steps : ℕ) = 0 ∨
        2 * C.start.card + C.steps ≤ n) := by
      simp only [C, intervalChain_steps, intervalChain_start_card]
      omega
    rw [if_neg hcondition]
    simp [C]
    omega

theorem startGroup_eq_empty_upper_inner {k a : ℕ} (hk : 0 < k)
    (hupper : n < 2 * a) (hinner : 2 * a ≤ n + k) :
    startGroup n k a = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  have hvalid := (endpoints_of_mem_startGroup_upper hk hupper hC).1
  omega

/-- The common real weight of chains in canonical start group `a`. -/
def startGroupChainWeight (n k a : ℕ) : ℝ :=
  (startingWeight n k a : ℝ) / (startGroup n k a).card

/-- The weight of an individual represented chain.  Non-good descriptors are
retained in the finite index type with weight zero. -/
def chainWeight (n k : ℕ) (C : BooleanChain n) : ℝ :=
  if C.IsGood k then startGroupChainWeight n k C.canonicalStart else 0

theorem chainWeight_of_mem_startGroup {k a : ℕ} {C : BooleanChain n}
    (hC : C ∈ startGroup n k a) :
    chainWeight n k C = startGroupChainWeight n k a := by
  have hdata := (mem_startGroup_iff C k a).mp hC
  rw [chainWeight, if_pos hdata.1, hdata.2]

/-- Dividing by the group cardinality distributes exactly the prescribed
total `W_n(a)` whenever the canonical group is occupied. -/
theorem sum_chainWeight_startGroup {k a : ℕ}
    (ha : (startGroup n k a).Nonempty) :
    ∑ C ∈ startGroup n k a, chainWeight n k C = (startingWeight n k a : ℝ) := by
  calc
    ∑ C ∈ startGroup n k a, chainWeight n k C =
        ∑ _C ∈ startGroup n k a, startGroupChainWeight n k a := by
      apply Finset.sum_congr rfl
      intro C hC
      exact chainWeight_of_mem_startGroup hC
    _ = ((startGroup n k a).card : ℝ) * startGroupChainWeight n k a := by
      simp
    _ = (startingWeight n k a : ℝ) := by
      unfold startGroupChainWeight
      have hcard : ((startGroup n k a).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr ha)
      field_simp

theorem chainWeight_pos_of_isGood (C : BooleanChain n) (k : ℕ)
    (hk : 1 < k) (hkn : k ≤ n) (hgood : C.IsGood k) :
    0 < chainWeight n k C := by
  rw [chainWeight, if_pos hgood, startGroupChainWeight]
  apply div_pos
  · exact_mod_cast startingWeight_pos k n C.canonicalStart hk hkn C.canonicalStart_le
  · exact_mod_cast (Finset.card_pos.mpr (C.startGroup_nonempty_of_isGood k hgood))

theorem chainWeight_nonneg (C : BooleanChain n) (k : ℕ)
    (hk : 1 < k) (hkn : k ≤ n) :
    0 ≤ chainWeight n k C := by
  by_cases hgood : C.IsGood k
  · exact (C.chainWeight_pos_of_isGood k hk hkn hgood).le
  · simp [chainWeight, hgood]

@[simp]
theorem chainWeight_permute (C : BooleanChain n) (e : Equiv.Perm (Fin n)) (k : ℕ) :
    chainWeight n k (C.permute e) = chainWeight n k C := by
  unfold chainWeight
  rw [canonicalStart_permute]
  exact if_congr (C.isGood_permute_iff e k) rfl rfl

/-- Coordinate symmetry makes the induced chain weight constant on each
Boolean layer.  This statement already uses the actual per-chain weights,
not merely unweighted chain counts. -/
theorem inducedWeight_eq_of_rank_eq (n k : ℕ) {x y : Cube n 1}
    (hxy : Cube.rank x = Cube.rank y) :
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) x =
      WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) y := by
  obtain ⟨e, he⟩ := exists_cubePermEquiv_eq_of_rank_eq hxy
  let E := permuteEquiv e
  let summand := fun z : Cube n 1 ↦ fun C : BooleanChain n ↦
    if z ∈ C.toChain.vertices then chainWeight n k C else 0
  calc
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) x = ∑ C, summand x C := rfl
    _ = ∑ C, summand y (E C) := by
      apply Fintype.sum_congr
      intro C
      change (if x ∈ C.toChain.vertices then chainWeight n k C else 0) =
        if y ∈ (C.permute e).toChain.vertices then chainWeight n k (C.permute e) else 0
      have hmem := C.mem_vertices_permute_iff e x
      rw [he] at hmem
      rw [C.chainWeight_permute e k]
      exact if_congr hmem.symm rfl rfl
    _ = ∑ C, summand y C := Equiv.sum_comp E (summand y)
    _ = WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) y := rfl

/-- A represented chain passes through layer `a` exactly when `a` lies in its
rank interval. -/
def PassesThroughLayer (C : BooleanChain n) (a : ℕ) : Prop :=
  C.start.card ≤ a ∧ a ≤ C.start.card + C.steps

instance decidablePassesThroughLayer (C : BooleanChain n) (a : ℕ) :
    Decidable (C.PassesThroughLayer a) := by
  unfold PassesThroughLayer
  infer_instance

/-- The actual total weight of represented chains incident with layer `a`. -/
def actualLayerWeightTotal (n k a : ℕ) : ℝ :=
  ∑ C : BooleanChain n, if C.PassesThroughLayer a then chainWeight n k C else 0

/-- Total weight of good chains whose lower endpoint has rank `a`. -/
def lowerEndpointWeightTotal (n k a : ℕ) : ℝ :=
  ∑ C : BooleanChain n,
    if C.IsGood k ∧ C.start.card = a then chainWeight n k C else 0

/-- Total weight of good chains whose upper endpoint has rank `a`. -/
def upperEndpointWeightTotal (n k a : ℕ) : ℝ :=
  ∑ C : BooleanChain n,
    if C.IsGood k ∧ C.start.card + C.steps = a then chainWeight n k C else 0

theorem layerIndicator_succ (C : BooleanChain n) (a : ℕ) (w : ℝ) :
    (if C.PassesThroughLayer (a + 1) then w else 0) =
      (if C.PassesThroughLayer a then w else 0) +
        (if C.start.card = a + 1 then w else 0) -
        (if C.start.card + C.steps = a then w else 0) := by
  have horder : C.start.card ≤ C.start.card + C.steps := by omega
  by_cases hlower : C.start.card = a + 1
  · have hnext : C.PassesThroughLayer (a + 1) := by
      unfold PassesThroughLayer
      omega
    have hprevious : ¬C.PassesThroughLayer a := by
      unfold PassesThroughLayer
      omega
    have hupper : a + 1 + (C.steps : ℕ) ≠ a := by omega
    simp [hnext, hprevious, hlower, hupper]
  · by_cases hupper : C.start.card + C.steps = a
    · have hnext : ¬C.PassesThroughLayer (a + 1) := by
        unfold PassesThroughLayer
        omega
      have hprevious : C.PassesThroughLayer a := by
        unfold PassesThroughLayer
        omega
      simp [hnext, hprevious, hlower, hupper]
    · have hiff : C.PassesThroughLayer (a + 1) ↔ C.PassesThroughLayer a := by
        unfold PassesThroughLayer
        omega
      rw [if_neg hlower, if_neg hupper, sub_zero, add_zero]
      exact if_congr hiff rfl rfl

/-- Moving up one rank adds chains at their lower endpoint and removes chains
just after their upper endpoint. -/
theorem actualLayerWeightTotal_succ (n k a : ℕ) :
    actualLayerWeightTotal n k (a + 1) =
      actualLayerWeightTotal n k a + lowerEndpointWeightTotal n k (a + 1) -
        upperEndpointWeightTotal n k a := by
  unfold actualLayerWeightTotal lowerEndpointWeightTotal upperEndpointWeightTotal
  calc
    ∑ C : BooleanChain n,
        (if C.PassesThroughLayer (a + 1) then chainWeight n k C else 0) =
        ∑ C : BooleanChain n,
          ((if C.PassesThroughLayer a then chainWeight n k C else 0) +
            (if C.IsGood k ∧ C.start.card = a + 1 then chainWeight n k C else 0) -
            (if C.IsGood k ∧ C.start.card + C.steps = a then chainWeight n k C else 0)) := by
      apply Fintype.sum_congr
      intro C
      by_cases hgood : C.IsGood k
      · simp only [hgood, true_and]
        exact C.layerIndicator_succ a (chainWeight n k C)
      · have hweight : chainWeight n k C = 0 := by simp [chainWeight, hgood]
        simp [hgood, hweight]
    _ =
        (∑ C : BooleanChain n,
            (if C.PassesThroughLayer a then chainWeight n k C else 0)) +
          (∑ C : BooleanChain n,
            (if C.IsGood k ∧ C.start.card = a + 1 then chainWeight n k C else 0)) -
          (∑ C : BooleanChain n,
            (if C.IsGood k ∧ C.start.card + C.steps = a then chainWeight n k C else 0)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem isGood_start_eq_iff_mem_startGroup_outer
    (C : BooleanChain n) {k a : ℕ} (hk : 0 < k) (houter : 2 * a ≤ n - k) :
    C.IsGood k ∧ C.start.card = a ↔ C ∈ startGroup n k a := by
  have hlower : 2 * a ≤ n := houter.trans (Nat.sub_le n k)
  constructor
  · rintro ⟨hgood, hstart⟩
    apply (mem_startGroup_iff C k a).mpr
    refine ⟨hgood, ?_⟩
    rw [C.canonicalStart_eq_ite]
    have hcondition : (C.steps : ℕ) = 0 ∨
        2 * C.start.card + C.steps ≤ n := by
      rcases hgood.2 with hsym | hfull
      · right
        omega
      · right
        omega
    rw [if_pos hcondition, hstart]
  · intro hC
    exact ⟨(mem_startGroup_iff C k a).mp hC |>.1,
      (endpoints_of_mem_startGroup_lower hk hlower hC).1⟩

theorem isGood_start_eq_iff_mem_startGroup_union_inner
    (C : BooleanChain n) {k a : ℕ} (hk : 0 < k)
    (hinner : n - k < 2 * a) (hlower : 2 * a ≤ n) :
    C.IsGood k ∧ C.start.card = a ↔
      C ∈ startGroup n k a ∨ C ∈ startGroup n k (a + k) := by
  constructor
  · rintro ⟨hgood, hstart⟩
    rcases hgood.2 with hsym | hfull
    · left
      apply (mem_startGroup_iff C k a).mpr
      refine ⟨⟨hgood.1, Or.inl hsym⟩, ?_⟩
      rw [C.canonicalStart_eq_ite]
      have hcondition : (C.steps : ℕ) = 0 ∨
          2 * C.start.card + C.steps ≤ n := Or.inr (by omega)
      rw [if_pos hcondition, hstart]
    · right
      apply (mem_startGroup_iff C k (a + k)).mpr
      refine ⟨⟨hgood.1, Or.inr hfull⟩, ?_⟩
      rw [C.canonicalStart_eq_ite]
      have hcondition : ¬((C.steps : ℕ) = 0 ∨
          2 * C.start.card + C.steps ≤ n) := by omega
      rw [if_neg hcondition, hstart, hfull]
  · rintro (hC | hC)
    · exact ⟨(mem_startGroup_iff C k a).mp hC |>.1,
        (endpoints_of_mem_startGroup_lower hk hlower hC).1⟩
    · have hupper : n < 2 * (a + k) := by omega
      have hdata := endpoints_of_mem_startGroup_upper hk hupper hC
      exact ⟨(mem_startGroup_iff C k (a + k)).mp hC |>.1, by omega⟩

theorem lowerEndpointWeightTotal_outer {k a : ℕ} (hk : 0 < k)
    (houter : 2 * a ≤ n - k) :
    lowerEndpointWeightTotal n k a = (startingWeight n k a : ℝ) := by
  unfold lowerEndpointWeightTotal
  calc
    ∑ C : BooleanChain n,
        (if C.IsGood k ∧ C.start.card = a then chainWeight n k C else 0) =
        ∑ C : BooleanChain n,
          if C ∈ startGroup n k a then chainWeight n k C else 0 := by
      apply Fintype.sum_congr
      intro C
      exact if_congr (isGood_start_eq_iff_mem_startGroup_outer C hk houter) rfl rfl
    _ = ∑ C ∈ startGroup n k a, chainWeight n k C :=
      Fintype.sum_extend_by_zero (startGroup n k a) (chainWeight n k)
    _ = (startingWeight n k a : ℝ) :=
      sum_chainWeight_startGroup
        (startGroup_nonempty_lower k a (houter.trans (Nat.sub_le n k)))

theorem lowerEndpointWeightTotal_inner {k a : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (hinner : n - k < 2 * a) (hlower : 2 * a ≤ n) :
    lowerEndpointWeightTotal n k a =
      (startingWeight n k a : ℝ) +
        (extendedStartingWeight n k ((a : ℤ) + (k : ℤ)) : ℝ) := by
  let G₁ := startGroup n k a
  let G₂ := startGroup n k (a + k)
  have hdisjoint : Disjoint G₁ G₂ := by
    exact startGroup_disjoint (by omega)
  unfold lowerEndpointWeightTotal
  calc
    ∑ C : BooleanChain n,
        (if C.IsGood k ∧ C.start.card = a then chainWeight n k C else 0) =
        ∑ C : BooleanChain n,
          if C ∈ G₁ ∪ G₂ then chainWeight n k C else 0 := by
      apply Fintype.sum_congr
      intro C
      apply if_congr
      · simpa only [Finset.mem_union] using
          isGood_start_eq_iff_mem_startGroup_union_inner C hk hinner hlower
      · rfl
      · rfl
    _ = ∑ C ∈ G₁ ∪ G₂, chainWeight n k C :=
      Fintype.sum_extend_by_zero (G₁ ∪ G₂) (chainWeight n k)
    _ = (∑ C ∈ G₁, chainWeight n k C) +
        ∑ C ∈ G₂, chainWeight n k C := by
      rw [Finset.sum_union hdisjoint]
    _ = (startingWeight n k a : ℝ) +
        (extendedStartingWeight n k ((a : ℤ) + (k : ℤ)) : ℝ) := by
      rw [sum_chainWeight_startGroup (startGroup_nonempty_lower k a hlower)]
      by_cases hsum : a + k ≤ n
      · have hvalid : n + k < 2 * (a + k) := by omega
        rw [sum_chainWeight_startGroup (startGroup_nonempty_upper hk hsum hvalid)]
        have hcast : (a : ℤ) + (k : ℤ) = ((a + k : ℕ) : ℤ) := by norm_num
        rw [hcast]
        rw [extendedStartingWeight_ofNat hsum]
      · have hgtNat : n < a + k := Nat.lt_of_not_ge hsum
        have hgt : (n : ℤ) < (a : ℤ) + (k : ℤ) := by exact_mod_cast hgtNat
        have hempty : G₂ = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro C hC
          have hlabel := (mem_startGroup_iff C k (a + k)).mp hC |>.2
          have hle : a + k ≤ n := by
            rw [← hlabel]
            exact C.canonicalStart_le
          omega
        rw [hempty, extendedStartingWeight_of_gt hgt]
        simp

theorem isGood_endpoint_eq_iff_mem_startGroup
    (C : BooleanChain n) {k a : ℕ} (hk : 0 < k) (hbelow : 2 * (a + 1) ≤ n) :
    C.IsGood k ∧ C.start.card + C.steps = a ↔
      k ≤ a ∧ C ∈ startGroup n k (a - k) := by
  constructor
  · rintro ⟨hgood, hendpoint⟩
    rcases hgood.2 with hsym | hfull
    · have horder := C.endpointRank_le
      omega
    · have hka : k ≤ a := by omega
      refine ⟨hka, (mem_startGroup_iff C k (a - k)).mpr ⟨⟨hgood.1, Or.inr hfull⟩, ?_⟩⟩
      rw [C.canonicalStart_eq_ite]
      have hcondition : (C.steps : ℕ) = 0 ∨
          2 * C.start.card + C.steps ≤ n := Or.inr (by omega)
      rw [if_pos hcondition]
      omega
  · rintro ⟨hka, hC⟩
    have hlower : 2 * (a - k) ≤ n := by omega
    have hdata := endpoints_of_mem_startGroup_lower hk hlower hC
    refine ⟨(mem_startGroup_iff C k (a - k)).mp hC |>.1, ?_⟩
    rw [hdata.2]
    rw [min_eq_left]
    · omega
    · omega

theorem upperEndpointWeightTotal_eq_ite {k a : ℕ} (hk : 0 < k)
    (hbelow : 2 * (a + 1) ≤ n) :
    upperEndpointWeightTotal n k a =
      if k ≤ a then (startingWeight n k (a - k) : ℝ) else 0 := by
  unfold upperEndpointWeightTotal
  by_cases hka : k ≤ a
  · rw [if_pos hka]
    calc
      ∑ C : BooleanChain n,
          (if C.IsGood k ∧ C.start.card + C.steps = a then chainWeight n k C else 0) =
          ∑ C : BooleanChain n,
            if C ∈ startGroup n k (a - k) then chainWeight n k C else 0 := by
        apply Fintype.sum_congr
        intro C
        apply if_congr
        · constructor
          · intro h
            exact (isGood_endpoint_eq_iff_mem_startGroup C hk hbelow).mp h |>.2
          · intro h
            exact (isGood_endpoint_eq_iff_mem_startGroup C hk hbelow).mpr ⟨hka, h⟩
        · rfl
        · rfl
      _ = ∑ C ∈ startGroup n k (a - k), chainWeight n k C :=
        Fintype.sum_extend_by_zero (startGroup n k (a - k)) (chainWeight n k)
      _ = (startingWeight n k (a - k) : ℝ) := by
        apply sum_chainWeight_startGroup
        apply startGroup_nonempty_lower k (a - k)
        omega
  · rw [if_neg hka]
    apply Fintype.sum_eq_zero
    intro C
    by_cases hendpoint : C.IsGood k ∧ C.start.card + C.steps = a
    · exact (hka ((isGood_endpoint_eq_iff_mem_startGroup C hk hbelow).mp hendpoint).1).elim
    · simp [hendpoint]

theorem upperEndpointWeightTotal_eq_extended {k a : ℕ} (hk : 0 < k)
    (hbelow : 2 * (a + 1) ≤ n) :
    upperEndpointWeightTotal n k a =
      (extendedStartingWeight n k ((a : ℤ) - (k : ℤ)) : ℝ) := by
  rw [upperEndpointWeightTotal_eq_ite hk hbelow]
  by_cases hka : k ≤ a
  · rw [if_pos hka]
    have hindex : (a : ℤ) - (k : ℤ) = ((a - k : ℕ) : ℤ) := by
      rw [Nat.cast_sub hka]
    rw [hindex, extendedStartingWeight_ofNat (by omega : a - k ≤ n)]
  · rw [if_neg hka]
    have hlt : a < k := Nat.lt_of_not_ge hka
    have hltInt : (a : ℤ) < (k : ℤ) := by exact_mod_cast hlt
    have hnegative : (a : ℤ) - (k : ℤ) < 0 := by omega
    rw [extendedStartingWeight_of_neg hnegative]
    norm_num

theorem lowerEndpointWeightTotal_eq {k a : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (hlower : 2 * a ≤ n) :
    lowerEndpointWeightTotal n k a =
      (startingWeight n k a : ℝ) +
        if n - k < 2 * a then
          (extendedStartingWeight n k ((a : ℤ) + (k : ℤ)) : ℝ)
        else 0 := by
  by_cases hinner : n - k < 2 * a
  · rw [if_pos hinner]
    exact lowerEndpointWeightTotal_inner hk hkn hinner hlower
  · rw [if_neg hinner, add_zero]
    apply lowerEndpointWeightTotal_outer hk
    omega

theorem actualLayerWeightTotal_zero (n k : ℕ) (hk : 0 < k) :
    actualLayerWeightTotal n k 0 = (startingWeight n k 0 : ℝ) := by
  calc
    actualLayerWeightTotal n k 0 = lowerEndpointWeightTotal n k 0 := by
      unfold actualLayerWeightTotal lowerEndpointWeightTotal
      apply Fintype.sum_congr
      intro C
      by_cases hgood : C.IsGood k
      · have hpasses : C.PassesThroughLayer 0 ↔ C.start.card = 0 := by
          unfold PassesThroughLayer
          omega
        rw [if_congr hpasses rfl rfl]
        simp [hgood]
      · have hweight : chainWeight n k C = 0 := by simp [chainWeight, hgood]
        simp [hweight, hgood]
    _ = (startingWeight n k 0 : ℝ) := by
      apply lowerEndpointWeightTotal_outer hk
      omega

/-- The actual sum of the individual chain weights through every lower layer
is exactly the recursive bookkeeping total from Section 4. -/
theorem actualLayerWeightTotal_eq_layerWeightTotal
    (k n a : ℕ) (hk : 0 < k) (hkn : k ≤ n) (hlower : 2 * a ≤ n) :
    actualLayerWeightTotal n k a = (layerWeightTotal n k a : ℝ) := by
  induction a with
  | zero =>
      rw [actualLayerWeightTotal_zero n k hk]
      unfold layerWeightTotal
      norm_num
  | succ a ih =>
      have hprev : 2 * a ≤ n := by omega
      have hindex : (((a + 1 : ℕ) : ℤ) - (k : ℤ) - 1) =
          (a : ℤ) - (k : ℤ) := by
        push_cast
        ring
      rw [actualLayerWeightTotal_succ, ih hprev,
        lowerEndpointWeightTotal_eq hk hkn hlower,
        upperEndpointWeightTotal_eq_extended hk hlower]
      conv_rhs => rw [layerWeightTotal]
      rw [hindex]
      push_cast
      ring

/-- The contribution to a rank layer from one canonical start group. -/
def startGroupIncidentWeight (n k a r : ℕ) : ℝ :=
  ∑ C ∈ startGroup n k a,
    if C.PassesThroughLayer r then chainWeight n k C else 0

theorem passesThroughLayer_iff_of_mem_startGroup_lower
    {k a r : ℕ} (hk : 0 < k) (ha : 2 * a ≤ n)
    {C : BooleanChain n} (hC : C ∈ startGroup n k a) :
    C.PassesThroughLayer r ↔ a ≤ r ∧ r ≤ min (a + k) (n - a) := by
  obtain ⟨hfirst, hlast⟩ := endpoints_of_mem_startGroup_lower hk ha hC
  unfold PassesThroughLayer
  rw [hlast, hfirst]

theorem passesThroughLayer_iff_of_mem_startGroup_upper
    {k a r : ℕ} (hk : 0 < k) (ha : n < 2 * a)
    {C : BooleanChain n} (hC : C ∈ startGroup n k a) :
    C.PassesThroughLayer r ↔ a - k ≤ r ∧ r ≤ a := by
  obtain ⟨_valid, hfirst, hlast⟩ := endpoints_of_mem_startGroup_upper hk ha hC
  unfold PassesThroughLayer
  rw [hlast, hfirst]

theorem startGroupIncidentWeight_lower {k a r : ℕ} (hk : 0 < k)
    (ha : 2 * a ≤ n) :
    startGroupIncidentWeight n k a r =
      if a ≤ r ∧ r ≤ min (a + k) (n - a) then
        (startingWeight n k a : ℝ)
      else 0 := by
  by_cases hpasses : a ≤ r ∧ r ≤ min (a + k) (n - a)
  · rw [if_pos hpasses]
    unfold startGroupIncidentWeight
    calc
      ∑ C ∈ startGroup n k a,
          (if C.PassesThroughLayer r then chainWeight n k C else 0) =
          ∑ C ∈ startGroup n k a, chainWeight n k C := by
        apply Finset.sum_congr rfl
        intro C hC
        rw [if_pos ((passesThroughLayer_iff_of_mem_startGroup_lower hk ha hC).mpr hpasses)]
      _ = (startingWeight n k a : ℝ) :=
        sum_chainWeight_startGroup (startGroup_nonempty_lower k a ha)
  · rw [if_neg hpasses]
    unfold startGroupIncidentWeight
    apply Finset.sum_eq_zero
    intro C hC
    rw [if_neg]
    exact fun h ↦ hpasses ((passesThroughLayer_iff_of_mem_startGroup_lower hk ha hC).mp h)

theorem startGroupIncidentWeight_upper {k a r : ℕ} (hk : 0 < k)
    (ha : a ≤ n) (hupper : n < 2 * a) (houter : n + k < 2 * a) :
    startGroupIncidentWeight n k a r =
      if a - k ≤ r ∧ r ≤ a then (startingWeight n k a : ℝ) else 0 := by
  by_cases hpasses : a - k ≤ r ∧ r ≤ a
  · rw [if_pos hpasses]
    unfold startGroupIncidentWeight
    calc
      ∑ C ∈ startGroup n k a,
          (if C.PassesThroughLayer r then chainWeight n k C else 0) =
          ∑ C ∈ startGroup n k a, chainWeight n k C := by
        apply Finset.sum_congr rfl
        intro C hC
        rw [if_pos ((passesThroughLayer_iff_of_mem_startGroup_upper hk hupper hC).mpr hpasses)]
      _ = (startingWeight n k a : ℝ) :=
        sum_chainWeight_startGroup (startGroup_nonempty_upper hk ha houter)
  · rw [if_neg hpasses]
    unfold startGroupIncidentWeight
    apply Finset.sum_eq_zero
    intro C hC
    rw [if_neg]
    exact fun h ↦ hpasses ((passesThroughLayer_iff_of_mem_startGroup_upper hk hupper hC).mp h)

theorem startGroupIncidentWeight_upper_inner {k a r : ℕ} (hk : 0 < k)
    (hupper : n < 2 * a) (hinner : 2 * a ≤ n + k) :
    startGroupIncidentWeight n k a r = 0 := by
  rw [startGroupIncidentWeight, startGroup_eq_empty_upper_inner hk hupper hinner]
  simp

/-- The actual incidence total is the sum of the contributions from the
canonical start groups. -/
theorem actualLayerWeightTotal_eq_sum_startGroupIncidentWeight (n k r : ℕ) :
    actualLayerWeightTotal n k r =
      ∑ a ∈ Finset.range (n + 1), startGroupIncidentWeight n k a r := by
  let term := fun C : BooleanChain n ↦
    if C.PassesThroughLayer r then chainWeight n k C else 0
  calc
    actualLayerWeightTotal n k r = ∑ C : BooleanChain n, term C := rfl
    _ = ∑ C : BooleanChain n, ∑ a ∈ Finset.range (n + 1),
          if C ∈ startGroup n k a then term C else 0 := by
      apply Fintype.sum_congr
      intro C
      by_cases hgood : C.IsGood k
      · rw [Finset.sum_eq_single C.canonicalStart]
        · simp [mem_startGroup_iff, hgood]
        · intro b hb hne
          have hnotmem : C ∉ startGroup n k b := by
            rw [mem_startGroup_iff]
            exact fun h ↦ hne (h.2.symm.trans rfl)
          simp [hnotmem]
        · intro hnotmem
          exact (hnotmem (Finset.mem_range.mpr
            (Nat.lt_succ_of_le C.canonicalStart_le))).elim
      · have hzero : chainWeight n k C = 0 := by simp [chainWeight, hgood]
        simp [mem_startGroup_iff, hgood, term, hzero]
    _ = ∑ a ∈ Finset.range (n + 1), ∑ C : BooleanChain n,
          if C ∈ startGroup n k a then term C else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.range (n + 1), startGroupIncidentWeight n k a r := by
      apply Finset.sum_congr rfl
      intro a _ha
      unfold startGroupIncidentWeight
      exact Fintype.sum_extend_by_zero (startGroup n k a) term

/-- Double-counting incidences identifies the sum of induced vertex weights
on a layer with the actual total chain weight through that layer. -/
theorem sum_inducedWeight_booleanLayer (n k a : ℕ) :
    ∑ x ∈ booleanLayerFinset n a,
        WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
          (chainWeight n k) x =
      actualLayerWeightTotal n k a := by
  rw [WeightedCover.sum_inducedWeight]
  unfold actualLayerWeightTotal
  apply Fintype.sum_congr
  intro C
  rw [C.card_booleanLayerFinset_inter_vertices a]
  by_cases hpasses : C.PassesThroughLayer a <;>
    simp [PassesThroughLayer] at hpasses ⊢

theorem sum_inducedWeight_booleanLayer_eq_card_mul
    (n k a : ℕ) {x : Cube n 1} (hx : Cube.rank x = a) :
    ∑ y ∈ booleanLayerFinset n a,
        WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
          (chainWeight n k) y =
      (booleanLayerFinset n a).card *
        WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
          (chainWeight n k) x := by
  calc
    ∑ y ∈ booleanLayerFinset n a,
        WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
          (chainWeight n k) y =
        ∑ _y ∈ booleanLayerFinset n a,
          WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
            (chainWeight n k) x := by
      apply Finset.sum_congr rfl
      intro y hy
      apply inducedWeight_eq_of_rank_eq n k
      exact (mem_booleanLayerFinset_iff.mp hy).trans hx.symm
    _ = (booleanLayerFinset n a).card *
        WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
          (chainWeight n k) x := by simp

/-- Once the actual incidence total through a layer is its binomial size,
uniformity forces the induced weight of every vertex in that layer to be one. -/
theorem inducedWeight_eq_one_of_actualLayerWeightTotal_eq_choose
    (n k a : ℕ) (ha : a ≤ n) {x : Cube n 1} (hx : Cube.rank x = a)
    (htotal : actualLayerWeightTotal n k a = (n.choose a : ℝ)) :
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
      (chainWeight n k) x = 1 := by
  have hsum := sum_inducedWeight_booleanLayer n k a
  have huniform := sum_inducedWeight_booleanLayer_eq_card_mul n k a hx
  have heq : (n.choose a : ℝ) *
      WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) x = (n.choose a : ℝ) := by
    calc
      (n.choose a : ℝ) *
          WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
            (chainWeight n k) x =
          (booleanLayerFinset n a).card *
            WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
              (chainWeight n k) x := by rw [card_booleanLayerFinset]
      _ = ∑ y ∈ booleanLayerFinset n a,
          WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
            (chainWeight n k) y := huniform.symm
      _ = actualLayerWeightTotal n k a := hsum
      _ = (n.choose a : ℝ) := htotal
  have hpositive : (0 : ℝ) < n.choose a := by
    exact_mod_cast Nat.choose_pos ha
  nlinarith

/-- A bridge against the recursive bookkeeping total suffices to force unit
induced weight on a lower layer. -/
theorem inducedWeight_eq_one_of_actual_eq_layerWeightTotal
    (n k a : ℕ) (hkn : k ≤ n) (hlower : 2 * a ≤ n)
    {x : Cube n 1} (hx : Cube.rank x = a)
    (hbridge : actualLayerWeightTotal n k a = (layerWeightTotal n k a : ℝ)) :
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
      (chainWeight n k) x = 1 := by
  apply inducedWeight_eq_one_of_actualLayerWeightTotal_eq_choose n k a (by omega) hx
  rw [hbridge]
  exact_mod_cast layerWeightTotal_eq_choose n k a hkn hlower

/-- The individual chain weights induce weight one at every vertex on the
lower side of the Boolean cube. -/
theorem inducedWeight_eq_one_lower (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (x : Cube n 1) (hlower : 2 * Cube.rank x ≤ n) :
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
      (chainWeight n k) x = 1 := by
  apply inducedWeight_eq_one_of_actual_eq_layerWeightTotal
    n k (Cube.rank x) hkn hlower rfl
  exact actualLayerWeightTotal_eq_layerWeightTotal k n (Cube.rank x) hk hkn hlower

@[simp]
theorem isGood_reflect_iff (C : BooleanChain n) (k : ℕ) :
    C.reflect.IsGood k ↔ C.IsGood k := by
  rw [isGood_iff, isGood_iff]
  exact C.good_reflect_iff k

/-- The canonical start-group label carried to by chain reflection.  Central
symmetric groups are fixed; every other occupied group is sent to its
complementary label. -/
def reflectedStartLabel (n k a : ℕ) : ℕ :=
  if 2 * a ≤ n ∧ n ≤ 2 * a + k then a else n - a

/-- Reflection transports the canonical label of a good represented chain
according to `reflectedStartLabel`. -/
theorem canonicalStart_reflect_of_isGood (C : BooleanChain n) (k : ℕ)
    (hk : 0 < k) (hgood : C.IsGood k) :
    C.reflect.canonicalStart =
      reflectedStartLabel n k C.canonicalStart := by
  rw [C.reflect.canonicalStart_eq_ite, C.canonicalStart_eq_ite]
  simp only [card_reflect_start, reflect_steps]
  unfold reflectedStartLabel
  have hend := C.endpointRank_le
  rcases hgood with ⟨hstepsLe, hsym | hfull⟩
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem startingWeight_reflectedStartLabel (n k a : ℕ) (ha : a ≤ n) :
    startingWeight n k (reflectedStartLabel n k a) =
      startingWeight n k a := by
  unfold reflectedStartLabel
  split_ifs
  · rfl
  · exact startingWeight_reflect ha

theorem reflectedStartLabel_involutive_of_isGood (C : BooleanChain n) (k : ℕ)
    (hk : 0 < k) (hgood : C.IsGood k) :
    reflectedStartLabel n k
        (reflectedStartLabel n k C.canonicalStart) =
      C.canonicalStart := by
  have hgoodReflect : C.reflect.IsGood k :=
    (C.isGood_reflect_iff k).mpr hgood
  have hfirst := C.canonicalStart_reflect_of_isGood k hk hgood
  have hsecond :=
    C.reflect.canonicalStart_reflect_of_isGood k hk hgoodReflect
  rw [reflect_reflect] at hsecond
  calc
    reflectedStartLabel n k
          (reflectedStartLabel n k C.canonicalStart) =
        reflectedStartLabel n k C.reflect.canonicalStart :=
      congrArg (reflectedStartLabel n k) hfirst.symm
    _ = C.canonicalStart := hsecond.symm

/-- Reflection is a bijection between the canonical start group of a good
chain and its reflected start group. -/
theorem card_startGroup_reflected_of_isGood (C : BooleanChain n) (k : ℕ)
    (hk : 0 < k) (hgood : C.IsGood k) :
    (startGroup n k C.canonicalStart).card =
      (startGroup n k
        (reflectedStartLabel n k C.canonicalStart)).card := by
  apply Finset.card_equiv (reflectEquiv n)
  intro D
  rw [mem_startGroup_iff, mem_startGroup_iff]
  simp only [reflectEquiv_apply]
  constructor
  · rintro ⟨hDgood, hDlabel⟩
    refine ⟨(D.isGood_reflect_iff k).mpr hDgood, ?_⟩
    rw [D.canonicalStart_reflect_of_isGood k hk hDgood, hDlabel]
  · rintro ⟨hDReflectGood, hDReflectLabel⟩
    have hDgood : D.IsGood k := (D.isGood_reflect_iff k).mp hDReflectGood
    refine ⟨hDgood, ?_⟩
    have hDcovariance := D.canonicalStart_reflect_of_isGood k hk hDgood
    have hlabels :
        reflectedStartLabel n k D.canonicalStart =
          reflectedStartLabel n k C.canonicalStart :=
      hDcovariance.symm.trans hDReflectLabel
    calc
      D.canonicalStart =
          reflectedStartLabel n k
            (reflectedStartLabel n k D.canonicalStart) :=
        (D.reflectedStartLabel_involutive_of_isGood k hk hDgood).symm
      _ = reflectedStartLabel n k
            (reflectedStartLabel n k C.canonicalStart) :=
        congrArg (reflectedStartLabel n k) hlabels
      _ = C.canonicalStart :=
        C.reflectedStartLabel_involutive_of_isGood k hk hgood

/-- The individual Section 4 weight is invariant under complementing and
reversing its represented Boolean chain. -/
theorem chainWeight_reflect (C : BooleanChain n) (k : ℕ) (hk : 0 < k) :
    chainWeight n k C.reflect = chainWeight n k C := by
  by_cases hgood : C.IsGood k
  · have hgoodReflect : C.reflect.IsGood k :=
      (C.isGood_reflect_iff k).mpr hgood
    rw [chainWeight, if_pos hgoodReflect, chainWeight, if_pos hgood]
    unfold startGroupChainWeight
    rw [C.canonicalStart_reflect_of_isGood k hk hgood,
      startingWeight_reflectedStartLabel n k C.canonicalStart
        C.canonicalStart_le,
      ← C.card_startGroup_reflected_of_isGood k hk hgood]
  · have hbadReflect : ¬C.reflect.IsGood k := by
      simpa using hgood
    simp [chainWeight, hgood, hbadReflect]

/-- Complementary Boolean vertices receive the same induced weight from the
concrete Section 4 weighting. -/
theorem inducedChainWeight_reflect (n k : ℕ) (hk : 0 < k) (x : Cube n 1) :
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) (Cube.reflect x) =
      WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) x :=
  inducedWeight_reflect (chainWeight n k)
    (fun C ↦ C.chainWeight_reflect k hk) x

/-- The Section 4 chain weights induce weight one at every Boolean vertex.
The lower half is the layer-total calculation; the upper half follows by
reflection. -/
theorem inducedWeight_eq_one (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (x : Cube n 1) :
    WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
      (chainWeight n k) x = 1 := by
  by_cases hlower : 2 * Cube.rank x ≤ n
  · exact inducedWeight_eq_one_lower k n hk hkn x hlower
  · have hrankLe : Cube.rank x ≤ n := by
      simpa using Cube.rank_le x
    have hreflectLower : 2 * Cube.rank (Cube.reflect x) ≤ n := by
      rw [Cube.rank_reflect]
      omega
    rw [← inducedChainWeight_reflect n k hk x]
    exact inducedWeight_eq_one_lower k n hk hkn (Cube.reflect x) hreflectLower

/-- The finite index type containing exactly the good represented chains. -/
abbrev GoodIndex (n k : ℕ) := {C : BooleanChain n // C.IsGood k}

/-- The generic chain carried by a good-chain index. -/
def indexedChain {n k : ℕ} (i : GoodIndex n k) : Chain n 1 := i.1.toChain

/-- The individual weight restricted to the actual good-chain family. -/
def indexedWeight (n k : ℕ) (i : GoodIndex n k) : ℝ := chainWeight n k i.1

theorem indexedChain_good {n k : ℕ} (i : GoodIndex n k) :
    (indexedChain i).Good k :=
  (i.1.isGood_iff k).mp i.2

theorem indexedWeight_pos (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (i : GoodIndex n k) :
    0 < indexedWeight n k i :=
  i.1.chainWeight_pos_of_isGood k hk hkn i.2

theorem indexedWeight_nonneg (k n : ℕ) (hk : 1 < k) (hkn : k ≤ n)
    (i : GoodIndex n k) :
    0 ≤ indexedWeight n k i :=
  (indexedWeight_pos k n hk hkn i).le

/-- Removing the zero-weight non-good descriptors from the ambient finite
type does not change induced weights. -/
theorem indexedInducedWeight_eq (n k : ℕ) (x : Cube n 1) :
    WeightedCover.inducedWeight (fun i : GoodIndex n k ↦ (indexedChain i).vertices)
        (indexedWeight n k) x =
      WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) x := by
  let goodFinset := (Finset.univ : Finset (BooleanChain n)).filter fun C ↦ C.IsGood k
  let term := fun C : BooleanChain n ↦
    if x ∈ C.toChain.vertices then chainWeight n k C else 0
  calc
    WeightedCover.inducedWeight (fun i : GoodIndex n k ↦ (indexedChain i).vertices)
        (indexedWeight n k) x = ∑ i : GoodIndex n k, term i.1 := rfl
    _ = ∑ C ∈ goodFinset, term C := by
      symm
      apply Finset.sum_subtype (p := fun C : BooleanChain n ↦ C.IsGood k)
      intro C
      simp [goodFinset]
    _ = ∑ C : BooleanChain n, term C := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C _hC hnot
      have hbad : ¬C.IsGood k := by
        simpa [goodFinset] using hnot
      simp [term, chainWeight, hbad]
    _ = WeightedCover.inducedWeight (fun C : BooleanChain n ↦ C.toChain.vertices)
        (chainWeight n k) x := rfl

theorem indexedInducedWeight_eq_one_lower (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (x : Cube n 1) (hlower : 2 * Cube.rank x ≤ n) :
    WeightedCover.inducedWeight (fun i : GoodIndex n k ↦ (indexedChain i).vertices)
      (indexedWeight n k) x = 1 := by
  rw [indexedInducedWeight_eq]
  exact inducedWeight_eq_one_lower k n hk hkn x hlower

/-- The actual finite family of good represented chains, with the Section 4
weights, covers every Boolean vertex with total induced weight one. -/
theorem indexedInducedWeight_eq_one (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (x : Cube n 1) :
    WeightedCover.inducedWeight (fun i : GoodIndex n k ↦ (indexedChain i).vertices)
      (indexedWeight n k) x = 1 := by
  rw [indexedInducedWeight_eq]
  exact inducedWeight_eq_one k n hk hkn x

end BooleanChain
end DOne
end WeightedChains
