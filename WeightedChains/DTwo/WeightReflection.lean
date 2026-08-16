import WeightedChains.DTwo.CanonicalIncidenceSum

/-!
# Reflection symmetry of the concrete ternary weighting

Reflection reverses a basic chain.  The tie convention for symmetric chains
means that its canonical label is not always literally reflected, so the
weight symmetry is proved at descriptor level, including the corresponding
start-group cardinalities.
-/

noncomputable section

namespace WeightedChains
namespace Ternary

@[simp]
theorem zeroCount_reflect {n : ℕ} (x : Cube n 2) :
    zeroCount (Cube.reflect x) = twoCount x := by
  unfold zeroCount twoCount Cube.typeOf
  apply Finset.card_equiv (Equiv.refl (Fin n))
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.refl_apply]
  change (x i).rev = 0 ↔ x i = 2
  constructor <;> intro h
  · apply Fin.ext_iff.mpr
    have hval := Fin.ext_iff.mp h
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_two] at hval ⊢
    have hx := (x i).isLt
    omega
  · apply Fin.ext_iff.mpr
    have hval := Fin.ext_iff.mp h
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_two] at hval ⊢
    have hx := (x i).isLt
    omega

@[simp]
theorem oneCount_reflect {n : ℕ} (x : Cube n 2) :
    oneCount (Cube.reflect x) = oneCount x := by
  unfold oneCount Cube.typeOf
  apply Finset.card_equiv (Equiv.refl (Fin n))
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.refl_apply]
  change (x i).rev = 1 ↔ x i = 1
  constructor <;> intro h
  · apply Fin.ext_iff.mpr
    have hval := Fin.ext_iff.mp h
    simp only [Fin.val_rev, Fin.val_one] at hval ⊢
    have hx := (x i).isLt
    omega
  · apply Fin.ext_iff.mpr
    have hval := Fin.ext_iff.mp h
    simp only [Fin.val_rev, Fin.val_one] at hval ⊢
    have hx := (x i).isLt
    omega

@[simp]
theorem twoCount_reflect {n : ℕ} (x : Cube n 2) :
    twoCount (Cube.reflect x) = zeroCount x := by
  unfold zeroCount twoCount Cube.typeOf
  apply Finset.card_equiv (Equiv.refl (Fin n))
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.refl_apply]
  change (x i).rev = 2 ↔ x i = 0
  constructor <;> intro h
  · apply Fin.ext_iff.mpr
    have hval := Fin.ext_iff.mp h
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_two] at hval ⊢
    have hx := (x i).isLt
    omega
  · apply Fin.ext_iff.mpr
    have hval := Fin.ext_iff.mp h
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_two] at hval ⊢
    have hx := (x i).isLt
    omega

@[simp]
theorem TypeCounts.ofVertex_reflect {n : ℕ} (x : Cube n 2) :
    TypeCounts.ofVertex (Cube.reflect x) = (TypeCounts.ofVertex x).reflect := by
  apply TypeCounts.ext <;> simp [TypeCounts.ofVertex]

namespace BasicChain

variable {n : ℕ}

/-- Reflection preserves the prescribed total attached to a descriptor's
canonical label, including the symmetric tie case. -/
theorem startTypeTotal_canonicalStartType_reflect
    (B : BasicChain n) (k : ℕ) :
    startTypeTotal k B.reflect.canonicalStartType =
      startTypeTotal k B.canonicalStartType := by
  have hfirstRank : Cube.rank B.toChain.first = Cube.rank B.start := by
    rw [B.toChain_first]
  have hfirstBound := Cube.rank_le B.toChain.first
  have hlastBound := Cube.rank_le B.toChain.last
  have hrankMono : Cube.rank B.toChain.first ≤ Cube.rank B.toChain.last :=
    Cube.rank_mono B.toChain.first_le_last
  unfold canonicalStartType
  simp only [B.toChain_first_reflect, B.toChain_last_reflect,
    middleDistance_reflect, TypeCounts.ofVertex_reflect, B.toChain_first]
  by_cases hlastFarther :
      Cube.middleDistance B.toChain.last < Cube.middleDistance B.start
  · have hfirstNot : ¬Cube.middleDistance B.start ≤
        Cube.middleDistance B.toChain.last := by omega
    have hlastLe : Cube.middleDistance B.toChain.last ≤
        Cube.middleDistance B.start := hlastFarther.le
    rw [if_neg hfirstNot, if_pos hlastLe, startTypeTotal_reflect]
  · by_cases hfirstFarther :
        Cube.middleDistance B.start < Cube.middleDistance B.toChain.last
    · have hfirstLe : Cube.middleDistance B.start ≤
          Cube.middleDistance B.toChain.last := hfirstFarther.le
      have hlastNot : ¬Cube.middleDistance B.toChain.last ≤
          Cube.middleDistance B.start := by omega
      rw [if_pos hfirstLe, if_neg hlastNot, startTypeTotal_reflect]
    · have hdistance : Cube.middleDistance B.toChain.last =
          Cube.middleDistance B.start := by omega
      have hboth : Cube.middleDistance B.start ≤
          Cube.middleDistance B.toChain.last := hdistance.ge
      have hboth' : Cube.middleDistance B.toChain.last ≤
          Cube.middleDistance B.start := hdistance.le
      rw [if_pos hboth, if_pos hboth']
      by_cases hrankEq : Cube.rank B.toChain.first = Cube.rank B.toChain.last
      · have hwidth : (B.width : ℕ) = 0 := by
          rw [B.rank_toChain_first, B.rank_toChain_last] at hrankEq
          omega
        have hwidthFin : B.width = 0 := Fin.ext hwidth
        have hlast : B.toChain.last = B.start := by
          rw [B.toChain_last, hwidthFin]
          funext q
          simp [evenVertex, initialSegment]
        have hstartType : TypeCounts.ofVertex B.toChain.last =
            TypeCounts.ofVertex B.start := by
          rw [hlast]
        rw [hstartType, startTypeTotal_reflect]
      · have hrankLt : Cube.rank B.toChain.first <
            Cube.rank B.toChain.last := lt_of_le_of_ne hrankMono hrankEq
        have hfirstBelow : Cube.rank B.toChain.first < n := by
          by_contra hnot
          have hfirstAbove : n ≤ Cube.rank B.toChain.first := by omega
          unfold Cube.middleDistance at hdistance
          rw [Nat.dist_eq_sub_of_le_right (by omega),
            Nat.dist_eq_sub_of_le_right (by omega)] at hdistance
          rw [B.toChain_first] at hrankLt
          omega
        have hlastAbove : n < Cube.rank B.toChain.last := by
          by_contra hnot
          have hlastBelow : Cube.rank B.toChain.last ≤ n := by omega
          unfold Cube.middleDistance at hdistance
          rw [Nat.dist_eq_sub_of_le (by omega),
            Nat.dist_eq_sub_of_le (by omega)] at hdistance
          rw [B.toChain_first] at hrankLt
          omega
        have hrankSum : Cube.rank B.toChain.first +
            Cube.rank B.toChain.last = 2 * n := by
          unfold Cube.middleDistance at hdistance
          rw [Nat.dist_eq_sub_of_le_right (by omega),
            Nat.dist_eq_sub_of_le (by omega)] at hdistance
          omega
        have hsymmetric : B.toChain.Symmetric := by
          rw [Chain.symmetric_iff_endpoint B.toChain B.toChain_saturated]
          simpa [Nat.mul_comm] using hrankSum
        have hlastType := B.type_toChain_last_eq_reflect hsymmetric
        rw [hlastType, TypeCounts.reflect_reflect]

/-- Descriptors in one canonical group also have the same canonical label
after reflection. -/
theorem canonicalStartType_reflect_eq_of_mem_startGroup
    (k : ℕ) (hk : 0 < k) (t : TypeCounts n)
    {B C : BasicChain n} (hB : B ∈ startGroup n k t)
    (hC : C ∈ startGroup n k t) :
    C.reflect.canonicalStartType = B.reflect.canonicalStartType := by
  have hwidthNat := width_eq_of_mem_startGroup k hk t hB hC
  have hfirst : TypeCounts.ofVertex B.toChain.first =
      TypeCounts.ofVertex C.toChain.first := by
    simpa only [B.toChain_first, C.toChain_first] using
      type_start_eq_of_mem_startGroup k hk t hB hC
  have htrace := type_vertexAt_eq_of_mem_startGroup
    k hk t hB hC (2 * B.width) le_rfl
  have hlast : TypeCounts.ofVertex B.toChain.last =
      TypeCounts.ofVertex C.toChain.last := by
    calc
      TypeCounts.ofVertex B.toChain.last =
          TypeCounts.ofVertex (B.vertexAt (2 * B.width)) := rfl
      _ = TypeCounts.ofVertex (C.vertexAt (2 * B.width)) := htrace
      _ = TypeCounts.ofVertex (C.vertexAt (2 * C.width)) := by
        rw [hwidthNat]
      _ = TypeCounts.ofVertex C.toChain.last := rfl
  have hfirstRank : Cube.rank C.toChain.first = Cube.rank B.toChain.first := by
    rw [← TypeCounts.rank_ofVertex, ← TypeCounts.rank_ofVertex, ← hfirst]
  have hlastRank : Cube.rank C.toChain.last = Cube.rank B.toChain.last := by
    rw [← TypeCounts.rank_ofVertex, ← TypeCounts.rank_ofVertex, ← hlast]
  have hfirstDistance : Cube.middleDistance C.toChain.first =
      Cube.middleDistance B.toChain.first := by
    unfold Cube.middleDistance
    rw [hfirstRank]
  have hlastDistance : Cube.middleDistance C.toChain.last =
      Cube.middleDistance B.toChain.last := by
    unfold Cube.middleDistance
    rw [hlastRank]
  have hstart : TypeCounts.ofVertex B.start =
      TypeCounts.ofVertex C.start := by
    simpa only [B.toChain_first, C.toChain_first] using hfirst
  have hstartDistance : Cube.middleDistance C.start =
      Cube.middleDistance B.start := by
    simpa only [B.toChain_first, C.toChain_first] using hfirstDistance
  unfold canonicalStartType
  simp only [C.toChain_first_reflect, C.toChain_last_reflect,
    B.toChain_first_reflect, B.toChain_last_reflect,
    middleDistance_reflect, TypeCounts.ofVertex_reflect]
  rw [hstartDistance, hlastDistance]
  split
  · exact congrArg TypeCounts.reflect hlast.symm
  · exact congrArg TypeCounts.reflect hstart.symm

/-- Reflection bijects the canonical start group of a good descriptor with
the canonical start group of its reflection. -/
theorem card_startGroup_reflect_canonicalStartType
    (B : BasicChain n) (k : ℕ) (hk : 0 < k)
    (hgood : B.toChain.Good k) :
    (startGroup n k B.reflect.canonicalStartType).card =
      (startGroup n k B.canonicalStartType).card := by
  symm
  apply Finset.card_equiv (reflectEquiv n)
  intro C
  constructor
  · intro hC
    have hB : B ∈ startGroup n k B.canonicalStartType :=
      (mem_startGroup_canonicalStartType_iff B k).2 hgood
    have hCdata := (mem_startGroup_iff C k B.canonicalStartType).1 hC
    apply (mem_startGroup_iff C.reflect k B.reflect.canonicalStartType).2
    refine ⟨(C.toChain_good_reflect_iff k).2 hCdata.1, ?_⟩
    exact canonicalStartType_reflect_eq_of_mem_startGroup
      k hk B.canonicalStartType hB hC
  · intro hC
    have hBreflect : B.reflect ∈
        startGroup n k B.reflect.canonicalStartType :=
      (mem_startGroup_canonicalStartType_iff B.reflect k).2
        ((B.toChain_good_reflect_iff k).2 hgood)
    have hCdata :=
      (mem_startGroup_iff C.reflect k B.reflect.canonicalStartType).1 hC
    have hreflected := canonicalStartType_reflect_eq_of_mem_startGroup
      k hk B.reflect.canonicalStartType hBreflect hC
    apply (mem_startGroup_iff C k B.canonicalStartType).2
    refine ⟨(C.toChain_good_reflect_iff k).1 hCdata.1, ?_⟩
    change C.reflect.reflect.canonicalStartType =
      B.reflect.reflect.canonicalStartType at hreflected
    simpa only [reflect_reflect] using hreflected

/-- The concrete distributed descriptor weight is invariant under chain
reflection. -/
@[simp]
theorem distributedStartTypeWeight_reflect
    (B : BasicChain n) (k : ℕ) (hk : 0 < k) :
    distributedChainWeight (startTypeTotal k) k B.reflect =
      distributedChainWeight (startTypeTotal k) k B := by
  by_cases hgood : B.toChain.Good k
  · have hgoodReflect : B.reflect.toChain.Good k :=
      (B.toChain_good_reflect_iff k).2 hgood
    unfold distributedChainWeight
    rw [if_pos (B.reflect.isGood_iff k |>.2 hgoodReflect),
      if_pos (B.isGood_iff k |>.2 hgood),
      startTypeTotal_canonicalStartType_reflect,
      card_startGroup_reflect_canonicalStartType B k hk hgood]
  · have hgoodReflect : ¬B.reflect.toChain.Good k := by
      intro h
      exact hgood ((B.toChain_good_reflect_iff k).1 h)
    unfold distributedChainWeight
    rw [if_neg (fun h ↦ hgoodReflect ((B.reflect.isGood_iff k).1 h)),
      if_neg (fun h ↦ hgood ((B.isGood_iff k).1 h))]

/-- Reflection of vertices preserves induced weight for the concrete
descriptor weighting. -/
theorem inducedWeight_startTypeTotal_reflect
    (n k : ℕ) (hk : 0 < k) (x : Cube n 2) :
    WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) (Cube.reflect x) =
      WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) x := by
  let summand := fun y : Cube n 2 ↦ fun B : BasicChain n ↦
    if y ∈ B.toChain.vertices then
      distributedChainWeight (startTypeTotal k) k B else 0
  calc
    WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) (Cube.reflect x) =
      ∑ B, summand (Cube.reflect x) B := rfl
    _ = ∑ B, summand (Cube.reflect x) (reflectEquiv n B) :=
      (Equiv.sum_comp (reflectEquiv n) (summand (Cube.reflect x))).symm
    _ = ∑ B, summand x B := by
      apply Fintype.sum_congr
      intro B
      change (if Cube.reflect x ∈ B.reflect.toChain.vertices then
          distributedChainWeight (startTypeTotal k) k B.reflect else 0) =
        if x ∈ B.toChain.vertices then
          distributedChainWeight (startTypeTotal k) k B else 0
      have hmem := B.mem_vertices_reflect_iff (Cube.reflect x)
      rw [Cube.reflect_reflect] at hmem
      by_cases hx : x ∈ B.toChain.vertices
      · have hreflect := hmem.2 hx
        simp [hx, hreflect, distributedStartTypeWeight_reflect B k hk]
      · have hreflect : Cube.reflect x ∉ B.reflect.toChain.vertices := by
          intro h
          exact hx (hmem.1 h)
        simp [hx, hreflect]
    _ = WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) x := rfl

/-- The concrete weighting induces weight one at every vertex of a lower
type. -/
theorem inducedWeight_startTypeTotal_eq_one_of_lower
    (n k a c : ℕ) (hk : 0 < k) (hvalid : a + c ≤ n) (hca : c ≤ a)
    {x : Cube n 2} (hxzero : zeroCount x = a) (hxtwo : twoCount x = c) :
    WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) x = 1 := by
  apply inducedWeight_eq_one_of_total_eq_trinomial
    (distributedChainWeight (startTypeTotal k) k)
    (distributedChainWeight_reindex (startTypeTotal k) k)
    a c hxzero hxtwo
  exact totalInducedWeightOnType_startTypeTotal_eq_trinomial_of_lower
    n k a c hk hvalid hca

/-- The concrete distributed weighting is a fractional cover of the whole
ternary cube. -/
theorem inducedWeight_startTypeTotal_eq_one
    (n k : ℕ) (hk : 0 < k) (x : Cube n 2) :
    WeightedCover.inducedWeight
        (fun B : BasicChain n ↦ B.toChain.vertices)
        (distributedChainWeight (startTypeTotal k) k) x = 1 := by
  have hvalid : zeroCount x + twoCount x ≤ n := by
    have hsum := zeroCount_add_oneCount_add_twoCount x
    omega
  by_cases hlower : twoCount x ≤ zeroCount x
  · exact inducedWeight_startTypeTotal_eq_one_of_lower
      n k (zeroCount x) (twoCount x) hk hvalid hlower rfl rfl
  · have hreflectedLower : twoCount (Cube.reflect x) ≤
        zeroCount (Cube.reflect x) := by
      simp only [twoCount_reflect, zeroCount_reflect]
      omega
    have hreflectedValid : zeroCount (Cube.reflect x) +
        twoCount (Cube.reflect x) ≤ n := by
      simpa only [zeroCount_reflect, twoCount_reflect, Nat.add_comm] using hvalid
    have hcover := inducedWeight_startTypeTotal_eq_one_of_lower
      n k (zeroCount (Cube.reflect x)) (twoCount (Cube.reflect x)) hk
      hreflectedValid hreflectedLower (x := Cube.reflect x) rfl rfl
    rw [inducedWeight_startTypeTotal_reflect n k hk x] at hcover
    exact hcover

end BasicChain
end Ternary
end WeightedChains
