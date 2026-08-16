import WeightedChains.GoodChainResidues
import WeightedChains.Appendices.LargeK

/-!
# The general asymptotic result

For fixed positive `d` and `k`, the largest `k`-separated family in
`{0, ..., d}^n` has density tending to `1 / (d * k + 1)`.

The upper bound repeatedly removes a block of `k` coordinates.  A symmetric
chain decomposition of that block contains a saturated chain with
`d * k + 1` vertices.  At most one point above each fixed tail can use that
chain—the maximal-length higher-dimensional analogue of a basic chain—while
every other block vertex leaves a smaller `k`-separated family.
The resulting contracting recurrence gives the limit.  The matching lower
bound uses the `d * k + 1` rank-residue families.
-/

namespace WeightedChains
namespace Asymptotics

open Filter Topology

noncomputable section

/-- All finite `k`-separated families in a cube. -/
def kSeparatedFinsets (n d k : ℕ) : Finset (Finset (Cube n d)) := by
  classical
  exact Finset.univ.filter fun A ↦ Cube.KSeparated (A : Set (Cube n d)) k

/-- The largest cardinality of a `k`-separated family in `{0, ..., d}^n`. -/
def maxKSeparatedCard (n d k : ℕ) : ℕ :=
  (kSeparatedFinsets n d k).sup Finset.card

theorem card_le_maxKSeparatedCard {n d k : ℕ} (A : Finset (Cube n d))
    (hA : Cube.KSeparated (A : Set (Cube n d)) k) :
    A.card ≤ maxKSeparatedCard n d k := by
  classical
  unfold maxKSeparatedCard
  apply Finset.le_sup (f := Finset.card)
  simp [kSeparatedFinsets, hA]

theorem maxKSeparatedCard_le_univ_card (n d k : ℕ) :
    maxKSeparatedCard n d k ≤ Fintype.card (Cube n d) := by
  classical
  unfold maxKSeparatedCard
  apply Finset.sup_le
  intro A hA
  exact A.card_le_univ

theorem card_cube (n d : ℕ) : Fintype.card (Cube n d) = (d + 1) ^ n := by
  simp

theorem exists_kSeparated_card_eq_maxKSeparatedCard (n d k : ℕ) :
    ∃ A : Finset (Cube n d),
      Cube.KSeparated (A : Set (Cube n d)) k ∧
        A.card = maxKSeparatedCard n d k := by
  classical
  have hfamilies : (kSeparatedFinsets n d k).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [kSeparatedFinsets, Cube.KSeparated]
  obtain ⟨A, hA, hcard⟩ :=
    Finset.exists_mem_eq_sup (kSeparatedFinsets n d k) hfamilies Finset.card
  refine ⟨A, ?_, hcard.symm⟩
  exact (Finset.mem_filter.mp hA).2

/-- The rank-residue families give the averaging lower bound. -/
theorem cube_card_le_modulus_mul_maxKSeparatedCard (n d k : ℕ) :
    (d + 1) ^ n ≤ (d * k + 1) * maxKSeparatedCard n d k := by
  classical
  rw [← card_cube]
  by_contra h
  have hlt : (d * k + 1) * maxKSeparatedCard n d k < Fintype.card (Cube n d) :=
    Nat.lt_of_not_ge h
  let residue : Cube n d → Fin (d * k + 1) := fun x ↦
    ⟨Cube.rank x % (d * k + 1), Nat.mod_lt _ (by omega)⟩
  have hlt' : Fintype.card (Fin (d * k + 1)) * maxKSeparatedCard n d k <
      Fintype.card (Cube n d) := by simpa using hlt
  obtain ⟨r, hr⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card residue hlt'
  let A : Finset (Cube n d) := Finset.univ.filter fun x ↦ residue x = r
  have hAcard : maxKSeparatedCard n d k < A.card := by
    simpa [A, Set.ncard_eq_toFinset_card] using hr
  have hAseparated : Cube.KSeparated (A : Set (Cube n d)) k := by
    intro x y hx hy hxy hne
    apply Cube.residueFamily_kSeparated n d k (r : ℕ) ?_ ?_ hxy hne
    · have hx' : residue x = r := by simpa [A] using hx
      change Cube.rank x ≡ (r : ℕ) [MOD d * k + 1]
      change Cube.rank x % (d * k + 1) = (r : ℕ) % (d * k + 1)
      have := congrArg Fin.val hx'
      simpa [residue, Nat.mod_eq_of_lt r.isLt] using this
    · have hy' : residue y = r := by simpa [A] using hy
      change Cube.rank y ≡ (r : ℕ) [MOD d * k + 1]
      change Cube.rank y % (d * k + 1) = (r : ℕ) % (d * k + 1)
      have := congrArg Fin.val hy'
      simpa [residue, Nat.mod_eq_of_lt r.isLt] using this
  exact (Nat.not_lt_of_ge (card_le_maxKSeparatedCard A hAseparated)) hAcard

/-! ## A full chain in a `k`-coordinate block -/

private def zeroVertex (k d : ℕ) : Cube k d := fun _ ↦ 0

private def fullChainIndex (k d : ℕ) : (LargeK.cubeSCD k d).Index :=
  ((LargeK.cubeSCD k d).encode (zeroVertex k d)).1

private theorem fullChain_startRank (k d : ℕ) :
    (LargeK.cubeSCD k d).startRank (fullChainIndex k d) = 0 := by
  have hrank : Cube.rank (zeroVertex k d) =
      (LargeK.cubeSCD k d).startRank (fullChainIndex k d) +
        ((LargeK.cubeSCD k d).encode (zeroVertex k d)).2 := by
    simpa only [fullChainIndex] using
      (LargeK.cubeSCD k d).rank_encode (zeroVertex k d)
  have hzero : Cube.rank (zeroVertex k d) = 0 := by
    simp [Cube.rank, zeroVertex]
  rw [hzero] at hrank
  omega

private theorem fullChain_steps (k d : ℕ) :
    (LargeK.cubeSCD k d).steps (fullChainIndex k d) = k * d := by
  have hsym := (LargeK.cubeSCD k d).symmetric (fullChainIndex k d)
  rw [fullChain_startRank] at hsym
  omega

/-- The rank-zero chain of the symmetric-chain decomposition.  Symmetry makes
it a full saturated chain of `d * k + 1` vertices. -/
private def fullChainFinset (k d : ℕ) : Finset (Cube k d) := by
  classical
  let S := LargeK.cubeSCD k d
  let i := fullChainIndex k d
  exact Finset.univ.image fun p : Fin (S.steps i + 1) ↦ S.encode.symm ⟨i, p⟩

private theorem mem_fullChainFinset_iff (k d : ℕ) (x : Cube k d) :
    x ∈ fullChainFinset k d ↔
      ((LargeK.cubeSCD k d).encode x).1 = fullChainIndex k d := by
  classical
  let S := LargeK.cubeSCD k d
  let i := fullChainIndex k d
  constructor
  · intro hx
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hx
    simp
  · intro hx
    rcases hxenc : S.encode x with ⟨j, p⟩
    have hji : j = i := by simpa only [S, i, hxenc] using hx
    subst j
    have hxrepr : S.encode.symm ⟨i, p⟩ = x := by
      simpa only [hxenc] using S.encode.symm_apply_apply x
    apply Finset.mem_image.mpr
    exact ⟨p, Finset.mem_univ p, hxrepr⟩

private theorem card_fullChainFinset (k d : ℕ) :
    (fullChainFinset k d).card = d * k + 1 := by
  classical
  let S := LargeK.cubeSCD k d
  let i := fullChainIndex k d
  change (Finset.univ.image fun p : Fin (S.steps i + 1) ↦ S.encode.symm ⟨i, p⟩).card = _
  rw [Finset.card_image_of_injective]
  · simp [S, i, fullChain_steps, Nat.mul_comm]
  · intro p q hpq
    have hsigma : (⟨i, p⟩ : Σ i, Fin (S.steps i + 1)) = ⟨i, q⟩ :=
      S.encode.symm.injective hpq
    exact eq_of_heq (Sigma.ext_iff.mp hsigma).2

private theorem comparable_of_mem_fullChainFinset (k d : ℕ)
    {x y : Cube k d} (hx : x ∈ fullChainFinset k d)
    (hy : y ∈ fullChainFinset k d) : x ≤ y ∨ y ≤ x := by
  apply (LargeK.cubeSCD k d).comparable_of_same_chain
  exact (mem_fullChainFinset_iff k d x).mp hx |>.trans
    ((mem_fullChainFinset_iff k d y).mp hy).symm

/-! ## The block recurrence -/

private def splitFamily {k n d : ℕ} (A : Finset (Cube (k + n) d)) :
    Finset (Cube k d × Cube n d) :=
  A.map (LargeK.splitCubeEquiv k n d).toEmbedding

private def blockFiber {k n d : ℕ} (P : Finset (Cube k d × Cube n d))
    (b : Cube k d) : Finset (Cube k d × Cube n d) :=
  P.filter fun z ↦ z.1 = b

private def tailSlice {k n d : ℕ} (P : Finset (Cube k d × Cube n d))
    (b : Cube k d) : Finset (Cube n d) :=
  (blockFiber P b).image Prod.snd

private theorem card_blockFiber_eq_tailSlice {k n d : ℕ}
    (P : Finset (Cube k d × Cube n d)) (b : Cube k d) :
    (blockFiber P b).card = (tailSlice P b).card := by
  classical
  symm
  apply Finset.card_image_iff.mpr
  intro z hz w hw hzw
  apply Prod.ext
  · have hzb : z.1 = b := (Finset.mem_filter.mp hz).2
    have hwb : w.1 = b := (Finset.mem_filter.mp hw).2
    exact hzb.trans hwb.symm
  · exact hzw

private theorem tailSlice_kSeparated {k n d : ℕ}
    (A : Finset (Cube (k + n) d))
    (hA : Cube.KSeparated (A : Set (Cube (k + n) d)) k)
    (b : Cube k d) :
    Cube.KSeparated (tailSlice (splitFamily A) b : Set (Cube n d)) k := by
  classical
  intro y y' hy hy' hyy' hne
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
  have hzP : z ∈ splitFamily A := (Finset.mem_filter.mp hz).1
  have hwP : w ∈ splitFamily A := (Finset.mem_filter.mp hw).1
  have hzb : z.1 = b := (Finset.mem_filter.mp hz).2
  have hwb : w.1 = b := (Finset.mem_filter.mp hw).2
  let E := LargeK.splitCubeEquiv k n d
  have hzx : E.symm z ∈ A := by simpa [splitFamily, E] using hzP
  have hwx : E.symm w ∈ A := by simpa [splitFamily, E] using hwP
  have hproduct : z ≤ w := by
    constructor
    · exact hzb.le.trans hwb.ge
    · exact hyy'
  have horder : E.symm z ≤ E.symm w := by
    apply (LargeK.splitCubeEquiv_le_iff k n d _ _).mp
    simpa [E] using hproduct
  have hdistinct : E.symm z ≠ E.symm w := by
    intro heq
    have : z = w := E.symm.injective heq
    exact hne (congrArg Prod.snd this)
  have hsep := hA hzx hwx horder hdistinct
  have hleft : (E (E.symm z)).1 = (E (E.symm w)).1 := by
    simpa [E] using hzb.trans hwb.symm
  rw [LargeK.hammingDistance_eq_right_of_left_eq k n d hleft] at hsep
  simpa [E] using hsep

private def chainPart {k n d : ℕ} (P : Finset (Cube k d × Cube n d)) :
    Finset (Cube k d × Cube n d) :=
  P.filter fun z ↦ z.1 ∈ fullChainFinset k d

private def offChainPart {k n d : ℕ} (P : Finset (Cube k d × Cube n d)) :
    Finset (Cube k d × Cube n d) :=
  P.filter fun z ↦ z.1 ∉ fullChainFinset k d

private def offChainBlocks (k d : ℕ) : Finset (Cube k d) :=
  Finset.univ.filter fun b ↦ b ∉ fullChainFinset k d

private theorem card_chainPart_le {k n d : ℕ}
    (A : Finset (Cube (k + n) d))
    (hA : Cube.KSeparated (A : Set (Cube (k + n) d)) k) :
    (chainPart (splitFamily A)).card ≤ (d + 1) ^ n := by
  classical
  let E := LargeK.splitCubeEquiv k n d
  let P := splitFamily A
  let C := chainPart P
  have hinj : Set.InjOn Prod.snd (C : Set (Cube k d × Cube n d)) := by
    intro z hz w hw hright
    by_contra hne
    have hzP : z ∈ P := (Finset.mem_filter.mp hz).1
    have hwP : w ∈ P := (Finset.mem_filter.mp hw).1
    have hzC : z.1 ∈ fullChainFinset k d := (Finset.mem_filter.mp hz).2
    have hwC : w.1 ∈ fullChainFinset k d := (Finset.mem_filter.mp hw).2
    have hzx : E.symm z ∈ A := by simpa [P, splitFamily, E] using hzP
    have hwx : E.symm w ∈ A := by simpa [P, splitFamily, E] using hwP
    have hdistinct : E.symm z ≠ E.symm w := by
      intro heq
      exact hne (E.symm.injective heq)
    have hdist : Cube.hammingDistance (E.symm z) (E.symm w) ≤ k := by
      apply LargeK.hammingDistance_le_left_of_right_eq k n d
      simpa [E] using hright
    rcases comparable_of_mem_fullChainFinset k d hzC hwC with hzw | hwz
    · have horder : E.symm z ≤ E.symm w := by
        apply (LargeK.splitCubeEquiv_le_iff k n d _ _).mp
        have hproduct : z ≤ w := ⟨hzw, hright.le⟩
        simpa [E] using hproduct
      exact (Nat.not_lt_of_ge hdist) (hA hzx hwx horder hdistinct)
    · have horder : E.symm w ≤ E.symm z := by
        apply (LargeK.splitCubeEquiv_le_iff k n d _ _).mp
        have hproduct : w ≤ z := ⟨hwz, hright.ge⟩
        simpa [E] using hproduct
      have hdist' : Cube.hammingDistance (E.symm w) (E.symm z) ≤ k := by
        simpa only [Cube.hammingDistance_comm] using hdist
      exact (Nat.not_lt_of_ge hdist') (hA hwx hzx horder (Ne.symm hdistinct))
  calc
    C.card = (C.image Prod.snd).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card (Cube n d) := Finset.card_le_univ _
    _ = (d + 1) ^ n := card_cube n d

private theorem card_offChainBlocks (k d : ℕ) :
    (offChainBlocks k d).card = (d + 1) ^ k - (d * k + 1) := by
  classical
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Cube k d)))
    (fun b ↦ b ∈ fullChainFinset k d)
  have hfirst : (Finset.univ.filter fun b : Cube k d ↦
      b ∈ fullChainFinset k d) = fullChainFinset k d := by ext; simp
  have hsecond : (Finset.univ.filter fun b : Cube k d ↦
      b ∉ fullChainFinset k d) = offChainBlocks k d := rfl
  rw [hfirst, hsecond, Finset.card_univ] at hpartition
  rw [card_fullChainFinset, card_cube] at hpartition
  omega

private theorem card_offChainPart_le {k n d : ℕ}
    (A : Finset (Cube (k + n) d))
    (hA : Cube.KSeparated (A : Set (Cube (k + n) d)) k) :
    (offChainPart (splitFamily A)).card ≤
      ((d + 1) ^ k - (d * k + 1)) * maxKSeparatedCard n d k := by
  classical
  let P := splitFamily A
  let O := offChainPart P
  have hmaps : Set.MapsTo Prod.fst (O : Set (Cube k d × Cube n d))
      (offChainBlocks k d : Set (Cube k d)) := by
    intro z hz
    simpa [O, offChainPart, offChainBlocks] using (Finset.mem_filter.mp hz).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ b ∈ offChainBlocks k d, (O.filter fun z ↦ z.1 = b).card ≤
        ∑ _b ∈ offChainBlocks k d, maxKSeparatedCard n d k := by
      apply Finset.sum_le_sum
      intro b hb
      have hbC : b ∉ fullChainFinset k d := by
        simpa [offChainBlocks] using hb
      have hfiber : O.filter (fun z ↦ z.1 = b) = blockFiber P b := by
        ext z
        change z ∈ (offChainPart P).filter (fun z ↦ z.1 = b) ↔
          z ∈ blockFiber P b
        simp only [offChainPart, blockFiber, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hzP, _hzC⟩, hzb⟩
          exact ⟨hzP, hzb⟩
        · rintro ⟨hzP, hzb⟩
          refine ⟨⟨hzP, ?_⟩, hzb⟩
          intro hzC
          exact hbC (hzb ▸ hzC)
      rw [hfiber, card_blockFiber_eq_tailSlice]
      apply card_le_maxKSeparatedCard
      exact tailSlice_kSeparated A hA b
    _ = ((d + 1) ^ k - (d * k + 1)) * maxKSeparatedCard n d k := by
      simp [card_offChainBlocks]

/-- Removing a block of `k` coordinates gives a contracting recurrence for
the extremal cardinality. -/
theorem maxKSeparatedCard_add_le (n d k : ℕ) :
    maxKSeparatedCard (k + n) d k ≤
      (d + 1) ^ n +
        ((d + 1) ^ k - (d * k + 1)) * maxKSeparatedCard n d k := by
  classical
  obtain ⟨A, hA, hcard⟩ := exists_kSeparated_card_eq_maxKSeparatedCard (k + n) d k
  let P := splitFamily A
  have hPcard : P.card = A.card := by simp [P, splitFamily]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := P) (fun z ↦ z.1 ∈ fullChainFinset k d)
  change (chainPart P).card + (offChainPart P).card = P.card at hpartition
  rw [hPcard, hcard] at hpartition
  rw [← hpartition]
  exact Nat.add_le_add (card_chainPart_le A hA) (card_offChainPart_le A hA)

/-! ## Solving the recurrence -/

/-- The extremal density in dimension `n`. -/
def density (n d k : ℕ) : ℝ :=
  (maxKSeparatedCard n d k : ℝ) / ((d + 1 : ℝ) ^ n)

/-- The contraction factor left after removing the full block chain. -/
private def contraction (d k : ℕ) : ℝ :=
  (((d + 1) ^ k - (d * k + 1) : ℕ) : ℝ) / ((d + 1 : ℝ) ^ k)

private theorem modulus_le_cubeBlockCard (d k : ℕ) :
    d * k + 1 ≤ (d + 1) ^ k := by
  rw [← card_fullChainFinset, ← card_cube]
  exact Finset.card_le_univ _

private theorem contraction_nonneg (d k : ℕ) : 0 ≤ contraction d k := by
  simp only [contraction]
  positivity

private theorem contraction_lt_one (d k : ℕ) : contraction d k < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < (d + 1 : ℝ) ^ k)).2
  exact_mod_cast Nat.sub_lt (by positivity : 0 < (d + 1) ^ k) (by omega : 0 < d * k + 1)

private theorem contraction_fixedPoint (d k : ℕ) :
    1 / ((d + 1 : ℝ) ^ k) +
        contraction d k * (1 / (d * k + 1 : ℝ)) =
      1 / (d * k + 1 : ℝ) := by
  have hmQ := modulus_le_cubeBlockCard d k
  simp only [contraction, Nat.cast_sub hmQ, Nat.cast_pow, Nat.cast_add,
    Nat.cast_mul, Nat.cast_one]
  have hQ : (d + 1 : ℝ) ^ k ≠ 0 := by positivity
  have hm : (d * k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem density_add_le (n d k : ℕ) :
    density (k + n) d k ≤
      1 / ((d + 1 : ℝ) ^ k) + contraction d k * density n d k := by
  have hrec := maxKSeparatedCard_add_le n d k
  have hrecReal : (maxKSeparatedCard (k + n) d k : ℝ) ≤
      ((d + 1 : ℝ) ^ n) +
        (((d + 1) ^ k - (d * k + 1) : ℕ) : ℝ) *
          maxKSeparatedCard n d k := by
    exact_mod_cast hrec
  unfold density contraction
  rw [pow_add]
  calc
    (maxKSeparatedCard (k + n) d k : ℝ) /
          ((d + 1 : ℝ) ^ k * (d + 1 : ℝ) ^ n) ≤
        (((d + 1 : ℝ) ^ n) +
            (((d + 1) ^ k - (d * k + 1) : ℕ) : ℝ) *
              maxKSeparatedCard n d k) /
          ((d + 1 : ℝ) ^ k * (d + 1 : ℝ) ^ n) := by
      exact div_le_div_of_nonneg_right hrecReal (by positivity)
    _ = 1 / ((d + 1 : ℝ) ^ k) +
          ((↑((d + 1) ^ k - (d * k + 1)) : ℝ) / (d + 1 : ℝ) ^ k) *
            ((maxKSeparatedCard n d k : ℝ) / (d + 1 : ℝ) ^ n) := by
      field_simp

private theorem fixedPoint_le_density (n d k : ℕ) :
    1 / (d * k + 1 : ℝ) ≤ density n d k := by
  have hlower := cube_card_le_modulus_mul_maxKSeparatedCard n d k
  have hlowerReal : ((d + 1 : ℝ) ^ n) ≤
      (d * k + 1 : ℝ) * maxKSeparatedCard n d k := by
    exact_mod_cast hlower
  unfold density
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < d * k + 1)
    (by positivity : (0 : ℝ) < (d + 1 : ℝ) ^ n)).2
  simpa only [one_mul, mul_comm] using hlowerReal

private theorem density_le_one (n d k : ℕ) : density n d k ≤ 1 := by
  have hupper := maxKSeparatedCard_le_univ_card n d k
  rw [card_cube] at hupper
  have hupperReal : (maxKSeparatedCard n d k : ℝ) ≤ (d + 1 : ℝ) ^ n := by
    exact_mod_cast hupper
  unfold density
  exact (div_le_one (by positivity : (0 : ℝ) < (d + 1 : ℝ) ^ n)).2 hupperReal

private theorem density_subsequence_le (r t d k : ℕ) :
    density (r + t * k) d k ≤
      1 / (d * k + 1 : ℝ) + (contraction d k) ^ t := by
  induction t with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero, pow_zero]
      apply (density_le_one r d k).trans
      have hnonneg : (0 : ℝ) ≤ 1 / (d * k + 1 : ℝ) := by positivity
      linarith
  | succ t ih =>
      rw [show r + (t + 1) * k = k + (r + t * k) by ring]
      calc
        density (k + (r + t * k)) d k ≤
            1 / ((d + 1 : ℝ) ^ k) +
              contraction d k * density (r + t * k) d k :=
          density_add_le (r + t * k) d k
        _ ≤ 1 / ((d + 1 : ℝ) ^ k) +
              contraction d k *
                (1 / (d * k + 1 : ℝ) + (contraction d k) ^ t) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ih (contraction_nonneg d k))
        _ = (1 / ((d + 1 : ℝ) ^ k) +
              contraction d k * (1 / (d * k + 1 : ℝ))) +
              (contraction d k) ^ (t + 1) := by
          rw [pow_succ]
          ring
        _ = 1 / (d * k + 1 : ℝ) + (contraction d k) ^ (t + 1) := by
          rw [contraction_fixedPoint]

private theorem density_le_fixedPoint_add_contraction_pow_div
    (n d k : ℕ) (_hk : 0 < k) :
    density n d k ≤
      1 / (d * k + 1 : ℝ) + (contraction d k) ^ (n / k) := by
  have h := density_subsequence_le (n % k) (n / k) d k
  rw [show n % k + (n / k) * k = n by
    simpa only [Nat.mul_comm] using Nat.mod_add_div n k] at h
  exact h

/-- For fixed positive `d` and `k`, the density of a largest `k`-separated
family tends to `1 / (d * k + 1)`, formalising the unnumbered asymptotic
claim in the conclusion of the paper. -/
theorem maxKSeparatedCard_density_tendsto
    (d k : ℕ) (_hd : 0 < d) (hk : 0 < k) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (maxKSeparatedCard n d k : ℝ) /
          (((d + 1 : ℕ) : ℝ) ^ n))
      Filter.atTop
      (nhds (((d * k + 1 : ℕ) : ℝ)⁻¹)) := by
  have hpow : Tendsto (fun n : ℕ ↦ (contraction d k) ^ (n / k)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (contraction_nonneg d k)
      (contraction_lt_one d k)).comp (Nat.tendsto_div_const_atTop hk.ne')
  have hupper : Tendsto
      (fun n : ℕ ↦ 1 / (d * k + 1 : ℝ) + (contraction d k) ^ (n / k))
      atTop (nhds (1 / (d * k + 1 : ℝ))) := by
    simpa using tendsto_const_nhds.add hpow
  have hdensity : Tendsto (fun n ↦ density n d k) atTop
      (nhds (1 / (d * k + 1 : ℝ))) := by
    apply Tendsto.squeeze tendsto_const_nhds hupper
    · exact fun n ↦ fixedPoint_le_density n d k
    · exact fun n ↦ density_le_fixedPoint_add_contraction_pow_div n d k hk
  simpa only [density, Nat.cast_add, Nat.cast_mul, Nat.cast_one, one_div] using hdensity

end

end Asymptotics
end WeightedChains
