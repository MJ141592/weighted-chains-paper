import WeightedChains.ResidueSymmetry
import WeightedChains.Appendices.Cuboid

/-!
# The large-separation appendix

This file formalises Appendix 2 of the paper.  The combinatorial input is the
de Bruijn--Tengbergen--Kruyswijk symmetric-chain decomposition of a product of
finite chains.  We include the standard constructive proof: the product of
two symmetric chains is partitioned into the nested ``hooks'' of its
rectangular grid, and iteration gives a decomposition of every discrete cube.
-/

namespace WeightedChains
namespace LargeK

/-! ## The hook decomposition of a rectangle -/

/-- The hook containing `(i,j)` in a rectangle whose first side is no longer
than its second side. -/
private def hookNumberLE {a b : ℕ} (_hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) : Fin (a + 1) :=
  if h : (p.1 : ℕ) + p.2 ≤ b then
    ⟨p.1, p.1.isLt⟩
  else
    ⟨b - p.2, by
      have hi : (p.1 : ℕ) ≤ a := Nat.le_of_lt_succ p.1.isLt
      have hj : (p.2 : ℕ) ≤ b := Nat.le_of_lt_succ p.2.isLt
      omega⟩

/-- Position of a grid point along its hook. -/
private def hookPositionLE {a b : ℕ} (hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) :
    Fin (a + b - 2 * (hookNumberLE hab p : ℕ) + 1) := by
  let r := (hookNumberLE hab p : ℕ)
  refine ⟨(p.1 : ℕ) + p.2 - r, ?_⟩
  have hi : (p.1 : ℕ) ≤ a := Nat.le_of_lt_succ p.1.isLt
  have hj : (p.2 : ℕ) ≤ b := Nat.le_of_lt_succ p.2.isLt
  by_cases h : (p.1 : ℕ) + p.2 ≤ b
  · have hr : r = p.1 := by simp [r, hookNumberLE, h]
    omega
  · have hr : r = b - p.2 := by simp [r, hookNumberLE, h]
    omega

private theorem hookNumberLE_eq_left {a b : ℕ} (hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) (h : (p.1 : ℕ) + p.2 ≤ b) :
    (hookNumberLE hab p : ℕ) = p.1 := by
  simp [hookNumberLE, h]

private theorem hookNumberLE_eq_right {a b : ℕ} (hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) (h : ¬((p.1 : ℕ) + p.2 ≤ b)) :
    (hookNumberLE hab p : ℕ) = b - p.2 := by
  simp [hookNumberLE, h]

private theorem hookNumberLE_le_rank {a b : ℕ} (hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) :
    (hookNumberLE hab p : ℕ) ≤ (p.1 : ℕ) + p.2 := by
  by_cases h : (p.1 : ℕ) + p.2 ≤ b
  · rw [hookNumberLE_eq_left hab p h]
    omega
  · rw [hookNumberLE_eq_right hab p h]
    have hj : (p.2 : ℕ) ≤ b := Nat.le_of_lt_succ p.2.isLt
    omega

private theorem hookNumberLE_add_position {a b : ℕ} (hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) :
    (hookNumberLE hab p : ℕ) + hookPositionLE hab p = (p.1 : ℕ) + p.2 := by
  unfold hookPositionLE
  exact Nat.add_sub_of_le (hookNumberLE_le_rank hab p)

private def gridHookEncodeLE {a b : ℕ} (hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) :
    Σ r : Fin (a + 1), Fin (a + b - 2 * (r : ℕ) + 1) :=
  ⟨hookNumberLE hab p, hookPositionLE hab p⟩

private theorem gridHookEncodeLE_injective {a b : ℕ} (hab : a ≤ b) :
    Function.Injective (gridHookEncodeLE hab) := by
  intro p q hpq
  have hfirst : (gridHookEncodeLE hab p).1 = (gridHookEncodeLE hab q).1 :=
    (Sigma.ext_iff.mp hpq).1
  have hr : ((gridHookEncodeLE hab p).1 : ℕ) = (gridHookEncodeLE hab q).1 :=
    congrArg Fin.val hfirst
  have hs : ((gridHookEncodeLE hab p).2 : ℕ) = (gridHookEncodeLE hab q).2 :=
    Fin.val_eq_val_of_heq (Sigma.ext_iff.mp hpq).2
  change (hookNumberLE hab p : ℕ) = hookNumberLE hab q at hr
  change (hookPositionLE hab p : ℕ) = hookPositionLE hab q at hs
  have hsum : (p.1 : ℕ) + p.2 = (q.1 : ℕ) + q.2 := by
    have hp := hookNumberLE_add_position hab p
    have hq := hookNumberLE_add_position hab q
    omega
  apply Prod.ext <;> apply Fin.ext
  · by_cases h : (p.1 : ℕ) + p.2 ≤ b
    · have hq : (q.1 : ℕ) + q.2 ≤ b := by omega
      rw [hookNumberLE_eq_left hab p h, hookNumberLE_eq_left hab q hq] at hr
      exact hr
    · have hq : ¬((q.1 : ℕ) + q.2 ≤ b) := by omega
      rw [hookNumberLE_eq_right hab p h, hookNumberLE_eq_right hab q hq] at hr
      omega
  · by_cases h : (p.1 : ℕ) + p.2 ≤ b
    · have hq : (q.1 : ℕ) + q.2 ≤ b := by omega
      rw [hookNumberLE_eq_left hab p h, hookNumberLE_eq_left hab q hq] at hr
      omega
    · have hq : ¬((q.1 : ℕ) + q.2 ≤ b) := by omega
      rw [hookNumberLE_eq_right hab p h, hookNumberLE_eq_right hab q hq] at hr
      have hjp : (p.2 : ℕ) ≤ b := Nat.le_of_lt_succ p.2.isLt
      have hjq : (q.2 : ℕ) ≤ b := Nat.le_of_lt_succ q.2.isLt
      omega

private theorem card_gridHookTarget {a b : ℕ} (hab : a ≤ b) :
    Fintype.card (Σ r : Fin (a + 1), Fin (a + b - 2 * (r : ℕ) + 1)) =
      Fintype.card (Fin (a + 1) × Fin (b + 1)) := by
  simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.card_prod]
  rw [Fin.sum_univ_eq_sum_range (fun r ↦ a + b - 2 * r + 1) (a + 1)]
  have hterm (r : ℕ) (hr : r < a + 1) :
      a + b - 2 * r + 1 = (a + b + 1) - 2 * r := by omega
  apply Eq.trans (Finset.sum_congr rfl fun r hr ↦ hterm r (by simpa using hr))
  rw [Finset.sum_tsub_distrib]
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    have hsum := Finset.sum_range_id_mul_two (a + 1)
    have hsum' : 2 * (∑ r ∈ Finset.range (a + 1), r) = (a + 1) * a := by
      simpa only [Nat.add_sub_cancel, Nat.mul_comm] using hsum
    have hprod : (a + 1) * (a + b + 1) = (a + 1) * (b + 1) + (a + 1) * a := by
      ring
    change (a + 1) * (a + b + 1) -
      2 * (∑ r ∈ Finset.range (a + 1), r) = (a + 1) * (b + 1)
    rw [hprod, hsum', Nat.add_sub_cancel_right]
  · intro r hr
    simp only [Finset.mem_range] at hr
    omega

/-- The standard hook equivalence for an `a` by `b` grid, with `a ≤ b`.
The hook numbered `r` has `a+b-2r+1` points. -/
private noncomputable def gridHookEquivLE {a b : ℕ} (hab : a ≤ b) :
    Fin (a + 1) × Fin (b + 1) ≃
      Σ r : Fin (a + 1), Fin (a + b - 2 * (r : ℕ) + 1) :=
  Equiv.ofBijective (gridHookEncodeLE hab)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨gridHookEncodeLE_injective hab, (card_gridHookTarget hab).symm⟩)

private theorem gridHookEquivLE_rank {a b : ℕ} (hab : a ≤ b)
    (p : Fin (a + 1) × Fin (b + 1)) :
    (p.1 : ℕ) + p.2 =
      (gridHookEquivLE hab p).1 + (gridHookEquivLE hab p).2 := by
  change (p.1 : ℕ) + p.2 =
    (gridHookEncodeLE hab p).1 + (gridHookEncodeLE hab p).2
  exact (hookNumberLE_add_position hab p).symm

private theorem gridHookEquivLE_mono {a b : ℕ} (hab : a ≤ b)
    {p q : Fin (a + 1) × Fin (b + 1)}
    (hchain : (gridHookEquivLE hab p).1 = (gridHookEquivLE hab q).1)
    (hpos : ((gridHookEquivLE hab p).2 : ℕ) ≤ (gridHookEquivLE hab q).2) :
    p ≤ q := by
  change (gridHookEncodeLE hab p).1 = (gridHookEncodeLE hab q).1 at hchain
  change ((gridHookEncodeLE hab p).2 : ℕ) ≤ (gridHookEncodeLE hab q).2 at hpos
  have hr : (hookNumberLE hab p : ℕ) = hookNumberLE hab q := by
    exact congrArg Fin.val hchain
  have hpRank := hookNumberLE_add_position hab p
  have hqRank := hookNumberLE_add_position hab q
  change (hookPositionLE hab p : ℕ) ≤ hookPositionLE hab q at hpos
  have hrank : (p.1 : ℕ) + p.2 ≤ (q.1 : ℕ) + q.2 := by omega
  constructor
  · by_cases hp : (p.1 : ℕ) + p.2 ≤ b
    · rw [hookNumberLE_eq_left hab p hp] at hr
      by_cases hq : (q.1 : ℕ) + q.2 ≤ b
      · rw [hookNumberLE_eq_left hab q hq] at hr
        exact hr.le
      · rw [hookNumberLE_eq_right hab q hq] at hr
        omega
    · have hq : ¬((q.1 : ℕ) + q.2 ≤ b) := by omega
      rw [hookNumberLE_eq_right hab p hp, hookNumberLE_eq_right hab q hq] at hr
      have hjp : (p.2 : ℕ) ≤ b := Nat.le_of_lt_succ p.2.isLt
      have hjq : (q.2 : ℕ) ≤ b := Nat.le_of_lt_succ q.2.isLt
      omega
  · by_cases hp : (p.1 : ℕ) + p.2 ≤ b
    · rw [hookNumberLE_eq_left hab p hp] at hr
      by_cases hq : (q.1 : ℕ) + q.2 ≤ b
      · rw [hookNumberLE_eq_left hab q hq] at hr
        omega
      · rw [hookNumberLE_eq_right hab q hq] at hr
        have hjq : (q.2 : ℕ) ≤ b := Nat.le_of_lt_succ q.2.isLt
        omega
    · have hq : ¬((q.1 : ℕ) + q.2 ≤ b) := by omega
      rw [hookNumberLE_eq_right hab p hp, hookNumberLE_eq_right hab q hq] at hr
      have hjp : (p.2 : ℕ) ≤ b := Nat.le_of_lt_succ p.2.isLt
      have hjq : (q.2 : ℕ) ≤ b := Nat.le_of_lt_succ q.2.isLt
      omega

/-! ## Constructive symmetric-chain decompositions -/

/-- A finite symmetric-chain decomposition, encoded by a chain index and the
position in that chain.  The order condition is stated directly on encoded
points, which is exactly what the Appendix 2 block argument needs. -/
structure RankedSCD (P : Type*) [LE P] (rank : P → ℕ) (totalRank : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  steps : Index → ℕ
  startRank : Index → ℕ
  encode : P ≃ Σ i : Index, Fin (steps i + 1)
  rank_encode : ∀ x, rank x = startRank (encode x).1 + (encode x).2
  symmetric : ∀ i, 2 * startRank i + steps i = totalRank
  mono_vertex : ∀ i {p q : Fin (steps i + 1)}, p ≤ q →
    encode.symm ⟨i, p⟩ ≤ encode.symm ⟨i, q⟩

private noncomputable def gridSCDLE {a b : ℕ} (hab : a ≤ b) :
    RankedSCD (Fin (a + 1) × Fin (b + 1))
      (fun p ↦ (p.1 : ℕ) + p.2) (a + b) where
  Index := Fin (a + 1)
  indexFintype := inferInstance
  steps r := a + b - 2 * (r : ℕ)
  startRank r := r
  encode := gridHookEquivLE hab
  rank_encode := gridHookEquivLE_rank hab
  symmetric := by
    intro r
    have hr : (r : ℕ) ≤ a := Nat.le_of_lt_succ r.isLt
    omega
  mono_vertex := by
    intro i p q hpq
    apply gridHookEquivLE_mono hab
    · have hp := (gridHookEquivLE hab).apply_symm_apply ⟨i, p⟩
      have hq := (gridHookEquivLE hab).apply_symm_apply ⟨i, q⟩
      exact (Sigma.ext_iff.mp hp).1.trans (Sigma.ext_iff.mp hq).1.symm
    · have hp :
          (((gridHookEquivLE hab) ((gridHookEquivLE hab).symm ⟨i, p⟩)).2 : ℕ) = p := by
        simpa only using Fin.val_eq_val_of_heq
          (Sigma.ext_iff.mp ((gridHookEquivLE hab).apply_symm_apply ⟨i, p⟩)).2
      have hq :
          (((gridHookEquivLE hab) ((gridHookEquivLE hab).symm ⟨i, q⟩)).2 : ℕ) = q := by
        simpa only using Fin.val_eq_val_of_heq
          (Sigma.ext_iff.mp ((gridHookEquivLE hab).apply_symm_apply ⟨i, q⟩)).2
      omega

private def swapGrid {a b : ℕ} :
    Fin (a + 1) × Fin (b + 1) ≃ Fin (b + 1) × Fin (a + 1) :=
  Equiv.prodComm _ _

private noncomputable def gridSCD (a b : ℕ) :
    RankedSCD (Fin (a + 1) × Fin (b + 1))
      (fun p ↦ (p.1 : ℕ) + p.2) (a + b) := by
  by_cases hab : a ≤ b
  · exact gridSCDLE hab
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    let G := gridSCDLE hba
    exact
      { Index := G.Index
        indexFintype := G.indexFintype
        steps := G.steps
        startRank := G.startRank
        encode := swapGrid.trans G.encode
        rank_encode := by
          intro p
          change (p.1 : ℕ) + p.2 =
            G.startRank (G.encode (p.2, p.1)).1 + (G.encode (p.2, p.1)).2
          rw [Nat.add_comm]
          exact G.rank_encode (p.2, p.1)
        symmetric := by
          intro i
          simpa only [Nat.add_comm] using G.symmetric i
        mono_vertex := by
          intro i p q hpq
          have hswapped := G.mono_vertex i hpq
          exact ⟨hswapped.2, hswapped.1⟩ }

private def sigmaPairEquiv {I J : Type*} {A : I → Type*} {B : J → Type*} :
    (Sigma A × Sigma B) ≃ Σ ij : I × J, A ij.1 × B ij.2 where
  toFun z := ⟨(z.1.1, z.2.1), (z.1.2, z.2.2)⟩
  invFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  left_inv := by rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩; rfl
  right_inv := by rintro ⟨⟨i, j⟩, ⟨x, y⟩⟩; rfl

private noncomputable def productSCDCoreEquiv
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ) :
    P × Q ≃
      Σ z : Σ ij : S.Index × T.Index,
        (gridSCD (S.steps ij.1) (T.steps ij.2)).Index,
        Fin ((gridSCD (S.steps z.1.1) (T.steps z.1.2)).steps z.2 + 1) :=
  (S.encode.prodCongr T.encode).trans sigmaPairEquiv |>.trans
    (Equiv.sigmaCongrRight fun ij ↦ (gridSCD (S.steps ij.1) (T.steps ij.2)).encode) |>.trans
    (Equiv.sigmaAssoc fun (ij : S.Index × T.Index)
      (r : (gridSCD (S.steps ij.1) (T.steps ij.2)).Index) ↦
      Fin ((gridSCD (S.steps ij.1) (T.steps ij.2)).steps r + 1)).symm

private theorem productSCDCoreEquiv_apply
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (z : P × Q) :
    productSCDCoreEquiv S T z =
      ⟨⟨((S.encode z.1).1, (T.encode z.2).1),
        ((gridSCD (S.steps (S.encode z.1).1) (T.steps (T.encode z.2).1)).encode
          ((S.encode z.1).2, (T.encode z.2).2)).1⟩,
       ((gridSCD (S.steps (S.encode z.1).1) (T.steps (T.encode z.2).1)).encode
          ((S.encode z.1).2, (T.encode z.2).2)).2⟩ := rfl

private noncomputable def productSCD
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ) :
    RankedSCD (P × Q) (fun z ↦ rankP z.1 + rankQ z.2) (NP + NQ) := by
  let G := fun ij : S.Index × T.Index ↦ gridSCD (S.steps ij.1) (T.steps ij.2)
  letI : Fintype S.Index := S.indexFintype
  letI : Fintype T.Index := T.indexFintype
  letI (ij : S.Index × T.Index) : Fintype (G ij).Index := (G ij).indexFintype
  exact
    { Index := Σ ij : S.Index × T.Index, (G ij).Index
      indexFintype := inferInstance
      steps z := (G z.1).steps z.2
      startRank z := S.startRank z.1.1 + T.startRank z.1.2 + (G z.1).startRank z.2
      encode := productSCDCoreEquiv S T
      rank_encode := by
        intro z
        let sx := S.encode z.1
        let ty := T.encode z.2
        let gz := (G (sx.1, ty.1)).encode (sx.2, ty.2)
        rw [productSCDCoreEquiv_apply]
        change rankP z.1 + rankQ z.2 =
          S.startRank sx.1 + T.startRank ty.1 +
            (G (sx.1, ty.1)).startRank gz.1 + gz.2
        have hs := S.rank_encode z.1
        have ht := T.rank_encode z.2
        have hg := (G (sx.1, ty.1)).rank_encode (sx.2, ty.2)
        dsimp only [sx, ty, gz] at *
        omega
      symmetric := by
        rintro ⟨⟨i, j⟩, r⟩
        have hs := S.symmetric i
        have ht := T.symmetric j
        have hg := (G (i, j)).symmetric r
        dsimp only [G] at hg ⊢
        omega
      mono_vertex := by
        rintro ⟨⟨i, j⟩, r⟩ p q hpq
        let gp := (G (i, j)).encode.symm ⟨r, p⟩
        let gq := (G (i, j)).encode.symm ⟨r, q⟩
        have hlocal : gp ≤ gq := (G (i, j)).mono_vertex r hpq
        change (S.encode.symm ⟨i, gp.1⟩, T.encode.symm ⟨j, gp.2⟩) ≤
          (S.encode.symm ⟨i, gq.1⟩, T.encode.symm ⟨j, gq.2⟩)
        exact ⟨S.mono_vertex i hlocal.1, T.mono_vertex j hlocal.2⟩ }

private def finChainEquiv (d : ℕ) :
    Fin (d + 1) ≃ Σ _i : PUnit, Fin (d + 1) where
  toFun x := ⟨PUnit.unit, x⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨⟩, x⟩; rfl

private def finChainSCD (d : ℕ) : RankedSCD (Fin (d + 1)) Fin.val d where
  Index := PUnit
  indexFintype := inferInstance
  steps _ := d
  startRank _ := 0
  encode := finChainEquiv d
  rank_encode _ := by simp [finChainEquiv]
  symmetric _ := by simp
  mono_vertex := by
    intro _ p q hpq
    simpa [finChainEquiv] using hpq

private noncomputable def RankedSCD.pullback
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ} {N : ℕ}
    (S : RankedSCD Q rankQ N) (e : P ≃ Q)
    (hrank : ∀ x, rankP x = rankQ (e x))
    (horder : ∀ {x y : P}, e x ≤ e y → x ≤ y) : RankedSCD P rankP N where
  Index := S.Index
  indexFintype := S.indexFintype
  steps := S.steps
  startRank := S.startRank
  encode := e.trans S.encode
  rank_encode x := by
    rw [hrank]
    exact S.rank_encode (e x)
  symmetric := S.symmetric
  mono_vertex := by
    intro i p q hpq
    apply horder
    change e (e.symm (S.encode.symm ⟨i, p⟩)) ≤
      e (e.symm (S.encode.symm ⟨i, q⟩))
    simpa only [Equiv.apply_symm_apply] using S.mono_vertex i hpq

private def cubeZeroEquiv (d : ℕ) : Cube 0 d ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv f := funext fun i ↦ Fin.elim0 i
  right_inv := by rintro ⟨⟩; rfl

private def punitSCD : RankedSCD PUnit.{1} (fun _ ↦ 0) 0 where
  Index := PUnit
  indexFintype := inferInstance
  steps _ := 0
  startRank _ := 0
  encode :=
    { toFun := fun _ ↦ ⟨PUnit.unit, 0⟩
      invFun := fun _ ↦ PUnit.unit
      left_inv := by rintro ⟨⟩; rfl
      right_inv := by rintro ⟨⟨⟩, p⟩; exact Sigma.ext rfl (Fin.heq_ext_iff rfl |>.2 (by omega)) }
  rank_encode _ := by simp
  symmetric _ := by simp
  mono_vertex := by intro _ _ _ _; trivial

/-- The constructive de Bruijn--Tengbergen--Kruyswijk decomposition of a
power of a finite chain. -/
noncomputable def cubeSCD (n d : ℕ) :
    RankedSCD (Cube n d) Cube.rank (n * d) := by
  induction n with
  | zero =>
      simpa only [Nat.zero_mul] using punitSCD.pullback (cubeZeroEquiv d)
        (fun x ↦ by simp [Cube.rank])
        (fun {x y : Cube 0 d}
          (_h : (cubeZeroEquiv d x : PUnit.{1}) ≤ cubeZeroEquiv d y) i ↦ Fin.elim0 i)
  | succ n ih =>
      let E := Fin.succFunEquiv (Fin (d + 1)) n
      let S := productSCD ih (finChainSCD d)
      have hrank (x : Cube (n + 1) d) :
          Cube.rank x = Cube.rank (E x).1 + ((E x).2 : ℕ) := by
        unfold Cube.rank
        rw [Fin.sum_univ_castSucc]
        rfl
      have horder {x y : Cube (n + 1) d} (hxy : E x ≤ E y) : x ≤ y := by
        intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · exact hxy.2
        · exact hxy.1 j
      simpa only [Nat.succ_mul] using S.pullback E hrank horder

/-! ## The de Bruijn--Tengbergen--Kruyswijk theorem for cuboids -/

private def cuboidZeroEquiv (bounds : Fin 0 → ℕ) : Cuboid bounds ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ i := Fin.elim0 i
  left_inv x := funext fun i ↦ Fin.elim0 i
  right_inv := by rintro ⟨⟩; rfl

/-- Split off the last coordinate of a coordinate-dependent cuboid. -/
private def cuboidSuccEquiv {n : ℕ} (bounds : Fin (n + 1) → ℕ) :
    Cuboid bounds ≃
      Cuboid (fun i : Fin n ↦ bounds i.castSucc) × Fin (bounds (Fin.last n) + 1) where
  toFun x := (fun i ↦ x i.castSucc, x (Fin.last n))
  invFun z i := Fin.lastCases z.2 (fun j ↦ z.1 j) i
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  right_inv z := by
    apply Prod.ext
    · funext i
      simp only [Fin.lastCases_castSucc]
    · simp only [Fin.lastCases_last]

private theorem rank_cuboidSuccEquiv {n : ℕ} (bounds : Fin (n + 1) → ℕ)
    (x : Cuboid bounds) :
    Cuboid.rank x =
      Cuboid.rank (cuboidSuccEquiv bounds x).1 +
        ((cuboidSuccEquiv bounds x).2 : ℕ) := by
  unfold Cuboid.rank
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem cuboidSuccEquiv_order {n : ℕ} (bounds : Fin (n + 1) → ℕ)
    {x y : Cuboid bounds} (hxy : cuboidSuccEquiv bounds x ≤ cuboidSuccEquiv bounds y) :
    x ≤ y := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact hxy.2
  · exact hxy.1 j

/-- The constructive symmetric-chain decomposition of an arbitrary finite
cuboid. It is obtained by iterating the two-chain hook construction above. -/
noncomputable def cuboidSCD : {n : ℕ} → (bounds : Fin n → ℕ) →
    RankedSCD (Cuboid bounds) Cuboid.rank (Cuboid.totalRank bounds)
  | 0, bounds =>
      punitSCD.pullback (cuboidZeroEquiv bounds)
        (fun x ↦ by simp [Cuboid.rank])
        (fun {x y : Cuboid bounds}
          (_h : (cuboidZeroEquiv bounds x : PUnit.{1}) ≤ cuboidZeroEquiv bounds y)
          i ↦ Fin.elim0 i)
  | n + 1, bounds => by
      let initBounds := fun i : Fin n ↦ bounds i.castSucc
      let E := cuboidSuccEquiv bounds
      let S := productSCD (cuboidSCD initBounds) (finChainSCD (bounds (Fin.last n)))
      have hrank (x : Cuboid bounds) :
          Cuboid.rank x =
            Cuboid.rank (E x).1 + ((E x).2 : ℕ) :=
        rank_cuboidSuccEquiv bounds x
      have horder {x y : Cuboid bounds} (hxy : E x ≤ E y) : x ≤ y :=
        cuboidSuccEquiv_order bounds hxy
      simpa only [Cuboid.totalRank, Fin.sum_univ_castSucc] using
        S.pullback E hrank horder

/-- **de Bruijn--Tengbergen--Kruyswijk.** Every finite product of finite
chains has a symmetric-chain decomposition. The witness is the constructive
decomposition `cuboidSCD` above. -/
theorem deBruijnTengbergenKruyswijk {n : ℕ} (bounds : Fin n → ℕ) :
    Nonempty (RankedSCD (Cuboid bounds) Cuboid.rank (Cuboid.totalRank bounds)) :=
  ⟨cuboidSCD bounds⟩

/-! ## The middle layer in the large-`k` range -/

private theorem modEq_eq_of_lt_add {x r M : ℕ} (hrM : r < M)
    (hx : x < r + M) (hmod : x ≡ r [MOD M]) : x = r := by
  rcases lt_trichotomy x r with hxr | hxr | hrx
  · have hdvd : M ∣ r - x := hmod.dvd'
    have hpos : 0 < r - x := Nat.sub_pos_of_lt hxr
    have hlower : M ≤ r - x := Nat.le_of_dvd hpos hdvd
    omega
  · exact hxr
  · have hdvd : M ∣ x - r := hmod.symm.dvd'
    have hpos : 0 < x - r := Nat.sub_pos_of_lt hrx
    have hlower : M ≤ x - r := Nat.le_of_dvd hpos hdvd
    omega

/-- In the Appendix 2 range, the lower residue family is just the lower
middle layer: the next congruent rank already lies above the cube. -/
theorem lowerResidueFinset_eq_middleLayer
    (n d k : ℕ) (hnk : n ≤ 2 * k) :
    Cube.lowerResidueFinset n d k =
      Finset.univ.filter fun x : Cube n d ↦
        Cube.rank x = Cube.lowerMiddleRank n d := by
  ext x
  simp only [Cube.lowerResidueFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hmod
    have hmul : n * d ≤ 2 * (d * k) := by
      have := Nat.mul_le_mul_right d hnk
      nlinarith
    apply modEq_eq_of_lt_add (M := d * k + 1)
    · unfold Cube.lowerMiddleRank
      omega
    · have hrank := Cube.rank_le x
      unfold Cube.lowerMiddleRank
      omega
    · exact hmod
  · intro h
    exact h.symm ▸ Nat.ModEq.rfl

private def centralPairFinset (a b : ℕ) :
    Finset (Fin (a + 1) × Fin (b + 1)) :=
  Finset.univ.filter fun p ↦ (p.1 : ℕ) + p.2 = (a + b) / 2

private theorem card_centralPairFinset (a b : ℕ) :
    (centralPairFinset a b).card = min a b + 1 := by
  classical
  by_cases hab : a ≤ b
  · have hmidLower : a ≤ (a + b) / 2 := by omega
    have hmidUpper : (a + b) / 2 ≤ b := by omega
    let forward : Fin (a + 1) → centralPairFinset a b := fun i ↦
      ⟨(i, ⟨(a + b) / 2 - i, by omega⟩), by
        simp only [centralPairFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩
    have hforward : Function.Injective forward := by
      intro i j hij
      exact Fin.ext (congrArg (fun p ↦ (p.1.1 : ℕ)) hij)
    let backward : centralPairFinset a b → Fin (a + 1) := fun p ↦ p.1.1
    have hbackward : Function.Injective backward := by
      intro p q hpq
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.ext (congrArg Fin.val hpq)
      · apply Fin.ext
        have hp := p.2
        have hq := q.2
        simp only [centralPairFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        have hfirst : (p.1.1 : ℕ) = q.1.1 := congrArg Fin.val hpq
        omega
    have hlower := Fintype.card_le_of_injective forward hforward
    have hupper := Fintype.card_le_of_injective backward hbackward
    rw [Fintype.card_fin, Fintype.card_coe] at hlower hupper
    rw [min_eq_left hab]
    omega
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    have hmidLower : b ≤ (a + b) / 2 := by omega
    have hmidUpper : (a + b) / 2 ≤ a := by omega
    let forward : Fin (b + 1) → centralPairFinset a b := fun j ↦
      ⟨(⟨(a + b) / 2 - j, by omega⟩, j), by
        simp only [centralPairFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        omega⟩
    have hforward : Function.Injective forward := by
      intro i j hij
      exact Fin.ext (congrArg (fun p ↦ (p.1.2 : ℕ)) hij)
    let backward : centralPairFinset a b → Fin (b + 1) := fun p ↦ p.1.2
    have hbackward : Function.Injective backward := by
      intro p q hpq
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        have hp := p.2
        have hq := q.2
        simp only [centralPairFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        have hsecond : (p.1.2 : ℕ) = q.1.2 := congrArg Fin.val hpq
        omega
      · exact Fin.ext (congrArg Fin.val hpq)
    have hlower := Fintype.card_le_of_injective forward hforward
    have hupper := Fintype.card_le_of_injective backward hbackward
    rw [Fintype.card_fin, Fintype.card_coe] at hlower hupper
    rw [min_eq_right hba]
    omega

/-! ## Counting chain blocks -/

private def chainPair
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (z : P × Q) : S.Index × T.Index :=
  ((S.encode z.1).1, (T.encode z.2).1)

private noncomputable def blockFiber
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q)) (ij : S.Index × T.Index) : Finset (P × Q) := by
  classical
  exact candidate.filter fun z ↦ chainPair S T z = ij

private noncomputable def blockLeftPosition
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q)) (ij : S.Index × T.Index)
    (z : blockFiber S T candidate ij) : Fin (S.steps ij.1 + 1) := by
  have hdata : z.1 ∈ candidate ∧ chainPair S T z.1 = ij := by
    simpa [blockFiber] using z.2
  have hpair := hdata.2
  have hi : (S.encode z.1.1).1 = ij.1 := congrArg Prod.fst hpair
  exact Fin.cast (congrArg (fun i ↦ S.steps i + 1) hi) (S.encode z.1.1).2

private noncomputable def blockRightPosition
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q)) (ij : S.Index × T.Index)
    (z : blockFiber S T candidate ij) : Fin (T.steps ij.2 + 1) := by
  have hdata : z.1 ∈ candidate ∧ chainPair S T z.1 = ij := by
    simpa [blockFiber] using z.2
  have hpair := hdata.2
  have hi : (T.encode z.1.2).1 = ij.2 := congrArg Prod.snd hpair
  exact Fin.cast (congrArg (fun i ↦ T.steps i + 1) hi) (T.encode z.1.2).2

private theorem blockLeftPosition_injective
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q))
    (hleft : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.1 = y.1 → x = y)
    (ij : S.Index × T.Index) :
    Function.Injective (blockLeftPosition S T candidate ij) := by
  intro x y hxy
  apply Subtype.ext
  have hxmem : x.1 ∈ candidate ∧ chainPair S T x.1 = ij := by
    simpa [blockFiber] using x.2
  have hymem : y.1 ∈ candidate ∧ chainPair S T y.1 = ij := by
    simpa [blockFiber] using y.2
  have hxidx : (S.encode x.1.1).1 = ij.1 := congrArg Prod.fst hxmem.2
  have hyidx : (S.encode y.1.1).1 = ij.1 := congrArg Prod.fst hymem.2
  have hbase : (S.encode x.1.1).1 = (S.encode y.1.1).1 := hxidx.trans hyidx.symm
  have hpos : ((S.encode x.1.1).2 : ℕ) = (S.encode y.1.1).2 := by
    have := congrArg Fin.val hxy
    simpa only [blockLeftPosition, Fin.val_cast] using this
  have hfirst : x.1.1 = y.1.1 := by
    apply S.encode.injective
    apply Sigma.ext hbase
    exact (Fin.heq_ext_iff (congrArg (fun i ↦ S.steps i + 1) hbase)).2 hpos
  apply hleft hxmem.1 hymem.1
  · exact hxmem.2.trans hymem.2.symm
  · exact hfirst

private theorem blockRightPosition_injective
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q))
    (hright : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.2 = y.2 → x = y)
    (ij : S.Index × T.Index) :
    Function.Injective (blockRightPosition S T candidate ij) := by
  intro x y hxy
  apply Subtype.ext
  have hxmem : x.1 ∈ candidate ∧ chainPair S T x.1 = ij := by
    simpa [blockFiber] using x.2
  have hymem : y.1 ∈ candidate ∧ chainPair S T y.1 = ij := by
    simpa [blockFiber] using y.2
  have hxidx : (T.encode x.1.2).1 = ij.2 := congrArg Prod.snd hxmem.2
  have hyidx : (T.encode y.1.2).1 = ij.2 := congrArg Prod.snd hymem.2
  have hbase : (T.encode x.1.2).1 = (T.encode y.1.2).1 := hxidx.trans hyidx.symm
  have hpos : ((T.encode x.1.2).2 : ℕ) = (T.encode y.1.2).2 := by
    have := congrArg Fin.val hxy
    simpa only [blockRightPosition, Fin.val_cast] using this
  have hsecond : x.1.2 = y.1.2 := by
    apply T.encode.injective
    apply Sigma.ext hbase
    exact (Fin.heq_ext_iff (congrArg (fun i ↦ T.steps i + 1) hbase)).2 hpos
  apply hright hxmem.1 hymem.1
  · exact hxmem.2.trans hymem.2.symm
  · exact hsecond

private theorem card_blockFiber_le_min
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q))
    (hleft : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.1 = y.1 → x = y)
    (hright : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.2 = y.2 → x = y)
    (ij : S.Index × T.Index) :
    (blockFiber S T candidate ij).card ≤ min (S.steps ij.1) (T.steps ij.2) + 1 := by
  have hleftCard := Fintype.card_le_of_injective
    (blockLeftPosition S T candidate ij)
    (blockLeftPosition_injective S T candidate hleft ij)
  have hrightCard := Fintype.card_le_of_injective
    (blockRightPosition S T candidate ij)
    (blockRightPosition_injective S T candidate hright ij)
  rw [Fintype.card_coe, Fintype.card_fin] at hleftCard hrightCard
  omega

private def indexFinset
    {P : Type*} [LE P] {rankP : P → ℕ} {N : ℕ}
    (S : RankedSCD P rankP N) : Finset S.Index :=
  @Finset.univ S.Index S.indexFintype

private def indexPairFinset
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ) :
    Finset (S.Index × T.Index) :=
  (indexFinset S).product (indexFinset T)

private theorem candidate_card_le_blockSum
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q))
    (hleft : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.1 = y.1 → x = y)
    (hright : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.2 = y.2 → x = y) :
    candidate.card ≤ (indexPairFinset S T).sum
      (fun ij ↦ min (S.steps ij.1) (T.steps ij.2) + 1) := by
  classical
  calc
    candidate.card = (indexPairFinset S T).sum
        (fun ij ↦ (blockFiber S T candidate ij).card) := by
      rw [Finset.card_eq_sum_card_fiberwise (s := candidate)
        (t := indexPairFinset S T) (f := chainPair S T) (by
          intro z _hz
          simp [indexPairFinset, indexFinset])]
      rfl
    _ ≤ (indexPairFinset S T).sum
        (fun ij ↦ min (S.steps ij.1) (T.steps ij.2) + 1) := by
      apply Finset.sum_le_sum (s := indexPairFinset S T)
        (f := fun ij ↦ (blockFiber S T candidate ij).card)
        (g := fun ij ↦ min (S.steps ij.1) (T.steps ij.2) + 1)
      intro ij _hij
      exact card_blockFiber_le_min S T candidate hleft hright ij

/-! ## The middle layer has the block-sum cardinality -/

private def RankedSCD.middlePosition
    {P : Type*} [LE P] {rankP : P → ℕ} {N : ℕ}
    (S : RankedSCD P rankP N) (i : S.Index) : Fin (S.steps i + 1) :=
  ⟨N / 2 - S.startRank i, by
    have hsym := S.symmetric i
    omega⟩

theorem RankedSCD.rank_symm_mk
    {P : Type*} [LE P] {rankP : P → ℕ} {N : ℕ}
    (S : RankedSCD P rankP N) (i : S.Index) (p : Fin (S.steps i + 1)) :
    rankP (S.encode.symm ⟨i, p⟩) = S.startRank i + p := by
  have hrank := S.rank_encode (S.encode.symm ⟨i, p⟩)
  have henc := S.encode.apply_symm_apply ⟨i, p⟩
  have hbase : (S.encode (S.encode.symm ⟨i, p⟩)).1 = i := by
    simpa only using (Sigma.ext_iff.mp henc).1
  have hpos : ((S.encode (S.encode.symm ⟨i, p⟩)).2 : ℕ) = p := by
    simpa only using Fin.val_eq_val_of_heq (Sigma.ext_iff.mp henc).2
  have hstart : S.startRank (S.encode (S.encode.symm ⟨i, p⟩)).1 =
      S.startRank i := congrArg S.startRank hbase
  calc
    rankP (S.encode.symm ⟨i, p⟩) =
        S.startRank (S.encode (S.encode.symm ⟨i, p⟩)).1 +
          (S.encode (S.encode.symm ⟨i, p⟩)).2 := hrank
    _ = S.startRank i + p := by omega

private theorem RankedSCD.rank_middleVertex
    {P : Type*} [LE P] {rankP : P → ℕ} {N : ℕ}
    (S : RankedSCD P rankP N) (i : S.Index) :
    rankP (S.encode.symm ⟨i, S.middlePosition i⟩) = N / 2 := by
  rw [S.rank_symm_mk]
  have hsym := S.symmetric i
  change S.startRank i + (N / 2 - S.startRank i) = N / 2
  omega

private noncomputable def RankedSCD.middleLayerEquivIndex
    {P : Type*} [LE P] {rankP : P → ℕ} {N : ℕ}
    (S : RankedSCD P rankP N) : {x : P // rankP x = N / 2} ≃ S.Index where
  toFun x := (S.encode x.1).1
  invFun i := ⟨S.encode.symm ⟨i, S.middlePosition i⟩, S.rank_middleVertex i⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply S.encode.injective
    have hmiddle := x.2
    have hrank := S.rank_encode x.1
    have hsym := S.symmetric (S.encode x.1).1
    have hpos : (S.middlePosition (S.encode x.1).1 : ℕ) = (S.encode x.1).2 := by
      change N / 2 - S.startRank (S.encode x.1).1 = (S.encode x.1).2
      omega
    rw [S.encode.apply_symm_apply]
    apply Sigma.ext (by rfl)
    exact heq_of_eq (Fin.ext hpos)
  right_inv := by
    intro i
    have henc := S.encode.apply_symm_apply ⟨i, S.middlePosition i⟩
    exact (Sigma.ext_iff.mp henc).1

private def middleLayerFinset {P : Type*} [Fintype P]
    (rankP : P → ℕ) (N : ℕ) : Finset P :=
  Finset.univ.filter fun x ↦ rankP x = N / 2

private theorem card_middleLayerFinset_eq_index
    {P : Type*} [Fintype P] [LE P] {rankP : P → ℕ} {N : ℕ}
    (S : RankedSCD P rankP N) :
    (middleLayerFinset rankP N).card = @Fintype.card S.Index S.indexFintype := by
  classical
  let _ : Fintype S.Index := S.indexFintype
  let E : (middleLayerFinset rankP N) ≃ {x : P // rankP x = N / 2} :=
    Equiv.subtypeEquiv (Equiv.refl P) (fun x ↦ by simp [middleLayerFinset])
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (E.trans S.middleLayerEquivIndex)

private theorem gridSCD_index_card (a b : ℕ) :
    @Fintype.card (gridSCD a b).Index (gridSCD a b).indexFintype = min a b + 1 := by
  by_cases hab : a ≤ b
  · simp [gridSCD, hab, gridSCDLE]
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    simp [gridSCD, hab, gridSCDLE, hba]

private theorem productSCD_index_card_eq_blockSum
    {P Q : Type*} [LE P] [LE Q] {rankP : P → ℕ} {rankQ : Q → ℕ}
    {NP NQ : ℕ} (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ) :
    @Fintype.card (productSCD S T).Index (productSCD S T).indexFintype =
      (indexPairFinset S T).sum
        (fun ij ↦ min (S.steps ij.1) (T.steps ij.2) + 1) := by
  classical
  let _ : Fintype S.Index := S.indexFintype
  let _ : Fintype T.Index := T.indexFintype
  let _ (ij : S.Index × T.Index) :
      Fintype (gridSCD (S.steps ij.1) (T.steps ij.2)).Index :=
    (gridSCD (S.steps ij.1) (T.steps ij.2)).indexFintype
  change Fintype.card (Σ ij : S.Index × T.Index,
      (gridSCD (S.steps ij.1) (T.steps ij.2)).Index) = _
  rw [Fintype.card_sigma]
  simp_rw [gridSCD_index_card]
  have hindex : indexPairFinset S T =
      (Finset.univ : Finset (S.Index × T.Index)) := by
    ext ij
    simp [indexPairFinset, indexFinset]
  rw [hindex]

private theorem candidate_card_le_middleLayer
    {P Q : Type*} [Fintype P] [Fintype Q] [LE P] [LE Q]
    {rankP : P → ℕ} {rankQ : Q → ℕ} {NP NQ : ℕ}
    (S : RankedSCD P rankP NP) (T : RankedSCD Q rankQ NQ)
    (candidate : Finset (P × Q))
    (hleft : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.1 = y.1 → x = y)
    (hright : ∀ {x y : P × Q}, x ∈ candidate → y ∈ candidate →
      chainPair S T x = chainPair S T y → x.2 = y.2 → x = y) :
    candidate.card ≤
      (middleLayerFinset (fun z : P × Q ↦ rankP z.1 + rankQ z.2) (NP + NQ)).card := by
  calc
    candidate.card ≤ (indexPairFinset S T).sum
        (fun ij ↦ min (S.steps ij.1) (T.steps ij.2) + 1) :=
      candidate_card_le_blockSum S T candidate hleft hright
    _ = @Fintype.card (productSCD S T).Index (productSCD S T).indexFintype :=
      (productSCD_index_card_eq_blockSum S T).symm
    _ = (middleLayerFinset (fun z : P × Q ↦ rankP z.1 + rankQ z.2)
        (NP + NQ)).card := (card_middleLayerFinset_eq_index (productSCD S T)).symm

theorem RankedSCD.comparable_of_same_chain
    {P : Type*} [LE P] {rankP : P → ℕ} {N : ℕ}
    (S : RankedSCD P rankP N) {x y : P}
    (hchain : (S.encode x).1 = (S.encode y).1) : x ≤ y ∨ y ≤ x := by
  rcases hx : S.encode x with ⟨i, p⟩
  rcases hy : S.encode y with ⟨j, q⟩
  have hij : i = j := by simpa only [hx, hy] using hchain
  subst j
  have hxrepr : S.encode.symm ⟨i, p⟩ = x := by simpa only [hx] using S.encode.symm_apply_apply x
  have hyrepr : S.encode.symm ⟨i, q⟩ = y := by simpa only [hy] using S.encode.symm_apply_apply y
  rcases le_total p q with hpq | hqp
  · exact Or.inl (hxrepr ▸ hyrepr ▸ S.mono_vertex i hpq)
  · exact Or.inr (hyrepr ▸ hxrepr ▸ S.mono_vertex i hqp)

/-! ## Splitting the cube into two coordinate blocks -/

/-- Reindex a cube on `p+q` coordinates as a pair of cubes on `p` and `q`
coordinates. -/
def splitCubeEquiv (p q d : ℕ) :
    Cube (p + q) d ≃ Cube p d × Cube q d :=
  (Equiv.piCongrLeft (fun _ : Fin (p + q) ↦ Fin (d + 1)) finSumFinEquiv).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin p) (Fin q) (Fin (d + 1)))

@[simp]
theorem splitCubeEquiv_apply_left (p q d : ℕ) (x : Cube (p + q) d)
    (i : Fin p) : (splitCubeEquiv p q d x).1 i = x (Fin.castAdd q i) := by
  rfl

@[simp]
theorem splitCubeEquiv_apply_right (p q d : ℕ) (x : Cube (p + q) d)
    (i : Fin q) : (splitCubeEquiv p q d x).2 i = x (Fin.natAdd p i) := by
  rfl

theorem rank_splitCubeEquiv (p q d : ℕ) (x : Cube (p + q) d) :
    Cube.rank x = Cube.rank (splitCubeEquiv p q d x).1 +
      Cube.rank (splitCubeEquiv p q d x).2 := by
  unfold Cube.rank
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [Fintype.sum_sum_type, splitCubeEquiv_apply_left,
    splitCubeEquiv_apply_right, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right]

theorem splitCubeEquiv_le_iff (p q d : ℕ) (x y : Cube (p + q) d) :
    splitCubeEquiv p q d x ≤ splitCubeEquiv p q d y ↔ x ≤ y := by
  constructor
  · intro h i
    rcases hi : finSumFinEquiv.symm i with j | j
    · have hcoord : i = Fin.castAdd q j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (finSumFinEquiv.apply_symm_apply i).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv hi
          _ = Fin.castAdd q j := finSumFinEquiv_apply_left j
      rw [hcoord]
      exact h.1 j
    · have hcoord : i = Fin.natAdd p j := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (finSumFinEquiv.apply_symm_apply i).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv hi
          _ = Fin.natAdd p j := finSumFinEquiv_apply_right j
      rw [hcoord]
      exact h.2 j
  · intro h
    constructor
    · intro i
      exact h (Fin.castAdd q i)
    · intro i
      exact h (Fin.natAdd p i)

/-- If the first blocks agree, every differing coordinate belongs to the
second block. -/
theorem hammingDistance_eq_right_of_left_eq (p q d : ℕ)
    {x y : Cube (p + q) d} (hleft : (splitCubeEquiv p q d x).1 =
      (splitCubeEquiv p q d y).1) :
    Cube.hammingDistance x y =
      Cube.hammingDistance (splitCubeEquiv p q d x).2
        (splitCubeEquiv p q d y).2 := by
  unfold Cube.hammingDistance
  have hdiff : Cube.differingCoordinates x y =
      (Cube.differingCoordinates (splitCubeEquiv p q d x).2
        (splitCubeEquiv p q d y).2).map (Fin.natAddEmb p) := by
    ext i
    simp only [Cube.differingCoordinates, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_map]
    constructor
    · intro hi
      rcases h : finSumFinEquiv.symm i with j | j
      · have hcoord : i = Fin.castAdd q j := by
          calc
            i = finSumFinEquiv (finSumFinEquiv.symm i) :=
              (finSumFinEquiv.apply_symm_apply i).symm
            _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv h
            _ = Fin.castAdd q j := finSumFinEquiv_apply_left j
        rw [hcoord] at hi
        exact False.elim (hi (congrFun hleft j))
      · refine ⟨j, ?_, ?_⟩
        · have hcoord : i = Fin.natAdd p j := by
            calc
              i = finSumFinEquiv (finSumFinEquiv.symm i) :=
                (finSumFinEquiv.apply_symm_apply i).symm
              _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv h
              _ = Fin.natAdd p j := finSumFinEquiv_apply_right j
          rw [hcoord] at hi
          simpa only [splitCubeEquiv_apply_right] using hi
        · apply Fin.ext
          have hcoord : i = Fin.natAdd p j := by
            calc
              i = finSumFinEquiv (finSumFinEquiv.symm i) :=
                (finSumFinEquiv.apply_symm_apply i).symm
              _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv h
              _ = Fin.natAdd p j := finSumFinEquiv_apply_right j
          exact congrArg Fin.val hcoord.symm
    · rintro ⟨j, hj, rfl⟩
      change x (Fin.natAdd p j) ≠ y (Fin.natAdd p j)
      simpa only [splitCubeEquiv_apply_right] using hj
  rw [hdiff, Finset.card_map]

/-- If the first blocks agree, every differing coordinate belongs to the
second block. -/
theorem hammingDistance_le_right_of_left_eq (p q d : ℕ)
    {x y : Cube (p + q) d} (hleft : (splitCubeEquiv p q d x).1 =
      (splitCubeEquiv p q d y).1) : Cube.hammingDistance x y ≤ q := by
  unfold Cube.hammingDistance Cube.differingCoordinates
  let f : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i} → Fin q :=
    fun i ↦
      match h : finSumFinEquiv.symm i.1 with
      | Sum.inl j => by
          exfalso
          have hi := i.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hcoord : i.1 = Fin.castAdd q j := by
            calc
              i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
                (finSumFinEquiv.apply_symm_apply i.1).symm
              _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv h
              _ = Fin.castAdd q j := finSumFinEquiv_apply_left j
          rw [hcoord] at hi
          exact hi (congrFun hleft j)
      | Sum.inr j => j
  have hf_repr
      (i : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i}) :
      Sum.inr (f i) = finSumFinEquiv.symm i.1 := by
    dsimp only [f]
    split
    next j h =>
      have hi := i.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hcoord : i.1 = Fin.castAdd q j := by
        calc
          i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
            (finSumFinEquiv.apply_symm_apply i.1).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv h
          _ = Fin.castAdd q j := finSumFinEquiv_apply_left j
      rw [hcoord] at hi
      exact False.elim (hi (congrFun hleft j))
    next j h => exact h.symm
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply finSumFinEquiv.symm.injective
    rw [← hf_repr i, ← hf_repr j, hij]
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective f hf

/-- If the second blocks agree, every differing coordinate belongs to the
first block. -/
theorem hammingDistance_le_left_of_right_eq (p q d : ℕ)
    {x y : Cube (p + q) d} (hright : (splitCubeEquiv p q d x).2 =
      (splitCubeEquiv p q d y).2) : Cube.hammingDistance x y ≤ p := by
  unfold Cube.hammingDistance Cube.differingCoordinates
  let f : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i} → Fin p :=
    fun i ↦
      match h : finSumFinEquiv.symm i.1 with
      | Sum.inl j => j
      | Sum.inr j => by
          exfalso
          have hi := i.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hcoord : i.1 = Fin.natAdd p j := by
            calc
              i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
                (finSumFinEquiv.apply_symm_apply i.1).symm
              _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv h
              _ = Fin.natAdd p j := finSumFinEquiv_apply_right j
          rw [hcoord] at hi
          exact hi (congrFun hright j)
  have hf_repr
      (i : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i}) :
      Sum.inl (f i) = finSumFinEquiv.symm i.1 := by
    dsimp only [f]
    split
    next j h => exact h.symm
    next j h =>
      have hi := i.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hcoord : i.1 = Fin.natAdd p j := by
        calc
          i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
            (finSumFinEquiv.apply_symm_apply i.1).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv h
          _ = Fin.natAdd p j := finSumFinEquiv_apply_right j
      rw [hcoord] at hi
      exact False.elim (hi (congrFun hright j))
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply finSumFinEquiv.symm.injective
    rw [← hf_repr i, ← hf_repr j, hij]
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective f hf

/-! ## Splitting a cuboid into two coordinate blocks -/

private def leftCuboidBounds {p q : ℕ} (bounds : Fin (p + q) → ℕ) : Fin p → ℕ :=
  fun i ↦ bounds (finSumFinEquiv (Sum.inl i))

private def rightCuboidBounds {p q : ℕ} (bounds : Fin (p + q) → ℕ) : Fin q → ℕ :=
  fun i ↦ bounds (finSumFinEquiv (Sum.inr i))

/-- Reindex an arbitrary cuboid on `p+q` coordinates as the product of its
first `p` and last `q` coordinate cuboids. -/
private def splitCuboidEquiv {p q : ℕ} (bounds : Fin (p + q) → ℕ) :
    Cuboid bounds ≃
      Cuboid (leftCuboidBounds bounds) × Cuboid (rightCuboidBounds bounds) :=
  (Equiv.piCongrLeft (fun i : Fin (p + q) ↦ Fin (bounds i + 1))
      finSumFinEquiv).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun s : Fin p ⊕ Fin q ↦ Fin (bounds (finSumFinEquiv s) + 1)))

@[simp]
private theorem splitCuboidEquiv_apply_left {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) (x : Cuboid bounds) (i : Fin p) :
    (splitCuboidEquiv bounds x).1 i = x (finSumFinEquiv (Sum.inl i)) := by
  rfl

@[simp]
private theorem splitCuboidEquiv_apply_right {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) (x : Cuboid bounds) (i : Fin q) :
    (splitCuboidEquiv bounds x).2 i = x (finSumFinEquiv (Sum.inr i)) := by
  rfl

private theorem rank_splitCuboidEquiv {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) (x : Cuboid bounds) :
    Cuboid.rank x = Cuboid.rank (splitCuboidEquiv bounds x).1 +
      Cuboid.rank (splitCuboidEquiv bounds x).2 := by
  unfold Cuboid.rank
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [Fintype.sum_sum_type, splitCuboidEquiv_apply_left,
    splitCuboidEquiv_apply_right]

private theorem totalRank_splitCuboid {p q : ℕ} (bounds : Fin (p + q) → ℕ) :
    Cuboid.totalRank bounds =
      Cuboid.totalRank (leftCuboidBounds bounds) +
        Cuboid.totalRank (rightCuboidBounds bounds) := by
  unfold Cuboid.totalRank leftCuboidBounds rightCuboidBounds
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [Fintype.sum_sum_type]

private theorem splitCuboidEquiv_le_iff {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) (x y : Cuboid bounds) :
    splitCuboidEquiv bounds x ≤ splitCuboidEquiv bounds y ↔ x ≤ y := by
  constructor
  · intro h i
    rcases hi : finSumFinEquiv.symm i with j | j
    · have hcoord : i = finSumFinEquiv (Sum.inl j) := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (finSumFinEquiv.apply_symm_apply i).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv hi
      rw [hcoord]
      exact h.1 j
    · have hcoord : i = finSumFinEquiv (Sum.inr j) := by
        calc
          i = finSumFinEquiv (finSumFinEquiv.symm i) :=
            (finSumFinEquiv.apply_symm_apply i).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv hi
      rw [hcoord]
      exact h.2 j
  · intro h
    constructor
    · intro i
      exact h (finSumFinEquiv (Sum.inl i))
    · intro i
      exact h (finSumFinEquiv (Sum.inr i))

private theorem cuboid_hammingDistance_le_right_of_left_eq {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) {x y : Cuboid bounds}
    (hleft : (splitCuboidEquiv bounds x).1 = (splitCuboidEquiv bounds y).1) :
    Cuboid.hammingDistance x y ≤ q := by
  unfold Cuboid.hammingDistance Cuboid.differingCoordinates
  let f : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i} → Fin q :=
    fun i ↦
      match h : finSumFinEquiv.symm i.1 with
      | Sum.inl j => by
          exfalso
          have hi := i.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hcoord : i.1 = finSumFinEquiv (Sum.inl j) := by
            calc
              i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
                (finSumFinEquiv.apply_symm_apply i.1).symm
              _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv h
          rw [hcoord] at hi
          exact hi (congrFun hleft j)
      | Sum.inr j => j
  have hf_repr
      (i : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i}) :
      Sum.inr (f i) = finSumFinEquiv.symm i.1 := by
    dsimp only [f]
    split
    next j h =>
      have hi := i.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hcoord : i.1 = finSumFinEquiv (Sum.inl j) := by
        calc
          i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
            (finSumFinEquiv.apply_symm_apply i.1).symm
          _ = finSumFinEquiv (Sum.inl j) := congrArg finSumFinEquiv h
      rw [hcoord] at hi
      exact False.elim (hi (congrFun hleft j))
    next j h => exact h.symm
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply finSumFinEquiv.symm.injective
    rw [← hf_repr i, ← hf_repr j, hij]
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective f hf

private theorem cuboid_hammingDistance_le_left_of_right_eq {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) {x y : Cuboid bounds}
    (hright : (splitCuboidEquiv bounds x).2 = (splitCuboidEquiv bounds y).2) :
    Cuboid.hammingDistance x y ≤ p := by
  unfold Cuboid.hammingDistance Cuboid.differingCoordinates
  let f : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i} → Fin p :=
    fun i ↦
      match h : finSumFinEquiv.symm i.1 with
      | Sum.inl j => j
      | Sum.inr j => by
          exfalso
          have hi := i.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hcoord : i.1 = finSumFinEquiv (Sum.inr j) := by
            calc
              i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
                (finSumFinEquiv.apply_symm_apply i.1).symm
              _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv h
          rw [hcoord] at hi
          exact hi (congrFun hright j)
  have hf_repr
      (i : {i // i ∈ Finset.univ.filter fun i : Fin (p + q) ↦ x i ≠ y i}) :
      Sum.inl (f i) = finSumFinEquiv.symm i.1 := by
    dsimp only [f]
    split
    next j h => exact h.symm
    next j h =>
      have hi := i.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hcoord : i.1 = finSumFinEquiv (Sum.inr j) := by
        calc
          i.1 = finSumFinEquiv (finSumFinEquiv.symm i.1) :=
            (finSumFinEquiv.apply_symm_apply i.1).symm
          _ = finSumFinEquiv (Sum.inr j) := congrArg finSumFinEquiv h
      rw [hcoord] at hi
      exact False.elim (hi (congrFun hright j))
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply finSumFinEquiv.symm.injective
    rw [← hf_repr i, ← hf_repr j, hij]
  rw [← Fintype.card_coe]
  simpa using Fintype.card_le_of_injective f hf

/-! ## The Appendix 2 block argument -/

private theorem card_middleLayer_split (p q d : ℕ) :
    (middleLayerFinset (fun z : Cube p d × Cube q d ↦
        Cube.rank z.1 + Cube.rank z.2) (p * d + q * d)).card =
      (middleLayerFinset (Cube.rank : Cube (p + q) d → ℕ) ((p + q) * d)).card := by
  classical
  let E : (middleLayerFinset (Cube.rank : Cube (p + q) d → ℕ) ((p + q) * d)) ≃
      (middleLayerFinset (fun z : Cube p d × Cube q d ↦
        Cube.rank z.1 + Cube.rank z.2) (p * d + q * d)) :=
    Equiv.subtypeEquiv (splitCubeEquiv p q d) (fun x ↦ by
      simp only [middleLayerFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← rank_splitCubeEquiv, Nat.add_mul])
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact (Fintype.card_congr E).symm

private theorem card_middleLayer_splitCuboid {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) :
    (middleLayerFinset
      (fun z : Cuboid (leftCuboidBounds bounds) × Cuboid (rightCuboidBounds bounds) ↦
        Cuboid.rank z.1 + Cuboid.rank z.2)
      (Cuboid.totalRank (leftCuboidBounds bounds) +
        Cuboid.totalRank (rightCuboidBounds bounds))).card =
      (Cuboid.lowerMiddleLayerFinset bounds).card := by
  classical
  let L : (Cuboid.lowerMiddleLayerFinset bounds) ≃
      {x : Cuboid bounds // Cuboid.rank x = Cuboid.lowerMiddleRank bounds} :=
    Equiv.subtypeEquiv (Equiv.refl (Cuboid bounds)) (fun x ↦ by
      simp [Cuboid.lowerMiddleLayerFinset])
  let M : (middleLayerFinset
      (fun z : Cuboid (leftCuboidBounds bounds) × Cuboid (rightCuboidBounds bounds) ↦
        Cuboid.rank z.1 + Cuboid.rank z.2)
      (Cuboid.totalRank (leftCuboidBounds bounds) +
        Cuboid.totalRank (rightCuboidBounds bounds))) ≃
      {z : Cuboid (leftCuboidBounds bounds) × Cuboid (rightCuboidBounds bounds) //
        Cuboid.rank z.1 + Cuboid.rank z.2 =
          (Cuboid.totalRank (leftCuboidBounds bounds) +
            Cuboid.totalRank (rightCuboidBounds bounds)) / 2} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun z ↦ by
      simp [middleLayerFinset])
  let E : {x : Cuboid bounds //
      Cuboid.rank x = Cuboid.lowerMiddleRank bounds} ≃
      {z : Cuboid (leftCuboidBounds bounds) × Cuboid (rightCuboidBounds bounds) //
        Cuboid.rank z.1 + Cuboid.rank z.2 =
          (Cuboid.totalRank (leftCuboidBounds bounds) +
            Cuboid.totalRank (rightCuboidBounds bounds)) / 2} :=
    Equiv.subtypeEquiv (splitCuboidEquiv bounds) (fun x ↦ by
      unfold Cuboid.lowerMiddleRank
      rw [← rank_splitCuboidEquiv, ← totalRank_splitCuboid])
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (M.trans (E.symm.trans L.symm))

/-- The Appendix 2 estimate after choosing coordinate blocks of sizes `p`
and `q`.  The hypotheses say that either block is small enough for equality
on the other block to contradict `k`-separation. -/
private theorem kSeparated_card_le_middleLayer_add
    (p q d k : ℕ) (hp : p ≤ k) (hq : q ≤ k)
    (candidate : Finset (Cube (p + q) d))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube (p + q) d)) k) :
    candidate.card ≤
      (middleLayerFinset (Cube.rank : Cube (p + q) d → ℕ) ((p + q) * d)).card := by
  classical
  let E := splitCubeEquiv p q d
  let S := cubeSCD p d
  let T := cubeSCD q d
  let splitCandidate : Finset (Cube p d × Cube q d) := candidate.map E.toEmbedding
  have hleft : ∀ {z w : Cube p d × Cube q d},
      z ∈ splitCandidate → w ∈ splitCandidate →
      chainPair S T z = chainPair S T w → z.1 = w.1 → z = w := by
    intro z w hz hw hchain hfirst
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    have hrightChain : (T.encode (E.toEmbedding x).2).1 =
        (T.encode (E.toEmbedding y).2).1 := by
      simpa only [chainPair] using congrArg Prod.snd hchain
    rcases T.comparable_of_same_chain hrightChain with hxy | hyx
    · have hproduct : E x ≤ E y := ⟨hfirst.le, hxy⟩
      have hxy' : x ≤ y := (splitCubeEquiv_le_iff p q d x y).1 hproduct
      by_cases hne : x = y
      · simp only [hne]
      · have hsep := hcandidate hx hy hxy' hne
        have hdist := hammingDistance_le_right_of_left_eq p q d hfirst
        omega
    · have hproduct : E y ≤ E x := ⟨hfirst.symm.le, hyx⟩
      have hyx' : y ≤ x := (splitCubeEquiv_le_iff p q d y x).1 hproduct
      by_cases hne : y = x
      · simp only [hne]
      · have hsep := hcandidate hy hx hyx' hne
        have hdist := hammingDistance_le_right_of_left_eq p q d hfirst.symm
        omega
  have hright : ∀ {z w : Cube p d × Cube q d},
      z ∈ splitCandidate → w ∈ splitCandidate →
      chainPair S T z = chainPair S T w → z.2 = w.2 → z = w := by
    intro z w hz hw hchain hsecond
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    have hleftChain : (S.encode (E.toEmbedding x).1).1 =
        (S.encode (E.toEmbedding y).1).1 := by
      simpa only [chainPair] using congrArg Prod.fst hchain
    rcases S.comparable_of_same_chain hleftChain with hxy | hyx
    · have hproduct : E x ≤ E y := ⟨hxy, hsecond.le⟩
      have hxy' : x ≤ y := (splitCubeEquiv_le_iff p q d x y).1 hproduct
      by_cases hne : x = y
      · simp only [hne]
      · have hsep := hcandidate hx hy hxy' hne
        have hdist := hammingDistance_le_left_of_right_eq p q d hsecond
        omega
    · have hproduct : E y ≤ E x := ⟨hyx, hsecond.symm.le⟩
      have hyx' : y ≤ x := (splitCubeEquiv_le_iff p q d y x).1 hproduct
      by_cases hne : y = x
      · simp only [hne]
      · have hsep := hcandidate hy hx hyx' hne
        have hdist := hammingDistance_le_left_of_right_eq p q d hsecond.symm
        omega
  calc
    candidate.card = splitCandidate.card := by simp [splitCandidate]
    _ ≤ (middleLayerFinset (fun z : Cube p d × Cube q d ↦
        Cube.rank z.1 + Cube.rank z.2) (p * d + q * d)).card :=
      candidate_card_le_middleLayer S T splitCandidate hleft hright
    _ = (middleLayerFinset (Cube.rank : Cube (p + q) d → ℕ) ((p + q) * d)).card :=
      card_middleLayer_split p q d

/-- The Appendix 2 block estimate for an arbitrary cuboid whose coordinates
are divided into blocks of sizes `p` and `q`. -/
theorem cuboid_kSeparated_card_le_lowerMiddleLayer_add {p q : ℕ}
    (bounds : Fin (p + q) → ℕ) (k : ℕ) (hp : p ≤ k) (hq : q ≤ k)
    (candidate : Finset (Cuboid bounds))
    (hcandidate : Cuboid.KSeparated (candidate : Set (Cuboid bounds)) k) :
    candidate.card ≤ (Cuboid.lowerMiddleLayerFinset bounds).card := by
  classical
  let E := splitCuboidEquiv bounds
  let S := cuboidSCD (leftCuboidBounds bounds)
  let T := cuboidSCD (rightCuboidBounds bounds)
  let splitCandidate : Finset
      (Cuboid (leftCuboidBounds bounds) × Cuboid (rightCuboidBounds bounds)) :=
    candidate.map E.toEmbedding
  have hleft : ∀ {z w : Cuboid (leftCuboidBounds bounds) ×
      Cuboid (rightCuboidBounds bounds)},
      z ∈ splitCandidate → w ∈ splitCandidate →
      chainPair S T z = chainPair S T w → z.1 = w.1 → z = w := by
    intro z w hz hw hchain hfirst
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    have hrightChain : (T.encode (E.toEmbedding x).2).1 =
        (T.encode (E.toEmbedding y).2).1 := by
      simpa only [chainPair] using congrArg Prod.snd hchain
    rcases T.comparable_of_same_chain hrightChain with hxy | hyx
    · have hproduct : E x ≤ E y := ⟨hfirst.le, hxy⟩
      have hxy' : x ≤ y := (splitCuboidEquiv_le_iff bounds x y).1 hproduct
      by_cases hne : x = y
      · simp only [hne]
      · have hsep := hcandidate hx hy hxy' hne
        have hdist := cuboid_hammingDistance_le_right_of_left_eq bounds hfirst
        omega
    · have hproduct : E y ≤ E x := ⟨hfirst.symm.le, hyx⟩
      have hyx' : y ≤ x := (splitCuboidEquiv_le_iff bounds y x).1 hproduct
      by_cases hne : y = x
      · simp only [hne]
      · have hsep := hcandidate hy hx hyx' hne
        have hdist := cuboid_hammingDistance_le_right_of_left_eq bounds hfirst.symm
        omega
  have hright : ∀ {z w : Cuboid (leftCuboidBounds bounds) ×
      Cuboid (rightCuboidBounds bounds)},
      z ∈ splitCandidate → w ∈ splitCandidate →
      chainPair S T z = chainPair S T w → z.2 = w.2 → z = w := by
    intro z w hz hw hchain hsecond
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    have hleftChain : (S.encode (E.toEmbedding x).1).1 =
        (S.encode (E.toEmbedding y).1).1 := by
      simpa only [chainPair] using congrArg Prod.fst hchain
    rcases S.comparable_of_same_chain hleftChain with hxy | hyx
    · have hproduct : E x ≤ E y := ⟨hxy, hsecond.le⟩
      have hxy' : x ≤ y := (splitCuboidEquiv_le_iff bounds x y).1 hproduct
      by_cases hne : x = y
      · simp only [hne]
      · have hsep := hcandidate hx hy hxy' hne
        have hdist := cuboid_hammingDistance_le_left_of_right_eq bounds hsecond
        omega
    · have hproduct : E y ≤ E x := ⟨hyx, hsecond.symm.le⟩
      have hyx' : y ≤ x := (splitCuboidEquiv_le_iff bounds y x).1 hproduct
      by_cases hne : y = x
      · simp only [hne]
      · have hsep := hcandidate hy hx hyx' hne
        have hdist := cuboid_hammingDistance_le_left_of_right_eq bounds hsecond.symm
        omega
  calc
    candidate.card = splitCandidate.card := by simp [splitCandidate]
    _ ≤ (middleLayerFinset
        (fun z : Cuboid (leftCuboidBounds bounds) ×
          Cuboid (rightCuboidBounds bounds) ↦ Cuboid.rank z.1 + Cuboid.rank z.2)
        (Cuboid.totalRank (leftCuboidBounds bounds) +
          Cuboid.totalRank (rightCuboidBounds bounds))).card :=
      candidate_card_le_middleLayer S T splitCandidate hleft hright
    _ = (Cuboid.lowerMiddleLayerFinset bounds).card :=
      card_middleLayer_splitCuboid bounds

private theorem kSeparated_card_le_middleLayer_of_add_eq
    (p q n d k : ℕ) (hadd : p + q = n) (hp : p ≤ k) (hq : q ≤ k)
    (candidate : Finset (Cube n d))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k) :
    candidate.card ≤
      (middleLayerFinset (Cube.rank : Cube n d → ℕ) (n * d)).card := by
  subst n
  exact kSeparated_card_le_middleLayer_add p q d k hp hq candidate hcandidate

/-! ## Cardinality and optimality -/

/-- **Appendix 2 (cardinality bound).**  For arbitrary alphabet bound `d`,
if the rational inequality `n / 2 ≤ k ≤ n` from the paper holds, every
`k`-separated family has cardinality at most the lower residue family.

Over natural numbers, the first rational inequality is expressed exactly as
`n ≤ 2 * k`; using Lean's truncated division in `n / 2 ≤ k` would be one
unit too weak when `n` is odd. -/
theorem kSeparated_card_le_lowerResidueFinset
    (n d k : ℕ) (hhalf : n ≤ 2 * k) (_hkn : k ≤ n)
    (candidate : Finset (Cube n d))
    (hcandidate : Cube.KSeparated (candidate : Set (Cube n d)) k) :
    candidate.card ≤ (Cube.lowerResidueFinset n d k).card := by
  rw [lowerResidueFinset_eq_middleLayer n d k hhalf]
  change candidate.card ≤
    (middleLayerFinset (Cube.rank : Cube n d → ℕ) (n * d)).card
  apply kSeparated_card_le_middleLayer_of_add_eq
      (p := n / 2) (q := n - n / 2) (n := n) (d := d) (k := k)
  · omega
  · omega
  · omega
  · exact hcandidate

/-- The finite lower residue family is `k`-separated, for every `n`, `d`, and
`k`. -/
theorem lowerResidueFinset_kSeparated (n d k : ℕ) :
    Cube.KSeparated (Cube.lowerResidueFinset n d k : Set (Cube n d)) k := by
  intro x y hx hy hxy hne
  exact Cube.lowerResidueFamily_kSeparated n d k
    (Cube.mem_lowerResidueFinset_iff.mp hx)
    (Cube.mem_lowerResidueFinset_iff.mp hy) hxy hne

/-- The finite upper residue family is `k`-separated, for every `n`, `d`, and
`k`. -/
theorem upperResidueFinset_kSeparated (n d k : ℕ) :
    Cube.KSeparated (Cube.upperResidueFinset n d k : Set (Cube n d)) k := by
  intro x y hx hy hxy hne
  exact Cube.upperResidueFamily_kSeparated n d k
    (Cube.mem_upperResidueFinset_iff.mp hx)
    (Cube.mem_upperResidueFinset_iff.mp hy) hxy hne

/-- **Appendix 2 (optimality).**  In the range `n / 2 ≤ k ≤ n`, the
lower residue family is a largest `k`-separated family. -/
theorem lowerResidueFinset_isMaximum
    (n d k : ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n) :
    Cube.KSeparated (Cube.lowerResidueFinset n d k : Set (Cube n d)) k ∧
      ∀ candidate : Finset (Cube n d),
        Cube.KSeparated (candidate : Set (Cube n d)) k →
          candidate.card ≤ (Cube.lowerResidueFinset n d k).card := by
  exact ⟨lowerResidueFinset_kSeparated n d k,
    fun candidate hcandidate ↦
      kSeparated_card_le_lowerResidueFinset n d k hhalf hkn candidate hcandidate⟩

/-- **Appendix 2 (symmetric optimality).**  In the same range, the upper
residue family is also a largest `k`-separated family. -/
theorem upperResidueFinset_isMaximum
    (n d k : ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n) :
    Cube.KSeparated (Cube.upperResidueFinset n d k : Set (Cube n d)) k ∧
      ∀ candidate : Finset (Cube n d),
        Cube.KSeparated (candidate : Set (Cube n d)) k →
          candidate.card ≤ (Cube.upperResidueFinset n d k).card := by
  refine ⟨upperResidueFinset_kSeparated n d k, ?_⟩
  intro candidate hcandidate
  rw [← Cube.card_lowerResidueFinset_eq_card_upperResidueFinset]
  exact kSeparated_card_le_lowerResidueFinset
    n d k hhalf hkn candidate hcandidate

/-! ## The cuboid extension -/

private theorem cuboid_kSeparated_card_le_lowerMiddleLayer_of_add_eq
    (p q n k : ℕ) (hadd : p + q = n) (hp : p ≤ k) (hq : q ≤ k)
    (bounds : Fin n → ℕ) (candidate : Finset (Cuboid bounds))
    (hcandidate : Cuboid.KSeparated (candidate : Set (Cuboid bounds)) k) :
    candidate.card ≤ (Cuboid.lowerMiddleLayerFinset bounds).card := by
  subst n
  exact cuboid_kSeparated_card_le_lowerMiddleLayer_add bounds k hp hq
    candidate hcandidate

/-- **Appendix 2 (cuboid cardinality bound).** Let the `n` coordinate bounds
be arbitrary. In the exact large-separation range `n ≤ 2 * k`, every
`k`-separated family in the resulting cuboid has cardinality at most its lower
central layer. -/
theorem cuboid_kSeparated_card_le_lowerMiddleLayer
    (n k : ℕ) (bounds : Fin n → ℕ) (hhalf : n ≤ 2 * k) (_hkn : k ≤ n)
    (candidate : Finset (Cuboid bounds))
    (hcandidate : Cuboid.KSeparated (candidate : Set (Cuboid bounds)) k) :
    candidate.card ≤ (Cuboid.lowerMiddleLayerFinset bounds).card := by
  apply cuboid_kSeparated_card_le_lowerMiddleLayer_of_add_eq
      (p := n / 2) (q := n - n / 2) (n := n) (k := k)
      (bounds := bounds) (candidate := candidate)
  · omega
  · omega
  · omega
  · exact hcandidate

/-- In the large-separation range, the lower central layer is a largest
`k`-separated family in every finite cuboid. -/
theorem cuboid_lowerMiddleLayer_isMaximum
    (n k : ℕ) (bounds : Fin n → ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n) :
    Cuboid.KSeparated
        (Cuboid.lowerMiddleLayerFinset bounds : Set (Cuboid bounds)) k ∧
      ∀ candidate : Finset (Cuboid bounds),
        Cuboid.KSeparated (candidate : Set (Cuboid bounds)) k →
          candidate.card ≤ (Cuboid.lowerMiddleLayerFinset bounds).card := by
  exact ⟨Cuboid.lowerMiddleLayerFinset_kSeparated bounds k,
    fun candidate hcandidate ↦
      cuboid_kSeparated_card_le_lowerMiddleLayer
        n k bounds hhalf hkn candidate hcandidate⟩

/-- By cuboid reflection, the upper central layer is also a largest
`k`-separated family in the same range. -/
theorem cuboid_upperMiddleLayer_isMaximum
    (n k : ℕ) (bounds : Fin n → ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n) :
    Cuboid.KSeparated
        (Cuboid.upperMiddleLayerFinset bounds : Set (Cuboid bounds)) k ∧
      ∀ candidate : Finset (Cuboid bounds),
        Cuboid.KSeparated (candidate : Set (Cuboid bounds)) k →
          candidate.card ≤ (Cuboid.upperMiddleLayerFinset bounds).card := by
  refine ⟨Cuboid.upperMiddleLayerFinset_kSeparated bounds k, ?_⟩
  intro candidate hcandidate
  rw [← Cuboid.card_lowerMiddleLayer_eq_card_upperMiddleLayer]
  exact cuboid_kSeparated_card_le_lowerMiddleLayer
    n k bounds hhalf hkn candidate hcandidate

end LargeK
end WeightedChains
