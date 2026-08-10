import WeightedChains.DTwoChains

/-!
# Existence of basic ternary chains

This file turns the numerical condition used throughout Section 5 into an
explicit finite basic-chain descriptor.  In particular, every lower-half
vertex starts a basic good chain: an outer vertex starts one of width `k`,
while an inner vertex starts the symmetric chain reaching the reflected type.
-/

set_option autoImplicit false

noncomputable section

namespace WeightedChains
namespace Ternary
namespace BasicChain

variable {n : ℕ}

/-- Enumerate `w` distinct zero coordinates of `x`. -/
def zeroCoordinateEmbedding (x : Cube n 2) (w : ℕ) (hw : w ≤ zeroCount x) :
    Fin w ↪ Fin n := by
  let zeros := zeroCoordinates x
  have hw' : w ≤ zeros.card := by simpa [zeros] using hw
  let enumerate : Fin zeros.card ≃ ↑zeros :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe zeros)).symm
  exact (Fin.castLEEmb hw').trans
    (enumerate.toEmbedding.trans (Function.Embedding.subtype _))

@[simp]
theorem zeroCoordinateEmbedding_mem (x : Cube n 2) (w : ℕ)
    (hw : w ≤ zeroCount x) (i : Fin w) :
    zeroCoordinateEmbedding x w hw i ∈ zeroCoordinates x := by
  simp [zeroCoordinateEmbedding]

theorem zeroCoordinateEmbedding_start (x : Cube n 2) (w : ℕ)
    (hw : w ≤ zeroCount x) (i : Fin w) :
    x (zeroCoordinateEmbedding x w hw i) = 0 := by
  simpa [zeroCoordinates] using zeroCoordinateEmbedding_mem x w hw i

theorem zeroCount_le_dimension (x : Cube n 2) : zeroCount x ≤ n := by
  have h := zeroCount_add_oneCount_add_twoCount x
  omega

/-- The canonical basic chain which starts at `x` and changes the first `w`
zero coordinates supplied by `zeroCoordinateEmbedding`. -/
def ofStartWidth (x : Cube n 2) (w : ℕ) (hw : w ≤ zeroCount x) : BasicChain n where
  width := ⟨w, Nat.lt_succ_of_le (hw.trans (zeroCount_le_dimension x))⟩
  start := x
  coordinate := zeroCoordinateEmbedding x w hw
  start_coordinate := zeroCoordinateEmbedding_start x w hw

@[simp]
theorem ofStartWidth_width (x : Cube n 2) (w : ℕ) (hw : w ≤ zeroCount x) :
    (ofStartWidth x w hw).width = w := rfl

@[simp]
theorem ofStartWidth_start (x : Cube n 2) (w : ℕ) (hw : w ≤ zeroCount x) :
    (ofStartWidth x w hw).start = x := rfl

/-- A basic chain with prescribed start and width exists exactly when there
are enough zero coordinates.  The reverse implication is the descriptor's
intrinsic `width_le_zeroCount` theorem. -/
theorem exists_start_width_iff (x : Cube n 2) (w : ℕ) :
    (∃ B : BasicChain n, B.start = x ∧ (B.width : ℕ) = w) ↔ w ≤ zeroCount x := by
  constructor
  · rintro ⟨B, rfl, rfl⟩
    exact B.width_le_zeroCount
  · intro hw
    exact ⟨ofStartWidth x w hw, rfl, rfl⟩

/-- If a vertex has at least `k` zero coordinates, it starts a basic good
chain of width `k`. -/
theorem exists_good_width_eq (x : Cube n 2) (k : ℕ) (hk : k ≤ zeroCount x) :
    ∃ B : BasicChain n,
      B.start = x ∧ (B.width : ℕ) = k ∧ B.toChain.Good k := by
  let B := ofStartWidth x k hk
  refine ⟨B, rfl, rfl, ?_⟩
  rw [B.toChain_good_iff]
  exact ⟨le_rfl, Or.inr rfl⟩

/-- A lower-half vertex starts the basic symmetric chain whose width is the
excess of zero coordinates over two coordinates. -/
theorem exists_symmetric_starting_at (x : Cube n 2)
    (hlower : twoCount x ≤ zeroCount x) :
    ∃ B : BasicChain n,
      B.start = x ∧ (B.width : ℕ) = zeroCount x - twoCount x ∧
        B.toChain.Symmetric := by
  have hw : zeroCount x - twoCount x ≤ zeroCount x := Nat.sub_le _ _
  let B := ofStartWidth x (zeroCount x - twoCount x) hw
  refine ⟨B, rfl, rfl, ?_⟩
  rw [B.toChain_symmetric_iff]
  change zeroCount x = twoCount x + (zeroCount x - twoCount x)
  omega

/-- Every lower-half vertex starts a basic good chain.  This is the chain
existence dichotomy used in the proof of Section 5: outer vertices use width
`k`, and inner vertices use their unique symmetric width. -/
theorem exists_good_starting_at_of_lower (x : Cube n 2) (k : ℕ)
    (hlower : twoCount x ≤ zeroCount x) :
    ∃ B : BasicChain n, B.start = x ∧ B.toChain.Good k := by
  by_cases houter : twoCount x + k ≤ zeroCount x
  · obtain ⟨B, hstart, hwidth, hgood⟩ :=
      exists_good_width_eq x k (by omega)
    exact ⟨B, hstart, hgood⟩
  · obtain ⟨B, hstart, hwidth, hsymm⟩ :=
      exists_symmetric_starting_at x hlower
    refine ⟨B, hstart, ?_⟩
    rw [B.toChain_good_iff]
    constructor
    · simpa only [hwidth] using (show zeroCount x - twoCount x ≤ k by omega)
    · exact Or.inl ((B.toChain_symmetric_iff).mp hsymm)

/-- Rank-language version of `exists_good_starting_at_of_lower`. -/
theorem exists_good_starting_at_of_rank_le (x : Cube n 2) (k : ℕ)
    (hlower : Cube.rank x ≤ n) :
    ∃ B : BasicChain n, B.start = x ∧ B.toChain.Good k :=
  exists_good_starting_at_of_lower x k ((rank_le_dimension_iff x).mp hlower)

end BasicChain
end Ternary
end WeightedChains
