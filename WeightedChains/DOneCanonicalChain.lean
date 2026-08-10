import WeightedChains.DOneChains

/-!
# Canonical witnesses for Boolean rank intervals

For every interval of ranks `[l,l+w]` inside the Boolean cube, this file gives
an explicit represented saturated chain.  These witnesses establish
nonemptiness of the start groups used to distribute the Section 4 weights.
-/

set_option autoImplicit false

namespace WeightedChains
namespace DOne
namespace BooleanChain

/-- Include the first `l` coordinates among `n` coordinates. -/
def initialEmbedding (n l : ℕ) (hl : l ≤ n) : Fin l ↪ Fin n where
  toFun i := ⟨i, lt_of_lt_of_le i.isLt hl⟩
  inj' i j hij := by
    apply Fin.ext
    exact congrArg (fun z : Fin n ↦ z.val) hij

/-- After the first `l` coordinates, enumerate the next `w` coordinates. -/
def intervalAddition (n l w : ℕ) (h : l + w ≤ n) : Fin w ↪ Fin n where
  toFun j := ⟨l + j, by omega⟩
  inj' i j hij := by
    apply Fin.ext
    have := congrArg (fun z : Fin n ↦ z.val) hij
    simp only at this
    omega

/-- An explicit chain whose endpoint ranks are `l` and `l+w`. -/
def intervalChain (n l w : ℕ) (h : l + w ≤ n) : BooleanChain n where
  steps := ⟨w, by omega⟩
  start := Finset.univ.map (initialEmbedding n l (by omega))
  addition := intervalAddition n l w h
  fresh := by
    rw [Finset.disjoint_left]
    intro x hxStart hxAddition
    obtain ⟨i, _hi, hix⟩ := Finset.mem_map.mp hxStart
    obtain ⟨j, _hj, hjx⟩ := Finset.mem_map.mp hxAddition
    have heq : initialEmbedding n l (by omega) i = intervalAddition n l w h j :=
      hix.trans hjx.symm
    have hval := congrArg Fin.val heq
    change (i : ℕ) = l + (j : ℕ) at hval
    omega

@[simp]
theorem intervalChain_steps (n l w : ℕ) (h : l + w ≤ n) :
    (intervalChain n l w h).steps = w := rfl

@[simp]
theorem intervalChain_start_card (n l w : ℕ) (h : l + w ≤ n) :
    (intervalChain n l w h).start.card = l := by
  simp [intervalChain]

@[simp]
theorem intervalChain_first_rank (n l w : ℕ) (h : l + w ≤ n) :
    Cube.rank (intervalChain n l w h).toChain.first = l := by
  simp

@[simp]
theorem intervalChain_last_rank (n l w : ℕ) (h : l + w ≤ n) :
    Cube.rank (intervalChain n l w h).toChain.last = l + w := by
  simp

end BooleanChain
end DOne
end WeightedChains
