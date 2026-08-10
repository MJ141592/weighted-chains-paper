import WeightedChains.WeightedUniqueness

/-!
# Outward propagation of uniqueness

This file packages the well-founded induction used in the uniqueness half of
Lemma 3.2.  Agreement is known at distance zero.  At every greater distance,
a reference point is forced in by a block whose other points are already-known
reference nonmembers, while a nonreference point is forced out by a block
containing an already-known reference member.
-/

set_option autoImplicit false

namespace WeightedChains
namespace UniquenessPropagation

variable {α ι : Type*} [DecidableEq α]

/-- Outward propagation along a selected family of exact-one blocks.

`active` abstracts the positive-weight condition: only active blocks need have
exactly one candidate point, and every propagation witness must be active. -/
theorem finset_eq_of_active_exact_one_outward_induction
    (blocks : ι → Finset α) (active : ι → Prop)
    (reference candidate : Finset α) (distance : α → ℕ)
    (hexact : ∀ i, active i → (candidate ∩ blocks i).card = 1)
    (hbase : ∀ x, distance x = 0 → (x ∈ candidate ↔ x ∈ reference))
    (hreference : ∀ x, x ∈ reference → 0 < distance x →
      ∃ i, active i ∧ x ∈ blocks i ∧
        ∀ y ∈ blocks i, y ≠ x → distance y < distance x ∧ y ∉ reference)
    (hnonreference : ∀ x, x ∉ reference → 0 < distance x →
      ∃ i, active i ∧ x ∈ blocks i ∧
        ∃ y ∈ blocks i, y ∈ reference ∧ distance y < distance x) :
    candidate = reference := by
  have hagree : ∀ m : ℕ, ∀ x : α, distance x = m →
      (x ∈ candidate ↔ x ∈ reference) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hxDistance
      by_cases hm : m = 0
      · apply hbase
        omega
      · have hxPositive : 0 < distance x := by omega
        by_cases hxReference : x ∈ reference
        · simp only [hxReference, iff_true]
          obtain ⟨i, hiActive, hxBlock, hother⟩ :=
            hreference x hxReference hxPositive
          refine (WeightedCover.mem_iff_other_points_not_mem_of_inter_card_eq_one
            (hexact i hiActive) hxBlock).mpr ?_
          intro y hyBlock hyx
          obtain ⟨hyDistance, hyReference⟩ := hother y hyBlock hyx
          have hyAgree : y ∈ candidate ↔ y ∈ reference := by
            apply ih (distance y)
            · omega
            · rfl
          intro hyCandidate
          exact hyReference (hyAgree.mp hyCandidate)
        · simp only [hxReference, iff_false]
          obtain ⟨i, hiActive, hxBlock, y, hyBlock, hyReference, hyDistance⟩ :=
            hnonreference x hxReference hxPositive
          have hyAgree : y ∈ candidate ↔ y ∈ reference := by
            apply ih (distance y)
            · omega
            · rfl
          have hyCandidate : y ∈ candidate := hyAgree.mpr hyReference
          have hxy : x ≠ y := by
            intro hxy
            subst y
            omega
          exact WeightedCover.not_mem_of_mem_of_inter_card_eq_one
            (hexact i hiActive) hyCandidate hyBlock hxBlock hxy
  apply Finset.ext
  intro x
  exact hagree (distance x) x rfl

/-- The same propagation theorem when every supplied block is exact-one. -/
theorem finset_eq_of_exact_one_outward_induction
    (blocks : ι → Finset α) (reference candidate : Finset α) (distance : α → ℕ)
    (hexact : ∀ i, (candidate ∩ blocks i).card = 1)
    (hbase : ∀ x, distance x = 0 → (x ∈ candidate ↔ x ∈ reference))
    (hreference : ∀ x, x ∈ reference → 0 < distance x →
      ∃ i, x ∈ blocks i ∧
        ∀ y ∈ blocks i, y ≠ x → distance y < distance x ∧ y ∉ reference)
    (hnonreference : ∀ x, x ∉ reference → 0 < distance x →
      ∃ i, x ∈ blocks i ∧
        ∃ y ∈ blocks i, y ∈ reference ∧ distance y < distance x) :
    candidate = reference := by
  apply finset_eq_of_active_exact_one_outward_induction blocks (fun _ ↦ True)
    reference candidate distance
  · intro i _hi
    exact hexact i
  · exact hbase
  · intro x hxReference hxPositive
    obtain ⟨i, hxBlock, hother⟩ := hreference x hxReference hxPositive
    exact ⟨i, trivial, hxBlock, hother⟩
  · intro x hxReference hxPositive
    obtain ⟨i, hxBlock, hother⟩ := hnonreference x hxReference hxPositive
    exact ⟨i, trivial, hxBlock, hother⟩

/-- Convenient weighted form: positive-weight blocks are exactly the active
blocks used by the propagation argument. -/
theorem finset_eq_of_positive_weight_outward_induction
    (blocks : ι → Finset α) (weight : ι → ℝ)
    (reference candidate : Finset α) (distance : α → ℕ)
    (hexact : ∀ i, 0 < weight i → (candidate ∩ blocks i).card = 1)
    (hbase : ∀ x, distance x = 0 → (x ∈ candidate ↔ x ∈ reference))
    (hreference : ∀ x, x ∈ reference → 0 < distance x →
      ∃ i, 0 < weight i ∧ x ∈ blocks i ∧
        ∀ y ∈ blocks i, y ≠ x → distance y < distance x ∧ y ∉ reference)
    (hnonreference : ∀ x, x ∉ reference → 0 < distance x →
      ∃ i, 0 < weight i ∧ x ∈ blocks i ∧
        ∃ y ∈ blocks i, y ∈ reference ∧ distance y < distance x) :
    candidate = reference :=
  finset_eq_of_active_exact_one_outward_induction blocks (fun i ↦ 0 < weight i)
    reference candidate distance hexact hbase hreference hnonreference

end UniquenessPropagation
end WeightedChains
