import WeightedChains.WeightedUniqueness
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Uniqueness from the connected middle-layer graph

The uniqueness proof in Lemma 3.2 uses the elementary fact that a choice of
exactly one endpoint of every edge of a connected bipartite graph must be one
of its two colour classes.  This file isolates that graph-theoretic argument.
-/

namespace WeightedChains
namespace MiddleLayerUniqueness

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A B left right : Set V}

/-- A set contains exactly one endpoint of every edge of `G`. -/
def EdgeExactlyOne (G : SimpleGraph V) (A : Set V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → (u ∈ A ↔ v ∉ A)

theorem edgeExactlyOne_iff (G : SimpleGraph V) (A : Set V) :
    EdgeExactlyOne G A ↔
      ∀ ⦃u v⦄, G.Adj u v →
        (u ∈ A ∧ v ∉ A) ∨ (u ∉ A ∧ v ∈ A) := by
  constructor
  · intro h u v huv
    have := h huv
    tauto
  · intro h u v huv
    have := h huv
    tauto

theorem EdgeExactlyOne.compl (hA : EdgeExactlyOne G A) :
    EdgeExactlyOne G Aᶜ := by
  intro u v huv
  have h := hA huv
  simp only [Set.mem_compl_iff]
  tauto

/-- Two exact-one choices which agree at the beginning of a walk agree at its
end. -/
theorem agree_at_end_of_walk (hA : EdgeExactlyOne G A) (hB : EdgeExactlyOne G B)
    {u v : V} (p : G.Walk u v) (hu : u ∈ A ↔ u ∈ B) :
    v ∈ A ↔ v ∈ B := by
  induction p with
  | nil => exact hu
  | @cons u w v huw p ih =>
      apply ih
      have hAu := hA huw
      have hBu := hB huw
      tauto

/-- On a connected graph, an exact-one edge choice is determined by its value
at any single vertex. -/
theorem eq_of_agree_at_vertex (hconnected : G.Connected)
    (hA : EdgeExactlyOne G A) (hB : EdgeExactlyOne G B)
    {u : V} (hu : u ∈ A ↔ u ∈ B) :
    A = B := by
  ext v
  obtain ⟨p⟩ := hconnected u v
  exact agree_at_end_of_walk hA hB p hu

/-- A connected graph has exactly two complementary ways to choose one
endpoint of every edge. -/
theorem eq_or_eq_compl (hconnected : G.Connected)
    (hA : EdgeExactlyOne G A) (hB : EdgeExactlyOne G B) :
    A = B ∨ A = Bᶜ := by
  let ⟨u⟩ := hconnected.nonempty
  by_cases hu : u ∈ A ↔ u ∈ B
  · exact Or.inl (eq_of_agree_at_vertex hconnected hA hB hu)
  · right
    refine eq_of_agree_at_vertex (A := A) (B := Bᶜ) hconnected hA hB.compl
      (u := u) ?_
    simp only [Set.mem_compl_iff]
    tauto

/-- Either colour class of a bipartition contains exactly one endpoint of
every edge. -/
theorem bipartite_left_edgeExactlyOne
    (h : G.IsBipartiteWith left right) :
    EdgeExactlyOne G left := by
  intro u v huv
  rcases h.mem_of_adj huv with huv | huv
  · have hv : v ∉ left := Set.disjoint_right.mp h.disjoint huv.2
    simp [huv.1, hv]
  · have hu : u ∉ left := Set.disjoint_right.mp h.disjoint huv.1
    simp [hu, huv.2]

/-- If the two parts cover the vertices, the complement of the left part is
the right part. -/
theorem bipartite_compl_left_eq_right
    (h : G.IsBipartiteWith left right) (hcover : left ∪ right = Set.univ) :
    leftᶜ = right := by
  apply compl_eq_iff_isCompl.mpr
  refine ⟨h.disjoint, ?_⟩
  rw [codisjoint_iff]
  change left ∪ right = Set.univ
  exact hcover

/-- A subset containing exactly one endpoint of every edge of a connected
bipartite graph is one of the two colour classes. -/
theorem eq_left_or_eq_right (hconnected : G.Connected)
    (hbipartite : G.IsBipartiteWith left right)
    (hcover : left ∪ right = Set.univ) (hA : EdgeExactlyOne G A) :
    A = left ∨ A = right := by
  rcases eq_or_eq_compl hconnected hA
      (bipartite_left_edgeExactlyOne hbipartite) with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (bipartite_compl_left_eq_right hbipartite hcover))

section BooleanAdjacentLayers

/-- Vertices in two adjacent layers of the Boolean lattice, represented as
finite subsets of the coordinate set. -/
def AdjacentLayerVertex (n r : ℕ) :=
  {s : Finset (Fin n) // s.card = r ∨ s.card = r + 1}

/-- The lower of the two adjacent Boolean layers. -/
def lowerLayer (n r : ℕ) : Set (AdjacentLayerVertex n r) :=
  {s | s.1.card = r}

/-- The upper of the two adjacent Boolean layers. -/
def upperLayer (n r : ℕ) : Set (AdjacentLayerVertex n r) :=
  {s | s.1.card = r + 1}

private def lowerVertex {n r : ℕ} (s : Finset (Fin n)) (hs : s.card = r) :
    AdjacentLayerVertex n r :=
  ⟨s, Or.inl hs⟩

private def upperVertex {n r : ℕ} (s : Finset (Fin n)) (hs : s.card = r + 1) :
    AdjacentLayerVertex n r :=
  ⟨s, Or.inr hs⟩

/-- The incidence graph between two adjacent layers of the Boolean lattice. -/
def adjacentLayerGraph (n r : ℕ) : SimpleGraph (AdjacentLayerVertex n r) where
  Adj s t := s.1 ⊂ t.1 ∨ t.1 ⊂ s.1
  symm.symm s t := by tauto
  loopless.irrefl s := by
    intro h
    rcases h with h | h <;> exact (ssubset_irrefl _ h)

theorem adjacentLayerGraph_isBipartiteWith (n r : ℕ) :
    (adjacentLayerGraph n r).IsBipartiteWith (lowerLayer n r) (upperLayer n r) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro s hsLower hsUpper
    change s.1.card = r at hsLower
    change s.1.card = r + 1 at hsUpper
    omega
  · intro s t hst
    change s.1 ⊂ t.1 ∨ t.1 ⊂ s.1 at hst
    rcases hst with hst | hts
    · left
      have hcard := Finset.card_lt_card hst
      rcases s.2 with hs | hs <;> rcases t.2 with ht | ht
      · omega
      · exact ⟨hs, ht⟩
      · omega
      · omega
    · right
      have hcard := Finset.card_lt_card hts
      rcases s.2 with hs | hs <;> rcases t.2 with ht | ht
      · omega
      · omega
      · exact ⟨hs, ht⟩
      · omega

theorem lowerLayer_union_upperLayer (n r : ℕ) :
    lowerLayer n r ∪ upperLayer n r = Set.univ := by
  ext s
  change (s.1.card = r ∨ s.1.card = r + 1) ↔ True
  simpa using s.2

private theorem lower_reachable_lower {n r : ℕ}
    (s t : Finset (Fin n)) (hs : s.card = r) (ht : t.card = r) :
    (adjacentLayerGraph n r).Reachable (lowerVertex s hs) (lowerVertex t ht) := by
  classical
  by_cases hst : s = t
  · subst s
    exact .rfl
  have hnotST : ¬s ⊆ t := by
    intro hsub
    exact hst (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hnotTS : ¬t ⊆ s := by
    intro hsub
    exact hst (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨a, ha⟩ := Finset.sdiff_nonempty.mpr hnotST
  have ⟨haS, haT⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨b, hb⟩ := Finset.sdiff_nonempty.mpr hnotTS
  have ⟨hbT, hbS⟩ := Finset.mem_sdiff.mp hb
  let u := insert b s
  have huCard : u.card = r + 1 := by
    simp [u, hbS, hs]
  have haU : a ∈ u := by simp [u, haS]
  let v := u.erase a
  have hvCard : v.card = r := by
    simp [v, Finset.card_erase_of_mem haU, huCard]
  have hsu : (adjacentLayerGraph n r).Adj
      (lowerVertex s hs) (upperVertex u huCard) := by
    left
    exact Finset.ssubset_insert hbS
  have huv : (adjacentLayerGraph n r).Adj
      (upperVertex u huCard) (lowerVertex v hvCard) := by
    right
    exact Finset.erase_ssubset haU
  have hvDiff : v \ t = (s \ t).erase a := by
    ext x
    simp only [v, u, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hxa, hxb | hxs⟩, hxt⟩
      · exact (hxt (hxb ▸ hbT)).elim
      · exact ⟨hxa, hxs, hxt⟩
    · rintro ⟨hxa, hxs, hxt⟩
      exact ⟨⟨hxa, Or.inr hxs⟩, hxt⟩
  have haDiff : a ∈ s \ t := Finset.mem_sdiff.mpr ⟨haS, haT⟩
  have hdecrease : (v \ t).card < (s \ t).card := by
    have hpositive : 0 < (s \ t).card := Finset.card_pos.mpr ⟨a, haDiff⟩
    rw [hvDiff, Finset.card_erase_of_mem haDiff]
    omega
  exact hsu.reachable.trans <| huv.reachable.trans <|
    lower_reachable_lower v t hvCard ht
termination_by (s \ t).card

private theorem reachable_lowerVertex {n r : ℕ} (x : AdjacentLayerVertex n r) :
    ∃ (s : Finset (Fin n)) (hs : s.card = r),
      (adjacentLayerGraph n r).Reachable x (lowerVertex s hs) := by
  classical
  rcases x.2 with hx | hx
  · exact ⟨x.1, hx, .rfl⟩
  · have hxNonempty : x.1.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hxNonempty
    let s := x.1.erase a
    have hs : s.card = r := by
      simp [s, Finset.card_erase_of_mem ha, hx]
    refine ⟨s, hs, ?_⟩
    apply SimpleGraph.Adj.reachable
    right
    exact Finset.erase_ssubset ha

/-- The incidence graph of two adjacent nonempty Boolean layers is connected. -/
theorem adjacentLayerGraph_connected {n r : ℕ} (hr : r ≤ n) :
    (adjacentLayerGraph n r).Connected := by
  classical
  have hcard : r ≤ (Finset.univ : Finset (Fin n)).card := by simpa using hr
  obtain ⟨root, _hrootSubset, hrootCard⟩ := Finset.exists_subset_card_eq hcard
  let rootVertex := lowerVertex root hrootCard
  let _ : Nonempty (AdjacentLayerVertex n r) := ⟨rootVertex⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨sx, hsx, hx⟩ := reachable_lowerVertex x
  obtain ⟨sy, hsy, hy⟩ := reachable_lowerVertex y
  exact hx.trans <| (lower_reachable_lower sx sy hsx hsy).trans hy.symm

/-- Concrete form of the middle-layer uniqueness step.  Its sole graph
hypothesis is the connectedness of the adjacent-layer incidence graph. -/
theorem adjacentLayer_choice_eq_lower_or_upper (n r : ℕ)
    (hconnected : (adjacentLayerGraph n r).Connected)
    {A : Set (AdjacentLayerVertex n r)}
    (hA : EdgeExactlyOne (adjacentLayerGraph n r) A) :
    A = lowerLayer n r ∨ A = upperLayer n r :=
  eq_left_or_eq_right hconnected (adjacentLayerGraph_isBipartiteWith n r)
    (lowerLayer_union_upperLayer n r) hA

/-- Unconditional form for two actual adjacent layers of the `n`-coordinate
Boolean lattice. -/
theorem adjacentLayer_choice_eq_lower_or_upper_of_le {n r : ℕ} (hr : r ≤ n)
    {A : Set (AdjacentLayerVertex n r)}
    (hA : EdgeExactlyOne (adjacentLayerGraph n r) A) :
    A = lowerLayer n r ∨ A = upperLayer n r :=
  adjacentLayer_choice_eq_lower_or_upper n r (adjacentLayerGraph_connected hr) hA

end BooleanAdjacentLayers

end MiddleLayerUniqueness
end WeightedChains
