import WeightedChains.Preliminaries
import WeightedChains.ResidueSymmetry
import WeightedChains.MainTheorem
import WeightedChains.Appendices.Sperner
import WeightedChains.Appendices.LargeK
import WeightedChains.Asymptotics

/-!
# Solution: proofs of the `WeightedChainsPalomar.Challenge` declarations

Proofs of the statements of `WeightedChainsPalomar.Challenge`, obtained from
the corresponding results of the `WeightedChains` library.

Each theorem below is stated byte-for-byte as in the `Challenge` module, so
that `leanprover/comparator` (configured by `comparator.json`) accepts it; the
proofs only translate between the project's vocabulary (`Cube.KSeparated`,
`Cube.lowerResidueFinset`, `Asymptotics.maxKSeparatedCard`, ...) and the
unfolded statements.  The `Challenge` module is intentionally *not* imported,
so that its `sorry` placeholders never enter this environment.
-/

namespace WeightedChains

/-- The paper's `k`-separation predicate on a finset, written out in the form
used by the compared statements: comparability is `∀ i, x i ≤ y i` and the
number of differing coordinates is a `Finset.filter` cardinality. -/
private theorem kSeparated_of_forall {n d k : ℕ} (A : Finset (Cube n d))
    (hA : ∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x ≠ y →
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) :
    Cube.KSeparated (A : Set (Cube n d)) k :=
  fun hx hy hle hne ↦ hA _ hx _ hy hle hne

/-- **The residue families are `k`-separated** (Remark after Theorem 1.1).

For every `n`, `d`, and `k`, both families `A₁` and `A₂` of the paper are
`k`-separated: two distinct vertices `x ≤ y` of `{0, …, d}ⁿ` whose ranks are
congruent modulo `d * k + 1` differ on more than `k` coordinates.  The
conclusion is stated once for the residue `n * d / 2 = ⌊nd/2⌋` (the family
`A₁`) and once for the residue `n * d - n * d / 2 = ⌈nd/2⌉` (the family `A₂`).
No restriction on `d` or `k` is needed for this direction. -/
theorem residue_families_kSeparated (n d k : ℕ) :
    (∀ x y : Fin n → Fin (d + 1),
      ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1] →
      ∑ i, (y i : ℕ) ≡ n * d / 2 [MOD d * k + 1] →
      (∀ i, x i ≤ y i) → x ≠ y →
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) ∧
    (∀ x y : Fin n → Fin (d + 1),
      ∑ i, (x i : ℕ) ≡ (n * d - n * d / 2) [MOD d * k + 1] →
      ∑ i, (y i : ℕ) ≡ (n * d - n * d / 2) [MOD d * k + 1] →
      (∀ i, x i ≤ y i) → x ≠ y →
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) :=
  ⟨fun _ _ hx hy hle hne ↦ Cube.lowerResidueFamily_kSeparated n d k hx hy hle hne,
    fun _ _ hx hy hle hne ↦ Cube.upperResidueFamily_kSeparated n d k hx hy hle hne⟩

/-- **The residue families have the same cardinality** (the introduction).

For every `n`, `d`, and `k`, the families `A₁` and `A₂` have the same number
of members: coordinatewise reflection `x ↦ d - x` of the cube maps one onto
the other.  Together with `main_theorem` this says that when `n * d` is odd
the paper's two extremal families are distinct and equally large, and
together with `large_k_bound` it says that `A₂` is also a largest
`k`-separated family in the range `n / 2 ≤ k ≤ n`. -/
theorem residue_families_card_eq (n d k : ℕ) :
    (Finset.univ.filter fun x : Fin n → Fin (d + 1) ↦
      ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1]).card =
    (Finset.univ.filter fun x : Fin n → Fin (d + 1) ↦
      ∑ i, (x i : ℕ) ≡ (n * d - n * d / 2) [MOD d * k + 1]).card :=
  Cube.card_lowerResidueFinset_eq_card_upperResidueFinset n d k

/-- **The main theorem** (Theorem 1.1 of the paper).

Let `1 < k ≤ n` and `d ∈ {1, 2}`.  Every `k`-separated family `A` of vertices
of the cube `{0, …, d}ⁿ` has at most as many members as the family `A₁` of
vertices whose rank is congruent to `⌊nd/2⌋` modulo `d * k + 1`, and `A`
attains this bound exactly when `A = A₁` or `A = A₂`, where `A₂` uses the
residue `⌈nd/2⌉` instead.  When `n * d` is even the two residues coincide, so
`A₁ = A₂` and the extremal family is unique.

The hypothesis `hA` is `k`-separation of `A`: distinct members `x ≤ y` of `A`
(coordinatewise) differ on strictly more than `k` coordinates.  The
`k`-separation of `A₁` and `A₂` themselves is the separate compared theorem
`residue_families_kSeparated`. -/
theorem main_theorem (n k d : ℕ) (hk : 1 < k) (hkn : k ≤ n) (hd : d = 1 ∨ d = 2)
    (A : Finset (Fin n → Fin (d + 1)))
    (hA : ∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x ≠ y →
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) :
    A.card ≤ (Finset.univ.filter fun x : Fin n → Fin (d + 1) ↦
        ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1]).card ∧
      (A.card = (Finset.univ.filter fun x : Fin n → Fin (d + 1) ↦
          ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1]).card ↔
        A = (Finset.univ.filter fun x : Fin n → Fin (d + 1) ↦
            ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1]) ∨
          A = (Finset.univ.filter fun x : Fin n → Fin (d + 1) ↦
            ∑ i, (x i : ℕ) ≡ (n * d - n * d / 2) [MOD d * k + 1])) :=
  main_cardinality_and_uniqueness n k d hk hkn hd A (kSeparated_of_forall A hA)

/-- **The cardinality bound for arbitrary `d` when `n / 2 ≤ k ≤ n`**
(the paper's appendix on this range).

For every alphabet bound `d`, if `n ≤ 2 * k` and `k ≤ n`, then every
`k`-separated family `A` in `{0, …, d}ⁿ` has at most as many members as the
residue family `A₁`.  In this range `A₁` is the middle layer of the cube, and
the bound follows from a symmetric chain decomposition; the paper does not
claim uniqueness of the extremal families here, and neither does this
statement. -/
theorem large_k_bound (n d k : ℕ) (hhalf : n ≤ 2 * k) (hkn : k ≤ n)
    (A : Finset (Fin n → Fin (d + 1)))
    (hA : ∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x ≠ y →
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) :
    A.card ≤ (Finset.univ.filter fun x : Fin n → Fin (d + 1) ↦
      ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1]).card :=
  LargeK.kSeparated_card_le_lowerResidueFinset n d k hhalf hkn A
    (kSeparated_of_forall A hA)

/-- The cuboid `k`-separation predicate, written out in the form used by the
compared statements. -/
private theorem cuboid_kSeparated_of_forall {n k : ℕ} {bounds : Fin n → ℕ}
    (A : Finset (Cuboid bounds))
    (hA : ∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x ≠ y →
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) :
    Cuboid.KSeparated (A : Set (Cuboid bounds)) k :=
  fun hx hy hle hne ↦ hA _ hx _ hy hle hne

/-- **The cardinality bound for cuboids when `n / 2 ≤ k ≤ n`** (the closing
remark of the paper's appendix on this range).

The same argument applies to a cuboid `{0, …, d₁} × ⋯ × {0, …, dₙ}` with
arbitrary coordinate bounds `dᵢ = bounds i`, whose vertices are the dependent
functions `(i : Fin n) → Fin (bounds i + 1)` and whose rank is again the
coordinate sum.  If `n ≤ 2 * k` and `k ≤ n`, every `k`-separated family `A` in
the cuboid has at most as many members as the lower central layer, the
vertices of rank `⌊(∑ dᵢ)/2⌋`, and likewise at most as many members as the
upper central layer, the vertices of rank `⌈(∑ dᵢ)/2⌉`.  The two layers have
the same cardinality by reflection; the cube case `bounds = fun _ ↦ d`
recovers `large_k_bound`. -/
theorem cuboid_large_k_bound (n k : ℕ) (bounds : Fin n → ℕ)
    (hhalf : n ≤ 2 * k) (hkn : k ≤ n)
    (A : Finset ((i : Fin n) → Fin (bounds i + 1)))
    (hA : ∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x ≠ y →
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) :
    A.card ≤ (Finset.univ.filter fun x : (i : Fin n) → Fin (bounds i + 1) ↦
        ∑ i, (x i : ℕ) = (∑ i, bounds i) / 2).card ∧
      A.card ≤ (Finset.univ.filter fun x : (i : Fin n) → Fin (bounds i + 1) ↦
        ∑ i, (x i : ℕ) = ∑ i, bounds i - (∑ i, bounds i) / 2).card :=
  ⟨(LargeK.cuboid_lowerMiddleLayer_isMaximum n k bounds hhalf hkn).2 A
      (cuboid_kSeparated_of_forall A hA),
    (LargeK.cuboid_upperMiddleLayer_isMaximum n k bounds hhalf hkn).2 A
      (cuboid_kSeparated_of_forall A hA)⟩

/-- The two middle layers of the Boolean cube, as the compared statement writes
them. -/
private theorem sperner_layers_eq (n : ℕ) :
    SpernerAppendix.lowerMiddleLayer n =
        (Finset.univ.filter fun x : Fin n → Fin 2 ↦ ∑ i, (x i : ℕ) = n / 2) ∧
      SpernerAppendix.upperMiddleLayer n =
        (Finset.univ.filter fun x : Fin n → Fin 2 ↦ ∑ i, (x i : ℕ) = n - n / 2) := by
  constructor
  · ext x
    simp only [SpernerAppendix.mem_lowerMiddleLayer_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  · ext x
    simp only [SpernerAppendix.mem_upperMiddleLayer_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl

/-- **Sperner's theorem, with its equality case** (the paper's appendix giving
a weighted-chain proof of Sperner's theorem).

Identify a subset of `{1, …, n}` with its indicator vector in `{0, 1}ⁿ`, so
that inclusion is the coordinatewise order.  An antichain `A` of subsets, that
is a family in which `x ≤ y` forces `x = y`, has at most `n.choose (n / 2)`
members, and has exactly that many members precisely when it is the layer of
all `⌊n/2⌋`-element subsets or the layer of all `⌈n/2⌉`-element subsets (which
coincide when `n` is even).  This is the case `d = 1`, `k = 1` of the paper's
problem, for which `1`-separation of `{0, 1}ⁿ` is exactly the antichain
condition. -/
theorem sperner_theorem (n : ℕ) (A : Finset (Fin n → Fin 2))
    (hA : ∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x = y) :
    A.card ≤ n.choose (n / 2) ∧
      (A.card = n.choose (n / 2) ↔
        A = (Finset.univ.filter fun x : Fin n → Fin 2 ↦ ∑ i, (x i : ℕ) = n / 2) ∨
          A = (Finset.univ.filter fun x : Fin n → Fin 2 ↦ ∑ i, (x i : ℕ) = n - n / 2)) := by
  obtain ⟨hlower, hupper⟩ := sperner_layers_eq n
  rw [← hlower, ← hupper]
  exact SpernerAppendix.cardinality_and_uniqueness n A
    (fun x y hx hy hle ↦ hA x hx y hy hle)

/-- **Asymptotic density of the largest `k`-separated family** (the
conclusions of the paper).

Fix `d ≥ 1` and `k ≥ 1`, and let `M n` be the largest cardinality of a
`k`-separated family in `{0, …, d}ⁿ`; the hypothesis `hM` says exactly that
`M n` is the greatest element of the set of cardinalities of `k`-separated
families.  Then `M n / (d + 1)ⁿ` tends to `1 / (d * k + 1)` as `n → ∞`.

The maximum is specified by the `IsGreatest` hypothesis rather than by a
definition, so that the `Challenge` module introduces no auxiliary constants.
Since the set of cardinalities is finite and nonempty (the empty family is
`k`-separated), such an `M` always exists and is unique. -/
theorem asymptotic_density (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (M : ℕ → ℕ)
    (hM : ∀ n, IsGreatest
      {m : ℕ | ∃ A : Finset (Fin n → Fin (d + 1)),
        (∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x ≠ y →
          k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) ∧
        A.card = m}
      (M n)) :
    Filter.Tendsto (fun n : ℕ ↦ (M n : ℝ) / (d + 1 : ℝ) ^ n) Filter.atTop
      (nhds (1 / (d * k + 1 : ℝ))) := by
  have hM' : ∀ n, M n = Asymptotics.maxKSeparatedCard n d k := by
    intro n
    obtain ⟨⟨B, hB, hBcard⟩, hgreatest⟩ := hM n
    obtain ⟨A, hA, hAcard⟩ :=
      Asymptotics.exists_kSeparated_card_eq_maxKSeparatedCard n d k
    apply le_antisymm
    · rw [← hBcard]
      exact Asymptotics.card_le_maxKSeparatedCard B (kSeparated_of_forall B hB)
    · exact hgreatest ⟨A, fun _ hx _ hy hle hne ↦ hA hx hy hle hne, hAcard⟩
  have key := Asymptotics.maxKSeparatedCard_density_tendsto d k hd hk
  have hfun : (fun n : ℕ ↦ (M n : ℝ) / (d + 1 : ℝ) ^ n) =
      fun n : ℕ ↦ (Asymptotics.maxKSeparatedCard n d k : ℝ) / (((d + 1 : ℕ) : ℝ) ^ n) := by
    funext n
    rw [hM']
    push_cast
    rfl
  have hlimit : (1 / (d * k + 1 : ℝ)) = ((d * k + 1 : ℕ) : ℝ)⁻¹ := by
    push_cast
    ring
  rw [hfun, hlimit]
  exact key

end WeightedChains
