import Mathlib

/-!
# Challenge: a generalisation of Sperner's theorem via weighted chains

This is the statement of record for the Lean formalisation of

> Y. Dillies, M. Johnson, A. Kowalska,
> *A generalisation of Sperner's theorem using weighted chain decomposition*,
> [arXiv:2509.26493](https://arxiv.org/abs/2509.26493).

It is written to be audited on its own.  The only import is Mathlib, and every
notion from the paper is spelled out in place rather than introduced through a
project definition:

* the *cube* `{0, …, d}ⁿ` is the function type `Fin n → Fin (d + 1)`;
* the *rank* `|x|` of a vertex is `∑ i, (x i : ℕ)`, the sum of its coordinates;
* `x ≤ y` *coordinatewise* is `∀ i, x i ≤ y i`;
* the number of coordinates on which `x` and `y` *differ* is
  `(Finset.univ.filter fun i ↦ x i ≠ y i).card`;
* a family `A` is *`k`-separated* when any two distinct comparable members
  `x ≤ y` of `A` differ on strictly more than `k` coordinates:
  `∀ x ∈ A, ∀ y ∈ A, (∀ i, x i ≤ y i) → x ≠ y → k < (Finset.univ.filter fun i ↦ x i ≠ y i).card`;
* the paper's families `A₁` and `A₂` consist of the vertices whose rank is
  congruent to `⌊nd/2⌋ = n * d / 2`, respectively `⌈nd/2⌉ = n * d - n * d / 2`,
  modulo `d * k + 1`:
  `Finset.univ.filter fun x ↦ ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1]`.

The `≡ … [MOD …]` notation is Mathlib's `Nat.ModEq`.

Seven results are compared (see `comparator.json`).  Together they state the
paper's main theorem for `d ∈ {1, 2}` (Theorem 1.1), the elementary facts from
the introduction that the residue families are `k`-separated in every
dimension and have the same cardinality, the cardinality bound for arbitrary
`d` in the range `n / 2 ≤ k ≤ n` (the paper's appendix on that range) together
with its extension to cuboids `{0, …, d₁} × ⋯ × {0, …, dₙ}`, the paper's
weighted-chain proof of Sperner's theorem with its equality case (the other
appendix), and the asymptotic density statement from the paper's conclusions.

Every declaration below is deliberately left with a `sorry` placeholder; that
is the Comparator convention.  The proofs are supplied by
`WeightedChainsPalomar.Solution`, which restates each theorem verbatim and
discharges it from the corresponding result of the `WeightedChains` library.
-/

namespace WeightedChains

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
      k < (Finset.univ.filter fun i ↦ x i ≠ y i).card) := by
  sorry

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
      ∑ i, (x i : ℕ) ≡ (n * d - n * d / 2) [MOD d * k + 1]).card := by
  sorry

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
            ∑ i, (x i : ℕ) ≡ (n * d - n * d / 2) [MOD d * k + 1])) := by
  sorry

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
      ∑ i, (x i : ℕ) ≡ n * d / 2 [MOD d * k + 1]).card := by
  sorry

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
        ∑ i, (x i : ℕ) = ∑ i, bounds i - (∑ i, bounds i) / 2).card := by
  sorry

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
  sorry

/-- **Asymptotic density of the largest `k`-separated family** (the
conclusions of the paper).

Fix `d ≥ 1` and `k ≥ 1`, and let `M n` be the largest cardinality of a
`k`-separated family in `{0, …, d}ⁿ`; the hypothesis `hM` says exactly that
`M n` is the greatest element of the set of cardinalities of `k`-separated
families.  Then `M n / (d + 1)ⁿ` tends to `1 / (d * k + 1)` as `n → ∞`.

The maximum is specified by the `IsGreatest` hypothesis rather than by a
definition, so that this file introduces no auxiliary constants.  Since the
set of cardinalities is finite and nonempty (the empty family is
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
  sorry

end WeightedChains
