import WeightedChains.Preliminaries

/-!
# The ternary cube

Foundational definitions and identities for Section 5 of the paper.  The
paper writes the type of a point of `{0, 1, 2}^n` as `(a, b, c)` and writes
`\binom{n}{a,c}` for the number of points of that type.
-/

namespace WeightedChains

namespace Ternary

/-- The number of zero coordinates of a ternary vertex. -/
def zeroCount {n : ℕ} (x : Cube n 2) : ℕ := Cube.typeOf x 0

/-- The number of one coordinates of a ternary vertex. -/
def oneCount {n : ℕ} (x : Cube n 2) : ℕ := Cube.typeOf x 1

/-- The number of two coordinates of a ternary vertex. -/
def twoCount {n : ℕ} (x : Cube n 2) : ℕ := Cube.typeOf x 2

/-- The entries `(a, b, c)` of a ternary type add up to the dimension. -/
theorem zeroCount_add_oneCount_add_twoCount {n : ℕ} (x : Cube n 2) :
    zeroCount x + oneCount x + twoCount x = n := by
  have h := Cube.sum_typeOf x
  rw [Fin.sum_univ_three] at h
  exact h

/-- The rank of a point of type `(a, b, c)` is `b + 2c`. -/
theorem rank_eq_oneCount_add_two_mul_twoCount {n : ℕ} (x : Cube n 2) :
    Cube.rank x = oneCount x + 2 * twoCount x := by
  have hcoordinate (i : Fin n) :
      (x i : ℕ) = ∑ j : Fin 3, if x i = j then (j : ℕ) else 0 := by
    symm
    simp
  unfold Cube.rank
  calc
    ∑ i, (x i : ℕ) = ∑ i, ∑ j : Fin 3, if x i = j then (j : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcoordinate i
    _ = ∑ j : Fin 3, ∑ i, if x i = j then (j : ℕ) else 0 := Finset.sum_comm
    _ = ∑ j : Fin 3, (j : ℕ) * Cube.typeOf x j := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [Cube.typeOf]
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]
    _ = oneCount x + 2 * twoCount x := by
      rw [Fin.sum_univ_three]
      simp [oneCount, twoCount]

/-- A subtraction-free version of the paper's identity
`b + 2c = n - a + c`. -/
theorem rank_add_zeroCount {n : ℕ} (x : Cube n 2) :
    Cube.rank x + zeroCount x = n + twoCount x := by
  rw [rank_eq_oneCount_add_two_mul_twoCount]
  have h := zeroCount_add_oneCount_add_twoCount x
  omega

/-- A ternary vertex is in the lower half of the cube exactly when its type
has at least as many zero coordinates as two coordinates. -/
theorem rank_le_dimension_iff {n : ℕ} (x : Cube n 2) :
    Cube.rank x ≤ n ↔ twoCount x ≤ zeroCount x := by
  rw [rank_eq_oneCount_add_two_mul_twoCount]
  have h := zeroCount_add_oneCount_add_twoCount x
  omega

/-- A ternary vertex lies in the middle layer exactly when the zero and two
entries of its type agree. -/
theorem rank_eq_dimension_iff {n : ℕ} (x : Cube n 2) :
    Cube.rank x = n ↔ zeroCount x = twoCount x := by
  rw [rank_eq_oneCount_add_two_mul_twoCount]
  have h := zeroCount_add_oneCount_add_twoCount x
  omega

/-- For a lower type `(a,b,c)`, being at least `k` rank steps below the
middle is the paper's arithmetic condition `c + k ≤ a`. -/
theorem rank_add_le_dimension_iff {n : ℕ} (x : Cube n 2) (k : ℕ) :
    Cube.rank x + k ≤ n ↔ twoCount x + k ≤ zeroCount x := by
  rw [rank_eq_oneCount_add_two_mul_twoCount]
  have h := zeroCount_add_oneCount_add_twoCount x
  omega

/-- A dimension-indexed triple `(a,b,c)` recording a ternary type. -/
@[ext]
structure TypeCounts (n : ℕ) where
  /-- Number of coordinates equal to zero. -/ zeros : ℕ
  /-- Number of coordinates equal to one. -/ ones : ℕ
  /-- Number of coordinates equal to two. -/ twos : ℕ
  /-- The three coordinate counts exhaust the dimension. -/ sum_eq : zeros + ones + twos = n

namespace TypeCounts

/-- The type triple of a ternary vertex. -/
def ofVertex {n : ℕ} (x : Cube n 2) : TypeCounts n where
  zeros := zeroCount x
  ones := oneCount x
  twos := twoCount x
  sum_eq := zeroCount_add_oneCount_add_twoCount x

/-- The common rank of the vertices represented by a type triple. -/
def rank {n : ℕ} (t : TypeCounts n) : ℕ := t.ones + 2 * t.twos

@[simp]
theorem rank_ofVertex {n : ℕ} (x : Cube n 2) :
    (ofVertex x).rank = Cube.rank x := by
  exact (rank_eq_oneCount_add_two_mul_twoCount x).symm

/-- Coordinatewise reflection `j ↦ 2-j` swaps the zero and two counts. -/
def reflect {n : ℕ} (t : TypeCounts n) : TypeCounts n where
  zeros := t.twos
  ones := t.ones
  twos := t.zeros
  sum_eq := by
    have h := t.sum_eq
    omega

@[simp] theorem reflect_zeros {n : ℕ} (t : TypeCounts n) : t.reflect.zeros = t.twos := rfl
@[simp] theorem reflect_ones {n : ℕ} (t : TypeCounts n) : t.reflect.ones = t.ones := rfl
@[simp] theorem reflect_twos {n : ℕ} (t : TypeCounts n) : t.reflect.twos = t.zeros := rfl

@[simp]
theorem reflect_reflect {n : ℕ} (t : TypeCounts n) : t.reflect.reflect = t := by
  cases t
  rfl

/-- Complementary type triples have ranks adding to `2n`. -/
theorem rank_add_rank_reflect {n : ℕ} (t : TypeCounts n) :
    t.rank + t.reflect.rank = 2 * n := by
  simp only [rank, reflect]
  have h := t.sum_eq
  omega

/-- A type triple is below the middle layer precisely when `c ≤ a`. -/
theorem rank_le_dimension_iff {n : ℕ} (t : TypeCounts n) :
    t.rank ≤ n ↔ t.twos ≤ t.zeros := by
  unfold rank
  have h := t.sum_eq
  omega

/-- The lower-outer condition `c+k ≤ a` is equivalent to leaving at least
`k` rank steps before the middle layer. -/
theorem rank_add_le_dimension_iff {n : ℕ} (t : TypeCounts n) (k : ℕ) :
    t.rank + k ≤ n ↔ t.twos + k ≤ t.zeros := by
  unfold rank
  have h := t.sum_eq
  omega

/-- The type after `i` complete blocks of a basic chain.  Each block changes
one zero coordinate through one to two. -/
def evenStep {n : ℕ} (t : TypeCounts n) (i : ℕ) (hi : i ≤ t.zeros) : TypeCounts n where
  zeros := t.zeros - i
  ones := t.ones
  twos := t.twos + i
  sum_eq := by
    have h := t.sum_eq
    omega

/-- The intermediate type inside block `i` of a basic chain. -/
def oddStep {n : ℕ} (t : TypeCounts n) (i : ℕ) (hi : i < t.zeros) : TypeCounts n where
  zeros := t.zeros - (i + 1)
  ones := t.ones + 1
  twos := t.twos + i
  sum_eq := by
    have h := t.sum_eq
    omega

@[simp]
theorem evenStep_rank {n : ℕ} (t : TypeCounts n) (i : ℕ) (hi : i ≤ t.zeros) :
    (t.evenStep i hi).rank = t.rank + 2 * i := by
  simp only [evenStep, rank]
  omega

@[simp]
theorem oddStep_rank {n : ℕ} (t : TypeCounts n) (i : ℕ) (hi : i < t.zeros) :
    (t.oddStep i hi).rank = t.rank + (2 * i + 1) := by
  simp only [oddStep, rank]
  omega

/-- A basic chain of width `w` ends at the type obtained after `w` complete
blocks and has traversed `2w` rank steps. -/
theorem evenStep_rank_sub {n : ℕ} (t : TypeCounts n) (w : ℕ) (hw : w ≤ t.zeros) :
    (t.evenStep w hw).rank - t.rank = 2 * w := by
  rw [evenStep_rank, Nat.add_sub_cancel_left]

/-- Starting at a lower type and taking `a-c` complete blocks reaches its
reflected type, which is the type-level form of a symmetric basic chain. -/
theorem evenStep_zero_sub_two_eq_reflect {n : ℕ} (t : TypeCounts n)
    (hlower : t.twos ≤ t.zeros) :
    t.evenStep (t.zeros - t.twos) (Nat.sub_le _ _) = t.reflect := by
  cases t with
  | mk zeros ones twos hsum =>
      change twos ≤ zeros at hlower
      apply TypeCounts.ext <;> simp only [evenStep, reflect] <;> omega

end TypeCounts

/-- The paper's trinomial coefficient `\binom{n}{a,c}`.  It chooses the
zero coordinates first and then the two coordinates; all remaining
coordinates are equal to one.  The definition is automatically zero when
`a + c > n`. -/
def trinomial (n a c : ℕ) : ℕ := n.choose a * (n - a).choose c

@[simp]
theorem trinomial_zero_right (n a : ℕ) : trinomial n a 0 = n.choose a := by
  simp [trinomial]

@[simp]
theorem trinomial_zero_left (n c : ℕ) : trinomial n 0 c = n.choose c := by
  simp [trinomial]

@[simp]
theorem trinomial_self_zero (n : ℕ) : trinomial n n 0 = 1 := by
  simp

/-- Interchanging zero and two coordinates preserves type size. -/
theorem trinomial_comm (n a c : ℕ) : trinomial n a c = trinomial n c a := by
  have ha := Nat.choose_mul (n := n) (k := a + c) (s := a) (Nat.le_add_right a c)
  have hc := Nat.choose_mul (n := n) (k := a + c) (s := c) (Nat.le_add_left c a)
  simp only [Nat.add_sub_cancel_left] at ha
  rw [Nat.add_sub_cancel_right] at hc
  unfold trinomial
  calc
    n.choose a * (n - a).choose c = n.choose (a + c) * (a + c).choose a := ha.symm
    _ = n.choose (a + c) * (a + c).choose c := by rw [Nat.choose_symm_add]
    _ = n.choose c * (n - c).choose a := hc

/-- There are no points of a putative type whose zero and two counts exceed
the dimension. -/
theorem trinomial_eq_zero_of_lt_add {n a c : ℕ} (h : n < a + c) :
    trinomial n a c = 0 := by
  by_cases ha : a ≤ n
  · have hc : n - a < c := by omega
    simp [trinomial, Nat.choose_eq_zero_of_lt hc]
  · have han : n < a := Nat.lt_of_not_ge ha
    simp [trinomial, Nat.choose_eq_zero_of_lt han]

/-- Every valid ternary type has a nonempty coordinate-permutation orbit. -/
theorem trinomial_pos {n a c : ℕ} (h : a + c ≤ n) : 0 < trinomial n a c := by
  exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

theorem trinomial_pos_iff {n a c : ℕ} : 0 < trinomial n a c ↔ a + c ≤ n := by
  constructor
  · intro hpositive
    by_contra hvalid
    have hzero := trinomial_eq_zero_of_lt_add (Nat.lt_of_not_ge hvalid)
    omega
  · exact trinomial_pos

theorem trinomial_eq_zero_iff {n a c : ℕ} : trinomial n a c = 0 ↔ n < a + c := by
  constructor
  · intro hzero
    by_contra hnot
    exact (Nat.ne_of_gt (trinomial_pos (Nat.le_of_not_gt hnot))) hzero
  · exact trinomial_eq_zero_of_lt_add

/-- The three-term Pascal identity, stated without truncated predecessor
subtractions.  This is the form used to pass from dimension `n` to `n+1` in
Section 5. -/
theorem trinomial_succ (n a c : ℕ) :
    trinomial (n + 1) (a + 1) (c + 1) =
      trinomial n a (c + 1) + trinomial n (a + 1) (c + 1) + trinomial n (a + 1) c := by
  by_cases ha : a < n
  · have hsub : n + 1 - (a + 1) = n - a := by omega
    have hsub' : n - a = (n - (a + 1)) + 1 := by omega
    have hpascal :
        (n - a).choose (c + 1) =
          (n - (a + 1)).choose c + (n - (a + 1)).choose (c + 1) := by
      rw [hsub', Nat.choose_succ_succ]
    simp only [trinomial, hsub]
    rw [Nat.choose_succ_succ, hpascal]
    ring
  · have hna : n ≤ a := Nat.le_of_not_gt ha
    by_cases han : a = n
    · subst a
      simp [trinomial]
    · have hlt : n < a := lt_of_le_of_ne hna (Ne.symm han)
      have hlt' : n + 1 < a + 1 := Nat.add_lt_add_right hlt 1
      have hlt'' : n < a + 1 := hlt.trans a.lt_succ_self
      simp [trinomial, Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt hlt',
        Nat.choose_eq_zero_of_lt hlt'']

/-- The trinomial coefficient extended by zero to negative type entries.
This matches the convention used in the recursive definition of `U_n` in
Section 5. -/
def extendedTrinomial (n : ℕ) (a c : ℤ) : ℤ :=
  if 0 ≤ a ∧ 0 ≤ c then trinomial n a.toNat c.toNat else 0

@[simp]
theorem extendedTrinomial_ofNat (n a c : ℕ) :
    extendedTrinomial n a c = trinomial n a c := by
  simp [extendedTrinomial]

@[simp]
theorem extendedTrinomial_eq_zero_of_neg_left {n : ℕ} {a c : ℤ} (ha : a < 0) :
    extendedTrinomial n a c = 0 := by
  simp only [extendedTrinomial]
  split_ifs with h
  · omega
  · rfl

@[simp]
theorem extendedTrinomial_eq_zero_of_neg_right {n : ℕ} {a c : ℤ} (hc : c < 0) :
    extendedTrinomial n a c = 0 := by
  simp only [extendedTrinomial]
  split_ifs with h
  · omega
  · rfl

/-- Reflection of types also preserves the zero-extended coefficient. -/
theorem extendedTrinomial_comm (n : ℕ) (a c : ℤ) :
    extendedTrinomial n a c = extendedTrinomial n c a := by
  simp only [extendedTrinomial]
  by_cases h : 0 ≤ a ∧ 0 ≤ c
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    exact_mod_cast trinomial_comm n a.toNat c.toNat
  · rw [if_neg h, if_neg]
    intro hswap
    exact h ⟨hswap.2, hswap.1⟩

/-- The zero extension also vanishes when the two specified entries cannot
fit in `n` coordinates. -/
theorem extendedTrinomial_eq_zero_of_lt_add {n : ℕ} {a c : ℤ}
    (h : (n : ℤ) < a + c) : extendedTrinomial n a c = 0 := by
  by_cases ha : a < 0
  · exact extendedTrinomial_eq_zero_of_neg_left ha
  by_cases hc : c < 0
  · exact extendedTrinomial_eq_zero_of_neg_right hc
  have ha0 : 0 ≤ a := Int.le_of_not_gt ha
  have hc0 : 0 ≤ c := Int.le_of_not_gt hc
  have haeq : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
  have hceq : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc0
  have hz : (n : ℤ) < (a.toNat : ℤ) + (c.toNat : ℤ) := by
    rwa [haeq, hceq]
  have h' : n < a.toNat + c.toNat := by
    exact_mod_cast hz
  simp [extendedTrinomial, ha0, hc0, trinomial_eq_zero_of_lt_add h']

/-- The three-term Pascal identity with the paper's zero convention for
negative indices. -/
theorem extendedTrinomial_succ (n : ℕ) (a c : ℤ) :
    extendedTrinomial (n + 1) a c =
      extendedTrinomial n (a - 1) c + extendedTrinomial n a c +
        extendedTrinomial n a (c - 1) := by
  by_cases ha : a < 0
  · have ha' : a - 1 < 0 := by omega
    simp [extendedTrinomial_eq_zero_of_neg_left ha,
      extendedTrinomial_eq_zero_of_neg_left ha']
  by_cases hc : c < 0
  · have hc' : c - 1 < 0 := by omega
    simp [extendedTrinomial_eq_zero_of_neg_right hc,
      extendedTrinomial_eq_zero_of_neg_right hc']
  have ha0 : 0 ≤ a := Int.le_of_not_gt ha
  have hc0 : 0 ≤ c := Int.le_of_not_gt hc
  rw [← Int.toNat_of_nonneg ha0, ← Int.toNat_of_nonneg hc0]
  generalize a.toNat = a' at *
  generalize c.toNat = c' at *
  cases a' with
  | zero =>
      cases c' with
      | zero => simp [extendedTrinomial, trinomial]
      | succ c' =>
          norm_num [extendedTrinomial, trinomial, Nat.choose_succ_succ]
          have hpos : (0 : ℤ) ≤ c' + 1 := by omega
          rw [if_pos hpos, if_pos hpos]
          ring
  | succ a' =>
      cases c' with
      | zero =>
          norm_num [extendedTrinomial, trinomial, Nat.choose_succ_succ]
          have hpos : (0 : ℤ) ≤ a' + 1 := by omega
          rw [if_pos hpos, if_pos hpos]
      | succ c' =>
          norm_num [extendedTrinomial]
          exact_mod_cast trinomial_succ n a' c'

end Ternary

end WeightedChains
