import WeightedChains.Preliminaries

/-!
# Paper-facing bridge definitions

Named versions of the geometric terminology in Definitions 2.8 and 2.9 of the
paper. Later proof modules use the equivalent arithmetic conditions directly;
these declarations provide stable, statement-level correspondence targets for
the publication artifact.
-/

set_option autoImplicit false

namespace WeightedChains
namespace Cube

/-- The lower side of the cube, expressed without fractions. -/
def lowerSide (n d : ℕ) : Set (Cube n d) :=
  {x | 2 * rank x ≤ n * d}

/-- The upper side of the cube, expressed without fractions. -/
def upperSide (n d : ℕ) : Set (Cube n d) :=
  {x | n * d ≤ 2 * rank x}

/-- A layer is inner when its distance from the middle is strictly less than
the maximum rank span `d * k` of a full-length good chain.

The complementary rank of zero-based layer `r` is `n * d - r`. This is the
corrected form of the paper's `n * d + 1 - r` display. -/
def InnerLayer (n d k r : ℕ) : Prop :=
  (2 * r).dist (n * d) < d * k

/-- A layer is outer when its distance from the middle is at least the maximum
rank span `d * k` of a full-length good chain. -/
def OuterLayer (n d k r : ℕ) : Prop :=
  d * k ≤ (2 * r).dist (n * d)

theorem innerLayer_iff_not_outerLayer (n d k r : ℕ) :
    InnerLayer n d k r ↔ ¬ OuterLayer n d k r := by
  simp only [InnerLayer, OuterLayer, not_le]

end Cube
end WeightedChains
