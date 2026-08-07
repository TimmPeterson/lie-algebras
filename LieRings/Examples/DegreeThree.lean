import LieRings.DimensionSubring.DegreeThree

/-!
# Using the third dimension-subring theorem

For a Lie ring `L`, the theorem is applied directly.  Recall that this library follows mathlib's
zero-based lower-central indexing: `lowerCentralSeries ℤ L 2` is conventional `gamma_3(L)`.
-/

namespace LieRings.Examples

universe u

variable (L : Type u) [LieRing L]

/-- The conventional statement `delta_3(L) = gamma_3(L)`. -/
example : dimensionSubring ℤ L 3 = lowerCentralSeries ℤ L 2 :=
  dimensionSubring_three_eq_lowerCentralSeries_two L

/-- Elementwise use: a member of `delta_3` belongs to `gamma_3`. -/
example (x : L) (hx : x ∈ dimensionSubring ℤ L 3) :
    x ∈ lowerCentralSeries ℤ L 2 := by
  rw [← dimensionSubring_three_eq_lowerCentralSeries_two L]
  exact hx


end LieRings.Examples
