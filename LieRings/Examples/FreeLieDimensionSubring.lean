import LieRings.DimensionSubring.FreeLie

/-!
# Dimension subrings of a free Lie ring

Copyable examples of the integral theorem `δₙ(F) = γₙ(F)` for a free Lie ring.
-/

namespace LieRings.Examples

universe u

/-- Mathlib numbers `γ₁` by zero, so this is `δₙ₊₁(F) = γₙ₊₁(F)`. -/
example (X : Type u) (n : ℕ) :
    dimensionSubring ℤ (FreeLieAlgebra ℤ X) (n + 1) =
      lowerCentralSeries ℤ (FreeLieAlgebra ℤ X) n :=
  FreeLieDimension.dimensionSubring_succ_eq_lowerCentralSeries X n

/-- Direct conventional indexing: `δₙ(F) = γₙ(F)` for every natural number `n`. -/
example (X : Type u) (n : ℕ) :
    dimensionSubring ℤ (FreeLieAlgebra ℤ X) n =
      lowerCentralSeries ℤ (FreeLieAlgebra ℤ X) (n - 1) :=
  FreeLieDimension.dimensionSubring_eq_lowerCentralSeries_pred X n

end LieRings.Examples
