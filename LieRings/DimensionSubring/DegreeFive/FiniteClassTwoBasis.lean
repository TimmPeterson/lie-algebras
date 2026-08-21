import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneousFactors

/-!
# Projections of exact free-Lie components
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]

local notation "F" => FreeLieAlgebra ℤ X

/-- Projection back to the same homogeneous component fixes an exact free-Lie element. -/
theorem freeLieLengthComponent_coe_exact
    (n : ℕ) (x : freeLieExact X n) :
    freeLieLengthComponent X n (x : F) = (x : F) := by
  apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
  rw [freeLieToFreeAlgebra_freeLieLengthComponent]
  exact associativeLengthComponent_eq_self_of_mem_exact X
    (freeLieToFreeAlgebra_mem_exact X x)

/-- A different homogeneous projection of an exact free-Lie element is zero. -/
theorem freeLieLengthComponent_coe_exact_of_ne
    {m n : ℕ} (x : freeLieExact X m) (hmn : m ≠ n) :
    freeLieLengthComponent X n (x : F) = 0 := by
  apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
  rw [freeLieToFreeAlgebra_freeLieLengthComponent, map_zero]
  exact associativeLengthComponent_eq_zero_of_mem_exact_of_ne X
    (freeLieToFreeAlgebra_mem_exact X x) hmn

end


end DegreeFive

end LieRings
