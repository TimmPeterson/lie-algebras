import LieRings.DimensionSubring.DegreeFive.FiniteRelationRows

/-!
# Vanishing of low free-Lie components
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- A homogeneous projection below the certified minimum weight of a free-Lie element is zero. -/
theorem freeLieLengthComponent_eq_zero_of_mem_lieHigh
    {x : F} {m n : ℕ} (hx : x ∈ FreeLieDimension.lieHigh X m) (hnm : n < m) :
    freeLieLengthComponent X n x = 0 := by
  apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
  rw [freeLieToFreeAlgebra_freeLieLengthComponent, map_zero]
  apply associativeLengthComponent_eq_zero_of_mem_high X
  · obtain ⟨p, hp, rfl⟩ := hx
    rw [FreeLieDimension.freeLieToFreeAlgebra_mk]
    exact FreeLieDimension.magmaToFreeAlgebra_mem_high X hp
  · exact hnm

end


end DegreeFive

end LieRings
