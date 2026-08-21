import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneousFactors

/-!
# Compatibility of the free-Lie and associative filtrations
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

local notation "F" => FreeLieAlgebra ℤ X

/-- A free-Lie element of bracket filtration at least `m` has associative filtration at least
`m` after the canonical PBW map. -/
theorem freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh
    {m : ℕ} {x : F} (hx : x ∈ FreeLieDimension.lieHigh X m) :
    PBW.freeLieToFreeAlgebra ℤ X x ∈ FreeLieDimension.associativeHigh X m := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [FreeLieDimension.freeLieToFreeAlgebra_mk]
  exact FreeLieDimension.magmaToFreeAlgebra_mem_high X hp

end


end DegreeFive

end LieRings
