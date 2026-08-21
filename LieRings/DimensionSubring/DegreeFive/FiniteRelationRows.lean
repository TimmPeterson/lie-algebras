import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneous

/-!
# Leading terms of filtered presentation relations
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- Homogeneous projection with its codomain restricted to the exact component. -/
def freeLieExactProjection (n : ℕ) : F →ₗ[ℤ] freeLieExact X n :=
  (freeLieLengthComponent X n).codRestrict (freeLieExact X n)
    (freeLieLengthComponent_mem_exact X n)

/-- Relations whose least possible bracket weight is `n`. -/
def filteredPresentationRelations
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) : Submodule ℤ F :=
  LinearMap.ker evaluation.toLinearMap ⊓ FreeLieDimension.lieHigh X n

/-- The submodule of weight-`n` leading terms of filtered defining relations. -/
def homogeneousRelationLeading
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) :
    Submodule ℤ (freeLieExact X n) :=
  (filteredPresentationRelations X L evaluation n).map
    (freeLieExactProjection X n)

/-- The leading term of a filtered relation, bundled in the leading-relation submodule. -/
def filteredRelationLeading
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    homogeneousRelationLeading X L evaluation n :=
  ⟨freeLieExactProjection X n (r : F), ⟨r, r.property, rfl⟩⟩

end


end DegreeFive

end LieRings
