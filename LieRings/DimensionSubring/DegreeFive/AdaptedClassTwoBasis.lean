import LieRings.DimensionSubring.DegreeFive.AdaptedCollectorBasis
import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis

/-! # The class-two basis induced by the shared collected presentation -/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "P" => GeneratorModule X
local notation "M" => FreeClassTwo P

/-- The class-two basis whose two blocks are exactly the collected weight-one and weight-two
bases used by the adapted packet collector. -/
def adaptedHomogeneousClassTwoBasis
    (evaluation : LieHom ℤ F L) :
    Module.Basis (FiniteClassTwoBasisIndex X) ℤ M :=
  (((collectedHomogeneousBasis X L evaluation 1).prod
      (collectedHomogeneousBasis X L evaluation 2)).map
      (finiteLowExactEquivClassTwo X)).reindex
    (finiteClassTwoBasisIndexEquiv X)

@[simp]
theorem adaptedHomogeneousClassTwoBasis_weightOne
    (evaluation : LieHom ℤ F L)
    (i : FreeLieExactBasisIndex X 1) :
    adaptedHomogeneousClassTwoBasis X L evaluation (.weightOne i) =
      freeClassTwoTruncation X
        ((collectedHomogeneousBasis X L evaluation 1 i :
          freeLieExact X 1) : F) := by
  rw [adaptedHomogeneousClassTwoBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply]
  simp [finiteClassTwoBasisIndexEquiv, finiteLowExactEquivClassTwo,
    finiteLowExactToClassTwo]

@[simp]
theorem adaptedHomogeneousClassTwoBasis_weightTwo
    (evaluation : LieHom ℤ F L)
    (i : FreeLieExactBasisIndex X 2) :
    adaptedHomogeneousClassTwoBasis X L evaluation (.weightTwo i) =
      freeClassTwoTruncation X
        ((collectedHomogeneousBasis X L evaluation 2 i :
          freeLieExact X 2) : F) := by
  rw [adaptedHomogeneousClassTwoBasis, Module.Basis.reindex_apply,
    Module.Basis.map_apply]
  simp [finiteClassTwoBasisIndexEquiv, finiteLowExactEquivClassTwo,
    finiteLowExactToClassTwo]

end

end DegreeFive

end LieRings
