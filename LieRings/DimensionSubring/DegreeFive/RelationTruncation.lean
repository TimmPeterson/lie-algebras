import Mathlib.Algebra.Lie.Free

/-!
# Canonical free Lie presentations

The small presentation interface shared by the factor-two argument.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- The canonical free Lie ring presenting `L`. -/
abbrev CanonicalFreeLie := FreeLieAlgebra ℤ L

/-- Evaluation of the canonical free Lie presentation. -/
def canonicalFreeLieEvaluation : CanonicalFreeLie L →ₗ⁅ℤ⁆ L :=
  FreeLieAlgebra.lift ℤ id

@[simp]
theorem canonicalFreeLieEvaluation_of (x : L) :
    canonicalFreeLieEvaluation L (FreeLieAlgebra.of ℤ x) = x := by
  exact FreeLieAlgebra.lift_of_apply _ _

/-- The canonical free Lie presentation is onto. -/
theorem canonicalFreeLieEvaluation_surjective :
    Function.Surjective (canonicalFreeLieEvaluation L) := by
  intro x
  exact ⟨FreeLieAlgebra.of ℤ x, canonicalFreeLieEvaluation_of L x⟩

end


end DegreeFive

end LieRings
