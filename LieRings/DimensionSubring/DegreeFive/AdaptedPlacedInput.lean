import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneous

/-!
# Free generators in homogeneous degree one
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]

/-- A free generator, bundled in the homogeneous component of weight one. -/
def adaptedFreeGeneratorExactOne (x : X) : freeLieExact X 1 :=
  ⟨FreeLieAlgebra.of ℤ x, ⟨FreeNonUnitalNonAssocAlgebra.of ℤ x, by
    intro w hw
    have hnz := Finsupp.mem_support_iff.mp hw
    have hw' : w = FreeMagma.of x := by
      by_contra hne
      exact hnz (by simp [FreeNonUnitalNonAssocAlgebra.of, hne])
    subst w
    rfl
  , rfl⟩⟩

end


end DegreeFive

end LieRings
