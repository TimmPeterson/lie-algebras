import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneous

/-!
# Homogeneous Magnus images

The exact-weight statements needed by the factor-two argument.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]

local notation "F" => FreeLieAlgebra ℤ X

/-- A homogeneous nonassociative polynomial maps to the matching homogeneous associative
component. -/
theorem magmaToFreeAlgebra_mem_exact {n : ℕ}
    {p : FreeNonUnitalNonAssocAlgebra ℤ X} (hp : p ∈ magmaExact X n) :
    FreeLieDimension.magmaToFreeAlgebra X p ∈
      FreeLieDimension.associativeExact X n := by
  rw [magmaExact, Finsupp.supported_eq_span_single] at hp
  induction hp using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨w, hw, rfl⟩ := hq
      rw [← hw]
      exact FreeLieDimension.magmaToFreeAlgebra_single_mem_exact X w
  | zero => simp
  | add a b ha hb ihA ihB =>
      rw [map_add]
      exact (FreeLieDimension.associativeExact X n).add_mem ihA ihB
  | smul c a ha ih =>
      rw [map_smul]
      exact (FreeLieDimension.associativeExact X n).smul_mem c ih

/-- The Magnus image of an element of `freeLieExact X n` is homogeneous of weight `n`. -/
theorem freeLieToFreeAlgebra_mem_exact {n : ℕ} (x : freeLieExact X n) :
    PBW.freeLieToFreeAlgebra ℤ X (x : F) ∈
      FreeLieDimension.associativeExact X n := by
  obtain ⟨p, hp, hpx⟩ := x.property
  rw [← hpx]
  rw [FreeLieDimension.freeLieToFreeAlgebra_mk]
  exact magmaToFreeAlgebra_mem_exact X hp

end


end DegreeFive

end LieRings
