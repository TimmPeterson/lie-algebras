import LieRings.DimensionSubring.FreeLie

/-!
# Homogeneous components of a free associative algebra

Word-length projections used by the factor-two coefficient calculation.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

local notation "A" => FreeAlgebra ℤ X
local notation "MA" => MonoidAlgebra ℤ (FreeMonoid X)

/-- Projection of a monoid polynomial onto words of one fixed length. -/
def monoidLengthComponent (n : ℕ) : MA →ₗ[ℤ] MA where
  toFun p := Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n) p
  map_add' p q := by
    ext w
    by_cases h : w.length = n <;> simp [h]
  map_smul' a p := by
    exact Finsupp.filter_smul

/-- Projection of a free associative polynomial onto words of one fixed length. -/
def associativeLengthComponent (n : ℕ) : A →ₗ[ℤ] A :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toLinearMap.comp
    ((monoidLengthComponent X n).comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

@[simp]
theorem equiv_associativeLengthComponent (n : ℕ) (p : A) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (associativeLengthComponent X n p) =
      Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n)
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
        (Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n)
          (FreeAlgebra.equivMonoidAlgebraFreeMonoid p))) = _
  exact FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply _

/-- A homogeneous projection is supported in precisely its indicated length. -/
theorem associativeLengthComponent_mem_exact (n : ℕ) (p : A) :
    associativeLengthComponent X n p ∈
      FreeLieDimension.associativeExact X n := by
  intro w hw
  have hnz := Finsupp.mem_support_iff.mp hw
  by_contra hlength
  apply hnz
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (associativeLengthComponent X n p)) w = 0
  rw [equiv_associativeLengthComponent]
  exact Finsupp.filter_apply_neg
    (fun w : FreeMonoid X ↦ w.length = n)
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) hlength

/-- Projection to length `n` vanishes on polynomials of minimum length `m > n`. -/
theorem associativeLengthComponent_eq_zero_of_mem_high
    {m n : ℕ} {p : A}
    (hp : p ∈ FreeLieDimension.associativeHigh X m) (hnm : n < m) :
    associativeLengthComponent X n p = 0 := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  ext w
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (associativeLengthComponent X n p)) w =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid 0) w
  rw [equiv_associativeLengthComponent]
  rw [map_zero]
  change (Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n)
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid p)) w = 0
  by_cases hw : w.length = n
  · rw [Finsupp.filter_apply_pos
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hw]
    by_contra hcoeff
    have hsupport : w ∈
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support :=
      Finsupp.mem_support_iff.mpr hcoeff
    exact (Nat.not_le_of_gt (hw ▸ hnm)) (hp hsupport)
  · rw [Finsupp.filter_apply_neg
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hw]

end


end DegreeFive

end LieRings
