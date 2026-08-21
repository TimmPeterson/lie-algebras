import LieRings.DimensionSubring.DegreeFive.Reduction
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Finite scalar quotients for the factor-two theorem

Only the scalar-quotient construction used to pass from a finitely generated witness to a
finite Lie ring is retained here.
-/

noncomputable section

namespace LieRings.DegreeFive

universe u

variable (B : Type u) [LieRing B]

/-- The ideal of scalar multiples `nB`. -/
def multipleIdeal (n : ℤ) : LieIdeal ℤ B where
  toSubmodule := LinearMap.range (n • (LinearMap.id : B →ₗ[ℤ] B))
  lie_mem := by
    rintro x y ⟨z, rfl⟩
    refine ⟨⁅x, z⁆, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [lie_smul]

theorem mem_multipleIdeal_iff (n : ℤ) (x : B) :
    x ∈ multipleIdeal B n ↔ ∃ y : B, n • y = x := by
  rfl

abbrev MultipleQuotient (n : ℕ) :=
  B ⧸ multipleIdeal B (n : ℤ)

theorem multipleQuotient_nsmul_eq_zero (n : ℕ)
    (x : MultipleQuotient B n) : n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change (LieSubmodule.Quotient.mk (n • x) : MultipleQuotient B n) = 0
      apply (LieSubmodule.Quotient.mk_eq_zero'
        (N := multipleIdeal B (n : ℤ))).mpr
      exact ⟨x, by simp⟩

theorem multipleQuotient_finite (n : ℕ) (hn : n ≠ 0)
    [Module.Finite ℤ B] : Finite (MultipleQuotient B n) := by
  letI : Module.Finite ℤ (MultipleQuotient B n) :=
    Module.Finite.quotient ℤ (multipleIdeal B (n : ℤ)).toSubmodule
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), ?_⟩, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr (Int.ofNat_ne_zero.mpr hn)
  · simpa using multipleQuotient_nsmul_eq_zero B n x

/-- The elementwise statement `2δ₄ ⊆ γ₄`. -/
def TwoDeltaFourProperty : Prop :=
  ∀ (M : Type u) [LieRing M] (x : M),
    x ∈ dimensionSubring ℤ M 4 → 2 • x ∈ lowerCentralSeries ℤ M 3

end LieRings.DegreeFive
