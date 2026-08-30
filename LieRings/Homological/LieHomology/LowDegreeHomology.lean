import LieRings.Homological.LieHomology.Complex
import LieRings.Homological.LieHomology.LowDegree

/-!
# Zeroth and first Chevalley--Eilenberg homology

This file identifies the first two homology objects of the all-degree CE complex with their
standard descriptions:

* `H₀(L; R) ≃ R` for trivial coefficients;
* `H₁(L; R) ≃ L / [L,L]`.

The concrete cycle and boundary modules below are aliases of Mathlib's short-complex homology
data. This keeps the formulas definitionally connected to the all-degree complex.
-/

open CategoryTheory

universe u v

namespace LieRings.Homological.LieHomology

noncomputable section

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-! ## Degree zero -/

private abbrev zerothShortComplex := (complex R L).sc' 1 0 0

/-- Degree-zero cycles in Mathlib's concrete short-complex model. -/
abbrev zerothCycles : Submodule R (⋀[R]^0 L) :=
  LinearMap.ker (zerothShortComplex R L).g.hom

/-- The degree-one boundary with codomain restricted to degree-zero cycles. -/
abbrev firstBoundaryToZerothCycles :
    (⋀[R]^1 L) →ₗ[R] zerothCycles R L :=
  (zerothShortComplex R L).moduleCatToCycles

/-- Mathlib's concrete cycles-modulo-boundaries model of zeroth CE homology. -/
abbrev ZerothHomology :=
  zerothCycles R L ⧸ LinearMap.range (firstBoundaryToZerothCycles R L)

/-- The abstract degree-zero homology of `complex R L` is its concrete quotient model. -/
noncomputable def zerothHomologyConcreteIso :
    homology (R := R) (L := L) 0 ≅ ModuleCat.of R (ZerothHomology R L) :=
  (complex R L).homologyIsoSc' 1 0 0
      (by simpa using ChainComplex.prev ℕ 0)
      ChainComplex.next_nat_zero ≪≫
    (zerothShortComplex R L).moduleCatHomologyIso

private def zerothCyclesEquivExteriorZero :
    zerothCycles R L ≃ₗ[R] (⋀[R]^0 L) :=
  LinearEquiv.ofBijective (zerothCycles R L).subtype
    ⟨Submodule.injective_subtype _, fun z => ⟨⟨z, by
      change (complex R L).d 0 0 z = 0
      rw [(complex R L).shape 0 0 (by simp)]
      rfl⟩, rfl⟩⟩

private theorem zerothBoundaries_eq_bot :
    LinearMap.range (firstBoundaryToZerothCycles R L) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change differential R L 0 z = 0
  rw [differential_zero, LinearMap.zero_apply]

/-- The usual formula `H₀(L; R) ≃ R` for trivial coefficients. -/
def zerothHomologyEquivBaseRing : ZerothHomology R L ≃ₗ[R] R :=
  ((LinearMap.range (firstBoundaryToZerothCycles R L)).quotEquivOfEqBot
      (zerothBoundaries_eq_bot R L)).trans
    ((zerothCyclesEquivExteriorZero R L).trans (exteriorPower.zeroEquiv R L))

/-- The all-degree CE homology object in degree zero is the base ring. -/
def homologyZeroEquivBaseRing : Homology (R := R) (L := L) 0 ≃ₗ[R] R :=
  (zerothHomologyConcreteIso R L).toLinearEquiv.trans
    (zerothHomologyEquivBaseRing R L)

/-! ## Degree one -/

private abbrev firstShortComplex := (complex R L).sc' 2 1 0

/-- Degree-one cycles in Mathlib's concrete short-complex model. -/
abbrev firstCycles : Submodule R (⋀[R]^1 L) :=
  LinearMap.ker (firstShortComplex R L).g.hom

/-- The degree-two boundary with codomain restricted to one-cycles. -/
abbrev secondBoundaryToFirstCycles :
    (⋀[R]^2 L) →ₗ[R] firstCycles R L :=
  (firstShortComplex R L).moduleCatToCycles

/-- Mathlib's concrete cycles-modulo-boundaries model of first CE homology. -/
abbrev FirstHomology :=
  firstCycles R L ⧸ LinearMap.range (secondBoundaryToFirstCycles R L)

/-- The abstract degree-one homology of `complex R L` is its concrete quotient model. -/
noncomputable def firstHomologyConcreteIso :
    homology (R := R) (L := L) 1 ≅ ModuleCat.of R (FirstHomology R L) :=
  (complex R L).homologyIsoSc' 2 1 0
      (by simpa using ChainComplex.prev ℕ 1)
      (by simpa using ChainComplex.next_nat_succ 0) ≪≫
    (firstShortComplex R L).moduleCatHomologyIso

private def firstCyclesEquivLie : firstCycles R L ≃ₗ[R] L where
  toFun z := exteriorPower.oneEquiv R L z.1
  invFun z := ⟨(exteriorPower.oneEquiv R L).symm z, by
    change differential R L 0 ((exteriorPower.oneEquiv R L).symm z) = 0
    rw [differential_zero, LinearMap.zero_apply]⟩
  left_inv z := by
    apply Subtype.ext
    exact (exteriorPower.oneEquiv R L).symm_apply_apply z.1
  right_inv z := (exteriorPower.oneEquiv R L).apply_symm_apply z
  map_add' a b := map_add (exteriorPower.oneEquiv R L) a.1 b.1
  map_smul' r a := map_smul (exteriorPower.oneEquiv R L) r a.1

private theorem firstCyclesEquivLie_boundary (z : ⋀[R]^2 L) :
    firstCyclesEquivLie R L (secondBoundaryToFirstCycles R L z) =
      degreeTwoBoundary R L z := by
  rfl

/-- The abelianization `L/[L,L]`. -/
abbrev Abelianization :=
  L ⧸ (⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆).toSubmodule

private theorem firstBoundaries_map_eq_derived :
    (LinearMap.range (secondBoundaryToFirstCycles R L)).map
        (firstCyclesEquivLie R L).toLinearMap =
      (⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆).toSubmodule := by
  apply le_antisymm
  · rintro y ⟨z, ⟨x, rfl⟩, rfl⟩
    change firstCyclesEquivLie R L (secondBoundaryToFirstCycles R L x) ∈
      (⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆).toSubmodule
    rw [firstCyclesEquivLie_boundary]
    have hx : degreeTwoBoundary R L x ∈
        LinearMap.range (degreeTwoBoundary R L) := ⟨x, rfl⟩
    rw [range_degreeTwoBoundary R L] at hx
    exact hx
  · intro y hy
    have hy' : y ∈ LinearMap.range (degreeTwoBoundary R L) := by
      rw [range_degreeTwoBoundary R L]
      exact hy
    obtain ⟨x, hx⟩ := hy'
    let z : firstCycles R L := secondBoundaryToFirstCycles R L x
    refine ⟨z, ⟨x, rfl⟩, ?_⟩
    change firstCyclesEquivLie R L z = y
    dsimp [z]
    rw [firstCyclesEquivLie_boundary]
    exact hx

/-- The usual formula `H₁(L; R) ≃ L/[L,L]`. -/
def firstHomologyEquivAbelianization :
    FirstHomology R L ≃ₗ[R] Abelianization R L :=
  Submodule.Quotient.equiv
    (LinearMap.range (secondBoundaryToFirstCycles R L))
    (⁅(⊤ : LieIdeal R L), (⊤ : LieIdeal R L)⁆).toSubmodule
    (firstCyclesEquivLie R L) (firstBoundaries_map_eq_derived R L)

/-- The all-degree CE homology object in degree one is the abelianization. -/
def homologyOneEquivAbelianization :
    Homology (R := R) (L := L) 1 ≃ₗ[R] Abelianization R L :=
  (firstHomologyConcreteIso R L).toLinearEquiv.trans
    (firstHomologyEquivAbelianization R L)

end

end LieRings.Homological.LieHomology
