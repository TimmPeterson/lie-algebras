import LieRings.DimensionSubring.DegreeFive.PresentationResolution
import LieRings.DimensionSubring.DegreeFive.LowSymbols
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The integral exterior-square splitting of the class-two presentation

For `M = P ⊕ ⋀²P`, its second exterior power splits into a low part, a mixed part,
and a high part.  The mixed projection is normalized integrally as

`(p,w) ∧ (p',w') ↦ p ⊗ w' - p' ⊗ w`.

This normalization is important: it contains neither division by two nor an implicit
symmetrization.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (P : Type u) [AddCommGroup P]

local notation "W" => ⋀[ℤ]^2 P
local notation "M" => FreeClassTwo P

/-- Projection to the degree-one summand of the free class-two Lie ring. -/
def freeClassTwoFst : M →ₗ[ℤ] P :=
  LinearMap.fst ℤ P W

/-- Projection to the degree-two summand of the free class-two Lie ring. -/
def freeClassTwoSnd : M →ₗ[ℤ] W :=
  LinearMap.snd ℤ P W

/-- Inclusion of the degree-one summand. -/
def freeClassTwoInl : P →ₗ[ℤ] M :=
  LinearMap.inl ℤ P W

/-- Inclusion of the degree-two summand. -/
def freeClassTwoInr : W →ₗ[ℤ] M :=
  LinearMap.inr ℤ P W

/-- The low `(1,1)` exterior component. -/
def freeClassTwoExteriorLow : ⋀[ℤ]^2 M →ₗ[ℤ] ⋀[ℤ]^2 P :=
  exteriorPower.map 2 (freeClassTwoFst P)

/-- Alternating map defining the mixed `(1,2)` component. -/
def freeClassTwoExteriorMixedAlternating :
    M [⋀^Fin 2]→ₗ[ℤ] (P ⊗[ℤ] W) where
  toFun v := ((v 0).1) ⊗ₜ[ℤ] (v 1).2 - ((v 1).1) ⊗ₜ[ℤ] (v 0).2
  map_update_add' v i x y := by
    fin_cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add] <;> abel
  map_update_smul' v i n x := by
    fin_cases i <;> simp [zsmul_sub] <;>
      rw [← TensorProduct.smul_tmul'] <;> rfl
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (v 0).1 ⊗ₜ[ℤ] (v 1).2 - (v 1).1 ⊗ₜ[ℤ] (v 0).2 = 0
      change v 0 = v 1 at hv
      rw [hv, sub_self]
    · change (v 0).1 ⊗ₜ[ℤ] (v 1).2 - (v 1).1 ⊗ₜ[ℤ] (v 0).2 = 0
      change v 1 = v 0 at hv
      rw [hv, sub_self]
    · exact (hij rfl).elim

/-- The mixed `(1,2)` exterior component. -/
def freeClassTwoExteriorMixed : ⋀[ℤ]^2 M →ₗ[ℤ] (P ⊗[ℤ] W) :=
  exteriorPower.alternatingMapLinearEquiv
    (freeClassTwoExteriorMixedAlternating P)

/-- The high `(2,2)` exterior component. -/
def freeClassTwoExteriorHigh : ⋀[ℤ]^2 M →ₗ[ℤ] ⋀[ℤ]^2 W :=
  exteriorPower.map 2 (freeClassTwoSnd P)

@[simp]
theorem freeClassTwoExteriorLow_wedge (x y : M) :
    freeClassTwoExteriorLow P (wedgeTwo M x y) =
      wedgeTwo P x.1 y.1 := by
  exact exteriorPower.map_apply_ιMulti
    (n := 2) (freeClassTwoFst P) ![x, y]

@[simp]
theorem freeClassTwoExteriorMixed_wedge (x y : M) :
    freeClassTwoExteriorMixed P (wedgeTwo M x y) =
      x.1 ⊗ₜ[ℤ] y.2 - y.1 ⊗ₜ[ℤ] x.2 := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (freeClassTwoExteriorMixedAlternating P) ![x, y]

@[simp]
theorem freeClassTwoExteriorHigh_wedge (x y : M) :
    freeClassTwoExteriorHigh P (wedgeTwo M x y) =
      wedgeTwo W x.2 y.2 := by
  exact exteriorPower.map_apply_ιMulti
    (n := 2) (freeClassTwoSnd P) ![x, y]

/-- Include the low exterior summand. -/
def freeClassTwoExteriorLowInclusion : ⋀[ℤ]^2 P →ₗ[ℤ] ⋀[ℤ]^2 M :=
  exteriorPower.map 2 (freeClassTwoInl P)

/-- Include the mixed tensor summand by `p ⊗ w ↦ (p,0) ∧ (0,w)`. -/
def freeClassTwoExteriorMixedInclusion : (P ⊗[ℤ] W) →ₗ[ℤ] ⋀[ℤ]^2 M :=
  TensorProduct.lift
    { toFun := fun p ↦
        { toFun := fun w ↦ wedgeTwo M (p, 0) (0, w)
          map_add' := by
            intro x y
            simpa using wedgeTwo_add_right M (p, 0) (0, x) (0, y)
          map_smul' := by
            intro n x
            simpa using wedgeTwo_zsmul_right M n (p, 0) (0, x) }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro w
        simpa using wedgeTwo_add_left M (x, 0) (y, 0) (0, w)
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro w
        change (exteriorPower.ιMulti ℤ 2) ![(n • x, 0), (0, w)] = _
        have h := (exteriorPower.ιMulti ℤ 2).map_update_smul
          (![(0 : M), (0, w)]) 0 n (x, 0)
        simpa using h }

/-- Include the high exterior summand. -/
def freeClassTwoExteriorHighInclusion : ⋀[ℤ]^2 W →ₗ[ℤ] ⋀[ℤ]^2 M :=
  exteriorPower.map 2 (freeClassTwoInr P)

@[simp]
theorem freeClassTwoExteriorLowInclusion_wedge (x y : P) :
    freeClassTwoExteriorLowInclusion P (wedgeTwo P x y) =
      wedgeTwo M (x, 0) (y, 0) := by
  exact exteriorPower.map_apply_ιMulti
    (n := 2) (freeClassTwoInl P) ![x, y]

@[simp]
theorem freeClassTwoExteriorMixedInclusion_tmul (x : P) (y : W) :
    freeClassTwoExteriorMixedInclusion P (x ⊗ₜ[ℤ] y) =
      wedgeTwo M (x, 0) (0, y) := by
  exact TensorProduct.lift.tmul x y

@[simp]
theorem freeClassTwoExteriorHighInclusion_wedge (x y : W) :
    freeClassTwoExteriorHighInclusion P (wedgeTwo W x y) =
      wedgeTwo M (0, x) (0, y) := by
  exact exteriorPower.map_apply_ιMulti
    (n := 2) (freeClassTwoInr P) ![x, y]

/-- Reassemble the three integral components. -/
def freeClassTwoExteriorReassemble : ⋀[ℤ]^2 M →ₗ[ℤ] ⋀[ℤ]^2 M :=
  (freeClassTwoExteriorLowInclusion P).comp (freeClassTwoExteriorLow P) +
    (freeClassTwoExteriorMixedInclusion P).comp (freeClassTwoExteriorMixed P) +
      (freeClassTwoExteriorHighInclusion P).comp (freeClassTwoExteriorHigh P)

/-- The low/mixed/high splitting reassembles to the original exterior tensor. -/
theorem freeClassTwoExteriorReassemble_eq_id :
    freeClassTwoExteriorReassemble P = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  let x : M := v 0
  let y : M := v 1
  change freeClassTwoExteriorReassemble P (wedgeTwo M x y) = wedgeTwo M x y
  simp only [freeClassTwoExteriorReassemble, LinearMap.add_apply, LinearMap.comp_apply,
    freeClassTwoExteriorLow_wedge, freeClassTwoExteriorMixed_wedge,
    freeClassTwoExteriorHigh_wedge, freeClassTwoExteriorLowInclusion_wedge,
    freeClassTwoExteriorHighInclusion_wedge, map_sub,
    freeClassTwoExteriorMixedInclusion_tmul]
  change wedgeTwo M (x.1, 0) (y.1, 0) +
      (wedgeTwo M (x.1, 0) (0, y.2) -
        wedgeTwo M (y.1, 0) (0, x.2)) +
      wedgeTwo M (0, x.2) (0, y.2) = wedgeTwo M x y
  have hskew : wedgeTwo M (0, x.2) (y.1, 0) =
      -wedgeTwo M (y.1, 0) (0, x.2) := by
    have h := (exteriorPower.ιMulti ℤ 2).map_swap
      ![(y.1, 0), (0, x.2)] (i := 0) (j := 1) (by decide)
    change wedgeTwo M (0, x.2) (y.1, 0) =
      -wedgeTwo M (y.1, 0) (0, x.2) at h
    exact h
  calc
    wedgeTwo M (x.1, 0) (y.1, 0) +
          (wedgeTwo M (x.1, 0) (0, y.2) -
            wedgeTwo M (y.1, 0) (0, x.2)) +
          wedgeTwo M (0, x.2) (0, y.2) =
        wedgeTwo M ((x.1, 0) + (0, x.2))
          ((y.1, 0) + (0, y.2)) := by
      rw [wedgeTwo_add_left, wedgeTwo_add_right, wedgeTwo_add_right, hskew]
      abel
    _ = wedgeTwo M x y := by
      congr 2 <;> ext <;> simp

/-- Pointwise decomposition into the three exterior components. -/
theorem freeClassTwoExterior_decomposition (z : ⋀[ℤ]^2 M) :
    z = freeClassTwoExteriorLowInclusion P (freeClassTwoExteriorLow P z) +
      freeClassTwoExteriorMixedInclusion P (freeClassTwoExteriorMixed P z) +
        freeClassTwoExteriorHighInclusion P (freeClassTwoExteriorHigh P z) := by
  have h := LinearMap.congr_fun (freeClassTwoExteriorReassemble_eq_id P) z
  simpa [freeClassTwoExteriorReassemble] using h.symm

end

end DegreeFive

end LieRings
