import LieRings.DimensionSubring.MetabelianVanishing.QuadraticPBWBlock
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The low relative row complex

Only the first three terms of the relative Chevalley--Eilenberg complex are
needed by the odd metabelian argument. This file fixes their integral signs
and proves the literal d₁ d₂ = 0 identity. Relation entries are subtypes of
one fixed Lie ideal throughout; no homogeneous component is ever retyped as a
relation.
-/

namespace LieRings.MetabelianVanishing.RelativeRows

open TensorProduct

universe u

noncomputable section

variable {F : Type u} [LieRing F] (R : LieIdeal ℤ F)

/-- Degree zero of the relative row complex. -/
abbrev CZero := UEA ℤ F

/-- Degree one: one full relation on the left of an enveloping word. -/
abbrev COne := R ⊗[ℤ] UEA ℤ F

/-- Degree two, sufficient to record the only relative syzygy used later. -/
abbrev CTwo := (⋀[ℤ]^2 R) ⊗[ℤ] UEA ℤ F

/-- Evaluation of a relation-on-the-left row. -/
def relationIota : R →ₗ[ℤ] UEA ℤ F :=
  (UniversalEnvelopingAlgebra.ι ℤ : LieHom ℤ F (UEA ℤ F)).toLinearMap.comp
    R.subtype

/-- Evaluation of a relation-on-the-left row. -/
def dOne : COne R →ₗ[ℤ] UEA ℤ F :=
  (TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (rho : R) (u : UEA ℤ F) ↦ relationIota R rho * u)
    (by
      intro x y u
      change relationIota R (x + y) * u =
        relationIota R x * u + relationIota R y * u
      rw [map_add, add_mul])
    (by
      intro z x u
      change relationIota R (z • x) * u = z • (relationIota R x * u)
      rw [map_zsmul]
      exact smul_mul_assoc z _ _)
    (by intro x u v; simp [mul_add])
    (by
      intro z x u
      exact mul_smul_comm z _ _))).toAddMonoidHom.toIntLinearMap

@[simp] theorem dOne_tmul (rho : R) (u : UEA ℤ F) :
    dOne R (rho ⊗ₜ[ℤ] u) =
      UniversalEnvelopingAlgebra.ι ℤ (rho : F) * u := rfl

/-- The full-relation bracket. The output remains an actual member of the
same relation ideal. -/
def relationBracket : R →ₗ[ℤ] R →ₗ[ℤ] R :=
  LinearMap.mk₂ ℤ
    (fun rho sigma ↦ ⁅rho, sigma⁆)
    (by intro x y z; simp)
    (by intro z x y; simp)
    (by intro x y z; simp)
    (by intro z x y; simp)

/-- One ordered multiplication term in the relative differential. -/
private def term (rho sigma : R) : UEA ℤ F →ₗ[ℤ] COne R where
  toFun u :=
    rho ⊗ₜ[ℤ] (relationIota R sigma * u)
  map_add' u v := by simp [mul_add, tmul_add]
  map_smul' z u := by
    rw [mul_smul_comm]
    exact tmul_smul z _ _

/-- The bracket term in the relative differential. -/
private def bracketTerm (rho sigma : R) : UEA ℤ F →ₗ[ℤ] COne R where
  toFun u := relationBracket R rho sigma ⊗ₜ[ℤ] u
  map_add' u v := by simp [tmul_add]
  map_smul' z u := tmul_smul z _ _

/-- Bilinearity of the ordered multiplication term in its two relation
entries. -/
private def termMap : R →ₗ[ℤ] R →ₗ[ℤ] (UEA ℤ F →ₗ[ℤ] COne R) :=
  LinearMap.mk₂ ℤ (term R)
    (by intro x y z; ext u; simp [term, add_tmul])
    (by intro z x y; ext u; simp [term, smul_tmul'])
    (by intro x y z; ext u; simp [term, add_mul, tmul_add])
    (by
      intro z x y
      ext u
      change x ⊗ₜ[ℤ] (relationIota R (z • y) * u) =
        z • (x ⊗ₜ[ℤ] (relationIota R y * u))
      rw [map_zsmul, smul_mul_assoc, tmul_smul]
      rfl)

/-- Bilinearity of the full-relation bracket term. -/
private def bracketTermMap : R →ₗ[ℤ] R →ₗ[ℤ] (UEA ℤ F →ₗ[ℤ] COne R) :=
  LinearMap.mk₂ ℤ (bracketTerm R)
    (by
      intro x y z
      ext u
      change relationBracket R (x + y) z ⊗ₜ[ℤ] u =
        relationBracket R x z ⊗ₜ[ℤ] u +
          relationBracket R y z ⊗ₜ[ℤ] u
      rw [map_add, LinearMap.add_apply, add_tmul])
    (by intro z x y; ext u; simp [bracketTerm, relationBracket, smul_tmul'])
    (by
      intro x y z
      ext u
      change relationBracket R x (y + z) ⊗ₜ[ℤ] u =
        relationBracket R x y ⊗ₜ[ℤ] u +
          relationBracket R x z ⊗ₜ[ℤ] u
      rw [map_add]
      change (relationBracket R x y + relationBracket R x z) ⊗ₜ[ℤ] u =
        relationBracket R x y ⊗ₜ[ℤ] u +
          relationBracket R x z ⊗ₜ[ℤ] u
      exact add_tmul _ _ _)
    (by intro z x y; ext u; simp [bracketTerm, relationBracket, smul_tmul'])

/-- The alternating two-relation row before passage to the exterior square. -/
def dTwoAlternating : R [⋀^Fin 2]→ₗ[ℤ] (UEA ℤ F →ₗ[ℤ] COne R) where
  toMultilinearMap :=
    MultilinearMap.mk'
      (fun a ↦ termMap R (a 0) (a 1) - termMap R (a 1) (a 0) -
        bracketTermMap R (a 0) (a 1))
      (by
        intro a i x y
        fin_cases i <;> simp [Function.update] <;> module)
      (by
        intro a i z x
        fin_cases i <;> simp [Function.update] <;> module)
  map_eq_zero_of_eq' := by
    intro a i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change a 0 = a 1 at hij
      change termMap R (a 0) (a 1) - termMap R (a 1) (a 0) -
        bracketTermMap R (a 0) (a 1) = 0
      rw [hij]
      simp only [sub_self, zero_sub]
      apply neg_eq_zero.mpr
      ext u
      simp [bracketTermMap, bracketTerm, relationBracket]
    · change a 1 = a 0 at hij
      change termMap R (a 0) (a 1) - termMap R (a 1) (a 0) -
        bracketTermMap R (a 0) (a 1) = 0
      rw [hij]
      simp only [sub_self, zero_sub]
      apply neg_eq_zero.mpr
      ext u
      simp [bracketTermMap, bracketTerm, relationBracket]
    · exact (hne rfl).elim

/-- Exterior-square version of the alternating two-relation row. -/
def dTwoCore : (⋀[ℤ]^2 R) →ₗ[ℤ] (UEA ℤ F →ₗ[ℤ] COne R) :=
  exteriorPower.alternatingMapLinearEquiv (dTwoAlternating R)

/-- Relative Chevalley--Eilenberg differential in degree two. -/
def dTwo : CTwo R →ₗ[ℤ] COne R :=
  (TensorProduct.lift (dTwoCore R)).toAddMonoidHom.toIntLinearMap

@[simp] theorem dTwo_wedge_tmul (a : Fin 2 → R) (u : UEA ℤ F) :
    dTwo R (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] u) =
      a 0 ⊗ₜ[ℤ] (UniversalEnvelopingAlgebra.ι ℤ (a 1 : F) * u) -
        a 1 ⊗ₜ[ℤ] (UniversalEnvelopingAlgebra.ι ℤ (a 0 : F) * u) -
        relationBracket R (a 0) (a 1) ⊗ₜ[ℤ] u := by
  change dTwoCore R (exteriorPower.ιMulti ℤ 2 a) u = _
  have h := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (dTwoAlternating R) a
  exact DFunLike.congr_fun h u

/-- The literal three-term relative identity. This fixes the bracket sign
used by the marked closed square. -/
theorem dOne_comp_dTwo : (dOne R).comp (dTwo R) = 0 := by
  apply TensorProduct.ext'
  intro w u
  let f : (⋀[ℤ]^2 R) →ₗ[ℤ] UEA ℤ F :=
    ((dOne R).comp (dTwo R)).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^2 R) _).flip u)
  have hf : f = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change dOne R (dTwo R (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] u)) = 0
    rw [dTwo_wedge_tmul, map_sub, map_sub, dOne_tmul, dOne_tmul, dOne_tmul]
    change UniversalEnvelopingAlgebra.ι ℤ (a 0 : F) *
          (UniversalEnvelopingAlgebra.ι ℤ (a 1 : F) * u) -
        UniversalEnvelopingAlgebra.ι ℤ (a 1 : F) *
          (UniversalEnvelopingAlgebra.ι ℤ (a 0 : F) * u) -
        UniversalEnvelopingAlgebra.ι ℤ
          (⁅(a 0 : F), (a 1 : F)⁆) * u = 0
    rw [← mul_assoc, ← mul_assoc]
    rw [LieRings.DegreeFive.iota_mul_iota_swap ℤ F (a 0 : F) (a 1 : F)]
    noncomm_ring
  have hw := LinearMap.congr_fun hf w
  simpa [f, LinearMap.comp_apply] using hw

/-- The range of d₁ is precisely the elements represented by relative rows. -/
theorem mem_range_dOne_iff (x : UEA ℤ F) :
    x ∈ LinearMap.range (dOne R) ↔
      ∃ c : COne R, dOne R c = x := by
  rfl

end

end LieRings.MetabelianVanishing.RelativeRows
