import LieRings.Homological.SymmetricPower
import LieRings.PBW.HigginsPBW
import Mathlib.Algebra.Module.CharacterModule

/-!
# Integral polarization with values in the rational circle

This is the basis-free integral argument needed by the terminal certificate.
The key point is that integral alternation is injective for every Abelian
group, not only for a free one.  Higgins's universal commutator Lie structure
provides its left inverse, after which injectivity of `ℚ/ℤ` extends a character
from the exterior square to the tensor square.
-/

namespace LieRings.IntegralPolarization

open scoped TensorProduct
open LieRings.PBW.Higgins

universe u

noncomputable section

variable (A : Type u) [AddCommGroup A]

abbrev RatCircle := AddCircle (1 : ℚ)
abbrev BilinearForm := A →ₗ[ℤ] A →ₗ[ℤ] RatCircle
abbrev ExteriorForm := (⋀[ℤ]^2 A) →ₗ[ℤ] RatCircle

local notation "T" => TensorAlgebra ℤ A
local notation "E" => ⋀[ℤ]^2 A

private def wedgeTwo (x y : A) : E :=
  exteriorPower.ιMulti ℤ 2 ![x, y]

@[simp] private theorem wedgeTwo_self (x : A) : wedgeTwo A x x = 0 := by
  exact (exteriorPower.ιMulti ℤ 2).map_eq_zero_of_eq ![x, x]
    (i := 0) (j := 1) rfl (by decide)

@[simp] private theorem wedgeTwo_add_left (x y z : A) :
    wedgeTwo A (x + y) z = wedgeTwo A x z + wedgeTwo A y z := by
  have h := (exteriorPower.ιMulti ℤ 2).map_update_add (![0, z]) 0 x y
  convert h using 1

@[simp] private theorem wedgeTwo_add_right (x y z : A) :
    wedgeTwo A x (y + z) = wedgeTwo A x y + wedgeTwo A x z := by
  have h := (exteriorPower.ιMulti ℤ 2).map_update_add (![x, 0]) 1 y z
  convert h using 1

@[simp] private theorem wedgeTwo_zsmul_right (z : ℤ) (x y : A) :
    wedgeTwo A x (z • y) = z • wedgeTwo A x y := by
  have h := (exteriorPower.ιMulti ℤ 2).map_update_smul (![x, 0]) 1 z y
  convert h using 1

private theorem wedgeTwo_skew (x y : A) :
    wedgeTwo A y x = -wedgeTwo A x y := by
  have h := (exteriorPower.ιMulti ℤ 2).map_swap
    (v := ![x, y]) (i := 0) (j := 1) (by decide)
  have hs : (![x, y] : Fin 2 → A) ∘ Equiv.swap 0 1 = ![y, x] := by
    funext i
    fin_cases i <;> rfl
  rw [hs] at h
  exact h

private theorem wedgeTwo_zsmul_left (z : ℤ) (x y : A) :
    wedgeTwo A (z • x) y = z • wedgeTwo A x y := by
  calc
    wedgeTwo A (z • x) y = -wedgeTwo A y (z • x) :=
      wedgeTwo_skew A y (z • x)
    _ = -(z • wedgeTwo A y x) := by rw [wedgeTwo_zsmul_right]
    _ = z • wedgeTwo A x y := by rw [wedgeTwo_skew A, smul_neg, neg_neg]

/-- Augmentation of the tensor algebra, killing its generating module. -/
private def tensorAugmentation : T →ₐ[ℤ] ℤ :=
  TensorAlgebra.lift ℤ (0 : A →ₗ[ℤ] ℤ)

@[simp] private theorem tensorAugmentation_ι (x : A) :
    tensorAugmentation A (TensorAlgebra.ι ℤ x) = 0 := by
  simp [tensorAugmentation]

private def tensorAugmentationOpposite : Tᵐᵒᵖ →+* ℤ where
  toFun a := tensorAugmentation A a.unop
  map_one' := by simp
  map_mul' a b := by
    rw [MulOpposite.unop_mul, map_mul]
    exact mul_comm _ _
  map_zero' := by simp
  map_add' a b := by simp

@[implicit_reducible] private noncomputable def exteriorModule : Module T E :=
  Module.compHom E (tensorAugmentation A).toRingHom

@[implicit_reducible] private noncomputable def exteriorModuleOpposite :
    Module Tᵐᵒᵖ E :=
  Module.compHom E (tensorAugmentationOpposite A)

@[implicit_reducible] private noncomputable def exteriorSMulCommClass :
    letI := exteriorModule A
    letI := exteriorModuleOpposite A
    SMulCommClass T Tᵐᵒᵖ E := by
  letI := exteriorModule A
  letI := exteriorModuleOpposite A
  constructor
  intro a b x
  change tensorAugmentation A a •
      (tensorAugmentationOpposite A b • x) =
    tensorAugmentationOpposite A b • (tensorAugmentation A a • x)
  rw [smul_smul, smul_smul, mul_comm]

private def exteriorBilinear : A →ₗ[ℤ] A →ₗ[ℤ] E where
  toFun x :=
    { toFun := fun y ↦ wedgeTwo A x y
      map_add' := wedgeTwo_add_right A x
      map_smul' := by intro z y; exact wedgeTwo_zsmul_right A z x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    exact wedgeTwo_add_left A x y
  map_smul' := by
    intro z x
    apply LinearMap.ext
    exact wedgeTwo_zsmul_left A z x

private noncomputable def exteriorLieStructure :
    letI := exteriorModule A
    letI := exteriorModuleOpposite A
    letI := exteriorSMulCommClass A
    LieStructure A E := by
  letI := exteriorModule A
  letI := exteriorModuleOpposite A
  letI := exteriorSMulCommClass A
  refine
    { bracket := exteriorBilinear A
      lie_self := wedgeTwo_self A
      balance := ?_
      jacobi := ?_ }
  · intro x y u v t
    change tensorAugmentationOpposite A
          (MulOpposite.op ⁅TensorAlgebra.ι ℤ u, TensorAlgebra.ι ℤ v⁆) •
          (tensorAugmentationOpposite A (MulOpposite.op t) • wedgeTwo A x y) =
        tensorAugmentation A (⁅TensorAlgebra.ι ℤ x, TensorAlgebra.ι ℤ y⁆ * t) •
          wedgeTwo A u v
    simp [tensorAugmentationOpposite, LieRing.of_associative_ring_bracket]
  · intro x y z
    change
      (tensorAugmentationOpposite A (MulOpposite.op (TensorAlgebra.ι ℤ z)) •
            wedgeTwo A x y -
          tensorAugmentation A (TensorAlgebra.ι ℤ z) • wedgeTwo A x y) +
        (tensorAugmentationOpposite A (MulOpposite.op (TensorAlgebra.ι ℤ x)) •
            wedgeTwo A y z -
          tensorAugmentation A (TensorAlgebra.ι ℤ x) • wedgeTwo A y z) +
        (tensorAugmentationOpposite A (MulOpposite.op (TensorAlgebra.ι ℤ y)) •
            wedgeTwo A z x -
          tensorAugmentation A (TensorAlgebra.ι ℤ y) • wedgeTwo A z x) = 0
    simp [tensorAugmentationOpposite]

private def exteriorToCommutatorAlternating :
    A [⋀^Fin 2]→ₗ[ℤ] tensorCommutatorIdeal A where
  toFun v := tensorCommutatorBracket A (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> apply Subtype.ext <;> simp [tensorCommutatorBracketValue, lie_add]
  map_update_smul' v i z x := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change tensorCommutatorBracket A (v 0) (v 1) = 0
      change v 0 = v 1 at hv
      rw [hv]
      apply Subtype.ext
      simp [tensorCommutatorBracketValue]
    · change tensorCommutatorBracket A (v 0) (v 1) = 0
      change v 1 = v 0 at hv
      rw [hv]
      apply Subtype.ext
      simp [tensorCommutatorBracketValue]
    · exact (hij rfl).elim

private def exteriorToCommutator : E →ₗ[ℤ] tensorCommutatorIdeal A :=
  exteriorPower.alternatingMapLinearEquiv (exteriorToCommutatorAlternating A)

@[simp] private theorem exteriorToCommutator_wedge (x y : A) :
    exteriorToCommutator A (wedgeTwo A x y) =
      tensorCommutatorBracket A x y := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (exteriorToCommutatorAlternating A) ![x, y]

private theorem exteriorToCommutator_injective :
    Function.Injective (exteriorToCommutator A) := by
  letI := tensorCommutatorIdealSMulCommClass A
  letI := exteriorModule A
  letI := exteriorModuleOpposite A
  letI := exteriorSMulCommClass A
  obtain ⟨f, _⟩ := tensorCommutatorLieStructure_isUniversal A E
    (exteriorLieStructure A)
  let fℤ : tensorCommutatorIdeal A →ₗ[ℤ] E :=
    f.toLinearMap.restrictScalars ℤ
  have hleft : fℤ.comp (exteriorToCommutator A) = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change f (exteriorToCommutator A (wedgeTwo A (v 0) (v 1))) =
      wedgeTwo A (v 0) (v 1)
    rw [exteriorToCommutator_wedge]
    exact f.map_bracket (v 0) (v 1)
  exact Function.LeftInverse.injective fun x ↦ LinearMap.congr_fun hleft x

private def tensorProductToTensorAlgebra : (A ⊗[ℤ] A) →ₗ[ℤ] T :=
  TensorProduct.lift
    { toFun := fun x ↦
        { toFun := fun y ↦ TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y
          map_add' := by intro y z; simp [mul_add]
          map_smul' := by
            intro z y
            rw [map_smul, mul_smul_comm]
            simp }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        simp [add_mul]
      map_smul' := by
        intro z x
        apply LinearMap.ext
        intro y
        change TensorAlgebra.ι ℤ (z • x) * TensorAlgebra.ι ℤ y =
          z • (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y)
        rw [map_smul]
        exact smul_mul_assoc z (TensorAlgebra.ι ℤ x) (TensorAlgebra.ι ℤ y) }

@[simp] private theorem tensorProductToTensorAlgebra_tmul (x y : A) :
    tensorProductToTensorAlgebra A (x ⊗ₜ[ℤ] y) =
      TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y :=
  TensorProduct.lift.tmul x y

private theorem exteriorToCommutator_coe (z : E) :
    (exteriorToCommutator A z : T) =
      tensorProductToTensorAlgebra A
        (SymmetricPower.exteriorTwoToTensor (R := ℤ) z) := by
  let lhs : E →ₗ[ℤ] T :=
    { toFun := fun z ↦ (exteriorToCommutator A z : T)
      map_add' := by intro x y; simp
      map_smul' := by intro z x; simp }
  let rhs : E →ₗ[ℤ] T :=
    (tensorProductToTensorAlgebra A).comp
      (SymmetricPower.exteriorTwoToTensor (R := ℤ))
  have h : lhs = rhs := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (exteriorToCommutator A (wedgeTwo A (v 0) (v 1)) : T) =
      tensorProductToTensorAlgebra A
        (SymmetricPower.exteriorTwoToTensor (R := ℤ)
          (wedgeTwo A (v 0) (v 1)))
    rw [exteriorToCommutator_wedge]
    change (tensorCommutatorBracket A (v 0) (v 1) : T) =
      tensorProductToTensorAlgebra A
        (SymmetricPower.exteriorTwoToTensor (R := ℤ)
          (exteriorPower.ιMulti ℤ 2 v))
    rw [SymmetricPower.exteriorTwoToTensor_ιMulti, map_sub,
      tensorProductToTensorAlgebra_tmul,
      tensorProductToTensorAlgebra_tmul]
    rfl
  exact LinearMap.congr_fun h z

/-- Integral alternation is injective for every Abelian group. -/
theorem exteriorTwoToTensor_injective :
    Function.Injective
      (SymmetricPower.exteriorTwoToTensor (R := ℤ) (M := A)) := by
  intro x y hxy
  apply exteriorToCommutator_injective A
  apply Subtype.ext
  rw [exteriorToCommutator_coe, exteriorToCommutator_coe, hxy]

/-- Polarization without dividing by two. -/
theorem exists_bilinear_skew_eq (Ω : ExteriorForm A) :
    ∃ H : BilinearForm A,
      ∀ x y, H y x - H x y = Ω (wedgeTwo A x y) := by
  let omegaCharacter : CharacterModule E := (-Ω).toAddMonoidHom
  obtain ⟨tensorCharacter, htensor⟩ :=
    CharacterModule.dual_surjective_of_injective
      (SymmetricPower.exteriorTwoToTensor (R := ℤ) (M := A))
      (exteriorTwoToTensor_injective A) omegaCharacter
  let H : BilinearForm A :=
    { toFun := fun x ↦
        { toFun := fun y ↦ tensorCharacter (x ⊗ₜ[ℤ] y)
          map_add' := by intro y z; rw [TensorProduct.tmul_add, map_add]
          map_smul' := by
            intro z y
            calc
              tensorCharacter (x ⊗ₜ[ℤ] (z • y)) =
                  tensorCharacter (z • (x ⊗ₜ[ℤ] y)) := by
                    rw [TensorProduct.tmul_smul]
                    rfl
              _ = z • tensorCharacter (x ⊗ₜ[ℤ] y) :=
                tensorCharacter.map_zsmul _ _ }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change tensorCharacter ((x + y) ⊗ₜ[ℤ] z) = _
        rw [TensorProduct.add_tmul, map_add]
        rfl
      map_smul' := by
        intro z x
        apply LinearMap.ext
        intro y
        change tensorCharacter ((z • x) ⊗ₜ[ℤ] y) = _
        calc
          tensorCharacter ((z • x) ⊗ₜ[ℤ] y) =
              tensorCharacter (z • (x ⊗ₜ[ℤ] y)) := by
                exact congrArg tensorCharacter
                  (TensorProduct.smul_tmul' (R := ℤ) z x y).symm
          _ = z • tensorCharacter (x ⊗ₜ[ℤ] y) :=
            tensorCharacter.map_zsmul _ _ }
  refine ⟨H, ?_⟩
  intro x y
  have hwedge := congrArg (fun c : CharacterModule E ↦ c (wedgeTwo A x y)) htensor
  change tensorCharacter
      (SymmetricPower.exteriorTwoToTensor (R := ℤ) (wedgeTwo A x y)) =
        -Ω (wedgeTwo A x y) at hwedge
  change tensorCharacter
      (SymmetricPower.exteriorTwoToTensor (R := ℤ)
        (exteriorPower.ιMulti ℤ 2 ![x, y])) =
        -Ω (wedgeTwo A x y) at hwedge
  rw [SymmetricPower.exteriorTwoToTensor_ιMulti, map_sub] at hwedge
  change H x y - H y x = -Ω (wedgeTwo A x y) at hwedge
  apply eq_of_sub_eq_zero
  calc
    (H y x - H x y) - Ω (wedgeTwo A x y) =
        -(H x y - H y x) - Ω (wedgeTwo A x y) := by abel
    _ = 0 := by rw [hwedge]; abel

end

end LieRings.IntegralPolarization
