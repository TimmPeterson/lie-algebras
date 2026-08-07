import LieRings.DimensionSubring.DegreeFive.LowSymbols
import LieRings.PBW.HigginsPBW
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Integral alternation on a free module

For a free integral module `M`, the usual map

`⋀²M → M ⊗ M`,  `x ∧ y ↦ x ⊗ y - y ⊗ x`

has an explicit left inverse.  The construction keeps the coefficient of the ordered tensor
`b i ⊗ b j` only when `i < j`.  In particular, no division by two is used.
-/

namespace LieRings

open scoped TensorProduct

universe u v

namespace DegreeFive

noncomputable section

variable {ι : Type u} [LinearOrder ι]
variable {M : Type v} [AddCommGroup M]

/-- Bilinear ordered-wedge collector attached to an integral basis. -/
def orderedWedgeBilinear (b : Module.Basis ι ℤ M) :
    M →ₗ[ℤ] M →ₗ[ℤ] ⋀[ℤ]^2 M :=
  b.constr ℤ fun i ↦
    b.constr ℤ fun j ↦
      if i < j then wedgeTwo M (b i) (b j) else 0

@[simp]
theorem orderedWedgeBilinear_basis (b : Module.Basis ι ℤ M) (i j : ι) :
    orderedWedgeBilinear b (b i) (b j) =
      if i < j then wedgeTwo M (b i) (b j) else 0 := by
  simp [orderedWedgeBilinear]

/-- Keep only the strictly ordered half of a tensor, interpreting it as an exterior tensor. -/
def orderedWedgeSection (b : Module.Basis ι ℤ M) :
    (M ⊗[ℤ] M) →ₗ[ℤ] ⋀[ℤ]^2 M :=
  TensorProduct.lift (orderedWedgeBilinear b)

@[simp]
theorem orderedWedgeSection_tmul
    (b : Module.Basis ι ℤ M) (x y : M) :
    orderedWedgeSection b (x ⊗ₜ[ℤ] y) = orderedWedgeBilinear b x y := by
  exact TensorProduct.lift.tmul x y

theorem wedgeTwo_skew (x y : M) :
    wedgeTwo M y x = -wedgeTwo M x y := by
  have h := (exteriorPower.ιMulti ℤ 2).map_swap
    (v := ![x, y]) (i := 0) (j := 1) (by decide)
  have hswap : (![x, y] : Fin 2 → M) ∘ Equiv.swap 0 1 = ![y, x] := by
    funext i
    fin_cases i <;> rfl
  rw [hswap] at h
  exact h

theorem wedgeTwo_zsmul_left (n : ℤ) (x y : M) :
    wedgeTwo M (n • x) y = n • wedgeTwo M x y := by
  calc
    wedgeTwo M (n • x) y = -wedgeTwo M y (n • x) := by
      exact wedgeTwo_skew (M := M) y (n • x)
    _ = -(n • wedgeTwo M y x) := by rw [wedgeTwo_zsmul_right]
    _ = n • wedgeTwo M x y := by rw [wedgeTwo_skew, smul_neg, neg_neg]

/-- The ordered-half collector is a left inverse to integral alternation. -/
theorem orderedWedgeSection_comp_exteriorToTensor
    (b : Module.Basis ι ℤ M) :
    (orderedWedgeSection b).comp (exteriorToTensor M) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change orderedWedgeSection b
      (exteriorToTensor M (wedgeTwo M (v 0) (v 1))) =
    wedgeTwo M (v 0) (v 1)
  let f : M →ₗ[ℤ] M →ₗ[ℤ] ⋀[ℤ]^2 M :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            orderedWedgeSection b
              (exteriorToTensor M (wedgeTwo M x y))
          map_add' := by intro y z; simp
          map_smul' := by intro n y; simp }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        simp
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro y
        change orderedWedgeSection b
            (exteriorToTensor M (wedgeTwo M (n • x) y)) =
          n • orderedWedgeSection b
            (exteriorToTensor M (wedgeTwo M x y))
        rw [wedgeTwo_zsmul_left, map_smul, map_smul] }
  let g : M →ₗ[ℤ] M →ₗ[ℤ] ⋀[ℤ]^2 M :=
    { toFun := fun x ↦
        { toFun := fun y ↦ wedgeTwo M x y
          map_add' := wedgeTwo_add_right M x
          map_smul' := by
            intro n y
            exact wedgeTwo_zsmul_right M n x y }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        exact wedgeTwo_add_left M x y z
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro y
        change wedgeTwo M (n • x) y = n • wedgeTwo M x y
        exact wedgeTwo_zsmul_left (M := M) n x y }
  have hfg : f = g := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change orderedWedgeSection b
        (exteriorToTensor M (wedgeTwo M (b i) (b j))) =
      wedgeTwo M (b i) (b j)
    rw [exteriorToTensor_wedge, map_sub, orderedWedgeSection_tmul,
      orderedWedgeSection_tmul, orderedWedgeBilinear_basis,
      orderedWedgeBilinear_basis]
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [if_pos hij, if_neg (not_lt_of_ge (le_of_lt hij)), sub_zero]
    · subst j
      rw [sub_self, wedgeTwo_self]
    · have hnot : ¬i < j := not_lt_of_ge (le_of_lt hij)
      rw [if_neg hnot, if_pos hij, zero_sub, wedgeTwo_skew, neg_neg]
  have hv := DFunLike.congr_fun (DFunLike.congr_fun hfg (v 0)) (v 1)
  exact hv

/-- Integral alternation is injective on every free Abelian group. -/
theorem exteriorToTensor_injective_of_basis (b : Module.Basis ι ℤ M) :
    Function.Injective (exteriorToTensor M) := by
  apply Function.LeftInverse.injective (g := orderedWedgeSection b)
  intro x
  exact LinearMap.congr_fun (orderedWedgeSection_comp_exteriorToTensor b) x

/-! ## Exactness against ordered quadratic tensors -/

/-- Replace a basis tensor by the same tensor with its two indices in nondecreasing order. -/
def orderedTensorBilinear (b : Module.Basis ι ℤ M) :
    M →ₗ[ℤ] M →ₗ[ℤ] (M ⊗[ℤ] M) :=
  b.constr ℤ fun i ↦
    b.constr ℤ fun j ↦
      if i ≤ j then b i ⊗ₜ[ℤ] b j else b j ⊗ₜ[ℤ] b i

@[simp]
theorem orderedTensorBilinear_basis
    (b : Module.Basis ι ℤ M) (i j : ι) :
    orderedTensorBilinear b (b i) (b j) =
      if i ≤ j then b i ⊗ₜ[ℤ] b j else b j ⊗ₜ[ℤ] b i := by
  simp [orderedTensorBilinear]

/-- Quadratic PBW ordering on the tensor square. -/
def orderedTensorNormal (b : Module.Basis ι ℤ M) :
    (M ⊗[ℤ] M) →ₗ[ℤ] (M ⊗[ℤ] M) :=
  TensorProduct.lift (orderedTensorBilinear b)

@[simp]
theorem orderedTensorNormal_tmul
    (b : Module.Basis ι ℤ M) (x y : M) :
    orderedTensorNormal b (x ⊗ₜ[ℤ] y) = orderedTensorBilinear b x y := by
  exact TensorProduct.lift.tmul x y

/-- On an ordered basis tensor, return the tensor missing from its alternation: the transpose
off the diagonal and the tensor itself on the diagonal. -/
def orderedTensorComplementBilinear (b : Module.Basis ι ℤ M) :
    M →ₗ[ℤ] M →ₗ[ℤ] (M ⊗[ℤ] M) :=
  b.constr ℤ fun i ↦
    b.constr ℤ fun j ↦
      if i < j then b j ⊗ₜ[ℤ] b i else b i ⊗ₜ[ℤ] b j

@[simp]
theorem orderedTensorComplementBilinear_basis
    (b : Module.Basis ι ℤ M) (i j : ι) :
    orderedTensorComplementBilinear b (b i) (b j) =
      if i < j then b j ⊗ₜ[ℤ] b i else b i ⊗ₜ[ℤ] b j := by
  simp [orderedTensorComplementBilinear]

def orderedTensorComplement (b : Module.Basis ι ℤ M) :
    (M ⊗[ℤ] M) →ₗ[ℤ] (M ⊗[ℤ] M) :=
  TensorProduct.lift (orderedTensorComplementBilinear b)

@[simp]
theorem orderedTensorComplement_tmul
    (b : Module.Basis ι ℤ M) (x y : M) :
    orderedTensorComplement b (x ⊗ₜ[ℤ] y) =
      orderedTensorComplementBilinear b x y := by
  exact TensorProduct.lift.tmul x y

/-- Every tensor is its alternating ordered half plus a linear function of its quadratic PBW
normal form. -/
theorem exteriorToTensor_section_add_complement_normal
    (b : Module.Basis ι ℤ M) :
    (exteriorToTensor M).comp (orderedWedgeSection b) +
        (orderedTensorComplement b).comp (orderedTensorNormal b) =
      LinearMap.id := by
  apply (b.tensorProduct b).ext
  rintro ⟨i, j⟩
  rw [Module.Basis.tensorProduct_apply]
  change exteriorToTensor M
        (orderedWedgeSection b (b i ⊗ₜ[ℤ] b j)) +
      orderedTensorComplement b
        (orderedTensorNormal b (b i ⊗ₜ[ℤ] b j)) =
    b i ⊗ₜ[ℤ] b j
  simp only [orderedWedgeSection_tmul,
    orderedWedgeBilinear_basis, orderedTensorNormal_tmul,
    orderedTensorBilinear_basis]
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [if_pos hij, exteriorToTensor_wedge, if_pos (le_of_lt hij),
      orderedTensorComplement_tmul,
      orderedTensorComplementBilinear_basis, if_pos hij]
    abel
  · subst j
    rw [if_neg (lt_irrefl i), map_zero, if_pos le_rfl,
      orderedTensorComplement_tmul,
      orderedTensorComplementBilinear_basis, if_neg (lt_irrefl i), zero_add]
  · have hnotlt : ¬i < j := not_lt_of_ge (le_of_lt hij)
    have hnle : ¬i ≤ j := not_le_of_gt hij
    rw [if_neg hnotlt, map_zero, if_neg hnle,
      orderedTensorComplement_tmul,
      orderedTensorComplementBilinear_basis, if_pos hij, zero_add]

/-- A tensor with zero ordered quadratic PBW normal form is uniquely an integral alternating
tensor. -/
theorem exteriorToTensor_orderedWedgeSection_of_normal_eq_zero
    (b : Module.Basis ι ℤ M) (t : M ⊗[ℤ] M)
    (ht : orderedTensorNormal b t = 0) :
    exteriorToTensor M (orderedWedgeSection b t) = t := by
  have h := LinearMap.congr_fun
    (exteriorToTensor_section_add_complement_normal b) t
  simpa [ht] using h

theorem exists_exteriorToTensor_eq_of_orderedTensorNormal_eq_zero
    (b : Module.Basis ι ℤ M) (t : M ⊗[ℤ] M)
    (ht : orderedTensorNormal b t = 0) :
    ∃ beta : ⋀[ℤ]^2 M, exteriorToTensor M beta = t :=
  ⟨orderedWedgeSection b t,
    exteriorToTensor_orderedWedgeSection_of_normal_eq_zero b t ht⟩

/-! ## Alternation is injective for every Abelian group -/

namespace IntegralAlternation

open LieRings.PBW.Higgins

local notation "T" => TensorAlgebra ℤ M
local notation "E" => ⋀[ℤ]^2 M

/-- Augmentation of the tensor algebra, killing the generating module. -/
def tensorAugmentation : T →ₐ[ℤ] ℤ :=
  TensorAlgebra.lift ℤ (0 : M →ₗ[ℤ] ℤ)

@[simp]
theorem tensorAugmentation_ι (x : M) :
    tensorAugmentation (M := M) (TensorAlgebra.ι ℤ x) = 0 := by
  simp [tensorAugmentation]

/-- The same augmentation on the opposite tensor algebra. -/
def tensorAugmentationOpposite : Tᵐᵒᵖ →+* ℤ where
  toFun a := tensorAugmentation (M := M) a.unop
  map_one' := by simp
  map_mul' a b := by
    rw [MulOpposite.unop_mul, map_mul]
    exact mul_comm _ _
  map_zero' := by simp
  map_add' a b := by simp

/-- The tensor algebra acts on `⋀²M` through augmentation. -/
@[implicit_reducible] noncomputable def exteriorModule : Module T E :=
  Module.compHom E (tensorAugmentation (M := M)).toRingHom

/-- The opposite tensor algebra acts through the same augmentation. -/
@[implicit_reducible] noncomputable def exteriorModuleOpposite : Module Tᵐᵒᵖ E :=
  Module.compHom E (tensorAugmentationOpposite (M := M))

@[implicit_reducible] noncomputable def exteriorSMulCommClass :
    letI := exteriorModule (M := M)
    letI := exteriorModuleOpposite (M := M)
    SMulCommClass T Tᵐᵒᵖ E := by
  letI := exteriorModule (M := M)
  letI := exteriorModuleOpposite (M := M)
  constructor
  intro a b x
  change tensorAugmentation (M := M) a •
      (tensorAugmentationOpposite (M := M) b • x) =
    tensorAugmentationOpposite (M := M) b •
      (tensorAugmentation (M := M) a • x)
  rw [smul_smul, smul_smul, mul_comm]

/-- The universal exterior bracket, as a curried bilinear map. -/
def exteriorBilinear : M →ₗ[ℤ] M →ₗ[ℤ] E where
  toFun x :=
    { toFun := fun y ↦ wedgeTwo M x y
      map_add' := wedgeTwo_add_right M x
      map_smul' := by
        intro n y
        exact wedgeTwo_zsmul_right M n x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact wedgeTwo_add_left M x y z
  map_smul' := by
    intro n x
    apply LinearMap.ext
    intro y
    exact wedgeTwo_zsmul_left (M := M) n x y

/-- Exterior square with augmentation actions is a Higgins Lie structure. -/
noncomputable def exteriorLieStructure :
    letI := exteriorModule (M := M)
    letI := exteriorModuleOpposite (M := M)
    letI := exteriorSMulCommClass (M := M)
    LieStructure M E := by
  letI := exteriorModule (M := M)
  letI := exteriorModuleOpposite (M := M)
  letI := exteriorSMulCommClass (M := M)
  refine
    { bracket := exteriorBilinear (M := M)
      lie_self := ?_
      balance := ?_
      jacobi := ?_ }
  · exact wedgeTwo_self M
  · intro x y u v t
    change tensorAugmentationOpposite (M := M)
          (MulOpposite.op
            ⁅TensorAlgebra.ι ℤ u, TensorAlgebra.ι ℤ v⁆) •
          (tensorAugmentationOpposite (M := M) (MulOpposite.op t) •
            wedgeTwo M x y) =
        tensorAugmentation (M := M)
          (⁅TensorAlgebra.ι ℤ x, TensorAlgebra.ι ℤ y⁆ * t) •
          wedgeTwo M u v
    simp [tensorAugmentationOpposite, LieRing.of_associative_ring_bracket]
  · intro x y z
    change
      (tensorAugmentationOpposite (M := M)
            (MulOpposite.op (TensorAlgebra.ι ℤ z)) • wedgeTwo M x y -
          tensorAugmentation (M := M) (TensorAlgebra.ι ℤ z) •
            wedgeTwo M x y) +
        (tensorAugmentationOpposite (M := M)
            (MulOpposite.op (TensorAlgebra.ι ℤ x)) • wedgeTwo M y z -
          tensorAugmentation (M := M) (TensorAlgebra.ι ℤ x) •
            wedgeTwo M y z) +
        (tensorAugmentationOpposite (M := M)
            (MulOpposite.op (TensorAlgebra.ι ℤ y)) • wedgeTwo M z x -
          tensorAugmentation (M := M) (TensorAlgebra.ι ℤ y) •
            wedgeTwo M z x) = 0
    simp [tensorAugmentationOpposite]

/-- Exterior tensor mapped to the concrete tensor-commutator ideal. -/
def exteriorToTensorCommutatorAlternating :
    M [⋀^Fin 2]→ₗ[ℤ] tensorCommutatorIdeal M where
  toFun v := tensorCommutatorBracket M (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> apply Subtype.ext <;>
      simp [tensorCommutatorBracketValue, lie_add]
  map_update_smul' v i n x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change tensorCommutatorBracket M (v 0) (v 1) = 0
      change v 0 = v 1 at hv
      rw [hv]
      apply Subtype.ext
      simp [tensorCommutatorBracketValue]
    · change tensorCommutatorBracket M (v 0) (v 1) = 0
      change v 1 = v 0 at hv
      rw [hv]
      apply Subtype.ext
      simp [tensorCommutatorBracketValue]
    · exact (hij rfl).elim

def exteriorToTensorCommutatorIdeal :
    E →ₗ[ℤ] tensorCommutatorIdeal M :=
  exteriorPower.alternatingMapLinearEquiv
    (exteriorToTensorCommutatorAlternating (M := M))

@[simp]
theorem exteriorToTensorCommutatorIdeal_wedge (x y : M) :
    exteriorToTensorCommutatorIdeal (M := M) (wedgeTwo M x y) =
      tensorCommutatorBracket M x y := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (exteriorToTensorCommutatorAlternating (M := M)) ![x, y]

/-- Universality of Higgins's concrete commutator structure supplies a left inverse to the
exterior commutator map. -/
theorem exteriorToTensorCommutatorIdeal_injective :
    Function.Injective (exteriorToTensorCommutatorIdeal (M := M)) := by
  letI := tensorCommutatorIdealSMulCommClass M
  letI := exteriorModule (M := M)
  letI := exteriorModuleOpposite (M := M)
  letI := exteriorSMulCommClass (M := M)
  obtain ⟨f, hf⟩ := tensorCommutatorLieStructure_isUniversal M E
    (exteriorLieStructure (M := M))
  let fℤ : tensorCommutatorIdeal M →ₗ[ℤ] E :=
    f.toLinearMap.restrictScalars ℤ
  have hleft : fℤ.comp (exteriorToTensorCommutatorIdeal (M := M)) =
      LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change f (exteriorToTensorCommutatorIdeal (M := M)
        (wedgeTwo M (v 0) (v 1))) = wedgeTwo M (v 0) (v 1)
    rw [exteriorToTensorCommutatorIdeal_wedge]
    exact f.map_bracket (v 0) (v 1)
  apply Function.LeftInverse.injective (g := fℤ)
  intro x
  exact LinearMap.congr_fun hleft x

/-- Multiply an ordered tensor inside the tensor algebra. -/
def tensorProductToTensorAlgebra : (M ⊗[ℤ] M) →ₗ[ℤ] T :=
  TensorProduct.lift
    { toFun := fun x ↦
        { toFun := fun y ↦ TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y
          map_add' := by intro y z; simp [mul_add]
          map_smul' := by
            intro n y
            rw [map_smul, mul_smul_comm]
            simp }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        simp [add_mul]
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro y
        change TensorAlgebra.ι ℤ (n • x) * TensorAlgebra.ι ℤ y =
          n • (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y)
        rw [map_smul]
        exact smul_mul_assoc n (TensorAlgebra.ι ℤ x) (TensorAlgebra.ι ℤ y) }

@[simp]
theorem tensorProductToTensorAlgebra_tmul (x y : M) :
    tensorProductToTensorAlgebra (M := M) (x ⊗ₜ[ℤ] y) =
      TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y := by
  exact TensorProduct.lift.tmul x y

/-- The underlying tensor-algebra value of the exterior commutator is multiplication of its
integral alternating tensor. -/
theorem exteriorToTensorCommutatorIdeal_coe (z : E) :
    (exteriorToTensorCommutatorIdeal (M := M) z : T) =
      tensorProductToTensorAlgebra (M := M) (exteriorToTensor M z) := by
  let lhs : E →ₗ[ℤ] T :=
    { toFun := fun z ↦ (exteriorToTensorCommutatorIdeal (M := M) z : T)
      map_add' := by intro x y; simp
      map_smul' := by intro n x; simp }
  let rhs : E →ₗ[ℤ] T :=
    (tensorProductToTensorAlgebra (M := M)).comp (exteriorToTensor M)
  have h : lhs = rhs := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (exteriorToTensorCommutatorIdeal (M := M)
        (wedgeTwo M (v 0) (v 1)) : T) =
      tensorProductToTensorAlgebra (M := M)
        (exteriorToTensor M (wedgeTwo M (v 0) (v 1)))
    rw [exteriorToTensorCommutatorIdeal_wedge, exteriorToTensor_wedge,
      map_sub, tensorProductToTensorAlgebra_tmul,
      tensorProductToTensorAlgebra_tmul]
    rfl
  exact LinearMap.congr_fun h z

/-- **Integral alternation is injective for every Abelian group.** -/
theorem exteriorToTensor_injective : Function.Injective (exteriorToTensor M) := by
  intro x y hxy
  apply exteriorToTensorCommutatorIdeal_injective (M := M)
  apply Subtype.ext
  rw [exteriorToTensorCommutatorIdeal_coe,
    exteriorToTensorCommutatorIdeal_coe, hxy]

end IntegralAlternation

end

end DegreeFive

end LieRings
