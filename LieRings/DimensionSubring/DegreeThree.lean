import LieRings.DimensionSubring.DegreeTwo
import LieRings.PBW.HigginsPBW
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# The third Lie dimension subring

This file proves the integral theorem `delta_3(L) = gamma_3(L)` for every Lie ring.  The proof
uses Higgins's universal commutator structure to polarize the bracket of the abelianization.  An
injective Abelian overgroup extends that polarization, producing a faithful three-step triangular
representation modulo `gamma_3`.  The cube of the augmentation ideal acts trivially in this
representation.
-/

namespace LieRings

universe u

namespace DegreeThree

noncomputable section

variable (L : Type u) [LieRing L]

/-- The copy of `gamma_3(L)` inside `gamma_2(L)`. -/
def gammaThreeInGammaTwo : Submodule ℤ (lowerCentralSeries ℤ L 1) :=
  (lowerCentralSeries ℤ L 2).toSubmodule.comap
    (lowerCentralSeries ℤ L 1).toSubmodule.subtype

/-- The degree-two lower-central quotient `gamma_2(L) / gamma_3(L)`. -/
abbrev GammaTwoQuotient :=
  (lowerCentralSeries ℤ L 1) ⧸ gammaThreeInGammaTwo L

/-- The abelianization `L / gamma_2(L)`. -/
abbrev Abelianization := L ⧸ lowerCentralSeries ℤ L 1

/-- A chosen embedding of `gamma_2/gamma_3` into an injective Abelian group. -/
def injectivePresentation :
    CategoryTheory.InjectivePresentation (ModuleCat.of ℤ (GammaTwoQuotient L)) :=
  Classical.choice (CategoryTheory.EnoughInjectives.presentation
    (ModuleCat.of ℤ (GammaTwoQuotient L)))

/-- The injective Abelian target used by the triangular representation.

This one-field wrapper separates the carrier from `ModuleCat`'s bundled module instance and thus
avoids an otherwise pervasive (but mathematically harmless) integral-module instance diamond.
-/
structure InjectiveTarget where
  down : (injectivePresentation L).J

/-- The underlying equivalence of the wrapped target with the chosen injective object. -/
def injectiveTargetEquivType :
    InjectiveTarget L ≃ (injectivePresentation L).J where
  toFun := InjectiveTarget.down
  invFun := InjectiveTarget.mk
  left_inv _ := rfl
  right_inv _ := rfl

local instance injectiveTargetAddCommGroup : AddCommGroup (InjectiveTarget L) :=
  (injectiveTargetEquivType L).addCommGroup

local instance injectivePresentationTargetInjective :
    CategoryTheory.Injective
      (ModuleCat.of ℤ ((injectivePresentation L).J : Type u)) :=
  (injectivePresentation L).injective

/-- The wrapped injective target is additively equivalent to the chosen `ModuleCat` object. -/
def injectiveTargetAddEquiv :
    InjectiveTarget L ≃+ (injectivePresentation L).J where
  toEquiv := injectiveTargetEquivType L
  map_add' _ _ := rfl

/-- The integral-linear form of `injectiveTargetAddEquiv`. -/
def injectiveTargetEquiv :
    InjectiveTarget L ≃ₗ[ℤ] (injectivePresentation L).J :=
  (injectiveTargetAddEquiv L).toIntLinearEquiv

local instance injectiveTargetInjectiveModule :
    Module.Injective ℤ (InjectiveTarget L) :=
  { out := by
      intro P P' _ _ _ _ f hf g
      let injJ : Module.Injective ℤ (injectivePresentation L).J :=
        Module.injective_module_of_injective_object ℤ (injectivePresentation L).J
      obtain ⟨h, hh⟩ := injJ.out f hf ((injectiveTargetEquiv L).toLinearMap.comp g)
      refine ⟨(injectiveTargetEquiv L).symm.toLinearMap.comp h, fun x ↦ ?_⟩
      apply (injectiveTargetEquiv L).injective
      simpa only [LinearEquiv.apply_symm_apply] using hh x }

/-- The chosen injective map `gamma_2/gamma_3 → C`. -/
def gammaTwoQuotientEmbedding :
    GammaTwoQuotient L →ₗ[ℤ] InjectiveTarget L :=
  (injectiveTargetEquiv L).symm.toLinearMap.comp
    (injectivePresentation L).f.hom

theorem gammaTwoQuotientEmbedding_injective :
    Function.Injective (gammaTwoQuotientEmbedding L) := by
  exact (injectiveTargetEquiv L).symm.injective.comp
    ((ModuleCat.mono_iff_injective (injectivePresentation L).f).mp inferInstance)

/-- A bracket, regarded as an element of `gamma_2`. -/
def bracketInGammaTwo (x y : L) : lowerCentralSeries ℤ L 1 :=
  ⟨⁅x, y⁆, by
    rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)⟩

@[simp]
theorem bracketInGammaTwo_add_left (x y z : L) :
    bracketInGammaTwo L (x + y) z =
      bracketInGammaTwo L x z + bracketInGammaTwo L y z := by
  apply Subtype.ext
  exact add_lie x y z

@[simp]
theorem bracketInGammaTwo_add_right (x y z : L) :
    bracketInGammaTwo L x (y + z) =
      bracketInGammaTwo L x y + bracketInGammaTwo L x z := by
  apply Subtype.ext
  exact lie_add x y z

@[simp]
theorem bracketInGammaTwo_smul_left (a : ℤ) (x y : L) :
    bracketInGammaTwo L (a • x) y = a • bracketInGammaTwo L x y := by
  apply Subtype.ext
  exact smul_lie a x y

@[simp]
theorem bracketInGammaTwo_smul_right (a : ℤ) (x y : L) :
    bracketInGammaTwo L x (a • y) = a • bracketInGammaTwo L x y := by
  apply Subtype.ext
  exact lie_smul a x y

/-- The bracket modulo `gamma_3`, before passing either argument to the abelianization. -/
def bracketModGammaThree : L →ₗ[ℤ] L →ₗ[ℤ] GammaTwoQuotient L where
  toFun x :=
    { toFun := fun y ↦ Submodule.Quotient.mk (bracketInGammaTwo L x y)
      map_add' := by
        intro y z
        rw [bracketInGammaTwo_add_right]
        exact map_add (Submodule.mkQ (gammaThreeInGammaTwo L)) _ _
      map_smul' := by
        intro a y
        rw [bracketInGammaTwo_smul_right]
        exact map_smul (Submodule.mkQ (gammaThreeInGammaTwo L)) a _ }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.add_apply]
    change Submodule.Quotient.mk (bracketInGammaTwo L (x + y) z) =
      Submodule.Quotient.mk (bracketInGammaTwo L x z) +
        Submodule.Quotient.mk (bracketInGammaTwo L y z)
    rw [bracketInGammaTwo_add_left]
    exact map_add (Submodule.mkQ (gammaThreeInGammaTwo L)) _ _
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    simp only [RingHom.id_apply]
    change Submodule.Quotient.mk (bracketInGammaTwo L (a • x) y) =
      (a : ℤ) •
        (Submodule.Quotient.mk (bracketInGammaTwo L x y) : GammaTwoQuotient L)
    rw [bracketInGammaTwo_smul_left]
    exact (Submodule.mkQ (gammaThreeInGammaTwo L)).map_smul a
      (bracketInGammaTwo L x y)

theorem bracket_mem_gammaThree_of_left_mem_gammaTwo
    {x y : L} (hx : x ∈ lowerCentralSeries ℤ L 1) :
    ⁅x, y⁆ ∈ lowerCentralSeries ℤ L 2 := by
  rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
  rw [← LieSubmodule.lie_comm]
  exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top y)

theorem bracket_mem_gammaThree_of_right_mem_gammaTwo
    {x y : L} (hy : y ∈ lowerCentralSeries ℤ L 1) :
    ⁅x, y⁆ ∈ lowerCentralSeries ℤ L 2 := by
  rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy

theorem bracketModGammaThree_eq_zero_of_left_mem
    {x : L} (hx : x ∈ lowerCentralSeries ℤ L 1) :
    bracketModGammaThree L x = 0 := by
  apply LinearMap.ext
  intro y
  apply (Submodule.Quotient.mk_eq_zero (gammaThreeInGammaTwo L)).mpr
  exact bracket_mem_gammaThree_of_left_mem_gammaTwo L hx

theorem bracketModGammaThree_eq_zero_of_right_mem
    (x : L) {y : L} (hy : y ∈ lowerCentralSeries ℤ L 1) :
    bracketModGammaThree L x y = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (gammaThreeInGammaTwo L)).mpr
  exact bracket_mem_gammaThree_of_right_mem_gammaTwo L hy

/-- The alternating bracket of the abelianization, valued in `gamma_2/gamma_3`. -/
def abelianizedBracket :
    Abelianization L →ₗ[ℤ] Abelianization L →ₗ[ℤ] GammaTwoQuotient L := by
  let right : L →ₗ[ℤ] Abelianization L →ₗ[ℤ] GammaTwoQuotient L :=
    { toFun := fun x ↦ (lowerCentralSeries ℤ L 1).toSubmodule.liftQ
          (bracketModGammaThree L x)
          (fun y hy ↦ bracketModGammaThree_eq_zero_of_right_mem L x hy)
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ z =>
            change bracketModGammaThree L (x + y) z =
              bracketModGammaThree L x z + bracketModGammaThree L y z
            exact DFunLike.congr_fun (map_add (bracketModGammaThree L) x y) z
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ z =>
            change bracketModGammaThree L (a • x) z =
              a • bracketModGammaThree L x z
            exact DFunLike.congr_fun (map_smul (bracketModGammaThree L) a x) z }
  exact (lowerCentralSeries ℤ L 1).toSubmodule.liftQ right
    (fun x hx ↦ by
      apply LinearMap.ext
      intro q
      induction q using Submodule.Quotient.induction_on with
      | _ y =>
          change bracketModGammaThree L x y = 0
          exact DFunLike.congr_fun
            (bracketModGammaThree_eq_zero_of_left_mem L hx) y)

@[simp]
theorem abelianizedBracket_mk_mk (x y : L) :
    abelianizedBracket L
        (LieSubmodule.Quotient.mk x : Abelianization L)
        (LieSubmodule.Quotient.mk y : Abelianization L) =
      Submodule.Quotient.mk (bracketInGammaTwo L x y) :=
  rfl

theorem abelianizedBracket_self (x : Abelianization L) :
    abelianizedBracket L x x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      rw [abelianizedBracket_mk_mk]
      apply (Submodule.Quotient.mk_eq_zero (gammaThreeInGammaTwo L)).mpr
      change ⁅x, x⁆ ∈ lowerCentralSeries ℤ L 2
      simp

local notation "M" => Abelianization L
local notation "C" => InjectiveTarget L
local notation "T" => TensorAlgebra ℤ M

/-- The tensor-algebra augmentation used to give `C` its trivial bimodule structure. -/
def tensorAugmentation : T →ₐ[ℤ] ℤ :=
  TensorAlgebra.lift ℤ (0 : M →ₗ[ℤ] ℤ)

@[simp]
theorem tensorAugmentation_ι (x : M) :
    tensorAugmentation L (TensorAlgebra.ι ℤ x) = 0 := by
  simp [tensorAugmentation]

local instance (priority := 2000) targetTensorModule : Module T C :=
  Module.compHom C (tensorAugmentation L).toRingHom

local instance (priority := 2000) targetTensorModuleOpposite : Module Tᵐᵒᵖ C :=
  Module.compHom C ((tensorAugmentation L).toRingHom.fromOpposite
    (fun _ _ ↦ mul_comm _ _))

@[simp]
theorem targetTensor_smul (a : T) (c : C) :
    a • c = tensorAugmentation L a • c :=
  by
    have hmodule : (inferInstance : Module ℤ C) = AddCommGroup.toIntModule C :=
      Subsingleton.elim _ _
    cases hmodule
    rfl

@[simp]
theorem targetTensorOpposite_smul (a : Tᵐᵒᵖ) (c : C) :
    a • c = tensorAugmentation L a.unop • c :=
  by
    have hmodule : (inferInstance : Module ℤ C) = AddCommGroup.toIntModule C :=
      Subsingleton.elim _ _
    cases hmodule
    rfl

local instance targetTensorSMulCommClass : SMulCommClass T Tᵐᵒᵖ C := by
  constructor
  intro a b c
  rw [targetTensor_smul, targetTensorOpposite_smul,
    targetTensor_smul, targetTensorOpposite_smul]
  simp only [smul_smul]
  rw [mul_comm]

/-- The bracket of the abelianization, embedded in the injective target. -/
def injectiveBracket : M →ₗ[ℤ] M →ₗ[ℤ] C where
  toFun x := (gammaTwoQuotientEmbedding L).comp (abelianizedBracket L x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    have h := DFunLike.congr_fun (map_smul (abelianizedBracket L) a x) y
    change gammaTwoQuotientEmbedding L (abelianizedBracket L (a • x) y) =
      a • gammaTwoQuotientEmbedding L (abelianizedBracket L x y)
    rw [h]
    simpa only [LinearMap.smul_apply, RingHom.id_apply] using
      map_smul (gammaTwoQuotientEmbedding L) a (abelianizedBracket L x y)

/-- The trivial-action Higgins Lie structure attached to the bracket
`(L/gamma_2)^2 → gamma_2/gamma_3 ↪ C`. -/
def quotientBracketLieStructure : PBW.Higgins.LieStructure M C where
  bracket := injectiveBracket L
  lie_self x := by
    change gammaTwoQuotientEmbedding L (abelianizedBracket L x x) = 0
    rw [abelianizedBracket_self, map_zero]
  balance x y u v t := by
    simp [targetTensor_smul, targetTensorOpposite_smul,
      LieRing.of_associative_ring_bracket]
  jacobi x y z := by
    simp [targetTensor_smul, targetTensorOpposite_smul]

/-- Universality supplies the integral commutator map into the injective target. -/
def commutatorToTarget :
    letI := PBW.Higgins.tensorCommutatorIdealSMulCommClass M
    PBW.Higgins.LieStructure.Hom M
      (PBW.Higgins.tensorCommutatorLieStructure M)
      (quotientBracketLieStructure L) := by
  letI := PBW.Higgins.tensorCommutatorIdealSMulCommClass M
  exact (PBW.Higgins.tensorCommutatorLieStructure_isUniversal M C
    (quotientBracketLieStructure L)).choose

@[simp]
theorem commutatorToTarget_bracket (x y : M) :
    commutatorToTarget L (PBW.Higgins.tensorCommutatorBracket M x y) =
      injectiveBracket L x y :=
  by
    letI := PBW.Higgins.tensorCommutatorIdealSMulCommClass M
    exact (commutatorToTarget L).map_bracket x y

/-- An integral-linear extension from the commutator ideal to the whole tensor algebra. -/
def polarizationExtension : T →ₗ[ℤ] C := by
  letI := PBW.Higgins.tensorCommutatorIdealSMulCommClass M
  let f : PBW.Higgins.tensorCommutatorIdeal M →ₗ[ℤ] C :=
    (commutatorToTarget L).toLinearMap.restrictScalars ℤ
  exact Classical.choose (Module.Injective.extension_property ℤ C
    (PBW.Higgins.tensorCommutatorIdeal M) T
    ((PBW.Higgins.tensorCommutatorIdeal M).subtype.restrictScalars ℤ)
    (PBW.Higgins.tensorCommutatorIdeal M).subtype_injective f)

theorem polarizationExtension_on_commutator
    (k : PBW.Higgins.tensorCommutatorIdeal M) :
    polarizationExtension L (k : T) = commutatorToTarget L k := by
  letI := PBW.Higgins.tensorCommutatorIdealSMulCommClass M
  let f : PBW.Higgins.tensorCommutatorIdeal M →ₗ[ℤ] C :=
    (commutatorToTarget L).toLinearMap.restrictScalars ℤ
  have h := Classical.choose_spec (Module.Injective.extension_property ℤ C
    (PBW.Higgins.tensorCommutatorIdeal M) T
    ((PBW.Higgins.tensorCommutatorIdeal M).subtype.restrictScalars ℤ)
    (PBW.Higgins.tensorCommutatorIdeal M).subtype_injective f)
  exact DFunLike.congr_fun h k

/-- A polarization of the bracket on the abelianization. -/
def polarization : M →ₗ[ℤ] M →ₗ[ℤ] C where
  toFun x :=
    { toFun := fun y ↦ polarizationExtension L
          (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y)
      map_add' := by
        intro y z
        simp [mul_add]
      map_smul' := by
        intro a y
        change polarizationExtension L
            (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ (a • y)) =
          a • polarizationExtension L
            (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y)
        rw [map_smul]
        change polarizationExtension L
            (TensorAlgebra.ι ℤ x *
              (algebraMap ℤ T a * TensorAlgebra.ι ℤ y)) = _
        rw [← mul_assoc,
          (Algebra.commutes a (TensorAlgebra.ι ℤ x)).symm, mul_assoc]
        exact map_smul (polarizationExtension L) a
          (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp [add_mul]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change polarizationExtension L
        (TensorAlgebra.ι ℤ (a • x) * TensorAlgebra.ι ℤ y) =
      a • polarizationExtension L
        (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y)
    rw [map_smul]
    change polarizationExtension L
        ((algebraMap ℤ T a * TensorAlgebra.ι ℤ x) *
          TensorAlgebra.ι ℤ y) = _
    rw [mul_assoc]
    exact map_smul (polarizationExtension L) a
      (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y)

/-- The antisymmetrization of `polarization` is exactly the bracket modulo `gamma_3`. -/
theorem polarization_sub_swap (x y : M) :
    polarization L x y - polarization L y x = injectiveBracket L x y := by
  change polarizationExtension L
      (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y) -
    polarizationExtension L
      (TensorAlgebra.ι ℤ y * TensorAlgebra.ι ℤ x) = _
  rw [← map_sub]
  change polarizationExtension L
      (⁅TensorAlgebra.ι ℤ x, TensorAlgebra.ι ℤ y⁆) = _
  rw [show ⁅TensorAlgebra.ι ℤ x, TensorAlgebra.ι ℤ y⁆ =
      (PBW.Higgins.tensorCommutatorBracket M x y : T) by
    rfl]
  rw [polarizationExtension_on_commutator, commutatorToTarget_bracket]

/-- The canonical map `gamma_2 → gamma_2/gamma_3 ↪ C`. -/
def gammaTwoToTarget : lowerCentralSeries ℤ L 1 →ₗ[ℤ] C :=
  (gammaTwoQuotientEmbedding L).comp (Submodule.mkQ (gammaThreeInGammaTwo L))

/-- Extend the degree-two coordinate to all of `L`, using injectivity of `C`. -/
def centralCoordinateExtension : L →ₗ[ℤ] C :=
  Classical.choose (Module.Injective.extension_property ℤ C
    (lowerCentralSeries ℤ L 1) L
    (lowerCentralSeries ℤ L 1).toSubmodule.subtype
    (lowerCentralSeries ℤ L 1).toSubmodule.injective_subtype
    (gammaTwoToTarget L))

theorem centralCoordinateExtension_on_gammaTwo
    (x : lowerCentralSeries ℤ L 1) :
    centralCoordinateExtension L x = gammaTwoToTarget L x := by
  have h := Classical.choose_spec (Module.Injective.extension_property ℤ C
    (lowerCentralSeries ℤ L 1) L
    (lowerCentralSeries ℤ L 1).toSubmodule.subtype
    (lowerCentralSeries ℤ L 1).toSubmodule.injective_subtype
    (gammaTwoToTarget L))
  exact DFunLike.congr_fun h x

theorem centralCoordinateExtension_bracket (x y : L) :
    centralCoordinateExtension L ⁅x, y⁆ =
      injectiveBracket L
        (LieSubmodule.Quotient.mk x : M)
        (LieSubmodule.Quotient.mk y : M) := by
  rw [show ⁅x, y⁆ = (bracketInGammaTwo L x y : L) by rfl,
    centralCoordinateExtension_on_gammaTwo]
  rfl

/-- The three-step space used to detect `gamma_2/gamma_3`. -/
abbrev TriangularSpace := ℤ × (M × C)

/-- The quotient map `L → L/gamma_2`. -/
def toAbelianization : L →ₗ[ℤ] M :=
  (lowerCentralSeries ℤ L 1).toSubmodule.mkQ

@[simp]
theorem toAbelianization_apply (x : L) :
    toAbelianization L x = (LieSubmodule.Quotient.mk x : M) :=
  rfl

/-- A strictly upper-triangular endomorphism associated to `x : L`. -/
def triangularGenerator (x : L) : Module.End ℤ (TriangularSpace L) where
  toFun v :=
    (0, (v.1 • toAbelianization L x,
      v.1 • centralCoordinateExtension L x +
        polarization L (toAbelianization L x) v.2.1))
  map_add' v w := by
    ext <;> simp [add_smul]
    abel
  map_smul' a v := by
    ext <;> simp [mul_smul]

@[simp]
theorem triangularGenerator_apply (x : L) (v : TriangularSpace L) :
    triangularGenerator L x v =
      (0, (v.1 • toAbelianization L x,
        v.1 • centralCoordinateExtension L x +
          polarization L (toAbelianization L x) v.2.1)) :=
  rfl

/-- The triangular generator depends integrally linearly on `x`. -/
def triangularGeneratorLinear :
    L →ₗ[ℤ] Module.End ℤ (TriangularSpace L) where
  toFun := triangularGenerator L
  map_add' x y := by
    apply LinearMap.ext
    intro v
    ext <;> simp [triangularGenerator, smul_add]
    abel
  map_smul' a x := by
    apply LinearMap.ext
    intro v
    change triangularGenerator L (a • x) v = a • triangularGenerator L x v
    apply Prod.ext
    · simp only [triangularGenerator_apply, Prod.smul_fst, smul_zero]
    · apply Prod.ext
      · simp only [triangularGenerator_apply, Prod.smul_snd, Prod.smul_fst,
          map_smul]
        rw [smul_smul, smul_smul, mul_comm]
      · simp only [triangularGenerator_apply, Prod.smul_snd, map_smul,
          LinearMap.smul_apply]
        rw [smul_smul, smul_add, smul_smul, mul_comm]

/-- The triangular generators form a Lie representation of `L`. -/
def triangularLieHom :
    L →ₗ⁅ℤ⁆ Module.End ℤ (TriangularSpace L) where
  toLinearMap := triangularGeneratorLinear L
  map_lie' := by
    intro x y
    apply LinearMap.ext
    intro v
    ext
    · simp [triangularGeneratorLinear, triangularGenerator,
        LieRing.of_associative_ring_bracket, Module.End.mul_apply]
    · simp [triangularGeneratorLinear, triangularGenerator,
        LieRing.of_associative_ring_bracket, Module.End.mul_apply]
      have hq : toAbelianization L ⁅x, y⁆ = 0 := by
        apply (LieSubmodule.Quotient.mk_eq_zero'
          (N := lowerCentralSeries ℤ L 1)).mpr
        exact (bracketInGammaTwo L x y).property
      change v.1 • (LieSubmodule.Quotient.mk ⁅x, y⁆ : M) = 0
      rw [show (LieSubmodule.Quotient.mk ⁅x, y⁆ : M) = 0 by exact hq,
        smul_zero]
    · have hq : toAbelianization L ⁅x, y⁆ = 0 := by
        apply (LieSubmodule.Quotient.mk_eq_zero'
          (N := lowerCentralSeries ℤ L 1)).mpr
        exact (bracketInGammaTwo L x y).property
      simp only [triangularGeneratorLinear, triangularGenerator_apply,
        LieRing.of_associative_ring_bracket, Module.End.mul_apply,
        LinearMap.sub_apply, zero_smul, zero_add]
      rw [hq, map_zero]
      simp only [LinearMap.zero_apply, add_zero, Prod.snd_sub]
      simp only [map_smul]
      rw [← smul_sub, polarization_sub_swap,
        centralCoordinateExtension_bracket]
      simp only [toAbelianization_apply]

/-- The induced representation of the universal enveloping algebra. -/
def triangularRepresentation :
    UEA ℤ L →ₐ[ℤ] Module.End ℤ (TriangularSpace L) :=
  UniversalEnvelopingAlgebra.lift ℤ (triangularLieHom L)

@[simp]
theorem triangularRepresentation_ι (x : L) :
    triangularRepresentation L (UniversalEnvelopingAlgebra.ι ℤ x) =
      triangularGenerator L x := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ (triangularLieHom L) x

/-- An upper-triangular endomorphism whose three diagonal blocks are multiplication by `z`. -/
def HasScalarDiagonal
    (f : Module.End ℤ (TriangularSpace L)) (z : ℤ) : Prop :=
  (∀ v, (f v).1 = z * v.1) ∧
  (∀ m c, (f (0, (m, c))).2.1 = z • m) ∧
  (∀ c, (f (0, (0, c))).2.2 = z • c)

theorem hasScalarDiagonal_add
    {f g : Module.End ℤ (TriangularSpace L)} {a b : ℤ}
    (hf : HasScalarDiagonal L f a) (hg : HasScalarDiagonal L g b) :
    HasScalarDiagonal L (f + g) (a + b) := by
  refine ⟨fun v ↦ ?_, fun m c ↦ ?_, fun c ↦ ?_⟩
  · simp only [LinearMap.add_apply, Prod.fst_add, hf.1 v, hg.1 v]
    ring
  · simp only [LinearMap.add_apply, Prod.snd_add, Prod.fst_add,
      hf.2.1 m c, hg.2.1 m c, add_smul]
  · simp only [LinearMap.add_apply, Prod.snd_add, hf.2.2 c, hg.2.2 c,
      add_smul]

theorem hasScalarDiagonal_mul
    {f g : Module.End ℤ (TriangularSpace L)} {a b : ℤ}
    (hf : HasScalarDiagonal L f a) (hg : HasScalarDiagonal L g b) :
    HasScalarDiagonal L (f * g) (a * b) := by
  refine ⟨fun v ↦ ?_, fun m c ↦ ?_, fun c ↦ ?_⟩
  · rw [Module.End.mul_apply, hf.1, hg.1]
    ring
  · rw [Module.End.mul_apply]
    have hg0 : (g (0, (m, c))).1 = 0 := by simpa using hg.1 (0, (m, c))
    have hgm : (g (0, (m, c))).2.1 = b • m := hg.2.1 m c
    have heq : g (0, (m, c)) =
        (0, (b • m, (g (0, (m, c))).2.2)) := by
      ext <;> simp [hg0, hgm]
    rw [heq, hf.2.1, smul_smul]
  · rw [Module.End.mul_apply]
    have hg0 : (g (0, (0, c))).1 = 0 := by simpa using hg.1 (0, (0, c))
    have hgm : (g (0, (0, c))).2.1 = 0 := by simpa using hg.2.1 0 c
    have heq : g (0, (0, c)) =
        (0, (0, (g (0, (0, c))).2.2)) := by
      ext <;> simp [hg0, hgm]
    rw [heq, hf.2.2, hg.2.2, smul_smul]

theorem hasScalarDiagonal_algebraMap (z : ℤ) :
    HasScalarDiagonal L
      (algebraMap ℤ (Module.End ℤ (TriangularSpace L)) z) z := by
  refine ⟨fun v ↦ ?_, fun m c ↦ ?_, fun c ↦ ?_⟩ <;>
    simp

theorem hasScalarDiagonal_generator (x : L) :
    HasScalarDiagonal L (triangularGenerator L x) 0 := by
  refine ⟨fun v ↦ ?_, fun m c ↦ ?_, fun c ↦ ?_⟩ <;>
    simp [triangularGenerator]

/-- Every represented enveloping-algebra element has augmentation on all diagonal blocks. -/
theorem triangularRepresentation_hasScalarDiagonal (u : UEA ℤ L) :
    HasScalarDiagonal L (triangularRepresentation L u) (UEA.augmentation ℤ L u) := by
  induction u using UEA.induction with
  | algebraMap z =>
      simpa [triangularRepresentation] using hasScalarDiagonal_algebraMap L z
  | ι x =>
      rw [triangularRepresentation_ι, UEA.augmentation_ι]
      exact hasScalarDiagonal_generator L x
  | mul a b ha hb =>
      simpa using hasScalarDiagonal_mul L ha hb
  | add a b ha hb =>
      simpa using hasScalarDiagonal_add L ha hb

/-- Augmentation-zero elements act strictly upper triangular. -/
theorem triangularRepresentation_strict
    {u : UEA ℤ L} (hu : u ∈ UEA.augmentationIdeal ℤ L) :
    HasScalarDiagonal L (triangularRepresentation L u) 0 := by
  have h := triangularRepresentation_hasScalarDiagonal L u
  rw [(UEA.mem_augmentationIdeal ℤ L).mp hu] at h
  exact h

/-- Three strictly upper-triangular endomorphisms of the chosen three-step space multiply to
zero. -/
theorem strict_mul_strict_mul_strict_eq_zero
    {f g h : Module.End ℤ (TriangularSpace L)}
    (hf : HasScalarDiagonal L f 0)
    (hg : HasScalarDiagonal L g 0)
    (hh : HasScalarDiagonal L h 0) :
    f * g * h = 0 := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have hh0 : (h v).1 = 0 := by simpa using hh.1 v
  have hg0 : (g (h v)).1 = 0 := by simpa using hg.1 (h v)
  have hgm : (g (h v)).2.1 = 0 := by
    have heq : h v = (0, ((h v).2.1, (h v).2.2)) := by
      ext <;> simp [hh0]
    rw [heq]
    simpa using hg.2.1 (h v).2.1 (h v).2.2
  have heq : g (h v) = (0, (0, (g (h v)).2.2)) := by
    ext <;> simp [hg0, hgm]
  rw [heq]
  have := hf.2.2 (g (h v)).2.2
  ext <;> simp [hf.1, hf.2.1, this]

/-- The cube of the augmentation ideal is killed by the triangular representation. -/
theorem triangularRepresentation_eq_zero_of_mem_cube
    {u : UEA ℤ L} (hu : u ∈ UEA.augmentationIdeal ℤ L ^ 3) :
    triangularRepresentation L u = 0 := by
  let I := UEA.augmentationIdeal ℤ L
  have hu' : u ∈ (I * I) * I := by
    simpa only [show (3 : ℕ) = 2 + 1 by rfl, Submodule.pow_succ,
      show (2 : ℕ) = 1 + 1 by rfl, Submodule.pow_one, Submodule.pow_zero,
      Submodule.one_mul] using hu
  refine Submodule.mul_induction_on hu' ?_ ?_
  · intro a ha b hb
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [map_mul, map_mul]
      exact strict_mul_strict_mul_strict_eq_zero L
        (triangularRepresentation_strict L hx)
        (triangularRepresentation_strict L hy)
        (triangularRepresentation_strict L hb)
    · intro x y hx hy
      rw [add_mul, map_add, hx, hy, add_zero]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- Membership in `delta_3` forces membership in `gamma_3`. -/
theorem dimensionSubring_three_le_lowerCentralSeries_two :
    dimensionSubring ℤ L 3 ≤ lowerCentralSeries ℤ L 2 := by
  intro x hx
  have hxTwo : x ∈ lowerCentralSeries ℤ L 1 := by
    rw [← dimensionSubring_two_eq_lowerCentralSeries_one ℤ L]
    exact dimensionSubring_antitone ℤ L (by omega : 2 ≤ 3) hx
  have hrep : triangularRepresentation L
      (UniversalEnvelopingAlgebra.ι ℤ x) = 0 :=
    triangularRepresentation_eq_zero_of_mem_cube L
      ((mem_dimensionSubring ℤ L).mp hx)
  have heval := LinearMap.congr_fun hrep
    ((1, (0, 0)) : TriangularSpace L)
  have hc : centralCoordinateExtension L x = 0 := by
    rw [triangularRepresentation_ι] at heval
    have hthird := congrArg (fun v : TriangularSpace L ↦ v.2.2) heval
    simpa [triangularGenerator] using hthird
  let xTwo : lowerCentralSeries ℤ L 1 := ⟨x, hxTwo⟩
  have hemb : gammaTwoQuotientEmbedding L
      (Submodule.Quotient.mk xTwo : GammaTwoQuotient L) = 0 := by
    change gammaTwoToTarget L xTwo = 0
    rw [← centralCoordinateExtension_on_gammaTwo L xTwo]
    exact hc
  have hclass : (Submodule.Quotient.mk xTwo : GammaTwoQuotient L) = 0 :=
    gammaTwoQuotientEmbedding_injective L (by simpa using hemb)
  exact (Submodule.Quotient.mk_eq_zero (gammaThreeInGammaTwo L)).mp hclass

end

end DegreeThree

/-- **Third dimension-subring theorem.** For every Lie ring,
`delta_3(L) = gamma_3(L)`.

Mathlib numbers the lower central series from zero, so conventional `gamma_3` is written
`lowerCentralSeries ℤ L 2`.
-/
theorem dimensionSubring_three_eq_lowerCentralSeries_two
    (L : Type u) [LieRing L] :
    dimensionSubring ℤ L 3 = lowerCentralSeries ℤ L 2 := by
  apply le_antisymm
  · exact DegreeThree.dimensionSubring_three_le_lowerCentralSeries_two L
  · simpa using lowerCentralSeries_le_dimensionSubring ℤ L 2

end LieRings
