import LieRings.Plotkin.CentralDerivative
import LieRings.Plotkin.Coinduced

/-!
# Embedding a split central extension in a coinduced semidirect product

This is the formal version of the manuscript's central-embedding lemma.  Its only PBW input is an
additive coefficient map splitting the copy of the central ideal in the derivative module.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

open CentralDerivative

variable (E : Type u) [LieRing E]
variable (D : LieIdeal ℤ E)

namespace CentralEmbedding

abbrev H := E ⧸ D
abbrev M := CentralDerivative.Derivative E D
abbrev J := Coinduced (H E D) D

/-- We regard the central ideal as a trivial module over the quotient. -/
instance ideal_trivialLieRingModule : LieRingModule (H E D) D where
  bracket _ _ := 0
  add_lie := by intros; change (0 : D) = 0 + 0; abel
  lie_add := by intros; change (0 : D) = 0 + 0; abel
  leibniz_lie := by intros; change (0 : D) = 0 + 0; abel

instance ideal_trivialLieModule : LieModule ℤ (H E D) D where
  smul_lie := by simp
  lie_smul := by simp

/-- The central copy of `D` inside the derivative module. -/
def centralInclusion (hcentral : D ≤ LieAlgebra.center ℤ E) :
    D →ₗ⁅ℤ,H E D⁆ M E D where
  toFun d := CentralDerivative.bar E D d
  map_add' d d' := (CentralDerivative.bar E D).map_add d d'
  map_smul' z d := (CentralDerivative.bar E D).map_smul z d
  map_lie' {x d} := by
    rw [show ⁅x, d⁆ = 0 by rfl]
    change CentralDerivative.bar E D (0 : E) =
      ⁅x, CentralDerivative.bar E D (d : E)⁆
    rw [map_zero]
    change 0 = ⁅x, CentralDerivative.bar E D (d : E)⁆
    symm
    exact CentralDerivative.quotient_lie_bar_eq_zero E D hcentral d d.property x

/-- The trivial module `D` embeds in the coinduced module by the augmentation. -/
def augmentationEmbedding : D →ₗ⁅ℤ,H E D⁆ J E D where
  toFun d :=
    { toFun := fun a ↦ UEA.augmentation ℤ (H E D) a • d
      map_add' := fun a b ↦ by rw [map_add, add_smul]
      map_smul' := fun z a ↦ by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [mul_smul] }
  map_add' d d' := by ext a; simp [smul_add]
  map_smul' z d := by
    ext a
    change UEA.augmentation ℤ (H E D) a • (z • (d : E)) =
      z • (UEA.augmentation ℤ (H E D) a • (d : E))
    rw [smul_smul, smul_smul, mul_comm]
  map_lie' {x d} := by
    rw [show ⁅x, d⁆ = 0 by rfl]
    ext a
    rw [Coinduced.lie_apply]
    change UEA.augmentation ℤ (H E D) a • (0 : E) =
      UEA.augmentation ℤ (H E D)
        (a * UniversalEnvelopingAlgebra.ι ℤ x) • (d : E)
    rw [smul_zero, map_mul, UEA.augmentation_ι, mul_zero, zero_smul]

@[simp]
theorem augmentationEmbedding_apply (d : D) (a : UEA ℤ (H E D)) :
    augmentationEmbedding E D d a = UEA.augmentation ℤ (H E D) a • d :=
  rfl

@[simp]
theorem augmentationEmbedding_one (d : D) :
    augmentationEmbedding E D d 1 = d := by
  simp [augmentationEmbedding]

variable (hcentral : D ≤ LieAlgebra.center ℤ E)
variable (coefficient : M E D →ₗ[ℤ] D)
variable (hcoefficient : ∀ d : D,
  coefficient (centralInclusion E D hcentral d) = d)

/-- The range of the central copy, as a Lie submodule. -/
abbrev centralRange : LieSubmodule ℤ (H E D) (M E D) :=
  LieModuleHom.range (centralInclusion E D hcentral)

/-- The coefficient map supplies an additive retraction onto the central range. -/
def rangeRetraction : M E D →ₗ[ℤ] centralRange E D hcentral where
  toFun m :=
    ⟨centralInclusion E D hcentral (coefficient m),
      ⟨coefficient m, rfl⟩⟩
  map_add' m n := by ext; simp
  map_smul' z m := by ext; simp

/-- On the central range, apply the coefficient and then the augmentation embedding. -/
def rangeToCoinduced :
    centralRange E D hcentral →ₗ⁅ℤ,H E D⁆ J E D where
  toFun n := augmentationEmbedding E D (coefficient n)
  map_add' m n := by simp
  map_smul' z m := by simp
  map_lie' {x n} := by
    rcases n with ⟨_, ⟨d, rfl⟩⟩
    have hnzero : ⁅x, centralInclusion E D hcentral d⁆ = 0 := by
      rw [← (centralInclusion E D hcentral).map_lie,
        show ⁅x, d⁆ = 0 by rfl, map_zero]
    have hnzeroRange :
        ⁅x, (⟨centralInclusion E D hcentral d, ⟨d, rfl⟩⟩ :
          centralRange E D hcentral)⁆ = 0 := by
      apply Subtype.ext
      exact hnzero
    rw [hnzeroRange]
    change augmentationEmbedding E D (coefficient (0 : M E D)) =
      ⁅x, augmentationEmbedding E D
        (coefficient (centralInclusion E D hcentral d))⁆
    rw [map_zero, map_zero]
    have hj := (augmentationEmbedding E D).map_lie x
      (coefficient (centralInclusion E D hcentral d))
    rw [show ⁅x, coefficient (centralInclusion E D hcentral d)⁆ = 0 by rfl,
      map_zero] at hj
    exact hj

/-- The coinduced extension `T : M → J`. -/
def extension : M E D →ₗ⁅ℤ,H E D⁆ J E D :=
  Plotkin.extend (M E D) (centralRange E D hcentral)
    (rangeRetraction E D hcentral coefficient)
    (rangeToCoinduced E D hcentral coefficient)

include hcoefficient in
theorem rangeRetraction_restricts (n : centralRange E D hcentral) :
    rangeRetraction E D hcentral coefficient n = n := by
  rcases n with ⟨_, ⟨d, rfl⟩⟩
  apply Subtype.ext
  change centralInclusion E D hcentral
      (coefficient (centralInclusion E D hcentral d)) =
    centralInclusion E D hcentral d
  rw [hcoefficient]

include hcoefficient in
@[simp]
theorem extension_central (d : D) :
    extension E D hcentral coefficient (centralInclusion E D hcentral d) =
      augmentationEmbedding E D d := by
  let n : centralRange E D hcentral :=
    ⟨centralInclusion E D hcentral d, ⟨d, rfl⟩⟩
  have h := Plotkin.extend_restricts (M E D) (centralRange E D hcentral)
    (rangeRetraction E D hcentral coefficient)
    (rangeRetraction_restricts E D hcentral coefficient hcoefficient)
    (rangeToCoinduced E D hcentral coefficient) n
  change Plotkin.extend (M E D) (centralRange E D hcentral)
      (rangeRetraction E D hcentral coefficient)
      (rangeToCoinduced E D hcentral coefficient) (n : M E D) = _
  rw [h]
  change augmentationEmbedding E D
      (coefficient (centralInclusion E D hcentral d)) = _
  rw [hcoefficient]

/-- The semidirect-product target of the central embedding. -/
abbrev Target :=
  (J E D) ⋊⁅Coinduced.derivationAction (H E D) D⁆ (H E D)

/-- The embedding from the manuscript, `e ↦ (T(bar e), e + D)`. -/
def map : E →ₗ⁅ℤ⁆ Target E D where
  toFun e :=
    ⟨extension E D hcentral coefficient (CentralDerivative.bar E D e),
      LieSubmodule.Quotient.mk e⟩
  map_add' e e' := by
    apply LieAlgebra.SemiDirectSum.ext
    · change extension E D hcentral coefficient
          (CentralDerivative.bar E D (e + e')) =
        extension E D hcentral coefficient (CentralDerivative.bar E D e) +
          extension E D hcentral coefficient (CentralDerivative.bar E D e')
      rw [map_add, map_add]
    · rfl
  map_smul' z e := by
    apply LieAlgebra.SemiDirectSum.ext
    · change extension E D hcentral coefficient
          (CentralDerivative.bar E D (z • e)) =
        z • extension E D hcentral coefficient (CentralDerivative.bar E D e)
      rw [map_smul, map_smul]
    · rfl
  map_lie' := by
    intro e e'
    apply LieAlgebra.SemiDirectSum.ext
    · change extension E D hcentral coefficient
          (CentralDerivative.bar E D ⁅e, e'⁆) =
        ⁅(0 : J E D), 0⁆ +
          ⁅(LieSubmodule.Quotient.mk e : H E D),
            extension E D hcentral coefficient (CentralDerivative.bar E D e')⁆ -
          ⁅(LieSubmodule.Quotient.mk e' : H E D),
            extension E D hcentral coefficient (CentralDerivative.bar E D e)⁆
      rw [CentralDerivative.bar_bracket, map_sub,
        (extension E D hcentral coefficient).map_lie,
        (extension E D hcentral coefficient).map_lie]
      simp
    · exact LieSubmodule.Quotient.mk_bracket D e e'

@[simp]
theorem map_right (e : E) : (map E D hcentral coefficient e).right =
    LieSubmodule.Quotient.mk e := rfl

include hcoefficient in
theorem map_injective : Function.Injective (map E D hcentral coefficient) := by
  intro e e' heq
  have hdiff : map E D hcentral coefficient (e - e') = 0 := by
    rw [map_sub, heq, sub_self]
  have hright : (LieSubmodule.Quotient.mk (e - e') : H E D) = 0 := by
    exact congrArg LieAlgebra.SemiDirectSum.right hdiff
  have hmem : e - e' ∈ D :=
    (LieSubmodule.Quotient.mk_eq_zero' (N := D)).mp hright
  let d : D := ⟨e - e', hmem⟩
  have hleft : extension E D hcentral coefficient
      (CentralDerivative.bar E D (e - e')) = 0 := by
    exact congrArg LieAlgebra.SemiDirectSum.left hdiff
  have hj : augmentationEmbedding E D d = 0 := by
    rw [← extension_central E D hcentral coefficient hcoefficient d]
    exact hleft
  have hd : d = 0 := by
    have := congrArg (fun α : J E D ↦ α 1) hj
    simpa using this
  exact sub_eq_zero.mp (congrArg Subtype.val hd)

include hcoefficient
/-- On `D`, the embedding lands in the first factor as the augmentation embedding. -/
theorem map_central (d : D) :
    map E D hcentral coefficient d =
      ⟨augmentationEmbedding E D d, 0⟩ := by
  apply LieAlgebra.SemiDirectSum.ext
  · exact extension_central E D hcentral coefficient hcoefficient d
  · exact (LieSubmodule.Quotient.mk_eq_zero' (N := D)).2 d.property

end CentralEmbedding

end

end LieRings.Plotkin
