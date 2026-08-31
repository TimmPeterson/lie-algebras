import LieRings.Plotkin.PushoutExtension
import LieRings.Plotkin.DistinguishedPBWCoefficient
import LieRings.Plotkin.CoinducedCoordinates
import Mathlib.Util.AssertNoSorry

/-!
# Central separation for finitely generated nilpotent Lie rings

This file assembles the finite cyclic pushout, the distinguished PBW
coefficient, the coinduced central embedding, Rees separation, and the
triangular nilpotent realization.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

variable {K : Type u} [LieRing K]

section PushoutCoordinates

variable {D : Type v} [AddCommGroup D]
variable (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
variable (hcentral : A ≤ LieAlgebra.center ℤ K)

/-- The original central ideal maps into the actual kernel ideal of the
pushout projection. -/
def cyclicPushoutIdealToKernel :
    A →ₗ[ℤ] CyclicPushoutKernel A χ hcentral where
  toFun a :=
    ⟨cyclicPushoutInclK A χ hcentral (a : K), by
      change cyclicPushoutProj A χ hcentral
        (cyclicPushoutInclK A χ hcentral (a : K)) = 0
      rw [cyclicPushoutProj_inclK]
      exact (LieSubmodule.Quotient.mk_eq_zero' (N := A)).mpr a.property⟩
  map_add' a b := by
    apply Subtype.ext
    exact map_add (cyclicPushoutInclK A χ hcentral) (a : K) (b : K)
  map_smul' z a := by
    apply Subtype.ext
    exact map_smul (cyclicPushoutInclK A χ hcentral) z (a : K)

@[simp]
theorem cyclicPushoutIdealToKernel_coe (a : A) :
    ((cyclicPushoutIdealToKernel A χ hcentral a :
        CyclicPushoutKernel A χ hcentral) : CyclicPushout A χ hcentral) =
      cyclicPushoutInclK A χ hcentral (a : K) :=
  rfl

/-- Injectivity of the original map into the pushout makes the induced map
from `A` to the actual kernel injective. -/
theorem cyclicPushoutIdealToKernel_injective
    (hincl : Function.Injective (cyclicPushoutInclK A χ hcentral)) :
    Function.Injective (cyclicPushoutIdealToKernel A χ hcentral) := by
  intro a b hab
  apply Subtype.ext
  apply hincl
  exact congrArg Subtype.val hab

/-- The pushout is additively finite whenever the original ring is. -/
theorem cyclicPushout_moduleFinite [Module.Finite ℤ K] [Finite D] :
    Module.Finite ℤ (CyclicPushout A χ hcentral) := by
  letI : Module.Finite ℤ D := Module.Finite.of_finite
  letI : Module.Finite ℤ (K ⧸ A) :=
    Module.Finite.quotient ℤ A.toSubmodule
  exact Module.Finite.equiv (cyclicPushoutAddEquiv A χ hcentral).symm

end PushoutCoordinates

private theorem separate_via_cyclicPushout
    {D : Type} [AddCommGroup D]
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥)
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K)
    (hincl : Function.Injective (cyclicPushoutInclK A χ hcentral))
    (coefficient :
      CentralDerivative.Derivative (CyclicPushout A χ hcentral)
          (CyclicPushoutKernel A χ hcentral) →ₗ[ℤ]
        CyclicPushoutKernel A χ hcentral)
    (hcoefficient : ∀ d : CyclicPushoutKernel A χ hcentral,
      coefficient
        (CentralEmbedding.centralInclusion
          (CyclicPushout A χ hcentral)
          (CyclicPushoutKernel A χ hcentral)
          (cyclicPushoutKernel_le_center A χ hcentral) d) = d)
    [Module.Finite ℤ K] :
    ∃ P : NilpotentIdealRepresentation K,
      Function.Injective (fun a : A ↦ P.map (a : K)) := by
  let E := CyclicPushout A χ hcentral
  let DE := CyclicPushoutKernel A χ hcentral
  have hHfg : IsFinitelyGenerated (CentralEmbedding.H E DE) := by
    exact cyclicPushoutQuotKernel_isFinitelyGenerated A χ hcentral hK
  have hHclass : lowerCentralSeries ℤ (CentralEmbedding.H E DE) c = ⊥ := by
    exact cyclicPushoutQuotKernel_lowerCentralSeries_eq_bot
      A χ hcentral c hclass
  obtain ⟨coordinates⟩ :=
    CentralEmbedding.exists_finiteSemidirectCentralCoordinates
      E DE (cyclicPushoutKernel_le_center A χ hcentral)
      coefficient hcoefficient
      (cyclicPushoutInclK A χ hcentral) A
      (cyclicPushoutIdealToKernel A χ hcentral)
      (cyclicPushoutIdealToKernel_injective A χ hcentral hincl)
      (fun a ↦ by
        change cyclicPushoutInclK A χ hcentral (a : K) =
          (((cyclicPushoutIdealToKernel A χ hcentral a :
              CyclicPushoutKernel A χ hcentral) :
            CyclicPushout A χ hcentral))
        exact (cyclicPushoutIdealToKernel_coe A χ hcentral a).symm)
      hHfg c hHclass
  exact coordinates.separate

/-- **Central prime separation for finitely generated nilpotent Lie rings.**
Every central ideal of prime order is detected by a finite-dimensional
nilpotent ideal representation. -/
theorem hasCentralPrimeSeparation_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥) :
    HasCentralPrimeSeparation K := by
  letI : Module.Finite ℤ K :=
    moduleFinite_of_finitelyGenerated_of_lowerCentralSeries_eq_bot K hK c hclass
  intro p A hp hcard hcentral
  have hprimeA : (Nat.card A).Prime := by
    simpa [hcard] using hp
  letI : Module.Finite ℤ (K ⧸ A) :=
    Module.Finite.quotient ℤ A.toSubmodule
  obtain ⟨D, instDAdd, instDFinite, instDCyclic, χ, _hχA, _hinclD,
      _hDcentral, hinclK, _hextension, _hsplit⟩ :=
    exists_finiteCyclic_central_pushout_of_finite_quotient
      A hprimeA hcentral inferInstance
  letI : AddCommGroup D := instDAdd
  letI : Finite D := instDFinite
  letI : IsAddCyclic D := instDCyclic
  letI : Module.Finite ℤ D := Module.Finite.of_finite
  let E := CyclicPushout A χ hcentral
  let DE := CyclicPushoutKernel A χ hcentral
  letI : Module.Finite ℤ E := by
    dsimp only [E]
    exact Module.Finite.equiv (cyclicPushoutAddEquiv A χ hcentral).symm
  letI : Module.Finite ℤ (E ⧸ DE) :=
    Module.Finite.quotient ℤ DE.toSubmodule
  obtain ⟨coefficient, hcoefficient⟩ :=
    DistinguishedPBW.exists_derivative_retraction_of_aligned_split
      (E := E) (D₀ := DE) (H := E ⧸ DE)
      (cyclicPushoutKernelAddEquiv A χ hcentral)
      (cyclicPushoutKernelAddEquiv_apply_kernel A χ hcentral)
      (cyclicPushoutKernel_le_center A χ hcentral)
  apply separate_via_cyclicPushout hK c hclass A χ hcentral hinclK coefficient
  intro d
  change coefficient (CentralDerivative.bar E DE (d : E)) = d
  exact hcoefficient d

end


end LieRings.Plotkin

assert_no_sorry LieRings.Plotkin.cyclicPushoutIdealToKernel
assert_no_sorry LieRings.Plotkin.cyclicPushout_moduleFinite
assert_no_sorry
  LieRings.Plotkin.hasCentralPrimeSeparation_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
