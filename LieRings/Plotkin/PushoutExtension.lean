import LieRings.Plotkin.CyclicPushout
import LieRings.Plotkin.FiniteGeneration
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Tactic
import Mathlib.Util.AssertNoSorry

/-!
# The kernel form of the finite cyclic pushout

The elementary pushout is naturally presented as an extension of `K / A` by
the auxiliary cyclic group `D`.  Later parts of the Plotkin argument instead
use the actual kernel ideal of the projection.  This file records the
canonical identifications between those two presentations and transports the
finiteness, cyclicity, finite-generation, and nilpotence data across them.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

variable {K : Type u} [LieRing K]
variable {D : Type v} [AddCommGroup D]

section

variable (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
variable (hcentral : A ≤ LieAlgebra.center ℤ K)

/-- The actual kernel ideal of the canonical pushout projection. -/
abbrev CyclicPushoutKernel :
    LieIdeal ℤ (CyclicPushout A χ hcentral) :=
  LieHom.ker (cyclicPushoutProj A χ hcentral)

/-- The extension with middle term the cyclic pushout. -/
def cyclicPushoutExtension :
    LieAlgebra.Extension ℤ (TrivialLieRing D) (K ⧸ A) :=
  (cyclicPushoutIsExtension A χ hcentral).extension

/-- The auxiliary cyclic group is canonically the kernel of the pushout
projection. -/
def cyclicPushoutKernelEquiv :
    TrivialLieRing D ≃ₗ⁅ℤ⁆ CyclicPushoutKernel A χ hcentral :=
  (cyclicPushoutExtension A χ hcentral).toKer

@[simp]
theorem cyclicPushoutKernelEquiv_coe (d : TrivialLieRing D) :
    ((cyclicPushoutKernelEquiv A χ hcentral d :
        CyclicPushoutKernel A χ hcentral) :
      CyclicPushout A χ hcentral) =
      cyclicPushoutInclD A χ hcentral d :=
  rfl

/-- The quotient by the actual kernel of the pushout projection is canonically
isomorphic to `K / A`. -/
def cyclicPushoutQuotKernelEquiv :
    (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral) ≃ₗ⁅ℤ⁆
      K ⧸ A := by
  let p := cyclicPushoutProj A χ hcentral
  have hrange : p.range = ⊤ :=
    (LieHom.range_eq_top p).mpr
      (cyclicPushoutProj_surjective A χ hcentral)
  exact p.quotKerEquivRange |>.trans
    ((LieEquiv.ofEq p.range ⊤ (by rw [hrange])).trans
      LieSubalgebra.topEquiv)

/-- The kernel ideal is central in the pushout. -/
theorem cyclicPushoutKernel_le_center :
    CyclicPushoutKernel A χ hcentral ≤
      LieAlgebra.center ℤ (CyclicPushout A χ hcentral) := by
  intro z hz
  have hz' : z ∈ LieHom.range (cyclicPushoutInclD A χ hcentral) := by
    rw [cyclicPushoutInclD_range_eq_proj_ker A χ hcentral]
    exact hz
  obtain ⟨d, rfl⟩ := hz'
  exact cyclicPushoutInclD_mem_center A χ hcentral d

/-- The actual kernel is finite when the chosen cyclic group is finite. -/
instance cyclicPushoutKernel_finite [Finite D] :
    Finite (CyclicPushoutKernel A χ hcentral) :=
  Finite.of_surjective (cyclicPushoutKernelEquiv A χ hcentral)
    (cyclicPushoutKernelEquiv A χ hcentral).surjective

/-- The actual kernel is additively cyclic when the chosen auxiliary group is
additively cyclic. -/
instance cyclicPushoutKernel_isAddCyclic [IsAddCyclic D] :
    IsAddCyclic (CyclicPushoutKernel A χ hcentral) :=
  isAddCyclic_of_surjective
    (cyclicPushoutKernelEquiv A χ hcentral).toLinearEquiv.toAddEquiv
    (cyclicPushoutKernelEquiv A χ hcentral).surjective

/-- The existing additive splitting, rewritten so that both factors are the
actual kernel and quotient belonging to the projection. -/
def cyclicPushoutKernelAddEquiv :
    CyclicPushout A χ hcentral ≃ₗ[ℤ]
      CyclicPushoutKernel A χ hcentral ×
        (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral) :=
  (cyclicPushoutAddEquiv A χ hcentral).trans
    ((cyclicPushoutKernelEquiv A χ hcentral).toLinearEquiv.prodCongr
      (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.toLinearEquiv)

/-- The first coordinate of the aligned splitting is a linear retraction onto
the actual kernel. -/
def cyclicPushoutKernelRetraction :
    CyclicPushout A χ hcentral →ₗ[ℤ]
      CyclicPushoutKernel A χ hcentral :=
  (LinearMap.fst ℤ _ _).comp
    (cyclicPushoutKernelAddEquiv A χ hcentral).toLinearMap

@[simp]
theorem cyclicPushoutKernelRetraction_inclD (d : TrivialLieRing D) :
    cyclicPushoutKernelRetraction A χ hcentral
        (cyclicPushoutInclD A χ hcentral d) =
      cyclicPushoutKernelEquiv A χ hcentral d := by
  change
    (((cyclicPushoutKernelEquiv A χ hcentral).toLinearEquiv.prodCongr
      (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.toLinearEquiv)
      (cyclicPushoutAddEquiv A χ hcentral
        (cyclicPushoutInclD A χ hcentral d))).1 =
      cyclicPushoutKernelEquiv A χ hcentral d
  rw [cyclicPushoutAddEquiv_inclD, LinearEquiv.prodCongr_apply]
  rfl

/-- The aligned splitting restricts to the identity on the actual kernel and
has zero quotient coordinate there. -/
@[simp]
theorem cyclicPushoutKernelAddEquiv_apply_kernel
    (d : CyclicPushoutKernel A χ hcentral) :
    cyclicPushoutKernelAddEquiv A χ hcentral (d : CyclicPushout A χ hcentral) =
      (d, 0) := by
  obtain ⟨x, rfl⟩ :=
    (cyclicPushoutKernelEquiv A χ hcentral).surjective d
  have hx :
      (((cyclicPushoutKernelEquiv A χ hcentral).toLieHom x :
          CyclicPushoutKernel A χ hcentral) : CyclicPushout A χ hcentral) =
        cyclicPushoutInclD A χ hcentral x := rfl
  rw [hx]
  change
    ((cyclicPushoutKernelEquiv A χ hcentral).toLinearEquiv.prodCongr
      (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.toLinearEquiv)
        (cyclicPushoutAddEquiv A χ hcentral
          (cyclicPushoutInclD A χ hcentral x)) =
      (cyclicPushoutKernelEquiv A χ hcentral x, 0)
  rw [cyclicPushoutAddEquiv_inclD, LinearEquiv.prodCongr_apply]
  simp

/-- Finite generation of the original Lie ring passes to the quotient by the
actual kernel of its cyclic pushout. -/
theorem cyclicPushoutQuotKernel_isFinitelyGenerated
    (hK : IsFinitelyGenerated K) :
    IsFinitelyGenerated
      (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral) := by
  exact LieRings.IsFinitelyGenerated.map
    (LieRings.IsFinitelyGenerated.quotient hK A)
      (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.toLieHom
      (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.surjective

/-- If the original ring has zero `c`th lower-central term, then so does the
quotient by the actual kernel of its cyclic pushout. -/
theorem cyclicPushoutQuotKernel_lowerCentralSeries_eq_bot
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) :
    lowerCentralSeries ℤ
      (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral) c = ⊥ := by
  have hq : Function.Surjective (UEA.lieIdealQuotientMk ℤ K A) :=
    LieSubmodule.Quotient.surjective_mk' A
  have hclass' :
      LieModule.lowerCentralSeries ℤ K K c = ⊥ := hclass
  have hbase : lowerCentralSeries ℤ (K ⧸ A) c = ⊥ := by
    change LieModule.lowerCentralSeries ℤ (K ⧸ A) (K ⧸ A) c = ⊥
    calc
      LieModule.lowerCentralSeries ℤ (K ⧸ A) (K ⧸ A) c =
          LieIdeal.map (UEA.lieIdealQuotientMk ℤ K A)
            (LieModule.lowerCentralSeries ℤ K K c) :=
        (LieIdeal.lowerCentralSeries_map_eq c hq).symm
      _ = LieIdeal.map (UEA.lieIdealQuotientMk ℤ K A) ⊥ :=
        congrArg (LieIdeal.map (UEA.lieIdealQuotientMk ℤ K A)) hclass'
      _ = ⊥ := by simp
  have hbase' :
      LieModule.lowerCentralSeries ℤ (K ⧸ A) (K ⧸ A) c = ⊥ := hbase
  change LieModule.lowerCentralSeries ℤ
    (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral)
      (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral) c = ⊥
  calc
    LieModule.lowerCentralSeries ℤ
        (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral)
        (CyclicPushout A χ hcentral ⧸ CyclicPushoutKernel A χ hcentral) c =
        LieIdeal.map
          (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.toLieHom
          (LieModule.lowerCentralSeries ℤ (K ⧸ A) (K ⧸ A) c) :=
      (LieIdeal.lowerCentralSeries_map_eq c
        (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.surjective).symm
    _ = LieIdeal.map
          (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.toLieHom ⊥ :=
      congrArg
        (LieIdeal.map
          (cyclicPushoutQuotKernelEquiv A χ hcentral).symm.toLieHom) hbase'
    _ = ⊥ := by simp

end

end


end LieRings.Plotkin

assert_no_sorry LieRings.Plotkin.cyclicPushoutKernelEquiv
assert_no_sorry LieRings.Plotkin.cyclicPushoutQuotKernelEquiv
assert_no_sorry LieRings.Plotkin.cyclicPushoutKernelAddEquiv
assert_no_sorry LieRings.Plotkin.cyclicPushoutQuotKernel_lowerCentralSeries_eq_bot
