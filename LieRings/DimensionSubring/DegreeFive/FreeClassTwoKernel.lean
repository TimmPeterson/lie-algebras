import LieRings.DimensionSubring.DegreeFive.RelationTruncation

/-!
# The kernel of free class-two truncation

The explicit map from the free Lie ring to `P ⊕ ⋀²P` has kernel exactly the third lower-central
term.  The reverse inclusion was already used in relation truncation; this file proves the
converse by constructing the inverse map into the class-two quotient.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

/-- Evaluation of the explicit free class-two model back into the free Lie ring modulo `γ₃`. -/
def freeClassTwoToFreeLieModGammaThree :
    FreeClassTwo (GeneratorModule X) →ₗ⁅ℤ⁆
      ModGammaThree (CanonicalFreeLie X) :=
  freeClassTwoEvaluation (GeneratorModule X) (CanonicalFreeLie X)
    (freeLieDegreeOne X)

/-- Evaluation after class-two truncation is the canonical quotient map modulo `γ₃`. -/
theorem freeClassTwoToFreeLieModGammaThree_comp_truncation :
    (freeClassTwoToFreeLieModGammaThree X).comp (freeClassTwoTruncation X) =
      UEA.lieIdealQuotientMk ℤ (CanonicalFreeLie X)
        (lowerCentralSeries ℤ (CanonicalFreeLie X) 2) := by
  apply FreeLieAlgebra.hom_ext
  intro x
  change freeClassTwoToFreeLieModGammaThree X
      (freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x)) =
    (LieSubmodule.Quotient.mk (FreeLieAlgebra.of ℤ x) :
      ModGammaThree (CanonicalFreeLie X))
  rw [freeClassTwoTruncation_of]
  rw [freeClassTwoToFreeLieModGammaThree, freeClassTwoEvaluation_apply]
  rw [freeLieDegreeOne_single, map_zero, add_zero]

/-- The kernel of the explicit truncation is exactly `γ₃` of the free Lie ring. -/
theorem freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two
    (x : CanonicalFreeLie X) :
    freeClassTwoTruncation X x = 0 ↔
      x ∈ lowerCentralSeries ℤ (CanonicalFreeLie X) 2 := by
  constructor
  · intro hx
    have hcomp := LieHom.congr_fun
      (freeClassTwoToFreeLieModGammaThree_comp_truncation X) x
    change freeClassTwoToFreeLieModGammaThree X (freeClassTwoTruncation X x) =
      (LieSubmodule.Quotient.mk x : ModGammaThree (CanonicalFreeLie X)) at hcomp
    rw [hx, map_zero] at hcomp
    exact (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ (CanonicalFreeLie X) 2)).mp hcomp.symm
  · intro hx
    have hmem : freeClassTwoTruncation X x ∈
        lowerCentralSeries ℤ (FreeClassTwo (GeneratorModule X)) 2 := by
      change freeClassTwoTruncation X x ∈
        LieModule.lowerCentralSeries ℤ (FreeClassTwo (GeneratorModule X))
          (FreeClassTwo (GeneratorModule X)) 2
      rw [← LieIdeal.lowerCentralSeries_map_eq 2
        (freeClassTwoTruncation_surjective X)]
      exact LieIdeal.mem_map hx
    change freeClassTwoTruncation X x ∈
      LieModule.lowerCentralSeries ℤ (FreeClassTwo (GeneratorModule X))
        (FreeClassTwo (GeneratorModule X)) 2 at hmem
    rw [FreeClassTwo.lowerCentralSeries_two_eq_bot] at hmem
    simpa using hmem

/-- Submodule form of the same kernel computation. -/
theorem freeClassTwoTruncation_ker :
    LinearMap.ker (freeClassTwoTruncation X).toLinearMap =
      (lowerCentralSeries ℤ (CanonicalFreeLie X) 2).toSubmodule := by
  ext x
  rw [LinearMap.mem_ker]
  exact freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two X x

end

end DegreeFive

end LieRings
