import LieRings.Homological.PresentationComparison
import Mathlib.Util.AssertNoSorry

/-!
# Compile gates for the integral Koszul construction

These examples exercise the public formulas used in weights two and three,
the all-degree square-zero theorem, stabilization by a rank-two unit
presentation, cylinder homotopy invariance, and descent of a character through
resolution comparison.
-/

open TensorProduct

namespace Koszul.Tests

noncomputable section

universe u v w

variable {A : Type u} [AddCommGroup A]
variable (P : Presentation.{u, v, w} A)

example (a : Fin 2 → P.rel) (s : Sym[ℤ] (Fin 0) P.gen) :
    dTwo P 0 (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s) =
      a 0 ⊗ₜ[ℤ] SymmetricPower.insert ℤ P.gen 0 (P.d (a 1)) s -
        a 1 ⊗ₜ[ℤ] SymmetricPower.insert ℤ P.gen 0 (P.d (a 0)) s :=
  dTwo_wedge_tmul P 0 a s

example (a : Fin 2 → P.rel) (s : Sym[ℤ] (Fin 1) P.gen) :
    dTwo P 1 (exteriorPower.ιMulti ℤ 2 a ⊗ₜ[ℤ] s) =
      a 0 ⊗ₜ[ℤ] SymmetricPower.insert ℤ P.gen 1 (P.d (a 1)) s -
        a 1 ⊗ₜ[ℤ] SymmetricPower.insert ℤ P.gen 1 (P.d (a 0)) s :=
  dTwo_wedge_tmul P 1 a s

example :
    (AllDegrees.differential P.d 0 1).comp
        (AllDegrees.differential P.d 1 0) = 0 :=
  AllDegrees.differential_comp_differential P.d 0 0

example :
    (AllDegrees.differential P.d 1 1).comp
        (AllDegrees.differential P.d 2 0) = 0 :=
  AllDegrees.differential_comp_differential P.d 1 0

example : CategoryTheory.Limits.IsZero ((complex P 2).X 3) :=
  complex_isZero_above P 2 3 (by omega)

example : CategoryTheory.Limits.IsZero ((complex P 3).X 4) :=
  complex_isZero_above P 3 4 (by omega)

example (q : ℕ) :
    ModuleCat.of ℤ (homologyOne P q) ≅
      (lowDegreeShortComplex (P := P) q).homology :=
  homologyOneIsoCategorical P q

example (q : ℕ) :
    homologyOne (Presentation.stabilize P (Fin 2 → ℤ)) q
      ≃ₗ[ℤ] homologyOne P q :=
  Presentation.stabilizeHomologyEquiv P (Fin 2 → ℤ) q

example (x : One (Presentation.stabilize P (Fin 2 → ℤ)) 1) :
    dTwo (Presentation.stabilize P (Fin 2 → ℤ)) 0
        (Presentation.hOne P (Fin 2 → ℤ) 0 x) +
      Presentation.hZero P (Fin 2 → ℤ) 1
        (dOne (Presentation.stabilize P (Fin 2 → ℤ)) 1 x) =
      x - PresentationHomology.oneMap
        (Presentation.stabilize P (Fin 2 → ℤ))
        (Presentation.stabilize P (Fin 2 → ℤ))
        ((Presentation.stabilizeIncl P (Fin 2 → ℤ)).comp
          (Presentation.stabilizeProj P (Fin 2 → ℤ))) 1 x :=
  Presentation.stabilizationContractionIdentity P (Fin 2 → ℤ) 0 x

example (x : One (Presentation.stabilize P (Fin 2 → ℤ)) 2) :
    dTwo (Presentation.stabilize P (Fin 2 → ℤ)) 1
        (Presentation.hOne P (Fin 2 → ℤ) 1 x) +
      Presentation.hZero P (Fin 2 → ℤ) 2
        (dOne (Presentation.stabilize P (Fin 2 → ℤ)) 2 x) =
      x - PresentationHomology.oneMap
        (Presentation.stabilize P (Fin 2 → ℤ))
        (Presentation.stabilize P (Fin 2 → ℤ))
        ((Presentation.stabilizeIncl P (Fin 2 → ℤ)).comp
          (Presentation.stabilizeProj P (Fin 2 → ℤ))) 2 x :=
  Presentation.stabilizationContractionIdentity P (Fin 2 → ℤ) 1 x

example {B : Type*} [AddCommGroup B] (Q : Presentation B)
    {f : A →ₗ[ℤ] B} (F G : Presentation.Hom P Q f) (q : ℕ) :
    PresentationHomology.map P Q F q =
      PresentationHomology.map P Q G q :=
  Presentation.homologyMap_eq_of_homotopy P Q F G q

example [Finite A] (q : ℕ) :
    homologyOne P q ≃ₗ[ℤ]
      FirstDerivedSymmetricPower q A :=
  Presentation.homologyComparisonEquiv P q

example {B : Type*} [AddCommGroup B] [Finite A] [Finite B]
    (Q : Presentation B) {f : A →ₗ[ℤ] B}
    (F : Presentation.Hom P Q f) (q : ℕ) :
    (Presentation.homologyComparisonEquiv Q q).toLinearMap.comp
        (PresentationHomology.map P Q F q) =
      PresentationHomology.map (Presentation.canonical A)
          (Presentation.canonical B) (Presentation.canonicalHom f) q ∘ₗ
        (Presentation.homologyComparisonEquiv P q).toLinearMap :=
  Presentation.homologyComparison_natural P Q F q

/-- A cycle character which kills boundaries descends through the quotient and
then through the presentation-comparison equivalence. -/
example [Finite A] {N : Type*} [AddCommGroup N]
    (χ : cyclesOne P 1 →ₗ[ℤ] N)
    (hχ : boundariesOne P 1 ≤ LinearMap.ker χ) :
    FirstDerivedSymmetricPower 1 A →ₗ[ℤ] N :=
  ((boundariesOne P 1).liftQ χ hχ).comp
    (Presentation.homologyComparisonEquiv P 1).symm.toLinearMap

end

end Koszul.Tests

assert_no_sorry Koszul.Presentation.stabilizeHomologyEquiv
assert_no_sorry Koszul.Presentation.homologyComparisonEquiv
assert_no_sorry Koszul.Presentation.homologyComparison_natural
