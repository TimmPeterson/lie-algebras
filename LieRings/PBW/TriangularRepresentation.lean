import LieRings.PBW.Surjectivity
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The representation-theoretic half of PBW

Cartan--Eilenberg prove linear independence of the ordered PBW monomials by constructing a
representation of `L` on the polynomial module.  The decisive property is that an ordered product
of basis elements sends the constant polynomial `1` to the corresponding commutative monomial.

This file isolates that property and proves all consequences of it.  In particular, once the
Cartan--Eilenberg representation has been constructed, no further linear-independence argument is
needed: evaluation at `1` is a left inverse to `orderedPBWMap`.
-/

namespace LieRings.PBW

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
variable (ι : Type w)

/-- Write a vector in the chosen basis and replace each basis vector `b i` by the variable `X i`. -/
noncomputable def basisPolynomial (b : Module.Basis ι R L) :
    L →ₗ[R] MvPolynomial ι R :=
  (Finsupp.linearCombination R (MvPolynomial.X : ι → MvPolynomial ι R)).comp
    b.repr.toLinearMap

@[simp]
theorem basisPolynomial_basis (b : Module.Basis ι R L) (i : ι) :
    basisPolynomial R L ι b (b i) = MvPolynomial.X i := by
  simp [basisPolynomial]

/-- Degree-one polynomials retain all basis coordinates. -/
theorem basisPolynomial_injective (b : Module.Basis ι R L) :
    Function.Injective (basisPolynomial R L ι b) :=
  (MvPolynomial.linearIndependent_X ι R).finsuppLinearCombination_injective.comp
    b.repr.injective

variable [LinearOrder ι]

/-- The ordered PBW map agrees with the canonical map on the degree-one copy of `L`. -/
theorem orderedPBWMap_basisPolynomial (b : Module.Basis ι R L) (x : L) :
    orderedPBWMap R L ι b (basisPolynomial R L ι b x) =
      UniversalEnvelopingAlgebra.ι R x := by
  let lhs : L →ₗ[R] UEA R L :=
    (orderedPBWMap R L ι b).comp (basisPolynomial R L ι b)
  change lhs x =
    (UniversalEnvelopingAlgebra.ι R : LieHom R L (UEA R L)).toLinearMap x
  have h : lhs =
      (UniversalEnvelopingAlgebra.ι R : LieHom R L (UEA R L)).toLinearMap := by
    apply b.ext
    intro i
    simp [lhs]
  exact LinearMap.congr_fun h x

/-- Any proof of ordered free-module PBW implies that `L → U(L)` is injective. -/
theorem canonicalMap_injective_of_freeModulePBW (b : Module.Basis ι R L)
    (hPBW : FreeModulePBW R L ι b) :
    Function.Injective
      (UniversalEnvelopingAlgebra.ι R : L → UEA R L) := by
  intro x y hxy
  apply basisPolynomial_injective R L ι b
  apply hPBW.1
  simpa only [orderedPBWMap_basisPolynomial] using hxy

/--
The exact output required from the Cartan--Eilenberg triangular-action construction.

`toLieHom` is a representation of `L` on the polynomial module.  The second field says that the
ordered PBW word with exponent vector `e`, acting on the vacuum `1`, gives precisely `X^e`.
-/
structure TriangularRepresentation (b : Module.Basis ι R L) where
  toLieHom : LieHom R L (Module.End R (MvPolynomial ι R))
  orderedMonomial_apply_one : ∀ e : ι →₀ ℕ,
    UniversalEnvelopingAlgebra.lift R toLieHom (orderedMonomial R L ι b e) 1 =
      MvPolynomial.monomial e 1

namespace TriangularRepresentation

variable {R L ι}
variable {b : Module.Basis ι R L}

/-- The action of `U(L)` supplied by a triangular representation. -/
noncomputable def envelopingAction (P : TriangularRepresentation R L ι b) :
    UEA R L →ₐ[R] Module.End R (MvPolynomial ι R) :=
  UniversalEnvelopingAlgebra.lift R P.toLieHom

@[simp]
theorem envelopingAction_ι (P : TriangularRepresentation R L ι b) (x : L) :
    P.envelopingAction (UniversalEnvelopingAlgebra.ι R x) = P.toLieHom x := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply R P.toLieHom x

/-- Evaluate the induced `U(L)`-action at the constant polynomial `1`. -/
noncomputable def vacuumEvaluation (P : TriangularRepresentation R L ι b) :
    UEA R L →ₗ[R] MvPolynomial ι R :=
  (LinearMap.applyₗ (1 : MvPolynomial ι R)).comp P.envelopingAction.toLinearMap

@[simp]
theorem vacuumEvaluation_apply (P : TriangularRepresentation R L ι b) (u : UEA R L) :
    P.vacuumEvaluation u = P.envelopingAction u 1 :=
  rfl

@[simp]
theorem vacuumEvaluation_orderedMonomial
    (P : TriangularRepresentation R L ι b) (e : ι →₀ ℕ) :
    P.vacuumEvaluation (orderedMonomial R L ι b e) =
      MvPolynomial.monomial e 1 :=
  P.orderedMonomial_apply_one e

@[simp]
theorem toLieHom_basis_apply_one
    (P : TriangularRepresentation R L ι b) (i : ι) :
    P.toLieHom (b i) 1 = MvPolynomial.X i := by
  have h := P.orderedMonomial_apply_one (Finsupp.single i 1)
  rw [orderedMonomial_single, UniversalEnvelopingAlgebra.lift_ι_apply] at h
  simpa [MvPolynomial.X] using h

/-- Acting on `1` recovers the degree-one polynomial carrying the coordinates of `x`. -/
theorem toLieHom_apply_one (P : TriangularRepresentation R L ι b) (x : L) :
    P.toLieHom x 1 = basisPolynomial R L ι b x := by
  let actionOnOne : L →ₗ[R] MvPolynomial ι R :=
    (LinearMap.applyₗ (1 : MvPolynomial ι R)).comp P.toLieHom.toLinearMap
  change actionOnOne x = basisPolynomial R L ι b x
  have h : actionOnOne = basisPolynomial R L ι b := by
    apply b.ext
    intro i
    simp [actionOnOne]
  exact LinearMap.congr_fun h x

/-- The Cartan--Eilenberg representation is faithful. -/
theorem toLieHom_injective (P : TriangularRepresentation R L ι b) :
    Function.Injective P.toLieHom := by
  intro x y hxy
  apply basisPolynomial_injective R L ι b
  rw [← P.toLieHom_apply_one x, ← P.toLieHom_apply_one y, hxy]

@[simp]
theorem vacuumEvaluation_orderedPBWMap_monomial
    (P : TriangularRepresentation R L ι b) (e : ι →₀ ℕ) (r : R) :
    P.vacuumEvaluation
        (orderedPBWMap R L ι b (MvPolynomial.monomial e r)) =
      MvPolynomial.monomial e r := by
  rw [orderedPBWMap_monomial, map_smul, vacuumEvaluation_orderedMonomial]
  simp [MvPolynomial.smul_monomial]

/-- Evaluation at the vacuum is a left inverse to the ordered PBW map. -/
theorem vacuumEvaluation_orderedPBWMap
    (P : TriangularRepresentation R L ι b) (p : MvPolynomial ι R) :
    P.vacuumEvaluation (orderedPBWMap R L ι b p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e r => exact P.vacuumEvaluation_orderedPBWMap_monomial e r
  | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq

/-- The ordered PBW map is injective as soon as the triangular representation exists. -/
theorem orderedPBWMap_injective (P : TriangularRepresentation R L ι b) :
    Function.Injective (orderedPBWMap R L ι b) := by
  intro p q hpq
  calc
    p = P.vacuumEvaluation (orderedPBWMap R L ι b p) :=
      (P.vacuumEvaluation_orderedPBWMap p).symm
    _ = P.vacuumEvaluation (orderedPBWMap R L ι b q) := congrArg P.vacuumEvaluation hpq
    _ = q := P.vacuumEvaluation_orderedPBWMap q

/-- **Free-module PBW from the Cartan--Eilenberg representation.** -/
theorem freeModulePBW (P : TriangularRepresentation R L ι b) :
    FreeModulePBW R L ι b := by
  rw [freeModulePBW_iff_orderedPBWMap_injective]
  exact P.orderedPBWMap_injective

/-- In particular, the canonical map `L → U(L)` is injective. -/
theorem canonicalMap_injective (P : TriangularRepresentation R L ι b) :
    Function.Injective
      (UniversalEnvelopingAlgebra.ι R : L → UEA R L) :=
  canonicalMap_injective_of_injective_lieHom R L
    (Module.End R (MvPolynomial ι R)) P.toLieHom P.toLieHom_injective

/-- The ordered PBW map, packaged as a linear equivalence. -/
noncomputable def orderedPBWLinearEquiv (P : TriangularRepresentation R L ι b) :
    MvPolynomial ι R ≃ₗ[R] UEA R L :=
  LinearEquiv.ofBijective (orderedPBWMap R L ι b) P.freeModulePBW

end TriangularRepresentation

end LieRings.PBW
