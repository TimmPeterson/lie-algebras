import LieRings.PBW.Reduction
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The ordered-monomial statement of PBW for a free module

This file defines the exact map that the free-module form of PBW says is an isomorphism.  The
definition is useful now because it fixes the public statement and all indexing conventions; the
proof will be built in later files.
-/

namespace LieRings.PBW

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
variable (ι : Type w) [LinearOrder ι]

/--
The ordered product in `U(L)` belonging to an exponent vector `e : ι →₀ ℕ` and an ordered basis
`b`.  If the support of `e` is `i₁ < ... < iₖ`, this is
`ι(b i₁) ^ (e i₁) * ... * ι(b iₖ) ^ (e iₖ)`.
-/
noncomputable def orderedMonomial (b : Module.Basis ι R L) (e : ι →₀ ℕ) : UEA R L :=
  ((Finsupp.toMultiset e).sort (· ≤ ·)).map
    (fun i => UniversalEnvelopingAlgebra.ι R (b i)) |>.prod

@[simp]
theorem orderedMonomial_zero (b : Module.Basis ι R L) :
    orderedMonomial R L ι b 0 = 1 := by
  simp [orderedMonomial]

@[simp]
theorem orderedMonomial_single (b : Module.Basis ι R L) (i : ι) :
    orderedMonomial R L ι b (Finsupp.single i 1) =
      UniversalEnvelopingAlgebra.ι R (b i) := by
  simp [orderedMonomial]

/--
The PBW ordered-monomial linear map.  A multivariate monomial with exponent vector `e` is sent to
the corresponding ordered product in `U(L)`.
-/
noncomputable def orderedPBWMap (b : Module.Basis ι R L) :
    MvPolynomial ι R →ₗ[R] UEA R L :=
  Finsupp.linearCombination R (orderedMonomial R L ι b)

@[simp]
theorem orderedPBWMap_monomial (b : Module.Basis ι R L) (e : ι →₀ ℕ) (r : R) :
    orderedPBWMap R L ι b (MvPolynomial.monomial e r) =
      r • orderedMonomial R L ι b e := by
  rw [← MvPolynomial.single_eq_monomial]
  exact Finsupp.linearCombination_single R r e

@[simp]
theorem orderedPBWMap_X (b : Module.Basis ι R L) (i : ι) :
    orderedPBWMap R L ι b (MvPolynomial.X i) =
      UniversalEnvelopingAlgebra.ι R (b i) := by
  rw [MvPolynomial.X, orderedPBWMap_monomial, one_smul,
    orderedMonomial_single]

/--
The precise global PBW assertion for a Lie algebra whose underlying `R`-module has the ordered
basis `b`: ordered monomials form an `R`-basis of `U(L)`.

This is a named proposition, not an axiom or a proved theorem.
-/
def FreeModulePBW (b : Module.Basis ι R L) : Prop :=
  Function.Bijective (orderedPBWMap R L ι b)

end LieRings.PBW
