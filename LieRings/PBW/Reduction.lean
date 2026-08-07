import LieRings.UniversalEnveloping.Basic
import Mathlib.Algebra.Lie.Free

/-!
# PBW reductions

This file records small, fully proved reductions that isolate the genuinely missing part of PBW.
It does **not** claim the PBW theorem.
-/

namespace LieRings

universe u v w

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

namespace PBW

/--
If `L` has an injective Lie morphism to an associative `R`-algebra, then the canonical map
`L → U(L)` is injective.
-/
theorem canonicalMap_injective_of_injective_lieHom
    (A : Type w) [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)
    (hf : Function.Injective f) :
    Function.Injective (UniversalEnvelopingAlgebra.ι R : L → UEA R L) := by
  intro x y hxy
  apply hf
  have h := congrArg (UniversalEnvelopingAlgebra.lift R f) hxy
  simpa using h

variable (X : Type v)

/-- The canonical evaluation of the free Lie algebra inside the free associative algebra. -/
noncomputable def freeLieToFreeAlgebra : FreeLieAlgebra R X →ₗ⁅R⁆ FreeAlgebra R X :=
  FreeLieAlgebra.lift R (FreeAlgebra.ι R)

/--
For a free Lie algebra, injectivity of `L → U(L)` is exactly the Magnus--Witt embedding problem.
Mathlib already proves `U(FreeLie(X)) ≃ FreeAlgebra(X)`; what remains is injectivity of the
canonical evaluation `FreeLie(X) → FreeAlgebra(X)`.
-/
theorem freeLie_canonicalMap_injective_iff_magnusWitt :
    Function.Injective
        (UniversalEnvelopingAlgebra.ι R :
          FreeLieAlgebra R X → UniversalEnvelopingAlgebra R (FreeLieAlgebra R X)) ↔
      Function.Injective (freeLieToFreeAlgebra R X) := by
  let e := FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R X
  constructor
  · intro hι x y hxy
    apply hι
    apply e.injective
    simpa [e, freeLieToFreeAlgebra] using hxy
  · intro hfree x y hxy
    apply hfree
    have h := congrArg e hxy
    simpa [e, freeLieToFreeAlgebra] using h

end PBW

end LieRings
