import LieRings.UniversalEnveloping.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The primitive coproduct on a universal enveloping algebra

This file constructs only the part of the standard Hopf-algebra structure needed by the
degree-five PBW collector.  Keeping it explicit avoids introducing a separate bundled Hopf
algebra API.
-/

namespace LieRings

open scoped TensorProduct

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

namespace UEA

/-- The primitive Lie map `x ↦ ι(x) ⊗ 1 + 1 ⊗ ι(x)`. -/
def primitiveGenerator :
    L →ₗ⁅R⁆ (UEA R L ⊗[R] UEA R L) where
  toLinearMap :=
    (Algebra.TensorProduct.includeLeft.toLinearMap.comp
      (UniversalEnvelopingAlgebra.ι R).toLinearMap) +
    (Algebra.TensorProduct.includeRight.toLinearMap.comp
      (UniversalEnvelopingAlgebra.ι R).toLinearMap)
  map_lie' := by
    intro x y
    let il : UEA R L →ₐ[R] UEA R L ⊗[R] UEA R L :=
      Algebra.TensorProduct.includeLeft
    let ir : UEA R L →ₐ[R] UEA R L ⊗[R] UEA R L :=
      Algebra.TensorProduct.includeRight
    change
      il (UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) +
          ir (UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) =
        ⁅il (UniversalEnvelopingAlgebra.ι R x) +
            ir (UniversalEnvelopingAlgebra.ι R x),
          il (UniversalEnvelopingAlgebra.ι R y) +
            ir (UniversalEnvelopingAlgebra.ι R y)⁆
    simp only [il, ir, LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub, map_mul,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    abel

@[simp]
theorem primitiveGenerator_apply (x : L) :
    primitiveGenerator R L x =
      (UniversalEnvelopingAlgebra.ι R x) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] (UniversalEnvelopingAlgebra.ι R x) := by
  rfl

/-- The standard coproduct on `U(L)`, characterized by making every Lie element primitive. -/
def coproduct : UEA R L →ₐ[R] UEA R L ⊗[R] UEA R L :=
  UniversalEnvelopingAlgebra.lift R (primitiveGenerator R L)

@[simp]
theorem coproduct_ι (x : L) :
    coproduct R L (UniversalEnvelopingAlgebra.ι R x) =
      (UniversalEnvelopingAlgebra.ι R x) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] (UniversalEnvelopingAlgebra.ι R x) := by
  simp [coproduct]

@[simp]
theorem coproduct_algebraMap (r : R) :
    coproduct R L (algebraMap R (UEA R L) r) =
      algebraMap R (UEA R L ⊗[R] UEA R L) r := by
  simp [coproduct]

/-- The reduced coproduct `Δ(u) - u ⊗ 1 - 1 ⊗ u`. -/
def reducedCoproduct : UEA R L →ₗ[R] UEA R L ⊗[R] UEA R L :=
  (coproduct R L).toLinearMap -
    Algebra.TensorProduct.includeLeft.toLinearMap -
      Algebra.TensorProduct.includeRight.toLinearMap

@[simp]
theorem reducedCoproduct_apply (u : UEA R L) :
    reducedCoproduct R L u = coproduct R L u - u ⊗ₜ[R] 1 - 1 ⊗ₜ[R] u := by
  rfl

@[simp]
theorem reducedCoproduct_ι (x : L) :
    reducedCoproduct R L (UniversalEnvelopingAlgebra.ι R x) = 0 := by
  rw [reducedCoproduct_apply, coproduct_ι]
  abel

/-- The reduced coproduct of a product of two primitive Lie elements is its symmetric
two-factor tensor. -/
theorem reducedCoproduct_ι_mul_ι (x y : L) :
    reducedCoproduct R L
        (UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y) =
      (UniversalEnvelopingAlgebra.ι R x) ⊗ₜ[R]
          (UniversalEnvelopingAlgebra.ι R y) +
        (UniversalEnvelopingAlgebra.ι R y) ⊗ₜ[R]
          (UniversalEnvelopingAlgebra.ι R x) := by
  simp only [reducedCoproduct_apply, map_mul, coproduct_ι,
    add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  abel

end UEA

end LieRings
