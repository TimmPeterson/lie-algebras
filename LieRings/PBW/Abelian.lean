import LieRings.PBW.Reduction
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# PBW for Abelian Lie algebras

For an Abelian Lie algebra, the enveloping algebra is the symmetric algebra.  This is the easiest
complete PBW case and does not require a basis.
-/

namespace LieRings.PBW

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [IsLieAbelian L]

/-- The universal enveloping algebra of an Abelian Lie algebra is commutative. -/
theorem commute_uea_of_isLieAbelian (a b : UEA R L) : Commute a b := by
  induction b using UEA.induction R L with
  | algebraMap r => exact Algebra.commute_algebraMap_right _ _
  | ι x =>
      induction a using UEA.induction R L with
      | algebraMap r => exact Algebra.commute_algebraMap_left _ _
      | ι y =>
          rw [commute_iff_eq]
          have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) y x
          rw [trivial_lie_zero] at h
          simp only [map_zero, LieRing.of_associative_ring_bracket] at h
          exact sub_eq_zero.mp h.symm
      | mul a b ha hb => exact ha.mul_left hb
      | add a b ha hb => exact ha.add_left hb
  | mul b c hb hc => exact hb.mul_right hc
  | add b c hb hc => exact hb.add_right hc

/-- The canonical Lie morphism from an Abelian Lie algebra to its symmetric algebra. -/
def toSymmetricLieHom : L →ₗ⁅R⁆ SymmetricAlgebra R L :=
  { SymmetricAlgebra.ι R L with
    map_lie' := fun {x y} =>
      calc
        SymmetricAlgebra.ι R L ⁅x, y⁆ = 0 := by
          rw [trivial_lie_zero]
          exact LinearMap.map_zero (SymmetricAlgebra.ι R L)
        _ = ⁅SymmetricAlgebra.ι R L x, SymmetricAlgebra.ι R L y⁆ := by
          rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self] }

/-- The canonical morphism `U(L) → SymmetricAlgebra R L` for Abelian `L`. -/
def abelianToSymmetric : UEA R L →ₐ[R] SymmetricAlgebra R L :=
  UniversalEnvelopingAlgebra.lift R (toSymmetricLieHom R L)

@[simp]
theorem abelianToSymmetric_ι (x : L) :
    abelianToSymmetric R L (UniversalEnvelopingAlgebra.ι R x) =
      SymmetricAlgebra.ι R L x := by
  change UniversalEnvelopingAlgebra.lift R (toSymmetricLieHom R L)
    (UniversalEnvelopingAlgebra.ι R x) = SymmetricAlgebra.ι R L x
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- Complete PBW in the Abelian case: `U(L) ≃ SymmetricAlgebra R L`. -/
noncomputable def abelianEquivSymmetric :
    UEA R L ≃ₐ[R] SymmetricAlgebra R L := by
  letI : CommRing (UEA R L) :=
    { (inferInstance : Ring (UEA R L)) with
      mul_comm := fun a b => (commute_uea_of_isLieAbelian R L a b).eq }
  let toSym : UEA R L →ₐ[R] SymmetricAlgebra R L := abelianToSymmetric R L
  let fromSym : SymmetricAlgebra R L →ₐ[R] UEA R L :=
    SymmetricAlgebra.lift
      (UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ UEA R L).toLinearMap
  exact AlgEquiv.ofAlgHom toSym fromSym
    (by
      ext x
      change abelianToSymmetric R L
          (SymmetricAlgebra.lift
            (UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ UEA R L).toLinearMap
            (SymmetricAlgebra.ι R L x)) = SymmetricAlgebra.ι R L x
      rw [SymmetricAlgebra.lift_ι_apply]
      exact abelianToSymmetric_ι R L x)
    (by
      ext x
      change SymmetricAlgebra.lift
          (UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ UEA R L).toLinearMap
          (abelianToSymmetric R L (UniversalEnvelopingAlgebra.ι R x)) =
        UniversalEnvelopingAlgebra.ι R x
      rw [abelianToSymmetric_ι, SymmetricAlgebra.lift_ι_apply]
      rfl)

@[simp]
theorem abelianEquivSymmetric_ι (x : L) :
    abelianEquivSymmetric R L (UniversalEnvelopingAlgebra.ι R x) =
      SymmetricAlgebra.ι R L x := by
  change abelianToSymmetric R L (UniversalEnvelopingAlgebra.ι R x) =
    SymmetricAlgebra.ι R L x
  exact abelianToSymmetric_ι R L x

end LieRings.PBW
