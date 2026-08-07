import LieRings.DimensionSubring.Centrality
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# The second Lie dimension subring

This file proves, without PBW, that

`dimensionSubring R L 2 = lowerCentralSeries R L 1`.

In conventional notation this is `delta_2(L) = gamma_2(L)`.  The proof maps `U(L)` to the
trivial square-zero extension of the abelianization `L / gamma_2(L)`.  Since the square of its
degree-one ideal is zero, an element of `L` whose canonical image belongs to the square of the
augmentation ideal must vanish in the abelianization.
-/

namespace LieRings

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

namespace DegreeTwo

/-- The abelianization `L / gamma_2(L)`, where this library numbers `gamma_2` by `1`. -/
abbrev Abelianization := L ⧸ lowerCentralSeries R L 1

local instance abelianizationModuleOp : Module Rᵐᵒᵖ (Abelianization R L) :=
  Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

local instance abelianizationIsCentralScalar : IsCentralScalar R (Abelianization R L) :=
  ⟨fun _ _ ↦ rfl⟩

/-- The degree-one map from `L` to the square-zero extension of its abelianization. -/
def toSquareZeroLieHom :
    L →ₗ⁅R⁆ TrivSqZeroExt R (Abelianization R L) where
  toLinearMap := (TrivSqZeroExt.inrHom R (Abelianization R L)).comp
    (lowerCentralSeries R L 1).toSubmodule.mkQ
  map_lie' := by
    intro x y
    have hxy : ⁅x, y⁆ ∈ lowerCentralSeries R L 1 := by
      rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
    have hq :
        (LieSubmodule.Quotient.mk ⁅x, y⁆ : Abelianization R L) = 0 :=
      (LieSubmodule.Quotient.mk_eq_zero' (N := lowerCentralSeries R L 1)).2 hxy
    change TrivSqZeroExt.inr
        (LieSubmodule.Quotient.mk ⁅x, y⁆ : Abelianization R L) =
      ⁅TrivSqZeroExt.inr (LieSubmodule.Quotient.mk x : Abelianization R L),
        TrivSqZeroExt.inr (LieSubmodule.Quotient.mk y : Abelianization R L)⁆
    rw [hq, TrivSqZeroExt.inr_zero]
    simp [LieRing.of_associative_ring_bracket, TrivSqZeroExt.inr_mul_inr]

@[simp]
theorem toSquareZeroLieHom_apply (x : L) :
    toSquareZeroLieHom R L x =
      TrivSqZeroExt.inr
        (LieSubmodule.Quotient.mk x : Abelianization R L) :=
  rfl

/-- The representation of `U(L)` that remembers scalars and the abelianized degree-one part. -/
noncomputable def squareZeroRepresentation :
    UEA R L →ₐ[R] TrivSqZeroExt R (Abelianization R L) :=
  UniversalEnvelopingAlgebra.lift R (toSquareZeroLieHom R L)

@[simp]
theorem squareZeroRepresentation_ι (x : L) :
    squareZeroRepresentation R L (UniversalEnvelopingAlgebra.ι R x) =
      TrivSqZeroExt.inr
        (LieSubmodule.Quotient.mk x : Abelianization R L) := by
  simp [squareZeroRepresentation]

/-- The scalar coordinate of the square-zero representation is the augmentation. -/
theorem fst_squareZeroRepresentation (u : UEA R L) :
    TrivSqZeroExt.fstHom R R (Abelianization R L)
        (squareZeroRepresentation R L u) = UEA.augmentation R L u := by
  have hmaps :
      (TrivSqZeroExt.fstHom R R (Abelianization R L)).comp
          (squareZeroRepresentation R L) = UEA.augmentation R L := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change TrivSqZeroExt.fstHom R R (Abelianization R L)
        (squareZeroRepresentation R L (UniversalEnvelopingAlgebra.ι R x)) =
      UEA.augmentation R L (UniversalEnvelopingAlgebra.ι R x)
    rw [squareZeroRepresentation_ι, UEA.augmentation_ι]
    rfl
  exact AlgHom.congr_fun hmaps u

/-- The augmentation ideal is sent into the square-zero ideal. -/
theorem squareZeroRepresentation_mem_kerIdeal
    {u : UEA R L} (hu : u ∈ UEA.augmentationIdeal R L) :
    squareZeroRepresentation R L u ∈
      TrivSqZeroExt.kerIdeal R (Abelianization R L) := by
  rw [TrivSqZeroExt.kerIdeal, RingHom.mem_ker]
  rw [fst_squareZeroRepresentation R L u]
  exact (UEA.mem_augmentationIdeal R L).mp hu

/-- The square of the augmentation ideal is killed by the square-zero representation. -/
theorem squareZeroRepresentation_eq_zero_of_mem_sq
    {u : UEA R L} (hu : u ∈ UEA.augmentationIdeal R L ^ 2) :
    squareZeroRepresentation R L u = 0 := by
  have hu' : u ∈ UEA.augmentationIdeal R L * UEA.augmentationIdeal R L := by
    simpa only [show (2 : ℕ) = 1 + 1 by rfl, Submodule.pow_succ,
      Submodule.pow_one, Submodule.pow_zero, Submodule.one_mul] using hu
  refine Submodule.mul_induction_on hu' ?_ ?_
  · intro a ha b hb
    rw [map_mul]
    have ha' := squareZeroRepresentation_mem_kerIdeal R L ha
    have hb' := squareZeroRepresentation_mem_kerIdeal R L hb
    rw [TrivSqZeroExt.mem_kerIdeal_iff_inr] at ha' hb'
    rw [ha', hb', TrivSqZeroExt.inr_mul_inr]
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

end DegreeTwo

/-- **Second dimension-subring theorem.**  In conventional notation, `delta_2(L) = gamma_2(L)`.

The library uses mathlib's zero-based lower-central-series indexing, so `gamma_2(L)` is written
`lowerCentralSeries R L 1`.
-/
theorem dimensionSubring_two_eq_lowerCentralSeries_one :
    dimensionSubring R L 2 = lowerCentralSeries R L 1 := by
  apply le_antisymm
  · intro x hx
    have hzero :
        DegreeTwo.squareZeroRepresentation R L
            (UniversalEnvelopingAlgebra.ι R x) = 0 :=
      DegreeTwo.squareZeroRepresentation_eq_zero_of_mem_sq R L
        ((mem_dimensionSubring R L).mp hx)
    have hinr :
        (TrivSqZeroExt.inr
            (LieSubmodule.Quotient.mk x : DegreeTwo.Abelianization R L) :
              TrivSqZeroExt R (DegreeTwo.Abelianization R L)) = 0 := by
      rw [DegreeTwo.squareZeroRepresentation_ι] at hzero
      exact hzero
    have hmk :
        (LieSubmodule.Quotient.mk x : DegreeTwo.Abelianization R L) = 0 := by
      apply TrivSqZeroExt.inr_injective (R := R)
      simpa using hinr
    exact (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries R L 1)).mp hmk
  · simpa using lowerCentralSeries_le_dimensionSubring R L 1

end LieRings
