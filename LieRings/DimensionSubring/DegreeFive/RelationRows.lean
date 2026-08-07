import LieRings.DimensionSubring.DegreeFive.FreeClassTwoKernel
import LieRings.DimensionSubring.DegreeFive.PresentationKernel

/-!
# Canonical low-weight relation rows

Surjectivity of relation truncation lets us choose, without bases or Smith normal form, one
relation row above every relation in the explicit class-two resolution.  Subtracting that row
from an arbitrary defining relation leaves a relation in `γ₃` of the free Lie ring.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- A fixed relation lift of every class-two resolution relation. -/
def relationRow (q : ClassTwoResolutionRelations L) :
    CanonicalLieRelations L :=
  Function.surjInv (relationTruncation_surjective L) q

@[simp]
theorem relationTruncation_relationRow (q : ClassTwoResolutionRelations L) :
    relationTruncation L (relationRow L q) = q :=
  Function.rightInverse_surjInv (relationTruncation_surjective L) q

/-- The chosen low row associated with a defining Lie-ideal relation. -/
def relationIdealRow (r : CanonicalLieRelationsIdeal L) :
    CanonicalLieRelationsIdeal L :=
  ⟨(relationRow L (relationTruncation L
      (r : CanonicalLieRelations L)) : CanonicalFreeLie L),
    (relationRow L (relationTruncation L
      (r : CanonicalLieRelations L))).property⟩

/-- The part of a relation remaining after its weight-one-plus-two row is removed. -/
def relationRowRemainder (r : CanonicalLieRelationsIdeal L) :
    CanonicalLieRelationsIdeal L :=
  ⟨(r : CanonicalFreeLie L) - (relationIdealRow L r : CanonicalFreeLie L), by
    rw [LieHom.mem_ker, map_sub]
    rw [show canonicalFreeLieEvaluation L (r : CanonicalFreeLie L) = 0 from r.property]
    rw [show canonicalFreeLieEvaluation L
        (relationIdealRow L r : CanonicalFreeLie L) = 0 from
      (relationIdealRow L r).property]
    exact sub_zero 0⟩

theorem relation_eq_row_add_remainder (r : CanonicalLieRelationsIdeal L) :
    (r : CanonicalFreeLie L) =
      (relationIdealRow L r : CanonicalFreeLie L) +
        (relationRowRemainder L r : CanonicalFreeLie L) := by
  simp [relationRowRemainder]

/-- The row remainder has zero class-two truncation. -/
theorem relationTruncation_rowRemainder_eq_zero
    (r : CanonicalLieRelationsIdeal L) :
    freeClassTwoTruncation L
        (relationRowRemainder L r : CanonicalFreeLie L) = 0 := by
  rw [relationRowRemainder, map_sub]
  change freeClassTwoTruncation L (r : CanonicalFreeLie L) -
      freeClassTwoTruncation L (relationIdealRow L r : CanonicalFreeLie L) = 0
  change (relationTruncation L (r : CanonicalLieRelations L) :
      FreeClassTwo (GeneratorModule L)) -
    (relationTruncation L (relationRow L
      (relationTruncation L (r : CanonicalLieRelations L))) :
        FreeClassTwo (GeneratorModule L)) = 0
  rw [relationTruncation_relationRow, sub_self]

/-- Consequently every row remainder has least Lie weight at least three. -/
theorem relationRowRemainder_mem_lowerCentralSeries_two
    (r : CanonicalLieRelationsIdeal L) :
    (relationRowRemainder L r : CanonicalFreeLie L) ∈
      lowerCentralSeries ℤ (CanonicalFreeLie L) 2 := by
  exact (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two L
    (relationRowRemainder L r : CanonicalFreeLie L)).mp
      (relationTruncation_rowRemainder_eq_zero L r)

/-- Equality-level row expansion for a tagged relation product in the enveloping algebra. -/
theorem iota_relation_mul_eq_row_add_remainder
    (r : CanonicalLieRelationsIdeal L)
    (u : UEA ℤ (CanonicalFreeLie L)) :
    UniversalEnvelopingAlgebra.ι ℤ (r : CanonicalFreeLie L) * u =
      UniversalEnvelopingAlgebra.ι ℤ
          (relationIdealRow L r : CanonicalFreeLie L) * u +
        UniversalEnvelopingAlgebra.ι ℤ
          (relationRowRemainder L r : CanonicalFreeLie L) * u := by
  rw [relation_eq_row_add_remainder L r, map_add, add_mul]

end

end DegreeFive

end LieRings
