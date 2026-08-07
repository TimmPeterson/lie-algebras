import LieRings.DimensionSubring.DegreeFive.RelationIdeal
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The enveloping kernel of the canonical free presentation

This file identifies the kernel of `U(F) → U(L)` with the collected relation ideal.  It is the
precise presentation criterion needed to lift a fifth-dimension witness to the free associative
algebra.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- Relations as a Lie ideal (rather than only as the underlying linear kernel). -/
abbrev CanonicalLieRelationsIdeal : LieIdeal ℤ (CanonicalFreeLie L) :=
  LieHom.ker (canonicalFreeLieEvaluation L)

/-- The first isomorphism theorem for the canonical free Lie presentation. -/
def canonicalQuotientEquiv :
    (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) ≃ₗ⁅ℤ⁆ L where
  toLieHom :=
    { (canonicalFreeLieEvaluation L).toLinearMap.quotKerEquivOfSurjective
        (canonicalFreeLieEvaluation_surjective L) with
      map_lie' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            change canonicalFreeLieEvaluation L ⁅x, y⁆ =
              ⁅canonicalFreeLieEvaluation L x, canonicalFreeLieEvaluation L y⁆
            exact LieHom.map_lie (canonicalFreeLieEvaluation L) x y }
  invFun := ((canonicalFreeLieEvaluation L).toLinearMap.quotKerEquivOfSurjective
    (canonicalFreeLieEvaluation_surjective L)).symm
  left_inv := ((canonicalFreeLieEvaluation L).toLinearMap.quotKerEquivOfSurjective
    (canonicalFreeLieEvaluation_surjective L)).left_inv
  right_inv := ((canonicalFreeLieEvaluation L).toLinearMap.quotKerEquivOfSurjective
    (canonicalFreeLieEvaluation_surjective L)).right_inv

@[simp]
theorem canonicalQuotientEquiv_mk (x : CanonicalFreeLie L) :
    canonicalQuotientEquiv L (LieSubmodule.Quotient.mk x) =
      canonicalFreeLieEvaluation L x := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk
    (canonicalFreeLieEvaluation L).toLinearMap
    (canonicalFreeLieEvaluation_surjective L) x

/-- The quotient equivalence sends the enveloping quotient map to the associative ideal quotient. -/
theorem quotientEquiv_mapToLieQuotient
    (F : Type*) [LieRing F] [LieAlgebra ℤ F]
    (I : LieIdeal ℤ F) (u : UEA ℤ F) :
    UEA.quotientEquivLieIdeal ℤ F I
        (UEA.mapToLieQuotient ℤ F I u) =
      Ideal.Quotient.mk (UEA.idealOfLieIdeal ℤ F I) u := by
  induction u using UEA.induction ℤ F with
  | algebraMap r => simp
  | ι x => rw [UEA.mapToLieQuotient_ι, UEA.quotientEquivLieIdeal_ι_mk]
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- Evaluation factors through the canonical Lie quotient. -/
theorem canonical_evaluation_factorization (x : CanonicalFreeLie L) :
    canonicalQuotientEquiv L
        (UEA.lieIdealQuotientMk ℤ (CanonicalFreeLie L)
          (CanonicalLieRelationsIdeal L) x) =
      canonicalFreeLieEvaluation L x := by
  exact canonicalQuotientEquiv_mk L x

/-- The induced enveloping map of canonical evaluation factors through the quotient and the
enveloping equivalence induced by the first isomorphism theorem. -/
theorem canonical_uea_evaluation_factorization (u : UEA ℤ (CanonicalFreeLie L)) :
    UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L) u =
      UEA.mapEquiv ℤ
        (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) L
        (canonicalQuotientEquiv L)
        (UEA.mapToLieQuotient ℤ (CanonicalFreeLie L)
          (CanonicalLieRelationsIdeal L) u) := by
  have hhom :
      UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L) =
        (UEA.mapEquiv ℤ
          (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) L
          (canonicalQuotientEquiv L)).toAlgHom.comp
            (UEA.mapToLieQuotient ℤ (CanonicalFreeLie L)
              (CanonicalLieRelationsIdeal L)) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply FreeLieAlgebra.hom_ext
    intro x
    change UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
        (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)) =
      UEA.mapEquiv ℤ (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) L
        (canonicalQuotientEquiv L)
        (UEA.mapToLieQuotient ℤ (CanonicalFreeLie L)
          (CanonicalLieRelationsIdeal L)
          (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)))
    rw [UEA.map_ι, UEA.mapToLieQuotient_ι, UEA.mapEquiv_apply]
    calc
      UniversalEnvelopingAlgebra.ι ℤ
          (canonicalFreeLieEvaluation L (FreeLieAlgebra.of ℤ x)) =
        UniversalEnvelopingAlgebra.ι ℤ
          (canonicalQuotientEquiv L
            (LieSubmodule.Quotient.mk (FreeLieAlgebra.of ℤ x))) :=
          congrArg (UniversalEnvelopingAlgebra.ι ℤ)
            (canonicalQuotientEquiv_mk L (FreeLieAlgebra.of ℤ x)).symm
      _ = UEA.map ℤ (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) L
          (canonicalQuotientEquiv L).toLieHom
          (UniversalEnvelopingAlgebra.ι ℤ
            (LieSubmodule.Quotient.mk (FreeLieAlgebra.of ℤ x))) :=
        (UEA.map_ι ℤ (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) L
          (canonicalQuotientEquiv L).toLieHom _).symm
  exact DFunLike.congr_fun hhom u

/-- **Canonical presentation criterion.** The kernel of `U(F) → U(L)` is exactly the
two-sided ideal generated by the free-Lie relations. -/
theorem mem_kernel_canonical_uea_evaluation_iff (u : UEA ℤ (CanonicalFreeLie L)) :
    UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L) u = 0 ↔
      u ∈ UEA.idealOfLieIdeal ℤ (CanonicalFreeLie L)
        (CanonicalLieRelationsIdeal L) := by
  rw [canonical_uea_evaluation_factorization L u]
  rw [map_eq_zero_iff
    (UEA.mapEquiv ℤ (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) L
      (canonicalQuotientEquiv L))
    (UEA.mapEquiv ℤ (CanonicalFreeLie L ⧸ CanonicalLieRelationsIdeal L) L
      (canonicalQuotientEquiv L)).injective]
  let e := UEA.quotientEquivLieIdeal ℤ (CanonicalFreeLie L)
    (CanonicalLieRelationsIdeal L)
  have he := map_eq_zero_iff e e.injective
    (x := UEA.mapToLieQuotient ℤ (CanonicalFreeLie L)
      (CanonicalLieRelationsIdeal L) u)
  calc
    UEA.mapToLieQuotient ℤ (CanonicalFreeLie L)
          (CanonicalLieRelationsIdeal L) u = 0 ↔
        e (UEA.mapToLieQuotient ℤ (CanonicalFreeLie L)
          (CanonicalLieRelationsIdeal L) u) = 0 := he.symm
    _ ↔ Ideal.Quotient.mk
          (UEA.idealOfLieIdeal ℤ (CanonicalFreeLie L)
            (CanonicalLieRelationsIdeal L)) u = 0 := by
          rw [quotientEquiv_mapToLieQuotient]
    _ ↔ u ∈ UEA.idealOfLieIdeal ℤ (CanonicalFreeLie L)
          (CanonicalLieRelationsIdeal L) := Ideal.Quotient.eq_zero_iff_mem

/-- Collected form of the presentation criterion: every element killed by evaluation is a finite
linear combination of products `ι(r)u` with the relation on the left. -/
theorem mem_kernel_canonical_uea_evaluation_iff_relation_sum
    (u : UEA ℤ (CanonicalFreeLie L)) :
    UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L) u = 0 ↔
      u ∈ rightRelationSpan ℤ (CanonicalFreeLie L)
        (CanonicalLieRelationsIdeal L) := by
  rw [mem_kernel_canonical_uea_evaluation_iff L u]
  exact mem_idealOfLieIdeal_iff_relation_sum ℤ (CanonicalFreeLie L)
    (CanonicalLieRelationsIdeal L) u

end

end DegreeFive

end LieRings
