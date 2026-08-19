import LieRings.Metabelian.FreeEvaluation
import Mathlib.Util.AssertNoSorry

/-!
# Compile gates for the relatively free metabelian Lie ring

These examples expose the capstone interfaces required by Point 3: integral
Hall normal form, metabelianity and the class cutoff, canonical surjective
evaluation, exact homogeneous ranges, and uniqueness of evaluation.
-/

namespace FreeMetabelian.Tests

noncomputable section

universe u v

variable {ι : Type u} [Fintype ι] [LinearOrder ι]
variable {X : Type v} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (b : Module.Basis ι ℤ X)

example (q : ℕ) :
    HallIndex.Module (ι := ι) q ≃ₗ[ℤ] Component X q :=
  hallEquiv b q

example (c : ℕ) : LieRings.IsMetabelian (Free X c) :=
  Free.isMetabelian

example (c : ℕ) :
    LieModule.lowerCentralSeries ℤ (Free X c) (Free X c) c = ⊥ :=
  Free.lowerCentralSeries_cutoff_eq_bot

variable {L : Type v} [LieRing L] [Finite L]

example {c : ℕ} (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥) (hc : 0 < c) :
    Function.Surjective (Evaluation.canonicalEvaluation hmeta hclass) :=
  Evaluation.canonicalEvaluation_surjective hmeta hclass hc

example (hmeta : LieRings.IsMetabelian L) (n : ℕ) :
    LinearMap.range
        (Evaluation.pieceEval hmeta (Evaluation.canonicalGeneratorMap L) n) =
      (LieModule.lowerCentralSeries ℤ L L n).toSubmodule :=
  Evaluation.canonicalPiece_range_eq_lowerCentralSeries hmeta n

end

end FreeMetabelian.Tests

assert_no_sorry FreeMetabelian.hallEquiv
assert_no_sorry FreeMetabelian.Free.isMetabelian
assert_no_sorry FreeMetabelian.Evaluation.canonicalPiece_range_eq_lowerCentralSeries
assert_no_sorry FreeMetabelian.Evaluation.lieHom_unique
