import LieRings.Plotkin.FreeNilpotentGenerators
import LieRings.Plotkin.ReesMap
import LieRings.Plotkin.FiniteGeneration

/-!
# Noetherian augmentation Rees rings of finitely generated nilpotent Lie rings

The weighted PBW calculation for a finite free nilpotent Lie ring gives a finite
almost-commutative word filtration on its augmentation Rees ring.  This file performs the
remaining presentation step: a finite presentation of a nilpotent Lie ring factors through the
corresponding free nilpotent quotient, and Noetherianity descends along the induced surjective
map of Rees rings.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

variable {X : Type u} [Finite X]
variable {K : Type v} [LieRing K]

local notation "FL" => FreeLieAlgebra ℤ X

/-- Evaluation in a Lie ring whose `c`th lower-central term vanishes factors through the free
nilpotent Lie ring of class at most `c`. -/
def freeNilpotentEvaluation (evaluation : FL →ₗ⁅ℤ⁆ K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥) :
    FreeNilpotent X c →ₗ⁅ℤ⁆ K where
  toLinearMap := (lowerCentralSeries ℤ FL c).toSubmodule.liftQ
    evaluation.toLinearMap (by
      intro x hx
      rw [LinearMap.mem_ker]
      have hmem : evaluation x ∈ lowerCentralSeries ℤ K c :=
        (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := evaluation) c)
          (LieIdeal.mem_map hx)
      rw [hclass] at hmem
      simpa using hmem)
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        rw [← LieSubmodule.Quotient.mk_bracket]
        change (lowerCentralSeries ℤ FL c).toSubmodule.liftQ
            evaluation.toLinearMap _ (Submodule.Quotient.mk ⁅x, y⁆) =
          ⁅(lowerCentralSeries ℤ FL c).toSubmodule.liftQ
              evaluation.toLinearMap _ (Submodule.Quotient.mk x),
            (lowerCentralSeries ℤ FL c).toSubmodule.liftQ
              evaluation.toLinearMap _ (Submodule.Quotient.mk y)⁆
        rw [Submodule.liftQ_apply, Submodule.liftQ_apply, Submodule.liftQ_apply]
        exact LieHom.map_lie evaluation x y

@[simp]
theorem freeNilpotentEvaluation_mk (evaluation : FL →ₗ⁅ℤ⁆ K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥) (x : FL) :
    freeNilpotentEvaluation evaluation c hclass (LieSubmodule.Quotient.mk x) =
      evaluation x :=
  rfl

/-- A surjective free evaluation remains surjective after factoring through the nilpotent
quotient. -/
theorem freeNilpotentEvaluation_surjective
    (evaluation : FL →ₗ⁅ℤ⁆ K) (hevaluation : Function.Surjective evaluation)
    (c : ℕ) (hclass : lowerCentralSeries ℤ K c = ⊥) :
    Function.Surjective (freeNilpotentEvaluation evaluation c hclass) := by
  intro y
  obtain ⟨x, rfl⟩ := hevaluation y
  exact ⟨LieSubmodule.Quotient.mk x, rfl⟩

/-- The augmentation Rees ring of a finitely generated nilpotent Lie ring is Noetherian. -/
theorem isNoetherianRing_augmentationRees_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥) :
    IsNoetherianRing (ReesRing (UEA.augmentationIdeal ℤ K)) := by
  obtain ⟨r, generators, hevaluation⟩ :=
    (isFinitelyGenerated_iff_hasFiniteFreePresentation K).mp hK
  let evaluation : FreeLieAlgebra ℤ (Fin r) →ₗ⁅ℤ⁆ K :=
    FreeLieAlgebra.lift ℤ generators
  let f : FreeNilpotent (Fin r) c →ₗ⁅ℤ⁆ K :=
    freeNilpotentEvaluation evaluation c hclass
  letI : IsNoetherianRing
      (ReesRing (UEA.augmentationIdeal ℤ (FreeNilpotent (Fin r) c))) :=
    isNoetherianRing_freeNilpotentRees (Fin r) c
  exact isNoetherianRing_augmentationRees_of_surjective f
    (freeNilpotentEvaluation_surjective evaluation hevaluation c hclass)

end

end LieRings.Plotkin
