import LieRings.DimensionSubring.MetabelianVanishing.Reduced
import LieRings.DimensionSubring.MetabelianVanishing.Statement

/-!
# Final assembly for odd metabelian dimension-subring vanishing

This file contains only the reduction-level composition.  The temporary
`_of_stepSeven` theorem makes the final dependency boundary explicit while the
Point-7 capstone is compiled in its own file; the public theorem below it is
obtained by supplying that ordinary theorem, never by adding an axiom.
-/

namespace LieRings

universe u

/-- The frozen final statement, parameterized solely by the one capstone that
Point 7 must export.  Once that theorem is imported, the public unparameterized
version is the specialization of this theorem to it. -/
theorem finite_metabelian_odd_dimensionSubring_eq_bot_of_stepSeven
    (hStepSeven :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (_hn3 : 3 ≤ n)
        {a : L},
        MetabelianVanishing.GoverningWitness n L data a → a = 0)
    (hReduction : ReductionProperty.{u})
    (hPS : PassiSickingProperty.{u})
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (hn : 1 ≤ n)
    (hmeta : IsMetabelian L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥) :
    dimensionSubring ℤ L (2 * n + 1) = ⊥ := by
  exact reduction_conclusion hReduction hPS
    (MetabelianVanishing.reducedTopLayerVanishes_of_stepSeven hStepSeven)
    n L hn hmeta hclass

end LieRings
