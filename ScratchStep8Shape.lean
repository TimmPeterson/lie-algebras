import LieRings.DimensionSubring.MetabelianVanishing.Reduced
import LieRings.DimensionSubring.MetabelianVanishing.Statement

namespace LieRings.MetabelianVanishing

universe u

example
    (hzero :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) {a : L},
        GoverningWitness n L data a → 3 ≤ n → a = 0) :
    ReducedTopLayerVanishes.{u} := by
  apply reducedTopLayerVanishes_of_stepSeven
  intro n L _ _ data hn3 a w
  exact hzero n L data w hn3

end LieRings.MetabelianVanishing

namespace LieRings

universe u

example
    (hzero :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) {a : L},
        MetabelianVanishing.GoverningWitness n L data a → 3 ≤ n → a = 0)
    (hReduction : ReductionProperty.{u})
    (hPS : PassiSickingProperty.{u})
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (hn : 1 ≤ n)
    (hmeta : IsMetabelian L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥) :
    dimensionSubring ℤ L (2 * n + 1) = ⊥ := by
  exact reduction_conclusion hReduction hPS
    (MetabelianVanishing.reducedTopLayerVanishes_of_stepSeven (by
      intro n L _ _ data hn3 a w
      exact hzero n L data w hn3))
    n L hn hmeta hclass

end LieRings
