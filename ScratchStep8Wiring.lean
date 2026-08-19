import LieRings.DimensionSubring.MetabelianVanishing.Reduced
import LieRings.DimensionSubring.MetabelianVanishing.Statement
import Mathlib.Util.AssertNoSorry

/-!
Scratch verification of the exact unconditional Step-8 wiring.  The sole
parameter below has the signature expected from the Point-7 capstone; in the
production file it is replaced by
`MetabelianVanishing.GoverningWitness.eq_zero`.
-/

namespace LieRings.MetabelianVanishing

universe u

theorem test_reducedTopLayerVanishes
    (hStepSeven :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (_hn2 : 2 ≤ n) {a : L},
        GoverningWitness n L data a → a = 0) :
    ReducedTopLayerVanishes.{u} := by
  intro n L _ hn data a haDim haTop
  by_cases hnSmall : n ≤ 2
  · exact reducedTopLayerVanishes_of_le_two
      n L hn hnSmall data a haDim haTop
  · letI : Finite L := data.finite_inst
    have hn2 : 2 ≤ n := by omega
    obtain ⟨w⟩ := exists_governingWitness n L data a haDim haTop
    exact hStepSeven n L data hn2 w

/-! The two low-degree specializations elaborate without invoking Point 7. -/

example
    (hStepSeven :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (_hn2 : 2 ≤ n) {a : L},
        GoverningWitness n L data a → a = 0)
    (L : Type u) [LieRing L] (data : CyclicTopData 1 L) (a : L)
    (haDim : a ∈ dimensionSubring ℤ L (2 * 1 + 1))
    (haTop : a ∈ lowerCentralSeries ℤ L 1) :
    a = 0 :=
  test_reducedTopLayerVanishes hStepSeven 1 L (by omega)
    data a haDim haTop

example
    (hStepSeven :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (_hn2 : 2 ≤ n) {a : L},
        GoverningWitness n L data a → a = 0)
    (L : Type u) [LieRing L] (data : CyclicTopData 2 L) (a : L)
    (haDim : a ∈ dimensionSubring ℤ L (2 * 2 + 1))
    (haTop : a ∈ lowerCentralSeries ℤ L 2) :
    a = 0 :=
  test_reducedTopLayerVanishes hStepSeven 2 L (by omega)
    data a haDim haTop

end LieRings.MetabelianVanishing

namespace LieRings

universe u

theorem test_finite_metabelian_odd_dimensionSubring_eq_bot
    (hStepSeven :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (_hn2 : 2 ≤ n) {a : L},
        MetabelianVanishing.GoverningWitness n L data a → a = 0)
    (hReduction : ReductionProperty.{u})
    (hPS : PassiSickingProperty.{u})
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (hn : 1 ≤ n)
    (hmeta : IsMetabelian L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥) :
    dimensionSubring ℤ L (2 * n + 1) = ⊥ := by
  exact reduction_conclusion hReduction hPS
    (MetabelianVanishing.test_reducedTopLayerVanishes hStepSeven)
    n L hn hmeta hclass

assert_no_sorry MetabelianVanishing.test_reducedTopLayerVanishes
assert_no_sorry test_finite_metabelian_odd_dimensionSubring_eq_bot

end LieRings
