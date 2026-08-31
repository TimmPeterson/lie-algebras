import LieRings.Plotkin.NilpotentTarget
import LieRings.Plotkin.Stabilization
import LieRings.Plotkin.CentralSeparation
import Mathlib.Util.AssertNoSorry

/-!
# Eventual vanishing for finitely generated nilpotent Lie rings

This file joins the three final nilpotent ingredients of the Plotkin argument: finite dimension
tail, zero omega intersection by central-prime separation, and stabilization inside a finite
additive group.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

variable {K : Type u} [LieRing K]

/-- Conditional form of eventual vanishing, exposing central-prime separation as a hypothesis. -/
theorem dimensionSubring_eventually_eq_bot_of_finitelyGenerated_of_lowerCentralSeries_eq_bot_of_separation
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥)
    (hsep : HasCentralPrimeSeparation K) :
    ∃ s : ℕ, dimensionSubring ℤ K s = ⊥ := by
  have homega : dimensionSubringOmega ℤ K = ⊥ :=
    dimensionSubringOmega_eq_bot_of_centralPrimeSeparation hK c hclass hsep
  letI : Finite (dimensionSubring ℤ K (c + 1)) :=
    finite_dimensionSubring_succ_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
      hK c hclass
  exact dimensionSubring_eventually_eq_bot_of_finite_of_omega_eq_bot
    K (c + 1) homega

/-- A finitely generated Lie ring whose zero-based `c`th lower-central term
vanishes has an eventually zero dimension filtration. -/
theorem dimensionSubring_eventually_eq_bot_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥) :
    ∃ s : ℕ, dimensionSubring ℤ K s = ⊥ := by
  exact
    dimensionSubring_eventually_eq_bot_of_finitelyGenerated_of_lowerCentralSeries_eq_bot_of_separation
      hK c hclass
      (hasCentralPrimeSeparation_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
        hK c hclass)

end

end LieRings.Plotkin

assert_no_sorry
  LieRings.Plotkin.dimensionSubring_eventually_eq_bot_of_finitelyGenerated_of_lowerCentralSeries_eq_bot_of_separation
assert_no_sorry
  LieRings.Plotkin.dimensionSubring_eventually_eq_bot_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
