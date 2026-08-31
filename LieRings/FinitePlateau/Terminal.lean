import LieRings.FinitePlateau.Presentation
import LieRings.DimensionSubring.MetabelianTwoFactor
import Mathlib.Util.AssertNoSorry

/-!
# The terminal dimension term of the finite-plateau example

The manuscript proves the terminal vanishing by one last PBW initial-form
calculation.  The general metabelian odd-dimensional theorem, already
available in the library, gives the same conclusion directly and avoids
duplicating that calculation.
-/

namespace LieRings.FinitePlateau

noncomputable section

/-- The dimension series of the manuscript's example vanishes immediately
after the claimed plateau: `δ_(2N+5)(L_N) = 0`. -/
theorem terminal_dimensionSubring_eq_bot (N : ℕ) :
    dimensionSubring ℤ (L N) (2 * N + 5) = ⊥ := by
  have h := MetabelianTwoFactor.nilpotent_dimensionSubring_eq_bot
    (N + 3) (L N) (by omega) (isMetabelian N)
      (lowerCentralSeries_cutoff_eq_bot N)
  simpa only [show 2 * (N + 3) - 1 = 2 * N + 5 by omega] using h

end

end LieRings.FinitePlateau

assert_no_sorry LieRings.FinitePlateau.terminal_dimensionSubring_eq_bot
