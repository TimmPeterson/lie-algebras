import LieRings.DimensionSubring.Centrality
import LieRings.DimensionSubring.Functoriality

/-!
# The class-three quotient
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- The universal quotient of `L` having nilpotency class at most three. -/
abbrev ClassThreeQuotient := L ⧸ lowerCentralSeries ℤ L 3

/-- The quotient by `γ₄(L)` has fourth lower-central term zero. -/
theorem classThreeQuotient_lowerCentralSeries_three_eq_bot :
    lowerCentralSeries ℤ (ClassThreeQuotient L) 3 = ⊥ := by
  let q : L →ₗ⁅ℤ⁆ ClassThreeQuotient L :=
    UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L 3)
  have hq : Function.Surjective q := by
    intro y
    exact Submodule.Quotient.mk_surjective
      (lowerCentralSeries ℤ L 3).toSubmodule y
  change LieModule.lowerCentralSeries ℤ (ClassThreeQuotient L)
      (ClassThreeQuotient L) 3 = ⊥
  rw [← LieIdeal.lowerCentralSeries_map_eq 3 hq]
  rw [LieIdeal.map_eq_bot_iff]
  intro x hx
  change (LieSubmodule.Quotient.mk x : ClassThreeQuotient L) = 0
  exact (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L 3)).mpr hx

end


end DegreeFive

end LieRings
