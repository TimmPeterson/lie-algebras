import LieRings.DimensionSubring.MetabelianVanishing.ExternalInputs

/-!
# Frozen statement for odd metabelian dimension-subring vanishing

Point 1 freezes the final signature and verifies its two low-degree index
specializations.  The theorem with this signature is proved only after the
internal `ReducedTopLayerVanishes` theorem has been constructed; no placeholder
constant is introduced here.
-/

namespace LieRings

universe u

/-- Once the reduced theorem is available, the reduction produces exactly the
intended conclusion, with no whole-ring 2-group or cyclicity hypothesis. -/
theorem reduction_conclusion
    (hReduction : ReductionProperty.{u})
    (hPS : PassiSickingProperty.{u})
    (hReduced : ReducedTopLayerVanishes.{u})
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (hn : 1 ≤ n)
    (hmeta : IsMetabelian L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥) :
    dimensionSubring ℤ L (2 * n + 1) = ⊥ :=
  hReduction hPS hReduced n L hn hmeta hclass

/-- The `n = 1` index is the third dimension-subring theorem. -/
private theorem degreeThree_target (L : Type u) [LieRing L]
    (hclass : lowerCentralSeries ℤ L 2 = ⊥) :
    dimensionSubring ℤ L (2 * 1 + 1) = ⊥ := by
  norm_num
  rw [dimensionSubring_three_eq_lowerCentralSeries_two L, hclass]

/-- The `n = 2` index is the existing fifth dimension-subring inclusion. -/
private theorem degreeFive_target (L : Type u) [LieRing L]
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    dimensionSubring ℤ L (2 * 2 + 1) = ⊥ := by
  norm_num
  apply le_antisymm
  · rw [← hclass]
    exact DegreeFour.dimensionSubring_five_le_lowerCentralSeries_three L
  · exact bot_le

end LieRings
