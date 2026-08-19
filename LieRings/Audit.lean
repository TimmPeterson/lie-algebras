import LieRings.DimensionSubring.MetabelianVanishing.Main
import Mathlib.Util.AssertNoSorry

#print axioms LieRings.DegreeFour.dimensionSubring_five_le_lowerCentralSeries_three
#check LieRings.DegreeFour.dimensionSubring_five_le_lowerCentralSeries_three

assert_no_sorry LieRings.DegreeFour.dimensionSubring_five_le_lowerCentralSeries_three

/-! The two already-known odd degrees use only the established degree-three
and degree-five results.  Keeping this check on the dedicated low-degree
theorem makes that dependency visible even though the final reduced theorem
also has a general `n ≥ 3` branch. -/

#check LieRings.MetabelianVanishing.reducedTopLayerVanishes_of_le_two
#print axioms LieRings.MetabelianVanishing.reducedTopLayerVanishes_of_le_two

assert_no_sorry LieRings.MetabelianVanishing.reducedTopLayerVanishes_of_le_two

/-! These conditional assertions audit the Step-8 glue independently of the
Step-7 capstone.  The corresponding unconditional assertions are added below
when the capstone is imported. -/

#check LieRings.MetabelianVanishing.reducedTopLayerVanishes_of_stepSeven
#check LieRings.finite_metabelian_odd_dimensionSubring_eq_bot_of_stepSeven
#check LieRings.MetabelianVanishing.GoverningWitness.eq_zero_of_completeFactorTwoCorrection

#print axioms LieRings.MetabelianVanishing.reducedTopLayerVanishes_of_stepSeven
#print axioms LieRings.finite_metabelian_odd_dimensionSubring_eq_bot_of_stepSeven
#print axioms LieRings.MetabelianVanishing.GoverningWitness.eq_zero_of_completeFactorTwoCorrection

assert_no_sorry LieRings.MetabelianVanishing.reducedTopLayerVanishes_of_stepSeven
assert_no_sorry LieRings.finite_metabelian_odd_dimensionSubring_eq_bot_of_stepSeven
assert_no_sorry LieRings.MetabelianVanishing.GoverningWitness.eq_zero_of_completeFactorTwoCorrection
