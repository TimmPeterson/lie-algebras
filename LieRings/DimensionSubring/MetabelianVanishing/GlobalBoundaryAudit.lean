import LieRings.DimensionSubring.MetabelianVanishing.MarkedCollector

/-!
# Audit of the frozen boundary for the corrected global closed-square proof

This module deliberately imports nothing downstream of `MarkedCollector`.
It records the exact pre-existing interfaces from which the global
occurrence/cell implementation starts.
-/

namespace LieRings.MetabelianVanishing

#check Phi
#check T
#check transgression
#check quadraticBlockValue_capstone

#check rowTruncation_succ
#check ordinaryTransfer
#check markedTransfer
#check markedTruncation

#check LedgerStep
#check runLedger_eq
#check runLedger_evaluation
#check rowMeasureLt_wellFounded
#check deterministicCollector

#check MarkedRow
#check ProvenancedRow
#check provenancedExpansion
#check provenancedExpansion_decreases
#check provenancedExpansion_preserves
#check provenancedCollector
#check ProvenancedCell

assert_no_sorry transgression
assert_no_sorry quadraticBlockValue_capstone
assert_no_sorry rowTruncation_succ
assert_no_sorry markedTransfer
assert_no_sorry markedTruncation
assert_no_sorry runLedger_eq
assert_no_sorry provenancedExpansion_preserves

end LieRings.MetabelianVanishing
