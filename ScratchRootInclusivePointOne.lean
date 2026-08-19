import LieRings.DimensionSubring.MetabelianVanishing.StepSeven
import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge

/-!
# Corrected Point 1: root-inclusive two-read terminal ledger

This is a separate verification file and is not imported by the library.
It replaces the false Point-1 interface in
`ScratchRootInclusivePoint23.lean`.

The false interface claimed a literal equality between the governing word
and a sum of final words all having PBW factor number at most two.  The
governing word contains the high-augmentation term, so that equality cannot
hold.  The corrected ledger retains one explicit residual occurrence.

The two non-residual external families are exactly the two opposite sides of
the already constructed terminal square:

* `terminalTwoFullLabelWord`, whose terminal factor-two read is the
  contextual factor edge and whose primitive is `terminalTwoPrimitive`;
* `terminalComponentFullLabelWord`, whose terminal factor-two read is the
  terminal defect and whose primitive is `componentTracePrimitive`.

The residual is defined by exact subtraction in the enveloping algebra.  It
is then proved, rather than assumed, to have zero complete factor-one read
and zero terminal factor-two read.  Consequently Point 2 receives exactly
the same two tasks as before: realize the factor family, and realize the
oppositely oriented correction family.  No chain, boundary, source
primitive, relation error, or terminal-coordinate error is assumed here.
-/

namespace LieRings.MetabelianVanishing.CorrectedPointOne

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance correctedPointOneFintype : Fintype L := Fintype.ofFinite L

abbrev Occurrence := UEA ℤ (FreeModel n L)

/-- The whole-label factor side of the terminal square. -/
def pointOneFactorWord {a : L} (w : GoverningWitness n L data a) :
    Occurrence n L :=
  w.terminalTwoFullLabelWord n L data hn

/-- The whole-label component/correction side of the terminal square. -/
def pointOneCorrectionWord {a : L} (w : GoverningWitness n L data a) :
    Occurrence n L :=
  w.terminalComponentFullLabelWord n L data hn

/-- Everything in the exact governing word not belonging to the two low-read
terminal families.  It is retained as a literal occurrence until its two
projection-vanishing theorems have been proved. -/
def pointOneResidualWord {a : L} (w : GoverningWitness n L data a) :
    Occurrence n L :=
  (w.externalMarkedWord n L data hn).word -
    pointOneCorrectionWord n L data hn w -
    pointOneFactorWord n L data hn w

/-- Literal evaluation of a finite occurrence ledger. -/
def occurrenceValue :
    (Occurrence n L →₀ ℤ) →ₗ[ℤ] Occurrence n L :=
  Finsupp.linearCombination ℤ (fun u : Occurrence n L ↦ u)

/-- The positive governing root. -/
def pointOneRootLedger {a : L} (w : GoverningWitness n L data a) :
    Occurrence n L →₀ ℤ :=
  Finsupp.single (w.externalMarkedWord n L data hn).word 1

/-- The complete corrected occurrence frontier.  Point 2 realizes the first
two summands; the last summand is discarded only after one of its certified
zero-read theorems is applied. -/
def pointOneFrontierLedger {a : L} (w : GoverningWitness n L data a) :
    Occurrence n L →₀ ℤ :=
  Finsupp.single (pointOneFactorWord n L data hn w) 1 +
    Finsupp.single (pointOneCorrectionWord n L data hn w) 1 +
    Finsupp.single (pointOneResidualWord n L data hn w) 1

/-- The exact enveloping-algebra equality underlying the corrected ledger.
No PBW projection occurs in this statement. -/
theorem pointOne_externalWord_eq_factor_add_correction_add_residual
    {a : L} (w : GoverningWitness n L data a) :
    (w.externalMarkedWord n L data hn).word =
      pointOneFactorWord n L data hn w +
        pointOneCorrectionWord n L data hn w +
        pointOneResidualWord n L data hn w := by
  rw [pointOneResidualWord]
  module

/-- One literal rewrite cell, oriented as `outputs - input`. -/
structure PointOneCell where
  input : Occurrence n L
  outputs : Occurrence n L →₀ ℤ
  preserves : occurrenceValue n L outputs = input

/-- Its signed occurrence boundary. -/
def PointOneCell.boundary (c : PointOneCell n L) :
    Occurrence n L →₀ ℤ :=
  c.outputs - Finsupp.single c.input 1

/-- The aggregate terminal-square rewrite as a certified cell.  This cell
packages an already proved exact word equality; it does not package either
of the low-read vanishing results below. -/
def pointOneTerminalSquareCell {a : L}
    (w : GoverningWitness n L data a) : PointOneCell n L where
  input := (w.externalMarkedWord n L data hn).word
  outputs := pointOneFrontierLedger n L data hn w
  preserves := by
    simp only [pointOneFrontierLedger, occurrenceValue, map_add,
      Finsupp.linearCombination_single, one_smul]
    exact (pointOne_externalWord_eq_factor_add_correction_add_residual
      n L data hn w).symm

/-- **Corrected Point-1 occurrence identity.**  The governing root is
explicit with coefficient `+1`, and the residual is explicit on the right. -/
theorem pointOne_root_add_cellBoundary_eq_frontier {a : L}
    (w : GoverningWitness n L data a) :
    pointOneRootLedger n L data hn w +
        (pointOneTerminalSquareCell n L data hn w).boundary n L =
      pointOneFrontierLedger n L data hn w := by
  classical
  simp only [pointOneRootLedger, PointOneCell.boundary,
    pointOneTerminalSquareCell]
  module

/-- The complete factor-one read of the correction family. -/
theorem pointOne_pbwPrimitive_correctionWord {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn (pointOneCorrectionWord n L data hn w) =
      w.componentTracePrimitive n L data hn := by
  exact w.pbwPrimitive_terminalComponentFullLabelWord n L data hn

/-- The complete factor-one read of the factor family. -/
theorem pointOne_pbwPrimitive_factorWord {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn (pointOneFactorWord n L data hn w) =
      w.terminalTwoPrimitive n L data hn := by
  exact w.pbwPrimitive_terminalTwoFullLabelWord n L data hn

/-- The governing external word has its recorded external primitive. -/
theorem pointOne_pbwPrimitive_externalWord {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn (w.externalMarkedWord n L data hn).word =
      (w.externalPrimitivePreimage n L data hn : FreeModel n L) := by
  apply canonicalMap_injective_of_freeModulePBW
    ℤ (FreeModel n L) (AdaptedIndex n L data hn)
    (adaptedWeightedBasis n L data hn).basis
    (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis)
  rw [← factorProj_one_eq_iota_pbwPrimitive,
    (w.externalMarkedWord n L data hn).projection_eq]
  rfl

/-- The retained residual is invisible to the complete factor-one read. -/
theorem pointOne_pbwPrimitive_residual_eq_zero {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn (pointOneResidualWord n L data hn w) = 0 := by
  rw [pointOneResidualWord, map_sub, map_sub,
    pointOne_pbwPrimitive_externalWord,
    pointOne_pbwPrimitive_correctionWord,
    pointOne_pbwPrimitive_factorWord,
    w.externalPrimitivePreimage_eq n L data hn]
  module

/-- The terminal factor-two read of the correction family is the complete
component defect. -/
theorem pointOne_rightSymbol_correctionWord {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (pointOneCorrectionWord n L data hn w) =
      w.terminalFactorDefect n L data hn := by
  exact w.rightSymbol_terminalComponentFullLabelWord n L data hn

/-- The terminal factor-two read of the factor family is the opposite of the
same defect. -/
theorem pointOne_rightSymbol_factorWord {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (pointOneFactorWord n L data hn w) =
      -w.terminalFactorDefect n L data hn := by
  rw [pointOneFactorWord,
    w.rightSymbol_terminalTwoFullLabelWord n L data hn,
    w.terminalTwoFullLabel_eq_dOne_contextualTerminalChain n L data hn,
    w.dOne_contextualTerminalChain_eq_neg_defect n L data hn]

/-- The terminal factor-two read of the governing external word is zero. -/
theorem pointOne_rightSymbol_externalWord {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.externalMarkedWord n L data hn).word = 0 := by
  rw [show (w.externalMarkedWord n L data hn).word =
      w.theta - UniversalEnvelopingAlgebra.ι ℤ
        (w.terminalOneRelation n L data hn : FreeModel n L) by
    exact w.terminalPacketWord_externalRows n L data hn]
  rw [map_sub, rightSymbol_theta_terminal_eq_zero n L data hn w,
    rightSymbol, LinearMap.comp_apply,
    fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2 (by omega),
    map_zero, sub_zero]

/-- The retained residual is also invisible to the terminal factor-two
read.  The proof uses the two opposite, independently proved terminal-square
edges; it does not infer the sign from the desired conclusion. -/
theorem pointOne_rightSymbol_residual_eq_zero {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (pointOneResidualWord n L data hn w) = 0 := by
  rw [pointOneResidualWord, map_sub, map_sub,
    pointOne_rightSymbol_externalWord,
    pointOne_rightSymbol_correctionWord,
    pointOne_rightSymbol_factorWord]
  module

/-- Point 2's factor-one interface: after the certified residual is removed,
the same two terminal families carry exactly the external primitive. -/
theorem pointOne_pbwPrimitive_factor_add_correction {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn
        (pointOneFactorWord n L data hn w +
          pointOneCorrectionWord n L data hn w) =
      (w.externalPrimitivePreimage n L data hn : FreeModel n L) := by
  rw [map_add, pointOne_pbwPrimitive_factorWord,
    pointOne_pbwPrimitive_correctionWord,
    w.externalPrimitivePreimage_eq n L data hn]
  module

/-- Point 2's factor-two interface: the same two terminal families have
opposite boundaries. -/
theorem pointOne_rightSymbol_factor_add_correction {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (pointOneFactorWord n L data hn w +
          pointOneCorrectionWord n L data hn w) = 0 := by
  rw [map_add, pointOne_rightSymbol_factorWord,
    pointOne_rightSymbol_correctionWord]
  module

/-- Applying the factor-one read to the complete corrected frontier gives
the external primitive. -/
theorem pointOne_pbwPrimitive_frontier {a : L}
    (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn
        (occurrenceValue n L (pointOneFrontierLedger n L data hn w)) =
      (w.externalPrimitivePreimage n L data hn : FreeModel n L) := by
  simp only [pointOneFrontierLedger, occurrenceValue, map_add,
    Finsupp.linearCombination_single, one_smul, map_add,
    pointOne_pbwPrimitive_factorWord,
    pointOne_pbwPrimitive_correctionWord,
    pointOne_pbwPrimitive_residual_eq_zero, add_zero,
    w.externalPrimitivePreimage_eq]
  module

/-- Applying the factor-two read to the complete corrected frontier gives
zero. -/
theorem pointOne_rightSymbol_frontier {a : L}
    (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (occurrenceValue n L (pointOneFrontierLedger n L data hn w)) = 0 := by
  simp only [pointOneFrontierLedger, occurrenceValue, map_add,
    Finsupp.linearCombination_single, one_smul, map_add,
    pointOne_rightSymbol_factorWord,
    pointOne_rightSymbol_correctionWord,
    pointOne_rightSymbol_residual_eq_zero, add_zero]
  module

assert_no_sorry pointOne_externalWord_eq_factor_add_correction_add_residual
assert_no_sorry pointOne_root_add_cellBoundary_eq_frontier
assert_no_sorry pointOne_pbwPrimitive_residual_eq_zero
assert_no_sorry pointOne_rightSymbol_residual_eq_zero
assert_no_sorry pointOne_pbwPrimitive_factor_add_correction
assert_no_sorry pointOne_rightSymbol_factor_add_correction
assert_no_sorry pointOne_pbwPrimitive_frontier
assert_no_sorry pointOne_rightSymbol_frontier

end

end LieRings.MetabelianVanishing.CorrectedPointOne
