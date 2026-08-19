import LieRings.DimensionSubring.MetabelianVanishing.RawContextualTerminalAggregate
import LieRings.DimensionSubring.MetabelianVanishing.CompleteCutoffCycle

/-!
# The total full-label correction for the raw cutoff

The complete factor-first chain cancels the factor-two symbol of the raw
cutoff input.  The contextual terminal chain accounts for the retained
factor-two wall of the full-label continuation.  Their two negatives
therefore have boundary equal to the remaining terminal component read.

This is an aggregate statement.  It does not identify an individual
homogeneous component with its stored full relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffTotalCorrectionFintype : Fintype L :=
  Fintype.ofFinite L

/-- The signed total chain left after canceling the raw cutoff input and its
placed contextual factor-two wall. -/
def GoverningWitness.rawCutoffTotalFullLabelCorrection
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  -w.completeFactorTwoChain n L data hn -
    w.rawCutoffContextualTerminalChain n L data hn

/-- Its boundary is the aggregate terminal component read of the raw
full-label continuation. -/
@[simp] theorem GoverningWitness.dOne_rawCutoffTotalFullLabelCorrection
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffTotalFullLabelCorrection n L data hn) =
      w.rawCutoffTerminalComponentFactor n L data hn := by
  rw [GoverningWitness.rawCutoffTotalFullLabelCorrection, map_sub, map_neg,
    w.dOne_completeFactorTwoChain_eq_neg_rawCutoffSymbol n L data hn,
    ← w.rawCutoffTerminalTwoFullLabel_eq_dOne n L data hn,
    w.rightSymbol_rawCutoff_terminal_decomposition n L data hn]
  change - -((w.rawCutoffTerminalComponentFactor n L data hn +
      w.rawCutoffTerminalTwoFullLabel n L data hn) :
        Sym[ℤ] (Fin 2) (A L n)) -
      w.rawCutoffTerminalTwoFullLabel n L data hn =
    w.rawCutoffTerminalComponentFactor n L data hn
  rw [neg_neg]
  exact add_sub_cancel_right
    (w.rawCutoffTerminalComponentFactor n L data hn)
    (w.rawCutoffTerminalTwoFullLabel n L data hn)

/-- Equivalent full-label form of the same aggregate boundary. -/
theorem GoverningWitness.dOne_rawCutoffTotalFullLabelCorrection_eq_fullLabel
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffTotalFullLabelCorrection n L data hn) =
      w.rawCutoffTerminalComponentFullLabel n L data hn := by
  rw [w.dOne_rawCutoffTotalFullLabelCorrection n L data hn,
    w.rawCutoffTerminalComponentFactor_eq_fullLabel n L data hn]

/-! ## The exact splice consumed by the corrected-cycle theorem -/

/-- The genuine full-relation placement errors made by the contextual raw
factor-two wall. -/
def GoverningWitness.rawCutoffContextualTerminalPlacementRelation
    {a : L} (w : GoverningWitness n L data a) : Relations n L data :=
  (w.rawCutoffProvenancedTerminalTwo n L data hn).sum (fun c z ↦
    z • c.sourcePlacementRelation n L data hn)

/-- Primitive read of the contextual raw factor-two wall, including exactly
its genuine full-relation placement error. -/
theorem GoverningWitness.terminalSourcePrimitive_rawCutoffContextualTerminalChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffContextualTerminalChain n L data hn) =
      w.rawFullCutoffTerminalTwoPrimitive n L data hn +
        (w.rawCutoffContextualTerminalPlacementRelation n L data hn :
          FreeModel n L) := by
  classical
  rw [GoverningWitness.rawCutoffContextualTerminalChain,
    GoverningWitness.rawFullCutoffTerminalTwoPrimitive,
    GoverningWitness.rawCutoffContextualTerminalPlacementRelation,
    map_finsuppSum]
  simp_rw [map_zsmul]
  have hcoe :
      ((w.rawCutoffProvenancedTerminalTwo n L data hn).sum (fun c z ↦
          z • c.sourcePlacementRelation n L data hn) : Relations n L data) =
        w.rawCutoffContextualTerminalPlacementRelation n L data hn := rfl
  change (w.rawCutoffProvenancedTerminalTwo n L data hn).sum (fun c z ↦
      z • terminalSourcePrimitive n L data hn (c.chain n L data hn)) =
    (w.rawCutoffProvenancedTerminalTwo n L data hn).sum (fun c z ↦
        z • c.primitive n L data hn) +
      (Relations n L data).subtype
        (w.rawCutoffContextualTerminalPlacementRelation n L data hn)
  rw [← hcoe, map_finsuppSum, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  rw [c.terminalSourcePrimitive_chain n L data hn, smul_add]
  rfl

/-- Splice a realization of the aggregate mark-one full-label ledger between
the contextual and the original terminal factor-two walls. -/
def GoverningWitness.rawCutoffSplicedCorrection
    {a : L} (w : GoverningWitness n L data a)
    (markOneChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  markOneChain + w.rawCutoffContextualTerminalChain n L data hn -
    w.rawCutoffTerminalTwoChain n L data hn

/-- Once the mark-one chain realizes the signed full-label ledger, the splice
has exactly the ordinary raw-cutoff boundary.  This follows by comparing the
two complete terminal decompositions of the same raw word. -/
theorem GoverningWitness.dOne_rawCutoffSplicedCorrection
    {a : L} (w : GoverningWitness n L data a)
    (markOneChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hmarkOne : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 markOneChain =
      w.rawCutoffTraceMarkOneFullLabel n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffSplicedCorrection n L data hn markOneChain) =
      w.rawCutoffOrdinaryFactorTwo n L data hn := by
  rw [GoverningWitness.rawCutoffSplicedCorrection, map_sub, map_add,
    hmarkOne,
    ← w.rawCutoffTerminalComponentFullLabel_eq_trace n L data hn,
    ← w.rawCutoffTerminalComponentFactor_eq_fullLabel n L data hn,
    ← w.rawCutoffTerminalTwoFullLabel_eq_dOne n L data hn,
    w.dOne_rawCutoffTerminalTwoChain_eq_symbol_sub_ordinary n L data hn,
    w.rightSymbol_rawCutoff_terminal_decomposition n L data hn]
  exact sub_sub_cancel
    (w.rawCutoffTerminalComponentFactor n L data hn +
      w.rawCutoffTerminalTwoFullLabel n L data hn)
    (w.rawCutoffOrdinaryFactorTwo n L data hn)

/-- Exact primitive of the same splice.  The only discrepancy from the three
literal primitive ledgers is a displayed difference of genuine full
relations. -/
theorem GoverningWitness.terminalSourcePrimitive_rawCutoffSplicedCorrection
    {a : L} (w : GoverningWitness n L data a)
    (markOneChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffSplicedCorrection n L data hn markOneChain) =
      terminalSourcePrimitive n L data hn markOneChain +
          w.rawFullCutoffTerminalTwoPrimitive n L data hn -
          w.rawCutoffTerminalTwoPrimitive n L data hn +
        ((w.rawCutoffContextualTerminalPlacementRelation n L data hn -
            w.rawCutoffTerminalTwoPlacementRelation n L data hn :
          Relations n L data) : FreeModel n L) := by
  rw [GoverningWitness.rawCutoffSplicedCorrection, map_sub, map_add,
    w.terminalSourcePrimitive_rawCutoffContextualTerminalChain n L data hn,
    w.terminalSourcePrimitive_rawCutoffTerminalTwoChain n L data hn]
  change terminalSourcePrimitive n L data hn markOneChain +
        (w.rawFullCutoffTerminalTwoPrimitive n L data hn +
          (w.rawCutoffContextualTerminalPlacementRelation n L data hn :
            FreeModel n L)) -
        (w.rawCutoffTerminalTwoPrimitive n L data hn +
          (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
            FreeModel n L)) =
      terminalSourcePrimitive n L data hn markOneChain +
          w.rawFullCutoffTerminalTwoPrimitive n L data hn -
          w.rawCutoffTerminalTwoPrimitive n L data hn +
        ((w.rawCutoffContextualTerminalPlacementRelation n L data hn :
            FreeModel n L) -
          (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
            FreeModel n L))
  module

/-- Evaluation-level endpoint of the raw cutoff splice.  Thus the remaining
mark-one construction has exactly two obligations: its displayed full-label
boundary and the manuscript's displayed primitive identity after evaluation.
All placement discrepancies have already been packaged as genuine full
relations. -/
theorem GoverningWitness.eq_zero_of_rawCutoffMarkOneChain
    {a : L} (w : GoverningWitness n L data a)
    (markOneChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hmarkOne : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 markOneChain =
      w.rawCutoffTraceMarkOneFullLabel n L data hn)
    (heval : evaluation n L data
        (terminalSourcePrimitive n L data hn markOneChain +
            w.rawFullCutoffTerminalTwoPrimitive n L data hn -
            w.rawCutoffTerminalTwoPrimitive n L data hn -
          w.rawCutoffOrdinaryPrimitive n L data hn) = 0) :
    a = 0 := by
  apply w.eq_zero_of_completeCutoffCorrection_eval n L data hn
    (w.rawCutoffSplicedCorrection n L data hn markOneChain)
  · exact w.dOne_rawCutoffSplicedCorrection n L data hn
      markOneChain hmarkOne
  · rw [w.terminalSourcePrimitive_rawCutoffSplicedCorrection
      n L data hn markOneChain]
    have hrel : evaluation n L data
        (((w.rawCutoffContextualTerminalPlacementRelation n L data hn -
            w.rawCutoffTerminalTwoPlacementRelation n L data hn :
          Relations n L data) : FreeModel n L)) = 0 :=
      (w.rawCutoffContextualTerminalPlacementRelation n L data hn -
        w.rawCutoffTerminalTwoPlacementRelation n L data hn).property
    simp only [map_sub, map_add, hrel, add_zero]
    simpa only [map_sub, map_add] using heval

end

end LieRings.MetabelianVanishing
