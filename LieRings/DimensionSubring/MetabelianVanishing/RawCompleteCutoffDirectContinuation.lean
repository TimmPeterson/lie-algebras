import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSubsetChain
import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge

/-!
# Direct completion of the raw cutoff continuation

This file performs the final additive assembly without using the canonical
exceptional boundary remainder.  Its only geometric input is an independently
constructed chain for the relation-on-the-left edge exposed by proper-subset
collection.  Both required identities for that chain are exact: its boundary
is the exposed factor-two edge, and its source primitive is the literal PBW
primitive of that edge modulo an element of `Relations`.

The resulting cutoff chain has boundary equal to the complete raw cutoff
symbol and source primitive equal to the PBW primitive of the complete raw
cutoff word modulo one explicitly grouped genuine relation.  Thus it is
accepted directly by `eq_zero_of_rawCompleteCutoffChain`.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCompleteCutoffDirectContinuationFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## Completing the exceptional component -/

/-- Add an independently constructed relation-on-the-left chain to the
proper-subset tail chain. -/
def GoverningWitness.rawCutoffExceptionalDirectChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.rawCutoffExceptionalSubsetTailChain n L data hn + leftChain

/-- The genuine relation error of the completed exceptional component. -/
def GoverningWitness.rawCutoffExceptionalDirectRelation
    {a : L} (w : GoverningWitness n L data a)
    (leftRelation : Relations n L data) : Relations n L data :=
  w.rawCutoffExceptionalSubsetTailPrimitiveError n L data hn + leftRelation

theorem GoverningWitness.dOne_rawCutoffExceptionalDirectChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hleftBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 leftChain =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffExceptionalDirectChain n L data hn leftChain) =
      w.rawCutoffHoleExceptionalFullLabelFactor n L data hn := by
  rw [GoverningWitness.rawCutoffExceptionalDirectChain, map_add,
    w.dOne_rawCutoffExceptionalSubsetTailChain n L data hn,
    hleftBoundary,
    w.rawCutoffHoleExceptionalFullLabelFactor_eq_component n L data hn]
  abel

theorem GoverningWitness.terminalSourcePrimitive_rawCutoffExceptionalDirectChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (leftRelation : Relations n L data)
    (hleftPrimitive : terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        (leftRelation : FreeModel n L)) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffExceptionalDirectChain n L data hn leftChain) =
      w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn +
        (w.rawCutoffExceptionalDirectRelation n L data hn leftRelation :
          FreeModel n L) := by
  rw [GoverningWitness.rawCutoffExceptionalDirectChain, map_add,
    w.terminalSourcePrimitive_rawCutoffExceptionalSubsetTailChain
      n L data hn,
    hleftPrimitive,
    w.rawCutoffHoleExceptionalFullLabelPrimitive_eq_component n L data hn,
    GoverningWitness.rawCutoffExceptionalDirectRelation]
  change _ - _ + _ + (_ + (leftRelation : FreeModel n L)) = _ +
    ((w.rawCutoffExceptionalSubsetTailPrimitiveError n L data hn :
      FreeModel n L) + (leftRelation : FreeModel n L))
  abel

/-! ## Exact continuation of the complete raw cutoff word -/

/-- The complete mark-one chain obtained from an independent realization of
the exceptional relation-on-the-left edge. -/
def GoverningWitness.rawCutoffDirectMarkOneChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.rawCutoffMarkOneCorrectionChain n L data hn
    (w.rawCutoffExceptionalDirectChain n L data hn leftChain)

/-- The actual cutoff continuation used to close the complete factor-two
chain.  The retained raw terminal factor-two chain is added back to the
ordinary splice, so its boundary is the full raw cutoff symbol. -/
def GoverningWitness.rawCompleteCutoffDirectChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.rawCutoffTerminalTwoChain n L data hn +
    w.rawCutoffSplicedCorrection n L data hn
      (w.rawCutoffDirectMarkOneChain n L data hn leftChain)

/-- All placement errors of the direct continuation, grouped before coercion
to the free model. -/
def GoverningWitness.rawCompleteCutoffDirectRelation
    {a : L} (w : GoverningWitness n L data a)
    (leftRelation : Relations n L data) : Relations n L data :=
  w.rawCutoffMarkOnePlacementRelation n L data hn
      (w.rawCutoffExceptionalDirectRelation n L data hn leftRelation) +
    w.rawCutoffContextualTerminalPlacementRelation n L data hn -
    w.rawFullCutoffTerminalOneRelation n L data hn

theorem GoverningWitness.dOne_rawCompleteCutoffDirectChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hleftBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 leftChain =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCompleteCutoffDirectChain n L data hn leftChain) =
      rightSymbol n L data hn 2 n (by omega)
        (w.rawCompleteCutoffWord n L data) := by
  have hexceptional := w.dOne_rawCutoffExceptionalDirectChain
    n L data hn leftChain hleftBoundary
  have hmarkOne := w.dOne_rawCutoffMarkOneCorrectionChain
    n L data hn
    (w.rawCutoffExceptionalDirectChain n L data hn leftChain)
    hexceptional
  rw [GoverningWitness.rawCompleteCutoffDirectChain, map_add,
    w.dOne_rawCutoffTerminalTwoChain_eq_symbol_sub_ordinary n L data hn,
    w.dOne_rawCutoffSplicedCorrection n L data hn
      (w.rawCutoffDirectMarkOneChain n L data hn leftChain)]
  · abel
  · exact hmarkOne

theorem GoverningWitness.terminalSourcePrimitive_rawCompleteCutoffDirectChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (leftRelation : Relations n L data)
    (hleftPrimitive : terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        (leftRelation : FreeModel n L)) :
    terminalSourcePrimitive n L data hn
        (w.rawCompleteCutoffDirectChain n L data hn leftChain) =
      pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) +
        (w.rawCompleteCutoffDirectRelation n L data hn leftRelation :
          FreeModel n L) := by
  have hexceptional :=
    w.terminalSourcePrimitive_rawCutoffExceptionalDirectChain
      n L data hn leftChain leftRelation hleftPrimitive
  have hmarkOne :=
    w.terminalSourcePrimitive_rawCutoffMarkOneCorrectionChain
      n L data hn
      (w.rawCutoffExceptionalDirectChain n L data hn leftChain)
      (w.rawCutoffExceptionalDirectRelation n L data hn leftRelation)
      hexceptional
  rw [GoverningWitness.rawCompleteCutoffDirectChain, map_add,
    w.terminalSourcePrimitive_rawCutoffTerminalTwoChain n L data hn,
    w.terminalSourcePrimitive_rawCutoffSplicedCorrection n L data hn
      (w.rawCutoffDirectMarkOneChain n L data hn leftChain),
    GoverningWitness.rawCutoffDirectMarkOneChain,
    hmarkOne,
    w.rawCutoffTraceMarkOneFullLabelPrimitive_eq_trace n L data hn,
    w.pbwPrimitive_rawCompleteCutoff_external n L data hn,
    GoverningWitness.rawCompleteCutoffDirectRelation]
  have hcoe :
      (((w.rawCutoffMarkOnePlacementRelation n L data hn
              (w.rawCutoffExceptionalDirectRelation n L data hn leftRelation) +
            w.rawCutoffContextualTerminalPlacementRelation n L data hn -
            w.rawFullCutoffTerminalOneRelation n L data hn :
          Relations n L data) : FreeModel n L)) =
        (w.rawCutoffMarkOnePlacementRelation n L data hn
            (w.rawCutoffExceptionalDirectRelation n L data hn leftRelation) :
          FreeModel n L) +
          (w.rawCutoffContextualTerminalPlacementRelation n L data hn :
            FreeModel n L) -
          (w.rawFullCutoffTerminalOneRelation n L data hn :
            FreeModel n L) := by
    rfl
  rw [hcoe, w.rawFullCutoffTerminalOneRelation_coe n L data hn]
  change
    (w.rawCutoffTerminalTwoPrimitive n L data hn +
        (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
          FreeModel n L)) +
      ((w.rawCutoffTracePrimitive n L data hn +
          (w.rawCutoffMarkOnePlacementRelation n L data hn
            (w.rawCutoffExceptionalDirectRelation n L data hn leftRelation) :
              FreeModel n L)) +
        w.rawFullCutoffTerminalTwoPrimitive n L data hn -
        w.rawCutoffTerminalTwoPrimitive n L data hn +
        ((w.rawCutoffContextualTerminalPlacementRelation n L data hn :
            FreeModel n L) -
          (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
            FreeModel n L))) =
      (w.rawCutoffTracePrimitive n L data hn +
        w.rawCutoffTerminalOnePrimitive n L data hn +
        w.rawFullCutoffTerminalTwoPrimitive n L data hn) +
      (((w.rawCutoffMarkOnePlacementRelation n L data hn
              (w.rawCutoffExceptionalDirectRelation n L data hn leftRelation) :
            FreeModel n L) +
          (w.rawCutoffContextualTerminalPlacementRelation n L data hn :
            FreeModel n L)) -
        w.rawCutoffTerminalOnePrimitive n L data hn)
  abel

/-- Noncircular Step-7 consumer.  The hypotheses are exactly the two reads of
one independently constructed relation-on-the-left chain. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalRelationLeftRelationChain
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (leftRelation : Relations n L data)
    (hleftBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 leftChain =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn)
    (hleftPrimitive : terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        (leftRelation : FreeModel n L)) :
    a = 0 := by
  apply w.eq_zero_of_rawCompleteCutoffChain n L data hn
    (w.rawCompleteCutoffDirectChain n L data hn leftChain)
    (w.rawCompleteCutoffDirectRelation n L data hn leftRelation)
  · exact w.dOne_rawCompleteCutoffDirectChain n L data hn
      leftChain hleftBoundary
  · exact w.terminalSourcePrimitive_rawCompleteCutoffDirectChain
      n L data hn leftChain leftRelation hleftPrimitive

end

end LieRings.MetabelianVanishing
