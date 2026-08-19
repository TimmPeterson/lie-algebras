import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffHoleTailCorrection

/-!
# Aggregate realization of the raw mark-one ledger

The non-hole and tail-one hole cells have already been realized by genuine
terminal-source chains.  This file performs only the final additive splice:
after supplying a realization of the complementary exceptional ledger, their
sum realizes the complete mark-one full-label ledger.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffMarkOneAggregateFintype : Fintype L :=
  Fintype.ofFinite L

/-- The complete mark-one correction obtained by adjoining an exceptional
chain to the already realized non-hole and tail-one ledgers. -/
def GoverningWitness.rawCutoffMarkOneCorrectionChain
    {a : L} (w : GoverningWitness n L data a)
    (exceptionalChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.rawCutoffNonHoleCorrectionChain n L data hn +
    w.rawCutoffHoleTailOneCorrectionChain n L data hn +
      exceptionalChain

/-- Literal full-relation primitive attached to the complete raw mark-one
ledger. -/
def GoverningWitness.rawCutoffTraceMarkOneFullLabelPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
    z • if c.mark.val = 1 then
      pbwPrimitive n L data hn
        (contextualFullRelationWord n L data hn
          c.root c.context c.left [])
    else 0)

/-- All genuine full-relation placement errors in the three-part mark-one
realization. -/
def GoverningWitness.rawCutoffMarkOnePlacementRelation
    {a : L} (w : GoverningWitness n L data a)
    (exceptionalRelation : Relations n L data) : Relations n L data :=
  w.rawCutoffNonHolePrimitiveError n L data hn +
    w.rawCutoffHoleTailOnePrimitiveError n L data hn +
      exceptionalRelation

/-- The only missing boundary input in the complete mark-one calculation is
the exceptional hole ledger. -/
theorem GoverningWitness.dOne_rawCutoffMarkOneCorrectionChain
    {a : L} (w : GoverningWitness n L data a)
    (exceptionalChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hexceptional : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 exceptionalChain =
      w.rawCutoffHoleExceptionalFullLabelFactor n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffMarkOneCorrectionChain n L data hn exceptionalChain) =
      w.rawCutoffTraceMarkOneFullLabel n L data hn := by
  rw [GoverningWitness.rawCutoffMarkOneCorrectionChain, map_add, map_add,
    w.dOne_rawCutoffNonHoleCorrectionChain n L data hn,
    w.dOne_rawCutoffHoleTailOneCorrectionChain n L data hn,
    hexceptional]
  calc
    w.rawCutoffNonHoleFullLabelFactor n L data hn +
          w.rawCutoffHoleTailOneFullLabelFactor n L data hn +
        w.rawCutoffHoleExceptionalFullLabelFactor n L data hn =
      w.rawCutoffNonHoleFullLabelFactor n L data hn +
        (w.rawCutoffHoleTailOneFullLabelFactor n L data hn +
          w.rawCutoffHoleExceptionalFullLabelFactor n L data hn) := by
        abel
    _ = w.rawCutoffNonHoleFullLabelFactor n L data hn +
        w.rawCutoffHoleFullLabelFactor n L data hn := by
      rw [w.rawCutoffHoleFullLabelFactor_split n L data hn]
    _ = w.rawCutoffTraceMarkOneFullLabel n L data hn :=
      w.rawCutoffMarkOneFullLabelFactor_split n L data hn

/-- Primitive form of the same three-part aggregate.  Its only non-literal
term is the displayed sum of genuine full relations. -/
theorem GoverningWitness.terminalSourcePrimitive_rawCutoffMarkOneCorrectionChain
    {a : L} (w : GoverningWitness n L data a)
    (exceptionalChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (exceptionalRelation : Relations n L data)
    (hexceptional : terminalSourcePrimitive n L data hn exceptionalChain =
      w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn +
        (exceptionalRelation : FreeModel n L)) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffMarkOneCorrectionChain n L data hn exceptionalChain) =
      w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn +
        (w.rawCutoffMarkOnePlacementRelation n L data hn
          exceptionalRelation : FreeModel n L) := by
  rw [GoverningWitness.rawCutoffMarkOneCorrectionChain, map_add, map_add,
    w.terminalSourcePrimitive_rawCutoffNonHoleCorrectionChain n L data hn,
    w.terminalSourcePrimitive_rawCutoffHoleTailOneCorrectionChain
      n L data hn,
    hexceptional,
    GoverningWitness.rawCutoffMarkOnePlacementRelation]
  have hprimitive :
      w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
          w.rawCutoffHoleTailOneFullLabelPrimitive n L data hn +
            w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn =
        w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn := by
    calc
      _ = w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
          (w.rawCutoffHoleTailOneFullLabelPrimitive n L data hn +
            w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn) := by
          abel
      _ = w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
          w.rawCutoffHoleFullLabelPrimitive n L data hn := by
        rw [w.rawCutoffHoleFullLabelPrimitive_split n L data hn]
      _ = w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn := by
        simpa only [
          GoverningWitness.rawCutoffTraceMarkOneFullLabelPrimitive] using
          w.rawCutoffMarkOneFullLabelPrimitive_split n L data hn
  rw [← hprimitive]
  have hcoe :
      ((w.rawCutoffNonHolePrimitiveError n L data hn +
          w.rawCutoffHoleTailOnePrimitiveError n L data hn +
        exceptionalRelation : Relations n L data) : FreeModel n L) =
      (w.rawCutoffNonHolePrimitiveError n L data hn : FreeModel n L) +
        (w.rawCutoffHoleTailOnePrimitiveError n L data hn :
          FreeModel n L) +
        (exceptionalRelation : FreeModel n L) := by
    rfl
  rw [hcoe]
  abel

end

end LieRings.MetabelianVanishing
