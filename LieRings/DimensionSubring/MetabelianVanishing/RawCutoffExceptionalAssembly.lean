import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffTotalCorrection
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffPrimitiveStokes

/-!
# Final assembly from the exceptional raw-cutoff chain

All non-exceptional cells have already been realized in the mark-one
aggregate.  Consequently the final argument needs only a chain realizing
the exceptional full-label factor, together with its literal primitive
identity modulo one genuine full relation.  The primitive Stokes identity
then identifies the aggregate mark-one primitive with the PBW terminal
component read, whose required evaluation was established independently.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalAssemblyFintype : Fintype L :=
  Fintype.ofFinite L

/-- Final raw-cutoff implication, with precisely the two identities supplied
by the exceptional-cycle construction.  No component of a relation is
assumed to be a relation: the only error term is the displayed element of
`Relations`. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalChain
    {a : L} (w : GoverningWitness n L data a)
    (exceptionalChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (exceptionalRelation : Relations n L data)
    (hexceptionalBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 exceptionalChain =
      w.rawCutoffHoleExceptionalFullLabelFactor n L data hn)
    (hexceptionalPrimitive :
      terminalSourcePrimitive n L data hn exceptionalChain =
        w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn +
          (exceptionalRelation : FreeModel n L)) :
    a = 0 := by
  let markOneChain :=
    w.rawCutoffMarkOneCorrectionChain n L data hn exceptionalChain
  apply w.eq_zero_of_rawCutoffMarkOneChain n L data hn markOneChain
  · exact w.dOne_rawCutoffMarkOneCorrectionChain n L data hn
      exceptionalChain hexceptionalBoundary
  · rw [w.terminalSourcePrimitive_rawCutoffMarkOneCorrectionChain
      n L data hn exceptionalChain exceptionalRelation
      hexceptionalPrimitive]
    have hplacement : evaluation n L data
        (w.rawCutoffMarkOnePlacementRelation n L data hn
          exceptionalRelation : FreeModel n L) = 0 :=
      (w.rawCutoffMarkOnePlacementRelation n L data hn
        exceptionalRelation).property
    rw [w.rawCutoffTraceMarkOneFullLabelPrimitive_eq_trace n L data hn,
      ← w.pbwPrimitive_rawCutoffAggregateTerminalComponentFullLabelWord
        n L data hn]
    simpa only [map_add, map_sub, hplacement, add_zero] using
      w.evaluation_rawCutoffAggregateTerminalComponentFullLabelWord
        n L data hn

end

end LieRings.MetabelianVanishing
