import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalBoundary
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalTopCoordinate
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffPrimitiveStokes

/-!
# Coordinate-level assembly of the exceptional raw-cutoff correction

The manuscript only needs the exceptional primitive discrepancy to vanish in
the terminal cyclic coordinate.  Requiring it to be a full defining relation
would be stronger and, for the canonical boundary remainder, circular.  This
file gives the exact coordinate-level consumer used by the final exceptional
row calculation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalCoordinateAssemblyFintype : Fintype L :=
  Fintype.ofFinite L

/-- A top-layer error with zero terminal cyclic coordinate evaluates to zero.
This is merely injectivity of the chosen cyclic top-layer coordinate. -/
private theorem evaluation_coe_eq_zero_of_terminalEval_eq_zero
    (error : TopPreimage n L data)
    (herror : terminalEval n L data error = 0) :
    evaluation n L data (error : FreeModel n L) = 0 := by
  have hsub :
      (⟨evaluation n L data (error : FreeModel n L), error.property⟩ :
        lowerCentralSeries ℤ L n) = 0 := by
    apply data.topEquiv.injective
    exact herror.trans data.topEquiv.toAddMonoidHom.map_zero.symm
  exact congrArg Subtype.val hsub

/-- Coordinate-level endpoint for the exceptional occurrence ledger.  The
boundary is exact, while its primitive is allowed one top-layer error whose
terminal coordinate is zero, exactly as in the manuscript's `Phi = T ∘ d`
calculation. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalComponentCoordinate
    {a : L} (w : GoverningWitness n L data a)
    (exceptionalChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (error : TopPreimage n L data)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 exceptionalChain =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
        z • c.holeExceptionalComponentFactor n L data hn))
    (hprimitive : terminalSourcePrimitive n L data hn exceptionalChain =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
          z • c.holeExceptionalComponentPrimitive n L data hn) +
        (error : FreeModel n L))
    (herror : terminalEval n L data error = 0) :
    a = 0 := by
  let markOneChain :=
    w.rawCutoffMarkOneCorrectionChain n L data hn exceptionalChain
  apply w.eq_zero_of_rawCutoffMarkOneChain n L data hn markOneChain
  · apply w.dOne_rawCutoffMarkOneCorrectionChain n L data hn
      exceptionalChain
    rw [hboundary]
    exact (w.rawCutoffHoleExceptionalFullLabelFactor_eq_component
      n L data hn).symm
  · have herrorEval :
        evaluation n L data (error : FreeModel n L) = 0 :=
      evaluation_coe_eq_zero_of_terminalEval_eq_zero n L data error herror
    have hnonHole : evaluation n L data
        (w.rawCutoffNonHolePrimitiveError n L data hn : FreeModel n L) = 0 :=
      (w.rawCutoffNonHolePrimitiveError n L data hn).property
    have htailOne : evaluation n L data
        (w.rawCutoffHoleTailOnePrimitiveError n L data hn : FreeModel n L) = 0 :=
      (w.rawCutoffHoleTailOnePrimitiveError n L data hn).property
    have hmarkPrimitive :
        terminalSourcePrimitive n L data hn markOneChain =
          w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn +
            (w.rawCutoffNonHolePrimitiveError n L data hn : FreeModel n L) +
            (w.rawCutoffHoleTailOnePrimitiveError n L data hn :
              FreeModel n L) +
            (error : FreeModel n L) := by
      change terminalSourcePrimitive n L data hn
          (w.rawCutoffMarkOneCorrectionChain n L data hn exceptionalChain) = _
      rw [GoverningWitness.rawCutoffMarkOneCorrectionChain,
        map_add, map_add,
        w.terminalSourcePrimitive_rawCutoffNonHoleCorrectionChain
          n L data hn,
        w.terminalSourcePrimitive_rawCutoffHoleTailOneCorrectionChain
          n L data hn,
        hprimitive,
        ← w.rawCutoffHoleExceptionalFullLabelPrimitive_eq_component
          n L data hn]
      have hfull :
          w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
                w.rawCutoffHoleTailOneFullLabelPrimitive n L data hn +
              w.rawCutoffHoleExceptionalFullLabelPrimitive n L data hn =
            w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn := by
        calc
          _ = w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
              (w.rawCutoffHoleTailOneFullLabelPrimitive n L data hn +
                w.rawCutoffHoleExceptionalFullLabelPrimitive
                  n L data hn) := by abel
          _ = w.rawCutoffNonHoleFullLabelPrimitive n L data hn +
              w.rawCutoffHoleFullLabelPrimitive n L data hn := by
            rw [w.rawCutoffHoleFullLabelPrimitive_split n L data hn]
          _ = w.rawCutoffTraceMarkOneFullLabelPrimitive n L data hn := by
            simpa only [
              GoverningWitness.rawCutoffTraceMarkOneFullLabelPrimitive] using
              w.rawCutoffMarkOneFullLabelPrimitive_split n L data hn
      rw [← hfull]
      abel
    rw [hmarkPrimitive,
      w.rawCutoffTraceMarkOneFullLabelPrimitive_eq_trace n L data hn,
      ← w.pbwPrimitive_rawCutoffAggregateTerminalComponentFullLabelWord
        n L data hn]
    simp only [map_add, map_sub, hnonHole, htailOne, herrorEval,
      add_zero]
    simpa only [map_add, map_sub] using
      w.evaluation_rawCutoffAggregateTerminalComponentFullLabelWord
        n L data hn

end

end LieRings.MetabelianVanishing
