import LieRings.DimensionSubring.MetabelianVanishing.CompleteCutoffSmith

/-!
# The corrected cycle from the complete cutoff continuation

This file is the algebraic endpoint of the complete marked-row ledger.  The
remaining geometric input is deliberately narrow: a chain realizing the
ordinary factor-two read of the continued cutoff, whose source primitive is
the ordinary factor-one read up to a top-layer error of zero terminal
coordinate.  The theorem below combines that chain with the original
factor-first chain and the retained marked factor-two wall.  All other errors
are grouped as genuine full relations before applying the terminal cyclic
coordinate.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeCutoffCycleFintype : Fintype L :=
  Fintype.ofFinite L

/-- Once the ordinary part of the continued cutoff has been realized with
the manuscript's terminal coordinate, the complete cutoff ledger is a
genuine source cycle with the governing external coordinate. -/
theorem GoverningWitness.eq_zero_of_completeCutoffCorrection
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (error : TopPreimage n L data)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.rawCutoffOrdinaryFactorTwo n L data hn)
    (hprimitive : terminalSourcePrimitive n L data hn correction =
      w.rawCutoffOrdinaryPrimitive n L data hn +
        (error : FreeModel n L))
    (herror : terminalEval n L data error = 0) :
    a = 0 := by
  have hcompleteBoundary :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (w.completeFactorTwoChain n L data hn) =
        -rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) := by
    calc
      _ = -w.completeFactorTwoCutoffFullLabel n L data hn := by
        rw [← w.completeNormalFormFullLabelRead_eq_dOne_completeFactorTwoChain
          n L data hn]
        exact w.completeNormalFullLabel_eq_neg_cutoff n L data hn
      _ = -rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) := by
        rw [w.rightSymbol_rawCompleteCutoffWord n L data hn]
  have hrawBoundary :=
    w.rightSymbol_rawCompleteCutoffWord_eq_ordinary_add_dOne
      n L data hn
  have hcycleBoundary :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          ((w.completeFactorTwoChain n L data hn +
            w.rawCutoffTerminalTwoChain n L data hn) + correction) = 0 := by
    rw [map_add, map_add, hcompleteBoundary,
      w.dOne_rawCutoffTerminalTwoChain_eq_symbol_sub_ordinary
        n L data hn, hboundary]
    abel
  let cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1 :=
    ⟨(w.completeFactorTwoChain n L data hn +
      w.rawCutoffTerminalTwoChain n L data hn) + correction,
      hcycleBoundary⟩
  let sourceRelation : Relations n L data :=
    w.terminalOneRelation n L data hn -
      w.rawCutoffTerminalOneRelation n L data hn +
      w.completeFactorTwoPrimitiveCorrection n L data +
      w.rawCutoffTerminalTwoPlacementRelation n L data hn
  let sourcePrimitive : TopPreimage n L data :=
    w.externalPrimitivePreimage n L data hn +
      relationTopPreimage n L data sourceRelation + error
  have hsourceRelation : (sourceRelation : FreeModel n L) =
      w.terminalOnePrimitive n L data hn -
        (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) +
        (w.completeFactorTwoPrimitiveCorrection n L data :
          FreeModel n L) +
        (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
          FreeModel n L) := by
    dsimp [sourceRelation]
    rw [w.terminalOneRelation_coe n L data hn]
  have hsource : (sourcePrimitive : FreeModel n L) =
      terminalSourcePrimitive n L data hn cycle.1 := by
    change (w.externalPrimitivePreimage n L data hn : FreeModel n L) +
        (sourceRelation : FreeModel n L) + (error : FreeModel n L) =
      terminalSourcePrimitive n L data hn
        ((w.completeFactorTwoChain n L data hn +
          w.rawCutoffTerminalTwoChain n L data hn) + correction)
    rw [map_add, map_add,
      w.terminalSourcePrimitive_completeFactorTwoChain n L data hn,
      w.terminalSourcePrimitive_rawCutoffTerminalTwoChain n L data hn,
      hprimitive, hsourceRelation,
      w.externalPrimitivePreimage_eq n L data hn]
    have hstokes := w.rawPBWPrimitiveTheta_eq_complete_add_cutoff
      n L data hn
    have hraw := w.pbwPrimitive_rawCompleteCutoffWord_eq_terminal_reads
      n L data hn
    have htheta := w.pbwPrimitive_theta_external n L data hn
    rw [hraw] at hstokes
    rw [htheta] at hstokes
    have hbase :
        w.componentTracePrimitive n L data hn +
              w.terminalTwoPrimitive n L data hn +
              w.terminalOnePrimitive n L data hn -
              (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) =
            w.completeFactorTwoFullLabelPrimitive n L data hn +
              w.rawCutoffOrdinaryPrimitive n L data hn +
              w.rawCutoffTerminalTwoPrimitive n L data hn := by
      calc
        _ = (w.componentTracePrimitive n L data hn +
                w.terminalOnePrimitive n L data hn +
                w.terminalTwoPrimitive n L data hn) -
              (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) := by
            abel
        _ = (w.completeFactorTwoFullLabelPrimitive n L data hn +
                (w.rawCutoffOrdinaryPrimitive n L data hn +
                  w.rawCutoffTerminalTwoPrimitive n L data hn +
                  (w.rawCutoffTerminalOneRelation n L data hn :
                    FreeModel n L))) -
              (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) := by
            rw [hstokes]
        _ = _ := by abel
    calc
      w.componentTracePrimitive n L data hn +
              w.terminalTwoPrimitive n L data hn +
            (w.terminalOnePrimitive n L data hn -
                (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) +
                (w.completeFactorTwoPrimitiveCorrection n L data :
                  FreeModel n L) +
              (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
                FreeModel n L)) +
          (error : FreeModel n L) =
        (w.componentTracePrimitive n L data hn +
              w.terminalTwoPrimitive n L data hn +
              w.terminalOnePrimitive n L data hn -
              (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L)) +
            (w.completeFactorTwoPrimitiveCorrection n L data :
              FreeModel n L) +
            (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
              FreeModel n L) +
          (error : FreeModel n L) := by abel
      _ = (w.completeFactorTwoFullLabelPrimitive n L data hn +
              w.rawCutoffOrdinaryPrimitive n L data hn +
              w.rawCutoffTerminalTwoPrimitive n L data hn) +
            (w.completeFactorTwoPrimitiveCorrection n L data :
              FreeModel n L) +
            (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
              FreeModel n L) +
          (error : FreeModel n L) := by rw [hbase]
      _ = _ := by abel
  have hcoordinate : terminalEval n L data sourcePrimitive =
      (w.externalMarkedWord n L data hn).value := by
    change terminalEval n L data
        (w.externalPrimitivePreimage n L data hn +
          relationTopPreimage n L data sourceRelation + error) = _
    rw [map_add, map_add, terminalEval_relationTopPreimage,
      herror, add_zero, add_zero]
    exact (w.terminalEval_externalPrimitivePreimage n L data hn).trans
      (w.externalMarkedWord_value n L data hn).symm
  exact w.eq_zero_of_terminalSourceCoordinate n L data hn cycle
    sourcePrimitive hsource hcoordinate

/-- Evaluation-level form of the complete-cutoff consumer.  The row
collector only has to show that its source primitive and the ordinary
cutoff primitive have the same image in `L`; the required `TopPreimage`
and its zero terminal coordinate are then canonical. -/
theorem GoverningWitness.eq_zero_of_completeCutoffCorrection_eval
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.rawCutoffOrdinaryFactorTwo n L data hn)
    (heval : evaluation n L data
        (terminalSourcePrimitive n L data hn correction -
          w.rawCutoffOrdinaryPrimitive n L data hn) = 0) :
    a = 0 := by
  let error : TopPreimage n L data :=
    ⟨terminalSourcePrimitive n L data hn correction -
        w.rawCutoffOrdinaryPrimitive n L data hn, by
      change evaluation n L data
          (terminalSourcePrimitive n L data hn correction -
            w.rawCutoffOrdinaryPrimitive n L data hn) ∈
        lowerCentralSeries ℤ L n
      rw [heval]
      exact LieSubmodule.zero_mem _⟩
  apply w.eq_zero_of_completeCutoffCorrection n L data hn
    correction error hboundary
  · change terminalSourcePrimitive n L data hn correction =
      w.rawCutoffOrdinaryPrimitive n L data hn +
        (terminalSourcePrimitive n L data hn correction -
          w.rawCutoffOrdinaryPrimitive n L data hn)
    abel
  · change data.topEquiv.toIntLinearEquiv.toLinearMap
      ⟨evaluation n L data
          (terminalSourcePrimitive n L data hn correction -
            w.rawCutoffOrdinaryPrimitive n L data hn), _⟩ = 0
    have hevalSubtype :
        (⟨evaluation n L data
            (terminalSourcePrimitive n L data hn correction -
              w.rawCutoffOrdinaryPrimitive n L data hn), by
            rw [heval]
            exact LieSubmodule.zero_mem _⟩ :
          lowerCentralSeries ℤ L n) = 0 := by
      apply Subtype.ext
      exact heval
    rw [hevalSubtype, map_zero]

end

end LieRings.MetabelianVanishing
