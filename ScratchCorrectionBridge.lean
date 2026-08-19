import ScratchAdaptedBridge
import LieRings.DimensionSubring.MetabelianVanishing.TerminalCorrection
import LieRings.DimensionSubring.MetabelianVanishing.TerminalRealization

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

theorem correctionPrimitive_reduction {a : L}
    (w : GoverningWitness n L data a)
    (hbridge : ∃ sigma : Relations n L data,
      w.completeFactorTwoFullLabelPrimitive n L data hn =
        w.componentTracePrimitive n L data hn +
          (sigma : FreeModel n L)) :
    ∃ rho : Relations n L data,
      terminalSourcePrimitive n L data hn
          (w.completeFactorTwoChain n L data hn) =
        w.componentTracePrimitive n L data hn +
          (rho : FreeModel n L) := by
  obtain ⟨sigma, hsigma⟩ := hbridge
  refine ⟨sigma + w.completeFactorTwoPrimitiveCorrection n L data, ?_⟩
  rw [w.terminalSourcePrimitive_completeFactorTwoChain n L data hn]
  change w.completeFactorTwoFullLabelPrimitive n L data hn +
      (w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L) =
    w.componentTracePrimitive n L data hn +
      ((sigma : FreeModel n L) +
        (w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L))
  rw [hsigma]
  abel

/-- The only genuinely geometric comparison still needed after the raw
full-label Stokes identity: the stopped cutoff continues to the contextual
terminal-two wall, while its terminal-one leaves are whole relations. -/
theorem correctionPrimitive_of_cutoffPrimitive {a : L}
    (w : GoverningWitness n L data a)
    (hcutoff : ∃ tau : Relations n L data,
      pbwPrimitive n L data hn (w.scratchCompleteCutoffWord n L data) =
        w.terminalTwoPrimitive n L data hn +
          (tau : FreeModel n L)) :
    ∃ rho : Relations n L data,
      terminalSourcePrimitive n L data hn
          (w.completeFactorTwoChain n L data hn) =
        w.componentTracePrimitive n L data hn +
          (rho : FreeModel n L) := by
  obtain ⟨tau, htau⟩ := hcutoff
  apply correctionPrimitive_reduction n L data hn w
  refine ⟨w.terminalOneRelation n L data hn - tau, ?_⟩
  have hcomplete := w.scratchPBWPrimitiveTheta_eq_complete_add_cutoff
    n L data hn
  have hcontext := w.pbwPrimitive_theta_external n L data hn
  rw [htau] at hcomplete
  rw [hcontext] at hcomplete
  rw [w.terminalOneRelation_coe n L data hn]
  change w.completeFactorTwoFullLabelPrimitive n L data hn =
    w.componentTracePrimitive n L data hn +
      ((w.terminalOneRelation n L data hn : FreeModel n L) -
        (tau : FreeModel n L))
  change w.componentTracePrimitive n L data hn +
        w.terminalOnePrimitive n L data hn +
        w.terminalTwoPrimitive n L data hn =
      w.completeFactorTwoFullLabelPrimitive n L data hn +
        (w.terminalTwoPrimitive n L data hn + (tau : FreeModel n L))
    at hcomplete
  abel_nf at hcomplete ⊢
  exact hcomplete.symm

end

end LieRings.MetabelianVanishing
