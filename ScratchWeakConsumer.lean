import LieRings.DimensionSubring.MetabelianVanishing.StepSeven

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

theorem GoverningWitness.scratch_eq_zero_of_contextualCorrectionCoordinate
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.terminalFactorDefect n L data hn)
    (error : TopPreimage n L data)
    (hprimitive : terminalSourcePrimitive n L data hn correction =
      w.componentTracePrimitive n L data hn +
        (error : FreeModel n L))
    (herror : terminalEval n L data error = 0) :
    a = 0 := by
  let cycle := w.contextualTerminalCycleWithCorrection
    n L data hn correction hboundary
  apply w.eq_zero_of_terminalCycleSourceValue n L data hn cycle
  have hpreimage : terminalSourceCyclePreimage n L data hn cycle =
      w.externalPrimitivePreimage n L data hn +
        relationTopPreimage n L data
          (w.terminalSourcePlacementRelation n L data hn) +
        error := by
    apply Subtype.ext
    rw [terminalSourceCyclePreimage_coe]
    change terminalSourcePrimitive n L data hn
        (w.contextualTerminalChain n L data hn + correction) = _
    rw [map_add,
      w.terminalSourcePrimitive_contextualTerminalChain n L data hn,
      hprimitive]
    change w.terminalTwoPrimitive n L data hn +
          (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) +
        (w.componentTracePrimitive n L data hn + (error : FreeModel n L)) =
      (w.externalPrimitivePreimage n L data hn : FreeModel n L) +
        (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) +
        (error : FreeModel n L)
    rw [w.externalPrimitivePreimage_eq n L data hn]
    change w.terminalTwoPrimitive n L data hn +
          (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) +
        (w.componentTracePrimitive n L data hn + (error : FreeModel n L)) =
      (w.componentTracePrimitive n L data hn +
          w.terminalTwoPrimitive n L data hn) +
        (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) +
        (error : FreeModel n L)
    abel
  rw [hpreimage, map_add, map_add,
    terminalEval_relationTopPreimage, herror, add_zero, add_zero]
  exact (w.terminalEval_externalPrimitivePreimage n L data hn).trans
    (w.externalMarkedWord_value n L data hn).symm

end

end LieRings.MetabelianVanishing
