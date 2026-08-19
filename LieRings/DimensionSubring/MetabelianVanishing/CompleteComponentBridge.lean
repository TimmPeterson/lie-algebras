import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoTerminalRead

/-!
# Common terminal factor-two read

The contextual component collector and the complete full-relation collector
are two normalizations of the same terminal factor-two edge.  This file
records the basis-independent comparison needed by the final closed square.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeComponentBridgeFintype : Fintype L :=
  Fintype.ofFinite L

/-- Factor-two PBW read of the already normalized, provenance-retaining
component frontier. -/
def GoverningWitness.completeComponentPBWFactorTwo {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.completeComponentPBWFrontier n L data hn).sum (fun s z ↦
    z • rightSymbol n L data hn 2 n (by omega) (s.value n L data hn))

/-- The normalized adapted component frontier is a common, basis-independent
realization of the terminal factor defect. -/
theorem GoverningWitness.completeComponentPBWFactorTwo_eq_terminalFactorDefect
    {a : L} (w : GoverningWitness n L data a) :
    w.completeComponentPBWFactorTwo n L data hn =
      w.terminalFactorDefect n L data hn := by
  have h := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.evaluate_completeComponentPBWFrontier n L data hn)
  change rightSymbol n L data hn 2 n (by omega)
      ((w.completeComponentPBWFrontier n L data hn).sum
        (fun s z ↦ z • s.value n L data hn)) =
    rightSymbol n L data hn 2 n (by omega)
      ((w.provenancedCells n L data hn).sum
        (fun c z ↦ z • c.componentRow.value)) at h
  rw [map_finsuppSum, map_finsuppSum] at h
  simpa only [map_zsmul,
    GoverningWitness.completeComponentPBWFactorTwo,
    GoverningWitness.terminalFactorDefect,
    ProvenancedCell.factorEdge] using h

end

end LieRings.MetabelianVanishing
