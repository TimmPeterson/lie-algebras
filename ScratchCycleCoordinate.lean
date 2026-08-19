import LieRings.DimensionSubring.MetabelianVanishing.StepSeven

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance scratchCycleCoordinateFintype : Fintype L := Fintype.ofFinite L

theorem GoverningWitness.terminalSourceCycleCoordinate_eq_external_of_relation
    {a : L} (w : GoverningWitness n L data a)
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (rho : Relations n L data)
    (hprimitive : terminalSourcePrimitive n L data hn c.1 =
      (w.externalPrimitivePreimage n L data hn : FreeModel n L) +
        (rho : FreeModel n L)) :
    terminalEval n L data (terminalSourceCyclePreimage n L data hn c) =
      (w.externalMarkedWord n L data hn).value := by
  have hpreimage : terminalSourceCyclePreimage n L data hn c =
      w.externalPrimitivePreimage n L data hn +
        relationTopPreimage n L data rho := by
    apply Subtype.ext
    rw [terminalSourceCyclePreimage_coe n L data hn c]
    exact hprimitive
  rw [hpreimage, map_add, terminalEval_relationTopPreimage, add_zero]
  rfl

end

end LieRings.MetabelianVanishing
