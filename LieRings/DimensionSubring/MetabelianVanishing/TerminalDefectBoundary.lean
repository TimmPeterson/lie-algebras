import LieRings.DimensionSubring.MetabelianVanishing.TerminalCertificateBridge

/-!
# An unconditional boundary preimage of the terminal defect

The contextual terminal chain already has boundary equal to the negative of
the terminal component defect.  Its negative is therefore a completely
explicit preimage of that defect in the genuine terminal Koszul
presentation.  We also record its primitive, since that formula identifies
precisely why this boundary preimage alone does not finish the manuscript's
corrected-cycle argument.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalDefectBoundaryFintype : Fintype L :=
  Fintype.ofFinite L

/-- The explicit boundary preimage obtained by reversing the already
constructed contextual terminal wall.  Every relation entry in this chain is
an actual element of the terminal source relation module. -/
def GoverningWitness.terminalDefectBoundaryCorrection {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  -w.contextualTerminalChain n L data hn

/-- The correction has exactly the positive boundary orientation required by
the corrected-cycle interface. -/
@[simp] theorem GoverningWitness.dOne_terminalDefectBoundaryCorrection
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.terminalDefectBoundaryCorrection n L data hn) =
      w.terminalFactorDefect n L data hn := by
  rw [GoverningWitness.terminalDefectBoundaryCorrection, map_neg,
    w.dOne_contextualTerminalChain_eq_neg_defect n L data hn]
  exact neg_neg _

/-- Exact primitive audit for the explicit boundary preimage.  It contributes
the negative terminal-two primitive, up to the displayed genuine full
relation; the missing manuscript construction must instead contribute the
component-trace primitive. -/
theorem GoverningWitness.terminalSourcePrimitive_terminalDefectBoundaryCorrection
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.terminalDefectBoundaryCorrection n L data hn) =
      -w.terminalTwoPrimitive n L data hn -
        (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) := by
  rw [GoverningWitness.terminalDefectBoundaryCorrection, map_neg,
    w.terminalSourcePrimitive_contextualTerminalChain n L data hn]
  abel

end

end LieRings.MetabelianVanishing
