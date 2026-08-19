import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalTailAssembly

/-!
# The exceptional component boundary

The complete full-label correction already bounds the whole mark-one ledger.
Subtracting the two previously realized non-exceptional pieces leaves exactly
the exceptional occurrence ledger.  This is the cycle/boundary assertion at
the last unresolved square; it uses the signed occurrence coefficients and
does not split a Smith coefficient among component descendants.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalBoundaryFintype : Fintype L :=
  Fintype.ofFinite L

/-- The signed remainder after removing the non-hole and derived-tail hole
parts from the complete mark-one boundary. -/
def GoverningWitness.rawCutoffExceptionalBoundaryChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.rawCutoffTotalFullLabelCorrection n L data hn -
    w.rawCutoffNonHoleCorrectionChain n L data hn -
      w.rawCutoffHoleTailOneCorrectionChain n L data hn

/-- The exceptional component ledger is a genuine terminal-source boundary.
This is the exact aggregate cycle assertion; each cell retains its occurrence
coefficient until after the three disjoint ledgers are subtracted. -/
theorem GoverningWitness.dOne_rawCutoffExceptionalBoundaryChain
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffExceptionalBoundaryChain n L data hn) =
      (w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
        z • c.holeExceptionalComponentFactor n L data hn) := by
  rw [GoverningWitness.rawCutoffExceptionalBoundaryChain, map_sub, map_sub,
    w.dOne_rawCutoffTotalFullLabelCorrection_eq_fullLabel n L data hn,
    w.rawCutoffTerminalComponentFullLabel_eq_trace n L data hn,
    w.dOne_rawCutoffNonHoleCorrectionChain n L data hn,
    w.dOne_rawCutoffHoleTailOneCorrectionChain n L data hn]
  rw [← w.rawCutoffHoleExceptionalFullLabelFactor_eq_component
    n L data hn]
  rw [← w.rawCutoffMarkOneFullLabelFactor_split n L data hn,
    ← w.rawCutoffHoleFullLabelFactor_split n L data hn]
  abel_nf
  exact add_sub_cancel_left _ _

end

end LieRings.MetabelianVanishing
