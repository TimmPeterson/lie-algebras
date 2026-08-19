import LieRings.DimensionSubring.MetabelianVanishing.ProvenanceLedger

/-!
# The terminal contextual Koszul cycle

The contextual collector already constructs the literal terminal factor-two
chain from the manuscript and computes its boundary as the negative of the
aggregate component defect.  This file records the deliberately narrow final
packaging: as soon as the full-relation provenance ledger identifies that
aggregate defect with zero, the same chain (with no replacement or auxiliary
summand) is a degree-one Koszul cycle.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalCycleFintype : Fintype L := Fintype.ofFinite L

/-- Package the literal terminal contextual chain as a Koszul cycle once the
single aggregate full-label cancellation has been established.  This is the
exact endpoint of the terminal cycle calculation: no extra chain is added. -/
def GoverningWitness.contextualTerminalCycleOfDefectEqZero {a : L}
    (w : GoverningWitness n L data a)
    (hdefect : w.terminalFactorDefect n L data hn = 0) :
    Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1 :=
  ⟨w.contextualTerminalChain n L data hn, by
    rw [w.dOne_contextualTerminalChain_eq_neg_defect n L data hn,
      hdefect, neg_zero]⟩

@[simp] theorem GoverningWitness.contextualTerminalCycleOfDefectEqZero_val
    {a : L} (w : GoverningWitness n L data a)
    (hdefect : w.terminalFactorDefect n L data hn = 0) :
    (w.contextualTerminalCycleOfDefectEqZero n L data hn hdefect :
      Koszul.One (terminalSourcePresentation n L data hn) 1) =
        w.contextualTerminalChain n L data hn :=
  rfl

end

end LieRings.MetabelianVanishing
