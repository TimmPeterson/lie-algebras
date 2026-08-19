import LieRings.DimensionSubring.MetabelianVanishing.ClosedSquare

/-!
Scratch audit of the purely algebraic terminal-cycle packaging.

This deliberately isolates what follows from the current closed-square API
from the genuinely missing row theorem.  The chosen lift below is *not* the
manuscript's factor-two ledger: the only presently available witness of the
displayed boundary is the negative contextual wall itself.  Consequently the
resulting cycle may be zero and cannot furnish the required terminal row
certificate.  The definitions nevertheless pin down the exact type of the
missing stronger construction.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

private theorem terminalFactorDefect_has_preimage {a : L}
    (w : GoverningWitness n L data a) :
    ∃ c : Koszul.One (terminalSourcePresentation n L data hn) 1,
      Koszul.dOne (terminalSourcePresentation n L data hn) 1 c =
        w.terminalFactorDefect n L data hn := by
  refine ⟨-w.contextualTerminalChain n L data hn, ?_⟩
  rw [map_neg, w.dOne_contextualTerminalChain_eq_neg_defect n L data hn]
  exact neg_neg _

/-- An arbitrary algebraic preimage of the terminal component defect. -/
private def terminalFactorDefectLift {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  Classical.choose (terminalFactorDefect_has_preimage n L data hn w)

private theorem dOne_terminalFactorDefectLift {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (terminalFactorDefectLift n L data hn w) =
      w.terminalFactorDefect n L data hn :=
  Classical.choose_spec (terminalFactorDefect_has_preimage n L data hn w)

/-- The formal sum which becomes the genuine manuscript cycle once
`terminalFactorDefectLift` is replaced by the provenance-grouped interior
factor-two ledger. -/
private def algebraicCompleteFactorTwoChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  w.contextualTerminalChain n L data hn +
    terminalFactorDefectLift n L data hn w

private theorem dOne_algebraicCompleteFactorTwoChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (algebraicCompleteFactorTwoChain n L data hn w) =
      rightSymbol n L data hn 2 n (by omega) w.theta := by
  rw [algebraicCompleteFactorTwoChain, map_add,
    w.dOne_contextualTerminalChain_eq_neg_defect n L data hn,
    dOne_terminalFactorDefectLift]
  rw [rightSymbol_theta_terminal_eq_zero n L data hn w]
  exact neg_add_cancel _

private def algebraicCompleteFactorTwoCycle {a : L}
  (w : GoverningWitness n L data a) :
    Koszul.cyclesOne (terminalSourcePresentation n L data hn) 1 :=
  ⟨algebraicCompleteFactorTwoChain n L data hn w, by
    change Koszul.dOne (terminalSourcePresentation n L data hn) 1
      (algebraicCompleteFactorTwoChain n L data hn w) = 0
    rw [dOne_algebraicCompleteFactorTwoChain,
      rightSymbol_theta_terminal_eq_zero n L data hn w]
    rfl⟩

/-- The strict comparison map is not part of the missing calculation. -/
private def algebraicTerminalComparison :
    Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id :=
  Koszul.Presentation.liftHom
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega)) LinearMap.id

/-- With the current API, after the kernel proof the sole remaining packet
field is exactly the certificate displayed as an argument here.  An arbitrary
defect lift cannot produce this certificate; the provenance-grouped ledger
must produce the cycle and certificate simultaneously. -/
private def algebraicPacketOfCertificate {a : L}
    (w : GoverningWitness n L data a)
    (hcert : TerminalRowCertificate n L data hn
      (w.externalMarkedWord n L data hn)
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega))
          (algebraicTerminalComparison n L data hn) 1
          (algebraicCompleteFactorTwoCycle n L data hn w)))) :
    TerminalQuadraticPacket n L data hn where
  g := algebraicTerminalComparison n L data hn
  cycle := algebraicCompleteFactorTwoCycle n L data hn w
  actualRows := w.externalRows n L data hn
  actualMarked := w.externalMarkedWord n L data hn
  actualMarked_word := rfl
  certificate := hcert

end

end LieRings.MetabelianVanishing
