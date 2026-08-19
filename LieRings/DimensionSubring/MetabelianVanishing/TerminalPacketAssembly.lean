import LieRings.DimensionSubring.MetabelianVanishing.Assembly

/-!
# Assembly of the certified terminal packet

This file is the deliberately small endpoint of the factor-two row
calculation.  The collector must supply the actual terminal Koszul cycle and
a certificate comparing the complete external marked word with the placed
Smith-block word.  Once those two facts are available, the finite row list is
the already existing list `GoverningWitness.externalRows`; no additional
choice of rows or primitive is made here.

In particular, none of the declarations below assert that the raw terminal
wall is a cycle.  Their `cycle` argument has subtype `Koszul.cyclesOne`, so the
complete cycle proof must already have been established by the full trace.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalPacketAssemblyFintype : Fintype L := Fintype.ofFinite L

/-! ## Direct assembly from the complete trace certificate -/

/-- Package the genuine terminal source cycle and the complete row
certificate into the terminal quadratic packet.  The actual rows and marked
word are not reconstructed: they are exactly the external rows and complete
external primitive already attached to the governing witness. -/
def GoverningWitness.terminalPacketOfCycleCertificate {a : L}
    (w : GoverningWitness n L data a)
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (certificate : TerminalRowCertificate n L data hn
      (w.externalMarkedWord n L data hn)
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega)) g 1 cycle))) :
    TerminalQuadraticPacket n L data hn where
  g := g
  cycle := cycle
  actualRows := w.externalRows n L data hn
  actualMarked := w.externalMarkedWord n L data hn
  actualMarked_word := rfl
  certificate := certificate

@[simp] theorem GoverningWitness.terminalPacketOfCycleCertificate_orientedPrimitive
    {a : L} (w : GoverningWitness n L data a)
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (certificate : TerminalRowCertificate n L data hn
      (w.externalMarkedWord n L data hn)
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega)) g 1 cycle))) :
    (w.terminalPacketOfCycleCertificate n L data hn g cycle certificate).orientedPrimitive =
      (w.externalMarkedWord n L data hn).value :=
  rfl

/-- The complete Step-7 terminal consequence.  After the collector has
produced the genuine factor-two cycle and its full-relation row certificate,
Point 6 annihilates the transported Smith block and hence the governing top
coordinate. -/
theorem GoverningWitness.eq_zero_of_terminalCycleCertificate {a : L}
    (w : GoverningWitness n L data a)
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (certificate : TerminalRowCertificate n L data hn
      (w.externalMarkedWord n L data hn)
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega)) g 1 cycle))) :
    a = 0 := by
  let p := w.terminalPacketOfCycleCertificate
    n L data hn g cycle certificate
  apply w.eq_zero_of_terminalPacket n L data hn p
  rfl

/-! ## Assembly through an explicitly collected row list -/

/-- A variant useful when the terminal collector first constructs a separate
finite row list and marked word.  The trace certificate compares the external
word with that actual word, while the block certificate performs the Smith
transport.  Both certificates retain genuine full relations throughout. -/
def terminalPacketOfCollectedRows
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (actualRows :
      (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ)
    (actualMarked : TerminalMarkedWord n L data hn)
    (actualMarked_word : actualMarked.word =
      terminalPacketWord n L data actualRows)
    (blockCertificate : TerminalRowCertificate n L data hn actualMarked
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega)) g 1 cycle))) :
    TerminalQuadraticPacket n L data hn where
  g := g
  cycle := cycle
  actualRows := actualRows
  actualMarked := actualMarked
  actualMarked_word := actualMarked_word
  certificate := blockCertificate

/-- A trace certificate from the governing external word to the explicitly
collected marked word supplies exactly the primitive equality required by the
final packet theorem. -/
theorem GoverningWitness.eq_zero_of_collectedTerminalPacket {a : L}
    (w : GoverningWitness n L data a)
    (g : Koszul.Presentation.Hom (terminalSourcePresentation n L data hn)
      (rPresentation n L data (by omega)) LinearMap.id)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (actualRows :
      (Relations n L data × UEA ℤ (FreeModel n L)) →₀ ℤ)
    (actualMarked : TerminalMarkedWord n L data hn)
    (actualMarked_word : actualMarked.word =
      terminalPacketWord n L data actualRows)
    (traceCertificate : TerminalRowCertificate n L data hn
      (w.externalMarkedWord n L data hn) actualMarked)
    (blockCertificate : TerminalRowCertificate n L data hn actualMarked
      (quadraticBlockMarkedWord n L data hn
        (Koszul.PresentationHomology.cyclesMap
          (terminalSourcePresentation n L data hn)
          (rPresentation n L data (by omega)) g 1 cycle))) :
    a = 0 := by
  let p := terminalPacketOfCollectedRows n L data hn g cycle actualRows
    actualMarked actualMarked_word blockCertificate
  apply w.eq_zero_of_terminalPacket n L data hn p
  exact traceCertificate.value_eq

end

end LieRings.MetabelianVanishing
