import LieRings.DimensionSubring.DegreeFive.FinitePlacedInput

/-!
# Finite presentation witnesses for the degree-five calculation

The Smith collector only needs finitely many free generators.  This file isolates the exact
finite datum it consumes.  The target Lie ring is arbitrary: only the free generating type is
finite.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "Packet" => FiniteSmithPlacedPacket X L

/-- A finite free-presentation witness for one element of the fifth dimension subring.

`relationWords` is already expressed as defining relations followed by words in the chosen
finite generators.  This is exactly the input format of `finiteInitialRelationWordCoefficients`.
-/
structure FinitePresentationDimensionFiveWitness
    (evaluation : LieHom ℤ F L) (a : L) where
  lieLift : F
  highWord : UEA ℤ F
  evaluates : evaluation lieLift = a
  lieLift_mem_gammaThree : lieLift ∈ lowerCentralSeries ℤ F 2
  highWord_mem : highWord ∈ UEA.augmentationIdeal ℤ F ^ 5
  relationWords :
    (LinearMap.ker evaluation.toLinearMap × List X) →₀ ℤ
  relationEquation :
    relationWords.sum (fun p n ↦ n •
      (UniversalEnvelopingAlgebra.ι ℤ (p.1 : F) *
        envelopingWord ℤ F (p.2.map (FreeLieAlgebra.of ℤ)))) =
      UniversalEnvelopingAlgebra.ι ℤ lieLift - highWord

namespace FinitePresentationDimensionFiveWitness

variable {X L}
variable {evaluation : LieHom ℤ (FreeLieAlgebra ℤ X) L} {a : L}

/-- Expand every finite relation word into Smith-row packets. -/
def initialPackets
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    FiniteSmithPlacedPacket X L evaluation →₀ ℤ :=
  w.relationWords.sum (fun p n ↦ n •
    finiteInitialRelationWordCoefficients X L evaluation p.1 p.2)

/-- Completely normalize all packets while retaining the distinguished relation mark. -/
def terminalPackets
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    FiniteSmithPlacedPacket X L evaluation →₀ ℤ :=
  finitePlacedCollect X L evaluation w.initialPackets

/-- The initial Smith packet family is exactly the original relation side. -/
theorem initialPackets_value
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    (finitePlacedPacketCollector X L evaluation).evaluate w.initialPackets =
      UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord := by
  unfold initialPackets
  rw [map_finsuppSum]
  calc
    _ = w.relationWords.sum (fun p n ↦ n •
        (UniversalEnvelopingAlgebra.ι ℤ (p.1 : FreeLieAlgebra ℤ X) *
          envelopingWord ℤ (FreeLieAlgebra ℤ X)
            (p.2.map (FreeLieAlgebra.of ℤ)))) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [map_zsmul]
      congr 1
      exact finiteInitialRelationWordCoefficients_value X L evaluation p.1 p.2
    _ = _ := w.relationEquation

/-- Exact value of the completely normalized terminal ledger. -/
theorem terminalPackets_value
    (w : FinitePresentationDimensionFiveWitness X L evaluation a) :
    (finitePlacedPacketCollector X L evaluation).evaluate w.terminalPackets =
      UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord := by
  rw [terminalPackets, finitePlacedCollect_value, w.initialPackets_value]

/-- Every packet in the final finite ledger is terminal for the deterministic placed rewrite. -/
theorem terminalPackets_terminal
    (w : FinitePresentationDimensionFiveWitness X L evaluation a)
    (p : FiniteSmithPlacedPacket X L evaluation)
    (hp : p ∈ w.terminalPackets.support) :
    finitePlacedPacketExpansion X L evaluation p = none := by
  exact finitePlacedPacketExpansion_eq_none_of_mem_finitePlacedCollect_support
    X L evaluation w.initialPackets p hp

end FinitePresentationDimensionFiveWitness

end

end DegreeFive

end LieRings
