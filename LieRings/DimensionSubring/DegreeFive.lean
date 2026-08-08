import LieRings.DimensionSubring.DegreeFive.Reduction
import LieRings.DimensionSubring.DegreeFive.Exterior
import LieRings.DimensionSubring.DegreeFive.Certificate
import LieRings.DimensionSubring.DegreeFive.FreeClassTwo
import LieRings.DimensionSubring.DegreeFive.FreePresentation
import LieRings.DimensionSubring.DegreeFive.PresentationResolution
import LieRings.DimensionSubring.DegreeFive.RelationTruncation
import LieRings.DimensionSubring.DegreeFive.RelationIdeal
import LieRings.DimensionSubring.DegreeFive.PresentationKernel
import LieRings.DimensionSubring.DegreeFive.Witness
import LieRings.DimensionSubring.DegreeFive.LowWeight
import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneous
import LieRings.DimensionSubring.DegreeFive.FiniteRelationRows
import LieRings.DimensionSubring.DegreeFive.FiniteRelationRowExpansion
import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneousFactors
import LieRings.DimensionSubring.DegreeFive.FiniteRelationCorrections
import LieRings.DimensionSubring.DegreeFive.FinitePlacedPackets
import LieRings.DimensionSubring.DegreeFive.FinitePlacedExpansion
import LieRings.DimensionSubring.DegreeFive.FinitePlacedCollector
import LieRings.DimensionSubring.DegreeFive.FinitePlacedInput
import LieRings.DimensionSubring.DegreeFive.PacketWeights
import LieRings.DimensionSubring.DegreeFive.PacketCollector
import LieRings.DimensionSubring.DegreeFive.PlacedIdentities
import LieRings.DimensionSubring.DegreeFive.FreeClassTwoKernel
import LieRings.DimensionSubring.DegreeFive.LowSymbols
import LieRings.DimensionSubring.DegreeFive.RelationRows
import LieRings.DimensionSubring.DegreeFive.WordExpansion
import LieRings.DimensionSubring.DegreeFive.PlacedLedger
import LieRings.DimensionSubring.DegreeFive.FilteredPackets
import LieRings.DimensionSubring.DegreeFive.SemanticPackets
import LieRings.DimensionSubring.DegreeFive.SemanticCollector
import LieRings.DimensionSubring.DegreeFive.LowSymbolExtraction
import LieRings.DimensionSubring.DegreeFive.FreeClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.WeightedClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.WeightedLedgerExtraction
import LieRings.DimensionSubring.DegreeFive.ExteriorSplit
import LieRings.DimensionSubring.DegreeFive.ExteriorAlternation
import LieRings.DimensionSubring.DegreeFive.ResolutionCycle
import LieRings.DimensionSubring.DegreeFive.SemanticResolutionTensor
import LieRings.DimensionSubring.DegreeFive.QuadraticCoordinates
import LieRings.DimensionSubring.DegreeFive.FinitePlacedResolution
import LieRings.DimensionSubring.DegreeFive.FinitePlacedTerminal
import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis
import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneousClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.CoordinateCertificate
import LieRings.DimensionSubring.DegreeFive.CoordinateSymplectic
import LieRings.DimensionSubring.DegreeFive.CoordinatePBW
import LieRings.DimensionSubring.DegreeFive.CoordinateTheta
import LieRings.DimensionSubring.DegreeFive.AdaptedSmith
import LieRings.DimensionSubring.DegreeFive.AdaptedPresentation
import LieRings.DimensionSubring.DegreeFive.StandingReduction
import LieRings.DimensionSubring.DegreeFive.AdaptedGammaThree
import LieRings.DimensionSubring.DegreeFive.AdaptedCollectorBasis
import LieRings.DimensionSubring.DegreeFive.AdaptedCollectedExpansion
import LieRings.DimensionSubring.DegreeFive.AdaptedCollectedCorrections
import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedPackets
import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedExpansion
import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedCollector
import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedInput
import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedTerminal
import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedWitness
import LieRings.DimensionSubring.DegreeFive.AdaptedTerminalCoordinates
import LieRings.DimensionSubring.DegreeFive.AdaptedCoordinateData
import LieRings.DimensionSubring.DegreeFive.AdaptedIdentities
import LieRings.DimensionSubring.DegreeFive.AdaptedRelationTails
import LieRings.DimensionSubring.DegreeFive.AdaptedWeightedClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.AdaptedPBWBridge
import LieRings.DimensionSubring.DegreeFive.AdaptedTerminalProjection
import LieRings.DimensionSubring.DegreeFive.AdaptedPreThetaBridge
import LieRings.DimensionSubring.DegreeFive.AdaptedWitnessBridge
import LieRings.DimensionSubring.DegreeFive.AdaptedDynkinReduction
import LieRings.DimensionSubring.DegreeFive.GlobalReduction
import LieRings.DimensionSubring.DegreeFive.FiniteWitnessReduction
import LieRings.UniversalEnveloping.Coproduct

/-!
# The fifth Lie dimension subring

This file collects the reduction, canonical-presentation, and quadratic machinery for the
integral theorem `δ₅(L) ⊆ γ₄(L)`. With this library's indexing, `γ₄(L)` is
`lowerCentralSeries ℤ L 3`.

The semantic placed collector is implemented and connected exactly to
`FinitePlacedRelationLedger`. Integral scalar, linear, and weighted PBW symbols are extracted
from its normal form, and the augmentation-five comparison word is proved invisible to them.
The invariant resolution-cycle calculus is complete: integral alternation is injective for every
Abelian group, an ordered quadratic boundary produces a `ResolutionCycleCertificate`, and that
certificate annihilates the represented element.  The coordinate PBW route includes the literal
adapted relation words, the exhaustive low-weight shape table, and the complete construction of
Theta from the pre-Theta ledger.  In particular,
`Coordinate.Data.CollectedExpression.PreThetaEquation.toCoefficientSystem` proves all four
equations `(B)`, `(Z)`, `(C1)`, and `(C2)`; the diagonal square equation `(C2)` is extracted
separately.  `StandingReductionData.terminalPreThetaEquation` now packages the actual terminal
ledger as that equation with no coordinate premise, and `terminalZeta_eq_zero` connects it to
the symplectic certificate theorem.  The remaining global interfaces are the semantic
identification of this terminal `z` projection with the original element's `γ₃` coordinate.
The quotient-theoretic standing reduction is formalized in `GlobalReduction`, and
`FiniteWitnessReduction` proves its finite-support witness property.  Thus its only remaining
external input is the explicitly parameterized inclusion `2δ₄ ⊆ γ₄`.
-/
