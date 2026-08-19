import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSubsetChain
import LieRings.DimensionSubring.MetabelianVanishing.TerminalPrefixCoordinate

/-!
# Prefix-and-coordinate endpoint for the exceptional relation-left edge

This is the weakest exact interface needed from the final exceptional comb.
The primitive discrepancy is not required to be a full relation.  Its prefix
must lie in `D_n`; after the canonical Smith-section relation is removed, only
the terminal coordinate of the remaining top homogeneous piece must vanish.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffExceptionalPrefixCoordinateFintype : Fintype L :=
  Fintype.ofFinite L

/-- Primitive discrepancy of a proposed realization of the exceptional
relation-on-the-left factor. -/
def GoverningWitness.rawCutoffExceptionalRelationLeftDiscrepancy
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1) : FreeModel n L :=
  terminalSourcePrimitive n L data hn leftChain -
    w.rawCutoffExceptionalRelationLeftPrimitive n L data hn

/-- Final exceptional consumer in the exact form produced by a grouped PBW
comb: relation membership is needed only below the top weight, and the top
weight is checked by the single cyclic coordinate. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalRelationLeftPrefixCoordinate
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hleftBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 leftChain =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn)
    (hprefix : prLE n L n (by omega)
        (w.rawCutoffExceptionalRelationLeftDiscrepancy
          n L data hn leftChain) ∈ D n L data n (by omega))
    (htop : topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega)
          (w.rawCutoffExceptionalRelationLeftDiscrepancy
              n L data hn leftChain -
            (terminalPrefixRelation n L data hn
              (w.rawCutoffExceptionalRelationLeftDiscrepancy
                n L data hn leftChain) hprefix : FreeModel n L))) = 0) :
    a = 0 := by
  let delta := w.rawCutoffExceptionalRelationLeftDiscrepancy
    n L data hn leftChain
  let error : TopPreimage n L data :=
    terminalPrefixError n L data hn delta hprefix
  apply w.eq_zero_of_rawCutoffExceptionalRelationLeftCoordinate
    n L data hn leftChain error hleftBoundary
  · change terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        (error : FreeModel n L)
    rw [show (error : FreeModel n L) = delta by
      exact terminalPrefixError_coe n L data hn delta hprefix]
    dsimp only [delta,
      GoverningWitness.rawCutoffExceptionalRelationLeftDiscrepancy]
    abel
  · change terminalEval n L data error = 0
    rw [show terminalEval n L data error =
        topCoord n L data
          (FreeMetabelian.Free.weightProject n (by omega)
            (delta - (terminalPrefixRelation n L data hn delta hprefix :
              FreeModel n L))) by
      exact terminalEval_terminalPrefixError n L data hn delta hprefix]
    exact htop

/-- A compact certificate for the grouped exceptional PBW computation.

The computation may keep all of its non-top terms grouped into one genuine
full relation `rho`; only the remaining homogeneous top piece has to be read
in the cyclic coordinate.  In particular, this theorem does not require (and
must not be proved by) declaring the individual PBW descendants of a
relation-context word to be relations. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalRelationLeftNormalForm
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (rho : Relations n L data)
    (top : FreeMetabelian.Piece (Generator L) n)
    (hleftBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 leftChain =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn)
    (hdelta : w.rawCutoffExceptionalRelationLeftDiscrepancy
        n L data hn leftChain =
      (rho : FreeModel n L) +
        FreeMetabelian.Free.weightIncl n (by omega) top)
    (htop : topCoord n L data top = 0) :
    a = 0 := by
  let error : TopPreimage n L data :=
    relationTopPreimage n L data rho + topInclPreimage n L data top
  apply w.eq_zero_of_rawCutoffExceptionalRelationLeftCoordinate
    n L data hn leftChain error hleftBoundary
  · change terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        (error : FreeModel n L)
    change terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn +
        ((rho : FreeModel n L) +
          FreeMetabelian.Free.weightIncl n (by omega) top)
    rw [← hdelta]
    dsimp only [GoverningWitness.rawCutoffExceptionalRelationLeftDiscrepancy]
    abel
  · change terminalEval n L data
      (relationTopPreimage n L data rho + topInclPreimage n L data top) = 0
    rw [map_add, terminalEval_relationTopPreimage]
    change 0 + topCoord n L data top = 0
    rw [htop, add_zero]

/-- Canonical-chain specialization of the grouped normal-form certificate.
The boundary hypothesis disappears because the aggregate exceptional
closed-square construction has already proved it.  This is the exact final
target for the remaining grouped Smith-head ledger. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalCanonicalNormalForm
    {a : L} (w : GoverningWitness n L data a)
    (rho : Relations n L data)
    (top : FreeMetabelian.Piece (Generator L) n)
    (hdelta : w.rawCutoffExceptionalRelationLeftDiscrepancy
        n L data hn
          (w.rawCutoffExceptionalRelationLeftChain n L data hn) =
      (rho : FreeModel n L) +
        FreeMetabelian.Free.weightIncl n (by omega) top)
    (htop : topCoord n L data top = 0) :
    a = 0 := by
  apply w.eq_zero_of_rawCutoffExceptionalRelationLeftNormalForm
    n L data hn
      (w.rawCutoffExceptionalRelationLeftChain n L data hn)
      rho top
  · exact w.dOne_rawCutoffExceptionalRelationLeftChain n L data hn
  · exact hdelta
  · exact htop

/-- Evaluation-level exceptional endpoint.  This is the weakest convenient
form for the manuscript's grouped full-commutator ledger: once the complete
primitive discrepancy evaluates to zero, it canonically defines a terminal
preimage with zero cyclic coordinate. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalRelationLeftEval
    {a : L} (w : GoverningWitness n L data a)
    (leftChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hleftBoundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 leftChain =
      w.rawCutoffExceptionalRelationLeftFactor n L data hn)
    (heval : evaluation n L data
        (w.rawCutoffExceptionalRelationLeftDiscrepancy
          n L data hn leftChain) = 0) :
    a = 0 := by
  let delta := w.rawCutoffExceptionalRelationLeftDiscrepancy
    n L data hn leftChain
  let error : TopPreimage n L data := ⟨delta, by
    change evaluation n L data delta ∈ lowerCentralSeries ℤ L n
    rw [show evaluation n L data delta = 0 by exact heval]
    exact LieSubmodule.zero_mem _⟩
  apply w.eq_zero_of_rawCutoffExceptionalRelationLeftCoordinate
    n L data hn leftChain error hleftBoundary
  · change terminalSourcePrimitive n L data hn leftChain =
      w.rawCutoffExceptionalRelationLeftPrimitive n L data hn + delta
    dsimp only [delta,
      GoverningWitness.rawCutoffExceptionalRelationLeftDiscrepancy]
    abel
  · change data.topEquiv.toIntLinearEquiv.toLinearMap
      ⟨evaluation n L data delta, _⟩ = 0
    have hsub :
        (⟨evaluation n L data delta, by
            rw [show evaluation n L data delta = 0 by exact heval]
            exact LieSubmodule.zero_mem _⟩ :
          lowerCentralSeries ℤ L n) = 0 := by
      apply Subtype.ext
      exact heval
    rw [hsub, map_zero]

/-- Canonical-chain form of the evaluation endpoint.  Thus the entire
remaining exceptional calculation has one proposition as its target. -/
theorem GoverningWitness.eq_zero_of_rawCutoffExceptionalCanonicalEval
    {a : L} (w : GoverningWitness n L data a)
    (heval : evaluation n L data
        (w.rawCutoffExceptionalRelationLeftDiscrepancy n L data hn
          (w.rawCutoffExceptionalRelationLeftChain n L data hn)) = 0) :
    a = 0 := by
  exact w.eq_zero_of_rawCutoffExceptionalRelationLeftEval n L data hn
    (w.rawCutoffExceptionalRelationLeftChain n L data hn)
    (w.dOne_rawCutoffExceptionalRelationLeftChain n L data hn) heval

end

end LieRings.MetabelianVanishing
