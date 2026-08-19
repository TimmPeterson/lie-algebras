import LieRings.DimensionSubring.MetabelianVanishing.TerminalCorrection
import LieRings.DimensionSubring.MetabelianVanishing.TerminalRealization

/-!
# Capstone for the PBW/Koszul assembly

This module contains only the final, narrow assembly.  The two hypotheses of
the conditional theorem below are exactly the boundary and primitive outputs
of the complete full-relation calculation; source-to-Smith realization is
already unconditional.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance stepSevenFintype : Fintype L := Fintype.ofFinite L

/-! ## The manuscript's terminal source coordinate -/

/-- The full relation by which the raw Smith block realizes the primitive of
a genuine cycle in the terminal source presentation. -/
noncomputable def terminalSourceCycleRelation
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1) :
    Relations n L data :=
  Classical.choose
    (terminalMappedBlockPrimitive_eq_source_add_relation
      n L data hn c)

theorem terminalSourceCycleRelation_spec
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1) :
    pbwPrimitive n L data hn
        (terminalBlockCanonicalRawMarkedWord n L data hn
          (Koszul.PresentationHomology.cyclesMap
            (terminalSourcePresentation n L data hn)
            (rPresentation n L data (by omega))
            (terminalComparisonHom n L data hn) 1 c)).word =
      terminalSourcePrimitive n L data hn c.1 +
        (terminalSourceCycleRelation n L data hn c : FreeModel n L) :=
  Classical.choose_spec
    (terminalMappedBlockPrimitive_eq_source_add_relation
      n L data hn c)

/-- The terminal source primitive of a genuine cycle, equipped with its
lower-central membership.  It is obtained from the raw Smith block primitive
by subtracting the one full realization relation. -/
noncomputable def terminalSourceCyclePreimage
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1) :
    TopPreimage n L data :=
  (terminalBlockCanonicalRawMarkedWord n L data hn
      (Koszul.PresentationHomology.cyclesMap
        (terminalSourcePresentation n L data hn)
        (rPresentation n L data (by omega))
        (terminalComparisonHom n L data hn) 1 c)).primitive -
    relationTopPreimage n L data
      (terminalSourceCycleRelation n L data hn c)

@[simp] theorem terminalSourceCyclePreimage_coe
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1) :
    (terminalSourceCyclePreimage n L data hn c : FreeModel n L) =
      terminalSourcePrimitive n L data hn c.1 := by
  let blockCycle := Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega))
    (terminalComparisonHom n L data hn) 1 c
  let raw := terminalBlockCanonicalRawMarkedWord
    n L data hn blockCycle
  have hraw : (raw.primitive : FreeModel n L) =
      pbwPrimitive n L data hn raw.word := by
    apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
      ℤ (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis
      (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
        (adaptedWeightedBasis n L data hn).basis)
    rw [← raw.projection_eq,
      ← factorProj_one_eq_iota_pbwPrimitive n L data hn]
  change (raw.primitive : FreeModel n L) -
      (terminalSourceCycleRelation n L data hn c : FreeModel n L) =
    terminalSourcePrimitive n L data hn c.1
  rw [hraw, terminalSourceCycleRelation_spec n L data hn c]
  abel

/-- Point 6 kills the terminal coordinate of every genuine source cycle.
Both discrepancies introduced by passing to the canonical Smith block are
full relations and hence have zero terminal evaluation. -/
theorem terminalEval_terminalSourceCyclePreimage_eq_zero
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1) :
    terminalEval n L data (terminalSourceCyclePreimage n L data hn c) = 0 := by
  let blockCycle := Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega))
    (terminalComparisonHom n L data hn) 1 c
  change terminalEval n L data
      (((quadraticBlockMarkedWord n L data hn blockCycle).primitive -
          relationTopPreimage n L data
            (terminalBlockPlacementCorrection n L data hn blockCycle)) -
        relationTopPreimage n L data
          (terminalSourceCycleRelation n L data hn c)) = 0
  rw [map_sub, map_sub, terminalEval_relationTopPreimage,
    terminalEval_relationTopPreimage, sub_zero, sub_zero]
  exact quadraticBlockValue_eq_zero n L data hn blockCycle

/-- The terminal coordinate of a realized source primitive depends only on
its Koszul boundary.  Indeed, the difference of two chains with the same
boundary is a genuine source cycle, and Point 6 kills the coordinate of its
canonical full-relation realization.  This is the precise independence
statement needed when the marked collector and the Smith collector provide
different, but boundary-equivalent, continuations. -/
theorem terminalEval_sourcePrimitive_eq_of_dOne_eq
    (x y : Koszul.One (terminalSourcePresentation n L data hn) 1)
    (hx hy : TopPreimage n L data)
    (hxeq : (hx : FreeModel n L) =
      terminalSourcePrimitive n L data hn x)
    (hyeq : (hy : FreeModel n L) =
      terminalSourcePrimitive n L data hn y)
    (hboundary : Koszul.dOne
      (terminalSourcePresentation n L data hn) 1 x =
        Koszul.dOne (terminalSourcePresentation n L data hn) 1 y) :
    terminalEval n L data hx = terminalEval n L data hy := by
  let c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1 :=
    ⟨x - y, by
      change Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (x - y) = 0
      rw [map_sub, hboundary, sub_self]⟩
  have hpreimage : hx - hy = terminalSourceCyclePreimage n L data hn c := by
    apply Subtype.ext
    rw [terminalSourceCyclePreimage_coe]
    change (hx : FreeModel n L) - (hy : FreeModel n L) =
      terminalSourcePrimitive n L data hn (x - y)
    rw [hxeq, hyeq, map_sub]
  have hzero : terminalEval n L data (hx - hy) = 0 := by
    rw [hpreimage]
    exact terminalEval_terminalSourceCyclePreimage_eq_zero n L data hn c
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- Cycle-agnostic terminal-coordinate conclusion.  The cycle may be any
genuine cycle in the manuscript's terminal source presentation; the only
input is that its realized source primitive has the external coordinate. -/
theorem GoverningWitness.eq_zero_of_terminalCycleSourceValue
    {a : L} (w : GoverningWitness n L data a)
    (c : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (hvalue : terminalEval n L data
        (terminalSourceCyclePreimage n L data hn c) =
      (w.externalMarkedWord n L data hn).value) :
    a = 0 := by
  have hext : (w.externalMarkedWord n L data hn).value = 0 :=
    hvalue.symm.trans
      (terminalEval_terminalSourceCyclePreimage_eq_zero n L data hn c)
  have hcoord : data.topEquiv ⟨a, by
      rw [← w.evaluates]
      change evaluation n L data
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
          lowerCentralSeries ℤ L n
      rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
      change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl
            (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
      rw [FreeMetabelian.Evaluation.linear_incl]
      cases n with
      | zero => simp
      | succ t =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ = 0 := by
    rw [← w.externalMarkedWord_value n L data hn]
    exact hext
  have hsub : (⟨a, by
      rw [← w.evaluates]
      change evaluation n L data
        (FreeMetabelian.Free.weightIncl n (by omega) w.atilde) ∈
          lowerCentralSeries ℤ L n
      rw [evaluation, FreeMetabelian.Evaluation.canonicalEvaluation]
      change FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) (n + 1)
          (FreeMetabelian.Free.incl
            (⟨n, by omega⟩ : Fin (n + 1)) w.atilde) ∈ _
      rw [FreeMetabelian.Evaluation.linear_incl]
      cases n with
      | zero => simp
      | succ t =>
          exact FreeMetabelian.Evaluation.componentEval_mem_lowerCentralSeries
            data.metabelian
            (FreeMetabelian.Evaluation.canonicalGeneratorMap L) t w.atilde⟩ :
        lowerCentralSeries ℤ L n) = 0 := by
    exact data.topEquiv.injective
      (hcoord.trans data.topEquiv.toAddMonoidHom.map_zero.symm)
  exact congrArg Subtype.val hsub

/-- Final assembly from the two exact outputs of the complete factor-two
calculation.  In particular the correction has the positive orientation. -/
theorem GoverningWitness.eq_zero_of_completeFactorTwoCorrection
    {a : L} (w : GoverningWitness n L data a)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1
          (w.completeFactorTwoChain n L data hn) =
        w.terminalFactorDefect n L data hn)
    (correctionRelation : Relations n L data)
    (hprimitive : terminalSourcePrimitive n L data hn
        (w.completeFactorTwoChain n L data hn) =
      w.componentTracePrimitive n L data hn +
        (correctionRelation : FreeModel n L)) :
    a = 0 := by
  let cycle := w.contextualTerminalCycleWithCorrection
    n L data hn (w.completeFactorTwoChain n L data hn) hboundary
  obtain ⟨realizationRelation, hrealization⟩ :=
    terminalMappedBlockPrimitive_eq_source_add_relation
      n L data hn cycle
  apply w.eq_zero_of_contextualCorrection n L data hn
    (w.completeFactorTwoChain n L data hn) hboundary
    (w.terminalSourcePlacementRelation n L data hn)
    correctionRelation realizationRelation
    (w.terminalSourcePrimitive_contextualTerminalChain n L data hn)
    hprimitive
  simpa only [cycle,
    GoverningWitness.contextualTerminalCycleWithCorrection_val] using
      hrealization

/-! ## Coordinate-level corrected-cycle consumer

The manuscript kills the intermediate PBW/transgression contribution only
after applying the terminal cyclic coordinate.  It need not, and in general
cannot, be promoted to a full relation.  The following is therefore the
correct weak interface for the final row calculation. -/

/-- A correction whose source primitive is the contextual component
primitive plus a top-layer error of zero terminal coordinate closes Step 7.
The error is a `TopPreimage`, rather than an element of `Relations`; this is
exactly the output supplied by the intermediate `Phi = T ∘ d` calculation. -/
theorem GoverningWitness.eq_zero_of_contextualCorrectionCoordinate
    {a : L} (w : GoverningWitness n L data a)
    (correction : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (hboundary : Koszul.dOne
        (terminalSourcePresentation n L data hn) 1 correction =
      w.terminalFactorDefect n L data hn)
    (error : TopPreimage n L data)
    (hprimitive : terminalSourcePrimitive n L data hn correction =
      w.componentTracePrimitive n L data hn +
        (error : FreeModel n L))
    (herror : terminalEval n L data error = 0) :
    a = 0 := by
  let cycle := w.contextualTerminalCycleWithCorrection
    n L data hn correction hboundary
  apply w.eq_zero_of_terminalCycleSourceValue n L data hn cycle
  have hpreimage : terminalSourceCyclePreimage n L data hn cycle =
      w.externalPrimitivePreimage n L data hn +
        relationTopPreimage n L data
          (w.terminalSourcePlacementRelation n L data hn) +
        error := by
    apply Subtype.ext
    rw [terminalSourceCyclePreimage_coe]
    change terminalSourcePrimitive n L data hn
        (w.contextualTerminalChain n L data hn + correction) = _
    rw [map_add,
      w.terminalSourcePrimitive_contextualTerminalChain n L data hn,
      hprimitive]
    change w.terminalTwoPrimitive n L data hn +
          (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) +
        (w.componentTracePrimitive n L data hn + (error : FreeModel n L)) =
      (w.externalPrimitivePreimage n L data hn : FreeModel n L) +
        (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) +
        (error : FreeModel n L)
    rw [w.externalPrimitivePreimage_eq n L data hn]
    abel
  rw [hpreimage, map_add, map_add,
    terminalEval_relationTopPreimage, herror, add_zero, add_zero]
  exact (w.terminalEval_externalPrimitivePreimage n L data hn).trans
    (w.externalMarkedWord_value n L data hn).symm

end

end LieRings.MetabelianVanishing
