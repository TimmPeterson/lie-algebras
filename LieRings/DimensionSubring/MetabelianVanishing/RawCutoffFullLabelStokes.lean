import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffComponentNormalization
import LieRings.DimensionSubring.MetabelianVanishing.TerminalFullLabel

/-!
# Full-label Stokes account for the raw complete cutoff

The raw cutoff starts with genuine top-marked relations.  This file records
the two aggregate consequences of running the contextual trace: its ordinary
component factor-two read is the same signed read as the terminal mark-one
whole-relation labels, and the remaining terminal factor-two labels are the
boundary of the literal contextual source chain.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffFullLabelStokesFintype : Fintype L :=
  Fintype.ofFinite L

private theorem rawProvenancedPart_fullLabel_value_marked
    (left : List (AdaptedIndex n L data hn))
    (rho : Relations n L data) (mark : Fin (n + 2))
    (right : List (AdaptedIndex n L data hn))
    (hmark : mark.val = n + 1) :
    (provenancedFullLabelCollector n L data hn).evaluate
        (rawProvenancedPart n L data hn
          (.marked left rho mark right)) =
      MarkedRow.value n L data hn (.marked left rho mark right) := by
  rw [rawProvenancedPart,
    LieRings.DegreeFive.FiniteTaggedCollector.evaluate_single, one_smul]
  have hmarkFin : mark = ⟨n + 1, by omega⟩ := Fin.ext hmark
  rw [hmarkFin]
  change provenancedFullLabelWord n L data hn
      (.marked rho .hole ⟨n + 1, by omega⟩ left right) = _
  simp [provenancedFullLabelWord, contextualFullRelationWord,
    MarkedRow.value, RelationContext.relation, rowTruncation_top]

/-- The whole-relation read of the raw contextual roots is their literal raw
cutoff word. -/
theorem GoverningWitness.evaluateFullLabel_rawCutoffProvenancedInitial
    {a : L} (w : GoverningWitness n L data a) :
    (provenancedFullLabelCollector n L data hn).evaluate
        (w.rawCutoffProvenancedInitial n L data hn) =
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedInitial, map_finsuppSum]
  calc
    _ = markedRowEvaluation n L data hn
        (w.rawCutoffFullLabelFrontier n L data hn) := by
      apply Finsupp.sum_congr
      intro r hr
      have hshape := w.rawCutoffFullLabelFrontier_shape_of_ne
        n L data hn r (Finsupp.mem_support_iff.mp hr)
      cases r with
      | ordinary word => exact hshape.elim
      | marked left rho mark right =>
          rw [map_zsmul,
            rawProvenancedPart_fullLabel_value_marked
              n L data hn left rho mark right hshape.1]
          rfl
    _ = _ := w.rawCutoffFullLabelFrontier_evaluation n L data hn

/-- Full-label evaluation is preserved by the whole raw contextual trace. -/
theorem GoverningWitness.evaluateFullLabel_rawCutoffProvenancedFrontier
    {a : L} (w : GoverningWitness n L data a) :
    (provenancedFullLabelCollector n L data hn).evaluate
        (w.rawCutoffProvenancedFrontier n L data hn) =
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [GoverningWitness.rawCutoffProvenancedFrontier, map_finsuppSum]
  calc
    _ = (provenancedFullLabelCollector n L data hn).evaluate
        (w.rawCutoffProvenancedInitial n L data hn) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul, provenancedFullLabelCollector_evaluate]
      rfl
    _ = _ := w.evaluateFullLabel_rawCutoffProvenancedInitial
      n L data hn

/-- Exact factor-two full-label read of the terminal raw contextual
frontier. -/
theorem GoverningWitness.rightSymbol_fullLabel_rawCutoffProvenancedFrontier
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • provenancedFullLabelRead n L data hn r) =
      rightSymbol n L data hn 2 n (by omega)
        (w.rawCompleteCutoffWord n L data) := by
  have h := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.evaluateFullLabel_rawCutoffProvenancedFrontier n L data hn)
  change rightSymbol n L data hn 2 n (by omega)
      ((w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • provenancedFullLabelWord n L data hn r)) = _ at h
  rw [map_finsuppSum] at h
  simpa only [map_zsmul, provenancedFullLabelRead] using h

/-- Terminal mark-one component labels in the raw cutoff frontier. -/
def GoverningWitness.rawCutoffTerminalComponentFullLabel
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum
    (fun r z ↦ z • provenancedComponentFullLabelSeed n L data hn r)

/-- Terminal factor-two whole-relation labels in the raw cutoff frontier. -/
def GoverningWitness.rawCutoffTerminalTwoFullLabel
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum
    (fun r z ↦ z • terminalTwoFullLabelSeed n L data hn r)

private theorem GoverningWitness.rawCutoffProvenancedFrontier_terminal_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (r : ProvenancedRow n L data hn)
    (hr : w.rawCutoffProvenancedFrontier n L data hn r ≠ 0) :
    provenancedExpansion n L data hn r = none := by
  by_contra hnonterminal
  apply hr
  rw [GoverningWitness.rawCutoffProvenancedFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro s hs
  change w.rawCutoffProvenancedInitial n L data hn s *
      (provenancedCollector n L data hn).normalForm s r = 0
  rw [(provenancedCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
    s r hnonterminal, mul_zero]

/-- The terminal whole-label read has exactly its component and placed
factor-two parts. -/
theorem GoverningWitness.rawCutoffFullLabel_terminal_decomposition
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • provenancedFullLabelRead n L data hn r) =
      w.rawCutoffTerminalComponentFullLabel n L data hn +
        w.rawCutoffTerminalTwoFullLabel n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffTerminalComponentFullLabel,
    GoverningWitness.rawCutoffTerminalTwoFullLabel]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hterminal := w.rawCutoffProvenancedFrontier_terminal_of_ne
    n L data hn r (Finsupp.mem_support_iff.mp hr)
  change w.rawCutoffProvenancedFrontier n L data hn r •
      provenancedFullLabelRead n L data hn r =
    w.rawCutoffProvenancedFrontier n L data hn r •
        provenancedComponentFullLabelSeed n L data hn r +
      w.rawCutoffProvenancedFrontier n L data hn r •
        terminalTwoFullLabelSeed n L data hn r
  rw [fullLabelRead_terminal_decomposition n L data hn r hterminal,
    zsmul_add]

/-- The mark-one whole-relation labels recorded by all raw truncation cells. -/
def GoverningWitness.rawCutoffTraceMarkOneFullLabel
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum
    (fun c z ↦ z • c.markOneFullLabelRead n L data hn)

/-- Aggregate full-label Stokes identity for the raw cutoff.  Since every
raw root is marked, there is no component seed at the root: the terminal
mark-one component labels are exactly the labels recorded by the trace. -/
theorem GoverningWitness.rawCutoffTerminalComponentFullLabel_eq_trace
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalComponentFullLabel n L data hn =
      w.rawCutoffTraceMarkOneFullLabel n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffTerminalComponentFullLabel,
    GoverningWitness.rawCutoffProvenancedFrontier,
    GoverningWitness.rawCutoffTraceMarkOneFullLabel,
    GoverningWitness.rawCutoffFullProvenancedCells]
  change Finsupp.linearCombination ℤ
      (provenancedComponentFullLabelSeed n L data hn)
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • (provenancedCollector n L data hn).normalForm r)) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.markOneFullLabelRead n L data hn)
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • provenancedTrace n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  change w.rawCutoffProvenancedInitial n L data hn r •
      normalFormProvenancedComponentFullLabelRead n L data hn r =
    w.rawCutoffProvenancedInitial n L data hn r •
      provenancedTraceMarkOneFullLabelRead n L data hn r
  rw [normalFormProvenancedComponentFullLabelRead_eq_trace]
  have hseed : provenancedComponentFullLabelSeed n L data hn r = 0 := by
    cases r with
    | marked => rfl
    | component root context mark left right =>
        exact (Finsupp.mem_support_iff.mp hr
          (w.rawCutoffProvenancedInitial_component
            n L data hn root context mark left right)).elim
  rw [hseed, zero_add]

/-- The placed terminal factor-two whole labels are exactly the boundary of
the genuine raw contextual source chain. -/
theorem GoverningWitness.rawCutoffTerminalTwoFullLabel_eq_dOne
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalTwoFullLabel n L data hn =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffContextualTerminalChain n L data hn) := by
  classical
  rw [w.dOne_rawCutoffContextualTerminalChain n L data hn,
    GoverningWitness.rawCutoffTerminalTwoFullLabel,
    GoverningWitness.rawCutoffProvenancedTerminalTwo]
  change Finsupp.linearCombination ℤ
      (terminalTwoFullLabelSeed n L data hn)
        (w.rawCutoffProvenancedFrontier n L data hn) =
    Finsupp.linearCombination ℤ
      (fun c ↦ rightSymbol n L data hn 2 n (by omega) c.row.value)
      ((w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • provenancedTerminalTwoPart n L data hn r))
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  cases hc : provenancedTerminal? n L data hn r with
  | none =>
      simp [provenancedTerminalTwoPart, terminalTwoFullLabelSeed, hc]
      module
  | some t =>
      cases t with
      | inl c =>
          simp [provenancedTerminalTwoPart, terminalTwoFullLabelSeed, hc]
          module
      | inr c =>
          simp [provenancedTerminalTwoPart, terminalTwoFullLabelSeed, hc]
          module

/-! ## The ordinary factor-two read of the same terminal frontier -/

/-- Terminal component factor-two read before replacing its homogeneous
component by the whole relation which labels the cell. -/
def GoverningWitness.rawCutoffTerminalComponentFactor
    {a : L} (w : GoverningWitness n L data a) :
    Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum
    (fun r z ↦ z • provenancedComponentFactorSeed
      n L data hn 2 n (by omega) r)

private theorem rightSymbol_rawTerminal_decomposition
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    rightSymbol n L data hn 2 n (by omega) r.value =
      provenancedComponentFactorSeed n L data hn 2 n (by omega) r +
        terminalTwoFullLabelSeed n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp [provenancedComponentFactorSeed,
      terminalTwoFullLabelSeed, provenancedTerminal?]
  · change rightSymbol n L data hn 2 n (by omega)
        (ProvenancedTerminalOne.row n L data hn t).value =
      provenancedComponentFactorSeed n L data hn 2 n (by omega)
          (ProvenancedTerminalOne.row n L data hn t) +
        terminalTwoFullLabelSeed n L data hn
          (ProvenancedTerminalOne.row n L data hn t)
    have hcomp : provenancedComponentFactorSeed n L data hn 2 n (by omega)
        (ProvenancedTerminalOne.row n L data hn t) = 0 := rfl
    have hterm : terminalTwoFullLabelSeed n L data hn
        (ProvenancedTerminalOne.row n L data hn t) = 0 := by
      simp [terminalTwoFullLabelSeed, ProvenancedTerminalOne.row,
        provenancedTerminal?, t.active]
    rw [hcomp, hterm, add_zero]
    rw [show (ProvenancedTerminalOne.row n L data hn t).value =
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.markedPrefix n L data hn
            t.context t.root t.mark) by
      simp [ProvenancedTerminalOne.row, ProvenancedRow.value,
        MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word]]
    unfold rightSymbol
    rw [LinearMap.comp_apply,
      fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2 (by omega),
      map_zero]
  · simp [ProvenancedTerminalTwo.row,
      provenancedComponentFactorSeed,
      terminalTwoFullLabelSeed, provenancedTerminal?, t.active]

/-- The ordinary terminal PBW decomposition of the raw cutoff word. -/
theorem GoverningWitness.rightSymbol_rawCutoff_terminal_decomposition
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.rawCompleteCutoffWord n L data) =
      w.rawCutoffTerminalComponentFactor n L data hn +
        w.rawCutoffTerminalTwoFullLabel n L data hn := by
  classical
  have heval := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.evaluate_rawCutoffProvenancedFrontier n L data hn)
  change rightSymbol n L data hn 2 n (by omega)
      ((w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • r.value)) = _ at heval
  rw [map_finsuppSum] at heval
  rw [← heval, GoverningWitness.rawCutoffTerminalComponentFactor,
    GoverningWitness.rawCutoffTerminalTwoFullLabel]
  simp only [map_zsmul]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hterminal := w.rawCutoffProvenancedFrontier_terminal_of_ne
    n L data hn r (Finsupp.mem_support_iff.mp hr)
  change w.rawCutoffProvenancedFrontier n L data hn r •
      rightSymbol n L data hn 2 n (by omega) r.value =
    w.rawCutoffProvenancedFrontier n L data hn r •
        provenancedComponentFactorSeed n L data hn 2 n (by omega) r +
      w.rawCutoffProvenancedFrontier n L data hn r •
        terminalTwoFullLabelSeed n L data hn r
  rw [rightSymbol_rawTerminal_decomposition n L data hn r hterminal,
    zsmul_add]

/-- Component Stokes for the raw trace: terminal homogeneous components and
all component edges in the signed trace have the same factor-two read. -/
theorem GoverningWitness.rawCutoffTerminalComponentFactor_eq_trace
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalComponentFactor n L data hn =
      (w.rawCutoffFullProvenancedCells n L data hn).sum
        (fun c z ↦ z • c.factorEdge n L data hn 2 n (by omega)) := by
  classical
  rw [GoverningWitness.rawCutoffTerminalComponentFactor,
    GoverningWitness.rawCutoffProvenancedFrontier,
    GoverningWitness.rawCutoffFullProvenancedCells]
  change Finsupp.linearCombination ℤ
      (provenancedComponentFactorSeed n L data hn 2 n (by omega))
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • (provenancedCollector n L data hn).normalForm r)) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.factorEdge n L data hn 2 n (by omega))
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • provenancedTrace n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  change w.rawCutoffProvenancedInitial n L data hn r •
      normalFormProvenancedComponentFactor n L data hn 2 n (by omega) r =
    w.rawCutoffProvenancedInitial n L data hn r •
      provenancedTraceFactor n L data hn 2 n (by omega) r
  rw [normalFormProvenancedComponentFactor_eq_trace]
  have hseed : provenancedComponentFactorSeed n L data hn
      2 n (by omega) r = 0 := by
    cases r with
    | marked => rfl
    | component root context mark left right =>
        exact (Finsupp.mem_support_iff.mp hr
          (w.rawCutoffProvenancedInitial_component
            n L data hn root context mark left right)).elim
  rw [hseed, zero_add]

/-- The two aggregate component reads agree.  This is obtained by comparing
the two exact terminal decompositions of the same raw word and cancelling
the common terminal-two wall; no individual truncation cell is equated with
its whole-relation label. -/
theorem GoverningWitness.rawCutoffTerminalComponentFactor_eq_fullLabel
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalComponentFactor n L data hn =
      w.rawCutoffTerminalComponentFullLabel n L data hn := by
  have hord := w.rightSymbol_rawCutoff_terminal_decomposition n L data hn
  have hfull := w.rightSymbol_fullLabel_rawCutoffProvenancedFrontier
    n L data hn
  rw [w.rawCutoffFullLabel_terminal_decomposition n L data hn] at hfull
  exact add_right_cancel (hord.symm.trans hfull.symm)

/-! ## The grouped primitive read -/

private def rawTerminalOnePrimitiveSeed
    (r : ProvenancedRow n L data hn) : FreeModel n L :=
  match provenancedTerminal? n L data hn r with
  | some (.inl c) => c.fullPrimitive n L data hn
  | _ => 0

private def rawTerminalTwoPrimitiveSeed
    (r : ProvenancedRow n L data hn) : FreeModel n L :=
  match provenancedTerminal? n L data hn r with
  | some (.inr c) => c.primitive n L data hn
  | _ => 0

private theorem pbwPrimitive_rawTerminal_decomposition
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    pbwPrimitive n L data hn r.value =
      provenancedComponentPrimitiveSeed n L data hn r +
        rawTerminalOnePrimitiveSeed n L data hn r +
        rawTerminalTwoPrimitiveSeed n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · simp [provenancedComponentPrimitiveSeed,
      rawTerminalOnePrimitiveSeed, rawTerminalTwoPrimitiveSeed,
      provenancedTerminal?]
  · have hfull := RelationContext.relation_eq_markedPrefix_of_active_top
      n L data hn t.context t.root t.mark t.active
    simp only [ProvenancedTerminalOne.row, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word,
      List.map_nil, List.prod_nil, one_mul, mul_one]
    rw [← hfull, pbwPrimitive_iota]
    simp [provenancedComponentPrimitiveSeed,
      rawTerminalOnePrimitiveSeed, rawTerminalTwoPrimitiveSeed,
      provenancedTerminal?, ProvenancedTerminalOne.fullPrimitive, t.active]
  · simp [ProvenancedTerminalTwo.primitive,
      provenancedComponentPrimitiveSeed,
      rawTerminalOnePrimitiveSeed, rawTerminalTwoPrimitiveSeed,
      provenancedTerminal?, ProvenancedTerminalTwo.row, t.active]

/-- Terminal homogeneous-component primitive in the raw frontier. -/
def GoverningWitness.rawCutoffTerminalComponentPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum
    (fun r z ↦ z • provenancedComponentPrimitiveSeed n L data hn r)

/-- All component primitives recorded by the raw truncation trace. -/
def GoverningWitness.rawCutoffTracePrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffFullProvenancedCells n L data hn).sum
    (fun c z ↦ z • c.primitive n L data hn)

/-- Whole contextual relations at the one-factor wall of the raw trace. -/
def GoverningWitness.rawCutoffTerminalOnePrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffProvenancedTerminalOne n L data hn).sum
    (fun c z ↦ z • c.fullPrimitive n L data hn)

/-- Placed primitives at the factor-two wall of the raw trace. -/
def GoverningWitness.rawFullCutoffTerminalTwoPrimitive
    {a : L} (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffProvenancedTerminalTwo n L data hn).sum
    (fun c z ↦ z • c.primitive n L data hn)

/-- Primitive Stokes for raw component cells. -/
theorem GoverningWitness.rawCutoffTerminalComponentPrimitive_eq_trace
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalComponentPrimitive n L data hn =
      w.rawCutoffTracePrimitive n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffTerminalComponentPrimitive,
    GoverningWitness.rawCutoffProvenancedFrontier,
    GoverningWitness.rawCutoffTracePrimitive,
    GoverningWitness.rawCutoffFullProvenancedCells]
  change Finsupp.linearCombination ℤ
      (provenancedComponentPrimitiveSeed n L data hn)
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • (provenancedCollector n L data hn).normalForm r)) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.primitive n L data hn)
        ((w.rawCutoffProvenancedInitial n L data hn).sum
          (fun r z ↦ z • provenancedTrace n L data hn r))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  change w.rawCutoffProvenancedInitial n L data hn r •
      normalFormProvenancedComponentPrimitive n L data hn r =
    w.rawCutoffProvenancedInitial n L data hn r •
      provenancedTracePrimitive n L data hn r
  rw [normalFormProvenancedComponentPrimitive_eq_trace]
  have hseed : provenancedComponentPrimitiveSeed n L data hn r = 0 := by
    cases r with
    | marked => rfl
    | component root context mark left right =>
        exact (Finsupp.mem_support_iff.mp hr
          (w.rawCutoffProvenancedInitial_component
            n L data hn root context mark left right)).elim
  rw [hseed, zero_add]

private theorem GoverningWitness.rawCutoffTerminalOnePrimitive_eq_seed
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • rawTerminalOnePrimitiveSeed n L data hn r) =
      w.rawCutoffTerminalOnePrimitive n L data hn := by
  classical
  rw [GoverningWitness.rawCutoffTerminalOnePrimitive,
    GoverningWitness.rawCutoffProvenancedTerminalOne,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [rawTerminalOnePrimitiveSeed,
      provenancedTerminalOnePart, hc]
  | some t =>
      cases t with
      | inl c => simp [rawTerminalOnePrimitiveSeed,
          provenancedTerminalOnePart, hc]
      | inr c => simp [rawTerminalOnePrimitiveSeed,
          provenancedTerminalOnePart, hc]

private theorem GoverningWitness.rawCutoffTerminalTwoPrimitive_eq_seed
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • rawTerminalTwoPrimitiveSeed n L data hn r) =
      w.rawFullCutoffTerminalTwoPrimitive n L data hn := by
  classical
  rw [GoverningWitness.rawFullCutoffTerminalTwoPrimitive,
    GoverningWitness.rawCutoffProvenancedTerminalTwo,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [rawTerminalTwoPrimitiveSeed,
      provenancedTerminalTwoPart, hc]
  | some t =>
      cases t with
      | inl c => simp [rawTerminalTwoPrimitiveSeed,
          provenancedTerminalTwoPart, hc]
      | inr c => simp [rawTerminalTwoPrimitiveSeed,
          provenancedTerminalTwoPart, hc]

/-- Exact grouped primitive frontier of the raw cutoff word.  In particular,
one-factor full relations are summed as whole relations before any quotient
or top-coordinate map is applied. -/
theorem GoverningWitness.pbwPrimitive_rawCompleteCutoff_external
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) =
      w.rawCutoffTracePrimitive n L data hn +
        w.rawCutoffTerminalOnePrimitive n L data hn +
        w.rawFullCutoffTerminalTwoPrimitive n L data hn := by
  classical
  have heval := congrArg (pbwPrimitive n L data hn)
    (w.evaluate_rawCutoffProvenancedFrontier n L data hn)
  change pbwPrimitive n L data hn
      ((w.rawCutoffProvenancedFrontier n L data hn).sum
        (fun r z ↦ z • r.value)) = _ at heval
  rw [map_finsuppSum] at heval
  rw [← heval, ← w.rawCutoffTerminalComponentPrimitive_eq_trace
    n L data hn, GoverningWitness.rawCutoffTerminalComponentPrimitive,
    ← w.rawCutoffTerminalOnePrimitive_eq_seed n L data hn,
    ← w.rawCutoffTerminalTwoPrimitive_eq_seed n L data hn]
  simp only [map_zsmul]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hterminal := w.rawCutoffProvenancedFrontier_terminal_of_ne
    n L data hn r (Finsupp.mem_support_iff.mp hr)
  have hdec := pbwPrimitive_rawTerminal_decomposition
    n L data hn r hterminal
  simpa only [smul_add] using congrArg
    (fun x ↦ w.rawCutoffProvenancedFrontier n L data hn r • x) hdec

/-- The grouped raw one-factor wall is an honest sum of full relations. -/
def GoverningWitness.rawFullCutoffTerminalOneRelation
    {a : L} (w : GoverningWitness n L data a) : Relations n L data :=
  (w.rawCutoffProvenancedTerminalOne n L data hn).sum
    (fun c z ↦ z • RelationContext.relation
      n L data hn c.context c.root)

@[simp] theorem GoverningWitness.rawFullCutoffTerminalOneRelation_coe
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawFullCutoffTerminalOneRelation n L data hn : FreeModel n L) =
      w.rawCutoffTerminalOnePrimitive n L data hn := by
  classical
  rw [GoverningWitness.rawFullCutoffTerminalOneRelation,
    GoverningWitness.rawCutoffTerminalOnePrimitive]
  change (Relations n L data).subtype
      ((w.rawCutoffProvenancedTerminalOne n L data hn).sum
        (fun c z ↦ z • RelationContext.relation
          n L data hn c.context c.root)) = _
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul]
  congr 1

end

end LieRings.MetabelianVanishing
