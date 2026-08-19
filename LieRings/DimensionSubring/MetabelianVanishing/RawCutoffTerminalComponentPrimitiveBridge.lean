import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge
import LieRings.DimensionSubring.MetabelianVanishing.CompleteCutoffSmith
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffFullLabelStokes

/-!
# Primitive read of the raw terminal component full-label word

This is the raw-cutoff specialization of the full-label terminal
decomposition.  It compares two projections of one literal UEA word and does
not assert that any exposed homogeneous component is itself a relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffTerminalComponentPrimitiveBridgeFintype : Fintype L :=
  Fintype.ofFinite L

private def rawTerminalComponentFullLabelWordSeed :
    ProvenancedRow n L data hn → UEA ℤ (FreeModel n L)
  | .marked _ _ _ _ _ => 0
  | .component rho c k left right =>
      if k.val = 1 then
        contextualFullRelationWord n L data hn rho c left right
      else 0

private def rawTerminalOnePrimitiveSeed :
    ProvenancedRow n L data hn → FreeModel n L
  | r => match provenancedTerminal? n L data hn r with
    | some (.inl c) => c.fullPrimitive n L data hn
    | _ => 0

private def rawTerminalTwoPrimitiveSeed :
    ProvenancedRow n L data hn → FreeModel n L
  | r => match provenancedTerminal? n L data hn r with
    | some (.inr c) => c.primitive n L data hn
    | _ => 0

/-- The literal whole-relation word at the mark-one component wall of the
raw contextual frontier. -/
def GoverningWitness.rawCutoffAggregateTerminalComponentFullLabelWord
    {a : L} (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.rawCutoffProvenancedFrontier n L data hn).sum (fun r z ↦
    z • rawTerminalComponentFullLabelWordSeed n L data hn r)

private theorem pbwPrimitive_rawFullLabelWord_terminal
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    pbwPrimitive n L data hn
        (provenancedFullLabelWord n L data hn r) =
      pbwPrimitive n L data hn
          (rawTerminalComponentFullLabelWordSeed n L data hn r) +
        rawTerminalOnePrimitiveSeed n L data hn r +
        rawTerminalTwoPrimitiveSeed n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · by_cases hb : b.val = 1
    · simp [provenancedFullLabelWord,
        rawTerminalComponentFullLabelWordSeed,
        rawTerminalOnePrimitiveSeed, rawTerminalTwoPrimitiveSeed,
        provenancedTerminal?, hb]
    · simp [provenancedFullLabelWord,
        rawTerminalComponentFullLabelWordSeed,
        rawTerminalOnePrimitiveSeed, rawTerminalTwoPrimitiveSeed,
        provenancedTerminal?, hb]
  · have hmark : t.mark.val ≠ 0 := by
      intro hzero
      simp [ProvenancedTerminalOne.row, provenancedExpansion, hzero] at hr
    have hword : provenancedFullLabelWord n L data hn t.row =
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.relation n L data hn t.context t.root :
            FreeModel n L) := by
      simp [ProvenancedTerminalOne.row, provenancedFullLabelWord,
        hmark, contextualFullRelationWord, MarkedRow.basisWord,
        LieRings.PBW.basisWord, LieRings.PBW.word]
    rw [hword, pbwPrimitive_iota]
    simp [rawTerminalComponentFullLabelWordSeed,
      rawTerminalOnePrimitiveSeed, rawTerminalTwoPrimitiveSeed,
      ProvenancedTerminalOne.row, provenancedTerminal?, t.active,
      ProvenancedTerminalOne.fullPrimitive]
  · have hmark : t.mark.val ≠ 0 := by
      intro hzero
      simp [ProvenancedTerminalTwo.row, provenancedExpansion, hzero] at hr
    rw [show provenancedFullLabelWord n L data hn t.row =
        contextualFullRelationWord n L data hn
          t.root t.context [t.factor] [] by
      simp [ProvenancedTerminalTwo.row, provenancedFullLabelWord, hmark]]
    rw [t.pbwPrimitive_contextualFullRelationWord n L data hn]
    simp [rawTerminalComponentFullLabelWordSeed,
      rawTerminalOnePrimitiveSeed, rawTerminalTwoPrimitiveSeed,
      ProvenancedTerminalTwo.row, provenancedTerminal?, t.active]

private theorem GoverningWitness.rawCutoffFrontier_terminal_of_ne
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

private theorem GoverningWitness.sum_rawTerminalOnePrimitiveSeed
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffProvenancedFrontier n L data hn).sum (fun r z ↦
        z • rawTerminalOnePrimitiveSeed n L data hn r) =
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

private theorem GoverningWitness.sum_rawTerminalTwoPrimitiveSeed
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCutoffProvenancedFrontier n L data hn).sum (fun r z ↦
        z • rawTerminalTwoPrimitiveSeed n L data hn r) =
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

/-- The primitive of the literal aggregate mark-one full-label word is
exactly the primitive of all raw contextual component cells. -/
theorem GoverningWitness.pbwPrimitive_rawCutoffAggregateTerminalComponentFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn
        (w.rawCutoffAggregateTerminalComponentFullLabelWord n L data hn) =
      w.rawCutoffTracePrimitive n L data hn := by
  classical
  let frontier := w.rawCutoffProvenancedFrontier n L data hn
  have hfull := congrArg (pbwPrimitive n L data hn)
    (w.evaluateFullLabel_rawCutoffProvenancedFrontier n L data hn)
  change pbwPrimitive n L data hn
      (frontier.sum (fun r z ↦
        z • provenancedFullLabelWord n L data hn r)) =
    pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) at hfull
  rw [map_finsuppSum] at hfull
  simp only [map_zsmul] at hfull
  have hdecomp :
      frontier.sum (fun r z ↦ z • pbwPrimitive n L data hn
          (provenancedFullLabelWord n L data hn r)) =
        frontier.sum (fun r z ↦ z • pbwPrimitive n L data hn
            (rawTerminalComponentFullLabelWordSeed n L data hn r)) +
          frontier.sum (fun r z ↦
            z • rawTerminalOnePrimitiveSeed n L data hn r) +
          frontier.sum (fun r z ↦
            z • rawTerminalTwoPrimitiveSeed n L data hn r) := by
    rw [← Finsupp.sum_add, ← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro r hr
    rw [pbwPrimitive_rawFullLabelWord_terminal n L data hn r
      (w.rawCutoffFrontier_terminal_of_ne n L data hn r
        (Finsupp.mem_support_iff.mp hr))]
    simp only [smul_add]
  have hraw := w.pbwPrimitive_rawCompleteCutoff_external n L data hn
  have hcomponent : pbwPrimitive n L data hn
      (w.rawCutoffAggregateTerminalComponentFullLabelWord n L data hn) =
      frontier.sum (fun r z ↦ z • pbwPrimitive n L data hn
        (rawTerminalComponentFullLabelWordSeed n L data hn r)) := by
    rw [GoverningWitness.rawCutoffAggregateTerminalComponentFullLabelWord,
      map_finsuppSum]
    simp only [map_zsmul]
    rfl
  rw [hdecomp,
    w.sum_rawTerminalOnePrimitiveSeed n L data hn,
    w.sum_rawTerminalTwoPrimitiveSeed n L data hn] at hfull
  rw [hraw] at hfull
  rw [hcomponent]
  apply add_right_cancel
    (b := w.rawCutoffTerminalOnePrimitive n L data hn +
      w.rawFullCutoffTerminalTwoPrimitive n L data hn)
  simpa only [add_assoc] using hfull

/-- The raw mark-one component word has exactly the evaluation required by
the complete-cutoff consumer.  Comparing the two primitive decompositions of
the same raw word leaves only the difference of the two grouped one-factor
full-relation walls. -/
theorem GoverningWitness.evaluation_rawCutoffAggregateTerminalComponentFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    evaluation n L data
        (pbwPrimitive n L data hn
              (w.rawCutoffAggregateTerminalComponentFullLabelWord
                n L data hn) +
            w.rawFullCutoffTerminalTwoPrimitive n L data hn -
            w.rawCutoffTerminalTwoPrimitive n L data hn -
          w.rawCutoffOrdinaryPrimitive n L data hn) = 0 := by
  have hfull := w.pbwPrimitive_rawCompleteCutoff_external n L data hn
  have hordinary :=
    w.pbwPrimitive_rawCompleteCutoffWord_eq_terminal_reads n L data hn
  have hbalance :
      w.rawCutoffTracePrimitive n L data hn +
          w.rawCutoffTerminalOnePrimitive n L data hn +
        w.rawFullCutoffTerminalTwoPrimitive n L data hn =
      w.rawCutoffOrdinaryPrimitive n L data hn +
          w.rawCutoffTerminalTwoPrimitive n L data hn +
        (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) :=
    hfull.symm.trans hordinary
  have hword :
      pbwPrimitive n L data hn
            (w.rawCutoffAggregateTerminalComponentFullLabelWord
              n L data hn) +
          w.rawFullCutoffTerminalTwoPrimitive n L data hn -
          w.rawCutoffTerminalTwoPrimitive n L data hn -
        w.rawCutoffOrdinaryPrimitive n L data hn =
      (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) -
        (w.rawFullCutoffTerminalOneRelation n L data hn : FreeModel n L) := by
    rw [w.pbwPrimitive_rawCutoffAggregateTerminalComponentFullLabelWord
      n L data hn,
      w.rawFullCutoffTerminalOneRelation_coe n L data hn]
    calc
      _ = (w.rawCutoffTracePrimitive n L data hn +
              w.rawCutoffTerminalOnePrimitive n L data hn +
            w.rawFullCutoffTerminalTwoPrimitive n L data hn) -
          w.rawCutoffTerminalOnePrimitive n L data hn -
          w.rawCutoffTerminalTwoPrimitive n L data hn -
          w.rawCutoffOrdinaryPrimitive n L data hn := by abel
      _ = (w.rawCutoffOrdinaryPrimitive n L data hn +
              w.rawCutoffTerminalTwoPrimitive n L data hn +
            (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L)) -
          w.rawCutoffTerminalOnePrimitive n L data hn -
          w.rawCutoffTerminalTwoPrimitive n L data hn -
          w.rawCutoffOrdinaryPrimitive n L data hn := by rw [hbalance]
      _ = _ := by abel
  have hold : evaluation n L data
      (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) = 0 :=
    (w.rawCutoffTerminalOneRelation n L data hn).property
  have hfullRelation : evaluation n L data
      (w.rawFullCutoffTerminalOneRelation n L data hn : FreeModel n L) = 0 :=
    (w.rawFullCutoffTerminalOneRelation n L data hn).property
  rw [hword, map_sub, hold, hfullRelation, sub_self]

end

end LieRings.MetabelianVanishing
