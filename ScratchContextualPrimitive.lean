import LieRings.DimensionSubring.MetabelianVanishing.TerminalCorrection

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance scratchContextualPrimitiveFintype : Fintype L :=
  Fintype.ofFinite L

theorem ProvenancedTerminalTwo.pbwPrimitive_contextualFullRelationWord
    (c : ProvenancedTerminalTwo n L data hn) :
    pbwPrimitive n L data hn
        (contextualFullRelationWord n L data hn
          c.root c.context [c.factor] []) =
      c.primitive n L data hn := by
  let R : FreeModel n L :=
    RelationContext.relation n L data hn c.context c.root
  let P : FreeModel n L :=
    RelationContext.markedPrefix n L data hn c.context c.root c.mark
  let f : FreeModel n L := adaptedBasis n L data hn c.factor
  have hRP : FreeMetabelian.Free.projectPrefix n (by omega) R =
      FreeMetabelian.Free.projectPrefix n (by omega) P := by
    exact RelationContext.projectPrefix_relation_eq_markedPrefix
      n L data hn c.context c.root c.mark c.active
  let top : FreeMetabelian.Piece (Generator L) n :=
    FreeMetabelian.Free.weightProject n (by omega) (R - P)
  have hR : R = P +
      FreeMetabelian.Free.weightIncl n (by omega) top := by
    have htop := sub_eq_weightIncl_top_of_projectPrefix_eq n L R P hRP
    change R - P = FreeMetabelian.Free.weightIncl n (by omega) top at htop
    calc
      R = (R - P) + P := by abel
      _ = FreeMetabelian.Free.weightIncl n (by omega) top + P := by rw [htop]
      _ = _ := add_comm _ _
  have hfull : contextualFullRelationWord n L data hn
        c.root c.context [c.factor] [] =
      UniversalEnvelopingAlgebra.ι ℤ f *
        UniversalEnvelopingAlgebra.ι ℤ R := by
    simp [contextualFullRelationWord, MarkedRow.basisWord,
      LieRings.PBW.basisWord, LieRings.PBW.word, f, R,
      adaptedWeightedBasis]
  have hrow : c.row.value =
      UniversalEnvelopingAlgebra.ι ℤ f *
        UniversalEnvelopingAlgebra.ι ℤ P := by
    simp [ProvenancedTerminalTwo.row, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, f, P, adaptedWeightedBasis]
  change pbwPrimitive n L data hn
      (contextualFullRelationWord n L data hn
        c.root c.context [c.factor] []) =
    pbwPrimitive n L data hn c.row.value
  apply LieRings.PBW.canonicalMap_injective_of_freeModulePBW
    ℤ (FreeModel n L) (AdaptedIndex n L data hn)
    (adaptedWeightedBasis n L data hn).basis
    (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis)
  rw [← factorProj_one_eq_iota_pbwPrimitive n L data hn,
    ← factorProj_one_eq_iota_pbwPrimitive n L data hn,
    hfull, hrow, hR, map_add, mul_add, map_add,
    factorProj_one_mul_iota_weightIncl_top_eq_zero
      n L data hn f top, add_zero]

def provenancedComponentFullLabelWordSeed :
    ProvenancedRow n L data hn → UEA ℤ (FreeModel n L)
  | .marked _ _ _ _ _ => 0
  | .component rho c k left right =>
      if k.val = 1 then
        contextualFullRelationWord n L data hn rho c left right
      else 0

def provenancedTerminalOnePrimitiveSeed' :
    ProvenancedRow n L data hn → FreeModel n L
  | r => match provenancedTerminal? n L data hn r with
    | some (.inl c) => c.fullPrimitive n L data hn
    | _ => 0

def provenancedTerminalTwoPrimitiveSeed' :
    ProvenancedRow n L data hn → FreeModel n L
  | r => match provenancedTerminal? n L data hn r with
    | some (.inr c) => c.primitive n L data hn
    | _ => 0

theorem pbwPrimitive_provenancedFullLabelWord_terminal
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    pbwPrimitive n L data hn
        (provenancedFullLabelWord n L data hn r) =
      pbwPrimitive n L data hn
          (provenancedComponentFullLabelWordSeed n L data hn r) +
        provenancedTerminalOnePrimitiveSeed' n L data hn r +
        provenancedTerminalTwoPrimitiveSeed' n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · by_cases hb : b.val = 1
    · simp [provenancedFullLabelWord,
        provenancedComponentFullLabelWordSeed,
        provenancedTerminalOnePrimitiveSeed',
        provenancedTerminalTwoPrimitiveSeed', provenancedTerminal?, hb]
    · simp [provenancedFullLabelWord,
        provenancedComponentFullLabelWordSeed,
        provenancedTerminalOnePrimitiveSeed',
        provenancedTerminalTwoPrimitiveSeed', provenancedTerminal?, hb]
  · have hfull := RelationContext.relation_eq_markedPrefix_of_active_top
      n L data hn t.context t.root t.mark t.active
    have hmark : t.mark.val ≠ 0 := by
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
    simp [provenancedComponentFullLabelWordSeed,
      provenancedTerminalOnePrimitiveSeed',
      provenancedTerminalTwoPrimitiveSeed', ProvenancedTerminalOne.row,
      provenancedTerminal?, t.active, ProvenancedTerminalOne.fullPrimitive]
  · have hmark : t.mark.val ≠ 0 := by
      intro hzero
      simp [ProvenancedTerminalTwo.row, provenancedExpansion, hzero] at hr
    rw [show provenancedFullLabelWord n L data hn t.row =
        contextualFullRelationWord n L data hn
          t.root t.context [t.factor] [] by
      simp [ProvenancedTerminalTwo.row, provenancedFullLabelWord, hmark]]
    rw [t.pbwPrimitive_contextualFullRelationWord n L data hn]
    simp [provenancedComponentFullLabelWordSeed,
      provenancedTerminalOnePrimitiveSeed',
      provenancedTerminalTwoPrimitiveSeed', ProvenancedTerminalTwo.row,
      provenancedTerminal?, t.active]

def GoverningWitness.terminalComponentFullLabelWord {a : L}
    (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.provenancedFrontier n L data hn).sum (fun r z ↦
    z • provenancedComponentFullLabelWordSeed n L data hn r)

private theorem GoverningWitness.sum_terminalOnePrimitiveSeed'_eq
    {a : L} (w : GoverningWitness n L data a) :
    (w.provenancedFrontier n L data hn).sum (fun r z ↦
        z • provenancedTerminalOnePrimitiveSeed' n L data hn r) =
      w.terminalOnePrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalOnePrimitive,
    GoverningWitness.provenancedTerminalOne,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [provenancedTerminalOnePrimitiveSeed',
      provenancedTerminalOnePart, hc]
  | some t =>
      cases t with
      | inl c => simp [provenancedTerminalOnePrimitiveSeed',
          provenancedTerminalOnePart, hc]
      | inr c => simp [provenancedTerminalOnePrimitiveSeed',
          provenancedTerminalOnePart, hc]

private theorem GoverningWitness.sum_terminalTwoPrimitiveSeed'_eq
    {a : L} (w : GoverningWitness n L data a) :
    (w.provenancedFrontier n L data hn).sum (fun r z ↦
        z • provenancedTerminalTwoPrimitiveSeed' n L data hn r) =
      w.terminalTwoPrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalTwoPrimitive,
    GoverningWitness.provenancedTerminalTwo,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [provenancedTerminalTwoPrimitiveSeed',
      provenancedTerminalTwoPart, hc]
  | some t =>
      cases t with
      | inl c => simp [provenancedTerminalTwoPrimitiveSeed',
          provenancedTerminalTwoPart, hc]
      | inr c => simp [provenancedTerminalTwoPrimitiveSeed',
          provenancedTerminalTwoPart, hc]

theorem GoverningWitness.pbwPrimitive_terminalComponentFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn
        (w.terminalComponentFullLabelWord n L data hn) =
      w.componentTracePrimitive n L data hn := by
  classical
  have hfull := congrArg (pbwPrimitive n L data hn)
    (w.evaluateFullLabel_provenancedFrontier n L data hn)
  change pbwPrimitive n L data hn
      ((w.provenancedFrontier n L data hn).sum (fun r z ↦
        z • provenancedFullLabelWord n L data hn r)) =
    pbwPrimitive n L data hn w.theta at hfull
  rw [map_finsuppSum] at hfull
  simp only [map_zsmul] at hfull
  have hdecomp :
      (w.provenancedFrontier n L data hn).sum (fun r z ↦
          z • pbwPrimitive n L data hn
            (provenancedFullLabelWord n L data hn r)) =
        (w.provenancedFrontier n L data hn).sum (fun r z ↦
            z • pbwPrimitive n L data hn
              (provenancedComponentFullLabelWordSeed n L data hn r)) +
          (w.provenancedFrontier n L data hn).sum (fun r z ↦
            z • provenancedTerminalOnePrimitiveSeed' n L data hn r) +
          (w.provenancedFrontier n L data hn).sum (fun r z ↦
            z • provenancedTerminalTwoPrimitiveSeed' n L data hn r) := by
    rw [← Finsupp.sum_add, ← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro r hrSupport
    have hterminal : provenancedExpansion n L data hn r = none := by
      by_contra hnonterminal
      apply Finsupp.mem_support_iff.mp hrSupport
      rw [GoverningWitness.provenancedFrontier, Finsupp.sum_apply]
      apply Finset.sum_eq_zero
      intro s hs
      change (w.provenancedInitial n L data hn s) *
          (provenancedCollector n L data hn).normalForm s r = 0
      rw [(provenancedCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
        s r hnonterminal, mul_zero]
    rw [pbwPrimitive_provenancedFullLabelWord_terminal
      n L data hn r hterminal]
    simp only [smul_add]
  have htheta : pbwPrimitive n L data hn w.theta =
      w.componentTracePrimitive n L data hn +
        w.terminalOnePrimitive n L data hn +
        w.terminalTwoPrimitive n L data hn :=
    w.pbwPrimitive_theta_external n L data hn
  have hcomponent : pbwPrimitive n L data hn
      (w.terminalComponentFullLabelWord n L data hn) =
      (w.provenancedFrontier n L data hn).sum (fun r z ↦
        z • pbwPrimitive n L data hn
          (provenancedComponentFullLabelWordSeed n L data hn r)) := by
    rw [GoverningWitness.terminalComponentFullLabelWord, map_finsuppSum]
    simp only [map_zsmul]
  rw [hdecomp, w.sum_terminalOnePrimitiveSeed'_eq n L data hn,
    w.sum_terminalTwoPrimitiveSeed'_eq n L data hn] at hfull
  rw [htheta] at hfull
  rw [hcomponent]
  apply add_right_cancel
    (b := w.terminalOnePrimitive n L data hn +
      w.terminalTwoPrimitive n L data hn)
  simpa only [add_assoc] using hfull

end

end LieRings.MetabelianVanishing
