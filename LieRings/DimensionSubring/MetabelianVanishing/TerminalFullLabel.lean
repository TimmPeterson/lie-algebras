import LieRings.DimensionSubring.MetabelianVanishing.ProvenanceLedger

/-!
# The exact terminal full-label defect

This file identifies the obstruction left by the contextual factor-two wall
with the sum of the genuine full contextual relation labels carried by the
terminal mark-one component leaves.  It does not choose a preimage of that
obstruction: the subsequent relation-preserving PBW collector supplies that
chain explicitly.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian
open TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalFullLabelFintype : Fintype L := Fintype.ofFinite L

private theorem rightSymbol_iota_mul_iota_two_scratch
    (x y : FreeModel n L) :
    rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ x *
          UniversalEnvelopingAlgebra.ι ℤ y) =
      SymmetricPower.insert ℤ (A L n) 1
        (prLE n L n (by omega) x)
        (SymmetricPower.degreeOne (prLE n L n (by omega) y)) := by
  rw [rightSymbol, LinearMap.comp_apply,
    fullRightSymbol_iota_mul_iota_two]
  have hmap := LinearMap.congr_fun
    (SymmetricPower.map_insert (R₀ := ℤ)
      (M₀ := FreeModel n L) (N₀ := A L n)
      (prLE n L n (by omega)) 1 x)
    (SymmetricPower.degreeOne y)
  simpa only [LinearMap.comp_apply, SymmetricPower.map_degreeOne] using hmap

private theorem rightSymbol_iota_mul_iota_two_comm_scratch
    (x y : FreeModel n L) :
    rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ y *
          UniversalEnvelopingAlgebra.ι ℤ x) =
      SymmetricPower.insert ℤ (A L n) 1
        (prLE n L n (by omega) x)
        (SymmetricPower.degreeOne (prLE n L n (by omega) y)) := by
  rw [rightSymbol_iota_mul_iota_two_scratch n L data hn]
  have hcomm := LinearMap.congr_fun
    (SymmetricPower.insert_comm (R₀ := ℤ) (M₀ := A L n) 0
      (prLE n L n (by omega) y)
      (prLE n L n (by omega) x))
    (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))
  have hinsertZero (z : A L n) :
      SymmetricPower.insert ℤ (A L n) 0 z
          (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i)) =
        SymmetricPower.degreeOne z := by
    rw [SymmetricPower.degreeOne_apply, SymmetricPower.insert_tprod]
    congr
    funext i
    exact Fin.elim0 i
  change SymmetricPower.insert ℤ (A L n) 1
      (prLE n L n (by omega) y)
      (SymmetricPower.insert ℤ (A L n) 0
        (prLE n L n (by omega) x)
        (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))) =
    SymmetricPower.insert ℤ (A L n) 1
      (prLE n L n (by omega) x)
      (SymmetricPower.insert ℤ (A L n) 0
        (prLE n L n (by omega) y)
        (SymmetricPower.tprod ℤ (fun i : Fin 0 ↦ Fin.elim0 i))) at hcomm
  rw [hinsertZero, hinsertZero] at hcomm
  exact hcomm

def terminalTwoFullLabelSeed
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  match provenancedTerminal? n L data hn r with
  | some (.inr c) =>
      rightSymbol n L data hn 2 n (by omega) c.row.value
  | _ => 0

theorem fullLabelRead_terminal_decomposition
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    provenancedFullLabelRead n L data hn r =
      provenancedComponentFullLabelSeed n L data hn r +
        terminalTwoFullLabelSeed n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · by_cases hb : b.val = 1 <;>
      simp [provenancedFullLabelRead, provenancedFullLabelWord,
        provenancedComponentFullLabelSeed, terminalTwoFullLabelSeed,
        provenancedTerminal?, hb]
  · by_cases hb : t.mark.val = 0
    · simp [provenancedFullLabelRead, provenancedFullLabelWord,
        ProvenancedTerminalOne.row, provenancedComponentFullLabelSeed,
        terminalTwoFullLabelSeed, provenancedTerminal?, hb]
    · simp only [provenancedFullLabelRead, ProvenancedTerminalOne.row,
        provenancedFullLabelWord, hb, if_false]
      have hword : contextualFullRelationWord n L data hn
          t.root t.context [] [] =
          UniversalEnvelopingAlgebra.ι ℤ
            (RelationContext.relation n L data hn t.context t.root :
              FreeModel n L) := by
        simp [contextualFullRelationWord, MarkedRow.basisWord,
          LieRings.PBW.basisWord, LieRings.PBW.word]
      rw [hword]
      unfold rightSymbol
      rw [LinearMap.comp_apply,
        fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2 (by omega),
        map_zero]
      simp [provenancedComponentFullLabelSeed, terminalTwoFullLabelSeed,
        provenancedTerminal?, t.active]
  · by_cases hb : t.mark.val = 0
    · have hw : RelationContext.weight n L data hn t.context = n := by
        simpa [hb] using t.active
      have hmark : t.mark = ⟨0, by omega⟩ := Fin.ext hb
      have hprefix : RelationContext.markedPrefix n L data hn
          t.context t.root t.mark = 0 := by
        rw [hmark]
        simp only [RelationContext.markedPrefix,
          rowTruncation_zero n L hn, map_zero]
      have hterminal : provenancedTerminal? n L data hn
          (ProvenancedTerminalTwo.row n L data hn t) = some (.inr t) := by
        simp only [ProvenancedTerminalTwo.row, provenancedTerminal?]
        rw [dif_pos t.active]
      simp only [provenancedFullLabelRead, ProvenancedTerminalTwo.row,
        provenancedFullLabelWord, hb, if_pos, map_zero,
        provenancedComponentFullLabelSeed, zero_add]
      change 0 = terminalTwoFullLabelSeed n L data hn t.row
      rw [show terminalTwoFullLabelSeed n L data hn t.row =
          rightSymbol n L data hn 2 n (by omega) t.row.value by
        simp only [terminalTwoFullLabelSeed, hterminal]]
      rw [show t.row.value = 0 by
        simp [ProvenancedTerminalTwo.row, ProvenancedRow.value, hprefix]]
      simp
    · simp only [provenancedFullLabelRead, ProvenancedTerminalTwo.row,
        provenancedFullLabelWord, hb, if_false]
      simp only [provenancedComponentFullLabelSeed]
      have hterminal : provenancedTerminal? n L data hn
          (ProvenancedTerminalTwo.row n L data hn t) = some (.inr t) := by
        simp [ProvenancedTerminalTwo.row, provenancedTerminal?, t.active]
      change rightSymbol n L data hn 2 n (by omega)
          (contextualFullRelationWord n L data hn
            t.root t.context [t.factor] []) =
        0 + terminalTwoFullLabelSeed n L data hn t.row
      have hseed : terminalTwoFullLabelSeed n L data hn t.row =
          rightSymbol n L data hn 2 n (by omega) t.row.value := by
        simp only [terminalTwoFullLabelSeed, hterminal]
      rw [hseed]
      rw [zero_add]
      have hword : contextualFullRelationWord n L data hn
          t.root t.context [t.factor] [] =
          UniversalEnvelopingAlgebra.ι ℤ
              ((adaptedWeightedBasis n L data hn).basis t.factor) *
            UniversalEnvelopingAlgebra.ι ℤ
              (RelationContext.relation n L data hn
                t.context t.root : FreeModel n L) := by
        simp only [contextualFullRelationWord, MarkedRow.basisWord,
          LieRings.PBW.basisWord, LieRings.PBW.word,
          List.map_singleton, List.prod_singleton, List.map_nil,
          List.prod_nil, mul_one]
      rw [hword,
        rightSymbol_iota_mul_iota_two_comm_scratch n L data hn]
      rw [← t.dOne_chain n L data hn,
        ProvenancedTerminalTwo.chain, Koszul.dOne_tmul]
      simp only [fullRelationToD]
      change SymmetricPower.insert ℤ (A L n) 1
          (prLE n L n (by omega)
            (RelationContext.relation n L data hn
              t.context t.root : FreeModel n L))
          (SymmetricPower.degreeOne
            (prLE n L n (by omega)
              (adaptedBasis n L data hn t.factor))) =
        SymmetricPower.insert ℤ (A L n) 1
          (relationPrefix n L data n (by omega)
            (RelationContext.relation n L data hn t.context t.root))
          (SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦
            prLE n L n (by omega) (adaptedBasis n L data hn t.factor)))
      have hrelation : relationPrefix n L data n (by omega)
          (RelationContext.relation n L data hn t.context t.root) =
          prLE n L n (by omega)
            (RelationContext.relation n L data hn
              t.context t.root : FreeModel n L) := rfl
      rw [hrelation]
      have htprod : SymmetricPower.tprod ℤ (fun _ : Fin 1 ↦
            prLE n L n (by omega) (adaptedBasis n L data hn t.factor)) =
          SymmetricPower.degreeOne
            (prLE n L n (by omega)
              (adaptedBasis n L data hn t.factor)) := by
        rw [SymmetricPower.degreeOne_apply]
        congr
        funext i
        fin_cases i
        rfl
      rw [htprod]

def GoverningWitness.terminalComponentFullLabel {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.provenancedFrontier n L data hn).sum
    (fun r z ↦ z • provenancedComponentFullLabelSeed n L data hn r)

def GoverningWitness.terminalTwoFullLabel {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.provenancedFrontier n L data hn).sum
    (fun r z ↦ z • terminalTwoFullLabelSeed n L data hn r)

theorem GoverningWitness.fullLabel_terminal_decomposition {a : L}
    (w : GoverningWitness n L data a) :
    (w.provenancedFrontier n L data hn).sum
        (fun r z ↦ z • provenancedFullLabelRead n L data hn r) =
      w.terminalComponentFullLabel n L data hn +
        w.terminalTwoFullLabel n L data hn := by
  classical
  rw [GoverningWitness.terminalComponentFullLabel,
    GoverningWitness.terminalTwoFullLabel]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hrSupport
  have hterminal : provenancedExpansion n L data hn r = none := by
    by_contra hnonterminal
    apply Finsupp.mem_support_iff.mp hrSupport
    rw [GoverningWitness.provenancedFrontier, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    change (GoverningWitness.provenancedInitial n L data hn w) s *
        (provenancedCollector n L data hn).normalForm s r = 0
    have hz :=
      (provenancedCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
        s r hnonterminal
    rw [hz, mul_zero]
  change (w.provenancedFrontier n L data hn) r •
      provenancedFullLabelRead n L data hn r =
    (w.provenancedFrontier n L data hn) r •
        provenancedComponentFullLabelSeed n L data hn r +
      (w.provenancedFrontier n L data hn) r •
        terminalTwoFullLabelSeed n L data hn r
  rw [fullLabelRead_terminal_decomposition n L data hn r hterminal,
    zsmul_add]

theorem GoverningWitness.terminalTwoFullLabel_eq_dOne_contextualTerminalChain
    {a : L} (w : GoverningWitness n L data a) :
    w.terminalTwoFullLabel n L data hn =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.contextualTerminalChain n L data hn) := by
  classical
  rw [w.dOne_contextualTerminalChain n L data hn,
    GoverningWitness.terminalTwoFullLabel,
    GoverningWitness.provenancedTerminalTwo]
  change Finsupp.linearCombination ℤ
      (terminalTwoFullLabelSeed n L data hn)
        (w.provenancedFrontier n L data hn) =
    Finsupp.linearCombination ℤ
      (fun c ↦ rightSymbol n L data hn 2 n (by omega) c.row.value)
      ((w.provenancedFrontier n L data hn).sum
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

theorem GoverningWitness.terminalComponentFullLabel_eq_defect {a : L}
    (w : GoverningWitness n L data a) :
    w.terminalComponentFullLabel n L data hn =
      w.terminalFactorDefect n L data hn := by
  have hfull := w.rightSymbol_fullLabel_provenancedFrontier n L data hn
  rw [w.fullLabel_terminal_decomposition n L data hn,
    rightSymbol_theta_terminal_eq_zero n L data hn w] at hfull
  have htwo :=
    w.terminalTwoFullLabel_eq_dOne_contextualTerminalChain n L data hn
  rw [w.dOne_contextualTerminalChain_eq_neg_defect n L data hn] at htwo
  rw [htwo] at hfull
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hfull)

theorem GoverningWitness.dOne_contextualTerminalChain_eq_neg_fullLabel
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (w.contextualTerminalChain n L data hn) =
        -w.terminalComponentFullLabel n L data hn := by
  rw [w.dOne_contextualTerminalChain_eq_neg_defect n L data hn,
    w.terminalComponentFullLabel_eq_defect n L data hn]

end

end LieRings.MetabelianVanishing
