import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoTerminalRead
import LieRings.DimensionSubring.MetabelianVanishing.TerminalFullLabel

/-!
# The complete terminal correction

This file closes the last terminal square.  The complete descending-factor
trace and the contextual weight trace are two boundary readings of the same
labelled full-relation ledger.  The cutoff edge of the first is the retained
factor-two edge of the second.  Consequently the genuine full-relation chain
read from the complete factor-two frontier has boundary equal to the
contextual component defect.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalCorrectionFintype : Fintype L := Fintype.ofFinite L

/-- The external whole-relation cutoff edge of the complete factor-two
trace, summed over the actual governing initial frontier. -/
def GoverningWitness.completeFactorTwoCutoffFullLabel {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.quotientWeightInitial n L data).sum (fun r z ↦
    z • completeFactorTwoCutoffFullLabelTrace n L data hn r)

/-- The full-label Stokes formula after summing over the governing initial
frontier. -/
theorem GoverningWitness.completeNormalFullLabel_eq_neg_cutoff
    {a : L} (w : GoverningWitness n L data a) :
    (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • completeNormalFormFullLabelRead n L data hn r) =
      -w.completeFactorTwoCutoffFullLabel n L data hn := by
  classical
  have hzero := w.completeFactorTwoInitialFullLabelRead_eq_zero
    n L data hn
  have hstokes :
      (w.quotientWeightInitial n L data).sum (fun r z ↦
          z • completeFactorTwoFullLabelRead n L data hn r) =
        (w.quotientWeightInitial n L data).sum (fun r z ↦
            z • completeNormalFormFullLabelRead n L data hn r) +
          w.completeFactorTwoCutoffFullLabel n L data hn := by
    rw [GoverningWitness.completeFactorTwoCutoffFullLabel]
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro r hr
    rw [completeFullLabelRead_eq_normalForm_add_cutoff n L data hn r]
    exact smul_add _ _ _
  rw [hzero] at hstokes
  exact eq_neg_of_add_eq_zero_left hstokes.symm

/-! ## The stopped-prefix side of the complete ledger -/

/-- The actual factor-two value of a stopped marked row.  The separate
`completeFactorTwoFullLabelRead` remembers the whole relation; their
difference below is precisely the prefix which has already been exposed by
weight truncation. -/
def completeFactorTwoStoppedTailRead :
    QuotientWeightRow n L data → Sym[ℤ] (Fin 2) (A L n)
  | .ordinary _ => 0
  | r@(.marked _ _ _ _) =>
      if r.factorCount n L = 2 then
        rightSymbol n L data hn 2 n (by omega) (r.value n L data)
      else 0

/-- The omitted prefix on a genuine stopped factor-two row.  It is defined
as the difference between the whole-relation and tail readings; the theorem
`completeFactorTwoStoppedPrefixRead_marked` below unfolds this into the
literal `rowTruncation` word. -/
def completeFactorTwoStoppedPrefixRead :
    QuotientWeightRow n L data → Sym[ℤ] (Fin 2) (A L n)
  | .ordinary _ => 0
  | r@(.marked _ _ _ _) =>
      if r.factorCount n L = 2 then
        completeFactorTwoFullLabelRead n L data hn r -
          rightSymbol n L data hn 2 n (by omega) (r.value n L data)
      else 0

/-- Signed stopped-prefix contribution on the actual complete terminal
frontier. -/
def GoverningWitness.completeFactorTwoStoppedPrefix {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
    z • completeFactorTwoStoppedPrefixRead n L data hn r)

/-- The stopped-prefix definition is the literal prefix word carried by the
row.  This records explicitly that no prefix is being asserted to be a full
relation. -/
theorem completeFactorTwoStoppedPrefixRead_marked
    (left right : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : Fin (n + 2))
    (htwo : left.length + 1 + right.length = 2) :
    completeFactorTwoStoppedPrefixRead n L data hn
        (.marked left rho s right) =
      rightSymbol n L data hn 2 n (by omega)
        (QuotientWeightRow.basisWord n L data left *
          UniversalEnvelopingAlgebra.ι ℤ
            (rowTruncation n L s.val (by omega) (rho : FreeModel n L)) *
          QuotientWeightRow.basisWord n L data right) := by
  simp only [completeFactorTwoStoppedPrefixRead,
    QuotientWeightRow.factorCount, htwo, if_pos,
    completeFactorTwoFullLabelRead,
    completeFactorTwoFullLabelWord, QuotientWeightRow.value]
  have hsplit : (rho : FreeModel n L) =
      rowTail n L s.val (by omega) (rho : FreeModel n L) +
        rowTruncation n L s.val (by omega) (rho : FreeModel n L) := by
    rw [rowTail, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have hword :
      QuotientWeightRow.basisWord n L data left *
          UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
          QuotientWeightRow.basisWord n L data right =
        QuotientWeightRow.basisWord n L data left *
            UniversalEnvelopingAlgebra.ι ℤ
              (rowTail n L s.val (by omega) (rho : FreeModel n L)) *
            QuotientWeightRow.basisWord n L data right +
          QuotientWeightRow.basisWord n L data left *
            UniversalEnvelopingAlgebra.ι ℤ
              (rowTruncation n L s.val (by omega) (rho : FreeModel n L)) *
          QuotientWeightRow.basisWord n L data right := by
    have hiota := congrArg (UniversalEnvelopingAlgebra.ι ℤ) hsplit
    rw [map_add] at hiota
    rw [hiota, mul_add, add_mul]
  have hread := congrArg (rightSymbol n L data hn 2 n (by omega)) hword
  rw [map_add] at hread
  rw [hread]
  abel

/-- On a terminal row, the whole-relation read is the sum of the actual tail
read and its stopped prefix. -/
private theorem completeFactorTwo_terminal_fullLabel_eq_tail_add_prefix
    (r : QuotientWeightRow n L data)
    (hr : completeFactorTwoExpansion n L data r = none) :
    completeFactorTwoFullLabelRead n L data hn r =
      completeFactorTwoStoppedTailRead n L data hn r +
        completeFactorTwoStoppedPrefixRead n L data hn r := by
  cases r with
  | ordinary xs =>
      simp [completeFactorTwoFullLabelRead,
        completeFactorTwoFullLabelWord,
        completeFactorTwoStoppedTailRead,
        completeFactorTwoStoppedPrefixRead]
  | marked left rho s right =>
      have hsmall :=
        (completeFactorTwoExpansion_marked_eq_none_iff
          n L data left right rho s).mp hr
      by_cases htwo : left.length + 1 + right.length = 2
      · simp [completeFactorTwoStoppedTailRead,
          completeFactorTwoStoppedPrefixRead,
          QuotientWeightRow.factorCount, htwo]
      · have hone : left.length + 1 + right.length = 1 := by omega
        have hleft : left = [] := List.length_eq_zero_iff.mp (by omega)
        have hright : right = [] := List.length_eq_zero_iff.mp (by omega)
        subst left
        subst right
        simp only [completeFactorTwoStoppedTailRead,
          completeFactorTwoStoppedPrefixRead,
          QuotientWeightRow.factorCount, List.length_nil, zero_add,
          show (1 : ℕ) ≠ 2 by omega, if_false, zero_add,
          completeFactorTwoFullLabelRead,
          completeFactorTwoFullLabelWord,
          QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_nil, List.prod_nil, one_mul, mul_one]
        unfold rightSymbol
        rw [LinearMap.comp_apply,
          fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2 (by omega),
          map_zero]

/-- The factor-two reading of the complete terminal frontier splits into its
ordinary rows and its stopped marked tails. -/
private theorem GoverningWitness.rightSymbol_completeFrontier_eq_ordinary_add_tail
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega) w.theta =
      w.completeFactorTwoOrdinaryFrontier n L data hn +
        (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
          z • completeFactorTwoStoppedTailRead n L data hn r) := by
  classical
  have heval := w.evaluate_completeFactorTwoFrontier n L data
  have hread := congrArg (rightSymbol n L data hn 2 n (by omega)) heval
  change rightSymbol n L data hn 2 n (by omega)
      ((w.completeFactorTwoFrontier n L data).sum
        (fun r z ↦ z • r.value n L data)) = _ at hread
  rw [map_finsuppSum] at hread
  simp only [map_zsmul] at hread
  rw [← hread]
  rw [GoverningWitness.completeFactorTwoOrdinaryFrontier,
    completeOrdinaryFactorTwoLinear_apply]
  change (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
      z • rightSymbol n L data hn 2 n (by omega) (r.value n L data)) =
    (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
      z • completeOrdinaryFactorTwoSeed n L data hn r) +
    (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
      z • completeFactorTwoStoppedTailRead n L data hn r)
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hrSupport
  have hterminal : completeFactorTwoExpansion n L data r = none := by
    by_contra hnonterminal
    apply Finsupp.mem_support_iff.mp hrSupport
    rw [GoverningWitness.completeFactorTwoFrontier, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    change (w.quotientWeightInitial n L data s) *
        (completeFactorTwoCollector n L data).normalForm s r = 0
    rw [(completeFactorTwoCollector n L data).normalForm_apply_eq_zero_of_nonterminal
      s r hnonterminal, mul_zero]
  cases r with
  | ordinary xs =>
      simp [completeOrdinaryFactorTwoSeed,
        completeFactorTwoStoppedTailRead, QuotientWeightRow.value]
      module
  | marked left rho s right =>
      have hsmall :=
        (completeFactorTwoExpansion_marked_eq_none_iff
          n L data left right rho s).mp hterminal
      by_cases htwo : left.length + 1 + right.length = 2
      · simp [completeOrdinaryFactorTwoSeed,
          completeFactorTwoStoppedTailRead,
          QuotientWeightRow.factorCount, htwo]
        module
      · have hone : left.length + 1 + right.length = 1 := by omega
        have hleft : left = [] := List.length_eq_zero_iff.mp (by omega)
        have hright : right = [] := List.length_eq_zero_iff.mp (by omega)
        subst left
        subst right
        simp only [completeOrdinaryFactorTwoSeed,
          completeFactorTwoStoppedTailRead,
          QuotientWeightRow.factorCount, List.length_nil, zero_add,
          show (1 : ℕ) ≠ 2 by omega, if_false, zero_add,
          QuotientWeightRow.value,
          QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_nil, List.prod_nil, one_mul, mul_one]
        unfold rightSymbol
        rw [LinearMap.comp_apply,
          fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2 (by omega),
          map_zero]
        module

/-- The stopped-prefix form of the complete ledger.  This is the precise
aggregate equality `cutoff = ordinary truncation - stopped prefixes` from the
manuscript. -/
theorem GoverningWitness.completeFactorTwoCutoff_eq_ordinary_sub_stoppedPrefix
    {a : L} (w : GoverningWitness n L data a) :
    w.completeFactorTwoCutoffFullLabel n L data hn =
      w.completeFactorTwoOrdinaryFrontier n L data hn -
        w.completeFactorTwoStoppedPrefix n L data hn := by
  classical
  have hnormal := w.completeNormalFullLabel_eq_neg_cutoff n L data hn
  have hnormalFrontier :
      (w.quotientWeightInitial n L data).sum (fun r z ↦
          z • completeNormalFormFullLabelRead n L data hn r) =
        (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
          z • completeFactorTwoFullLabelRead n L data hn r) := by
    let F : (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ]
        Sym[ℤ] (Fin 2) (A L n) :=
      Finsupp.linearCombination ℤ
        (completeFactorTwoFullLabelRead n L data hn)
    change (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • F ((completeFactorTwoCollector n L data).normalForm r)) =
      F ((w.quotientWeightInitial n L data).sum (fun r z ↦
        z • (completeFactorTwoCollector n L data).normalForm r))
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro r hr
    rw [map_zsmul]
  rw [hnormalFrontier] at hnormal
  have hsplit :
      (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
          z • completeFactorTwoFullLabelRead n L data hn r) =
        (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
            z • completeFactorTwoStoppedTailRead n L data hn r) +
          w.completeFactorTwoStoppedPrefix n L data hn := by
    rw [GoverningWitness.completeFactorTwoStoppedPrefix, ← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro r hrSupport
    have hterminal : completeFactorTwoExpansion n L data r = none := by
      by_contra hnonterminal
      apply Finsupp.mem_support_iff.mp hrSupport
      rw [GoverningWitness.completeFactorTwoFrontier, Finsupp.sum_apply]
      apply Finset.sum_eq_zero
      intro s hs
      change (w.quotientWeightInitial n L data s) *
          (completeFactorTwoCollector n L data).normalForm s r = 0
      rw [(completeFactorTwoCollector n L data).normalForm_apply_eq_zero_of_nonterminal
        s r hnonterminal, mul_zero]
    rw [completeFactorTwo_terminal_fullLabel_eq_tail_add_prefix
      n L data hn r hterminal]
    exact smul_add _ _ _
  rw [hsplit] at hnormal
  have hfront := w.rightSymbol_completeFrontier_eq_ordinary_add_tail
    n L data hn
  rw [rightSymbol_theta_terminal_eq_zero n L data hn w] at hfront
  have hordinary : w.completeFactorTwoOrdinaryFrontier n L data hn =
      -(w.completeFactorTwoFrontier n L data).sum (fun r z ↦
        z • completeFactorTwoStoppedTailRead n L data hn r) :=
    eq_neg_of_add_eq_zero_left hfront.symm
  calc
    w.completeFactorTwoCutoffFullLabel n L data hn =
        -((w.completeFactorTwoFrontier n L data).sum (fun r z ↦
            z • completeFactorTwoStoppedTailRead n L data hn r) +
          w.completeFactorTwoStoppedPrefix n L data hn) := by
            rw [hnormal]
            simp
    _ = -(w.completeFactorTwoFrontier n L data).sum (fun r z ↦
            z • completeFactorTwoStoppedTailRead n L data hn r) -
          w.completeFactorTwoStoppedPrefix n L data hn := by abel
    _ = w.completeFactorTwoOrdinaryFrontier n L data hn -
          w.completeFactorTwoStoppedPrefix n L data hn := by
            rw [← hordinary]

end

end LieRings.MetabelianVanishing
