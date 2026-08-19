import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoFullLabelStokes
import LieRings.DimensionSubring.MetabelianVanishing.TerminalCertificateBridge

/-!
# Reading the terminal full-label frontier as a Koszul boundary

At a terminal leaf of the complete factor-two collector, the full-label read
vanishes on ordinary rows and on one-factor marked rows.  On a marked
factor-two row it is exactly the boundary of the genuine full-relation
Koszul row retained by `completeFactorTwoPart`.  This file records that local
classification and its aggregate form for the governing frontier.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeFactorTwoTerminalReadFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## The initial whole-label read -/

/-- Forgetting the active quotient bound in an initial second-pass row
recovers the literal full triangular placed row. -/
theorem completeFactorTwoFullLabelWord_quotientWeightRowOfPlaced
    (r : TriangularPlacedRow n L) :
    completeFactorTwoFullLabelWord n L data
        (quotientWeightRowOfPlaced n L data r) =
      TriangularPlacedRow.value n L data r := by
  rfl

/-- The aggregate initial whole-label factor-two read vanishes.  This is
the governing PBW coefficient equation before the quotient-weight Stokes
calculation; no terminal or cutoff term has yet been discarded. -/
theorem GoverningWitness.completeFactorTwoInitialFullLabelRead_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelRead n L data hn r) = 0 := by
  classical
  have hvalue := w.evaluate_triangularPlacedFrontier n L data
  change (w.triangularPlacedFrontier n L data).sum (fun r z ↦
      z • TriangularPlacedRow.value n L data r) = w.theta at hvalue
  have hread := congrArg (rightSymbol n L data hn 2 n (by omega)) hvalue
  rw [map_finsuppSum] at hread
  rw [GoverningWitness.quotientWeightInitial,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  calc
    _ = (w.triangularPlacedFrontier n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelRead n L data hn
          (quotientWeightRowOfPlaced n L data r)) := by
      apply Finsupp.sum_congr
      intro r hr
      simp
    _ = rightSymbol n L data hn 2 n (by omega) w.theta := by
      rw [← hread]
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul]
      congr 1
    _ = 0 := rightSymbol_theta_terminal_eq_zero n L data hn w

/-- Koszul chain contributed by one terminal quotient-weight row. -/
def completeFactorTwoChainPart
    (r : QuotientWeightRow n L data) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (completeFactorTwoPart n L data r).sum
    (fun q z ↦ z • q.one n L data hn)

private def completeFactorTwoBoundaryLinear :
    (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ (fun r ↦
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
      (completeFactorTwoChainPart n L data hn r))

private theorem completeFactorTwoRow_dOne_one
    (r : CompleteFactorTwoRow n L data) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (r.one n L data hn) =
      completeFactorTwoFullLabelRead n L data hn r.1 := by
  rcases r with ⟨r, hr⟩
  cases r with
  | ordinary xs => contradiction
  | marked left rho s right =>
      simp only [QuotientWeightRow.factorCount] at hr
      have hlen : (left ++ right).length = 1 := by
        simp only [List.length_append]
        omega
      rw [CompleteFactorTwoRow.one, Koszul.dOne_tmul]
      change SymmetricPower.insert ℤ (A L n) 1
          (prLE n L n (by omega) (rho : FreeModel n L))
          (SymmetricPower.degreeOne
            (prLE n L n (by omega)
              (triangularPBWBasis n L data
                ((left ++ right).get ⟨0, by rw [hlen]; omega⟩)))) = _
      rcases left with _ | ⟨v, left⟩
      · rcases right with _ | ⟨u, right⟩
        · simp at hlen
        · have hright : right = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.nil_append, List.length_cons] at hlen
            omega
          subst right
          simp only [List.nil_append,
            completeFactorTwoFullLabelRead,
            completeFactorTwoFullLabelWord,
            QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, List.map_nil, List.prod_nil,
            List.map_singleton, List.prod_singleton, one_mul]
          exact (rightSymbol_iota_mul_iota_two n L data hn _ _).symm
      · have hleft : left = [] := by
          simp only [List.length_cons, List.length_append] at hlen
          have : left.length = 0 := by omega
          exact List.length_eq_zero_iff.mp this
        have hright : right = [] := by
          subst left
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons, List.length_nil,
            List.length_append] at hlen
          omega
        subst left
        subst right
        simp only [List.cons_append, List.nil_append,
          completeFactorTwoFullLabelRead,
          completeFactorTwoFullLabelWord,
          QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_nil, List.prod_nil,
          List.map_singleton, List.prod_singleton, mul_one]
        exact (rightSymbol_iota_mul_iota_two_comm n L data hn _ _).symm

/-- At a terminal leaf, the whole-relation factor-two read is precisely the
boundary of the retained genuine Koszul row. -/
theorem dOne_completeFactorTwoChainPart_of_terminal
    (r : QuotientWeightRow n L data)
    (hr : completeFactorTwoExpansion n L data r = none) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (completeFactorTwoChainPart n L data hn r) =
      completeFactorTwoFullLabelRead n L data hn r := by
  classical
  cases r with
  | ordinary xs =>
      simp [completeFactorTwoChainPart, completeFactorTwoPart,
        completeFactorTwoFullLabelRead, completeFactorTwoFullLabelWord]
      rfl
  | marked left rho s right =>
      have hsmall :=
        (completeFactorTwoExpansion_marked_eq_none_iff
          n L data left right rho s).mp hr
      by_cases htwo : left.length + 1 + right.length = 2
      · rw [completeFactorTwoChainPart, completeFactorTwoPart]
        simp only [QuotientWeightRow.factorCount, htwo, ↓reduceDIte]
        rw [Finsupp.sum_single_index]
        · simp only [one_smul]
          simpa using completeFactorTwoRow_dOne_one n L data hn
            ⟨.marked left rho s right,
              by simpa [QuotientWeightRow.factorCount]⟩
        · simp
      · have hone : left.length + 1 + right.length = 1 := by omega
        rw [completeFactorTwoChainPart, completeFactorTwoPart]
        simp only [QuotientWeightRow.factorCount, htwo, ↓reduceDIte,
          map_zero]
        have hleft : left = [] := List.length_eq_zero_iff.mp (by omega)
        have hright : right = [] := List.length_eq_zero_iff.mp (by omega)
        subst left
        subst right
        simp only [completeFactorTwoFullLabelRead,
          completeFactorTwoFullLabelWord,
          QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, List.map_nil, List.prod_nil, one_mul, mul_one]
        unfold rightSymbol
        rw [LinearMap.comp_apply,
          fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2 (by omega),
          map_zero]
        rfl

/-! ## Primitive read of the same terminal leaves -/

/-- Whole-relation discrepancy between the canonical source placement and
the full-label word on a terminal leaf.  The only nonzero cases are a
one-factor relation leaf and a factor-two leaf with the ordinary factor to
the left of the mark. -/
def completeTerminalPrimitiveCorrection :
    QuotientWeightRow n L data → Relations n L data
  | .ordinary _ => 0
  | .marked [] rho _ [] => -rho
  | .marked [] _ _ (_ :: _) => 0
  | .marked (v :: _) rho _ _ =>
      triangularRelationRightBracket n L data rho v

private theorem terminalSourcePrimitive_completeFactorTwoRow_one
    (r : CompleteFactorTwoRow n L data) :
    terminalSourcePrimitive n L data hn (r.one n L data hn) =
      pbwPrimitive n L data hn
        (terminalFullRelationFactorWord n L data
          (r.relation n L data)
          (triangularPBWBasis n L data (r.factor n L data))) := by
  exact terminalSourcePrimitive_fullRelationFactorChain
    n L data hn (r.relation n L data)
      (triangularPBWBasis n L data (r.factor n L data))

/-- Primitive version of the terminal classification.  Every discrepancy is
an actual element of the full relation submodule. -/
theorem terminalSourcePrimitive_completeFactorTwoChainPart_of_terminal
    (r : QuotientWeightRow n L data)
    (hr : completeFactorTwoExpansion n L data r = none) :
    terminalSourcePrimitive n L data hn
        (completeFactorTwoChainPart n L data hn r) =
      pbwPrimitive n L data hn
          (completeFactorTwoFullLabelWord n L data r) +
        (completeTerminalPrimitiveCorrection n L data r : FreeModel n L) := by
  classical
  cases r with
  | ordinary xs =>
      simp [completeFactorTwoChainPart, completeFactorTwoPart,
        completeFactorTwoFullLabelWord,
        completeTerminalPrimitiveCorrection]
  | marked left rho s right =>
      have hsmall :=
        (completeFactorTwoExpansion_marked_eq_none_iff
          n L data left right rho s).mp hr
      rcases left with _ | ⟨v, left⟩
      · rcases right with _ | ⟨u, right⟩
        · have hpart : completeFactorTwoPart n L data
              (.marked [] rho s []) = 0 := by
            simp [completeFactorTwoPart,
              QuotientWeightRow.factorCount]
          have hchain : completeFactorTwoChainPart n L data hn
              (.marked [] rho s []) = 0 := by
            rw [completeFactorTwoChainPart, hpart]
            rfl
          rw [hchain, map_zero]
          rw [show completeFactorTwoFullLabelWord n L data
              (.marked [] rho s []) =
                UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) by
            simp [completeFactorTwoFullLabelWord,
              QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word],
            pbwPrimitive_iota]
          simp [completeTerminalPrimitiveCorrection]
        · have hright : right = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_nil, List.length_cons] at hsmall
            omega
          subst right
          have htwo : ([] : List (TriangularPBWIndex n L)).length + 1 +
              [u].length = 2 := by simp
          rw [completeFactorTwoChainPart, completeFactorTwoPart]
          simp only [QuotientWeightRow.factorCount, htwo, ↓reduceDIte]
          rw [Finsupp.sum_single_index]
          · simp only [one_smul, completeTerminalPrimitiveCorrection,
              map_zero, add_zero]
            rw [terminalSourcePrimitive_completeFactorTwoRow_one
              n L data hn]
            congr 1
            simp [terminalFullRelationFactorWord,
              CompleteFactorTwoRow.relation,
              CompleteFactorTwoRow.factor,
              completeFactorTwoFullLabelWord,
              QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word]
          · simp
      · have hleft : left = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons, List.length_append] at hsmall
          omega
        have hright : right = [] := by
          subst left
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons, List.length_nil,
            List.length_append] at hsmall
          omega
        subst left
        subst right
        have htwo : [v].length + 1 +
            ([] : List (TriangularPBWIndex n L)).length = 2 := by simp
        rw [completeFactorTwoChainPart, completeFactorTwoPart]
        simp only [QuotientWeightRow.factorCount, htwo, ↓reduceDIte]
        rw [Finsupp.sum_single_index]
        · simp only [one_smul, completeTerminalPrimitiveCorrection]
          rw [terminalSourcePrimitive_completeFactorTwoRow_one
            n L data hn]
          let R : FreeModel n L := rho
          let x : FreeModel n L := triangularPBWBasis n L data v
          have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
            (FreeModel n L) R x
          have hprimitive := congrArg (pbwPrimitive n L data hn) hswap
          simp only [map_add, pbwPrimitive_iota] at hprimitive
          simpa [terminalFullRelationFactorWord,
            completeFactorTwoFullLabelWord,
            QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
            LieRings.PBW.word, R, x,
            triangularRelationRightBracket] using hprimitive
        · simp

/-! ## Aggregate primitive read of the complete terminal frontier -/

/-- PBW primitive carried by all whole-relation labels in the complete
factor-two terminal frontier. -/
def GoverningWitness.completeFactorTwoFullLabelPrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
    z • pbwPrimitive n L data hn
      (completeFactorTwoFullLabelWord n L data r))

/-- The sum of the genuine full-relation placement corrections in the
complete factor-two terminal frontier. -/
def GoverningWitness.completeFactorTwoPrimitiveCorrection {a : L}
    (w : GoverningWitness n L data a) : Relations n L data :=
  (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
    z • completeTerminalPrimitiveCorrection n L data r)

/-- Aggregate primitive classification of the manuscript's complete
factor-two chain.  Crucially, the error term is an element of `Relations`,
not a separately projected homogeneous tail. -/
theorem GoverningWitness.terminalSourcePrimitive_completeFactorTwoChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.completeFactorTwoChain n L data hn) =
      w.completeFactorTwoFullLabelPrimitive n L data hn +
        (w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L) := by
  classical
  have hchain : w.completeFactorTwoChain n L data hn =
      (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
        z • completeFactorTwoChainPart n L data hn r) := by
    rw [GoverningWitness.completeFactorTwoChain,
      GoverningWitness.completeFactorTwoRows]
    change Finsupp.linearCombination ℤ
        (fun q : CompleteFactorTwoRow n L data ↦ q.one n L data hn)
        ((w.completeFactorTwoFrontier n L data).sum (fun r z ↦
          z • completeFactorTwoPart n L data r)) = _
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro r hr
    rw [map_zsmul]
    rfl
  rw [hchain, map_finsuppSum,
    GoverningWitness.completeFactorTwoFullLabelPrimitive,
    GoverningWitness.completeFactorTwoPrimitiveCorrection]
  simp_rw [map_zsmul]
  change (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
      z • terminalSourcePrimitive n L data hn
        (completeFactorTwoChainPart n L data hn r)) =
    (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
        z • pbwPrimitive n L data hn
          (completeFactorTwoFullLabelWord n L data r)) +
      (Relations n L data).subtype
        ((w.completeFactorTwoFrontier n L data).sum (fun r z ↦
          z • completeTerminalPrimitiveCorrection n L data r))
  rw [map_finsuppSum, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  change (w.completeFactorTwoFrontier n L data r) •
      terminalSourcePrimitive n L data hn
        (completeFactorTwoChainPart n L data hn r) =
    (w.completeFactorTwoFrontier n L data r) •
        pbwPrimitive n L data hn
          (completeFactorTwoFullLabelWord n L data r) +
      (w.completeFactorTwoFrontier n L data r) •
        (completeTerminalPrimitiveCorrection n L data r : FreeModel n L)
  rw [← smul_add]
  apply congrArg (fun x : FreeModel n L ↦
    (w.completeFactorTwoFrontier n L data r) • x)
  exact terminalSourcePrimitive_completeFactorTwoChainPart_of_terminal
    n L data hn r (by
      by_contra hnonterminal
      apply Finsupp.mem_support_iff.mp hr
      rw [GoverningWitness.completeFactorTwoFrontier, Finsupp.sum_apply]
      apply Finset.sum_eq_zero
      intro s hs
      change (w.quotientWeightInitial n L data s) *
          (completeFactorTwoCollector n L data).normalForm s r = 0
      rw [(completeFactorTwoCollector n L data).normalForm_apply_eq_zero_of_nonterminal
        s r hnonterminal, mul_zero])

/-- The normal-form full-label read below one row is the boundary of the sum
of all genuine factor-two Koszul rows in that normal form. -/
theorem completeNormalFormFullLabelRead_eq_dOne
    (r : QuotientWeightRow n L data) :
    completeNormalFormFullLabelRead n L data hn r =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (((completeFactorTwoCollector n L data).normalForm r).sum
          (fun q z ↦ z • completeFactorTwoChainPart n L data hn q)) := by
  classical
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro q hq
  rw [map_zsmul]
  change (completeFactorTwoCollector n L data).normalForm r q •
      completeFactorTwoFullLabelRead n L data hn q =
    (completeFactorTwoCollector n L data).normalForm r q •
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (completeFactorTwoChainPart n L data hn q)
  congr 1
  symm
  apply dOne_completeFactorTwoChainPart_of_terminal n L data hn q
  by_contra hnonterminal
  exact Finsupp.mem_support_iff.mp hq
    ((completeFactorTwoCollector n L data).normalForm_apply_eq_zero_of_nonterminal
      r q hnonterminal)

/-- Aggregate terminal classification for the complete governing frontier. -/
theorem GoverningWitness.completeNormalFormFullLabelRead_eq_dOne_completeFactorTwoChain
    {a : L} (w : GoverningWitness n L data a) :
    (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • completeNormalFormFullLabelRead n L data hn r) =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.completeFactorTwoChain n L data hn) := by
  classical
  have hchain : w.completeFactorTwoChain n L data hn =
      (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
        z • completeFactorTwoChainPart n L data hn r) := by
    rw [GoverningWitness.completeFactorTwoChain,
      GoverningWitness.completeFactorTwoRows]
    change Finsupp.linearCombination ℤ
        (fun q : CompleteFactorTwoRow n L data ↦ q.one n L data hn)
        ((w.completeFactorTwoFrontier n L data).sum (fun r z ↦
          z • completeFactorTwoPart n L data r)) = _
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro r hr
    rw [map_zsmul]
    rfl
  have hboundary (x : QuotientWeightRow n L data →₀ ℤ) :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (x.sum (fun r z ↦ z • completeFactorTwoChainPart n L data hn r)) =
        completeFactorTwoBoundaryLinear n L data hn x := by
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro r hr
    rw [map_zsmul]
    rfl
  rw [hchain, hboundary]
  rw [GoverningWitness.completeFactorTwoFrontier, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul]
  congr 1
  symm
  rw [completeNormalFormFullLabelRead_eq_dOne n L data hn r]
  exact (hboundary ((completeFactorTwoCollector n L data).normalForm r)).symm

end

end LieRings.MetabelianVanishing
