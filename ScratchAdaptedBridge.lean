import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoTerminalRead

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

/-- Factor-two PBW read of the already normalized, provenance-retaining
component frontier. -/
def GoverningWitness.completeComponentPBWFactorTwo {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.completeComponentPBWFrontier n L data hn).sum (fun s z ↦
    z • rightSymbol n L data hn 2 n (by omega) (s.value n L data hn))

/-- The normalized adapted component frontier is a common, basis-independent
realization of the terminal factor defect. -/
theorem GoverningWitness.completeComponentPBWFactorTwo_eq_terminalFactorDefect
    {a : L} (w : GoverningWitness n L data a) :
    w.completeComponentPBWFactorTwo n L data hn =
      w.terminalFactorDefect n L data hn := by
  have h := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.evaluate_completeComponentPBWFrontier n L data hn)
  change rightSymbol n L data hn 2 n (by omega)
      ((w.completeComponentPBWFrontier n L data hn).sum
        (fun s z ↦ z • s.value n L data hn)) =
    rightSymbol n L data hn 2 n (by omega)
      ((w.provenancedCells n L data hn).sum
        (fun c z ↦ z • c.componentRow.value)) at h
  rw [map_finsuppSum, map_finsuppSum] at h
  simpa only [map_zsmul,
    GoverningWitness.completeComponentPBWFactorTwo,
    GoverningWitness.terminalFactorDefect,
    ProvenancedCell.factorEdge] using h

/-! A primitive-level audit of the second (quotient-weight) collector.  The
factor-two Stokes theorem in the production files is obtained by applying
`rightSymbol`.  For the primitive comparison we need the stronger equality
before taking any PBW factor projection. -/

def scratchCompleteCutoffWordSeed
    (r : QuotientWeightRow n L data) : UEA ℤ (FreeModel n L) :=
  match r with
  | .ordinary _ => 0
  | .marked left rho s right =>
      if 2 < left.length + 1 + right.length ∧ s.val = n + 1 then
        completeFactorTwoFullLabelWord n L data (.marked left rho s right)
      else 0

private def scratchCompleteCutoffWordTraceStep
    (r : QuotientWeightRow n L data)
    (rec : ∀ q, (completeFactorTwoCollector n L data).relation q r →
      UEA ℤ (FreeModel n L)) : UEA ℤ (FreeModel n L) :=
  scratchCompleteCutoffWordSeed n L data r +
    match h : (completeFactorTwoCollector n L data).expansion r with
    | none => 0
    | some qs => (qs.attach.map fun q ↦ q.1.1 •
        rec q.1.2
          ((completeFactorTwoCollector n L data).decreases h q.1 q.2)).sum

def scratchCompleteCutoffWordTrace
    (r : QuotientWeightRow n L data) : UEA ℤ (FreeModel n L) :=
  (completeFactorTwoCollector n L data).wellFounded.fix
    (scratchCompleteCutoffWordTraceStep n L data) r

theorem scratchCompleteCutoffWordTrace_eq
    (r : QuotientWeightRow n L data) :
    scratchCompleteCutoffWordTrace n L data r =
      scratchCompleteCutoffWordTraceStep n L data r
        (fun q _ ↦ scratchCompleteCutoffWordTrace n L data q) := by
  rw [scratchCompleteCutoffWordTrace,
    (completeFactorTwoCollector n L data).wellFounded.fix_eq]
  congr 1

def scratchCompleteNormalFullLabelWord
    (r : QuotientWeightRow n L data) : UEA ℤ (FreeModel n L) :=
  ((completeFactorTwoCollector n L data).normalForm r).sum
    (fun q z ↦ z • completeFactorTwoFullLabelWord n L data q)

private theorem scratchFullLabelWord_markedTransfer
    (left rest : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (v : TriangularPBWIndex n L) :
    completeFactorTwoFullLabelWord n L data
        (.marked left rho ⟨0, by omega⟩ (v :: rest)) =
      completeFactorTwoFullLabelWord n L data
          (.marked (left ++ [v]) rho ⟨0, by omega⟩ rest) +
        completeFactorTwoFullLabelWord n L data
          (.marked left (triangularRelationRightBracket n L data rho v)
            ⟨0, by omega⟩ rest) := by
  let lw := QuotientWeightRow.basisWord n L data left
  let rwrd := QuotientWeightRow.basisWord n L data rest
  let R : FreeModel n L := rho
  let xv : FreeModel n L := triangularPBWBasis n L data v
  have hleftWord : QuotientWeightRow.basisWord n L data
      (left ++ [v]) = lw * UniversalEnvelopingAlgebra.ι ℤ xv := by
    simp [QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, List.map_append, lw, xv]
  have hrightWord : QuotientWeightRow.basisWord n L data (v :: rest) =
      UniversalEnvelopingAlgebra.ι ℤ xv * rwrd := by
    simp [QuotientWeightRow.basisWord, LieRings.PBW.basisWord,
      LieRings.PBW.word, rwrd, xv]
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L) R xv
  simp only [completeFactorTwoFullLabelWord]
  rw [hleftWord, hrightWord]
  change lw * UniversalEnvelopingAlgebra.ι ℤ R *
      (UniversalEnvelopingAlgebra.ι ℤ xv * rwrd) =
    (lw * UniversalEnvelopingAlgebra.ι ℤ xv) *
        UniversalEnvelopingAlgebra.ι ℤ R * rwrd +
      lw * UniversalEnvelopingAlgebra.ι ℤ ⁅R, xv⁆ * rwrd
  calc
    _ = lw * (UniversalEnvelopingAlgebra.ι ℤ R *
        UniversalEnvelopingAlgebra.ι ℤ xv) * rwrd := by
          noncomm_ring
    _ = lw * (UniversalEnvelopingAlgebra.ι ℤ xv *
          UniversalEnvelopingAlgebra.ι ℤ R +
        UniversalEnvelopingAlgebra.ι ℤ ⁅R, xv⁆) * rwrd := by
          rw [hswap]
    _ = _ := by noncomm_ring

private theorem scratchQuotientTruncationRows_fullLabelWord
    (left right : List (TriangularPBWIndex n L))
    (rho : Relations n L data) (s : ℕ) (hs : s < n + 1) :
    ((quotientTruncationRows n L data left right rho s hs).map
      (fun q ↦ q.1 •
        completeFactorTwoFullLabelWord n L data q.2)).sum = 0 := by
  classical
  apply List.sum_eq_zero
  intro z hz
  rw [List.mem_map] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  rw [quotientTruncationRows, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  simp [completeFactorTwoFullLabelWord]

theorem scratchCompleteExpansion_fullLabelWord_balance
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (hn : 2 ≤ n)
    (h : completeFactorTwoExpansion n L data r = some qs) :
    (qs.map fun q ↦ q.1 •
        completeFactorTwoFullLabelWord n L data q.2).sum +
      scratchCompleteCutoffWordSeed n L data r =
        completeFactorTwoFullLabelWord n L data r := by
  classical
  cases r with
  | ordinary xs =>
      simp only [completeFactorTwoExpansion] at h
      simp only [quotientWeightExpansion] at h
      split at h <;> try contradiction
      rename_i d hd
      rw [Option.some.injEq] at h
      subst qs
      simp [quotientOrdinaryCorrection, completeFactorTwoFullLabelWord,
        scratchCompleteCutoffWordSeed]
      apply List.sum_eq_zero
      intro z hz
      rw [List.mem_map] at hz
      obtain ⟨q, hq, rfl⟩ := hz
      simp [completeFactorTwoFullLabelWord]
  | marked left rho s right =>
      simp only [completeFactorTwoExpansion] at h
      split at h
      · contradiction
      · rename_i hlarge
        simp only [quotientWeightExpansion] at h
        split at h
        · contradiction
        · rename_i hone
          split at h
          · rename_i hcut
            rw [Option.some.injEq] at h
            subst qs
            have hfactor : 2 < left.length + 1 + right.length := by
              simpa [QuotientWeightRow.factorCount] using hlarge
            simp [scratchCompleteCutoffWordSeed, hfactor, hcut]
          · rename_i hcut
            have hslt : s.val < n + 1 := by omega
            split at h
            · rename_i v rest hright
              split at h
              · rename_i hv
                rw [Option.some.injEq] at h
                subst qs
                simp only [List.map_cons, List.map_nil, List.sum_cons,
                  List.sum_nil, one_smul, add_zero]
                have hword := scratchFullLabelWord_markedTransfer
                  n L data hn left rest rho v
                simpa [scratchCompleteCutoffWordSeed, hcut] using hword.symm
              · rename_i hv
                rw [Option.some.injEq] at h
                subst qs
                rw [List.map_cons, List.sum_cons,
                  scratchQuotientTruncationRows_fullLabelWord
                    n L data left (v :: rest) rho s.val hslt]
                simp [scratchCompleteCutoffWordSeed, hcut,
                  completeFactorTwoFullLabelWord]
            · rename_i hright
              rw [Option.some.injEq] at h
              subst qs
              rw [List.map_cons, List.sum_cons,
                scratchQuotientTruncationRows_fullLabelWord
                  n L data left [] rho s.val hslt]
              simp [scratchCompleteCutoffWordSeed, hcut,
                completeFactorTwoFullLabelWord]

private def scratchCompleteFullLabelWordLinear :
    (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ
    (completeFactorTwoFullLabelWord n L data)

private theorem scratchSum_smul_add_completeFullLabelWord
    (rows : List (ℤ × QuotientWeightRow n L data)) :
    (rows.map (fun q ↦ q.1 •
      (scratchCompleteNormalFullLabelWord n L data q.2 +
        scratchCompleteCutoffWordTrace n L data q.2))).sum =
      (rows.map (fun q ↦ q.1 •
        scratchCompleteNormalFullLabelWord n L data q.2)).sum +
      (rows.map (fun q ↦ q.1 •
        scratchCompleteCutoffWordTrace n L data q.2)).sum := by
  induction rows with
  | nil => simp
  | cons q rows ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        _ = q.1 • scratchCompleteNormalFullLabelWord n L data q.2 +
              q.1 • scratchCompleteCutoffWordTrace n L data q.2 +
              (rows.map (fun p ↦ p.1 •
                (scratchCompleteNormalFullLabelWord n L data p.2 +
                  scratchCompleteCutoffWordTrace n L data p.2))).sum := by
                rw [smul_add]
        _ = q.1 • scratchCompleteNormalFullLabelWord n L data q.2 +
              q.1 • scratchCompleteCutoffWordTrace n L data q.2 +
              ((rows.map (fun p ↦ p.1 •
                  scratchCompleteNormalFullLabelWord n L data p.2)).sum +
                (rows.map (fun p ↦ p.1 •
                  scratchCompleteCutoffWordTrace n L data p.2)).sum) := by
                    rw [ih]
        _ = _ := by module

/-- Raw-UEA form of the full-label Stokes equation.  Unlike the factor read
used later in the production development, this equality retains enough
information to apply the PBW primitive projection. -/
theorem scratchCompleteFullLabelWord_eq_normalForm_add_cutoff
    (hn : 2 ≤ n) (r : QuotientWeightRow n L data) :
    completeFactorTwoFullLabelWord n L data r =
      scratchCompleteNormalFullLabelWord n L data r +
        scratchCompleteCutoffWordTrace n L data r := by
  classical
  let C := completeFactorTwoCollector n L data
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : completeFactorTwoExpansion n L data r with
      | none =>
          have hseed : scratchCompleteCutoffWordSeed n L data r = 0 := by
            cases r with
            | ordinary xs => rfl
            | marked left rho s right =>
                have hsmall :=
                  (completeFactorTwoExpansion_marked_eq_none_iff
                    n L data left right rho s).mp hexp
                simp [scratchCompleteCutoffWordSeed, hsmall]
          rw [scratchCompleteNormalFullLabelWord,
            C.normalForm_eq_single_of_terminal hexp,
            scratchCompleteCutoffWordTrace_eq]
          unfold scratchCompleteCutoffWordTraceStep
          have hexp' : C.expansion r = none := hexp
          split
          · simp [hseed]
          · rename_i rows he
            rw [hexp'] at he
            contradiction
      | some qs =>
          have hnf :
              scratchCompleteNormalFullLabelWord n L data r =
                (qs.map fun q ↦ q.1 •
                  scratchCompleteNormalFullLabelWord n L data q.2).sum := by
            change scratchCompleteFullLabelWordLinear n L data
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change scratchCompleteFullLabelWordLinear n L data
                (q.1 • C.normalForm q.2) =
              q.1 • scratchCompleteNormalFullLabelWord n L data q.2
            rw [map_zsmul]
            rfl
          have htrace :
              scratchCompleteCutoffWordTrace n L data r =
                scratchCompleteCutoffWordSeed n L data r +
                  (qs.map fun q ↦ q.1 •
                    scratchCompleteCutoffWordTrace n L data q.2).sum := by
            have hexp' : C.expansion r = some qs := hexp
            rw [scratchCompleteCutoffWordTrace_eq]
            unfold scratchCompleteCutoffWordTraceStep
            split
            · rename_i he
              rw [hexp'] at he
              contradiction
            · rename_i rows he
              have hrows : rows = qs := by
                rw [hexp'] at he
                exact (Option.some.inj he).symm
              subst rows
              congr 1
              simpa only using congrArg List.sum
                (List.attach_map_val (l := qs)
                  (f := fun q ↦ q.1 •
                    scratchCompleteCutoffWordTrace n L data q.2))
          rw [hnf, htrace]
          change completeFactorTwoFullLabelWord n L data r =
            (qs.map fun q ↦ q.1 •
                scratchCompleteNormalFullLabelWord n L data q.2).sum +
              (scratchCompleteCutoffWordSeed n L data r +
                (qs.map fun q ↦ q.1 •
                  scratchCompleteCutoffWordTrace n L data q.2).sum)
          have hchildren :
              (qs.map fun q ↦ q.1 •
                completeFactorTwoFullLabelWord n L data q.2).sum =
              (qs.map fun q ↦ q.1 •
                scratchCompleteNormalFullLabelWord n L data q.2).sum +
              (qs.map fun q ↦ q.1 •
                scratchCompleteCutoffWordTrace n L data q.2).sum := by
            calc
              _ = (qs.map fun q ↦ q.1 •
                    (scratchCompleteNormalFullLabelWord n L data q.2 +
                      scratchCompleteCutoffWordTrace n L data q.2)).sum := by
                    apply congrArg List.sum
                    apply List.map_congr_left
                    intro q hq
                    rw [ih q.2 (C.decreases hexp q hq)]
              _ = _ := scratchSum_smul_add_completeFullLabelWord
                    n L data qs
          have hlocal := scratchCompleteExpansion_fullLabelWord_balance
            n L data hn hexp
          rw [← hlocal, hchildren]
          module

/-- The literal whole-label word at the start of the second pass is the
governing element itself. -/
theorem GoverningWitness.scratchCompleteInitialFullLabelWord_eq_theta
    {a : L} (w : GoverningWitness n L data a) :
    (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelWord n L data r) = w.theta := by
  classical
  have hvalue := w.evaluate_triangularPlacedFrontier n L data
  change (w.triangularPlacedFrontier n L data).sum (fun r z ↦
      z • TriangularPlacedRow.value n L data r) = w.theta at hvalue
  rw [GoverningWitness.quotientWeightInitial,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  calc
    _ = (w.triangularPlacedFrontier n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelWord n L data
          (quotientWeightRowOfPlaced n L data r)) := by
      apply Finsupp.sum_congr
      intro r hr
      simp
    _ = (w.triangularPlacedFrontier n L data).sum (fun r z ↦
        z • TriangularPlacedRow.value n L data r) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [completeFactorTwoFullLabelWord_quotientWeightRowOfPlaced]
    _ = w.theta := hvalue

/-- Raw whole-label contribution stopped at the external factor-two cutoff. -/
def GoverningWitness.scratchCompleteCutoffWord {a : L}
    (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.quotientWeightInitial n L data).sum (fun r z ↦
    z • scratchCompleteCutoffWordTrace n L data r)

/-- Aggregate raw-UEA Stokes equation for the complete second pass. -/
theorem GoverningWitness.scratchTheta_eq_completeNormalWord_add_cutoff
    {a : L} (w : GoverningWitness n L data a) (hn : 2 ≤ n) :
    w.theta =
      (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • scratchCompleteNormalFullLabelWord n L data r) +
      w.scratchCompleteCutoffWord n L data := by
  classical
  rw [← w.scratchCompleteInitialFullLabelWord_eq_theta n L data,
    GoverningWitness.scratchCompleteCutoffWord,
    ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  rw [scratchCompleteFullLabelWord_eq_normalForm_add_cutoff
    n L data hn r]
  exact smul_add _ _ _

/-- The raw terminal normal-form sum is precisely the whole-relation word
sum over the complete terminal frontier. -/
theorem GoverningWitness.scratchCompleteNormalWord_eq_frontierWord
    {a : L} (w : GoverningWitness n L data a) :
    (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • scratchCompleteNormalFullLabelWord n L data r) =
      (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelWord n L data r) := by
  classical
  rw [GoverningWitness.completeFactorTwoFrontier,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  change (w.quotientWeightInitial n L data r) •
      scratchCompleteFullLabelWordLinear n L data
        ((completeFactorTwoCollector n L data).normalForm r) =
    scratchCompleteFullLabelWordLinear n L data
      ((w.quotientWeightInitial n L data r) •
        (completeFactorTwoCollector n L data).normalForm r)
  rw [map_zsmul]

/-- Primitive projection of the exact raw Stokes equation. -/
theorem GoverningWitness.scratchPBWPrimitiveTheta_eq_complete_add_cutoff
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn w.theta =
      w.completeFactorTwoFullLabelPrimitive n L data hn +
        pbwPrimitive n L data hn
          (w.scratchCompleteCutoffWord n L data) := by
  have h := congrArg (pbwPrimitive n L data hn)
    (w.scratchTheta_eq_completeNormalWord_add_cutoff n L data hn)
  rw [map_add] at h
  rw [w.scratchCompleteNormalWord_eq_frontierWord n L data] at h
  rw [map_finsuppSum] at h
  simpa only [map_zsmul,
    GoverningWitness.completeFactorTwoFullLabelPrimitive] using h

end

end LieRings.MetabelianVanishing
