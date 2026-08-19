import LieRings.DimensionSubring.MetabelianVanishing.TerminalCorrection
import LieRings.DimensionSubring.MetabelianVanishing.TerminalRealization

/-!
# Primitive bridge for the complete factor-two correction

This file retains the raw UEA-valued full-label Stokes ledger.  It is the
primitive-level counterpart of the factor-two boundary ledger: no PBW factor
is discarded before the terminal comparison.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeFactorTwoPrimitiveBridgeFintype : Fintype L :=
  Fintype.ofFinite L

/-! A primitive-level audit of the second (quotient-weight) collector.  The
factor-two Stokes theorem in the production files is obtained by applying
`rightSymbol`.  For the primitive comparison we need the stronger equality
before taking any PBW factor projection. -/

def rawCompleteCutoffWordSeed
    (r : QuotientWeightRow n L data) : UEA ℤ (FreeModel n L) :=
  match r with
  | .ordinary _ => 0
  | .marked left rho s right =>
      if 2 < left.length + 1 + right.length ∧ s.val = n + 1 then
        completeFactorTwoFullLabelWord n L data (.marked left rho s right)
      else 0

private def rawCompleteCutoffWordTraceStep
    (r : QuotientWeightRow n L data)
    (rec : ∀ q, (completeFactorTwoCollector n L data).relation q r →
      UEA ℤ (FreeModel n L)) : UEA ℤ (FreeModel n L) :=
  rawCompleteCutoffWordSeed n L data r +
    match h : (completeFactorTwoCollector n L data).expansion r with
    | none => 0
    | some qs => (qs.attach.map fun q ↦ q.1.1 •
        rec q.1.2
          ((completeFactorTwoCollector n L data).decreases h q.1 q.2)).sum

def rawCompleteCutoffWordTrace
    (r : QuotientWeightRow n L data) : UEA ℤ (FreeModel n L) :=
  (completeFactorTwoCollector n L data).wellFounded.fix
    (rawCompleteCutoffWordTraceStep n L data) r

theorem rawCompleteCutoffWordTrace_eq
    (r : QuotientWeightRow n L data) :
    rawCompleteCutoffWordTrace n L data r =
      rawCompleteCutoffWordTraceStep n L data r
        (fun q _ ↦ rawCompleteCutoffWordTrace n L data q) := by
  rw [rawCompleteCutoffWordTrace,
    (completeFactorTwoCollector n L data).wellFounded.fix_eq]
  congr 1

def rawCompleteNormalFullLabelWord
    (r : QuotientWeightRow n L data) : UEA ℤ (FreeModel n L) :=
  ((completeFactorTwoCollector n L data).normalForm r).sum
    (fun q z ↦ z • completeFactorTwoFullLabelWord n L data q)

private theorem rawFullLabelWord_markedTransfer
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

private theorem rawQuotientTruncationRows_fullLabelWord
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

theorem rawCompleteExpansion_fullLabelWord_balance
    {r : QuotientWeightRow n L data}
    {qs : List (ℤ × QuotientWeightRow n L data)}
    (hn : 2 ≤ n)
    (h : completeFactorTwoExpansion n L data r = some qs) :
    (qs.map fun q ↦ q.1 •
        completeFactorTwoFullLabelWord n L data q.2).sum +
      rawCompleteCutoffWordSeed n L data r =
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
        rawCompleteCutoffWordSeed]
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
            simp [rawCompleteCutoffWordSeed, hfactor, hcut]
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
                have hword := rawFullLabelWord_markedTransfer
                  n L data hn left rest rho v
                simpa [rawCompleteCutoffWordSeed, hcut] using hword.symm
              · rename_i hv
                rw [Option.some.injEq] at h
                subst qs
                rw [List.map_cons, List.sum_cons,
                  rawQuotientTruncationRows_fullLabelWord
                    n L data left (v :: rest) rho s.val hslt]
                simp [rawCompleteCutoffWordSeed, hcut,
                  completeFactorTwoFullLabelWord]
            · rename_i hright
              rw [Option.some.injEq] at h
              subst qs
              rw [List.map_cons, List.sum_cons,
                rawQuotientTruncationRows_fullLabelWord
                  n L data left [] rho s.val hslt]
              simp [rawCompleteCutoffWordSeed, hcut,
                completeFactorTwoFullLabelWord]

private def rawCompleteFullLabelWordLinear :
    (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ] UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ
    (completeFactorTwoFullLabelWord n L data)

private theorem rawSum_smul_add_completeFullLabelWord
    (rows : List (ℤ × QuotientWeightRow n L data)) :
    (rows.map (fun q ↦ q.1 •
      (rawCompleteNormalFullLabelWord n L data q.2 +
        rawCompleteCutoffWordTrace n L data q.2))).sum =
      (rows.map (fun q ↦ q.1 •
        rawCompleteNormalFullLabelWord n L data q.2)).sum +
      (rows.map (fun q ↦ q.1 •
        rawCompleteCutoffWordTrace n L data q.2)).sum := by
  induction rows with
  | nil => simp
  | cons q rows ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        _ = q.1 • rawCompleteNormalFullLabelWord n L data q.2 +
              q.1 • rawCompleteCutoffWordTrace n L data q.2 +
              (rows.map (fun p ↦ p.1 •
                (rawCompleteNormalFullLabelWord n L data p.2 +
                  rawCompleteCutoffWordTrace n L data p.2))).sum := by
                rw [smul_add]
        _ = q.1 • rawCompleteNormalFullLabelWord n L data q.2 +
              q.1 • rawCompleteCutoffWordTrace n L data q.2 +
              ((rows.map (fun p ↦ p.1 •
                  rawCompleteNormalFullLabelWord n L data p.2)).sum +
                (rows.map (fun p ↦ p.1 •
                  rawCompleteCutoffWordTrace n L data p.2)).sum) := by
                    rw [ih]
        _ = _ := by module

/-- Raw-UEA form of the full-label Stokes equation.  Unlike the factor read
used later in the production development, this equality retains enough
information to apply the PBW primitive projection. -/
theorem rawCompleteFullLabelWord_eq_normalForm_add_cutoff
    (hn : 2 ≤ n) (r : QuotientWeightRow n L data) :
    completeFactorTwoFullLabelWord n L data r =
      rawCompleteNormalFullLabelWord n L data r +
        rawCompleteCutoffWordTrace n L data r := by
  classical
  let C := completeFactorTwoCollector n L data
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : completeFactorTwoExpansion n L data r with
      | none =>
          have hseed : rawCompleteCutoffWordSeed n L data r = 0 := by
            cases r with
            | ordinary xs => rfl
            | marked left rho s right =>
                have hsmall :=
                  (completeFactorTwoExpansion_marked_eq_none_iff
                    n L data left right rho s).mp hexp
                simp [rawCompleteCutoffWordSeed, hsmall]
          rw [rawCompleteNormalFullLabelWord,
            C.normalForm_eq_single_of_terminal hexp,
            rawCompleteCutoffWordTrace_eq]
          unfold rawCompleteCutoffWordTraceStep
          have hexp' : C.expansion r = none := hexp
          split
          · simp [hseed]
          · rename_i rows he
            rw [hexp'] at he
            contradiction
      | some qs =>
          have hnf :
              rawCompleteNormalFullLabelWord n L data r =
                (qs.map fun q ↦ q.1 •
                  rawCompleteNormalFullLabelWord n L data q.2).sum := by
            change rawCompleteFullLabelWordLinear n L data
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change rawCompleteFullLabelWordLinear n L data
                (q.1 • C.normalForm q.2) =
              q.1 • rawCompleteNormalFullLabelWord n L data q.2
            rw [map_zsmul]
            rfl
          have htrace :
              rawCompleteCutoffWordTrace n L data r =
                rawCompleteCutoffWordSeed n L data r +
                  (qs.map fun q ↦ q.1 •
                    rawCompleteCutoffWordTrace n L data q.2).sum := by
            have hexp' : C.expansion r = some qs := hexp
            rw [rawCompleteCutoffWordTrace_eq]
            unfold rawCompleteCutoffWordTraceStep
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
                    rawCompleteCutoffWordTrace n L data q.2))
          rw [hnf, htrace]
          change completeFactorTwoFullLabelWord n L data r =
            (qs.map fun q ↦ q.1 •
                rawCompleteNormalFullLabelWord n L data q.2).sum +
              (rawCompleteCutoffWordSeed n L data r +
                (qs.map fun q ↦ q.1 •
                  rawCompleteCutoffWordTrace n L data q.2).sum)
          have hchildren :
              (qs.map fun q ↦ q.1 •
                completeFactorTwoFullLabelWord n L data q.2).sum =
              (qs.map fun q ↦ q.1 •
                rawCompleteNormalFullLabelWord n L data q.2).sum +
              (qs.map fun q ↦ q.1 •
                rawCompleteCutoffWordTrace n L data q.2).sum := by
            calc
              _ = (qs.map fun q ↦ q.1 •
                    (rawCompleteNormalFullLabelWord n L data q.2 +
                      rawCompleteCutoffWordTrace n L data q.2)).sum := by
                    apply congrArg List.sum
                    apply List.map_congr_left
                    intro q hq
                    rw [ih q.2 (C.decreases hexp q hq)]
              _ = _ := rawSum_smul_add_completeFullLabelWord
                    n L data qs
          have hlocal := rawCompleteExpansion_fullLabelWord_balance
            n L data hn hexp
          rw [← hlocal, hchildren]
          module

/-- The literal whole-label word at the start of the second pass is the
governing element itself. -/
theorem GoverningWitness.rawCompleteInitialFullLabelWord_eq_theta
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
def GoverningWitness.rawCompleteCutoffWord {a : L}
    (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.quotientWeightInitial n L data).sum (fun r z ↦
    z • rawCompleteCutoffWordTrace n L data r)

/-- Aggregate raw-UEA Stokes equation for the complete second pass. -/
theorem GoverningWitness.rawTheta_eq_completeNormalWord_add_cutoff
    {a : L} (w : GoverningWitness n L data a) (hn : 2 ≤ n) :
    w.theta =
      (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • rawCompleteNormalFullLabelWord n L data r) +
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [← w.rawCompleteInitialFullLabelWord_eq_theta n L data,
    GoverningWitness.rawCompleteCutoffWord,
    ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  rw [rawCompleteFullLabelWord_eq_normalForm_add_cutoff
    n L data hn r]
  exact smul_add _ _ _

/-- The raw terminal normal-form sum is precisely the whole-relation word
sum over the complete terminal frontier. -/
theorem GoverningWitness.rawCompleteNormalWord_eq_frontierWord
    {a : L} (w : GoverningWitness n L data a) :
    (w.quotientWeightInitial n L data).sum (fun r z ↦
        z • rawCompleteNormalFullLabelWord n L data r) =
      (w.completeFactorTwoFrontier n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelWord n L data r) := by
  classical
  rw [GoverningWitness.completeFactorTwoFrontier,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  change (w.quotientWeightInitial n L data r) •
      rawCompleteFullLabelWordLinear n L data
        ((completeFactorTwoCollector n L data).normalForm r) =
    rawCompleteFullLabelWordLinear n L data
      ((w.quotientWeightInitial n L data r) •
        (completeFactorTwoCollector n L data).normalForm r)
  rw [map_zsmul]

/-- Primitive projection of the exact raw Stokes equation. -/
theorem GoverningWitness.rawPBWPrimitiveTheta_eq_complete_add_cutoff
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn w.theta =
      w.completeFactorTwoFullLabelPrimitive n L data hn +
        pbwPrimitive n L data hn
          (w.rawCompleteCutoffWord n L data) := by
  have h := congrArg (pbwPrimitive n L data hn)
    (w.rawTheta_eq_completeNormalWord_add_cutoff n L data hn)
  rw [map_add] at h
  rw [w.rawCompleteNormalWord_eq_frontierWord n L data] at h
  rw [map_finsuppSum] at h
  simpa only [map_zsmul,
    GoverningWitness.completeFactorTwoFullLabelPrimitive] using h

/-! ## The opposite side of the terminal square

The complete factor-two collector is compared below with the literal
mark-one labels of the contextual collector.  The first point which must be
recorded is that replacing the active marked prefix by its *whole contextual
relation* does not alter the PBW primitive at a terminal factor-two wall.
The difference is a homogeneous top piece multiplied by another primitive
factor, and hence has zero complete factor-one projection. -/

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

/-- The raw UEA word carried by the contextual factor-two terminal wall.
This is the single whole-label target against which the stopped complete
cutoff has to be compared: neither of its two relevant PBW projections is
chosen separately. -/
def GoverningWitness.terminalTwoFullLabelWord {a : L}
    (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.provenancedTerminalTwo n L data hn).sum (fun c z ↦ z •
    contextualFullRelationWord n L data hn
      c.root c.context [c.factor] [])

/-- The complete one-factor PBW read of the raw contextual factor-two word
is exactly the primitive already attached to that wall. -/
theorem GoverningWitness.pbwPrimitive_terminalTwoFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn
        (w.terminalTwoFullLabelWord n L data hn) =
      w.terminalTwoPrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalTwoFullLabelWord,
    GoverningWitness.terminalTwoPrimitive, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul,
    c.pbwPrimitive_contextualFullRelationWord n L data hn]

/-- The factor-two read of the very same raw word is the full-label
contextual terminal edge (and hence the boundary of the contextual terminal
chain). -/
theorem GoverningWitness.rightSymbol_terminalTwoFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.terminalTwoFullLabelWord n L data hn) =
      w.terminalTwoFullLabel n L data hn := by
  classical
  rw [GoverningWitness.terminalTwoFullLabelWord, map_finsuppSum,
    w.terminalTwoFullLabel_eq_dOne_contextualTerminalChain n L data hn,
    w.dOne_contextualTerminalChain n L data hn]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul]
  let R : FreeModel n L :=
    RelationContext.relation n L data hn c.context c.root
  let P : FreeModel n L :=
    RelationContext.markedPrefix n L data hn c.context c.root c.mark
  let f : FreeModel n L := adaptedBasis n L data hn c.factor
  have hprefix : prLE n L n (by omega) R =
      prLE n L n (by omega) P := by
    exact RelationContext.projectPrefix_relation_eq_markedPrefix
      n L data hn c.context c.root c.mark c.active
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
  have hlocal : rightSymbol n L data hn 2 n (by omega)
        (contextualFullRelationWord n L data hn
          c.root c.context [c.factor] []) =
      rightSymbol n L data hn 2 n (by omega) c.row.value := by
    rw [hfull, hrow,
      rightSymbol_iota_mul_iota_two_comm n L data hn,
      rightSymbol_iota_mul_iota_two_comm n L data hn,
      hprefix]
  exact congrArg (fun x ↦
    (w.provenancedTerminalTwo n L data hn c) • x) hlocal

/-- The raw UEA sum of the genuine full contextual relation labels transferred
to mark-one component leaves.  This is the horizontal side of the terminal
square before taking either its factor-two boundary or its PBW primitive. -/
private def provenancedComponentFullLabelWordSeed :
    ProvenancedRow n L data hn → UEA ℤ (FreeModel n L)
  | .marked _ _ _ _ _ => 0
  | .component rho c k left right =>
      if k.val = 1 then
        contextualFullRelationWord n L data hn rho c left right
      else 0

def GoverningWitness.terminalComponentFullLabelWord {a : L}
    (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.provenancedFrontier n L data hn).sum (fun r z ↦ z •
    provenancedComponentFullLabelWordSeed n L data hn r)

private def provenancedTerminalOnePrimitiveSeedForFullLabel :
    ProvenancedRow n L data hn → FreeModel n L
  | r => match provenancedTerminal? n L data hn r with
    | some (.inl c) => c.fullPrimitive n L data hn
    | _ => 0

private def provenancedTerminalTwoPrimitiveSeedForFullLabel :
    ProvenancedRow n L data hn → FreeModel n L
  | r => match provenancedTerminal? n L data hn r with
    | some (.inr c) => c.primitive n L data hn
    | _ => 0

private theorem pbwPrimitive_provenancedFullLabelWord_terminal
    (r : ProvenancedRow n L data hn)
    (hr : provenancedExpansion n L data hn r = none) :
    pbwPrimitive n L data hn
        (provenancedFullLabelWord n L data hn r) =
      pbwPrimitive n L data hn
          (provenancedComponentFullLabelWordSeed n L data hn r) +
        provenancedTerminalOnePrimitiveSeedForFullLabel n L data hn r +
        provenancedTerminalTwoPrimitiveSeedForFullLabel n L data hn r := by
  rcases provenanced_terminal_cases n L data hn r hr with
    ⟨rho, c, b, right, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · by_cases hb : b.val = 1
    · simp [provenancedFullLabelWord,
        provenancedComponentFullLabelWordSeed,
        provenancedTerminalOnePrimitiveSeedForFullLabel,
        provenancedTerminalTwoPrimitiveSeedForFullLabel,
        provenancedTerminal? , hb]
    · simp [provenancedFullLabelWord,
        provenancedComponentFullLabelWordSeed,
        provenancedTerminalOnePrimitiveSeedForFullLabel,
        provenancedTerminalTwoPrimitiveSeedForFullLabel,
        provenancedTerminal?, hb]
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
    simp [provenancedTerminalOnePrimitiveSeedForFullLabel,
      provenancedComponentFullLabelWordSeed,
      provenancedTerminalTwoPrimitiveSeedForFullLabel,
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
    simp [provenancedTerminalOnePrimitiveSeedForFullLabel,
      provenancedComponentFullLabelWordSeed,
      provenancedTerminalTwoPrimitiveSeedForFullLabel,
      ProvenancedTerminalTwo.row, provenancedTerminal?, t.active]

private theorem GoverningWitness.sum_terminalOnePrimitiveSeedForFullLabel_eq
    {a : L} (w : GoverningWitness n L data a) :
    (w.provenancedFrontier n L data hn).sum (fun r z ↦
        z • provenancedTerminalOnePrimitiveSeedForFullLabel
          n L data hn r) =
      w.terminalOnePrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalOnePrimitive,
    GoverningWitness.provenancedTerminalOne,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [provenancedTerminalOnePrimitiveSeedForFullLabel,
      provenancedTerminalOnePart, hc]
  | some t =>
      cases t with
      | inl c => simp [provenancedTerminalOnePrimitiveSeedForFullLabel,
          provenancedTerminalOnePart, hc]
      | inr c => simp [provenancedTerminalOnePrimitiveSeedForFullLabel,
          provenancedTerminalOnePart, hc]

private theorem GoverningWitness.sum_terminalTwoPrimitiveSeedForFullLabel_eq
    {a : L} (w : GoverningWitness n L data a) :
    (w.provenancedFrontier n L data hn).sum (fun r z ↦
        z • provenancedTerminalTwoPrimitiveSeedForFullLabel
          n L data hn r) =
      w.terminalTwoPrimitive n L data hn := by
  classical
  rw [GoverningWitness.terminalTwoPrimitive,
    GoverningWitness.provenancedTerminalTwo,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : provenancedTerminal? n L data hn r with
  | none => simp [provenancedTerminalTwoPrimitiveSeedForFullLabel,
      provenancedTerminalTwoPart, hc]
  | some t =>
      cases t with
      | inl c => simp [provenancedTerminalTwoPrimitiveSeedForFullLabel,
          provenancedTerminalTwoPart, hc]
      | inr c => simp [provenancedTerminalTwoPrimitiveSeedForFullLabel,
          provenancedTerminalTwoPart, hc]

/-- The PBW primitive of the literal mark-one full-label wall is precisely
the component primitive in the manuscript's external-edge ledger. -/
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
            z • provenancedTerminalOnePrimitiveSeedForFullLabel
              n L data hn r) +
          (w.provenancedFrontier n L data hn).sum (fun r z ↦
            z • provenancedTerminalTwoPrimitiveSeedForFullLabel
              n L data hn r) := by
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
  rw [hdecomp,
    w.sum_terminalOnePrimitiveSeedForFullLabel_eq n L data hn,
    w.sum_terminalTwoPrimitiveSeedForFullLabel_eq n L data hn] at hfull
  rw [htheta] at hfull
  rw [hcomponent]
  apply add_right_cancel
    (b := w.terminalOnePrimitive n L data hn +
      w.terminalTwoPrimitive n L data hn)
  simpa only [add_assoc] using hfull

/-- The other low PBW read of the same literal mark-one full-label wall is
exactly the terminal factor-two defect.  Thus the word used in the primitive
comparison and the symmetric boundary to be corrected are not two separately
chosen representatives. -/
theorem GoverningWitness.rightSymbol_terminalComponentFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.terminalComponentFullLabelWord n L data hn) =
      w.terminalFactorDefect n L data hn := by
  classical
  rw [GoverningWitness.terminalComponentFullLabelWord, map_finsuppSum]
  simp only [map_zsmul]
  change (w.provenancedFrontier n L data hn).sum (fun r z ↦
      z • rightSymbol n L data hn 2 n (by omega)
        (provenancedComponentFullLabelWordSeed n L data hn r)) = _
  rw [← w.terminalComponentFullLabel_eq_defect n L data hn,
    GoverningWitness.terminalComponentFullLabel]
  apply Finsupp.sum_congr
  intro r hr
  cases r with
  | marked root context mark left right =>
      simp [provenancedComponentFullLabelWordSeed,
        provenancedComponentFullLabelSeed]
  | component root context mark left right =>
      by_cases hmark : mark.val = 1 <;>
        simp [provenancedComponentFullLabelWordSeed,
          provenancedComponentFullLabelSeed, hmark]

/-! ## The single remaining closed-square comparison

The complete factor-first pass and the contextual pass must not be compared
once after applying `rightSymbol` and a second time after applying
`pbwPrimitive`.  The occurrence-labelled ledger compares their *raw UEA
words*.  The next definitions and lemmas package the two consequences of that
one comparison. -/

/-- Raw whole-relation word retained at the factor-at-most-two frontier of
the complete factor-first pass. -/
def GoverningWitness.completeTerminalFullLabelWord {a : L}
    (w : GoverningWitness n L data a) : UEA ℤ (FreeModel n L) :=
  (w.completeFactorTwoFrontier n L data).sum (fun r z ↦ z •
    completeFactorTwoFullLabelWord n L data r)

/-- Its primitive is exactly the primitive aggregate already used by the
terminal source-placement theorem. -/
theorem GoverningWitness.pbwPrimitive_completeTerminalFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn
        (w.completeTerminalFullLabelWord n L data) =
      w.completeFactorTwoFullLabelPrimitive n L data hn := by
  classical
  rw [GoverningWitness.completeTerminalFullLabelWord, map_finsuppSum]
  simp only [map_zsmul]
  rfl

/-- The factor-two read of the same raw frontier is the Koszul boundary of
the complete genuine full-relation chain. -/
theorem GoverningWitness.rightSymbol_completeTerminalFullLabelWord
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.completeTerminalFullLabelWord n L data) =
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.completeFactorTwoChain n L data hn) := by
  classical
  rw [GoverningWitness.completeTerminalFullLabelWord, map_finsuppSum]
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
  rw [hchain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul]
  congr 1
  symm
  apply dOne_completeFactorTwoChainPart_of_terminal n L data hn r
  by_contra hnonterminal
  apply Finsupp.mem_support_iff.mp hr
  rw [GoverningWitness.completeFactorTwoFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro s hs
  change (w.quotientWeightInitial n L data s) *
      (completeFactorTwoCollector n L data).normalForm s r = 0
  rw [(completeFactorTwoCollector n L data).normalForm_apply_eq_zero_of_nonterminal
    s r hnonterminal, mul_zero]

/-- The factor-two projection of the raw cutoff word is the full-label
cutoff edge of the complete collector.  This is deliberately proved only
after summing the whole Stokes ledger: no private recursion equation, and no
pointwise identification of incomplete PBW descendants, is needed. -/
theorem GoverningWitness.rightSymbol_rawCompleteCutoffWord
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.rawCompleteCutoffWord n L data) =
      w.completeFactorTwoCutoffFullLabel n L data hn := by
  have hraw := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.rawTheta_eq_completeNormalWord_add_cutoff n L data hn)
  rw [map_add, rightSymbol_theta_terminal_eq_zero n L data hn w,
    w.rawCompleteNormalWord_eq_frontierWord n L data] at hraw
  change 0 = rightSymbol n L data hn 2 n (by omega)
      (w.completeTerminalFullLabelWord n L data) +
        rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) at hraw
  rw [w.rightSymbol_completeTerminalFullLabelWord n L data hn] at hraw
  have hboundary :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (w.completeFactorTwoChain n L data hn) =
        -w.completeFactorTwoCutoffFullLabel n L data hn := by
    rw [← w.completeNormalFormFullLabelRead_eq_dOne_completeFactorTwoChain
      n L data hn]
    exact w.completeNormalFullLabel_eq_neg_cutoff n L data hn
  rw [hboundary] at hraw
  apply sub_eq_zero.mp
  calc
    rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) -
        w.completeFactorTwoCutoffFullLabel n L data hn =
      -w.completeFactorTwoCutoffFullLabel n L data hn +
        rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) := by abel
    _ = 0 := hraw.symm

/-- A raw closed-square comparison supplies the positive boundary orientation
required by the corrected contextual cycle. -/
theorem GoverningWitness.dOne_completeFactorTwoChain_of_fullLabelWord_eq
    {a : L} (w : GoverningWitness n L data a)
    (hword : w.completeTerminalFullLabelWord n L data =
      w.terminalComponentFullLabelWord n L data hn) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.completeFactorTwoChain n L data hn) =
      w.terminalFactorDefect n L data hn := by
  rw [← w.rightSymbol_completeTerminalFullLabelWord n L data hn,
    hword, w.rightSymbol_terminalComponentFullLabelWord n L data hn]

/-- The very same raw comparison supplies the primitive equation, with the
only source-placement error kept as one genuine element of `Relations`. -/
theorem GoverningWitness.terminalSourcePrimitive_completeFactorTwoChain_of_fullLabelWord_eq
    {a : L} (w : GoverningWitness n L data a)
    (hword : w.completeTerminalFullLabelWord n L data =
      w.terminalComponentFullLabelWord n L data hn) :
    terminalSourcePrimitive n L data hn
        (w.completeFactorTwoChain n L data hn) =
      w.componentTracePrimitive n L data hn +
        (w.completeFactorTwoPrimitiveCorrection n L data :
          FreeModel n L) := by
  rw [w.terminalSourcePrimitive_completeFactorTwoChain n L data hn,
    ← w.pbwPrimitive_completeTerminalFullLabelWord n L data hn,
    hword, w.pbwPrimitive_terminalComponentFullLabelWord n L data hn]

/-! ## Coordinate-level terminal consumer

This is the endpoint used by the manuscript.  It deliberately asks only for
the equality after applying the terminal cyclic functional; it does not ask
that two full free-model primitives differ by an element of `Relations`.
The source-to-Smith realization supplies the missing `TopPreimage` comparison
with a genuine full relation, and the quadratic certificate kills the mapped
cycle. -/

theorem GoverningWitness.eq_zero_of_terminalSourceCoordinate
    {a : L} (w : GoverningWitness n L data a)
    (cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1)
    (sourcePrimitive : TopPreimage n L data)
    (hsource : (sourcePrimitive : FreeModel n L) =
      terminalSourcePrimitive n L data hn cycle.1)
    (hcoordinate : terminalEval n L data sourcePrimitive =
      (w.externalMarkedWord n L data hn).value) :
    a = 0 := by
  let blockCycle := Koszul.PresentationHomology.cyclesMap
    (terminalSourcePresentation n L data hn)
    (rPresentation n L data (by omega))
    (terminalComparisonHom n L data hn) 1 cycle
  let raw := terminalBlockCanonicalRawMarkedWord n L data hn blockCycle
  obtain ⟨rho, hrealization⟩ :=
    terminalMappedBlockPrimitive_eq_source_add_relation
      n L data hn cycle
  have hrawPrimitive : (raw.primitive : FreeModel n L) =
      pbwPrimitive n L data hn raw.word := by
    apply canonicalMap_injective_of_freeModulePBW
      ℤ (FreeModel n L) (AdaptedIndex n L data hn)
      (adaptedWeightedBasis n L data hn).basis
      (freeModulePBW_int (FreeModel n L) (AdaptedIndex n L data hn)
        (adaptedWeightedBasis n L data hn).basis)
    rw [← raw.projection_eq,
      factorProj_one_eq_iota_pbwPrimitive n L data hn]
  have hrawTop : raw.primitive =
      sourcePrimitive + relationTopPreimage n L data rho := by
    apply Subtype.ext
    change (raw.primitive : FreeModel n L) =
      (sourcePrimitive : FreeModel n L) + (rho : FreeModel n L)
    rw [hrawPrimitive, hsource]
    exact hrealization
  have hrawValue : raw.value = terminalEval n L data sourcePrimitive := by
    change terminalEval n L data raw.primitive = _
    rw [hrawTop, map_add, terminalEval_relationTopPreimage, add_zero]
  have hcanonical : raw.value =
      (quadraticBlockMarkedWord n L data hn blockCycle).value :=
    (terminalBlockCanonicalRawCertificate n L data hn blockCycle).value_eq
  have hsourceZero : terminalEval n L data sourcePrimitive = 0 := by
    rw [← hrawValue, hcanonical,
      quadraticBlockMarkedWord_value,
      quadraticBlockValue_eq_zero]
  have hexternal : (w.externalMarkedWord n L data hn).value = 0 := by
    rw [← hcoordinate]
    exact hsourceZero
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
    exact hexternal
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

/-! ## Direct cutoff-continuation consumer

The most economical completion of the manuscript's terminal collection is to
continue the discarded *whole-relation* cutoff rows themselves down to factor
two.  The next theorem isolates exactly the two outputs required from that
finite continuation.  They are two projections of the same collected row
list, not independent choices. -/

/-- A factor-two continuation of the raw cutoff rows closes the complete
chain.  If its literal relation-on-the-left realization has the same PBW
primitive as the raw cutoff word modulo one genuine full relation, the
resulting cycle has the governing external coordinate and is killed by the
quadratic certificate. -/
theorem GoverningWitness.eq_zero_of_rawCompleteCutoffChain
    {a : L} (w : GoverningWitness n L data a)
    (cutoffChain : Koszul.One
      (terminalSourcePresentation n L data hn) 1)
    (cutoffRelation : Relations n L data)
    (hcutoffBoundary :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1 cutoffChain =
        rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data))
    (hcutoffPrimitive :
      terminalSourcePrimitive n L data hn cutoffChain =
        pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) +
          (cutoffRelation : FreeModel n L)) :
    a = 0 := by
  have hcompleteBoundary :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (w.completeFactorTwoChain n L data hn) =
        -rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) := by
    have hboundary :
        Koszul.dOne (terminalSourcePresentation n L data hn) 1
            (w.completeFactorTwoChain n L data hn) =
          -w.completeFactorTwoCutoffFullLabel n L data hn := by
      rw [← w.completeNormalFormFullLabelRead_eq_dOne_completeFactorTwoChain
        n L data hn]
      exact w.completeNormalFullLabel_eq_neg_cutoff n L data hn
    calc
      _ = -w.completeFactorTwoCutoffFullLabel n L data hn := hboundary
      _ = -rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) := by
            rw [w.rightSymbol_rawCompleteCutoffWord n L data hn]
  have hcycleBoundary :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (w.completeFactorTwoChain n L data hn + cutoffChain) = 0 := by
    rw [map_add, hcompleteBoundary, hcutoffBoundary]
    abel
  let cycle : Koszul.cyclesOne
      (terminalSourcePresentation n L data hn) 1 :=
    ⟨w.completeFactorTwoChain n L data hn + cutoffChain, hcycleBoundary⟩
  have hcombinedPrimitive :
      terminalSourcePrimitive n L data hn cycle.1 =
        pbwPrimitive n L data hn w.theta +
          ((w.completeFactorTwoPrimitiveCorrection n L data +
              cutoffRelation : Relations n L data) : FreeModel n L) := by
    change terminalSourcePrimitive n L data hn
        (w.completeFactorTwoChain n L data hn + cutoffChain) =
      pbwPrimitive n L data hn w.theta +
        ((w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L) +
          (cutoffRelation : FreeModel n L))
    rw [map_add,
      w.terminalSourcePrimitive_completeFactorTwoChain n L data hn,
      hcutoffPrimitive]
    have hstokes := w.rawPBWPrimitiveTheta_eq_complete_add_cutoff
      n L data hn
    calc
      w.completeFactorTwoFullLabelPrimitive n L data hn +
            (w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L) +
          (pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) +
            (cutoffRelation : FreeModel n L)) =
        (w.completeFactorTwoFullLabelPrimitive n L data hn +
            pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data)) +
          ((w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L) +
            (cutoffRelation : FreeModel n L)) := by abel
      _ = _ := by rw [← hstokes]
  let sourceRelation : Relations n L data :=
    w.terminalOneRelation n L data hn +
      w.completeFactorTwoPrimitiveCorrection n L data + cutoffRelation
  let sourcePrimitive : TopPreimage n L data :=
    w.externalPrimitivePreimage n L data hn +
      relationTopPreimage n L data sourceRelation
  have hsourceRelation : (sourceRelation : FreeModel n L) =
      w.terminalOnePrimitive n L data hn +
        (w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L) +
        (cutoffRelation : FreeModel n L) := by
    dsimp [sourceRelation]
    rw [w.terminalOneRelation_coe n L data hn]
  have hcutoffRelationCoe :
      (((w.completeFactorTwoPrimitiveCorrection n L data +
          cutoffRelation : Relations n L data)) : FreeModel n L) =
        (w.completeFactorTwoPrimitiveCorrection n L data : FreeModel n L) +
          (cutoffRelation : FreeModel n L) := rfl
  have hsource : (sourcePrimitive : FreeModel n L) =
      terminalSourcePrimitive n L data hn cycle.1 := by
    change (w.externalPrimitivePreimage n L data hn : FreeModel n L) +
        (sourceRelation : FreeModel n L) = _
    rw [hcombinedPrimitive,
      w.externalPrimitivePreimage_eq n L data hn,
      w.pbwPrimitive_theta_external n L data hn,
      hsourceRelation, hcutoffRelationCoe]
    abel
  have hcoordinate : terminalEval n L data sourcePrimitive =
      (w.externalMarkedWord n L data hn).value := by
    change terminalEval n L data
        (w.externalPrimitivePreimage n L data hn +
          relationTopPreimage n L data sourceRelation) = _
    rw [map_add, terminalEval_relationTopPreimage, add_zero]
    rfl
  exact w.eq_zero_of_terminalSourceCoordinate n L data hn cycle
    sourcePrimitive hsource hcoordinate


end

end LieRings.MetabelianVanishing
