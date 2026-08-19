import LieRings.DimensionSubring.MetabelianVanishing.ClosedSquare
import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmith

/-!
# The full-label terminal provenance ledger

The contextual collector evaluates a marked row using a truncation of its
stored root relation.  For the terminal factor-two argument we also need the
second, purely formal read in which the *whole contextual relation* is kept as
the label.  The marked truncation rule transfers this label from mark `1` to
the component branch; consequently this read is preserved exactly by every
rewrite step.
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

local instance provenanceLedgerFintype : Fintype L := Fintype.ofFinite L

/-! ## The literal whole-relation read -/

/-- Put the genuine full contextual relation at the displayed placement. -/
def contextualFullRelationWord
    (rho : Relations n L data) (c : RelationContext n L data hn)
    (left right : List (AdaptedIndex n L data hn)) :
    UEA ℤ (FreeModel n L) :=
  MarkedRow.basisWord n L data hn left *
    UniversalEnvelopingAlgebra.ι ℤ
      (RelationContext.relation n L data hn c rho : FreeModel n L) *
    MarkedRow.basisWord n L data hn right

/-- The manuscript's full-label read.  A positive marked row carries its
whole contextual relation.  At the last truncation step the label passes to
the mark-one component row. -/
def provenancedFullLabelWord : ProvenancedRow n L data hn →
    UEA ℤ (FreeModel n L)
  | .marked rho c k left right =>
      if k.val = 0 then 0 else
        contextualFullRelationWord n L data hn rho c left right
  | .component rho c k left right =>
      if k.val = 1 then
        contextualFullRelationWord n L data hn rho c left right
      else 0

/-- Exact terminal factor-two symbol of the full-label word. -/
def provenancedFullLabelRead (r : ProvenancedRow n L data hn) :
    Sym[ℤ] (Fin 2) (A L n) :=
  rightSymbol n L data hn 2 n (by omega)
    (provenancedFullLabelWord n L data hn r)

/-! ## One-step preservation -/

/-- Every contextual rewrite preserves the whole-relation label in the UEA.
The only non-transfer case is truncation: above mark one the label stays on
the marked child, while at mark one it moves to the component child. -/
theorem provenancedExpansion_preserves_fullLabelWord
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    (qs.map fun q ↦ q.1 • provenancedFullLabelWord n L data hn q.2).sum =
      provenancedFullLabelWord n L data hn r := by
  classical
  cases r with
  | component rho c k left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        have hleftEq : left = leftRev.reverse ++ [x] := by
          have hr := congrArg List.reverse hleft
          simpa using hr
        by_cases hk : k.val = 1
        · simp only [List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, one_smul, neg_one_smul, add_zero]
          simp only [provenancedFullLabelWord, hk, if_pos]
          rw [hleftEq]
          simp only [contextualFullRelationWord, MarkedRow.basisWord,
            LieRings.PBW.basisWord, LieRings.PBW.word, List.map_append,
            List.map_cons, List.map_singleton, List.map_nil,
            List.prod_append, List.prod_cons, List.prod_singleton,
            List.prod_nil, mul_one]
          let R : FreeModel n L :=
            RelationContext.relation n L data hn c rho
          let xv : FreeModel n L :=
            (adaptedWeightedBasis n L data hn).basis x
          have hcontext :
              (RelationContext.relation n L data hn
                  (RelationContext.lieRight c x) rho : FreeModel n L) =
                ⁅R, xv⁆ := by
            rfl
          rw [hcontext]
          have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
            (FreeModel n L) R xv
          rw [← sub_eq_add_neg]
          change
            MarkedRow.basisWord n L data hn leftRev.reverse *
                  UniversalEnvelopingAlgebra.ι ℤ R *
                  (UniversalEnvelopingAlgebra.ι ℤ xv *
                    MarkedRow.basisWord n L data hn right) -
                MarkedRow.basisWord n L data hn leftRev.reverse *
                  UniversalEnvelopingAlgebra.ι ℤ ⁅R, xv⁆ *
                  MarkedRow.basisWord n L data hn right =
              (MarkedRow.basisWord n L data hn leftRev.reverse *
                  UniversalEnvelopingAlgebra.ι ℤ xv) *
                UniversalEnvelopingAlgebra.ι ℤ R *
                MarkedRow.basisWord n L data hn right
          calc
            _ = MarkedRow.basisWord n L data hn leftRev.reverse *
                (UniversalEnvelopingAlgebra.ι ℤ R *
                    UniversalEnvelopingAlgebra.ι ℤ xv -
                  UniversalEnvelopingAlgebra.ι ℤ ⁅R, xv⁆) *
                MarkedRow.basisWord n L data hn right := by noncomm_ring
            _ = MarkedRow.basisWord n L data hn leftRev.reverse *
                (UniversalEnvelopingAlgebra.ι ℤ xv *
                  UniversalEnvelopingAlgebra.ι ℤ R) *
                MarkedRow.basisWord n L data hn right := by
                  rw [hswap]
                  noncomm_ring
            _ = _ := by noncomm_ring
        · simp [provenancedFullLabelWord, hk]
  | marked rho c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          by_cases hk : k.val = 0
          · have hkfin : k = ⟨0, by omega⟩ := Fin.ext hk
            rw [hkfin]
            simp [provenancedFullLabelWord]
          · simp only [List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, one_smul, add_zero]
            simp only [provenancedFullLabelWord, hk, if_false]
            simp only [contextualFullRelationWord, MarkedRow.basisWord,
              LieRings.PBW.basisWord, LieRings.PBW.word, List.map_append,
              List.map_cons, List.map_singleton, List.map_nil,
              List.prod_append, List.prod_cons, List.prod_singleton,
              List.prod_nil, mul_one]
            let R : FreeModel n L :=
              RelationContext.relation n L data hn c rho
            let xv : FreeModel n L :=
              (adaptedWeightedBasis n L data hn).basis x
            have hcontext :
                (RelationContext.relation n L data hn
                    (RelationContext.lieRight c x) rho : FreeModel n L) =
                  ⁅R, xv⁆ := by
              rfl
            rw [hcontext]
            have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
              (FreeModel n L) R xv
            change
              (MarkedRow.basisWord n L data hn left *
                    UniversalEnvelopingAlgebra.ι ℤ xv) *
                    UniversalEnvelopingAlgebra.ι ℤ R *
                    MarkedRow.basisWord n L data hn right +
                  MarkedRow.basisWord n L data hn left *
                    UniversalEnvelopingAlgebra.ι ℤ ⁅R, xv⁆ *
                    MarkedRow.basisWord n L data hn right =
                MarkedRow.basisWord n L data hn left *
                  UniversalEnvelopingAlgebra.ι ℤ R *
                  (UniversalEnvelopingAlgebra.ι ℤ xv *
                    MarkedRow.basisWord n L data hn right)
            calc
              _ = MarkedRow.basisWord n L data hn left *
                  (UniversalEnvelopingAlgebra.ι ℤ xv *
                      UniversalEnvelopingAlgebra.ι ℤ R +
                    UniversalEnvelopingAlgebra.ι ℤ ⁅R, xv⁆) *
                  MarkedRow.basisWord n L data hn right := by noncomm_ring
              _ = MarkedRow.basisWord n L data hn left *
                  (UniversalEnvelopingAlgebra.ι ℤ R *
                    UniversalEnvelopingAlgebra.ι ℤ xv) *
                  MarkedRow.basisWord n L data hn right := by rw [← hswap]
              _ = _ := by noncomm_ring
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rename_i hk
            rw [Option.some.injEq] at h
            subst qs
            simp [provenancedFullLabelWord, hk]
          · rename_i hk
            split at h
            · contradiction
            · rw [Option.some.injEq] at h
              subst qs
              have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
              by_cases hkone : k.val = 1
              · have hpred : k.val - 1 = 0 := by omega
                simp [provenancedFullLabelWord, hk, hkone, hpred]
              · have hpred : k.val - 1 ≠ 0 := by omega
                simp [provenancedFullLabelWord, hk, hkone, hpred]

/-- The requested factor-two full-label read is preserved by one rewrite. -/
theorem provenancedExpansion_preserves_fullLabelRead
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    (qs.map fun q ↦ q.1 • provenancedFullLabelRead n L data hn q.2).sum =
      provenancedFullLabelRead n L data hn r := by
  simp only [provenancedFullLabelRead]
  simp_rw [← map_zsmul]
  calc
    _ = ((qs.map fun q ↦
          q.1 • provenancedFullLabelWord n L data hn q.2).map
            (rightSymbol n L data hn 2 n (by omega))).sum := by
          rw [List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro q hq
          rfl
    _ = (rightSymbol n L data hn 2 n (by omega))
          ((qs.map fun q ↦
            q.1 • provenancedFullLabelWord n L data hn q.2).sum) := by
          rw [map_list_sum]
    _ = _ := congrArg (rightSymbol n L data hn 2 n (by omega))
      (provenancedExpansion_preserves_fullLabelWord n L data hn h)

/-! ## Global preservation of the full-label read -/

/-- The same deterministic rewrite tree, evaluated by its full contextual
relation labels. -/
def provenancedFullLabelCollector :
    LieRings.DegreeFive.FiniteTaggedCollector
      (ProvenancedRow n L data hn) (UEA ℤ (FreeModel n L)) :=
  { provenancedCollector n L data hn with
    value := provenancedFullLabelWord n L data hn
    preserves := provenancedExpansion_preserves_fullLabelWord n L data hn }

@[simp] theorem provenancedFullLabelCollector_normalForm
    (r : ProvenancedRow n L data hn) :
    (provenancedFullLabelCollector n L data hn).normalForm r =
      (provenancedCollector n L data hn).normalForm r := rfl

theorem provenancedFullLabelCollector_evaluate
    (r : ProvenancedRow n L data hn) :
    (provenancedFullLabelCollector n L data hn).evaluate
        ((provenancedCollector n L data hn).normalForm r) =
      provenancedFullLabelWord n L data hn r := by
  rw [← provenancedFullLabelCollector_normalForm n L data hn r]
  exact LieRings.DegreeFive.FiniteTaggedCollector.evaluate_normalForm _ r

theorem evaluateFullLabel_provenancedRowsOfRightFactor
    (rho : Relations n L data) (u : UEA ℤ (FreeModel n L)) :
    (provenancedFullLabelCollector n L data hn).evaluate
        (provenancedRowsOfRightFactor n L data hn rho u) =
      UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) * u := by
  classical
  rw [← evaluate_provenancedRowsOfRightFactor n L data hn rho u]
  change Finsupp.linearCombination ℤ
      (provenancedFullLabelWord n L data hn)
        (provenancedRowsOfRightFactor n L data hn rho u) =
    Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
      (provenancedRowsOfRightFactor n L data hn rho u)
  rw [provenancedRowsOfRightFactor, map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro e he
  rw [Finsupp.linearCombination_single,
    Finsupp.linearCombination_single]
  congr 1
  simp [provenancedFullLabelWord, contextualFullRelationWord,
    ProvenancedRow.value, RelationContext.markedPrefix,
    RelationContext.relation, rowTruncation_top]

theorem GoverningWitness.evaluateFullLabel_provenancedInitial {a : L}
    (w : GoverningWitness n L data a) :
    (provenancedFullLabelCollector n L data hn).evaluate
        (GoverningWitness.provenancedInitial n L data hn w) = w.theta := by
  classical
  rw [GoverningWitness.provenancedInitial, map_finsuppSum,
    GoverningWitness.theta]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul,
    evaluateFullLabel_provenancedRowsOfRightFactor n L data hn]

theorem GoverningWitness.evaluateFullLabel_provenancedFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (provenancedFullLabelCollector n L data hn).evaluate
        (GoverningWitness.provenancedFrontier n L data hn w) = w.theta := by
  classical
  rw [GoverningWitness.provenancedFrontier, map_finsuppSum]
  calc
    _ = (provenancedFullLabelCollector n L data hn).evaluate
        (GoverningWitness.provenancedInitial n L data hn w) := by
      change (GoverningWitness.provenancedInitial n L data hn w).sum
          (fun r z ↦ (provenancedFullLabelCollector n L data hn).evaluate
            (z • (provenancedCollector n L data hn).normalForm r)) =
        (GoverningWitness.provenancedInitial n L data hn w).sum
          (fun r z ↦ z • provenancedFullLabelWord n L data hn r)
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul, provenancedFullLabelCollector_evaluate]
    _ = w.theta := w.evaluateFullLabel_provenancedInitial n L data hn

/-- The full-label factor-two symbol of the terminal contextual frontier is
the factor-two symbol of the original governing element. -/
theorem GoverningWitness.rightSymbol_fullLabel_provenancedFrontier {a : L}
    (w : GoverningWitness n L data a) :
    (GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • provenancedFullLabelRead n L data hn r) =
      rightSymbol n L data hn 2 n (by omega) w.theta := by
  have h := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.evaluateFullLabel_provenancedFrontier n L data hn)
  change rightSymbol n L data hn 2 n (by omega)
      ((GoverningWitness.provenancedFrontier n L data hn w).sum
        (fun r z ↦ z • provenancedFullLabelWord n L data hn r)) =
    rightSymbol n L data hn 2 n (by omega) w.theta at h
  rw [map_finsuppSum] at h
  simpa only [map_zsmul, provenancedFullLabelRead] using h

/-! ## The mark-one trace ledger -/

/-- The full contextual relation charged to a truncation cell precisely when
that cell has mark one.  This is the label transferred to its component child
by the final truncation step. -/
def ProvenancedCell.markOneFullLabelRead
    (c : ProvenancedCell n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  if c.mark.val = 1 then
    rightSymbol n L data hn 2 n (by omega)
      (contextualFullRelationWord n L data hn
        c.root c.context c.left [])
  else 0

/-- A row contributes to the internal full-label ledger exactly when it is a
mark-one component row. -/
def provenancedComponentFullLabelSeed
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  match r with
  | .marked _ _ _ _ _ => 0
  | .component rho c k left right =>
      if k.val = 1 then
        rightSymbol n L data hn 2 n (by omega)
          (contextualFullRelationWord n L data hn rho c left right)
      else 0

/-- Mark-one component labels in all terminal leaves below one row. -/
def normalFormProvenancedComponentFullLabelRead
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  ((provenancedCollector n L data hn).normalForm r).sum
    (fun s z ↦ z • provenancedComponentFullLabelSeed n L data hn s)

/-- Mark-one full labels recorded by every truncation cell below one row. -/
def provenancedTraceMarkOneFullLabelRead
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  (provenancedTrace n L data hn r).sum
    (fun c z ↦ z • c.markOneFullLabelRead n L data hn)

private def provenancedComponentFullLabelLinear :
    (ProvenancedRow n L data hn →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ
    (provenancedComponentFullLabelSeed n L data hn)

private def provenancedCellFullLabelLinear :
    (ProvenancedCell n L data hn →₀ ℤ) →ₗ[ℤ]
      Sym[ℤ] (Fin 2) (A L n) :=
  Finsupp.linearCombination ℤ
    (fun c ↦ c.markOneFullLabelRead n L data hn)

private def provenancedCellFullLabelSeed
    (r : ProvenancedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  match provenancedCell? n L data hn r with
  | none => 0
  | some c => c.markOneFullLabelRead n L data hn

/-- Local Stokes identity for the mark-one ledger.  On the last truncation,
the cell label is exactly the label of the newly emitted component row. -/
private theorem provenancedExpansion_componentFullLabel
    {r : ProvenancedRow n L data hn}
    {qs : List (ℤ × ProvenancedRow n L data hn)}
    (h : provenancedExpansion n L data hn r = some qs) :
    (qs.map (fun q ↦ q.1 •
      provenancedComponentFullLabelSeed n L data hn q.2)).sum =
      provenancedComponentFullLabelSeed n L data hn r +
        provenancedCellFullLabelSeed n L data hn r := by
  classical
  have hfull := provenancedExpansion_preserves_fullLabelRead
    n L data hn h
  cases r with
  | component rho c k left right =>
      simp only [provenancedExpansion] at h
      split at h
      · contradiction
      · rename_i x leftRev hleft
        rw [Option.some.injEq] at h
        subst qs
        by_cases hk : k.val = 1
        · simpa [provenancedComponentFullLabelSeed,
            provenancedCellFullLabelSeed, provenancedCell?,
            provenancedFullLabelRead, provenancedFullLabelWord, hk] using hfull
        · simp [provenancedComponentFullLabelSeed,
            provenancedCellFullLabelSeed, provenancedCell?, hk]
  | marked rho c k left right =>
      cases right with
      | cons x right =>
          simp only [provenancedExpansion] at h
          rw [Option.some.injEq] at h
          subst qs
          simp [provenancedComponentFullLabelSeed,
            provenancedCellFullLabelSeed, provenancedCell?]
      | nil =>
          simp only [provenancedExpansion] at h
          split at h
          · rename_i hk
            rw [Option.some.injEq] at h
            subst qs
            simp [provenancedComponentFullLabelSeed,
              provenancedCellFullLabelSeed, provenancedCell?, hk]
          · rename_i hk
            split at h
            · contradiction
            · rename_i hw
              rw [Option.some.injEq] at h
              subst qs
              have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
              have hcell : provenancedCell? n L data hn
                  (.marked rho c k left []) =
                    some ⟨rho, c, k, left, hkpos, by simpa using hw⟩ := by
                simp [provenancedCell?, hkpos, hw]
              by_cases hkone : k.val = 1
              · simp [provenancedComponentFullLabelSeed,
                  provenancedCellFullLabelSeed, hcell,
                  ProvenancedCell.markOneFullLabelRead, hkone]
              · simp [provenancedComponentFullLabelSeed,
                  provenancedCellFullLabelSeed, hcell,
                  ProvenancedCell.markOneFullLabelRead, hkone]

private theorem provenancedFullLabelCell?_eq_none_of_expansion_eq_none
    (r : ProvenancedRow n L data hn)
    (h : provenancedExpansion n L data hn r = none) :
    provenancedCell? n L data hn r = none := by
  classical
  cases r with
  | component rho c k left right => rfl
  | marked rho c k left right =>
      cases right with
      | cons x right => simp [provenancedCell?]
      | nil =>
          by_cases hk : 0 < k.val
          · by_cases hw : provenancedWall n L data hn c k left = false
            · exfalso
              have hne : provenancedExpansion n L data hn
                  (.marked rho c k left []) ≠ none := by
                simp [provenancedExpansion, Nat.ne_of_gt hk, hw]
              exact hne h
            · simp [provenancedCell?, hk, hw]
          · simp [provenancedCell?, hk]

private theorem sum_smul_add_provenancedFullLabel
    (qs : List (ℤ × ProvenancedRow n L data hn)) :
    (qs.map (fun q ↦ q.1 •
      (provenancedComponentFullLabelSeed n L data hn q.2 +
        provenancedTraceMarkOneFullLabelRead n L data hn q.2))).sum =
      (qs.map (fun q ↦ q.1 •
        provenancedComponentFullLabelSeed n L data hn q.2)).sum +
      (qs.map (fun q ↦ q.1 •
        provenancedTraceMarkOneFullLabelRead n L data hn q.2)).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons, smul_add]
      simp only [smul_add] at ih
      rw [ih]
      module

/-- Full-label Stokes identity along the complete contextual trace.  Thus the
sum of all terminal mark-one components is exactly the sum of the mark-one
truncation labels (up to a possible component already present at the root). -/
theorem normalFormProvenancedComponentFullLabelRead_eq_trace
    (r : ProvenancedRow n L data hn) :
    normalFormProvenancedComponentFullLabelRead n L data hn r =
      provenancedComponentFullLabelSeed n L data hn r +
        provenancedTraceMarkOneFullLabelRead n L data hn r := by
  classical
  let C := provenancedCollector n L data hn
  induction r using C.wellFounded.induction with
  | h r ih =>
      cases hexp : provenancedExpansion n L data hn r with
      | none =>
          have hcell :=
            provenancedFullLabelCell?_eq_none_of_expansion_eq_none
              n L data hn r hexp
          rw [normalFormProvenancedComponentFullLabelRead,
            C.normalForm_eq_single_of_terminal hexp,
            provenancedTraceMarkOneFullLabelRead,
            provenancedTrace_eq_of_expansion_none n L data hn r hexp]
          simp [provenancedComponentFullLabelSeed, hcell]
      | some qs =>
          have hnf :
              normalFormProvenancedComponentFullLabelRead n L data hn r =
                (qs.map (fun q ↦ q.1 •
                  normalFormProvenancedComponentFullLabelRead
                    n L data hn q.2)).sum := by
            change provenancedComponentFullLabelLinear n L data hn
              (C.normalForm r) = _
            rw [C.normalForm_eq_sum_of_expansion r qs hexp, map_list_sum]
            simp only [List.map_map, Function.comp_apply]
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            change provenancedComponentFullLabelLinear n L data hn
                (q.1 • C.normalForm q.2) =
              q.1 • normalFormProvenancedComponentFullLabelRead
                n L data hn q.2
            rw [map_zsmul]
            rfl
          have hhere : provenancedCellFullLabelLinear n L data hn
                (match provenancedCell? n L data hn r with
                | none => 0
                | some c => Finsupp.single c 1) =
              provenancedCellFullLabelSeed n L data hn r := by
            cases hc : provenancedCell? n L data hn r <;>
              simp [provenancedCellFullLabelSeed, hc,
                provenancedCellFullLabelLinear]
            all_goals module
          have htrace :
              provenancedTraceMarkOneFullLabelRead n L data hn r =
                provenancedCellFullLabelSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    provenancedTraceMarkOneFullLabelRead
                      n L data hn q.2)).sum := by
            change provenancedCellFullLabelLinear n L data hn
              (provenancedTrace n L data hn r) = _
            rw [provenancedTrace_eq_of_expansion_some
              n L data hn r qs hexp, map_add, map_list_sum]
            have hchildren :
                ((qs.attach.map fun q ↦ q.1.1 •
                    provenancedTrace n L data hn q.1.2).map
                  (provenancedCellFullLabelLinear n L data hn)).sum =
                  (qs.attach.map fun q ↦ q.1.1 •
                    provenancedTraceMarkOneFullLabelRead
                      n L data hn q.1.2).sum := by
              apply congrArg List.sum
              rw [List.map_map]
              apply List.map_congr_left
              intro q hq
              change provenancedCellFullLabelLinear n L data hn
                    (q.1.1 • provenancedTrace n L data hn q.1.2) =
                  q.1.1 • provenancedTraceMarkOneFullLabelRead
                    n L data hn q.1.2
              rw [map_zsmul]
              rfl
            calc
              _ = provenancedCellFullLabelSeed n L data hn r +
                  (qs.attach.map fun q ↦ q.1.1 •
                    provenancedTraceMarkOneFullLabelRead
                      n L data hn q.1.2).sum :=
                congrArg₂ (· + ·) hhere hchildren
              _ = provenancedCellFullLabelSeed n L data hn r +
                  (qs.map (fun q ↦ q.1 •
                    provenancedTraceMarkOneFullLabelRead
                      n L data hn q.2)).sum := by
                congr 1
                exact congrArg List.sum
                  (List.attach_map_val (l := qs)
                    (f := fun q ↦ q.1 •
                      provenancedTraceMarkOneFullLabelRead
                        n L data hn q.2))
          have hih :
              (qs.map (fun q ↦ q.1 •
                normalFormProvenancedComponentFullLabelRead
                  n L data hn q.2)).sum =
                (qs.map (fun q ↦ q.1 •
                  (provenancedComponentFullLabelSeed n L data hn q.2 +
                    provenancedTraceMarkOneFullLabelRead
                      n L data hn q.2))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro q hq
            rw [ih q.2 (C.decreases hexp q hq)]
          have hsplit := sum_smul_add_provenancedFullLabel
            n L data hn qs
          have hlocal := provenancedExpansion_componentFullLabel
            n L data hn hexp
          rw [hnf, hih, hsplit, hlocal, htrace]
          abel

end

end LieRings.MetabelianVanishing
