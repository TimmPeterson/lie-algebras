import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge

/-!
# The occurrence frontier of the complete factor-two cutoff

The raw Stokes account in `CompleteFactorTwoPrimitiveBridge` records the UEA
word discarded whenever the quotient-weight collector reaches the top mark
above factor two.  This file retains the actual signed row occurrences which
produce that word.  In particular, the full relation, its placement, and the
top mark remain available to the continuation collector.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCompleteCutoffRowsFintype : Fintype L := Fintype.ofFinite L

/-- Exactly the rows discarded by the top-mark cutoff of the complete
factor-two collector. -/
def IsRawCompleteCutoffRow : QuotientWeightRow n L data → Prop
  | .ordinary _ => False
  | .marked left _ s right =>
      2 < left.length + 1 + right.length ∧ s.val = n + 1

/-- The single cutoff occurrence emitted at one collector node. -/
def rawCompleteCutoffRowsSeed
    (r : QuotientWeightRow n L data) :
    QuotientWeightRow n L data →₀ ℤ :=
  match r with
  | .ordinary _ => 0
  | .marked left rho s right =>
      if 2 < left.length + 1 + right.length ∧ s.val = n + 1 then
        Finsupp.single (.marked left rho s right) 1
      else 0

private def rawCompleteCutoffRowsTraceStep
    (r : QuotientWeightRow n L data)
    (rec : ∀ q, (completeFactorTwoCollector n L data).relation q r →
      QuotientWeightRow n L data →₀ ℤ) :
    QuotientWeightRow n L data →₀ ℤ :=
  rawCompleteCutoffRowsSeed n L data r +
    match h : (completeFactorTwoCollector n L data).expansion r with
    | none => 0
    | some qs => (qs.attach.map fun q ↦ q.1.1 •
        rec q.1.2
          ((completeFactorTwoCollector n L data).decreases h q.1 q.2)).sum

/-- The complete signed cutoff occurrence frontier below one row. -/
def rawCompleteCutoffRowsTrace
    (r : QuotientWeightRow n L data) :
    QuotientWeightRow n L data →₀ ℤ :=
  (completeFactorTwoCollector n L data).wellFounded.fix
    (rawCompleteCutoffRowsTraceStep n L data) r

theorem rawCompleteCutoffRowsTrace_eq
    (r : QuotientWeightRow n L data) :
    rawCompleteCutoffRowsTrace n L data r =
      rawCompleteCutoffRowsTraceStep n L data r
        (fun q _ ↦ rawCompleteCutoffRowsTrace n L data q) := by
  rw [rawCompleteCutoffRowsTrace,
    (completeFactorTwoCollector n L data).wellFounded.fix_eq]
  congr 1

private def rawCompleteCutoffRowsEvaluation :
    (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ]
      UEA ℤ (FreeModel n L) :=
  Finsupp.linearCombination ℤ
    (completeFactorTwoFullLabelWord n L data)

private theorem rawCompleteCutoffRowsEvaluation_seed
    (r : QuotientWeightRow n L data) :
    rawCompleteCutoffRowsEvaluation n L data
        (rawCompleteCutoffRowsSeed n L data r) =
      rawCompleteCutoffWordSeed n L data r := by
  classical
  cases r with
  | ordinary xs => rfl
  | marked left rho s right =>
      by_cases hcut :
          2 < left.length + 1 + right.length ∧ s.val = n + 1
      · simp [rawCompleteCutoffRowsSeed, rawCompleteCutoffWordSeed, hcut,
          rawCompleteCutoffRowsEvaluation]
      · simp [rawCompleteCutoffRowsSeed, rawCompleteCutoffWordSeed, hcut,
          rawCompleteCutoffRowsEvaluation]

/-- Evaluating the occurrence trace by its literal whole-relation labels
recovers the previously constructed raw cutoff word trace. -/
theorem rawCompleteCutoffRowsTrace_evaluation
    (r : QuotientWeightRow n L data) :
    rawCompleteCutoffRowsEvaluation n L data
        (rawCompleteCutoffRowsTrace n L data r) =
      rawCompleteCutoffWordTrace n L data r := by
  classical
  let C := completeFactorTwoCollector n L data
  induction r using C.wellFounded.induction with
  | h r ih =>
      rw [rawCompleteCutoffRowsTrace_eq,
        rawCompleteCutoffWordTrace_eq]
      change rawCompleteCutoffRowsEvaluation n L data
          (rawCompleteCutoffRowsSeed n L data r +
            match h : (completeFactorTwoCollector n L data).expansion r with
            | none => 0
            | some qs => (qs.attach.map fun q ↦ q.1.1 •
                rawCompleteCutoffRowsTrace n L data q.1.2).sum) =
        rawCompleteCutoffWordSeed n L data r +
          match h : (completeFactorTwoCollector n L data).expansion r with
          | none => 0
          | some qs => (qs.attach.map fun q ↦ q.1.1 •
              rawCompleteCutoffWordTrace n L data q.1.2).sum
      rw [map_add, rawCompleteCutoffRowsEvaluation_seed]
      cases hexp : C.expansion r with
      | none => simp only [map_zero, add_zero]
      | some rows =>
          rw [map_list_sum]
          apply congrArg (fun x ↦ rawCompleteCutoffWordSeed n L data r + x)
          apply congrArg List.sum
          rw [List.map_map]
          apply List.map_congr_left
          intro q hq
          change rawCompleteCutoffRowsEvaluation n L data
              (q.1.1 • rawCompleteCutoffRowsTrace n L data q.1.2) =
            q.1.1 • rawCompleteCutoffWordTrace n L data q.1.2
          rw [map_zsmul,
            ih q.1.2 (C.decreases hexp q.1 q.2)]

/-- Aggregate signed cutoff occurrences for the governing initial frontier. -/
def GoverningWitness.rawCompleteCutoffRows {a : L}
    (w : GoverningWitness n L data a) :
    QuotientWeightRow n L data →₀ ℤ :=
  (w.quotientWeightInitial n L data).sum (fun r z ↦
    z • rawCompleteCutoffRowsTrace n L data r)

/-- The aggregate occurrence frontier evaluates to the exact raw cutoff word
used in the primitive Stokes equation. -/
theorem GoverningWitness.rawCompleteCutoffRows_evaluation
    {a : L} (w : GoverningWitness n L data a) :
    (w.rawCompleteCutoffRows n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelWord n L data r) =
      w.rawCompleteCutoffWord n L data := by
  classical
  change rawCompleteCutoffRowsEvaluation n L data
      (w.rawCompleteCutoffRows n L data) = _
  rw [GoverningWitness.rawCompleteCutoffRows,
    GoverningWitness.rawCompleteCutoffWord, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul, rawCompleteCutoffRowsTrace_evaluation]

private theorem rawCompleteCutoffRowsSeed_apply_eq_zero_of_not
    (root target : QuotientWeightRow n L data)
    (htarget : ¬IsRawCompleteCutoffRow n L data target) :
    rawCompleteCutoffRowsSeed n L data root target = 0 := by
  classical
  cases root with
  | ordinary xs => rfl
  | marked left rho s right =>
      by_cases hcut :
          2 < left.length + 1 + right.length ∧ s.val = n + 1
      · have hne : target ≠ .marked left rho s right := by
          intro heq
          subst target
          exact htarget hcut
        simp [rawCompleteCutoffRowsSeed, hcut, hne]
      · simp [rawCompleteCutoffRowsSeed, hcut]

private theorem rawCompleteCutoffRowsTrace_apply_eq_zero_of_not
    (root target : QuotientWeightRow n L data)
    (htarget : ¬IsRawCompleteCutoffRow n L data target) :
    rawCompleteCutoffRowsTrace n L data root target = 0 := by
  classical
  let C := completeFactorTwoCollector n L data
  induction root using C.wellFounded.induction with
  | h root ih =>
      rw [rawCompleteCutoffRowsTrace_eq]
      unfold rawCompleteCutoffRowsTraceStep
      change (rawCompleteCutoffRowsSeed n L data root +
          match h : (completeFactorTwoCollector n L data).expansion root with
          | none => 0
          | some qs => (qs.attach.map fun q ↦ q.1.1 •
              rawCompleteCutoffRowsTrace n L data q.1.2).sum) target = 0
      rw [Finsupp.add_apply,
        rawCompleteCutoffRowsSeed_apply_eq_zero_of_not
          n L data root target htarget, zero_add]
      split
      · rfl
      · rename_i rows hexp
        change (Finsupp.lapply target :
            (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ] ℤ)
            ((rows.attach.map fun q ↦ q.1.1 •
              rawCompleteCutoffRowsTrace n L data q.1.2).sum) = 0
        rw [map_list_sum, List.map_map]
        apply List.sum_eq_zero
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨q, hq, rfl⟩ := hy
        change q.1.1 * rawCompleteCutoffRowsTrace n L data q.1.2 target = 0
        rw [ih q.1.2
          ((completeFactorTwoCollector n L data).decreases
            hexp q.1 q.2), mul_zero]

/-- Every row in the cutoff occurrence trace has the exact top-marked shape
at which the raw collector stopped. -/
theorem rawCompleteCutoffRowsTrace_isCutoff
    (root target : QuotientWeightRow n L data)
    (htarget : rawCompleteCutoffRowsTrace n L data root target ≠ 0) :
    IsRawCompleteCutoffRow n L data target := by
  by_contra hnot
  exact htarget
    (rawCompleteCutoffRowsTrace_apply_eq_zero_of_not
      n L data root target hnot)

/-- Aggregate support theorem in predicate form. -/
theorem GoverningWitness.rawCompleteCutoffRows_isCutoff
    {a : L} (w : GoverningWitness n L data a)
    (r : QuotientWeightRow n L data)
    (hr : w.rawCompleteCutoffRows n L data r ≠ 0) :
    IsRawCompleteCutoffRow n L data r := by
  classical
  by_contra hnot
  apply hr
  rw [GoverningWitness.rawCompleteCutoffRows, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change (w.quotientWeightInitial n L data root) *
      rawCompleteCutoffRowsTrace n L data root r = 0
  rw [rawCompleteCutoffRowsTrace_apply_eq_zero_of_not
      n L data root r hnot, mul_zero]

/-- Aggregate support theorem with the row fields exposed for downstream
pattern matching. -/
theorem GoverningWitness.rawCompleteCutoffRows_shape
    {a : L} (w : GoverningWitness n L data a)
    (r : QuotientWeightRow n L data)
    (hr : w.rawCompleteCutoffRows n L data r ≠ 0) :
    ∃ (left right : List (TriangularPBWIndex n L))
        (rho : Relations n L data),
      r = .marked left rho ⟨n + 1, by omega⟩ right ∧
        2 < left.length + 1 + right.length := by
  have hcut := w.rawCompleteCutoffRows_isCutoff n L data r hr
  cases r with
  | ordinary xs => exact hcut.elim
  | marked left rho s right =>
      rcases hcut with ⟨hlarge, hs⟩
      have hseq : s = ⟨n + 1, by omega⟩ := Fin.ext hs
      exact ⟨left, right, rho, by rw [hseq], hlarge⟩

/-! ## Provenance of the relation carried by a cutoff row -/

/-- A relation occurring in the raw cutoff is either already in the derived
tail, or is one of the original triangular relations whose Smith head has
zero-based weight zero.  The second alternative is the unique exceptional
family in the terminal calculation. -/
def RawCutoffRelationShape (rho : Relations n L data) : Prop :=
  (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 ∨
    ∃ tag : TriangularRelationIndex n L,
      tag.1.val = 0 ∧ rho = triangularRelationOfIndex n L data tag

/-- Row form of `RawCutoffRelationShape`; ordinary rows impose no relation
condition. -/
def RawCutoffRowShape : QuotientWeightRow n L data → Prop
  | .ordinary _ => True
  | .marked _ rho _ _ => RawCutoffRelationShape n L data rho

private theorem tail_one_of_tail_tag
    (tag : TriangularRelationIndex n L) (htag : tag.1.val ≠ 0) :
    (triangularRelationOfIndex n L data tag : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  have htail := triangularRelationOfIndex_mem_tail n L data tag
  rw [FreeMetabelian.Free.mem_tail_iff] at htail ⊢
  intro i hi
  exact htail i (by omega)

private theorem triangularRelationRightBracket_mem_tail_one_any
    (rho : Relations n L data) (v : TriangularPBWIndex n L) :
    (triangularRelationRightBracket n L data rho v : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  have hzero : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 0 := by
    rw [FreeMetabelian.Free.mem_tail_iff]
    intro i hi
    omega
  have hb := RelationContext.bracket_weightIncl_right_mem_tail n L
    (rho : FreeModel n L) 0 v.1.val v.1.isLt hzero
    (triangularPieceBasis n L data v.1.val v.1.isLt v.2)
  rw [FreeMetabelian.Free.mem_tail_iff] at hb ⊢
  intro i hi
  change ⁅(rho : FreeModel n L), triangularPBWBasis n L data v⁆ i = 0
  rw [triangularPBWBasis_apply]
  exact hb i (by omega)

theorem completeFactorTwoExpansion_preserves_rawCutoffRowShape
    {r : QuotientWeightRow n L data}
    {rows : List (ℤ × QuotientWeightRow n L data)}
    (hr : RawCutoffRowShape n L data r)
    (hexp : completeFactorTwoExpansion n L data r = some rows) :
    ∀ q ∈ rows, RawCutoffRowShape n L data q.2 := by
  classical
  intro q hq
  cases r with
  | ordinary xs =>
      simp only [completeFactorTwoExpansion] at hexp
      simp only [quotientWeightExpansion] at hexp
      split at hexp <;> try contradiction
      rename_i d hd
      rw [Option.some.injEq] at hexp
      subst rows
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · trivial
      · rw [quotientOrdinaryCorrection, List.mem_map] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        trivial
  | marked left rho s right =>
      simp only [RawCutoffRowShape] at hr
      simp only [completeFactorTwoExpansion] at hexp
      split at hexp
      · contradiction
      · rename_i hlarge
        simp only [quotientWeightExpansion] at hexp
        split at hexp
        · contradiction
        · rename_i hone
          split at hexp
          · rename_i hcut
            rw [Option.some.injEq] at hexp
            subst rows
            simp at hq
          · rename_i hcut
            split at hexp
            · rename_i v rest hright
              split at hexp
              · rename_i hv
                rw [Option.some.injEq] at hexp
                subst rows
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with rfl | rfl
                · exact hr
                · exact Or.inl
                    (triangularRelationRightBracket_mem_tail_one_any
                      n L data rho v)
              · rename_i hv
                rw [Option.some.injEq] at hexp
                subst rows
                simp only [List.mem_cons] at hq
                rcases hq with rfl | hq
                · exact hr
                · rw [quotientTruncationRows, List.mem_map] at hq
                  obtain ⟨p, hp, rfl⟩ := hq
                  trivial
            · rename_i hright
              rw [Option.some.injEq] at hexp
              subst rows
              simp only [List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact hr
              · rw [quotientTruncationRows, List.mem_map] at hq
                obtain ⟨p, hp, rfl⟩ := hq
                trivial

/-- Every supported row entering the complete factor-two collector has the
required relation provenance. -/
theorem GoverningWitness.quotientWeightInitial_rawCutoffRowShape_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (r : QuotientWeightRow n L data)
    (hr : w.quotientWeightInitial n L data r ≠ 0) :
    RawCutoffRowShape n L data r := by
  classical
  rw [GoverningWitness.quotientWeightInitial, Finsupp.sum_apply] at hr
  have hexists : ∃ p ∈ (w.triangularPlacedFrontier n L data).support,
      Finsupp.single (quotientWeightRowOfPlaced n L data p)
        (w.triangularPlacedFrontier n L data p) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun p hp ↦ hall p hp))
  obtain ⟨p, hp, hpr⟩ := hexists
  have hre : r = quotientWeightRowOfPlaced n L data p := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at hpr
  subst r
  simp only [quotientWeightRowOfPlaced, RawCutoffRowShape]
  by_cases htag : p.tag.1.val = 0
  · exact Or.inr ⟨p.tag, htag, rfl⟩
  · exact Or.inl (tail_one_of_tail_tag n L data p.tag htag)

/-- Relation provenance is inherited by every supported occurrence in the
recursive cutoff trace. -/
theorem rawCompleteCutoffRowsTrace_rawCutoffRowShape
    (root target : QuotientWeightRow n L data)
    (hroot : RawCutoffRowShape n L data root)
    (htarget : rawCompleteCutoffRowsTrace n L data root target ≠ 0) :
    RawCutoffRowShape n L data target := by
  classical
  let C := completeFactorTwoCollector n L data
  induction root using C.wellFounded.induction with
  | h root ih =>
      rw [rawCompleteCutoffRowsTrace_eq] at htarget
      unfold rawCompleteCutoffRowsTraceStep at htarget
      by_contra htargetShape
      apply htarget
      rw [Finsupp.add_apply]
      have hseed : rawCompleteCutoffRowsSeed n L data root target = 0 := by
        cases root with
        | ordinary xs => rfl
        | marked left rho s right =>
            by_cases hcut :
                2 < left.length + 1 + right.length ∧ s.val = n + 1
            · have hne : target ≠ .marked left rho s right := by
                intro heq
                subst target
                exact htargetShape hroot
              simp [rawCompleteCutoffRowsSeed, hcut, hne]
            · simp [rawCompleteCutoffRowsSeed, hcut]
      rw [hseed, zero_add]
      split
      · rfl
      · rename_i rows hexp
        change (Finsupp.lapply target :
            (QuotientWeightRow n L data →₀ ℤ) →ₗ[ℤ] ℤ)
            ((rows.attach.map fun q ↦ q.1.1 •
              rawCompleteCutoffRowsTrace n L data q.1.2).sum) = 0
        rw [map_list_sum, List.map_map]
        apply List.sum_eq_zero
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨q, hq, rfl⟩ := hy
        change q.1.1 * rawCompleteCutoffRowsTrace n L data q.1.2 target = 0
        have hqShape := completeFactorTwoExpansion_preserves_rawCutoffRowShape
          n L data hroot hexp q.1 q.2
        have htraceZero :
            rawCompleteCutoffRowsTrace n L data q.1.2 target = 0 := by
          by_contra htrace
          exact htargetShape
            (ih q.1.2 (C.decreases hexp q.1 q.2) hqShape htrace)
        rw [htraceZero, mul_zero]

/-- Aggregate cutoff support theorem: no relation of a third, untracked kind
can occur. -/
theorem GoverningWitness.rawCompleteCutoffRows_rawCutoffRowShape_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (r : QuotientWeightRow n L data)
    (hr : w.rawCompleteCutoffRows n L data r ≠ 0) :
    RawCutoffRowShape n L data r := by
  classical
  rw [GoverningWitness.rawCompleteCutoffRows, Finsupp.sum_apply] at hr
  by_contra hshape
  apply hr
  apply Finset.sum_eq_zero
  intro root hroot
  change w.quotientWeightInitial n L data root *
      rawCompleteCutoffRowsTrace n L data root r = 0
  by_cases hrootZero : w.quotientWeightInitial n L data root = 0
  · rw [hrootZero, zero_mul]
  · have hrootShape :=
        w.quotientWeightInitial_rawCutoffRowShape_of_ne
          n L data root hrootZero
    have htrace : rawCompleteCutoffRowsTrace n L data root r = 0 := by
      by_contra htrace
      exact hshape (rawCompleteCutoffRowsTrace_rawCutoffRowShape
        n L data root r hrootShape htrace)
    rw [htrace, mul_zero]

end

end LieRings.MetabelianVanishing
