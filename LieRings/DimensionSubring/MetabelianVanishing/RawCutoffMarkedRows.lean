import LieRings.DimensionSubring.MetabelianVanishing.RawCompleteCutoffRows
import LieRings.DimensionSubring.MetabelianVanishing.MarkedCollector

/-!
# Adapted marked rows for the raw cutoff frontier

The quotient-weight collector stops certain whole-relation rows above factor
two in the triangular PBW basis.  This file changes only the two ordinary
UEA words to the adapted PBW basis.  The distinguished entry remains the
same genuine full relation and remains in the same left/right placement.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffMarkedRowsFintype : Fintype L :=
  Fintype.ofFinite L

/-- Expand arbitrary UEA words on the two sides of a genuine full relation
into adapted ordered PBW words.  No commutation across the marked relation is
performed here. -/
def markedRowsAround
    (left : UEA ℤ (FreeModel n L)) (rho : Relations n L data)
    (right : UEA ℤ (FreeModel n L)) :
    MarkedRow n L data hn →₀ ℤ :=
  let B := adaptedWeightedBasis n L data hn
  (B.pbwEquiv.symm left).sum fun e z ↦
    (B.pbwEquiv.symm right).sum fun f t ↦
      Finsupp.single
        (.marked (exponentWord n L data hn e) rho
          ⟨n + 1, by omega⟩ (exponentWord n L data hn f)) (z * t)

private theorem pbw_sum_orderedMonomial
    (u : UEA ℤ (FreeModel n L)) :
    ((adaptedWeightedBasis n L data hn).pbwEquiv.symm u).sum
        (fun e z ↦ z • orderedMonomial ℤ (FreeModel n L)
          (AdaptedIndex n L data hn)
          (adaptedWeightedBasis n L data hn).basis e) = u := by
  let B := adaptedWeightedBasis n L data hn
  have hsum : (B.pbwEquiv.symm u).sum
      (fun e z ↦ MvPolynomial.monomial e z) = B.pbwEquiv.symm u := by
    simpa only [MvPolynomial.monomial] using
      (Finsupp.sum_single (B.pbwEquiv.symm u))
  calc
    _ = (B.pbwEquiv.symm u).sum
        (fun e z ↦ B.pbwEquiv (MvPolynomial.monomial e z)) := by
      apply Finsupp.sum_congr
      intro e he
      rw [B.pbwEquiv_monomial]
    _ = B.pbwEquiv ((B.pbwEquiv.symm u).sum
        (fun e z ↦ MvPolynomial.monomial e z)) := by
      rw [map_finsuppSum]
    _ = B.pbwEquiv (B.pbwEquiv.symm u) := by rw [hsum]
    _ = u := B.pbwEquiv.apply_symm_apply u

private theorem markedRow_value_exponentWords
    (rho : Relations n L data)
    (e f : AdaptedIndex n L data hn →₀ ℕ) :
    (MarkedRow.marked (exponentWord n L data hn e) rho
        ⟨n + 1, by omega⟩ (exponentWord n L data hn f) :
      MarkedRow n L data hn).value =
      orderedMonomial ℤ (FreeModel n L) (AdaptedIndex n L data hn)
          (adaptedWeightedBasis n L data hn).basis e *
        UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
        orderedMonomial ℤ (FreeModel n L) (AdaptedIndex n L data hn)
          (adaptedWeightedBasis n L data hn).basis f := by
  simp [MarkedRow.value, MarkedRow.basisWord, exponentWord,
    orderedMonomial, LieRings.PBW.basisWord, LieRings.PBW.word,
    List.map_map, Function.comp_def]

/-- Evaluating the adapted expansion recovers the literal placed product
`left * ι rho * right`. -/
theorem markedRowEvaluation_markedRowsAround
    (left : UEA ℤ (FreeModel n L)) (rho : Relations n L data)
    (right : UEA ℤ (FreeModel n L)) :
    markedRowEvaluation n L data hn
        (markedRowsAround n L data hn left rho right) =
      left * UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) * right := by
  classical
  let B := adaptedWeightedBasis n L data hn
  let lf := B.pbwEquiv.symm left
  let rf := B.pbwEquiv.symm right
  change markedRowEvaluation n L data hn
      (lf.sum fun e z ↦ rf.sum fun f t ↦
        Finsupp.single
          (.marked (exponentWord n L data hn e) rho
            ⟨n + 1, by omega⟩ (exponentWord n L data hn f)) (z * t)) = _
  rw [map_finsuppSum]
  change lf.sum (fun e z ↦ markedRowEvaluation n L data hn
      (rf.sum fun f t ↦ Finsupp.single
        (.marked (exponentWord n L data hn e) rho
          ⟨n + 1, by omega⟩ (exponentWord n L data hn f)) (z * t))) = _
  have hrows : lf.sum (fun e z ↦ markedRowEvaluation n L data hn
        (rf.sum fun f t ↦ Finsupp.single
          (.marked (exponentWord n L data hn e) rho
            ⟨n + 1, by omega⟩ (exponentWord n L data hn f)) (z * t))) =
      lf.sum (fun e z ↦ rf.sum (fun f t ↦
        (z * t) •
          (orderedMonomial ℤ (FreeModel n L)
              (AdaptedIndex n L data hn) B.basis e *
            UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
            orderedMonomial ℤ (FreeModel n L)
              (AdaptedIndex n L data hn) B.basis f))) := by
    apply Finsupp.sum_congr
    intro e he
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro f hf
    rw [markedRowEvaluation_single,
      markedRow_value_exponentWords n L data hn]
  rw [hrows]
  rw [← pbw_sum_orderedMonomial n L data hn left,
    ← pbw_sum_orderedMonomial n L data hn right]
  rw [Finsupp.sum_mul, Finsupp.sum_mul]
  apply Finsupp.sum_congr
  intro e he
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro f hf
  rw [smul_mul_assoc, smul_mul_smul]

/-- Adapt one quotient-weight row.  Ordinary rows are irrelevant to the raw
cutoff frontier and map to zero.  The numerical mark is intentionally ignored:
the output stores the same whole relation at the top mark. -/
def adaptedMarkedRowsOfQuotientWeightRow :
    QuotientWeightRow n L data → MarkedRow n L data hn →₀ ℤ
  | .ordinary _ => 0
  | .marked left rho _ right =>
      markedRowsAround n L data hn
        (QuotientWeightRow.basisWord n L data left) rho
        (QuotientWeightRow.basisWord n L data right)

/-- Rowwise exact evaluation of the adapted expansion by the whole-relation
label. -/
theorem markedRowEvaluation_adaptedMarkedRowsOfQuotientWeightRow
    (r : QuotientWeightRow n L data) :
    markedRowEvaluation n L data hn
        (adaptedMarkedRowsOfQuotientWeightRow n L data hn r) =
      completeFactorTwoFullLabelWord n L data r := by
  cases r with
  | ordinary xs => rfl
  | marked left rho s right =>
      exact markedRowEvaluation_markedRowsAround n L data hn
        (QuotientWeightRow.basisWord n L data left) rho
        (QuotientWeightRow.basisWord n L data right)

/-- Adapt the entire signed raw cutoff occurrence frontier. -/
def GoverningWitness.rawCompleteCutoffMarkedRows {a : L}
    (w : GoverningWitness n L data a) : MarkedRow n L data hn →₀ ℤ :=
  (w.rawCompleteCutoffRows n L data).sum fun r z ↦
    z • adaptedMarkedRowsOfQuotientWeightRow n L data hn r

/-- The aggregate adapted marked-row frontier evaluates to the exact raw
cutoff UEA word. -/
theorem GoverningWitness.rawCompleteCutoffMarkedRows_evaluation {a : L}
    (w : GoverningWitness n L data a) :
    markedRowEvaluation n L data hn
        (w.rawCompleteCutoffMarkedRows n L data hn) =
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [GoverningWitness.rawCompleteCutoffMarkedRows, map_finsuppSum]
  calc
    _ = (w.rawCompleteCutoffRows n L data).sum (fun r z ↦
        z • completeFactorTwoFullLabelWord n L data r) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul,
        markedRowEvaluation_adaptedMarkedRowsOfQuotientWeightRow]
    _ = _ := w.rawCompleteCutoffRows_evaluation n L data

/-! ## Relation provenance through the basis change -/

/-- Row form of the cutoff relation-shape invariant after changing the
ordinary words to the adapted PBW basis. -/
def RawCutoffMarkedRelationShape : MarkedRow n L data hn → Prop
  | .ordinary _ => True
  | .marked _ rho _ _ => RawCutoffRelationShape n L data rho

private theorem adaptedMarkedRowsOfQuotientWeightRow_preserves_relationShape
    (r : QuotientWeightRow n L data)
    (hr : RawCutoffRowShape n L data r)
    (q : MarkedRow n L data hn)
    (hq : adaptedMarkedRowsOfQuotientWeightRow n L data hn r q ≠ 0) :
    RawCutoffMarkedRelationShape n L data hn q := by
  classical
  cases r with
  | ordinary xs => simp [adaptedMarkedRowsOfQuotientWeightRow] at hq
  | marked left rho s right =>
      simp only [RawCutoffRowShape] at hr
      rw [adaptedMarkedRowsOfQuotientWeightRow, markedRowsAround,
        Finsupp.sum_apply] at hq
      have he : ∃ e ∈
          ((adaptedWeightedBasis n L data hn).pbwEquiv.symm
            (QuotientWeightRow.basisWord n L data left)).support,
          (((adaptedWeightedBasis n L data hn).pbwEquiv.symm
            (QuotientWeightRow.basisWord n L data right)).sum fun f t ↦
              Finsupp.single
                (.marked (exponentWord n L data hn e) rho
                  ⟨n + 1, by omega⟩ (exponentWord n L data hn f))
                (((adaptedWeightedBasis n L data hn).pbwEquiv.symm
                    (QuotientWeightRow.basisWord n L data left)) e * t)) q ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hq (Finset.sum_eq_zero (fun e he ↦ hall e he))
      obtain ⟨e, he, heq⟩ := he
      rw [Finsupp.sum_apply] at heq
      have hf : ∃ f ∈
          ((adaptedWeightedBasis n L data hn).pbwEquiv.symm
            (QuotientWeightRow.basisWord n L data right)).support,
          Finsupp.single
              (.marked (exponentWord n L data hn e) rho
                ⟨n + 1, by omega⟩ (exponentWord n L data hn f))
              (((adaptedWeightedBasis n L data hn).pbwEquiv.symm
                  (QuotientWeightRow.basisWord n L data left)) e *
                ((adaptedWeightedBasis n L data hn).pbwEquiv.symm
                  (QuotientWeightRow.basisWord n L data right)) f) q ≠ 0 := by
        by_contra hall
        push Not at hall
        exact heq (Finset.sum_eq_zero (fun f hf ↦ hall f hf))
      obtain ⟨f, hf, hfq⟩ := hf
      have hrow : q = .marked (exponentWord n L data hn e) rho
          ⟨n + 1, by omega⟩ (exponentWord n L data hn f) := by
        by_contra hne
        simp [Finsupp.single_apply, hne] at hfq
      subst q
      exact hr

/-- Every adapted raw-cutoff row still carries either a derived-tail
relation or the original weight-one triangular relation. -/
theorem GoverningWitness.rawCompleteCutoffMarkedRows_relationShape_of_ne
    {a : L} (w : GoverningWitness n L data a)
    (r : MarkedRow n L data hn)
    (hr : w.rawCompleteCutoffMarkedRows n L data hn r ≠ 0) :
    RawCutoffMarkedRelationShape n L data hn r := by
  classical
  rw [GoverningWitness.rawCompleteCutoffMarkedRows,
    Finsupp.sum_apply] at hr
  have hexists : ∃ q ∈ (w.rawCompleteCutoffRows n L data).support,
      (w.rawCompleteCutoffRows n L data q •
        adaptedMarkedRowsOfQuotientWeightRow n L data hn q) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun q hq ↦ hall q hq))
  obtain ⟨q, hq, hqr⟩ := hexists
  have hqcoeff : w.rawCompleteCutoffRows n L data q ≠ 0 :=
    Finsupp.mem_support_iff.mp hq
  have hrow : adaptedMarkedRowsOfQuotientWeightRow n L data hn q r ≠ 0 := by
    intro hz
    simp [hz] at hqr
  exact adaptedMarkedRowsOfQuotientWeightRow_preserves_relationShape
    n L data hn q
      (w.rawCompleteCutoffRows_rawCutoffRowShape_of_ne
        n L data q hqcoeff) r hrow

end

end LieRings.MetabelianVanishing
