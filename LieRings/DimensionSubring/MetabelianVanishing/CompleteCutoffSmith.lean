import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffMarkedRows
import LieRings.DimensionSubring.MetabelianVanishing.StepSeven

/-!
# Continuation of the complete cutoff frontier

The factor-first collector leaves a signed family of top-marked, genuine
full-relation rows above factor two.  This file continues precisely those
occurrences with the manuscript's deterministic marked collector.  The
resulting ordinary factor-one and factor-two reads, the two retained marked
placements, and the whole factor-one relations are all read from one common
frontier.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeCutoffSmithFintype : Fintype L :=
  Fintype.ofFinite L

/-! ## The common continued frontier -/

/-- Continue every signed raw cutoff occurrence through the exact marked
collector. -/
def GoverningWitness.rawCutoffClosedSquareFrontier {a : L}
    (w : GoverningWitness n L data a) : MarkedRow n L data hn →₀ ℤ :=
  (w.rawCompleteCutoffMarkedRows n L data hn).sum fun r z ↦
    z • (closedSquareCollector n L data hn).normalForm r

/-- Continuing the cutoff rows preserves their literal aggregate UEA word. -/
theorem GoverningWitness.rawCutoffClosedSquareFrontier_evaluation {a : L}
    (w : GoverningWitness n L data a) :
    markedRowEvaluation n L data hn
        (w.rawCutoffClosedSquareFrontier n L data hn) =
      w.rawCompleteCutoffWord n L data := by
  classical
  rw [GoverningWitness.rawCutoffClosedSquareFrontier, map_finsuppSum]
  calc
    _ = markedRowEvaluation n L data hn
        (w.rawCompleteCutoffMarkedRows n L data hn) := by
      change (w.rawCompleteCutoffMarkedRows n L data hn).sum
          (fun r z ↦ (closedSquareCollector n L data hn).evaluate
            (z • (closedSquareCollector n L data hn).normalForm r)) =
        (w.rawCompleteCutoffMarkedRows n L data hn).sum
          (fun r z ↦ z • MarkedRow.value n L data hn r)
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul]
      rw [closedSquareCollector_evaluate]
    _ = _ := w.rawCompleteCutoffMarkedRows_evaluation n L data hn

private theorem markedRowsAround_reachable_of_ne
    (left : UEA ℤ (FreeModel n L)) (rho : Relations n L data)
    (right : UEA ℤ (FreeModel n L)) (r : MarkedRow n L data hn)
    (hr : markedRowsAround n L data hn left rho right r ≠ 0) :
    ClosedSquareReachable n L data hn r := by
  classical
  rw [markedRowsAround, Finsupp.sum_apply] at hr
  have he : ∃ e ∈ ((adaptedWeightedBasis n L data hn).pbwEquiv.symm left).support,
      (((adaptedWeightedBasis n L data hn).pbwEquiv.symm right).sum fun f t ↦
        Finsupp.single
          (.marked (exponentWord n L data hn e) rho
            ⟨n + 1, by omega⟩ (exponentWord n L data hn f))
          (((adaptedWeightedBasis n L data hn).pbwEquiv.symm left) e * t)) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun e he ↦ hall e he))
  obtain ⟨e, he, her⟩ := he
  rw [Finsupp.sum_apply] at her
  have hf : ∃ f ∈ ((adaptedWeightedBasis n L data hn).pbwEquiv.symm right).support,
      Finsupp.single
        (.marked (exponentWord n L data hn e) rho
          ⟨n + 1, by omega⟩ (exponentWord n L data hn f))
        (((adaptedWeightedBasis n L data hn).pbwEquiv.symm left) e *
          ((adaptedWeightedBasis n L data hn).pbwEquiv.symm right) f) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact her (Finset.sum_eq_zero (fun f hf ↦ hall f hf))
  obtain ⟨f, hf, hfr⟩ := hf
  have hre : r = .marked (exponentWord n L data hn e) rho
      ⟨n + 1, by omega⟩ (exponentWord n L data hn f) := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at hfr
  subst r
  exact Or.inl rfl

private theorem adaptedMarkedRowsOfQuotientWeightRow_reachable_of_ne
    (q : QuotientWeightRow n L data) (r : MarkedRow n L data hn)
    (hr : adaptedMarkedRowsOfQuotientWeightRow n L data hn q r ≠ 0) :
    ClosedSquareReachable n L data hn r := by
  cases q with
  | ordinary xs => exact (hr rfl).elim
  | marked left rho s right =>
      exact markedRowsAround_reachable_of_ne n L data hn _ rho _ r hr

theorem GoverningWitness.rawCompleteCutoffMarkedRows_reachable_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : w.rawCompleteCutoffMarkedRows n L data hn r ≠ 0) :
    ClosedSquareReachable n L data hn r := by
  classical
  rw [GoverningWitness.rawCompleteCutoffMarkedRows, Finsupp.sum_apply] at hr
  have hq : ∃ q ∈ (w.rawCompleteCutoffRows n L data).support,
      (w.rawCompleteCutoffRows n L data q •
        adaptedMarkedRowsOfQuotientWeightRow n L data hn q) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun q hq ↦ hall q hq))
  obtain ⟨q, hq, hqr⟩ := hq
  have hne : adaptedMarkedRowsOfQuotientWeightRow n L data hn q r ≠ 0 := by
    intro hz
    simp [hz] at hqr
  exact adaptedMarkedRowsOfQuotientWeightRow_reachable_of_ne
    n L data hn q r hne

theorem GoverningWitness.rawCutoffClosedSquareFrontier_reachable_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : w.rawCutoffClosedSquareFrontier n L data hn r ≠ 0) :
    ClosedSquareReachable n L data hn r := by
  classical
  rw [GoverningWitness.rawCutoffClosedSquareFrontier, Finsupp.sum_apply] at hr
  have hroot : ∃ root ∈
      (w.rawCompleteCutoffMarkedRows n L data hn).support,
      (w.rawCompleteCutoffMarkedRows n L data hn root •
        (closedSquareCollector n L data hn).normalForm root) r ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hr (Finset.sum_eq_zero (fun root hroot ↦ hall root hroot))
  obtain ⟨root, hroot, hrootr⟩ := hroot
  have hnormal : (closedSquareCollector n L data hn).normalForm root r ≠ 0 := by
    intro hz
    simp [hz] at hrootr
  exact closedSquare_reachable_of_normalForm_apply_ne_zero n L data hn root
    (w.rawCompleteCutoffMarkedRows_reachable_of_ne n L data hn root
      (Finsupp.mem_support_iff.mp hroot)) hnormal

theorem GoverningWitness.rawCutoffClosedSquareFrontier_terminal_of_ne {a : L}
    (w : GoverningWitness n L data a) (r : MarkedRow n L data hn)
    (hr : w.rawCutoffClosedSquareFrontier n L data hn r ≠ 0) :
    closedSquareExpansion n L data hn r = none := by
  by_contra hnonterminal
  apply hr
  rw [GoverningWitness.rawCutoffClosedSquareFrontier, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro root hroot
  change w.rawCompleteCutoffMarkedRows n L data hn root *
      (closedSquareCollector n L data hn).normalForm root r = 0
  rw [(closedSquareCollector n L data hn).normalForm_apply_eq_zero_of_nonterminal
    root r hnonterminal, mul_zero]

/-! ## The four terminal reads -/

/-- Retained genuine marked factor-two occurrences of the continued cutoff. -/
def GoverningWitness.rawCutoffTerminalTwo {a : L}
    (w : GoverningWitness n L data a) :
    TerminalFactorTwo n L data hn →₀ ℤ :=
  (w.rawCutoffClosedSquareFrontier n L data hn).sum fun r z ↦
    z • terminalFactorTwoPart n L data hn r

/-- Their degree-one Koszul chain. -/
def GoverningWitness.rawCutoffTerminalTwoChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (w.rawCutoffTerminalTwo n L data hn).sum fun c z ↦
    z • terminalFactorChain n L data hn c

/-- Ordinary factor-one PBW read of the common terminal frontier. -/
def GoverningWitness.rawCutoffOrdinaryPrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffClosedSquareFrontier n L data hn).sum fun r z ↦
    z • ordinaryPrimitiveSeed n L data hn r

/-- Ordinary factor-two PBW read of the same terminal frontier. -/
def GoverningWitness.rawCutoffOrdinaryFactorTwo {a : L}
    (w : GoverningWitness n L data a) : Sym[ℤ] (Fin 2) (A L n) :=
  (w.rawCutoffClosedSquareFrontier n L data hn).sum fun r z ↦
    z • ordinaryFactorSeed n L data hn 2 n (by omega) r

/-- Whole relation retained at a marked factor-one leaf. -/
def cutoffTerminalOneRelationSeed :
    MarkedRow n L data hn → Relations n L data
  | .marked [] rho _ [] => rho
  | _ => 0

/-- Aggregate whole factor-one relation of the continued cutoff. -/
def GoverningWitness.rawCutoffTerminalOneRelation {a : L}
    (w : GoverningWitness n L data a) : Relations n L data :=
  (w.rawCutoffClosedSquareFrontier n L data hn).sum fun r z ↦
    z • cutoffTerminalOneRelationSeed n L data hn r

/-- PBW primitive of the literal retained marked factor-two placements. -/
def GoverningWitness.rawCutoffTerminalTwoPrimitive {a : L}
    (w : GoverningWitness n L data a) : FreeModel n L :=
  (w.rawCutoffTerminalTwo n L data hn).sum fun c z ↦
    z • pbwPrimitive n L data hn c.row.value

/-- Genuine placement corrections for the retained marked factor-two rows. -/
def GoverningWitness.rawCutoffTerminalTwoPlacementRelation {a : L}
    (w : GoverningWitness n L data a) : Relations n L data :=
  (w.rawCutoffTerminalTwo n L data hn).sum fun c z ↦
    z • c.sourcePlacementRelation n L data hn

@[simp] theorem GoverningWitness.dOne_rawCutoffTerminalTwoChain {a : L}
    (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffTerminalTwoChain n L data hn) =
      (w.rawCutoffTerminalTwo n L data hn).sum (fun c z ↦
        z • rightSymbol n L data hn 2 n (by omega) c.row.value) := by
  classical
  rw [GoverningWitness.rawCutoffTerminalTwoChain, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, dOne_terminalFactorChain]
  rfl

theorem GoverningWitness.terminalSourcePrimitive_rawCutoffTerminalTwoChain
    {a : L} (w : GoverningWitness n L data a) :
    terminalSourcePrimitive n L data hn
        (w.rawCutoffTerminalTwoChain n L data hn) =
      w.rawCutoffTerminalTwoPrimitive n L data hn +
        (w.rawCutoffTerminalTwoPlacementRelation n L data hn :
          FreeModel n L) := by
  classical
  rw [GoverningWitness.rawCutoffTerminalTwoChain,
    GoverningWitness.rawCutoffTerminalTwoPrimitive,
    GoverningWitness.rawCutoffTerminalTwoPlacementRelation,
    map_finsuppSum]
  simp_rw [map_zsmul]
  change (w.rawCutoffTerminalTwo n L data hn).sum
      (fun c z ↦ z • terminalSourcePrimitive n L data hn
        (terminalFactorChain n L data hn c)) =
    (w.rawCutoffTerminalTwo n L data hn).sum
        (fun c z ↦ z • pbwPrimitive n L data hn c.row.value) +
      (Relations n L data).subtype
        ((w.rawCutoffTerminalTwo n L data hn).sum
          (fun c z ↦ z • c.sourcePlacementRelation n L data hn))
  rw [map_finsuppSum, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro c hc
  rw [c.terminalSourcePrimitive_factorChain n L data hn, smul_add]
  rfl

/-! ## Exact reads of the common frontier -/

private def cutoffTerminalFactorSymbolSeed
    (r : MarkedRow n L data hn) : Sym[ℤ] (Fin 2) (A L n) :=
  match terminalFactorTwo? n L data hn r with
  | none => 0
  | some c => rightSymbol n L data hn 2 n (by omega) c.row.value

private theorem GoverningWitness.rawCutoffTerminalFactorSymbol_eq {a : L}
    (w : GoverningWitness n L data a) :
    (w.rawCutoffTerminalTwo n L data hn).sum (fun c z ↦
        z • rightSymbol n L data hn 2 n (by omega) c.row.value) =
      (w.rawCutoffClosedSquareFrontier n L data hn).sum (fun r z ↦
        z • cutoffTerminalFactorSymbolSeed n L data hn r) := by
  classical
  rw [GoverningWitness.rawCutoffTerminalTwo,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : terminalFactorTwo? n L data hn r with
  | none =>
      simp [terminalFactorTwoPart, cutoffTerminalFactorSymbolSeed, hc]
      module
  | some c =>
      simp [terminalFactorTwoPart, cutoffTerminalFactorSymbolSeed, hc]

private theorem cutoff_terminal_rightSymbol_decomposition
    (r : MarkedRow n L data hn)
    (hreach : ClosedSquareReachable n L data hn r)
    (hterminal : closedSquareExpansion n L data hn r = none) :
    rightSymbol n L data hn 2 n (by omega) r.value =
      ordinaryFactorSeed n L data hn 2 n (by omega) r +
        cutoffTerminalFactorSymbolSeed n L data hn r := by
  cases r with
  | ordinary word =>
      simp [MarkedRow.value, ordinaryFactorSeed,
        cutoffTerminalFactorSymbolSeed, terminalFactorTwo?]
  | marked left rho k right =>
      rcases reachable_terminal_marked n L data hn left rho k right
          hreach hterminal with hone | htwo
      · rcases hone with ⟨rfl, rfl, hk⟩
        have hmarked : (MarkedRow.marked [] rho k [] :
            MarkedRow n L data hn) =
              .marked [] rho ⟨n + 1, by omega⟩ [] := by
          congr 1
          exact Fin.ext hk
        have hzero : rightSymbol n L data hn 2 n (by omega)
            (MarkedRow.marked [] rho ⟨n + 1, by omega⟩ [] :
              MarkedRow n L data hn).value = 0 := by
          rw [show (MarkedRow.marked [] rho ⟨n + 1, by omega⟩ [] :
              MarkedRow n L data hn).value =
                UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) by
            simp [MarkedRow.value, MarkedRow.basisWord,
              LieRings.PBW.basisWord, LieRings.PBW.word,
              rowTruncation_top]]
          change SymmetricPower.map (R := ℤ) (ι := Fin 2)
              (prLE n L n (by omega))
              (fullRightSymbol n L data hn 2
                (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L))) = 0
          rw [fullRightSymbol_iota_eq_zero_of_one_lt n L data hn 2
            (by omega), map_zero]
        rw [hmarked, hzero]
        simp [ordinaryFactorSeed, cutoffTerminalFactorSymbolSeed,
          terminalFactorTwo?]
      · obtain ⟨c, hc⟩ := htwo
        have hr : (MarkedRow.marked left rho k right :
            MarkedRow n L data hn) = c.row := hc.symm
        rw [hr]
        rcases c with ⟨rho', factor, placement⟩
        cases placement <;>
          simp [TerminalFactorTwo.row, ordinaryFactorSeed,
            cutoffTerminalFactorSymbolSeed, terminalFactorTwo?]

/-- Exact factor-two identity of the cutoff continuation.  The ordinary and
marked reads are taken from the same signed terminal frontier. -/
theorem GoverningWitness.dOne_rawCutoffTerminalTwoChain_eq_symbol_sub_ordinary
    {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.rawCutoffTerminalTwoChain n L data hn) =
      rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) -
        w.rawCutoffOrdinaryFactorTwo n L data hn := by
  classical
  have heval := congrArg (rightSymbol n L data hn 2 n (by omega))
    (w.rawCutoffClosedSquareFrontier_evaluation n L data hn)
  change rightSymbol n L data hn 2 n (by omega)
      ((w.rawCutoffClosedSquareFrontier n L data hn).sum
        (fun r z ↦ z • r.value)) =
    rightSymbol n L data hn 2 n (by omega)
      (w.rawCompleteCutoffWord n L data) at heval
  rw [map_finsuppSum] at heval
  simp_rw [map_zsmul] at heval
  rw [w.dOne_rawCutoffTerminalTwoChain n L data hn,
    w.rawCutoffTerminalFactorSymbol_eq n L data hn,
    ← heval, GoverningWitness.rawCutoffOrdinaryFactorTwo]
  apply eq_sub_iff_add_eq.mpr
  have hsum :
      (w.rawCutoffClosedSquareFrontier n L data hn).sum (fun r z ↦
          z • ordinaryFactorSeed n L data hn 2 n (by omega) r) +
        (w.rawCutoffClosedSquareFrontier n L data hn).sum (fun r z ↦
          z • cutoffTerminalFactorSymbolSeed n L data hn r) =
      (w.rawCutoffClosedSquareFrontier n L data hn).sum (fun r z ↦
          z • rightSymbol n L data hn 2 n (by omega) r.value) := by
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro r hr
    have hdec := cutoff_terminal_rightSymbol_decomposition n L data hn r
      (w.rawCutoffClosedSquareFrontier_reachable_of_ne
        n L data hn r (Finsupp.mem_support_iff.mp hr))
      (w.rawCutoffClosedSquareFrontier_terminal_of_ne
        n L data hn r (Finsupp.mem_support_iff.mp hr))
    rw [hdec]
    module
  exact (add_comm _ _).trans hsum

/-- Additive form of
`dOne_rawCutoffTerminalTwoChain_eq_symbol_sub_ordinary`.  This is the form
used when the continued cutoff is spliced onto the complete factor-first
chain. -/
theorem GoverningWitness.rightSymbol_rawCompleteCutoffWord_eq_ordinary_add_dOne
    {a : L} (w : GoverningWitness n L data a) :
    rightSymbol n L data hn 2 n (by omega)
        (w.rawCompleteCutoffWord n L data) =
      (show Sym[ℤ] (Fin (1 + 1))
          (terminalSourcePresentation n L data hn).gen from
        w.rawCutoffOrdinaryFactorTwo n L data hn) +
        Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (w.rawCutoffTerminalTwoChain n L data hn) := by
  have h := w.dOne_rawCutoffTerminalTwoChain_eq_symbol_sub_ordinary
    n L data hn
  apply (eq_sub_iff_add_eq.mp h).symm.trans
  exact add_comm _ _
/-
  rw [← heval, GoverningWitness.rawCutoffOrdinaryFactorTwo,
    w.dOne_rawCutoffTerminalTwoChain n L data hn,
    w.rawCutoffTerminalFactorSymbol_eq n L data hn,
    ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  simp only [map_zsmul, smul_add]
  exact congrArg (fun x ↦
    (w.rawCutoffClosedSquareFrontier n L data hn r) • x)
      (cutoff_terminal_rightSymbol_decomposition n L data hn r
        (w.rawCutoffClosedSquareFrontier_reachable_of_ne
          n L data hn r (Finsupp.mem_support_iff.mp hr))
        (w.rawCutoffClosedSquareFrontier_terminal_of_ne
          n L data hn r (Finsupp.mem_support_iff.mp hr)))
-/

private def cutoffTerminalTwoPrimitiveSeed
    (r : MarkedRow n L data hn) : FreeModel n L :=
  match terminalFactorTwo? n L data hn r with
  | none => 0
  | some c => pbwPrimitive n L data hn c.row.value

private theorem GoverningWitness.rawCutoffTerminalTwoPrimitive_eq {a : L}
    (w : GoverningWitness n L data a) :
    w.rawCutoffTerminalTwoPrimitive n L data hn =
      (w.rawCutoffClosedSquareFrontier n L data hn).sum (fun r z ↦
        z • cutoffTerminalTwoPrimitiveSeed n L data hn r) := by
  classical
  rw [GoverningWitness.rawCutoffTerminalTwoPrimitive,
    GoverningWitness.rawCutoffTerminalTwo,
    Finsupp.sum_sum_index (fun _ ↦ by simp) (fun _ _ _ ↦ by module)]
  apply Finsupp.sum_congr
  intro r hr
  cases hc : terminalFactorTwo? n L data hn r with
  | none =>
      simp [terminalFactorTwoPart, cutoffTerminalTwoPrimitiveSeed, hc]
  | some c =>
      simp [terminalFactorTwoPart, cutoffTerminalTwoPrimitiveSeed, hc]

private theorem cutoff_terminal_primitive_decomposition
    (r : MarkedRow n L data hn)
    (hreach : ClosedSquareReachable n L data hn r)
    (hterminal : closedSquareExpansion n L data hn r = none) :
    pbwPrimitive n L data hn r.value =
      ordinaryPrimitiveSeed n L data hn r +
        cutoffTerminalTwoPrimitiveSeed n L data hn r +
        (cutoffTerminalOneRelationSeed n L data hn r : FreeModel n L) := by
  cases r with
  | ordinary word =>
      simp [MarkedRow.value, ordinaryPrimitiveSeed,
        cutoffTerminalTwoPrimitiveSeed, cutoffTerminalOneRelationSeed,
        terminalFactorTwo?]
  | marked left rho k right =>
      rcases reachable_terminal_marked n L data hn left rho k right
          hreach hterminal with hone | htwo
      · rcases hone with ⟨rfl, rfl, hk⟩
        have hmarked : (MarkedRow.marked [] rho k [] :
            MarkedRow n L data hn) =
              .marked [] rho ⟨n + 1, by omega⟩ [] := by
          congr 1
          exact Fin.ext hk
        rw [hmarked]
        simp only [MarkedRow.value, MarkedRow.basisWord,
          LieRings.PBW.basisWord, LieRings.PBW.word, rowTruncation_top,
          List.map_nil, List.prod_nil, one_mul, mul_one,
          ordinaryPrimitiveSeed,
          cutoffTerminalTwoPrimitiveSeed, cutoffTerminalOneRelationSeed,
          terminalFactorTwo?, ↓reduceIte, zero_add]
        exact pbwPrimitive_iota n L data hn (rho : FreeModel n L)
      · obtain ⟨c, hc⟩ := htwo
        have hr : (MarkedRow.marked left rho k right :
            MarkedRow n L data hn) = c.row := hc.symm
        rw [hr]
        rcases c with ⟨rho', factor, placement⟩
        cases placement <;>
          simp [TerminalFactorTwo.row, ordinaryPrimitiveSeed,
            cutoffTerminalTwoPrimitiveSeed, cutoffTerminalOneRelationSeed,
            terminalFactorTwo?]

/-- Exact primitive identity of the same cutoff continuation.  In
particular, the one-factor marked leaves are summed as whole relations before
the primitive projection is compared. -/
theorem GoverningWitness.pbwPrimitive_rawCompleteCutoffWord_eq_terminal_reads
    {a : L} (w : GoverningWitness n L data a) :
    pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) =
      w.rawCutoffOrdinaryPrimitive n L data hn +
        w.rawCutoffTerminalTwoPrimitive n L data hn +
        (w.rawCutoffTerminalOneRelation n L data hn : FreeModel n L) := by
  classical
  have heval := congrArg (pbwPrimitive n L data hn)
    (w.rawCutoffClosedSquareFrontier_evaluation n L data hn)
  change pbwPrimitive n L data hn
      ((w.rawCutoffClosedSquareFrontier n L data hn).sum
        (fun r z ↦ z • r.value)) =
    pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) at heval
  rw [map_finsuppSum] at heval
  simp_rw [map_zsmul] at heval
  rw [← heval, GoverningWitness.rawCutoffOrdinaryPrimitive,
    w.rawCutoffTerminalTwoPrimitive_eq n L data hn,
    GoverningWitness.rawCutoffTerminalOneRelation]
  rw [show ((w.rawCutoffClosedSquareFrontier n L data hn).sum
      (fun r z ↦ z • cutoffTerminalOneRelationSeed n L data hn r) :
        Relations n L data) =
      (w.rawCutoffClosedSquareFrontier n L data hn).sum
        (fun r z ↦ z • cutoffTerminalOneRelationSeed n L data hn r) by rfl]
  have hcoe :
      (((w.rawCutoffClosedSquareFrontier n L data hn).sum
          (fun r z ↦ z • cutoffTerminalOneRelationSeed n L data hn r) :
            Relations n L data) : FreeModel n L) =
        (w.rawCutoffClosedSquareFrontier n L data hn).sum
          (fun r z ↦ z •
            (cutoffTerminalOneRelationSeed n L data hn r : FreeModel n L)) := by
    change (Relations n L data).subtype
        ((w.rawCutoffClosedSquareFrontier n L data hn).sum
          (fun r z ↦ z • cutoffTerminalOneRelationSeed n L data hn r)) = _
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro r hr
    rw [map_zsmul]
    rfl
  rw [hcoe]
  change (w.rawCutoffClosedSquareFrontier n L data hn).sum
      (fun r z ↦ z • pbwPrimitive n L data hn r.value) =
    (w.rawCutoffClosedSquareFrontier n L data hn).sum
        (fun r z ↦ z • ordinaryPrimitiveSeed n L data hn r) +
      (w.rawCutoffClosedSquareFrontier n L data hn).sum
        (fun r z ↦ z • cutoffTerminalTwoPrimitiveSeed n L data hn r) +
      (w.rawCutoffClosedSquareFrontier n L data hn).sum
        (fun r z ↦ z •
          (cutoffTerminalOneRelationSeed n L data hn r : FreeModel n L))
  rw [← Finsupp.sum_add, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  simpa only [smul_add] using congrArg (fun x ↦
    (w.rawCutoffClosedSquareFrontier n L data hn r) • x)
      (cutoff_terminal_primitive_decomposition n L data hn r
        (w.rawCutoffClosedSquareFrontier_reachable_of_ne
          n L data hn r (Finsupp.mem_support_iff.mp hr))
        (w.rawCutoffClosedSquareFrontier_terminal_of_ne
          n L data hn r (Finsupp.mem_support_iff.mp hr)))

end

end LieRings.MetabelianVanishing
