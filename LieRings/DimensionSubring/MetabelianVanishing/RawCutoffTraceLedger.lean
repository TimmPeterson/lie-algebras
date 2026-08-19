import LieRings.DimensionSubring.MetabelianVanishing.CompleteCutoffSmith

/-!
# The truncation-cell ledger of the raw complete cutoff

The complete factor-first pass stops genuine full-relation occurrences at
the top mark.  `CompleteCutoffSmith` continues those occurrences through the
marked collector and reads the ordinary terminal terms.  Here we retain the
other side of the same Stokes formula: the signed truncation cells that emit
those ordinary terms.  Thus the primitive and factor-two reads below are not
independent sums; both are projections of one occurrence-labelled ledger.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance rawCutoffTraceLedgerFintype : Fintype L :=
  Fintype.ofFinite L

/-- Every signed truncation occurrence below the raw complete cutoff. -/
def GoverningWitness.rawCutoffTraceCells {a : L}
    (w : GoverningWitness n L data a) :
    TruncationCell n L data hn →₀ ℤ :=
  (w.rawCompleteCutoffMarkedRows n L data hn).sum fun r z ↦
    z • closedSquareTraceCells n L data hn r

private theorem GoverningWitness.rawCompleteCutoffMarkedRows_ordinary_eq_zero
    {a : L} (w : GoverningWitness n L data a)
    (word : List (AdaptedIndex n L data hn)) :
    w.rawCompleteCutoffMarkedRows n L data hn (.ordinary word) = 0 := by
  classical
  rw [GoverningWitness.rawCompleteCutoffMarkedRows, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro r hr
  cases r with
  | ordinary xs => simp [adaptedMarkedRowsOfQuotientWeightRow]
  | marked left rho s right =>
      change w.rawCompleteCutoffRows n L data
          (.marked left rho s right) *
        adaptedMarkedRowsOfQuotientWeightRow n L data hn
          (.marked left rho s right) (.ordinary word) = 0
      apply mul_eq_zero_of_right
      simp [adaptedMarkedRowsOfQuotientWeightRow, markedRowsAround]

/-- The ordinary primitive at the terminal cutoff frontier is exactly the
sum of primitive vertical edges in its signed truncation-cell trace. -/
theorem GoverningWitness.rawCutoffOrdinaryPrimitive_eq_traceCells
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffOrdinaryPrimitive n L data hn =
      (w.rawCutoffTraceCells n L data hn).sum
        (fun c z ↦ z • c.primitive n L data hn) := by
  classical
  change Finsupp.linearCombination ℤ
      (ordinaryPrimitiveSeed n L data hn)
      (w.rawCutoffClosedSquareFrontier n L data hn) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.primitive n L data hn)
      (w.rawCutoffTraceCells n L data hn)
  rw [GoverningWitness.rawCutoffClosedSquareFrontier,
    GoverningWitness.rawCutoffTraceCells, map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul, map_zsmul]
  change w.rawCompleteCutoffMarkedRows n L data hn r •
      normalFormOrdinaryPrimitive n L data hn r =
    w.rawCompleteCutoffMarkedRows n L data hn r •
      tracePrimitive n L data hn r
  rw [normalFormOrdinaryPrimitive_eq_tracePrimitive]
  cases r with
  | marked => simp [ordinaryPrimitiveSeed]
  | ordinary word =>
      rw [w.rawCompleteCutoffMarkedRows_ordinary_eq_zero
        n L data hn word]
      module

/-- The ordinary factor-two term at the terminal cutoff frontier is exactly
the factor-two read of those same signed truncation cells. -/
theorem GoverningWitness.rawCutoffOrdinaryFactorTwo_eq_traceCells
    {a : L} (w : GoverningWitness n L data a) :
    w.rawCutoffOrdinaryFactorTwo n L data hn =
      (w.rawCutoffTraceCells n L data hn).sum
        (fun c z ↦ z • c.factorEdge n L data hn 2 n (by omega)) := by
  classical
  change Finsupp.linearCombination ℤ
      (ordinaryFactorSeed n L data hn 2 n (by omega))
      (w.rawCutoffClosedSquareFrontier n L data hn) =
    Finsupp.linearCombination ℤ
      (fun c ↦ c.factorEdge n L data hn 2 n (by omega))
      (w.rawCutoffTraceCells n L data hn)
  rw [GoverningWitness.rawCutoffClosedSquareFrontier,
    GoverningWitness.rawCutoffTraceCells, map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro r hr
  rw [map_zsmul, map_zsmul]
  change w.rawCompleteCutoffMarkedRows n L data hn r •
      normalFormOrdinaryFactor n L data hn 2 n (by omega) r =
    w.rawCompleteCutoffMarkedRows n L data hn r •
      traceFactor n L data hn 2 n (by omega) r
  rw [normalFormOrdinaryFactor_eq_traceFactor]
  cases r with
  | marked => simp [ordinaryFactorSeed]
  | ordinary word =>
      rw [w.rawCompleteCutoffMarkedRows_ordinary_eq_zero
        n L data hn word]
      module

end

end LieRings.MetabelianVanishing
