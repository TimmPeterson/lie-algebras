import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoTerminalRead

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance scratchInitialReadFintype : Fintype L := Fintype.ofFinite L

theorem test_word (r : TriangularPlacedRow n L) :
    completeFactorTwoFullLabelWord n L data
        (quotientWeightRowOfPlaced n L data r) =
      TriangularPlacedRow.value n L data r := by
  rfl

theorem test_initial {a : L} (w : GoverningWitness n L data a) :
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

end

end LieRings.MetabelianVanishing
