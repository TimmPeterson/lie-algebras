import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge
import LieRings.DimensionSubring.MetabelianVanishing.Reduced

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

theorem scratch_eq_zero
    {a : L} (w : GoverningWitness n L data a)
    (hboundary :
      rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) =
        w.terminalTwoFullLabel n L data hn)
    (hprimitive : ∃ tau : Relations n L data,
      pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) =
        w.terminalTwoPrimitive n L data hn +
          (tau : FreeModel n L)) :
    a = 0 := by
  obtain ⟨tau, htau⟩ := hprimitive
  apply w.eq_zero_of_rawCompleteCutoffChain n L data hn
    (w.contextualTerminalChain n L data hn)
    (w.terminalSourcePlacementRelation n L data hn - tau)
  · rw [← w.terminalTwoFullLabel_eq_dOne_contextualTerminalChain
      n L data hn]
    exact hboundary.symm
  · rw [w.terminalSourcePrimitive_contextualTerminalChain n L data hn,
      htau]
    change w.terminalTwoPrimitive n L data hn +
        (w.terminalSourcePlacementRelation n L data hn : FreeModel n L) =
      (w.terminalTwoPrimitive n L data hn + (tau : FreeModel n L)) +
        ((w.terminalSourcePlacementRelation n L data hn : FreeModel n L) -
          (tau : FreeModel n L))
    abel

/-- Scratch specialization of the general reduced glue to the unconditional
Step-7 capstone above. -/
theorem scratch_reducedTopLayerVanishes
    (hboundary : ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
      (data : CyclicTopData n L) (hn : 2 ≤ n) {a : L}
      (w : GoverningWitness n L data a),
      rightSymbol n L data hn 2 n (by omega)
          (w.rawCompleteCutoffWord n L data) =
        w.terminalTwoFullLabel n L data hn)
    (hprimitive : ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
      (data : CyclicTopData n L) (hn : 2 ≤ n) {a : L}
      (w : GoverningWitness n L data a),
      ∃ tau : Relations n L data,
        pbwPrimitive n L data hn (w.rawCompleteCutoffWord n L data) =
          w.terminalTwoPrimitive n L data hn + (tau : FreeModel n L)) :
    ReducedTopLayerVanishes.{u} := by
  apply reducedTopLayerVanishes_of_stepSeven
  intro n L _ data hn3 a w
  exact scratch_eq_zero n L data (by omega) w
    (hboundary n L data (by omega) w)
    (hprimitive n L data (by omega) w)

end

end LieRings.MetabelianVanishing

namespace LieRings

universe u

theorem scratch_final
    (hStepSeven :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (_hn3 : 3 ≤ n) {a : L},
        MetabelianVanishing.GoverningWitness n L data a → a = 0)
    (hReduction : ReductionProperty.{u})
    (hPS : PassiSickingProperty.{u})
    (n : ℕ) (L : Type u) [LieRing L] [Finite L]
    (hn : 1 ≤ n)
    (hmeta : IsMetabelian L)
    (hclass : lowerCentralSeries ℤ L (n + 1) = ⊥) :
    dimensionSubring ℤ L (2 * n + 1) = ⊥ := by
  exact finite_metabelian_odd_dimensionSubring_eq_bot_of_stepSeven
    hStepSeven hReduction hPS n L hn hmeta hclass

end LieRings
