import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge
import LieRings.DimensionSubring.MetabelianVanishing.Reduced

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

example {a : L} (w : GoverningWitness n L data a) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (w.completeFactorTwoChain n L data hn) =
      -w.completeFactorTwoCutoffFullLabel n L data hn := by
  rw [← w.completeNormalFormFullLabelRead_eq_dOne_completeFactorTwoChain
    n L data hn]
  exact w.completeNormalFullLabel_eq_neg_cutoff n L data hn

example {a : L} (w : GoverningWitness n L data a)
    (hword : w.completeTerminalFullLabelWord n L data =
      w.terminalComponentFullLabelWord n L data hn) :
    a = 0 := by
  exact w.eq_zero_of_completeFactorTwoCorrection n L data hn
    (w.dOne_completeFactorTwoChain_of_fullLabelWord_eq
      n L data hn hword)
    (w.completeFactorTwoPrimitiveCorrection n L data)
    (w.terminalSourcePrimitive_completeFactorTwoChain_of_fullLabelWord_eq
      n L data hn hword)

example
    (hword :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (hn : 2 ≤ n) {a : L}
        (w : GoverningWitness n L data a),
        w.completeTerminalFullLabelWord n L data =
          w.terminalComponentFullLabelWord n L data hn) :
    ReducedTopLayerVanishes.{u} := by
  apply reducedTopLayerVanishes_of_stepSeven
  intro n L _ _ data hn3 a w
  have hn2 : 2 ≤ n := by omega
  exact w.eq_zero_of_completeFactorTwoCorrection n L data hn2
    (w.dOne_completeFactorTwoChain_of_fullLabelWord_eq
      n L data hn2 (hword n L data hn2 w))
    (w.completeFactorTwoPrimitiveCorrection n L data)
    (w.terminalSourcePrimitive_completeFactorTwoChain_of_fullLabelWord_eq
      n L data hn2 (hword n L data hn2 w))

end

end LieRings.MetabelianVanishing
