import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge

/-!
# Primitive read below one complete factor-two row

The terminal full-label boundary already has a rowwise theorem.  This file
records the matching rowwise primitive theorem, with every placement error
summed in the genuine relation submodule before coercion.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance completeFactorTwoPerRowPrimitiveFintype : Fintype L :=
  Fintype.ofFinite L

/-- The chain read from the complete normal form below one quotient-weight
row has the primitive of that same whole-label normal form, modulo the sum
of its genuine full-relation placement corrections. -/
theorem terminalSourcePrimitive_completeNormalFormChain
    (r : QuotientWeightRow n L data) :
    terminalSourcePrimitive n L data hn
        (((completeFactorTwoCollector n L data).normalForm r).sum
          (fun q z ↦ z • completeFactorTwoChainPart n L data hn q)) =
      pbwPrimitive n L data hn
          (rawCompleteNormalFullLabelWord n L data r) +
        (((completeFactorTwoCollector n L data).normalForm r).sum
          (fun q z ↦ z •
            completeTerminalPrimitiveCorrection n L data q) :
          Relations n L data) := by
  classical
  rw [map_finsuppSum, rawCompleteNormalFullLabelWord, map_finsuppSum]
  simp_rw [map_zsmul]
  change ((completeFactorTwoCollector n L data).normalForm r).sum
      (fun q z ↦ z • terminalSourcePrimitive n L data hn
        (completeFactorTwoChainPart n L data hn q)) =
    ((completeFactorTwoCollector n L data).normalForm r).sum
        (fun q z ↦ z • pbwPrimitive n L data hn
          (completeFactorTwoFullLabelWord n L data q)) +
      (Relations n L data).subtype
        (((completeFactorTwoCollector n L data).normalForm r).sum
          (fun q z ↦ z •
            completeTerminalPrimitiveCorrection n L data q))
  rw [map_finsuppSum, ← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro q hq
  rw [map_zsmul]
  change ((completeFactorTwoCollector n L data).normalForm r q) •
      terminalSourcePrimitive n L data hn
        (completeFactorTwoChainPart n L data hn q) =
    ((completeFactorTwoCollector n L data).normalForm r q) •
        pbwPrimitive n L data hn
          (completeFactorTwoFullLabelWord n L data q) +
      ((completeFactorTwoCollector n L data).normalForm r q) •
        (completeTerminalPrimitiveCorrection n L data q : FreeModel n L)
  rw [← smul_add]
  apply congrArg (fun x : FreeModel n L ↦
    (completeFactorTwoCollector n L data).normalForm r q • x)
  apply terminalSourcePrimitive_completeFactorTwoChainPart_of_terminal
    n L data hn q
  by_contra hnonterminal
  exact Finsupp.mem_support_iff.mp hq
    ((completeFactorTwoCollector n L data).normalForm_apply_eq_zero_of_nonterminal
      r q hnonterminal)

end

end LieRings.MetabelianVanishing
