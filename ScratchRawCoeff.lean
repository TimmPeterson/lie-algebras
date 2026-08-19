import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSupport
import LieRings.DimensionSubring.MetabelianVanishing.CompleteCutoffCycle

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)
variable {a : L} (w : GoverningWitness n L data a)
variable (c : ProvenancedCell n L data hn)

#check w.rawCutoffFullProvenancedCells n L data hn c
#check add_sub_cancel_right
#check add_sub_cancel_left
#check neg_one_zsmul
#check neg_one_smul
#check sub_sub_cancel_left
#check sub_sub_cancel
#check GoverningWitness.eq_zero_of_completeCutoffCorrection_eval

example : w.rawCutoffFullProvenancedCells n L data hn c •
      (0 : Sym[ℤ] (Fin 2) (A L n)) =
    w.rawCutoffFullProvenancedCells n L data hn c • 0 +
      w.rawCutoffFullProvenancedCells n L data hn c • 0 := by
  rw [zsmul_zero, zero_add]

end

end LieRings.MetabelianVanishing
