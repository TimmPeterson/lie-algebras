import LieRings.DimensionSubring.DegreeFive.Reduction
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The exterior bracket in nilpotency class three

If `γ₄(L) = 0`, then `γ₃(L)` is central. Consequently the bracket of lifts descends to an
alternating map on `L / γ₃(L)`, and hence to its second exterior power. This is the invariant
map used to annihilate the alternating tensor extracted from a degree-five PBW witness.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- The class-two quotient used by the invariant part of the degree-five argument. -/
abbrev ModGammaThree := L ⧸ lowerCentralSeries ℤ L 2

/-- Bracketing an element of `γ₃` on the left gives an element of `γ₄`. -/
theorem bracket_mem_lowerCentralSeries_three_of_left_mem_two
    {x y : L} (hx : x ∈ lowerCentralSeries ℤ L 2) :
    ⁅x, y⁆ ∈ lowerCentralSeries ℤ L 3 := by
  rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
  rw [← LieSubmodule.lie_comm]
  exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top y)

/-- Bracketing an element of `γ₃` on the right gives an element of `γ₄`. -/
theorem bracket_mem_lowerCentralSeries_three_of_right_mem_two
    {x y : L} (hy : y ∈ lowerCentralSeries ℤ L 2) :
    ⁅x, y⁆ ∈ lowerCentralSeries ℤ L 3 := by
  rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) hy

/-- The integral bilinear bracket, written as a curried linear map. -/
def bracketBilinear : L →ₗ[ℤ] L →ₗ[ℤ] L where
  toFun x :=
    { toFun := fun y ↦ ⁅x, y⁆
      map_add' := lie_add x
      map_smul' := fun a y ↦ lie_smul a x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact add_lie x y z
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact smul_lie a x y

/-- In class three, the bracket of lifts is well defined on `L / γ₃(L)` in both variables. -/
def bracketModGammaThree
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    ModGammaThree L →ₗ[ℤ] ModGammaThree L →ₗ[ℤ] L := by
  let right : L →ₗ[ℤ] ModGammaThree L →ₗ[ℤ] L :=
    { toFun := fun x ↦ (lowerCentralSeries ℤ L 2).toSubmodule.liftQ
          (bracketBilinear L x)
          (fun y hy ↦ by
            have hmem := bracket_mem_lowerCentralSeries_three_of_right_mem_two L
              (x := x) (y := y) hy
            rw [hclass] at hmem
            simpa using hmem)
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ z => exact add_lie x y z
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ y => exact smul_lie a x y }
  exact (lowerCentralSeries ℤ L 2).toSubmodule.liftQ right
    (fun x hx ↦ by
      apply LinearMap.ext
      intro q
      induction q using Submodule.Quotient.induction_on with
      | _ y =>
          have hmem := bracket_mem_lowerCentralSeries_three_of_left_mem_two L
            (x := x) (y := y) hx
          rw [hclass] at hmem
          simpa using hmem)

@[simp]
theorem bracketModGammaThree_mk_mk
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (x y : L) :
    bracketModGammaThree L hclass
        (LieSubmodule.Quotient.mk x : ModGammaThree L)
        (LieSubmodule.Quotient.mk y : ModGammaThree L) = ⁅x, y⁆ :=
  rfl

/-- The descended bracket remains alternating. -/
theorem bracketModGammaThree_self
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (x : ModGammaThree L) :
    bracketModGammaThree L hclass x x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

/-- The descended bracket as a two-variable multilinear map. -/
def quotientBracketMultilinear
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    MultilinearMap ℤ (fun _ : Fin 2 ↦ ModGammaThree L) L where
  toFun v := bracketModGammaThree L hclass (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i a x := by
    fin_cases i <;> simp

/-- The descended bracket as a two-variable alternating map. -/
def quotientBracketAlternating
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    ModGammaThree L [⋀^Fin 2]→ₗ[ℤ] L where
  toMultilinearMap := quotientBracketMultilinear L hclass
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change bracketModGammaThree L hclass (v 0) (v 1) = 0
      change v 0 = v 1 at hv
      rw [hv]
      exact bracketModGammaThree_self L hclass (v 1)
    · change bracketModGammaThree L hclass (v 0) (v 1) = 0
      change v 1 = v 0 at hv
      rw [hv]
      exact bracketModGammaThree_self L hclass (v 0)
    · exact (hij rfl).elim

/-- The bracket map `⋀²(L/γ₃) → L` available in nilpotency class three. -/
def exteriorBracket
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    ⋀[ℤ]^2 (ModGammaThree L) →ₗ[ℤ] L :=
  exteriorPower.alternatingMapLinearEquiv
    (quotientBracketAlternating L hclass)

/-- A convenient binary notation-free constructor for a decomposable exterior tensor. -/
def exteriorWedge (x y : ModGammaThree L) : ⋀[ℤ]^2 (ModGammaThree L) :=
  exteriorPower.ιMulti ℤ 2 ![x, y]

@[simp]
theorem exteriorBracket_wedge
    (hclass : lowerCentralSeries ℤ L 3 = ⊥)
    (x y : ModGammaThree L) :
    exteriorBracket L hclass (exteriorWedge L x y) =
      bracketModGammaThree L hclass x y := by
  change exteriorPower.alternatingMapLinearEquiv
      (quotientBracketAlternating L hclass)
        (exteriorPower.ιMulti ℤ 2 ![x, y]) =
      quotientBracketAlternating L hclass ![x, y]
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (quotientBracketAlternating L hclass) ![x, y]

/-- The natural map `γ₂(L) → L/γ₃(L)`. -/
def gammaTwoToModGammaThree :
    lowerCentralSeries ℤ L 1 →ₗ[ℤ] ModGammaThree L :=
  (lowerCentralSeries ℤ L 2).toSubmodule.mkQ.comp
    (lowerCentralSeries ℤ L 1).toSubmodule.subtype

@[simp]
theorem gammaTwoToModGammaThree_apply
    (x : lowerCentralSeries ℤ L 1) :
    gammaTwoToModGammaThree L x =
      (LieSubmodule.Quotient.mk (x : L) : ModGammaThree L) :=
  rfl

/-- The induced map `⋀²γ₂(L) → ⋀²(L/γ₃(L))`. -/
def gammaTwoExteriorMap :
    ⋀[ℤ]^2 (lowerCentralSeries ℤ L 1) →ₗ[ℤ]
      ⋀[ℤ]^2 (ModGammaThree L) :=
  exteriorPower.map 2 (gammaTwoToModGammaThree L)

/-- In class three, the exterior bracket kills every exterior tensor whose two entries lie
in `γ₂(L)`, because `[γ₂(L), γ₂(L)] ⊆ γ₄(L) = 0`. -/
theorem exteriorBracket_comp_gammaTwoExteriorMap_eq_zero
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    (exteriorBracket L hclass).comp (gammaTwoExteriorMap L) = 0 := by
  apply exteriorPower.linearMap_ext
  ext v
  change exteriorBracket L hclass
      (gammaTwoExteriorMap L (exteriorPower.ιMulti ℤ 2 v)) = 0
  change exteriorBracket L hclass
      (exteriorPower.map 2 (gammaTwoToModGammaThree L)
        (exteriorPower.ιMulti ℤ 2 v)) = 0
  rw [exteriorPower.map_apply_ιMulti
    (n := 2) (gammaTwoToModGammaThree L) v]
  change exteriorBracket L hclass
      (exteriorWedge L
        (LieSubmodule.Quotient.mk (v 0 : L))
        (LieSubmodule.Quotient.mk (v 1 : L))) = 0
  rw [exteriorBracket_wedge, bracketModGammaThree_mk_mk]
  have hmem : ⁅(v 0 : L), (v 1 : L)⁆ ∈ lowerCentralSeries ℤ L 3 := by
    apply bracket_dimensionSubring_le_lowerCentralSeries ℤ L 1 1
    exact LieSubmodule.lie_mem_lie
      (lowerCentralSeries_le_dimensionSubring ℤ L 1 (v 0).property)
      (lowerCentralSeries_le_dimensionSubring ℤ L 1 (v 1).property)
  rw [hclass] at hmem
  simpa using hmem

end

end DegreeFive

end LieRings
