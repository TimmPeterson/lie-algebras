import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# A basis-free model of the free two-step Lie ring

For an Abelian group `P`, the group `P ⊕ ⋀²P` carries the two-step Lie bracket
`[(x,a),(y,b)] = (0,x∧y)`.  When `P` is free on a set, this is the quotient of the free Lie ring
by its third lower-central term.  This explicit model supplies the weight-one-plus-two
truncation used in the degree-five PBW extraction without choosing a Hall basis.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (P : Type u) [AddCommGroup P]

/-- The exterior product of two elements, in the second exterior power. -/
def wedgeTwo (x y : P) : ⋀[ℤ]^2 P :=
  exteriorPower.ιMulti ℤ 2 ![x, y]

@[simp]
theorem wedgeTwo_self (x : P) : wedgeTwo P x x = 0 := by
  change exteriorPower.ιMulti ℤ 2 ![x, x] = 0
  exact (exteriorPower.ιMulti ℤ 2).map_eq_zero_of_eq ![x, x]
    (i := 0) (j := 1) rfl (by decide)

@[simp]
theorem wedgeTwo_add_left (x y z : P) :
    wedgeTwo P (x + y) z = wedgeTwo P x z + wedgeTwo P y z := by
  change (exteriorPower.ιMulti ℤ 2) ![x + y, z] =
    (exteriorPower.ιMulti ℤ 2) ![x, z] + (exteriorPower.ιMulti ℤ 2) ![y, z]
  have h := (exteriorPower.ιMulti ℤ 2).map_update_add (![0, z]) 0 x y
  convert h using 1

@[simp]
theorem wedgeTwo_add_right (x y z : P) :
    wedgeTwo P x (y + z) = wedgeTwo P x y + wedgeTwo P x z := by
  change (exteriorPower.ιMulti ℤ 2) ![x, y + z] =
    (exteriorPower.ιMulti ℤ 2) ![x, y] + (exteriorPower.ιMulti ℤ 2) ![x, z]
  have h := (exteriorPower.ιMulti ℤ 2).map_update_add (![x, 0]) 1 y z
  convert h using 1

@[simp]
theorem wedgeTwo_zsmul_right (n : ℤ) (x y : P) :
    wedgeTwo P x (n • y) = n • wedgeTwo P x y := by
  change (exteriorPower.ιMulti ℤ 2) ![x, n • y] =
    n • (exteriorPower.ιMulti ℤ 2) ![x, y]
  have h := (exteriorPower.ιMulti ℤ 2).map_update_smul (![x, 0]) 1 n y
  convert h using 1

@[simp]
theorem wedgeTwo_zero_left (y : P) : wedgeTwo P 0 y = 0 := by
  change (exteriorPower.ιMulti ℤ 2) ![0, y] = 0
  exact (exteriorPower.ιMulti ℤ 2).map_coord_zero 0 rfl

@[simp]
theorem wedgeTwo_zero_right (x : P) : wedgeTwo P x 0 = 0 := by
  change (exteriorPower.ιMulti ℤ 2) ![x, 0] = 0
  exact (exteriorPower.ιMulti ℤ 2).map_coord_zero 1 rfl

/-- The underlying Abelian group of the free two-step nilpotent Lie ring on `P`. -/
abbrev FreeClassTwo := P × ⋀[ℤ]^2 P

namespace FreeClassTwo

instance : Bracket (FreeClassTwo P) (FreeClassTwo P) where
  bracket x y := (0, wedgeTwo P x.1 y.1)

@[simp]
theorem bracket_apply (x y : FreeClassTwo P) :
    ⁅x, y⁆ = (0, wedgeTwo P x.1 y.1) :=
  rfl

instance : LieRing (FreeClassTwo P) where
  add_lie x y z := by
    change ((0, wedgeTwo P (x.1 + y.1) z.1) : P × ⋀[ℤ]^2 P) = _
    change ((0, wedgeTwo P (x.1 + y.1) z.1) : P × ⋀[ℤ]^2 P) =
      (0, wedgeTwo P x.1 z.1) + (0, wedgeTwo P y.1 z.1)
    rw [wedgeTwo_add_left]
    ext <;> simp
  lie_add x y z := by
    change ((0, wedgeTwo P x.1 (y.1 + z.1)) : P × ⋀[ℤ]^2 P) = _
    change ((0, wedgeTwo P x.1 (y.1 + z.1)) : P × ⋀[ℤ]^2 P) =
      (0, wedgeTwo P x.1 y.1) + (0, wedgeTwo P x.1 z.1)
    rw [wedgeTwo_add_right]
    ext <;> simp
  lie_self x := by
    change ((0, wedgeTwo P x.1 x.1) : P × ⋀[ℤ]^2 P) = (0, 0)
    apply Prod.ext <;> simp
  leibniz_lie x y z := by
    change ((0, wedgeTwo P x.1 0) : P × ⋀[ℤ]^2 P) =
      (0, wedgeTwo P 0 z.1) + (0, wedgeTwo P y.1 0)
    ext <;> simp

instance : LieAlgebra ℤ (FreeClassTwo P) where
  lie_smul n x y := by
    change ((0, wedgeTwo P x.1 (n • y.1)) : P × ⋀[ℤ]^2 P) =
      n • (0, wedgeTwo P x.1 y.1)
    rw [wedgeTwo_zsmul_right]
    change (0, n • wedgeTwo P x.1 y.1) =
      (n • (0 : P), n • wedgeTwo P x.1 y.1)
    simp

/-- The degree-one inclusion. -/
def of : P →ₗ[ℤ] FreeClassTwo P where
  toFun x := (x, 0)
  map_add' x y := by
    change (x + y, 0) = ((x, 0) : P × ⋀[ℤ]^2 P) + (y, 0)
    simp
  map_smul' n x := by
    change (n • x, 0) = (n • x, n • (0 : ⋀[ℤ]^2 P))
    simp

@[simp]
theorem of_apply (x : P) : of P x = (x, 0) := by rfl

/-- Projection to the degree-one component. -/
def degreeOne : FreeClassTwo P →ₗ[ℤ] P :=
  LinearMap.fst ℤ P (⋀[ℤ]^2 P)

/-- Projection to the degree-two component. -/
def degreeTwo : FreeClassTwo P →ₗ[ℤ] ⋀[ℤ]^2 P :=
  LinearMap.snd ℤ P (⋀[ℤ]^2 P)

@[simp]
theorem degreeOne_apply (x : FreeClassTwo P) : degreeOne P x = x.1 := rfl

@[simp]
theorem degreeTwo_apply (x : FreeClassTwo P) : degreeTwo P x = x.2 := rfl

/-- The explicit Lie ring `P ⊕ ⋀²P` has nilpotency class at most two. -/
theorem lowerCentralSeries_two_eq_bot :
    LieModule.lowerCentralSeries ℤ (FreeClassTwo P) (FreeClassTwo P) 2 = ⊥ := by
  have hgammaTwo : LieModule.lowerCentralSeries ℤ (FreeClassTwo P)
      (FreeClassTwo P) 1 ≤
      LinearMap.ker (degreeOne P) := by
    let K : LieSubmodule ℤ (FreeClassTwo P) (FreeClassTwo P) := {
      carrier := {z | z.1 = 0}
      zero_mem' := rfl
      add_mem' hx hy := by
        change _ = 0 at hx hy ⊢
        simp [hx, hy]
      smul_mem' n x hx := by
        change _ = 0 at hx ⊢
        simp [hx]
      lie_mem := by intro x y hy; rfl }
    have hle : LieModule.lowerCentralSeries ℤ (FreeClassTwo P)
        (FreeClassTwo P) 1 ≤ K := by
      rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
      intro x _ y _
      rfl
    intro z hz
    rw [LinearMap.mem_ker]
    exact hle hz
  apply le_antisymm
  · change LieModule.lowerCentralSeries ℤ (FreeClassTwo P)
        (FreeClassTwo P) 2 ≤ ⊥
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
    intro x _ y hy
    have hyzero : y.1 = 0 := LinearMap.mem_ker.mp (hgammaTwo hy)
    change ((0, wedgeTwo P x.1 y.1) : FreeClassTwo P) ∈
      (⊥ : LieIdeal ℤ (FreeClassTwo P))
    rw [hyzero, wedgeTwo_zero_right]
    simp
  · exact bot_le

end FreeClassTwo

end

end DegreeFive

end LieRings
