import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Nilpotent

/-!
# Metabelian Lie rings

This file contains the intrinsic definition of a metabelian Lie ring and its
elementwise bracket criterion.  It has no dependency on any dimension-subring
proof.
-/

namespace LieRings

universe u

/-- A Lie ring is metabelian when its second derived ideal is zero. -/
def IsMetabelian (L : Type u) [LieRing L] : Prop :=
  LieAlgebra.derivedSeries ℤ L 2 = ⊥

namespace IsMetabelian

variable {L : Type u} [LieRing L]

/-- In a metabelian Lie ring, two elements of the first derived ideal bracket to zero. -/
theorem bracket_eq_zero (h : IsMetabelian L) {x y : L}
    (hx : x ∈ LieAlgebra.derivedSeries ℤ L 1)
    (hy : y ∈ LieAlgebra.derivedSeries ℤ L 1) :
    ⁅x, y⁆ = 0 := by
  have hxy : ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ L 2 := by
    change ⁅x, y⁆ ∈ LieAlgebra.derivedSeriesOfIdeal ℤ L (1 + 1) ⊤
    rw [LieAlgebra.derivedSeriesOfIdeal_succ]
    exact LieSubmodule.lie_mem_lie hx hy
  rw [h] at hxy
  simpa using hxy

/-- Elementwise vanishing on the first derived ideal characterizes metabelianity. -/
theorem iff_bracket_eq_zero :
    IsMetabelian L ↔
      ∀ {x y : L},
        x ∈ LieAlgebra.derivedSeries ℤ L 1 →
        y ∈ LieAlgebra.derivedSeries ℤ L 1 →
        ⁅x, y⁆ = 0 := by
  constructor
  · intro h x y hx hy
    exact h.bracket_eq_zero hx hy
  · intro h
    change LieAlgebra.derivedSeriesOfIdeal ℤ L (1 + 1) ⊤ = ⊥
    rw [LieAlgebra.derivedSeriesOfIdeal_succ]
    rw [LieSubmodule.lie_eq_bot_iff]
    intro x hx y hy
    exact h hx hy

end IsMetabelian

end LieRings
