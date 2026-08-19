import LieRings.DimensionSubring.DegreeThree
import LieRings.DimensionSubring.DegreeFour
import Mathlib.Algebra.Lie.Solvable

/-!
# External inputs for odd metabelian dimension-subring vanishing

This file fixes the two assumptions which are allowed in the final theorem:
the Passi--Sicking inclusion and the cyclic-last-layer reduction.  The
metabelian and cyclic-top interfaces used by the internal proof are also fixed
here.
-/

namespace LieRings

universe u

/-- A Lie ring is metabelian when its second derived ideal is zero. -/
def IsMetabelian (L : Type u) [LieRing L] : Prop :=
  LieAlgebra.derivedSeries ℤ L 2 = ⊥

namespace IsMetabelian

variable {L : Type u} [LieRing L]

/-- The usable form of metabelianity: two elements of the first derived ideal
have zero bracket. -/
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

/-- Vanishing of brackets in the first derived ideal is equivalent to the
chosen definition of metabelianity. -/
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

/-- The Passi--Sicking inclusion, deliberately isolated as an external input. -/
def PassiSickingProperty : Prop :=
  ∀ (L : Type u) [LieRing L], IsMetabelian L →
    ∀ (r : ℕ) (x : L),
      x ∈ dimensionSubring ℤ L (r + 1) →
      (2 : ℤ) • x ∈ lowerCentralSeries ℤ L r

/-- Data in the reduced case: only the last lower-central layer is required
to be a cyclic group of 2-power order. -/
structure CyclicTopData (n : ℕ) (L : Type u) [LieRing L] where
  finite_inst : Finite L
  metabelian : IsMetabelian L
  classBound : lowerCentralSeries ℤ L (n + 1) = ⊥
  exponent : ℕ
  topEquiv : lowerCentralSeries ℤ L n ≃+ ZMod (2 ^ exponent)

/-- The internal reduced theorem which will be established by the Koszul/PBW
argument. -/
def ReducedTopLayerVanishes : Prop :=
  ∀ (n : ℕ) (L : Type u) [LieRing L], 1 ≤ n →
    ∀ data : CyclicTopData n L, ∀ a : L,
      a ∈ dimensionSubring ℤ L (2 * n + 1) →
      a ∈ lowerCentralSeries ℤ L n →
      a = 0

/-- The cyclic-last-layer reduction from the beginning of the manuscript. -/
def ReductionProperty : Prop :=
  PassiSickingProperty.{u} →
  ReducedTopLayerVanishes.{u} →
  ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L], 1 ≤ n →
    IsMetabelian L →
    lowerCentralSeries ℤ L (n + 1) = ⊥ →
    dimensionSubring ℤ L (2 * n + 1) = ⊥

end LieRings
