import LieRings.DimensionSubring.Centrality
import Mathlib.Algebra.Lie.Solvable
import Mathlib.GroupTheory.PGroup

/-!
# External inputs for metabelian odd dimension-subring vanishing

This file contains only the two assumptions deliberately deferred by the project: the reduced
finite `2`-primary situation and the Passi--Sicking inclusion.  It contains no part of their
future proofs.
-/

namespace LieRings.DimensionSubring.MetabelianOdd

universe u

/-- A Lie ring is metabelian when its second derived ideal is zero. -/
def IsMetabelian (L : Type u) [LieRing L] : Prop :=
  LieAlgebra.derivedSeries ℤ L 2 = ⊥

/-- The finite, `2`-primary, cyclic-top-layer input used by the reduced proof. -/
structure ReducedData (n : ℕ) (L : Type u) [LieRing L] where
  finite_inst : Finite L
  two_group : IsPGroup 2 (Multiplicative L)
  metabelian : IsMetabelian L
  classBound : lowerCentralSeries ℤ L (n + 1) = ⊥
  topExponent : ℕ
  topEquiv : lowerCentralSeries ℤ L n ≃+ ZMod (2 ^ topExponent)

/-- The classical Passi--Sicking input, indexed without truncated subtraction. -/
def PassiSickingProperty : Prop :=
  ∀ (L : Type u) [LieRing L], IsMetabelian L →
    ∀ (r : ℕ) (x : L),
      x ∈ dimensionSubring ℤ L (r + 1) →
      (2 : ℤ) • x ∈ lowerCentralSeries ℤ L r

/-- The reduced top-layer assertion proved by the new coordinate argument. -/
def ReducedTopLayerVanishes : Prop :=
  ∀ (n : ℕ) (L : Type u) [LieRing L], 1 ≤ n →
    ∀ R : ReducedData n L, ∀ a : L,
      a ∈ dimensionSubring ℤ L (2 * n + 1) →
      a ∈ lowerCentralSeries ℤ L n →
      a = 0

/-- The deferred family-valued reduction from the general theorem to reduced top layers. -/
def ReductionProperty : Prop :=
  PassiSickingProperty.{u} →
  ReducedTopLayerVanishes.{u} →
    ∀ (n : ℕ) (L : Type u) [LieRing L], 1 ≤ n →
      IsMetabelian L →
      lowerCentralSeries ℤ L (n + 1) = ⊥ →
      dimensionSubring ℤ L (2 * n + 1) = ⊥

/-- Exactly the two results intentionally carried as assumptions in this project stage. -/
structure ExternalInputs : Prop where
  passiSicking : PassiSickingProperty.{u}
  reduction : ReductionProperty.{u}

end LieRings.DimensionSubring.MetabelianOdd
