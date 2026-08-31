import LieRings.DimensionSubring.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# Stabilization of a finite dimension-subring tail

This file formalizes the last, purely finite, step in the nilpotent argument: if one term of the
dimension filtration is finite and the omega intersection is zero, then a finite term is already
zero.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

variable (K : Type u) [LieRing K]

/-- The tail of the dimension filtration, viewed inside its fixed finite first term. -/
def dimensionTail (k n : ℕ) : Submodule ℤ (dimensionSubring ℤ K k) :=
  (dimensionSubring ℤ K (k + n)).toSubmodule.comap
    (dimensionSubring ℤ K k).toSubmodule.subtype

theorem dimensionTail_antitone (k : ℕ) :
    Antitone (dimensionTail K k) := by
  intro m n hmn x hx
  exact dimensionSubring_antitone ℤ K (Nat.add_le_add_left hmn k) hx

/-- A finite dimension term plus a zero omega intersection forces eventual vanishing. -/
theorem dimensionSubring_eventually_eq_bot_of_finite_of_omega_eq_bot
    (k : ℕ) [Finite (dimensionSubring ℤ K k)]
    (homega : dimensionSubringOmega ℤ K = ⊥) :
    ∃ s : ℕ, dimensionSubring ℤ K s = ⊥ := by
  let tailOrderHom : ℕ →o (Submodule ℤ (dimensionSubring ℤ K k))ᵒᵈ :=
    { toFun := fun n ↦ OrderDual.toDual (dimensionTail K k n)
      monotone' := dimensionTail_antitone K k }
  letI : IsArtinian ℤ (dimensionSubring ℤ K k) := isArtinian_of_finite
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes tailOrderHom
  refine ⟨k + n, le_bot_iff.mp ?_⟩
  intro x hx
  have hxk : x ∈ dimensionSubring ℤ K k :=
    dimensionSubring_antitone ℤ K (Nat.le_add_right k n) hx
  let tx : dimensionSubring ℤ K k := ⟨x, hxk⟩
  have htail : tx ∈ dimensionTail K k n := hx
  have hxomega : x ∈ dimensionSubringOmega ℤ K := by
    rw [mem_dimensionSubringOmega]
    intro q
    let m := max n q
    have hnm : n ≤ m := Nat.le_max_left n q
    have hstable : dimensionTail K k n = dimensionTail K k m := by
      exact congrArg OrderDual.ofDual (hn m hnm)
    have htm : tx ∈ dimensionTail K k m := by
      rw [← hstable]
      exact htail
    have hkm : x ∈ dimensionSubring ℤ K (k + m) := htm
    exact dimensionSubring_antitone ℤ K
      (le_trans (Nat.le_max_right n q) (Nat.le_add_left m k)) hkm
  rw [homega] at hxomega
  exact hxomega

end

end LieRings.Plotkin
