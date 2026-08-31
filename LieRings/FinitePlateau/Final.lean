import LieRings.FinitePlateau.Height
import LieRings.FinitePlateau.Terminal
import LieRings.FinitePlateau.TopLayer
import LieRings.FinitePlateau.HallNormalForm
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Util.AssertNoSorry

/-!
# The explicit finite-plateau family

This module assembles the elementary height, exact-order, Hall--Magnus
critical calculation, and terminal vanishing for the manuscript's family
`L N`.  The conditional assembly lemmas isolate the final monotonicity
argument, while the public theorems invoke the proved critical containment.
-/

namespace LieRings.FinitePlateau

noncomputable section

/-- Because the distinguished generator is central, its Lie-ideal span is
exactly its ordinary additive cyclic span. -/
theorem exceptionalIdeal_toSubmodule_eq_span
    (N : ℕ) (hN : 1 ≤ N) :
    (exceptionalIdeal N).toSubmodule = ℤ ∙ a N := by
  apply le_antisymm
  · intro z hz
    change z ∈ LieSubmodule.lieSpan ℤ (L N) {a N} at hz
    induction hz using LieSubmodule.lieSpan_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact (ℤ ∙ a N).zero_mem
    | add x y hx hy ihx ihy => exact (ℤ ∙ a N).add_mem ihx ihy
    | smul n x hx ih => exact (ℤ ∙ a N).smul_mem n ih
    | lie x y hy ih =>
        have hyCenter := exceptionalIdeal_le_center N hN hy
        rw [LieModule.mem_maxTrivSubmodule] at hyCenter
        rw [hyCenter x]
        exact (ℤ ∙ a N).zero_mem
  · exact LieSubmodule.submodule_span_le_lieSpan

/-- The exceptional ideal is canonically an additive cyclic group of order
two.  The equivalence sends the additive span of `a` through the standard
quotient-by-additive-order description. -/
def exceptionalIdealEquivZModTwo
    (N : ℕ) (hN : 1 ≤ N) :
    exceptionalIdeal N ≃ₗ[ℤ] ZMod 2 := by
  have horderInt : (addOrderOf (a N) : ℤ) = (2 : ℤ) := by
    exact_mod_cast addOrderOf_a_eq_two N hN
  have hspan :
      (Ideal.span {(addOrderOf (a N) : ℤ)} : Submodule ℤ ℤ) =
        (Ideal.span {(2 : ℤ)} : Submodule ℤ ℤ) := by
    rw [horderInt]
  exact
    (LinearEquiv.ofEq (exceptionalIdeal N).toSubmodule (ℤ ∙ a N)
      (exceptionalIdeal_toSubmodule_eq_span N hN)).trans
      ((CharacterModule.intSpanEquivQuotAddOrderOf (a N)).trans
        ((Submodule.quotEquivOfEq _ _ hspan).trans
          (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv))

theorem exceptionalIdeal_ne_bot (N : ℕ) (hN : 1 ≤ N) :
    exceptionalIdeal N ≠ ⊥ := by
  intro hbot
  have ha : a N ∈ exceptionalIdeal N := by
    change a N ∈ LieSubmodule.lieSpan ℤ (L N) {a N}
    exact LieSubmodule.subset_lieSpan (Set.mem_singleton (a N))
  rw [hbot] at ha
  exact a_ne_zero N hN (by simpa using ha)

/-- Monotonicity propagates the critical equality across the entire claimed
plateau. -/
theorem dimensionSubring_eq_exceptionalIdeal_of_critical_upper
    (N : ℕ) (hN : 1 ≤ N)
    (hcritical : dimensionSubring ℤ (L N) (N + 4) ≤ exceptionalIdeal N)
    (q : ℕ) (hqlower : N + 4 ≤ q) (hqupper : q ≤ 2 * N + 4) :
    dimensionSubring ℤ (L N) q = exceptionalIdeal N := by
  apply le_antisymm
  · exact (dimensionSubring_antitone ℤ (L N) hqlower).trans hcritical
  · exact (exceptionalIdeal_le_dimensionSubring_twoN_add_four N hN).trans
      (dimensionSubring_antitone ℤ (L N) hqupper)

/-- Complete assembly of the explicit-family form of Theorem A from the one
critical upper containment.  Besides the plateau itself, the conclusion
records metabelianity, exact nilpotency class `N+3` (in zero-based lower
central indexing), the identification of the plateau with `ZMod 2`, and
the terminal strict drop to zero. -/
theorem finite_plateau_theoremA_of_critical_upper
    (N : ℕ) (hN : 1 ≤ N)
    (hcritical : dimensionSubring ℤ (L N) (N + 4) ≤ exceptionalIdeal N) :
    IsMetabelian (L N) ∧
      (lowerCentralSeries ℤ (L N) (N + 2) ≠ ⊥ ∧
        lowerCentralSeries ℤ (L N) (N + 3) = ⊥) ∧
      (∀ q : ℕ, N + 4 ≤ q → q ≤ 2 * N + 4 →
        dimensionSubring ℤ (L N) q = exceptionalIdeal N) ∧
      Nonempty (exceptionalIdeal N ≃ₗ[ℤ] ZMod 2) ∧
      dimensionSubring ℤ (L N) (2 * N + 5) = ⊥ ∧
      dimensionSubring ℤ (L N) (2 * N + 4) ≠
        dimensionSubring ℤ (L N) (2 * N + 5) := by
  have hplateau : ∀ q : ℕ, N + 4 ≤ q → q ≤ 2 * N + 4 →
      dimensionSubring ℤ (L N) q = exceptionalIdeal N := by
    intro q hqlower hqupper
    exact dimensionSubring_eq_exceptionalIdeal_of_critical_upper
      N hN hcritical q hqlower hqupper
  have hterminal := terminal_dimensionSubring_eq_bot N
  have hlast := hplateau (2 * N + 4) (by omega) le_rfl
  refine ⟨isMetabelian N, exact_lowerCentral_height N hN, hplateau,
    ⟨exceptionalIdealEquivZModTwo N hN⟩, hterminal, ?_⟩
  rw [hlast, hterminal]
  exact exceptionalIdeal_ne_bot N hN

/-- The literal plateau-and-drop formulation used in the statement of the
manuscript theorem, still isolated from the filtered critical upper bound.
The witness is `m = N + 4`. -/
theorem finite_plateau_publication_of_critical_upper
    (N : ℕ) (hN : 1 ≤ N)
    (hcritical : dimensionSubring ℤ (L N) (N + 4) ≤ exceptionalIdeal N) :
    ∃ m : ℕ, 1 ≤ m ∧
      (∀ q : ℕ, m ≤ q → q ≤ m + N →
        dimensionSubring ℤ (L N) q = dimensionSubring ℤ (L N) m) ∧
      dimensionSubring ℤ (L N) (m + N) ≠
        dimensionSubring ℤ (L N) (m + N + 1) := by
  let m := N + 4
  have hm : 1 ≤ m := by
    dsimp [m]
    omega
  have hmEq : dimensionSubring ℤ (L N) m = exceptionalIdeal N := by
    exact dimensionSubring_eq_exceptionalIdeal_of_critical_upper
      N hN hcritical m (by simp [m]) (by dsimp [m]; omega)
  refine ⟨m, hm, ?_, ?_⟩
  · intro q hqlower hqupper
    rw [hmEq]
    exact dimensionSubring_eq_exceptionalIdeal_of_critical_upper
      N hN hcritical q (by simpa [m] using hqlower) (by dsimp [m] at hqupper; omega)
  · have hlast : dimensionSubring ℤ (L N) (m + N) = exceptionalIdeal N := by
      exact dimensionSubring_eq_exceptionalIdeal_of_critical_upper
        N hN hcritical (m + N) (by dsimp [m]; omega) (by dsimp [m]; omega)
    have hterminal : dimensionSubring ℤ (L N) (m + N + 1) = ⊥ := by
      rw [show m + N + 1 = 2 * N + 5 by dsimp [m]; omega]
      exact terminal_dimensionSubring_eq_bot N
    rw [hlast, hterminal]
    exact exceptionalIdeal_ne_bot N hN

/-- **The explicit-family form of Theorem A.**  For every `N ≥ 1`, the
presented Lie ring is metabelian of exact nilpotency class `N+3`; its
dimension series is constantly the exceptional cyclic ideal of order two
from `N+4` through `2N+4`, and vanishes at `2N+5`. -/
theorem finite_plateau_theoremA
    (N : ℕ) (hN : 1 ≤ N) :
    IsMetabelian (L N) ∧
      (lowerCentralSeries ℤ (L N) (N + 2) ≠ ⊥ ∧
        lowerCentralSeries ℤ (L N) (N + 3) = ⊥) ∧
      (∀ q : ℕ, N + 4 ≤ q → q ≤ 2 * N + 4 →
        dimensionSubring ℤ (L N) q = exceptionalIdeal N) ∧
      Nonempty (exceptionalIdeal N ≃ₗ[ℤ] ZMod 2) ∧
      dimensionSubring ℤ (L N) (2 * N + 5) = ⊥ ∧
      dimensionSubring ℤ (L N) (2 * N + 4) ≠
        dimensionSubring ℤ (L N) (2 * N + 5) :=
  finite_plateau_theoremA_of_critical_upper N hN
    (dimensionSubring_critical_le_exceptionalIdeal N hN)

/-- The literal plateau-and-drop statement of the publication, with the
explicit witness `m=N+4` supplied by `L N`. -/
theorem finite_plateau_publication
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ m : ℕ, 1 ≤ m ∧
      (∀ q : ℕ, m ≤ q → q ≤ m + N →
        dimensionSubring ℤ (L N) q = dimensionSubring ℤ (L N) m) ∧
      dimensionSubring ℤ (L N) (m + N) ≠
        dimensionSubring ℤ (L N) (m + N + 1) :=
  finite_plateau_publication_of_critical_upper N hN
    (dimensionSubring_critical_le_exceptionalIdeal N hN)

end

end LieRings.FinitePlateau

assert_no_sorry LieRings.FinitePlateau.finite_plateau_theoremA_of_critical_upper
assert_no_sorry LieRings.FinitePlateau.finite_plateau_publication_of_critical_upper
assert_no_sorry LieRings.FinitePlateau.finite_plateau_theoremA
assert_no_sorry LieRings.FinitePlateau.finite_plateau_publication
