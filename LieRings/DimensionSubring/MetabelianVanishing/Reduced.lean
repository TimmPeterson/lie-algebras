import LieRings.DimensionSubring.MetabelianVanishing.StepSeven

/-!
# The reduced odd-degree theorem

The degree-three and degree-five branches are kept separate from the general
PBW assembly.  This makes their dependency on the existing low-degree
dimension-subring theorems explicit.
-/

namespace LieRings.MetabelianVanishing

universe u

/-- The reduced conclusion in the two degrees already available in the
library. -/
theorem reducedTopLayerVanishes_of_le_two
    (n : ℕ) (L : Type u) [LieRing L] (hn : 1 ≤ n) (hn2 : n ≤ 2)
    (data : CyclicTopData n L) (a : L)
    (haDim : a ∈ dimensionSubring ℤ L (2 * n + 1))
    (_haTop : a ∈ lowerCentralSeries ℤ L n) : a = 0 := by
  letI : Finite L := data.finite_inst
  have hnCases : n = 1 ∨ n = 2 := by omega
  rcases hnCases with rfl | rfl
  · have ha : a ∈ lowerCentralSeries ℤ L 2 := by
      rw [← dimensionSubring_three_eq_lowerCentralSeries_two L]
      simpa using haDim
    rw [data.classBound] at ha
    simpa using ha
  · have ha : a ∈ lowerCentralSeries ℤ L 3 :=
      DegreeFour.dimensionSubring_five_le_lowerCentralSeries_three L (by
        simpa using haDim)
    rw [data.classBound] at ha
    simpa using ha

/-- Assemble the complete reduced theorem from the single output of Point 7.

The hypothesis is deliberately the narrowest possible Step-7 interface: it
starts with the governing witness already extracted from the dimension-subring
condition, and it is used only in degrees `n ≥ 3`.  In particular, neither of
the low-degree branches depends on the PBW/Koszul assembly. -/
theorem reducedTopLayerVanishes_of_stepSeven
    (hStepSeven :
      ∀ (n : ℕ) (L : Type u) [LieRing L] [Finite L]
        (data : CyclicTopData n L) (_hn3 : 3 ≤ n) {a : L},
        GoverningWitness n L data a → a = 0) :
    ReducedTopLayerVanishes.{u} := by
  intro n L _ hn data a haDim haTop
  by_cases hn2 : n ≤ 2
  · exact reducedTopLayerVanishes_of_le_two n L hn hn2 data a haDim haTop
  · letI : Finite L := data.finite_inst
    have hn3 : 3 ≤ n := by omega
    obtain ⟨w⟩ := exists_governingWitness n L data a haDim haTop
    exact hStepSeven n L data hn3 w

end LieRings.MetabelianVanishing
