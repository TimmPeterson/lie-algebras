import LieRings.Plotkin.Nilpotent
import LieRings.DimensionSubring.Functoriality
import LieRings.DimensionSubring.Centrality
import Mathlib.Util.AssertNoSorry

/-!
# The finitely generated Plotkin theorem

This file contains the formal quotient argument after the nilpotent theorem.  The conditional
helpers expose central-prime separation explicitly; the public results discharge it using the
central-separation construction.
-/

namespace LieRings.Plotkin

noncomputable section

universe u

/-- Quotienting by a lower-central term kills that term in the quotient. -/
theorem lowerCentralSeries_quotient_eq_bot
    (L : Type u) [LieRing L] (c : ℕ) :
    lowerCentralSeries ℤ (L ⧸ lowerCentralSeries ℤ L c) c = ⊥ := by
  let I : LieIdeal ℤ L := lowerCentralSeries ℤ L c
  let q : L →ₗ⁅ℤ⁆ L ⧸ I := UEA.lieIdealQuotientMk ℤ L I
  have hq : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' I
  change LieModule.lowerCentralSeries ℤ (L ⧸ I) (L ⧸ I) c = ⊥
  rw [← LieIdeal.lowerCentralSeries_map_eq c hq,
    LieIdeal.map_eq_bot_iff]
  intro x hx
  change (LieSubmodule.Quotient.mk x : L ⧸ I) = 0
  exact (LieSubmodule.Quotient.mk_eq_zero' (N := I)).mpr hx

/-- For every fixed lower-central term, a sufficiently deep dimension term is contained in it. -/
theorem finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries_of_separation
    (L : Type u) [LieRing L] (hL : LieRings.IsFinitelyGenerated L) (n : ℕ)
    (hsep : HasCentralPrimeSeparation
      (L ⧸ lowerCentralSeries ℤ L n)) :
    ∃ m : ℕ, dimensionSubring ℤ L m ≤ lowerCentralSeries ℤ L n := by
  let I : LieIdeal ℤ L := lowerCentralSeries ℤ L n
  have hquotFG : IsFinitelyGenerated (L ⧸ I) :=
    LieRings.IsFinitelyGenerated.quotient hL I
  have hquotClass : lowerCentralSeries ℤ (L ⧸ I) n = ⊥ := by
    exact lowerCentralSeries_quotient_eq_bot L n
  obtain ⟨m, hm⟩ :=
    dimensionSubring_eventually_eq_bot_of_finitelyGenerated_of_lowerCentralSeries_eq_bot_of_separation
      hquotFG n hquotClass hsep
  exact ⟨m, dimensionSubring_le_of_quotient_eq_bot ℤ L I m hm⟩

/-- For every zero-based lower-central term, a sufficiently deep dimension
term is contained in it. -/
theorem finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries
    (L : Type u) [LieRing L] (hL : LieRings.IsFinitelyGenerated L) (n : ℕ) :
    ∃ m : ℕ, dimensionSubring ℤ L m ≤ lowerCentralSeries ℤ L n := by
  let I : LieIdeal ℤ L := lowerCentralSeries ℤ L n
  have hquotFG : IsFinitelyGenerated (L ⧸ I) :=
    LieRings.IsFinitelyGenerated.quotient hL I
  have hquotClass : lowerCentralSeries ℤ (L ⧸ I) n = ⊥ :=
    lowerCentralSeries_quotient_eq_bot L n
  exact
    finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries_of_separation
      L hL n
      (hasCentralPrimeSeparation_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
        hquotFG n hquotClass)

/-- Manuscript-indexed form: `lowerCentralSeries ℤ L (n - 1)` is
`γₙ(L)`, since Mathlib starts the lower-central series at index zero. -/
theorem finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries_oneIndexed
    (L : Type u) [LieRing L] (hL : LieRings.IsFinitelyGenerated L)
    (n : ℕ) (_hn : 1 ≤ n) :
    ∃ m : ℕ, dimensionSubring ℤ L m ≤
      lowerCentralSeries ℤ L (n - 1) :=
  finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries
    L hL (n - 1)

/-- Conditional final form: under central-prime separation, the two omega intersections agree. -/
theorem finitelyGenerated_dimensionSubringOmega_eq_lowerCentralSeriesOmega_of_separation
    (L : Type u) [LieRing L] (hL : LieRings.IsFinitelyGenerated L)
    (hsep : ∀ n : ℕ, HasCentralPrimeSeparation
      (L ⧸ lowerCentralSeries ℤ L n)) :
    dimensionSubringOmega ℤ L = lowerCentralSeriesOmega ℤ L := by
  apply le_antisymm
  · intro x hx
    rw [mem_lowerCentralSeriesOmega]
    intro n
    obtain ⟨m, hm⟩ :=
      finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries_of_separation
        L hL n (hsep n)
    exact hm ((mem_dimensionSubringOmega ℤ L).mp hx m)
  · exact lowerCentralSeriesOmega_le_dimensionSubringOmega ℤ L

/-- The Plotkin equality for every finitely generated Lie ring. -/
theorem finitelyGenerated_dimensionSubringOmega_eq_lowerCentralSeriesOmega
    (L : Type u) [LieRing L] (hL : LieRings.IsFinitelyGenerated L) :
    dimensionSubringOmega ℤ L = lowerCentralSeriesOmega ℤ L := by
  apply
    finitelyGenerated_dimensionSubringOmega_eq_lowerCentralSeriesOmega_of_separation
      L hL
  intro n
  let I : LieIdeal ℤ L := lowerCentralSeries ℤ L n
  exact hasCentralPrimeSeparation_of_finitelyGenerated_of_lowerCentralSeries_eq_bot
    (LieRings.IsFinitelyGenerated.quotient hL I) n
    (lowerCentralSeries_quotient_eq_bot L n)

end

end LieRings.Plotkin

assert_no_sorry LieRings.Plotkin.lowerCentralSeries_quotient_eq_bot
assert_no_sorry
  LieRings.Plotkin.finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries_of_separation
assert_no_sorry
  LieRings.Plotkin.finitelyGenerated_dimensionSubringOmega_eq_lowerCentralSeriesOmega_of_separation
assert_no_sorry
  LieRings.Plotkin.finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries
assert_no_sorry
  LieRings.Plotkin.finitelyGenerated_dimensionSubring_eventually_le_lowerCentralSeries_oneIndexed
assert_no_sorry
  LieRings.Plotkin.finitelyGenerated_dimensionSubringOmega_eq_lowerCentralSeriesOmega
