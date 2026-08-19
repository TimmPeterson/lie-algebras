import LieRings.DimensionSubring.MetabelianVanishing.GlobalVerticalFrontier

/-!
# Finite Stokes for the global comparison trace

The external incidence ledger is the canonically expanded sum of the four
oriented sides of every retained comparison cell.  Internal coefficient
copies are paired using their numbered paths; the preceding adjacency and
gluing theorems show that such copies occur twice with opposite signs.  This
file records the resulting finite Stokes equality before any target-specific
read or silence criterion is applied.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalFiniteStokesFintype : Fintype L :=
  Fintype.ofFinite L

/-- The literal sum of the four oriented incidence lists.  Keeping this in
the provenance row group retains full contextual relations and homogeneous
children as different constructors. -/
def traceIncidenceBoundary
    (cells : List (LabelledComparisonCell n L data hn)) :
    ProvenancedRow n L data hn →₀ ℤ :=
  (cells.map fun c ↦
    let cell := c.cell n L data hn
    cell.top n L data hn + cell.bottom n L data hn +
      cell.right n L data hn + cell.left n L data hn).sum

/-- The literal four-incidence expression is the sum of the comparison-cell
boundaries. -/
theorem traceIncidenceBoundary_eq
    (cells : List (LabelledComparisonCell n L data hn)) :
    traceIncidenceBoundary n L data hn cells =
      (cells.map fun c ↦ (c.cell n L data hn).boundary n L data hn).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  rfl

/-- Canonical coefficient ledger left after the numbered internal gluings.
The definition is deliberately independent of the later target read. -/
def canonicalExternalBoundary
    (cells : List (LabelledComparisonCell n L data hn)) :
    MvPolynomial (AdaptedIndex n L data hn) ℤ :=
  canonicalPlacedExpansion n L data hn
    (traceIncidenceBoundary n L data hn cells)

/-- Finite Stokes: the complete external boundary of any finite saturated
cell list is zero in the fixed canonical incidence group. -/
theorem canonicalExternalBoundary_eq_zero
    (cells : List (LabelledComparisonCell n L data hn)) :
    canonicalExternalBoundary n L data hn cells = 0 := by
  classical
  rw [canonicalExternalBoundary, traceIncidenceBoundary_eq, map_list_sum]
  simpa [canonicalTraceBoundary,
    LabelledComparisonCell.canonicalBoundary,
    List.map_map, Function.comp_def] using
      (canonicalTraceBoundary_eq_zero n L data hn cells)

/-- Governing-witness specialization of finite Stokes, still retaining the
literal source-labelled initial copies in the construction of the cell list. -/
theorem GoverningWitness.globalFiniteStokes
    {a : L} (w : GoverningWitness n L data a) :
    canonicalExternalBoundary n L data hn
      ((w.globalLabelledComparisonTrace n L data hn).map
        GoverningComparisonCell.cell) = 0 :=
  canonicalExternalBoundary_eq_zero n L data hn _

end

end LieRings.MetabelianVanishing
