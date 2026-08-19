import LieRings.DimensionSubring.MetabelianVanishing.GlobalLiteralOperations

/-!
# Oriented comparison cells

This is the literal square from the corrected closed-square proof.  Its four
edges are retained separately with their manuscript orientations.  The raw
boundary is the difference `H (V R) - V (H R)`; it vanishes only after
evaluation, equivalently after expansion in the fixed adapted PBW basis.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance globalComparisonCellFintype : Fintype L :=
  Fintype.ofFinite L

/-- A comparison cell based at one finite signed occurrence list. -/
structure ComparisonCell where
  base : ProvenancedRow n L data hn →₀ ℤ

namespace ComparisonCell

/-- The oriented horizontal edge `h(R)`. -/
def top (c : ComparisonCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  c.base - horizontalOperation n L data hn c.base

/-- The oppositely oriented horizontal edge `-h(VR)`. -/
def bottom (c : ComparisonCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  -verticalOperation n L data hn c.base +
    horizontalOperation n L data hn
      (verticalOperation n L data hn c.base)

/-- The oppositely oriented vertical edge `-v(R)`. -/
def right (c : ComparisonCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  -c.base + verticalOperation n L data hn c.base

/-- The oriented vertical edge `v(HR)`. -/
def left (c : ComparisonCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  horizontalOperation n L data hn c.base -
    verticalOperation n L data hn
      (horizontalOperation n L data hn c.base)

/-- Sum of the four oriented incidences of a comparison cell. -/
def boundary (c : ComparisonCell n L data hn) :
    ProvenancedRow n L data hn →₀ ℤ :=
  c.top n L data hn + c.bottom n L data hn +
    c.right n L data hn + c.left n L data hn

/-- Before canonical expansion, the only uncancelled corners are the two
orders of the horizontal and vertical operations. -/
theorem boundary_eq_horizontal_vertical_sub
    (c : ComparisonCell n L data hn) :
    c.boundary n L data hn =
      horizontalOperation n L data hn
          (verticalOperation n L data hn c.base) -
        verticalOperation n L data hn
          (horizontalOperation n L data hn c.base) := by
  classical
  simp only [boundary, top, bottom, right, left]
  abel

/-- The evaluated boundary of every comparison cell is zero. -/
theorem evaluate_boundary_eq_zero (c : ComparisonCell n L data hn) :
    Finsupp.linearCombination ℤ (ProvenancedRow.value n L data hn)
        (c.boundary n L data hn) = 0 := by
  rw [boundary_eq_horizontal_vertical_sub, map_sub,
    evaluate_horizontalOperation, evaluate_verticalOperation,
    evaluate_verticalOperation, evaluate_horizontalOperation, sub_self]

/-- Coefficientwise finite-Stokes identity for a single cell in the fixed
canonical placed-basis incidence group. -/
theorem canonicalPlacedExpansion_boundary_eq_zero
    (c : ComparisonCell n L data hn) :
    canonicalPlacedExpansion n L data hn (c.boundary n L data hn) = 0 := by
  rw [boundary_eq_horizontal_vertical_sub, map_sub,
    canonicalPlacedExpansion_horizontal_vertical, sub_self]

end ComparisonCell

end


end LieRings.MetabelianVanishing
