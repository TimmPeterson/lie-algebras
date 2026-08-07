import LieRings.DimensionSubring.Centrality

/-!
# Small examples: applying dimension centrality

These examples are intentionally short.  They are meant to be copied into downstream files.
-/

namespace LieRings.Examples

universe u

variable (L : Type u) [LieRing L] [LieAlgebra ℤ L]

/-- Over `ℤ`, the library theorem directly states `[δₙ₊₁(L),L] = γₙ₊₂(L)`. -/
example (n : ℕ) :
    ⁅dimensionSubring ℤ L (n + 1), (⊤ : LieIdeal ℤ L)⁆ =
      lowerCentralSeries ℤ L (n + 1) :=
  dimensionSubring_bracket_eq_lowerCentralSeries ℤ L n

/-- The same theorem when the index is already known to be positive. -/
example (n : ℕ) (hn : 1 ≤ n) :
    ⁅dimensionSubring ℤ L n, (⊤ : LieIdeal ℤ L)⁆ = lowerCentralSeries ℤ L n :=
  dimensionSubring_bracket_eq_lowerCentralSeries_of_pos ℤ L hn

/-- A typical one-line consequence: `δₙ₊₁` is central modulo `γₙ₊₁`. -/
example (n : ℕ) :
    ⁅dimensionSubring ℤ L (n + 1), (⊤ : LieIdeal ℤ L)⁆ ≤
      lowerCentralSeries ℤ L n :=
  dimensionSubring_bracket_le_previousLowerCentralSeries ℤ L n

/-- Strong centrality of the dimension filtration. -/
example (m n : ℕ) :
    ⁅dimensionSubring ℤ L (m + 1), dimensionSubring ℤ L (n + 1)⁆ ≤
      lowerCentralSeries ℤ L (m + n + 1) :=
  bracket_dimensionSubring_le_lowerCentralSeries ℤ L m n

/-- The same result in the conventional positive indexing:
`[δₘ(L),δₙ(L)] ⊆ γₘ₊ₙ(L)`. -/
example (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ⁅dimensionSubring ℤ L m, dimensionSubring ℤ L n⁆ ≤
      lowerCentralSeries ℤ L (m + n - 1) :=
  bracket_dimensionSubring_le_lowerCentralSeries_of_pos ℤ L hm hn

end LieRings.Examples
