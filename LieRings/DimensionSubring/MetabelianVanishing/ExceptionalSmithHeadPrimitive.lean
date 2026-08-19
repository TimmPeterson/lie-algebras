import LieRings.DimensionSubring.MetabelianVanishing.OrderedPBWPrimitive

/-!
# The ordered Smith-head primitive

This file records the sign convention used for the exceptional Smith-head
row.  The actual PBW collection is proved once, in `OrderedPBWPrimitive`.
No second subset collector is introduced here.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance exceptionalSmithHeadPrimitiveFintype : Fintype L :=
  Fintype.ofFinite L

/-- If the appended adapted basis vector belongs before every spectator, its
complete primitive is the negative of the manuscript's right comb beginning
at that vector. -/
theorem pbwPrimitive_basisWord_mul_iota_head_of_le
    (h x : AdaptedIndex n L data hn)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : (x :: xs).Pairwise (· ≤ ·))
    (hhead : ∀ y ∈ x :: xs, h ≤ y) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn (x :: xs) *
          UniversalEnvelopingAlgebra.ι ℤ
            (adaptedBasis n L data hn h)) =
      -adaptedRightComb n L data hn
        (adaptedBasis n L data hn h) (x :: xs) := by
  rw [pbwPrimitive_basisWord_mul_iota_of_le_all
    n L data hn h x xs hordered hhead]
  exact adaptedRightComb_bracket_skew n L data hn x h xs

end

end LieRings.MetabelianVanishing
