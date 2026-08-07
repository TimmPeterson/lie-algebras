import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneousFactors

/-!
# Normalized commutator corrections for finite Smith rows

Bracketing a Smith row of weight `s` with a homogeneous basis factor of weight `w` produces an
actual defining relation of minimum weight `s+w`.  Here it is expanded into individual Smith
rows through weight four plus a genuine weight-five remainder.  Coefficients below `s+w` are
proved to vanish, which is the strict first-coordinate descent in the placed collector.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- A low Smith row bundled as a defining relation. -/
def lowRelationSmithRowKernel
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) :
    LinearMap.ker evaluation.toLinearMap :=
  ⟨lowRelationSmithRow X L evaluation i,
    lowRelationSmithRow_mem_ker X L evaluation i⟩

/-- The commutator correction is again a defining relation. -/
def lowRelationSmithRowBracketKernel
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation)
    (x : LowHomogeneousBasisIndex X) :
    LinearMap.ker evaluation.toLinearMap :=
  ⟨⁅lowRelationSmithRow X L evaluation i,
      lowHomogeneousBasisValue X x⁆, by
    change evaluation ⁅lowRelationSmithRow X L evaluation i,
      lowHomogeneousBasisValue X x⁆ = 0
    rw [LieHom.map_lie, lowRelationSmithRow_mem_ker, zero_lie]⟩

/-- The bracket correction starts in the sum of the two declared weights. -/
theorem lowRelationSmithRowBracketKernel_mem_lieHigh
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation)
    (x : LowHomogeneousBasisIndex X) :
    (lowRelationSmithRowBracketKernel X L evaluation i x : F) ∈
      FreeLieDimension.lieHigh X
        (lowRelationSmithRowWeight X L evaluation i +
          lowHomogeneousBasisWeight X x) := by
  exact FreeLieDimension.lieHigh_lie_mem X
    (lowRelationSmithRow_mem_lieHigh X L evaluation i)
    (lowHomogeneousFilteredFactor X x).filtered

/-- Normalized Smith-row coefficients of a relation commutator. -/
def lowRelationBracketRowCoefficients
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation)
    (x : LowHomogeneousBasisIndex X) :
    LowRelationSmithRowIndex X L evaluation →₀ ℤ :=
  fourLowRelationSmithRowCoefficients X L evaluation
    (lowRelationSmithRowBracketKernel X L evaluation i x)

/-- No normalized correction row has weight below `s+w`. -/
theorem lowRelationBracketRowCoefficients_apply_eq_zero_of_lt
    (evaluation : LieHom ℤ F L)
    (i j : LowRelationSmithRowIndex X L evaluation)
    (x : LowHomogeneousBasisIndex X)
    (hj : lowRelationSmithRowWeight X L evaluation j <
      lowRelationSmithRowWeight X L evaluation i +
        lowHomogeneousBasisWeight X x) :
    lowRelationBracketRowCoefficients X L evaluation i x j = 0 := by
  exact fourLowRelationSmithRowCoefficients_apply_eq_zero_of_lt
    X L evaluation (lowRelationSmithRowBracketKernel X L evaluation i x) j
      (lowRelationSmithRowBracketKernel_mem_lieHigh X L evaluation i x) hj

/-- The weight-five remainder of a normalized relation commutator. -/
def lowRelationBracketWeightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation)
    (x : LowHomogeneousBasisIndex X) :
    LinearMap.ker evaluation.toLinearMap :=
  ⟨(iteratedRelationSmithRemainder X L evaluation 4
      (lowRelationSmithRowBracketKernel X L evaluation i x) : F),
    (iteratedRelationSmithRemainder X L evaluation 4
      (lowRelationSmithRowBracketKernel X L evaluation i x)).property.1⟩

theorem lowRelationBracketWeightFiveRemainder_mem_lieHigh
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation)
    (x : LowHomogeneousBasisIndex X) :
    (lowRelationBracketWeightFiveRemainder X L evaluation i x : F) ∈
      FreeLieDimension.lieHigh X 5 :=
  fourRowWeightFiveRemainder_mem_lieHigh X L evaluation
    (lowRelationSmithRowBracketKernel X L evaluation i x)

/-- **Exact normalized relation-commutator expansion.** -/
theorem lowRelationSmithRow_bracket_eq_rows_add_weightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation)
    (x : LowHomogeneousBasisIndex X) :
    ⁅lowRelationSmithRow X L evaluation i,
        lowHomogeneousBasisValue X x⁆ =
      (lowRelationBracketRowCoefficients X L evaluation i x).sum
          (fun j c ↦ c • lowRelationSmithRow X L evaluation j) +
        (lowRelationBracketWeightFiveRemainder X L evaluation i x : F) := by
  simpa [lowRelationBracketRowCoefficients,
    lowRelationBracketWeightFiveRemainder,
    lowRelationSmithRowBracketKernel] using
      relation_eq_fourLowRelationSmithRows_add_weightFiveRemainder
        X L evaluation (lowRelationSmithRowBracketKernel X L evaluation i x)

end

end DegreeFive

end LieRings
