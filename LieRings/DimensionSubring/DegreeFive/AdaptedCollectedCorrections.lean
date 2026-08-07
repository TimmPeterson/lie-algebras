import LieRings.DimensionSubring.DegreeFive.AdaptedCollectedExpansion

/-!
# Relation commutators in the common collected presentation

When a relation is moved across an adapted PBW factor, its commutator is normalized using the
same sorted rows.  This is the exact compatibility required by the placed collection step.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X

/-- A collected low row bundled as an actual defining relation. -/
def adaptedLowRelationRowKernel
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X) :
    LinearMap.ker evaluation.toLinearMap :=
  ⟨adaptedLowRelationRow X L evaluation i,
    adaptedLowRelationRow_mem_ker X L evaluation i⟩

/-- Its commutator with one collected PBW factor is again a defining relation. -/
def adaptedLowRelationRowBracketKernel
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X)
    (x : AdaptedLowBasisIndex X) :
    LinearMap.ker evaluation.toLinearMap :=
  ⟨⁅adaptedLowRelationRow X L evaluation i,
      adaptedLowBasisValue X L evaluation x⁆, by
    change evaluation ⁅adaptedLowRelationRow X L evaluation i,
      adaptedLowBasisValue X L evaluation x⁆ = 0
    rw [LieHom.map_lie, adaptedLowRelationRow_mem_ker, zero_lie]⟩

/-- The correction begins at the sum of the row and factor weights. -/
theorem adaptedLowRelationRowBracketKernel_mem_lieHigh
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X)
    (x : AdaptedLowBasisIndex X) :
    (adaptedLowRelationRowBracketKernel X L evaluation i x : F) ∈
      FreeLieDimension.lieHigh X
        (adaptedLowRelationRowWeight X i + adaptedLowBasisWeight X x) := by
  exact FreeLieDimension.lieHigh_lie_mem X
    (adaptedLowRelationRow_mem_lieHigh X L evaluation i)
    (freeLieExact_mem_lieHigh X
      (⟨adaptedLowBasisValue X L evaluation x,
        adaptedLowBasisValue_mem_exact X L evaluation x⟩ :
          freeLieExact X (adaptedLowBasisWeight X x)))

/-- Collected-row coefficients of the relation commutator. -/
def adaptedLowRelationBracketRowCoefficients
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X)
    (x : AdaptedLowBasisIndex X) :
    AdaptedLowRelationRowIndex X →₀ ℤ :=
  fourCollectedLowRowCoefficients X L evaluation
    (adaptedLowRelationRowBracketKernel X L evaluation i x)

/-- No correction row occurs below the sum of the input weights. -/
theorem adaptedLowRelationBracketRowCoefficients_apply_eq_zero_of_lt
    (evaluation : LieHom ℤ F L)
    (i j : AdaptedLowRelationRowIndex X)
    (x : AdaptedLowBasisIndex X)
    (hj : adaptedLowRelationRowWeight X j <
      adaptedLowRelationRowWeight X i + adaptedLowBasisWeight X x) :
    adaptedLowRelationBracketRowCoefficients X L evaluation i x j = 0 := by
  exact fourCollectedLowRowCoefficients_apply_eq_zero_of_lt
    X L evaluation (adaptedLowRelationRowBracketKernel X L evaluation i x) j
      (adaptedLowRelationRowBracketKernel_mem_lieHigh X L evaluation i x) hj

/-- The genuine weight-five residual of the normalized commutator. -/
def adaptedLowRelationBracketWeightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X)
    (x : AdaptedLowBasisIndex X) :
    LinearMap.ker evaluation.toLinearMap :=
  ⟨(iteratedCollectedRelationRemainder X L evaluation 4
      (adaptedLowRelationRowBracketKernel X L evaluation i x) : F),
    (iteratedCollectedRelationRemainder X L evaluation 4
      (adaptedLowRelationRowBracketKernel X L evaluation i x)).property.1⟩

theorem adaptedLowRelationBracketWeightFiveRemainder_mem_lieHigh
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X)
    (x : AdaptedLowBasisIndex X) :
    (adaptedLowRelationBracketWeightFiveRemainder X L evaluation i x : F) ∈
      FreeLieDimension.lieHigh X 5 :=
  fourCollectedWeightFiveRemainder_mem_lieHigh X L evaluation
    (adaptedLowRelationRowBracketKernel X L evaluation i x)

/-- Exact normalized commutator expansion, with no basis conversion left implicit. -/
theorem adaptedLowRelationRow_bracket_eq_rows_add_weightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X)
    (x : AdaptedLowBasisIndex X) :
    ⁅adaptedLowRelationRow X L evaluation i,
        adaptedLowBasisValue X L evaluation x⁆ =
      (adaptedLowRelationBracketRowCoefficients X L evaluation i x).sum
          (fun j c ↦ c • adaptedLowRelationRow X L evaluation j) +
        (adaptedLowRelationBracketWeightFiveRemainder
          X L evaluation i x : F) := by
  simpa [adaptedLowRelationBracketRowCoefficients,
    adaptedLowRelationBracketWeightFiveRemainder,
    adaptedLowRelationRowBracketKernel] using
      relation_eq_fourCollectedLowRows_add_weightFiveRemainder
        X L evaluation
          (adaptedLowRelationRowBracketKernel X L evaluation i x)

end

end DegreeFive

end LieRings
