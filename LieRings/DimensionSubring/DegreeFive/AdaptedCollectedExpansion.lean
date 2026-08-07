import LieRings.DimensionSubring.DegreeFive.AdaptedCollectorBasis

/-!
# Coefficient expansion in the common collected presentation

This file is the coefficient-level companion of `AdaptedPresentation`.  Every coefficient is
read from `collectedLeadingRelationBasis`, and every tagged summand is interpreted by
`collectedRelationRow`.  Thus the expansion cannot accidentally return to the pre-Smith free
Lie basis.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X

/-- Coordinates of a leading relation in the sorted collected relation basis. -/
def collectedRelationRowCoefficients
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (d : homogeneousRelationLeading X L evaluation n) :
    FreeLieExactBasisIndex X n →₀ ℤ :=
  (collectedLeadingRelationBasis X L evaluation n).repr d

/-- Evaluating those coordinates gives the sorted collected row lift. -/
theorem collectedRelationRowCoefficients_sum
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (d : homogeneousRelationLeading X L evaluation n) :
    (collectedRelationRowCoefficients X L evaluation n d).sum
        (fun i c ↦ c • (collectedRelationRow X L evaluation n i : F)) =
      collectedRelationRowLift X L evaluation n d := by
  change ((collectedLeadingRelationBasis X L evaluation n).repr d).sum
      (fun i c ↦ c • (collectedRelationRow X L evaluation n i : F)) = _
  rw [collectedRelationRowLift, Module.Basis.constr_apply]

/-- Coefficients removed at stage `k`, embedded into the common low-factor index. -/
def iteratedCollectedLowRowCoefficients
    (evaluation : LieHom ℤ F L) (k : Fin 4)
    (r : LinearMap.ker evaluation.toLinearMap) :
    AdaptedLowRelationRowIndex X →₀ ℤ :=
  (collectedRelationRowCoefficients X L evaluation (k.1 + 1)
      (filteredRelationLeading X L evaluation (k.1 + 1)
        (iteratedCollectedRelationRemainder X L evaluation k.1 r))).mapDomain
    (adaptedLowBasisIndexOf X (by omega) (by omega))

/-- Before its first possible nonzero weight, collected elimination removes nothing. -/
theorem iteratedCollectedRelationRemainder_eq_of_mem_lieHigh
    (evaluation : LieHom ℤ F L) (r : LinearMap.ker evaluation.toLinearMap)
    {t k : ℕ} (hr : (r : F) ∈ FreeLieDimension.lieHigh X t)
    (hk : k + 1 ≤ t) :
    (iteratedCollectedRelationRemainder X L evaluation k r : F) = (r : F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkt : k + 1 < t := by omega
      have ih' : (iteratedCollectedRelationRemainder X L evaluation k r : F) =
          (r : F) := ih (by omega)
      change collectedRelationRemainder X L evaluation (k + 1)
          (iteratedCollectedRelationRemainder X L evaluation k r) = (r : F)
      unfold collectedRelationRemainder
      have hleading : filteredRelationLeading X L evaluation (k + 1)
          (iteratedCollectedRelationRemainder X L evaluation k r) = 0 := by
        apply Subtype.ext
        change freeLieExactProjection X (k + 1)
            (iteratedCollectedRelationRemainder X L evaluation k r : F) = 0
        rw [ih']
        apply Subtype.ext
        exact freeLieLengthComponent_eq_zero_of_mem_lieHigh X hr hkt
      rw [hleading, map_zero, sub_zero, ih']

/-- Hence every collected-row coefficient below the first possible weight vanishes. -/
theorem iteratedCollectedLowRowCoefficients_eq_zero_of_lt
    (evaluation : LieHom ℤ F L) (r : LinearMap.ker evaluation.toLinearMap)
    (k : Fin 4) {t : ℕ} (hr : (r : F) ∈ FreeLieDimension.lieHigh X t)
    (hk : k.1 + 1 < t) :
    iteratedCollectedLowRowCoefficients X L evaluation k r = 0 := by
  unfold iteratedCollectedLowRowCoefficients collectedRelationRowCoefficients
  have hrem := iteratedCollectedRelationRemainder_eq_of_mem_lieHigh
    X L evaluation r hr (by omega : k.1 + 1 ≤ t)
  have hleading : filteredRelationLeading X L evaluation (k.1 + 1)
      (iteratedCollectedRelationRemainder X L evaluation k.1 r) = 0 := by
    apply Subtype.ext
    change freeLieExactProjection X (k.1 + 1)
        (iteratedCollectedRelationRemainder X L evaluation k.1 r : F) = 0
    rw [hrem]
    apply Subtype.ext
    exact freeLieLengthComponent_eq_zero_of_mem_lieHigh X hr hk
  rw [hleading]
  have hz : (collectedLeadingRelationBasis X L evaluation (k.1 + 1)).repr
      (0 : homogeneousRelationLeading X L evaluation (k.1 + 1)) = 0 :=
    (collectedLeadingRelationBasis X L evaluation (k.1 + 1)).repr.map_zero
  rw [hz]
  rfl

@[simp]
theorem iteratedCollectedLowRowCoefficients_apply_same
    (evaluation : LieHom ℤ F L) (k : Fin 4)
    (r : LinearMap.ker evaluation.toLinearMap)
    (i : FreeLieExactBasisIndex X (k.1 + 1)) :
    iteratedCollectedLowRowCoefficients X L evaluation k r
        (adaptedLowBasisIndexOf X (by omega) (by omega) i) =
      collectedRelationRowCoefficients X L evaluation (k.1 + 1)
        (filteredRelationLeading X L evaluation (k.1 + 1)
          (iteratedCollectedRelationRemainder X L evaluation k.1 r)) i := by
  rw [iteratedCollectedLowRowCoefficients, Finsupp.mapDomain_apply]
  intro a b hab
  exact Fin.ext (congrArg (fun z ↦ z.2.1) hab)

/-- One embedded stage evaluates to exactly the corresponding sorted row part. -/
theorem iteratedCollectedLowRowCoefficients_sum
    (evaluation : LieHom ℤ F L) (k : Fin 4)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (iteratedCollectedLowRowCoefficients X L evaluation k r).sum
        (fun i c ↦ c • adaptedLowRelationRow X L evaluation i) =
      iteratedCollectedRelationRowPart X L evaluation k.1 r := by
  unfold iteratedCollectedLowRowCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · simpa only [adaptedLowRelationRow, adaptedLowBasisIndexOf] using
      collectedRelationRowCoefficients_sum X L evaluation (k.1 + 1)
        (filteredRelationLeading X L evaluation (k.1 + 1)
          (iteratedCollectedRelationRemainder X L evaluation k.1 r))
  · intro i
    simp
  · intro i a b
    simp [add_smul]

/-- Coefficients of all sorted rows removed through weight four. -/
def fourCollectedLowRowCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    AdaptedLowRelationRowIndex X →₀ ℤ :=
  ∑ k : Fin 4, iteratedCollectedLowRowCoefficients X L evaluation k r

/-- A relation of minimum weight `t` has no collected-row coefficient below `t`. -/
theorem fourCollectedLowRowCoefficients_apply_eq_zero_of_lt
    (evaluation : LieHom ℤ F L) (r : LinearMap.ker evaluation.toLinearMap)
    (i : AdaptedLowRelationRowIndex X) {t : ℕ}
    (hr : (r : F) ∈ FreeLieDimension.lieHigh X t)
    (hi : adaptedLowRelationRowWeight X i < t) :
    fourCollectedLowRowCoefficients X L evaluation r i = 0 := by
  unfold fourCollectedLowRowCoefficients
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k.1 + 1 = adaptedLowRelationRowWeight X i
  · have hkval : k.1 = i.1.1 := by
      simpa [adaptedLowRelationRowWeight, adaptedLowBasisWeight] using hki
    have hkfin : k = i.1 := Fin.ext hkval
    subst k
    rw [iteratedCollectedLowRowCoefficients_eq_zero_of_lt
      X L evaluation r i.1 hr]
    rfl
    exact hi
  · apply Finsupp.mapDomain_notin_range
    rintro ⟨j, hj⟩
    apply hki
    have hw := congrArg (adaptedLowBasisWeight X) hj
    simpa [adaptedLowRelationRowWeight] using hw

/-- The four-stage coefficient family evaluates to the four collected row parts. -/
theorem fourCollectedLowRowCoefficients_sum
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (fourCollectedLowRowCoefficients X L evaluation r).sum
        (fun i c ↦ c • adaptedLowRelationRow X L evaluation i) =
      ∑ k : Fin 4, iteratedCollectedRelationRowPart X L evaluation k.1 r := by
  unfold fourCollectedLowRowCoefficients
  let φ : (AdaptedLowRelationRowIndex X →₀ ℤ) →ₗ[ℤ] F :=
    Finsupp.linearCombination ℤ (adaptedLowRelationRow X L evaluation)
  change φ (∑ k : Fin 4,
      iteratedCollectedLowRowCoefficients X L evaluation k r) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact iteratedCollectedLowRowCoefficients_sum X L evaluation k r

/-- Exact relation expansion through weight four, entirely in common collected row tags. -/
theorem relation_eq_fourCollectedLowRows_add_weightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (r : F) =
      (fourCollectedLowRowCoefficients X L evaluation r).sum
          (fun i c ↦ c • adaptedLowRelationRow X L evaluation i) +
        (iteratedCollectedRelationRemainder X L evaluation 4 r : F) := by
  rw [fourCollectedLowRowCoefficients_sum]
  simpa only [Fin.sum_univ_four] using
    relation_eq_four_collected_rowParts_add_weightFiveRemainder
      X L evaluation r

/-- The residual is an actual defining relation. -/
theorem fourCollectedWeightFiveRemainder_mem_ker
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    evaluation (iteratedCollectedRelationRemainder X L evaluation 4 r : F) = 0 :=
  (iteratedCollectedRelationRemainder X L evaluation 4 r).property.1

/-- The residual has minimum bracket weight five. -/
theorem fourCollectedWeightFiveRemainder_mem_lieHigh
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (iteratedCollectedRelationRemainder X L evaluation 4 r : F) ∈
      FreeLieDimension.lieHigh X 5 :=
  (iteratedCollectedRelationRemainder X L evaluation 4 r).property.2

end

end DegreeFive

end LieRings
