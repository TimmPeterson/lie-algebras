import LieRings.DimensionSubring.DegreeFive.FiniteRelationRows

/-!
# Coefficient expansion of finite Smith relation rows

The Smith-row construction in `FiniteRelationRows` gives a linear combination of rows at
each filtration stage.  A placed collector needs the individual tagged rows and their integer
coefficients.  This file makes that finite expansion explicit and proves the exact telescoping
identity through weight four.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- A homogeneous projection below the certified minimum weight of a free-Lie element is zero. -/
theorem freeLieLengthComponent_eq_zero_of_mem_lieHigh
    {x : F} {m n : ℕ} (hx : x ∈ FreeLieDimension.lieHigh X m) (hnm : n < m) :
    freeLieLengthComponent X n x = 0 := by
  apply FreeLieDimension.freeLieToFreeAlgebra_injective_int X
  rw [freeLieToFreeAlgebra_freeLieLengthComponent, map_zero]
  apply associativeLengthComponent_eq_zero_of_mem_high X
  · obtain ⟨p, hp, rfl⟩ := hx
    rw [FreeLieDimension.freeLieToFreeAlgebra_mk]
    exact FreeLieDimension.magmaToFreeAlgebra_mem_high X hp
  · exact hnm

/-- The finite coefficient family of Smith rows representing a leading relation term. -/
def relationSmithRowCoefficients
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (d : homogeneousRelationLeading X L evaluation n) :
    RelationSmithRowIndex X L evaluation n →₀ ℤ :=
  (homogeneousRelationSmithForm X L evaluation n).bN.repr d

/-- Evaluating the coefficient family of individual Smith rows gives the row lift. -/
theorem relationSmithRowCoefficients_sum
    (evaluation : LieHom ℤ F L) (n : ℕ)
    (d : homogeneousRelationLeading X L evaluation n) :
    (relationSmithRowCoefficients X L evaluation n d).sum
        (fun i c ↦ c • (relationSmithRow X L evaluation n i : F)) =
      relationSmithRowLift X L evaluation n d := by
  change ((homogeneousRelationSmithForm X L evaluation n).bN.repr d).sum
      (fun i c ↦ c • (relationSmithRow X L evaluation n i : F)) = _
  rw [relationSmithRowLift, Module.Basis.constr_apply]

/-- The tagged union of the Smith rows in weights one through four. -/
abbrev LowRelationSmithRowIndex
    (evaluation : LieHom ℤ F L) :=
  Σ k : Fin 4, RelationSmithRowIndex X L evaluation (k.1 + 1)

/-- The actual relation represented by a low Smith-row tag. -/
def lowRelationSmithRow
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) : F :=
  relationSmithRow X L evaluation (i.1.1 + 1) i.2

/-- The certified least weight of a low Smith-row tag. -/
def lowRelationSmithRowWeight
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) : ℕ :=
  i.1.1 + 1

theorem lowRelationSmithRowWeight_pos
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) :
    0 < lowRelationSmithRowWeight X L evaluation i := by
  simp [lowRelationSmithRowWeight]

theorem lowRelationSmithRowWeight_le_four
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) :
    lowRelationSmithRowWeight X L evaluation i ≤ 4 := by
  have hi := i.1.2
  simp [lowRelationSmithRowWeight] at hi ⊢

theorem lowRelationSmithRow_mem_ker
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) :
    evaluation (lowRelationSmithRow X L evaluation i) = 0 :=
  relationSmithRow_mem_ker X L evaluation (i.1.1 + 1) i.2

theorem lowRelationSmithRow_mem_lieHigh
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) :
    lowRelationSmithRow X L evaluation i ∈
      FreeLieDimension.lieHigh X
        (lowRelationSmithRowWeight X L evaluation i) :=
  relationSmithRow_mem_lieHigh X L evaluation (i.1.1 + 1) i.2

/-- Coefficients of the Smith rows removed at one of the first four stages, embedded in the
single tagged row type. -/
def iteratedLowRelationSmithRowCoefficients
    (evaluation : LieHom ℤ F L) (k : Fin 4)
    (r : LinearMap.ker evaluation.toLinearMap) :
    LowRelationSmithRowIndex X L evaluation →₀ ℤ :=
  (relationSmithRowCoefficients X L evaluation (k.1 + 1)
      (filteredRelationLeading X L evaluation (k.1 + 1)
        (iteratedRelationSmithRemainder X L evaluation k.1 r))).mapDomain
    (fun i ↦ (⟨k, i⟩ : LowRelationSmithRowIndex X L evaluation))

/-- Before the first possible nonzero homogeneous weight, Smith elimination removes nothing. -/
theorem iteratedRelationSmithRemainder_eq_of_mem_lieHigh
    (evaluation : LieHom ℤ F L) (r : LinearMap.ker evaluation.toLinearMap)
    {t k : ℕ} (hr : (r : F) ∈ FreeLieDimension.lieHigh X t)
    (hk : k + 1 ≤ t) :
    (iteratedRelationSmithRemainder X L evaluation k r : F) = (r : F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hkt : k + 1 < t := by omega
      have ih' : (iteratedRelationSmithRemainder X L evaluation k r : F) = (r : F) :=
        ih (by omega)
      change relationSmithRemainder X L evaluation (k + 1)
          (iteratedRelationSmithRemainder X L evaluation k r) = (r : F)
      unfold relationSmithRemainder
      have hleading : filteredRelationLeading X L evaluation (k + 1)
          (iteratedRelationSmithRemainder X L evaluation k r) = 0 := by
        apply Subtype.ext
        change freeLieExactProjection X (k + 1)
            (iteratedRelationSmithRemainder X L evaluation k r : F) = 0
        rw [ih']
        apply Subtype.ext
        exact freeLieLengthComponent_eq_zero_of_mem_lieHigh X hr hkt
      rw [hleading, map_zero, sub_zero, ih']

/-- Consequently every Smith-row coefficient below the first possible weight vanishes. -/
theorem iteratedLowRelationSmithRowCoefficients_eq_zero_of_lt
    (evaluation : LieHom ℤ F L) (r : LinearMap.ker evaluation.toLinearMap)
    (k : Fin 4) {t : ℕ} (hr : (r : F) ∈ FreeLieDimension.lieHigh X t)
    (hk : k.1 + 1 < t) :
    iteratedLowRelationSmithRowCoefficients X L evaluation k r = 0 := by
  unfold iteratedLowRelationSmithRowCoefficients relationSmithRowCoefficients
  have hrem := iteratedRelationSmithRemainder_eq_of_mem_lieHigh
    X L evaluation r hr (by omega : k.1 + 1 ≤ t)
  have hleading : filteredRelationLeading X L evaluation (k.1 + 1)
      (iteratedRelationSmithRemainder X L evaluation k.1 r) = 0 := by
    apply Subtype.ext
    change freeLieExactProjection X (k.1 + 1)
        (iteratedRelationSmithRemainder X L evaluation k.1 r : F) = 0
    rw [hrem]
    apply Subtype.ext
    exact freeLieLengthComponent_eq_zero_of_mem_lieHigh X hr hk
  rw [hleading, map_zero]
  rfl

@[simp]
theorem iteratedLowRelationSmithRowCoefficients_apply_same
    (evaluation : LieHom ℤ F L) (k : Fin 4)
    (r : LinearMap.ker evaluation.toLinearMap)
    (i : RelationSmithRowIndex X L evaluation (k.1 + 1)) :
    iteratedLowRelationSmithRowCoefficients X L evaluation k r ⟨k, i⟩ =
      relationSmithRowCoefficients X L evaluation (k.1 + 1)
        (filteredRelationLeading X L evaluation (k.1 + 1)
          (iteratedRelationSmithRemainder X L evaluation k.1 r)) i := by
  rw [iteratedLowRelationSmithRowCoefficients, Finsupp.mapDomain_apply]
  intro i j hij
  exact eq_of_heq (Sigma.mk.inj_iff.mp hij |>.2)

theorem iteratedLowRelationSmithRowCoefficients_apply_ne
    (evaluation : LieHom ℤ F L) (k l : Fin 4) (hkl : k ≠ l)
    (r : LinearMap.ker evaluation.toLinearMap)
    (i : RelationSmithRowIndex X L evaluation (l.1 + 1)) :
    iteratedLowRelationSmithRowCoefficients X L evaluation k r ⟨l, i⟩ = 0 := by
  unfold iteratedLowRelationSmithRowCoefficients
  apply Finsupp.mapDomain_notin_range
  rintro ⟨j, hj⟩
  exact hkl (Sigma.mk.inj_iff.mp hj |>.1)

/-- The finite coefficient family of all rows removed through weight four. -/
def fourLowRelationSmithRowCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    LowRelationSmithRowIndex X L evaluation →₀ ℤ :=
  ∑ k : Fin 4, iteratedLowRelationSmithRowCoefficients X L evaluation k r

/-- A relation of minimum weight `t` has no tagged Smith-row coefficient below `t`. -/
theorem fourLowRelationSmithRowCoefficients_apply_eq_zero_of_lt
    (evaluation : LieHom ℤ F L) (r : LinearMap.ker evaluation.toLinearMap)
    (i : LowRelationSmithRowIndex X L evaluation) {t : ℕ}
    (hr : (r : F) ∈ FreeLieDimension.lieHigh X t)
    (hi : lowRelationSmithRowWeight X L evaluation i < t) :
    fourLowRelationSmithRowCoefficients X L evaluation r i = 0 := by
  unfold fourLowRelationSmithRowCoefficients
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k = i.1
  · subst k
    rw [iteratedLowRelationSmithRowCoefficients_eq_zero_of_lt
      X L evaluation r i.1 hr]
    · rfl
    · exact hi
  · exact iteratedLowRelationSmithRowCoefficients_apply_ne
      X L evaluation k i.1 hki r i.2

/-- One embedded stage evaluates to the corresponding row part. -/
theorem iteratedLowRelationSmithRowCoefficients_sum
    (evaluation : LieHom ℤ F L) (k : Fin 4)
    (r : LinearMap.ker evaluation.toLinearMap) :
  (iteratedLowRelationSmithRowCoefficients X L evaluation k r).sum
        (fun i c ↦ c • lowRelationSmithRow X L evaluation i) =
      iteratedRelationSmithRowPart X L evaluation k.1 r := by
  unfold iteratedLowRelationSmithRowCoefficients
  rw [Finsupp.sum_mapDomain_index]
  exact relationSmithRowCoefficients_sum X L evaluation (k.1 + 1) _
  · intro i
    simp
  · intro i a b
    simp [add_smul]

/-- The tagged four-stage coefficient family evaluates to the sum of the four row parts. -/
theorem fourLowRelationSmithRowCoefficients_sum
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (fourLowRelationSmithRowCoefficients X L evaluation r).sum
        (fun i c ↦ c • lowRelationSmithRow X L evaluation i) =
      ∑ k : Fin 4, iteratedRelationSmithRowPart X L evaluation k.1 r := by
  unfold fourLowRelationSmithRowCoefficients
  let φ : (LowRelationSmithRowIndex X L evaluation →₀ ℤ) →ₗ[ℤ] F :=
    Finsupp.linearCombination ℤ (lowRelationSmithRow X L evaluation)
  change φ (∑ k : Fin 4,
      iteratedLowRelationSmithRowCoefficients X L evaluation k r) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact iteratedLowRelationSmithRowCoefficients_sum X L evaluation k r

/-- **Exact coefficient-level Smith expansion through weight four.** -/
theorem relation_eq_fourLowRelationSmithRows_add_weightFiveRemainder
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (r : F) =
      (fourLowRelationSmithRowCoefficients X L evaluation r).sum
          (fun i c ↦ c • lowRelationSmithRow X L evaluation i) +
        (iteratedRelationSmithRemainder X L evaluation 4 r : F) := by
  rw [fourLowRelationSmithRowCoefficients_sum]
  simpa only [Fin.sum_univ_four] using
    relation_eq_four_rowParts_add_weightFiveRemainder X L evaluation r

/-- The residual term in the coefficient expansion is an actual defining relation. -/
theorem fourRowWeightFiveRemainder_mem_ker
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    evaluation (iteratedRelationSmithRemainder X L evaluation 4 r : F) = 0 :=
  (iteratedRelationSmithRemainder X L evaluation 4 r).property.1

/-- The residual term has certified minimum bracket weight five. -/
theorem fourRowWeightFiveRemainder_mem_lieHigh
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (iteratedRelationSmithRemainder X L evaluation 4 r : F) ∈
      FreeLieDimension.lieHigh X 5 :=
  iteratedRelationSmithRemainder_four_mem_lieHigh_five X L evaluation r

end

end DegreeFive

end LieRings
