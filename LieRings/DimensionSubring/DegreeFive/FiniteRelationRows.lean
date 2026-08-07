import LieRings.DimensionSubring.DegreeFive.FiniteHomogeneous

/-!
# Finite Smith rows for a free Lie presentation

For a finite generator type, each homogeneous component of the integral free Lie ring is finite
free.  This file applies Smith normal form to the leading homogeneous terms of the relation
ideal.  The resulting rows have genuine diagonal heads; no saturation or divisibility inference
is hidden in their definition.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- Homogeneous projection with its codomain restricted to the exact component. -/
def freeLieExactProjection (n : ℕ) : F →ₗ[ℤ] freeLieExact X n :=
  (freeLieLengthComponent X n).codRestrict (freeLieExact X n)
    (freeLieLengthComponent_mem_exact X n)

@[simp]
theorem coe_freeLieExactProjection (n : ℕ) (x : F) :
    (freeLieExactProjection X n x : F) = freeLieLengthComponent X n x :=
  rfl

/-- Relations whose least possible bracket weight is `n`. -/
def filteredPresentationRelations
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) : Submodule ℤ F :=
  LinearMap.ker evaluation.toLinearMap ⊓ FreeLieDimension.lieHigh X n

/-- The submodule of weight-`n` leading terms of filtered defining relations. -/
def homogeneousRelationLeading
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) :
    Submodule ℤ (freeLieExact X n) :=
  (filteredPresentationRelations X L evaluation n).map
    (freeLieExactProjection X n)

/-- Smith normal form for the leading relation submodule in weight `n`. -/
def homogeneousRelationSmithData
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) :
    Σ k : ℕ, Module.Basis.SmithNormalForm
      (homogeneousRelationLeading X L evaluation n)
      (FreeLieExactBasisIndex X n) k :=
  Submodule.smithNormalForm (freeLieExactBasis X n)
    (homogeneousRelationLeading X L evaluation n)

/-- Number of chosen Smith rows in one homogeneous weight. -/
abbrev RelationSmithRowIndex
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) :=
  Fin (homogeneousRelationSmithData X L evaluation n).1

/-- The Smith-normal-form package in one weight. -/
def homogeneousRelationSmithForm
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) :
    Module.Basis.SmithNormalForm
      (homogeneousRelationLeading X L evaluation n)
      (FreeLieExactBasisIndex X n)
      (homogeneousRelationSmithData X L evaluation n).1 :=
  (homogeneousRelationSmithData X L evaluation n).2

/-- A relation lift of each diagonal Smith generator.  It lies in the actual kernel and in the
weight filtration, rather than merely representing a class modulo higher weight. -/
def relationSmithRow
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (i : RelationSmithRowIndex X L evaluation n) :
    filteredPresentationRelations X L evaluation n := by
  let d : homogeneousRelationLeading X L evaluation n :=
    (homogeneousRelationSmithForm X L evaluation n).bN i
  have hd : (d : freeLieExact X n) ∈
      homogeneousRelationLeading X L evaluation n := d.property
  exact ⟨Classical.choose hd, (Classical.choose_spec hd).1⟩

/-- The selected row projects to the selected basis vector of the leading relation submodule. -/
theorem freeLieExactProjection_relationSmithRow
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (i : RelationSmithRowIndex X L evaluation n) :
    freeLieExactProjection X n (relationSmithRow X L evaluation n i : F) =
      ((homogeneousRelationSmithForm X L evaluation n).bN i :
        homogeneousRelationLeading X L evaluation n) := by
  unfold relationSmithRow
  dsimp only
  exact (Classical.choose_spec
    ((homogeneousRelationSmithForm X L evaluation n).bN i).property).2

/-- **Single-head equation.**  The leading component of a chosen relation row is an integral
multiple of one distinct ambient homogeneous basis vector. -/
theorem relationSmithRow_head
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (i : RelationSmithRowIndex X L evaluation n) :
    freeLieExactProjection X n (relationSmithRow X L evaluation n i : F) =
      (homogeneousRelationSmithForm X L evaluation n).a i •
        (homogeneousRelationSmithForm X L evaluation n).bM
          ((homogeneousRelationSmithForm X L evaluation n).f i) := by
  rw [freeLieExactProjection_relationSmithRow]
  exact (homogeneousRelationSmithForm X L evaluation n).snf i

/-- Every chosen row is an actual defining relation. -/
theorem relationSmithRow_mem_ker
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (i : RelationSmithRowIndex X L evaluation n) :
    evaluation (relationSmithRow X L evaluation n i : F) = 0 := by
  exact (relationSmithRow X L evaluation n i).property.1

/-- Every chosen row has minimum bracket weight at least its declared weight. -/
theorem relationSmithRow_mem_lieHigh
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (i : RelationSmithRowIndex X L evaluation n) :
    (relationSmithRow X L evaluation n i : F) ∈
      FreeLieDimension.lieHigh X n :=
  (relationSmithRow X L evaluation n i).property.2

/-- Linear recombination of the chosen rows. -/
def relationSmithRowLift
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) :
    homogeneousRelationLeading X L evaluation n →ₗ[ℤ] F :=
  ((homogeneousRelationSmithForm X L evaluation n).bN.constr ℤ)
    (fun i ↦ (relationSmithRow X L evaluation n i : F))

/-- Recombining rows and then taking the leading component is the inclusion of the leading
relation submodule. -/
theorem freeLieExactProjection_comp_relationSmithRowLift
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ) :
    (freeLieExactProjection X n).comp
        (relationSmithRowLift X L evaluation n) =
      (homogeneousRelationLeading X L evaluation n).subtype := by
  apply LinearMap.ext_on_range
    (homogeneousRelationSmithForm X L evaluation n).bN.span_eq
  intro i
  rw [LinearMap.comp_apply, relationSmithRowLift,
    Module.Basis.constr_basis, freeLieExactProjection_relationSmithRow]
  rfl

/-- The leading term of a filtered relation, bundled in the leading-relation submodule. -/
def filteredRelationLeading
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    homogeneousRelationLeading X L evaluation n :=
  ⟨freeLieExactProjection X n (r : F), ⟨r, r.property, rfl⟩⟩

/-- Subtract the unique row combination having the same leading homogeneous component. -/
def relationSmithRemainder
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) : F :=
  (r : F) - relationSmithRowLift X L evaluation n
    (filteredRelationLeading X L evaluation n r)

/-- The Smith remainder is still a defining relation. -/
theorem relationSmithRemainder_mem_ker
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    evaluation (relationSmithRemainder X L evaluation n r) = 0 := by
  unfold relationSmithRemainder
  rw [map_sub, show evaluation (r : F) = 0 from r.property.1]
  suffices evaluation (relationSmithRowLift X L evaluation n
      (filteredRelationLeading X L evaluation n r)) = 0 by rw [this, sub_zero]
  let N : Submodule ℤ (homogeneousRelationLeading X L evaluation n) :=
    LinearMap.ker (evaluation.toLinearMap.comp
      (relationSmithRowLift X L evaluation n))
  have hbasis : ∀ i, (homogeneousRelationSmithForm X L evaluation n).bN i ∈ N := by
    intro i
    change evaluation (relationSmithRowLift X L evaluation n
      ((homogeneousRelationSmithForm X L evaluation n).bN i)) = 0
    rw [relationSmithRowLift, Module.Basis.constr_basis]
    exact relationSmithRow_mem_ker X L evaluation n i
  have htop : N = ⊤ := by
    apply top_unique
    rw [← (homogeneousRelationSmithForm X L evaluation n).bN.span_eq,
      Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hbasis i
  change filteredRelationLeading X L evaluation n r ∈ N
  rw [htop]
  trivial

/-- The Smith remainder has zero weight-`n` component. -/
theorem freeLieLengthComponent_relationSmithRemainder_eq_zero
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    freeLieLengthComponent X n
      (relationSmithRemainder X L evaluation n r) = 0 := by
  have hzero : freeLieExactProjection X n
      (relationSmithRemainder X L evaluation n r) = 0 := by
    rw [relationSmithRemainder, map_sub]
    have hcomp := LinearMap.congr_fun
      (freeLieExactProjection_comp_relationSmithRowLift X L evaluation n)
        (filteredRelationLeading X L evaluation n r)
    change freeLieExactProjection X n
        (relationSmithRowLift X L evaluation n
          (filteredRelationLeading X L evaluation n r)) =
      (filteredRelationLeading X L evaluation n r : freeLieExact X n) at hcomp
    rw [hcomp]
    change freeLieExactProjection X n (r : F) -
      freeLieExactProjection X n (r : F) = 0
    exact sub_self _
  exact congrArg Subtype.val hzero

/-- **Integral row elimination.**  After subtracting its Smith row combination, a relation of
minimum weight `n` has minimum weight at least `n+1`. -/
theorem relationSmithRemainder_mem_lieHigh_succ
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    relationSmithRemainder X L evaluation n r ∈
      FreeLieDimension.lieHigh X (n + 1) := by
  apply mem_lieHigh_succ_of_component_eq_zero X
  · unfold relationSmithRemainder
    apply (FreeLieDimension.lieHigh X n).sub_mem r.property.2
    let N : Submodule ℤ (homogeneousRelationLeading X L evaluation n) :=
      (FreeLieDimension.lieHigh X n).comap
        (relationSmithRowLift X L evaluation n)
    have hbasis : ∀ i, (homogeneousRelationSmithForm X L evaluation n).bN i ∈ N := by
      intro i
      change relationSmithRowLift X L evaluation n
          ((homogeneousRelationSmithForm X L evaluation n).bN i) ∈
        FreeLieDimension.lieHigh X n
      rw [relationSmithRowLift, Module.Basis.constr_basis]
      exact relationSmithRow_mem_lieHigh X L evaluation n i
    have htop : N = ⊤ := by
      apply top_unique
      rw [← (homogeneousRelationSmithForm X L evaluation n).bN.span_eq,
        Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbasis i
    change filteredRelationLeading X L evaluation n r ∈ N
    rw [htop]
    trivial
  · exact freeLieLengthComponent_relationSmithRemainder_eq_zero
      X L evaluation n r

/-- The remainder bundled for the next Smith-elimination step. -/
def relationSmithRemainderFilteredSucc
    (evaluation : F →ₗ⁅ℤ⁆ L) (n : ℕ)
    (r : filteredPresentationRelations X L evaluation n) :
    filteredPresentationRelations X L evaluation (n + 1) :=
  ⟨relationSmithRemainder X L evaluation n r,
    relationSmithRemainder_mem_ker X L evaluation n r,
    relationSmithRemainder_mem_lieHigh_succ X L evaluation n r⟩

/-- Every integral relation starts in bracket weight one. -/
def presentationRelationAsFilteredOne
    (evaluation : F →ₗ⁅ℤ⁆ L) (r : LinearMap.ker evaluation.toLinearMap) :
    filteredPresentationRelations X L evaluation 1 :=
  ⟨(r : F), r.property, by
    rw [FreeLieDimension.lieHigh_one]
    trivial⟩

/-- Successively remove Smith heads.  After `k` eliminations the output has minimum weight
`k+1`. -/
def iteratedRelationSmithRemainder
    (evaluation : F →ₗ⁅ℤ⁆ L) :
    (k : ℕ) → LinearMap.ker evaluation.toLinearMap →
      filteredPresentationRelations X L evaluation (k + 1)
  | 0, r => presentationRelationAsFilteredOne X L evaluation r
  | k + 1, r => relationSmithRemainderFilteredSucc X L evaluation (k + 1)
      (iteratedRelationSmithRemainder evaluation k r)

/-- Row contribution removed at stage `k`, whose declared least weight is `k+1`. -/
def iteratedRelationSmithRowPart
    (evaluation : F →ₗ⁅ℤ⁆ L) (k : ℕ)
    (r : LinearMap.ker evaluation.toLinearMap) : F :=
  relationSmithRowLift X L evaluation (k + 1)
    (filteredRelationLeading X L evaluation (k + 1)
      (iteratedRelationSmithRemainder X L evaluation k r))

/-- One stage is exactly its row contribution plus its next remainder. -/
theorem iteratedRelationSmithRemainder_eq_rowPart_add_succ
    (evaluation : F →ₗ⁅ℤ⁆ L) (k : ℕ)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (iteratedRelationSmithRemainder X L evaluation k r : F) =
      iteratedRelationSmithRowPart X L evaluation k r +
        (iteratedRelationSmithRemainder X L evaluation (k + 1) r : F) := by
  change (iteratedRelationSmithRemainder X L evaluation k r : F) =
    relationSmithRowLift X L evaluation (k + 1)
        (filteredRelationLeading X L evaluation (k + 1)
          (iteratedRelationSmithRemainder X L evaluation k r)) +
      relationSmithRemainder X L evaluation (k + 1)
        (iteratedRelationSmithRemainder X L evaluation k r)
  unfold relationSmithRemainder
  abel

/-- Telescoping form of successive integral Smith-row elimination. -/
theorem relation_eq_sum_rowParts_add_iteratedRemainder
    (evaluation : F →ₗ⁅ℤ⁆ L) (steps : ℕ)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (r : F) =
      ∑ k ∈ Finset.range steps, iteratedRelationSmithRowPart X L evaluation k r +
        (iteratedRelationSmithRemainder X L evaluation steps r : F) := by
  induction steps with
  | zero =>
      simp [iteratedRelationSmithRemainder, presentationRelationAsFilteredOne]
  | succ steps ih =>
      rw [Finset.sum_range_succ, add_assoc]
      rw [← iteratedRelationSmithRemainder_eq_rowPart_add_succ
        X L evaluation steps r]
      exact ih

/-- The concrete four-row expansion used below weight five.  Its residual is an actual relation
of minimum weight five. -/
theorem relation_eq_four_rowParts_add_weightFiveRemainder
    (evaluation : F →ₗ⁅ℤ⁆ L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (r : F) = iteratedRelationSmithRowPart X L evaluation 0 r +
      iteratedRelationSmithRowPart X L evaluation 1 r +
      iteratedRelationSmithRowPart X L evaluation 2 r +
      iteratedRelationSmithRowPart X L evaluation 3 r +
      (iteratedRelationSmithRemainder X L evaluation 4 r : F) := by
  have h := relation_eq_sum_rowParts_add_iteratedRemainder
    X L evaluation 4 r
  simpa [Finset.sum_range_succ] using h

theorem iteratedRelationSmithRemainder_four_mem_lieHigh_five
    (evaluation : F →ₗ⁅ℤ⁆ L)
    (r : LinearMap.ker evaluation.toLinearMap) :
    (iteratedRelationSmithRemainder X L evaluation 4 r : F) ∈
      FreeLieDimension.lieHigh X 5 :=
  (iteratedRelationSmithRemainder X L evaluation 4 r).property.2

end


end DegreeFive

end LieRings
