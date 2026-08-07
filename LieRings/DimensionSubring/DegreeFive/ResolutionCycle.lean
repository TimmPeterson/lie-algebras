import LieRings.DimensionSubring.DegreeFive.ExteriorSplit
import LieRings.DimensionSubring.DegreeFive.ExteriorAlternation
import LieRings.DimensionSubring.DegreeFive.Certificate

/-!
# Calculus of a lifted class-two presentation cycle

This file formalizes the invariant part of the degree-five argument.  A tensor over the
kernel of `P ⊕ ⋀²P → L/γ₃` has an alternating boundary.  Splitting that boundary into
weights `(1,1)`, `(1,2)`, and `(2,2)` shows, integrally, that its mixed and high bracket
values vanish in nilpotency class three.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

local notation "P" => GeneratorModule L
local notation "W" => ⋀[ℤ]^2 P
local notation "M" => FreeClassTwo P
local notation "Rel₂" => ClassTwoResolutionRelations L

/-! ## Bracket evaluation on the three summands -/

/-- Bracket evaluation on the exterior square of the canonical generator module. -/
def generatorExteriorBracketAlternating :
    P [⋀^Fin 2]→ₗ[ℤ] L where
  toFun v := ⁅canonicalGeneratorEvaluation L (v 0),
    canonicalGeneratorEvaluation L (v 1)⁆
  map_update_add' v i x y := by fin_cases i <;> simp
  map_update_smul' v i n x := by fin_cases i <;> simp <;> rfl
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change ⁅canonicalGeneratorEvaluation L (v 0),
        canonicalGeneratorEvaluation L (v 1)⁆ = 0
      change v 0 = v 1 at hv
      rw [hv, lie_self]
    · change ⁅canonicalGeneratorEvaluation L (v 0),
        canonicalGeneratorEvaluation L (v 1)⁆ = 0
      change v 1 = v 0 at hv
      rw [hv, lie_self]
    · exact (hij rfl).elim

/-- Evaluate a weight-two exterior generator as a Lie bracket in `L`. -/
def generatorExteriorBracket : W →ₗ[ℤ] L :=
  exteriorPower.alternatingMapLinearEquiv
    (generatorExteriorBracketAlternating L)

@[simp]
theorem generatorExteriorBracket_wedge (x y : P) :
    generatorExteriorBracket L (wedgeTwo P x y) =
      ⁅canonicalGeneratorEvaluation L x, canonicalGeneratorEvaluation L y⁆ := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (generatorExteriorBracketAlternating L) ![x, y]

/-- Every degree-two evaluation belongs to `γ₂(L)`. -/
theorem generatorExteriorBracket_mem_gammaTwo (w : W) :
    generatorExteriorBracket L w ∈ lowerCentralSeries ℤ L 1 := by
  let N : Submodule ℤ W :=
    (lowerCentralSeries ℤ L 1).toSubmodule.comap
      (generatorExteriorBracket L)
  have hwedge (v : Fin 2 → P) : exteriorPower.ιMulti ℤ 2 v ∈ N := by
    change generatorExteriorBracket L (exteriorPower.ιMulti ℤ 2 v) ∈
      lowerCentralSeries ℤ L 1
    rw [show exteriorPower.ιMulti ℤ 2 v = wedgeTwo P (v 0) (v 1) by rfl,
      generatorExteriorBracket_wedge]
    change _ ∈ LieModule.lowerCentralSeries ℤ L L 1
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _)
      (LieSubmodule.mem_top _)
  have hspan : Submodule.span ℤ
      (Set.range (exteriorPower.ιMulti ℤ 2 : (Fin 2 → P) → W)) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hwedge v
  apply hspan
  have hwtop : w ∈ (⊤ : Submodule ℤ W) := Submodule.mem_top
  have htop : Submodule.span ℤ
      (Set.range (exteriorPower.ιMulti ℤ 2 : (Fin 2 → P) → W)) = ⊤ :=
    exteriorPower.ιMulti_span ℤ 2 P
  exact htop.symm ▸ hwtop

/-- Linear evaluation of `P ⊕ ⋀²P` by generators and brackets. -/
def freeClassTwoEvaluationToL : M →ₗ[ℤ] L :=
  (canonicalGeneratorEvaluation L).comp (freeClassTwoFst P) +
    (generatorExteriorBracket L).comp (freeClassTwoSnd P)

@[simp]
theorem freeClassTwoEvaluationToL_apply (x : M) :
    freeClassTwoEvaluationToL L x =
      canonicalGeneratorEvaluation L x.1 + generatorExteriorBracket L x.2 :=
  rfl

/-- Evaluation in `L/γ₃` is the quotient of the explicit evaluation in `L`. -/
theorem canonicalClassTwoEvaluation_eq_mk_freeClassTwoEvaluationToL (x : M) :
    canonicalClassTwoEvaluation L x =
      (LieSubmodule.Quotient.mk (freeClassTwoEvaluationToL L x) :
        ModGammaThree L) := by
  rw [canonicalClassTwoEvaluation, freeClassTwoEvaluation_apply,
    freeClassTwoEvaluationToL_apply]
  change LieSubmodule.Quotient.mk (canonicalGeneratorEvaluation L x.1) +
      degreeTwoEvaluation P L (canonicalGeneratorEvaluation L) x.2 =
    LieSubmodule.Quotient.mk
      (canonicalGeneratorEvaluation L x.1 + generatorExteriorBracket L x.2)
  rw [show (LieSubmodule.Quotient.mk
        (canonicalGeneratorEvaluation L x.1 + generatorExteriorBracket L x.2) :
          ModGammaThree L) =
      LieSubmodule.Quotient.mk (canonicalGeneratorEvaluation L x.1) +
        LieSubmodule.Quotient.mk (generatorExteriorBracket L x.2) by
    exact map_add (lowerCentralSeries ℤ L 2).toSubmodule.mkQ _ _]
  congr 1
  let f : W →ₗ[ℤ] ModGammaThree L :=
    (lowerCentralSeries ℤ L 2).toSubmodule.mkQ.comp
      (generatorExteriorBracket L)
  have hf : degreeTwoEvaluation P L (canonicalGeneratorEvaluation L) = f := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change degreeTwoEvaluation P L (canonicalGeneratorEvaluation L)
        (wedgeTwo P (v 0) (v 1)) =
      LieSubmodule.Quotient.mk
        (generatorExteriorBracket L (wedgeTwo P (v 0) (v 1)))
    rw [degreeTwoEvaluation_wedge, generatorExteriorBracket_wedge]
  exact LinearMap.congr_fun hf x.2

/-- The degree-one part of a class-two presentation relation evaluates into `γ₂(L)`. -/
theorem relationFst_evaluation_mem_gammaTwo (r : Rel₂) :
    canonicalGeneratorEvaluation L (r : M).1 ∈ lowerCentralSeries ℤ L 1 := by
  have hrzero : canonicalClassTwoEvaluation L (r : M) = 0 := r.property
  rw [canonicalClassTwoEvaluation_eq_mk_freeClassTwoEvaluationToL] at hrzero
  have hsumGammaThree : freeClassTwoEvaluationToL L (r : M) ∈
      lowerCentralSeries ℤ L 2 :=
    (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ L 2)).mp hrzero
  have hsumGammaTwo : freeClassTwoEvaluationToL L (r : M) ∈
      lowerCentralSeries ℤ L 1 :=
    LieModule.antitone_lowerCentralSeries ℤ L L (by omega) hsumGammaThree
  have hwGammaTwo := generatorExteriorBracket_mem_gammaTwo L (r : M).2
  have hsub := (lowerCentralSeries ℤ L 1).sub_mem hsumGammaTwo hwGammaTwo
  convert hsub using 1
  rw [freeClassTwoEvaluationToL_apply]
  abel

/-- A class-two presentation relation evaluates into `γ₃(L)` before passing to the
quotient. -/
theorem relation_evaluation_mem_gammaThree (r : Rel₂) :
    freeClassTwoEvaluationToL L (r : M) ∈ lowerCentralSeries ℤ L 2 := by
  have hrzero : canonicalClassTwoEvaluation L (r : M) = 0 := r.property
  rw [canonicalClassTwoEvaluation_eq_mk_freeClassTwoEvaluationToL] at hrzero
  exact (LieSubmodule.Quotient.mk_eq_zero'
    (N := lowerCentralSeries ℤ L 2)).mp hrzero

/-- Low bracket evaluation. -/
abbrev freeClassTwoLowBracket : ⋀[ℤ]^2 P →ₗ[ℤ] L :=
  generatorExteriorBracket L

/-- Mixed bracket evaluation `P ⊗ ⋀²P → L`. -/
def freeClassTwoMixedBracket : (P ⊗[ℤ] W) →ₗ[ℤ] L :=
  TensorProduct.lift
    { toFun := fun p ↦
        { toFun := fun w ↦
            ⁅canonicalGeneratorEvaluation L p, generatorExteriorBracket L w⁆
          map_add' := by intro x y; simp
          map_smul' := by intro n x; simp }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro w
        simp
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro w
        simp }

@[simp]
theorem freeClassTwoMixedBracket_tmul (x : P) (y : W) :
    freeClassTwoMixedBracket L (x ⊗ₜ[ℤ] y) =
      ⁅canonicalGeneratorEvaluation L x, generatorExteriorBracket L y⁆ := by
  exact TensorProduct.lift.tmul x y

/-- High bracket evaluation on `⋀²(⋀²P)`. -/
def freeClassTwoHighBracketAlternating :
    W [⋀^Fin 2]→ₗ[ℤ] L where
  toFun v := ⁅generatorExteriorBracket L (v 0), generatorExteriorBracket L (v 1)⁆
  map_update_add' v i x y := by fin_cases i <;> simp
  map_update_smul' v i n x := by fin_cases i <;> simp <;> rfl
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change ⁅generatorExteriorBracket L (v 0),
        generatorExteriorBracket L (v 1)⁆ = 0
      change v 0 = v 1 at hv
      rw [hv, lie_self]
    · change ⁅generatorExteriorBracket L (v 0),
        generatorExteriorBracket L (v 1)⁆ = 0
      change v 1 = v 0 at hv
      rw [hv, lie_self]
    · exact (hij rfl).elim

def freeClassTwoHighBracket : ⋀[ℤ]^2 W →ₗ[ℤ] L :=
  exteriorPower.alternatingMapLinearEquiv
    (freeClassTwoHighBracketAlternating L)

@[simp]
theorem freeClassTwoHighBracket_wedge (x y : W) :
    freeClassTwoHighBracket L (wedgeTwo W x y) =
      ⁅generatorExteriorBracket L x, generatorExteriorBracket L y⁆ := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (freeClassTwoHighBracketAlternating L) ![x, y]

/-- In class three, the high bracket map is zero. -/
theorem freeClassTwoHighBracket_eq_zero
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    freeClassTwoHighBracket L = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change freeClassTwoHighBracket L (wedgeTwo W (v 0) (v 1)) = 0
  rw [freeClassTwoHighBracket_wedge]
  have hmem : ⁅generatorExteriorBracket L (v 0),
      generatorExteriorBracket L (v 1)⁆ ∈ lowerCentralSeries ℤ L 3 := by
    apply bracket_dimensionSubring_le_lowerCentralSeries ℤ L 1 1
    exact LieSubmodule.lie_mem_lie
      (lowerCentralSeries_le_dimensionSubring ℤ L 1
        (generatorExteriorBracket_mem_gammaTwo L (v 0)))
      (lowerCentralSeries_le_dimensionSubring ℤ L 1
        (generatorExteriorBracket_mem_gammaTwo L (v 1)))
  rw [hclass] at hmem
  simpa using hmem

/-! ## The boundary of a lifted relation cycle -/

/-- Inclusion of the class-two presentation relations into `P ⊕ ⋀²P`. -/
def classTwoResolutionRelationInclusion : Rel₂ →ₗ[ℤ] M :=
  (LinearMap.ker (canonicalClassTwoEvaluation L).toLinearMap).subtype

/-- Boundary tensor `(d₃ ⊗ 1)χ`. -/
def classTwoResolutionBoundary : (Rel₂ ⊗[ℤ] M) →ₗ[ℤ] (M ⊗[ℤ] M) :=
  TensorProduct.map (classTwoResolutionRelationInclusion L) LinearMap.id

/-- Its `(1,2)` tensor component. -/
def classTwoResolutionBoundaryMixed :
    (Rel₂ ⊗[ℤ] M) →ₗ[ℤ] (P ⊗[ℤ] W) :=
  TensorProduct.map
    ((freeClassTwoFst P).comp (classTwoResolutionRelationInclusion L))
    (freeClassTwoSnd P)

/-- Its `(2,1)` tensor component. -/
def classTwoResolutionBoundaryReverseMixed :
    (Rel₂ ⊗[ℤ] M) →ₗ[ℤ] (W ⊗[ℤ] P) :=
  TensorProduct.map
    ((freeClassTwoSnd P).comp (classTwoResolutionRelationInclusion L))
    (freeClassTwoFst P)

/-- Its `(1,1)` tensor component. -/
def classTwoResolutionBoundaryLow :
    (Rel₂ ⊗[ℤ] M) →ₗ[ℤ] (P ⊗[ℤ] P) :=
  TensorProduct.map
    ((freeClassTwoFst P).comp (classTwoResolutionRelationInclusion L))
    (freeClassTwoFst P)

@[simp]
theorem classTwoResolutionBoundary_tmul (r : Rel₂) (x : M) :
    classTwoResolutionBoundary L (r ⊗ₜ[ℤ] x) = (r : M) ⊗ₜ[ℤ] x := by
  change (TensorProduct.map (classTwoResolutionRelationInclusion L) LinearMap.id)
      (r ⊗ₜ[ℤ] x) = _
  calc
    _ = classTwoResolutionRelationInclusion L r ⊗ₜ[ℤ] LinearMap.id x :=
      TensorProduct.map_tmul
        (classTwoResolutionRelationInclusion L) LinearMap.id r x
    _ = _ := rfl

@[simp]
theorem classTwoResolutionBoundaryMixed_tmul (r : Rel₂) (x : M) :
    classTwoResolutionBoundaryMixed L (r ⊗ₜ[ℤ] x) =
      (r : M).1 ⊗ₜ[ℤ] x.2 := by
  change (TensorProduct.map
      ((freeClassTwoFst P).comp (classTwoResolutionRelationInclusion L))
      (freeClassTwoSnd P)) (r ⊗ₜ[ℤ] x) = _
  calc
    _ = ((freeClassTwoFst P).comp (classTwoResolutionRelationInclusion L)) r
          ⊗ₜ[ℤ] freeClassTwoSnd P x :=
      TensorProduct.map_tmul
        ((freeClassTwoFst P).comp (classTwoResolutionRelationInclusion L))
        (freeClassTwoSnd P) r x
    _ = _ := rfl

@[simp]
theorem classTwoResolutionBoundaryReverseMixed_tmul (r : Rel₂) (x : M) :
    classTwoResolutionBoundaryReverseMixed L (r ⊗ₜ[ℤ] x) =
      (r : M).2 ⊗ₜ[ℤ] x.1 := by
  exact TensorProduct.map_tmul
    ((freeClassTwoSnd P).comp (classTwoResolutionRelationInclusion L))
    (freeClassTwoFst P) r x

@[simp]
theorem classTwoResolutionBoundaryLow_tmul (r : Rel₂) (x : M) :
    classTwoResolutionBoundaryLow L (r ⊗ₜ[ℤ] x) =
      (r : M).1 ⊗ₜ[ℤ] x.1 := by
  exact TensorProduct.map_tmul
    ((freeClassTwoFst P).comp (classTwoResolutionRelationInclusion L))
    (freeClassTwoFst P) r x

/-- Projecting integral alternation to `P ⊗ ⋀²P` is exactly the mixed exterior
component. -/
theorem tensorMixedProjection_comp_exteriorToTensor :
    (TensorProduct.map (freeClassTwoFst P) (freeClassTwoSnd P)).comp
        (exteriorToTensor M) =
      freeClassTwoExteriorMixed P := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change TensorProduct.map (freeClassTwoFst P) (freeClassTwoSnd P)
      (exteriorToTensor M (wedgeTwo M (v 0) (v 1))) =
    freeClassTwoExteriorMixed P (wedgeTwo M (v 0) (v 1))
  rw [exteriorToTensor_wedge, map_sub, TensorProduct.map_tmul,
    TensorProduct.map_tmul, freeClassTwoExteriorMixed_wedge]
  rfl

/-- The same projection applied to a relation boundary. -/
theorem tensorMixedProjection_comp_classTwoResolutionBoundary :
    (TensorProduct.map (freeClassTwoFst P) (freeClassTwoSnd P)).comp
        (classTwoResolutionBoundary L) =
      classTwoResolutionBoundaryMixed L := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro x
  change TensorProduct.map (freeClassTwoFst P) (freeClassTwoSnd P)
      (classTwoResolutionBoundary L (r ⊗ₜ[ℤ] x)) =
    classTwoResolutionBoundaryMixed L (r ⊗ₜ[ℤ] x)
  rw [classTwoResolutionBoundary_tmul, classTwoResolutionBoundaryMixed_tmul]
  exact TensorProduct.map_tmul (freeClassTwoFst P) (freeClassTwoSnd P)
    (r : M) x

/-- The reverse mixed projection of the total boundary. -/
theorem tensorReverseMixedProjection_comp_classTwoResolutionBoundary :
    (TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)).comp
        (classTwoResolutionBoundary L) =
      classTwoResolutionBoundaryReverseMixed L := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro x
  change TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)
      (classTwoResolutionBoundary L (r ⊗ₜ[ℤ] x)) =
    classTwoResolutionBoundaryReverseMixed L (r ⊗ₜ[ℤ] x)
  rw [classTwoResolutionBoundary_tmul,
    classTwoResolutionBoundaryReverseMixed_tmul]
  exact TensorProduct.map_tmul (freeClassTwoSnd P) (freeClassTwoFst P)
    (r : M) x

/-- The low projection of the total boundary. -/
theorem tensorLowProjection_comp_classTwoResolutionBoundary :
    (TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)).comp
        (classTwoResolutionBoundary L) =
      classTwoResolutionBoundaryLow L := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro x
  change TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)
      (classTwoResolutionBoundary L (r ⊗ₜ[ℤ] x)) =
    classTwoResolutionBoundaryLow L (r ⊗ₜ[ℤ] x)
  rw [classTwoResolutionBoundary_tmul, classTwoResolutionBoundaryLow_tmul]
  exact TensorProduct.map_tmul (freeClassTwoFst P) (freeClassTwoFst P)
    (r : M) x

/-- Bracket evaluation on an ordered low tensor. -/
def freeClassTwoLowTensorBracket : (P ⊗[ℤ] P) →ₗ[ℤ] L :=
  TensorProduct.lift
    { toFun := fun x ↦
        { toFun := fun y ↦
            ⁅canonicalGeneratorEvaluation L x, canonicalGeneratorEvaluation L y⁆
          map_add' := by intro y z; simp
          map_smul' := by intro n y; simp }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        simp
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro y
        simp }

@[simp]
theorem freeClassTwoLowTensorBracket_tmul (x y : P) :
    freeClassTwoLowTensorBracket L (x ⊗ₜ[ℤ] y) =
      ⁅canonicalGeneratorEvaluation L x, canonicalGeneratorEvaluation L y⁆ := by
  exact TensorProduct.lift.tmul x y

/-- Bracket evaluation on a reverse mixed tensor. -/
def freeClassTwoReverseMixedBracket : (W ⊗[ℤ] P) →ₗ[ℤ] L :=
  TensorProduct.lift
    { toFun := fun w ↦
        { toFun := fun p ↦
            ⁅generatorExteriorBracket L w, canonicalGeneratorEvaluation L p⁆
          map_add' := by intro x y; simp
          map_smul' := by intro n x; simp }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro p
        simp
      map_smul' := by
        intro n x
        apply LinearMap.ext
        intro p
        simp }

@[simp]
theorem freeClassTwoReverseMixedBracket_tmul (w : W) (p : P) :
    freeClassTwoReverseMixedBracket L (w ⊗ₜ[ℤ] p) =
      ⁅generatorExteriorBracket L w, canonicalGeneratorEvaluation L p⁆ := by
  exact TensorProduct.lift.tmul w p

/-- Low-low alternation evaluates to twice the exterior bracket. -/
theorem lowTensorBracket_comp_lowProjection_comp_exteriorToTensor :
    (freeClassTwoLowTensorBracket L).comp
        ((TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)).comp
          (exteriorToTensor M)) =
      (2 : ℤ) • (freeClassTwoLowBracket L).comp
        (freeClassTwoExteriorLow P) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change freeClassTwoLowTensorBracket L
      (TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)
        (exteriorToTensor M (wedgeTwo M (v 0) (v 1)))) =
    (2 : ℤ) • freeClassTwoLowBracket L
      (freeClassTwoExteriorLow P (wedgeTwo M (v 0) (v 1)))
  rw [exteriorToTensor_wedge, map_sub, TensorProduct.map_tmul,
    TensorProduct.map_tmul, map_sub, freeClassTwoLowTensorBracket_tmul,
    freeClassTwoLowTensorBracket_tmul, freeClassTwoExteriorLow_wedge,
    generatorExteriorBracket_wedge]
  change ⁅canonicalGeneratorEvaluation L (v 0).1,
      canonicalGeneratorEvaluation L (v 1).1⁆ -
    ⁅canonicalGeneratorEvaluation L (v 1).1,
      canonicalGeneratorEvaluation L (v 0).1⁆ =
    (2 : ℤ) • ⁅canonicalGeneratorEvaluation L (v 0).1,
      canonicalGeneratorEvaluation L (v 1).1⁆
  have hskew : ⁅canonicalGeneratorEvaluation L (v 1).1,
      canonicalGeneratorEvaluation L (v 0).1⁆ =
      -⁅canonicalGeneratorEvaluation L (v 0).1,
        canonicalGeneratorEvaluation L (v 1).1⁆ := (lie_skew _ _).symm
  rw [hskew]
  abel

/-- Reverse-mixed alternation has the same bracket value as the mixed exterior component. -/
theorem reverseMixedBracket_comp_reverseProjection_comp_exteriorToTensor :
    (freeClassTwoReverseMixedBracket L).comp
        ((TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)).comp
          (exteriorToTensor M)) =
      (freeClassTwoMixedBracket L).comp (freeClassTwoExteriorMixed P) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change freeClassTwoReverseMixedBracket L
      (TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)
        (exteriorToTensor M (wedgeTwo M (v 0) (v 1)))) =
    freeClassTwoMixedBracket L
      (freeClassTwoExteriorMixed P (wedgeTwo M (v 0) (v 1)))
  rw [exteriorToTensor_wedge, map_sub, TensorProduct.map_tmul,
    TensorProduct.map_tmul, map_sub, freeClassTwoReverseMixedBracket_tmul,
    freeClassTwoReverseMixedBracket_tmul, freeClassTwoExteriorMixed_wedge,
    map_sub, freeClassTwoMixedBracket_tmul, freeClassTwoMixedBracket_tmul]
  change ⁅generatorExteriorBracket L (v 0).2,
      canonicalGeneratorEvaluation L (v 1).1⁆ -
    ⁅generatorExteriorBracket L (v 1).2,
      canonicalGeneratorEvaluation L (v 0).1⁆ =
    ⁅canonicalGeneratorEvaluation L (v 0).1,
      generatorExteriorBracket L (v 1).2⁆ -
    ⁅canonicalGeneratorEvaluation L (v 1).1,
      generatorExteriorBracket L (v 0).2⁆
  have h₁ : ⁅generatorExteriorBracket L (v 0).2,
      canonicalGeneratorEvaluation L (v 1).1⁆ =
      -⁅canonicalGeneratorEvaluation L (v 1).1,
        generatorExteriorBracket L (v 0).2⁆ := (lie_skew _ _).symm
  have h₂ : ⁅generatorExteriorBracket L (v 1).2,
      canonicalGeneratorEvaluation L (v 0).1⁆ =
      -⁅canonicalGeneratorEvaluation L (v 0).1,
        generatorExteriorBracket L (v 1).2⁆ := (lie_skew _ _).symm
  rw [h₁, h₂]
  abel

/-- On a relation boundary, the low and reverse-mixed bracket values cancel in class three. -/
theorem low_add_reverseMixed_boundary_bracket_eq_zero
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (chi : Rel₂ ⊗[ℤ] M) :
    freeClassTwoLowTensorBracket L (classTwoResolutionBoundaryLow L chi) +
      freeClassTwoReverseMixedBracket L
        (classTwoResolutionBoundaryReverseMixed L chi) = 0 := by
  induction chi using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
      rw [classTwoResolutionBoundaryLow_tmul,
        classTwoResolutionBoundaryReverseMixed_tmul,
        freeClassTwoLowTensorBracket_tmul,
        freeClassTwoReverseMixedBracket_tmul]
      rw [← add_lie]
      have hmem : ⁅freeClassTwoEvaluationToL L (r : M),
          canonicalGeneratorEvaluation L x.1⁆ ∈
          lowerCentralSeries ℤ L 3 := by
        exact bracket_mem_lowerCentralSeries_three_of_left_mem_two L
          (relation_evaluation_mem_gammaThree L r)
      rw [hclass] at hmem
      simpa [freeClassTwoEvaluationToL_apply] using hmem
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add]
      calc
        (freeClassTwoLowTensorBracket L (classTwoResolutionBoundaryLow L x) +
            freeClassTwoLowTensorBracket L (classTwoResolutionBoundaryLow L y)) +
              (freeClassTwoReverseMixedBracket L
                  (classTwoResolutionBoundaryReverseMixed L x) +
                freeClassTwoReverseMixedBracket L
                  (classTwoResolutionBoundaryReverseMixed L y)) =
            (freeClassTwoLowTensorBracket L
                (classTwoResolutionBoundaryLow L x) +
              freeClassTwoReverseMixedBracket L
                (classTwoResolutionBoundaryReverseMixed L x)) +
            (freeClassTwoLowTensorBracket L
                (classTwoResolutionBoundaryLow L y) +
              freeClassTwoReverseMixedBracket L
                (classTwoResolutionBoundaryReverseMixed L y)) := by abel
        _ = 0 := by rw [hx, hy, add_zero]

/-- **Integral cross identity.**  For a lifted cycle, the mixed bracket is minus twice its
low bracket. -/
theorem freeClassTwoExteriorMixed_bracket_eq_neg_two_low_of_boundary
    (hclass : lowerCentralSeries ℤ L 3 = ⊥)
    (beta : ⋀[ℤ]^2 M) (chi : Rel₂ ⊗[ℤ] M)
    (hbeta : exteriorToTensor M beta = classTwoResolutionBoundary L chi) :
    freeClassTwoMixedBracket L (freeClassTwoExteriorMixed P beta) =
      -(2 : ℤ) • freeClassTwoLowBracket L
        (freeClassTwoExteriorLow P beta) := by
  have hlow := congrArg
    (TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)) hbeta
  have hreverse := congrArg
    (TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)) hbeta
  have hlowEval := congrArg (freeClassTwoLowTensorBracket L) hlow
  have hreverseEval := congrArg (freeClassTwoReverseMixedBracket L) hreverse
  have hlowFormula := LinearMap.congr_fun
    (lowTensorBracket_comp_lowProjection_comp_exteriorToTensor L) beta
  have hreverseFormula := LinearMap.congr_fun
    (reverseMixedBracket_comp_reverseProjection_comp_exteriorToTensor L) beta
  have hlowBoundary := LinearMap.congr_fun
    (tensorLowProjection_comp_classTwoResolutionBoundary L) chi
  have hreverseBoundary := LinearMap.congr_fun
    (tensorReverseMixedProjection_comp_classTwoResolutionBoundary L) chi
  change freeClassTwoLowTensorBracket L
      (TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)
        (exteriorToTensor M beta)) =
    freeClassTwoLowTensorBracket L
      (TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)
        (classTwoResolutionBoundary L chi)) at hlowEval
  change freeClassTwoReverseMixedBracket L
      (TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)
        (exteriorToTensor M beta)) =
    freeClassTwoReverseMixedBracket L
      (TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)
        (classTwoResolutionBoundary L chi)) at hreverseEval
  change freeClassTwoLowTensorBracket L
      (TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)
        (exteriorToTensor M beta)) =
    (2 : ℤ) • freeClassTwoLowBracket L
      (freeClassTwoExteriorLow P beta) at hlowFormula
  change freeClassTwoReverseMixedBracket L
      (TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)
        (exteriorToTensor M beta)) =
    freeClassTwoMixedBracket L
      (freeClassTwoExteriorMixed P beta) at hreverseFormula
  change TensorProduct.map (freeClassTwoFst P) (freeClassTwoFst P)
      (classTwoResolutionBoundary L chi) =
    classTwoResolutionBoundaryLow L chi at hlowBoundary
  change TensorProduct.map (freeClassTwoSnd P) (freeClassTwoFst P)
      (classTwoResolutionBoundary L chi) =
    classTwoResolutionBoundaryReverseMixed L chi at hreverseBoundary
  rw [hlowFormula, hlowBoundary] at hlowEval
  rw [hreverseFormula, hreverseBoundary] at hreverseEval
  have hzero := low_add_reverseMixed_boundary_bracket_eq_zero L hclass chi
  rw [← hlowEval, ← hreverseEval] at hzero
  simpa [neg_smul] using eq_neg_of_add_eq_zero_right hzero

/-- Every mixed boundary tensor has zero mixed bracket in class three. -/
theorem freeClassTwoMixedBracket_comp_boundaryMixed_eq_zero
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    (freeClassTwoMixedBracket L).comp
        (classTwoResolutionBoundaryMixed L) = 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro x
  change ⁅canonicalGeneratorEvaluation L (r : M).1,
      generatorExteriorBracket L x.2⁆ = 0
  have hmem : ⁅canonicalGeneratorEvaluation L (r : M).1,
      generatorExteriorBracket L x.2⁆ ∈ lowerCentralSeries ℤ L 3 := by
    apply bracket_dimensionSubring_le_lowerCentralSeries ℤ L 1 1
    exact LieSubmodule.lie_mem_lie
      (lowerCentralSeries_le_dimensionSubring ℤ L 1
        (relationFst_evaluation_mem_gammaTwo L r))
      (lowerCentralSeries_le_dimensionSubring ℤ L 1
        (generatorExteriorBracket_mem_gammaTwo L x.2))
  rw [hclass] at hmem
  simpa using hmem

/-- **Mixed vanishing for a lifted cycle.**  If `β` alternates to the boundary of a tensor
over the presentation relations, then its `(1,2)` bracket value is zero in class three. -/
theorem freeClassTwoExteriorMixed_bracket_eq_zero_of_boundary
    (hclass : lowerCentralSeries ℤ L 3 = ⊥)
    (beta : ⋀[ℤ]^2 M) (chi : Rel₂ ⊗[ℤ] M)
    (hbeta : exteriorToTensor M beta = classTwoResolutionBoundary L chi) :
    freeClassTwoMixedBracket L (freeClassTwoExteriorMixed P beta) = 0 := by
  have hproject := congrArg
    (TensorProduct.map (freeClassTwoFst P) (freeClassTwoSnd P)) hbeta
  have hmixed : freeClassTwoExteriorMixed P beta =
      classTwoResolutionBoundaryMixed L chi := by
    calc
      freeClassTwoExteriorMixed P beta =
          TensorProduct.map (freeClassTwoFst P) (freeClassTwoSnd P)
            (exteriorToTensor M beta) := by
        have h := LinearMap.congr_fun
          (tensorMixedProjection_comp_exteriorToTensor L) beta
        exact h.symm
      _ = TensorProduct.map (freeClassTwoFst P) (freeClassTwoSnd P)
            (classTwoResolutionBoundary L chi) := hproject
      _ = classTwoResolutionBoundaryMixed L chi := by
        exact LinearMap.congr_fun
          (tensorMixedProjection_comp_classTwoResolutionBoundary L) chi
  rw [hmixed]
  have hzero := LinearMap.congr_fun
    (freeClassTwoMixedBracket_comp_boundaryMixed_eq_zero L hclass) chi
  exact hzero

/-! ## Recombining bracket evaluation -/

/-- Bracket evaluation on the whole explicit class-two presentation module. -/
def freeClassTwoTotalBracketAlternating :
    M [⋀^Fin 2]→ₗ[ℤ] L where
  toFun v := ⁅freeClassTwoEvaluationToL L (v 0),
    freeClassTwoEvaluationToL L (v 1)⁆
  map_update_add' v i x y := by fin_cases i <;> simp <;> abel
  map_update_smul' v i n x := by fin_cases i <;> simp <;> rfl
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change ⁅freeClassTwoEvaluationToL L (v 0),
        freeClassTwoEvaluationToL L (v 1)⁆ = 0
      change v 0 = v 1 at hv
      rw [hv, lie_self]
    · change ⁅freeClassTwoEvaluationToL L (v 0),
        freeClassTwoEvaluationToL L (v 1)⁆ = 0
      change v 1 = v 0 at hv
      rw [hv, lie_self]
    · exact (hij rfl).elim

def freeClassTwoTotalBracket : ⋀[ℤ]^2 M →ₗ[ℤ] L :=
  exteriorPower.alternatingMapLinearEquiv
    (freeClassTwoTotalBracketAlternating L)

@[simp]
theorem freeClassTwoTotalBracket_wedge (x y : M) :
    freeClassTwoTotalBracket L (wedgeTwo M x y) =
      ⁅freeClassTwoEvaluationToL L x, freeClassTwoEvaluationToL L y⁆ := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (freeClassTwoTotalBracketAlternating L) ![x, y]

/-- Bracket evaluation respects the integral low/mixed/high exterior splitting. -/
theorem freeClassTwoTotalBracket_decomposition :
    freeClassTwoTotalBracket L =
      (freeClassTwoLowBracket L).comp (freeClassTwoExteriorLow P) +
        (freeClassTwoMixedBracket L).comp (freeClassTwoExteriorMixed P) +
          (freeClassTwoHighBracket L).comp (freeClassTwoExteriorHigh P) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change freeClassTwoTotalBracket L (exteriorPower.ιMulti ℤ 2 v) =
    ((freeClassTwoLowBracket L).comp (freeClassTwoExteriorLow P) +
      (freeClassTwoMixedBracket L).comp (freeClassTwoExteriorMixed P) +
        (freeClassTwoHighBracket L).comp (freeClassTwoExteriorHigh P))
      (exteriorPower.ιMulti ℤ 2 v)
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  let x : M := v 0
  let y : M := v 1
  change freeClassTwoTotalBracket L (wedgeTwo M x y) =
    (freeClassTwoLowBracket L
        (freeClassTwoExteriorLow P (wedgeTwo M x y)) +
      freeClassTwoMixedBracket L
        (freeClassTwoExteriorMixed P (wedgeTwo M x y))) +
      freeClassTwoHighBracket L
        (freeClassTwoExteriorHigh P (wedgeTwo M x y))
  rw [freeClassTwoTotalBracket_wedge]
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    freeClassTwoExteriorLow_wedge, freeClassTwoExteriorMixed_wedge,
    freeClassTwoExteriorHigh_wedge, generatorExteriorBracket_wedge,
    map_sub, freeClassTwoMixedBracket_tmul, freeClassTwoHighBracket_wedge,
    freeClassTwoEvaluationToL_apply]
  have hskew : ⁅generatorExteriorBracket L x.2,
      canonicalGeneratorEvaluation L y.1⁆ =
      -⁅canonicalGeneratorEvaluation L y.1,
        generatorExteriorBracket L x.2⁆ := (lie_skew _ _).symm
  rw [add_lie, lie_add, lie_add, hskew]
  abel

/-- In class three, a lifted boundary has the same total bracket value as its low part. -/
theorem freeClassTwoTotalBracket_eq_low_of_boundary
    (hclass : lowerCentralSeries ℤ L 3 = ⊥)
    (beta : ⋀[ℤ]^2 M) (chi : Rel₂ ⊗[ℤ] M)
    (hbeta : exteriorToTensor M beta = classTwoResolutionBoundary L chi) :
    freeClassTwoTotalBracket L beta =
      freeClassTwoLowBracket L (freeClassTwoExteriorLow P beta) := by
  have hdecomp := LinearMap.congr_fun
    (freeClassTwoTotalBracket_decomposition L) beta
  rw [hdecomp]
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [freeClassTwoExteriorMixed_bracket_eq_zero_of_boundary L hclass beta chi hbeta]
  have hhigh : freeClassTwoHighBracket L
      (freeClassTwoExteriorHigh P beta) = 0 := by
    have h := LinearMap.congr_fun
      (freeClassTwoHighBracket_eq_zero L hclass)
      (freeClassTwoExteriorHigh P beta)
    simpa using h
  rw [hhigh]
  abel

/-! ## Passage to `L/γ₃` and the invariant certificate -/

/-- The explicit class-two presentation map, viewed only as a linear map. -/
abbrev classTwoToModGammaThree : M →ₗ[ℤ] ModGammaThree L :=
  (canonicalClassTwoEvaluation L).toLinearMap

/-- Image of a total exterior tensor in `⋀²(L/γ₃)`. -/
def classTwoExteriorToModGammaThree :
    ⋀[ℤ]^2 M →ₗ[ℤ] ⋀[ℤ]^2 (ModGammaThree L) :=
  exteriorPower.map 2 (classTwoToModGammaThree L)

/-- Image of a low exterior tensor in `⋀²(L/γ₃)`. -/
def generatorExteriorToModGammaThree :
    ⋀[ℤ]^2 P →ₗ[ℤ] ⋀[ℤ]^2 (ModGammaThree L) :=
  exteriorPower.map 2
    ((lowerCentralSeries ℤ L 2).toSubmodule.mkQ.comp
      (canonicalGeneratorEvaluation L))

@[simp]
theorem classTwoExteriorToModGammaThree_wedge (x y : M) :
    classTwoExteriorToModGammaThree L (wedgeTwo M x y) =
      exteriorWedge L
        (LieSubmodule.Quotient.mk (freeClassTwoEvaluationToL L x))
        (LieSubmodule.Quotient.mk (freeClassTwoEvaluationToL L y)) := by
  calc
    classTwoExteriorToModGammaThree L (wedgeTwo M x y) =
        exteriorPower.ιMulti ℤ 2
          ![classTwoToModGammaThree L x, classTwoToModGammaThree L y] := by
      exact exteriorPower.map_apply_ιMulti
        (n := 2) (classTwoToModGammaThree L) ![x, y]
    _ = _ := by
      change exteriorWedge L (canonicalClassTwoEvaluation L x)
          (canonicalClassTwoEvaluation L y) = _
      rw [canonicalClassTwoEvaluation_eq_mk_freeClassTwoEvaluationToL,
        canonicalClassTwoEvaluation_eq_mk_freeClassTwoEvaluationToL]

@[simp]
theorem generatorExteriorToModGammaThree_wedge (x y : P) :
    generatorExteriorToModGammaThree L (wedgeTwo P x y) =
      exteriorWedge L
        (LieSubmodule.Quotient.mk (canonicalGeneratorEvaluation L x))
        (LieSubmodule.Quotient.mk (canonicalGeneratorEvaluation L y)) := by
  exact exteriorPower.map_apply_ιMulti
    (n := 2)
    ((lowerCentralSeries ℤ L 2).toSubmodule.mkQ.comp
      (canonicalGeneratorEvaluation L)) ![x, y]

/-- Integral alternation commutes with a linear map. -/
theorem exteriorToTensor_naturality
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →ₗ[ℤ] B) :
    (TensorProduct.map f f).comp (exteriorToTensor A) =
      (exteriorToTensor B).comp (exteriorPower.map 2 f) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change TensorProduct.map f f
      (exteriorToTensor A (wedgeTwo A (v 0) (v 1))) =
    exteriorToTensor B
      (exteriorPower.map 2 f (wedgeTwo A (v 0) (v 1)))
  have hmap : exteriorPower.map 2 f (wedgeTwo A (v 0) (v 1)) =
      wedgeTwo B (f (v 0)) (f (v 1)) := by
    exact exteriorPower.map_apply_ιMulti (n := 2) f ![v 0, v 1]
  rw [exteriorToTensor_wedge, map_sub, TensorProduct.map_tmul,
    TensorProduct.map_tmul, hmap, exteriorToTensor_wedge]

/-- The descended exterior bracket agrees with explicit total bracket evaluation. -/
theorem exteriorBracket_comp_classTwoExteriorToModGammaThree
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    (exteriorBracket L hclass).comp (classTwoExteriorToModGammaThree L) =
      freeClassTwoTotalBracket L := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorBracket L hclass
      (classTwoExteriorToModGammaThree L (wedgeTwo M (v 0) (v 1))) =
    freeClassTwoTotalBracket L (wedgeTwo M (v 0) (v 1))
  rw [classTwoExteriorToModGammaThree_wedge, exteriorBracket_wedge,
    bracketModGammaThree_mk_mk, freeClassTwoTotalBracket_wedge]

/-- The descended exterior bracket agrees with low bracket evaluation. -/
theorem exteriorBracket_comp_generatorExteriorToModGammaThree
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    (exteriorBracket L hclass).comp (generatorExteriorToModGammaThree L) =
      freeClassTwoLowBracket L := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorBracket L hclass
      (generatorExteriorToModGammaThree L (wedgeTwo P (v 0) (v 1))) =
    freeClassTwoLowBracket L (wedgeTwo P (v 0) (v 1))
  rw [generatorExteriorToModGammaThree_wedge, exteriorBracket_wedge,
    bracketModGammaThree_mk_mk, generatorExteriorBracket_wedge]

/-- Finite invariant output of the terminal PBW collector, before forgetting the canonical
free presentation. -/
structure ResolutionCycleCertificate
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (a : L) where
  beta : ⋀[ℤ]^2 M
  chi : Rel₂ ⊗[ℤ] M
  alternating_boundary :
    exteriorToTensor M beta = classTwoResolutionBoundary L chi
  total_maps_zero : classTwoExteriorToModGammaThree L beta = 0
  evaluates : a =
    -(freeClassTwoLowBracket L (freeClassTwoExteriorLow P beta))

/-- A lifted alternating boundary automatically maps to zero in the quotient exterior square.
Integral alternation is injective for every Abelian group. -/
theorem classTwoExteriorToModGammaThree_eq_zero_of_boundary
    (beta : ⋀[ℤ]^2 M) (chi : Rel₂ ⊗[ℤ] M)
    (hbeta : exteriorToTensor M beta = classTwoResolutionBoundary L chi) :
    classTwoExteriorToModGammaThree L beta = 0 := by
  apply IntegralAlternation.exteriorToTensor_injective
  rw [map_zero]
  have hnat := LinearMap.congr_fun
    (exteriorToTensor_naturality (classTwoToModGammaThree L)) beta
  change TensorProduct.map (classTwoToModGammaThree L)
      (classTwoToModGammaThree L) (exteriorToTensor M beta) =
    exteriorToTensor (ModGammaThree L)
      (classTwoExteriorToModGammaThree L beta) at hnat
  rw [← hnat, hbeta]
  clear hbeta hnat beta
  induction chi using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
      rw [classTwoResolutionBoundary_tmul, TensorProduct.map_tmul]
      have hr : classTwoToModGammaThree L (r : M) = 0 := r.property
      rw [hr, TensorProduct.zero_tmul]
  | add x y hx hy =>
      calc
        TensorProduct.map (classTwoToModGammaThree L)
            (classTwoToModGammaThree L)
            (classTwoResolutionBoundary L (x + y)) =
            TensorProduct.map (classTwoToModGammaThree L)
              (classTwoToModGammaThree L)
              (classTwoResolutionBoundary L x +
                classTwoResolutionBoundary L y) := by rw [map_add]
        _ =
            TensorProduct.map (classTwoToModGammaThree L)
                (classTwoToModGammaThree L)
                (classTwoResolutionBoundary L x) +
              TensorProduct.map (classTwoToModGammaThree L)
                (classTwoToModGammaThree L)
                (classTwoResolutionBoundary L y) :=
          map_add _ _ _
        _ = 0 := by rw [hx, hy, add_zero]

/-- Constructor in which quotient-exterior vanishing is discharged automatically. -/
def ResolutionCycleCertificate.ofBoundary
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (a : L)
    (beta : ⋀[ℤ]^2 M) (chi : Rel₂ ⊗[ℤ] M)
    (alternating_boundary :
      exteriorToTensor M beta = classTwoResolutionBoundary L chi)
    (evaluates : a =
      -(freeClassTwoLowBracket L (freeClassTwoExteriorLow P beta))) :
    ResolutionCycleCertificate L hclass a where
  beta := beta
  chi := chi
  alternating_boundary := alternating_boundary
  total_maps_zero := classTwoExteriorToModGammaThree_eq_zero_of_boundary L
    beta chi alternating_boundary
  evaluates := evaluates

/-- Constructor matching the output of placed PBW extraction: the ledger evaluates `a` as the
sum of the low and mixed brackets.  The integral cross identity turns that sum into minus the
low bracket required by the invariant certificate. -/
def ResolutionCycleCertificate.ofBoundaryAndLedgerEvaluation
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (a : L)
    (beta : ⋀[ℤ]^2 M) (chi : Rel₂ ⊗[ℤ] M)
    (alternating_boundary :
      exteriorToTensor M beta = classTwoResolutionBoundary L chi)
    (ledger_evaluates : a =
      freeClassTwoLowBracket L (freeClassTwoExteriorLow P beta) +
        freeClassTwoMixedBracket L (freeClassTwoExteriorMixed P beta)) :
    ResolutionCycleCertificate L hclass a := by
  apply ResolutionCycleCertificate.ofBoundary L hclass a beta chi
    alternating_boundary
  rw [ledger_evaluates,
    freeClassTwoExteriorMixed_bracket_eq_neg_two_low_of_boundary L hclass
      beta chi alternating_boundary]
  abel

/-- Basis-dependent PBW output in its most economical form.  The quadratic PBW equation says
that the ordered normal form of `(d₃ ⊗ 1)χ` is zero.  Exactness of the ordered tensor normal
form then constructs the alternating lift `β` integrally; no division by two is involved. -/
def ResolutionCycleCertificate.ofOrderedBoundary
    {ι : Type*} [LinearOrder ι]
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (a : L)
    (b : Module.Basis ι ℤ M) (chi : Rel₂ ⊗[ℤ] M)
    (boundary_normal_eq_zero :
      orderedTensorNormal b (classTwoResolutionBoundary L chi) = 0)
    (ledger_evaluates : a =
      freeClassTwoLowBracket L
          (freeClassTwoExteriorLow P
            (orderedWedgeSection b (classTwoResolutionBoundary L chi))) +
        freeClassTwoMixedBracket L
          (freeClassTwoExteriorMixed P
            (orderedWedgeSection b (classTwoResolutionBoundary L chi)))) :
    ResolutionCycleCertificate L hclass a := by
  let beta : ⋀[ℤ]^2 M :=
    orderedWedgeSection b (classTwoResolutionBoundary L chi)
  apply ResolutionCycleCertificate.ofBoundaryAndLedgerEvaluation
    L hclass a beta chi
  · exact exteriorToTensor_orderedWedgeSection_of_normal_eq_zero b
      (classTwoResolutionBoundary L chi) boundary_normal_eq_zero
  · exact ledger_evaluates

/-- A resolution-cycle certificate supplies exactly the invariant certificate used by the
global quotient reduction. -/
def ResolutionCycleCertificate.toInvariantCertificate
    {hclass : lowerCentralSeries ℤ L 3 = ⊥} {a : L}
    (c : ResolutionCycleCertificate L hclass a) :
    InvariantCertificate L hclass a where
  low := generatorExteriorToModGammaThree L
    (freeClassTwoExteriorLow P c.beta)
  other := classTwoExteriorToModGammaThree L c.beta -
    generatorExteriorToModGammaThree L
      (freeClassTwoExteriorLow P c.beta)
  total_zero := by rw [add_sub_cancel, c.total_maps_zero]
  other_evaluates_zero := by
    rw [map_sub]
    have htotal := LinearMap.congr_fun
      (exteriorBracket_comp_classTwoExteriorToModGammaThree L hclass) c.beta
    have hlow := LinearMap.congr_fun
      (exteriorBracket_comp_generatorExteriorToModGammaThree L hclass)
        (freeClassTwoExteriorLow P c.beta)
    change exteriorBracket L hclass
        (classTwoExteriorToModGammaThree L c.beta) =
      freeClassTwoTotalBracket L c.beta at htotal
    change exteriorBracket L hclass
        (generatorExteriorToModGammaThree L
          (freeClassTwoExteriorLow P c.beta)) =
      freeClassTwoLowBracket L (freeClassTwoExteriorLow P c.beta) at hlow
    rw [htotal, hlow]
    rw [freeClassTwoTotalBracket_eq_low_of_boundary L hclass c.beta c.chi
      c.alternating_boundary, sub_self]
  evaluates := by
    rw [show exteriorBracket L hclass
        (generatorExteriorToModGammaThree L
          (freeClassTwoExteriorLow P c.beta)) =
        freeClassTwoLowBracket L (freeClassTwoExteriorLow P c.beta) by
      exact LinearMap.congr_fun
        (exteriorBracket_comp_generatorExteriorToModGammaThree L hclass)
          (freeClassTwoExteriorLow P c.beta)]
    exact c.evaluates

/-- Hence every resolution-cycle certificate evaluates to zero. -/
theorem ResolutionCycleCertificate.value_eq_zero
    {hclass : lowerCentralSeries ℤ L 3 = ⊥} {a : L}
    (c : ResolutionCycleCertificate L hclass a) : a = 0 :=
  c.toInvariantCertificate.value_eq_zero

end

end DegreeFive

end LieRings
