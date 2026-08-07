import LieRings.DimensionSubring.DegreeFive.StandingReduction
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The third homogeneous Smith quotient

For a surjective free presentation of a class-three Lie ring, the quotient of the exact
weight-three component by the leading weight-three relations is canonically `γ₃(L)`.  This is
the precise fact needed to single out `z` and the relation `qz` in the adapted presentation.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X

/-- A term of free bracket weight at least four evaluates to zero in a class-three target. -/
theorem evaluation_eq_zero_of_mem_lieHigh_four
    (evaluation : LieHom ℤ F L)
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) (f : F)
    (hf : f ∈ FreeLieDimension.lieHigh X 4) : evaluation f = 0 := by
  have hf' : f ∈ lowerCentralSeries ℤ F 3 := by
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X 3] using hf
  have hmap : evaluation f ∈ lowerCentralSeries ℤ L 3 := by
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := evaluation) 3)
    exact LieIdeal.mem_map hf'
  rw [hclass] at hmap
  exact hmap

/-- Evaluation of exact weight three, with codomain restricted to `γ₃(L)`. -/
def exactThreeEvaluation
    (evaluation : LieHom ℤ F L) :
    freeLieExact X 3 →ₗ[ℤ] lowerCentralSeries ℤ L 2 :=
  (evaluation.toLinearMap.domRestrict (freeLieExact X 3)).codRestrict
    (lowerCentralSeries ℤ L 2) (fun x ↦ by
    have hxHigh := freeLieExact_mem_lieHigh X x
    have hx : (x : F) ∈ lowerCentralSeries ℤ F 2 := by
      simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X 2] using hxHigh
    apply (LieIdeal.map_lowerCentralSeries_le (R := ℤ) (f := evaluation) 2)
    exact LieIdeal.mem_map hx)

@[simp]
theorem coe_exactThreeEvaluation
    (evaluation : LieHom ℤ F L) (x : freeLieExact X 3) :
    (exactThreeEvaluation X L evaluation x : L) = evaluation (x : F) := rfl

/-- Exact weight three surjects onto `γ₃(L)` for a surjective presentation of a class-three
target. -/
theorem exactThreeEvaluation_surjective
    (evaluation : LieHom ℤ F L) (heval : Function.Surjective evaluation)
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    Function.Surjective (exactThreeEvaluation X L evaluation) := by
  intro y
  have hymap : (y : L) ∈
      (lowerCentralSeries ℤ F 2).map evaluation := by
    rw [LieIdeal.lowerCentralSeries_map_eq 2 heval]
    exact y.property
  obtain ⟨f, hfeval⟩ := LieIdeal.mem_map_of_surjective
    (I := lowerCentralSeries ℤ F 2) heval hymap
  let x : freeLieExact X 3 :=
    ⟨freeLieLengthComponent X 3 (f : F),
      freeLieLengthComponent_mem_exact X 3 (f : F)⟩
  refine ⟨x, Subtype.ext ?_⟩
  have hfHigh : (f : F) ∈ FreeLieDimension.lieHigh X 3 := by
    simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X 2] using f.property
  have hxHigh : (x : F) ∈ FreeLieDimension.lieHigh X 3 :=
    freeLieExact_mem_lieHigh X x
  have hcomponent : freeLieLengthComponent X 3 ((f : F) - (x : F)) = 0 := by
    rw [map_sub, freeLieLengthComponent_coe_exact X 3 x]
    change freeLieLengthComponent X 3 (f : F) -
      freeLieLengthComponent X 3 (f : F) = 0
    exact sub_self _
  have hremHigh : (f : F) - (x : F) ∈ FreeLieDimension.lieHigh X 4 := by
    simpa using mem_lieHigh_succ_of_component_eq_zero X
      ((FreeLieDimension.lieHigh X 3).sub_mem hfHigh hxHigh) hcomponent
  have hremZero := evaluation_eq_zero_of_mem_lieHigh_four
    X L evaluation hclass ((f : F) - (x : F)) hremHigh
  rw [map_sub, sub_eq_zero] at hremZero
  change evaluation (x : F) = (y : L)
  exact hremZero.symm.trans hfeval

/-- The leading weight-three relation module is exactly the kernel of exact evaluation to
`γ₃(L)`. -/
theorem homogeneousRelationLeading_three_eq_ker
    (evaluation : LieHom ℤ F L)
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    homogeneousRelationLeading X L evaluation 3 =
      LinearMap.ker (exactThreeEvaluation X L evaluation) := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hprojection⟩ := hx
    change exactThreeEvaluation X L evaluation x = 0
    apply Subtype.ext
    change evaluation (x : F) = 0
    have hrHigh : (r : F) ∈ FreeLieDimension.lieHigh X 3 := hr.2
    have hxHigh : (x : F) ∈ FreeLieDimension.lieHigh X 3 :=
      freeLieExact_mem_lieHigh X x
    have hprojection' : freeLieLengthComponent X 3 (r : F) = (x : F) :=
      congrArg Subtype.val hprojection
    have hcomponent : freeLieLengthComponent X 3 ((r : F) - (x : F)) = 0 := by
      rw [map_sub, freeLieLengthComponent_coe_exact X 3 x]
      rw [hprojection', sub_self]
    have hremHigh : (r : F) - (x : F) ∈ FreeLieDimension.lieHigh X 4 := by
      simpa using mem_lieHigh_succ_of_component_eq_zero X
        ((FreeLieDimension.lieHigh X 3).sub_mem hrHigh hxHigh) hcomponent
    have hremZero := evaluation_eq_zero_of_mem_lieHigh_four
      X L evaluation hclass ((r : F) - (x : F)) hremHigh
    rw [map_sub] at hremZero
    have hrzero : evaluation r = 0 := hr.1
    simpa [hrzero] using hremZero
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hxeval : evaluation (x : F) = 0 := congrArg Subtype.val hx
    let r : filteredPresentationRelations X L evaluation 3 :=
      ⟨(x : F), hxeval, freeLieExact_mem_lieHigh X x⟩
    exact ⟨r, r.property, by
      apply Subtype.ext
      simpa [r] using freeLieLengthComponent_coe_exact X 3 x⟩

/-- The third homogeneous relation quotient is canonically the cyclic `γ₃(L)` from the
standing reduction. -/
def homogeneousThreeQuotientEquivGammaThree
    (evaluation : LieHom ℤ F L) (heval : Function.Surjective evaluation)
    (hclass : lowerCentralSeries ℤ L 3 = ⊥) :
    (freeLieExact X 3 ⧸ homogeneousRelationLeading X L evaluation 3) ≃ₗ[ℤ]
      lowerCentralSeries ℤ L 2 :=
  (Submodule.quotEquivOfEq _ _
      (homogeneousRelationLeading_three_eq_ker X L evaluation hclass)).trans
    ((exactThreeEvaluation X L evaluation).quotKerEquivOfSurjective
      (exactThreeEvaluation_surjective X L evaluation heval hclass))

/-- Under the standing reduction, the third homogeneous quotient is literally `ZMod q`. -/
def homogeneousThreeQuotientEquivZMod
    (R : StandingReductionData L)
    (evaluation : LieHom ℤ F L) (heval : Function.Surjective evaluation) :
    (freeLieExact X 3 ⧸ homogeneousRelationLeading X L evaluation 3) ≃ₗ[ℤ]
      ZMod R.q :=
  (homogeneousThreeQuotientEquivGammaThree X L evaluation heval R.classThree).trans
    R.gammaThreeEquiv.toIntLinearEquiv

/-- For the canonical free presentation, the cyclic weight-three identification uses no
hypothesis beyond the standing reduction. -/
def StandingReductionData.canonicalHomogeneousThreeQuotientEquivZMod
    (R : StandingReductionData L) :
    letI : Finite L := R.finite_inst
    (freeLieExact L 3 ⧸ homogeneousRelationLeading L L
      (canonicalFreeLieEvaluation L) 3) ≃ₗ[ℤ] ZMod R.q := by
  letI : Finite L := R.finite_inst
  exact homogeneousThreeQuotientEquivZMod L L R
    (canonicalFreeLieEvaluation L) (canonicalFreeLieEvaluation_surjective L)

end

end DegreeFive

end LieRings
