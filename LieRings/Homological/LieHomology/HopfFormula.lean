import LieRings.Homological.LieHomology.Presentation
import LieRings.Homological.SecondHomology

/-!
# The Hopf formula for Chevalley--Eilenberg second homology

For a surjection from a free Lie algebra `F → L`, we identify the standard CE object

`H₂(L; R) = ker(d₂) / im(d₃)`

with the Hopf multiplier `(ker p ∩ [F,F]) / [F, ker p]`.  The proof follows the reduced-exterior
square argument in the manuscript literally.
-/

universe u v w

namespace LieRings.Homological.LieHomology

noncomputable section

-- The quotient constructions below contain several nested subtypes and need a larger typeclass
-- elaboration budget.  This does not increase tactic proof search.
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 100000

variable (R : Type u) (X : Type v) {L : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]

private abbrev F := FreeLieAlgebra R X

/-- The relation ideal of a free presentation. -/
abbrev presentationRelations (p : LieHom R (F R X) L) : LieIdeal R (F R X) :=
  LieHom.ker p

/-- The Hopf numerator `ker p ∩ [F,F]`. -/
abbrev presentationHopfNumerator (p : LieHom R (F R X) L) : LieIdeal R (F R X) :=
  presentationRelations R X p ⊓ freeDerived R X

/-- The Hopf denominator `[F, ker p]`. -/
abbrev presentationHopfDenominator (p : LieHom R (F R X) L) : LieIdeal R (F R X) :=
  ⁅(⊤ : LieIdeal R (F R X)), presentationRelations R X p⁆

theorem presentationHopfDenominator_le_numerator (p : LieHom R (F R X) L) :
    presentationHopfDenominator R X p ≤ presentationHopfNumerator R X p := by
  rw [le_inf_iff]
  exact ⟨LieSubmodule.lie_le_right _ _,
    LieSubmodule.mono_lie_right (⊤ : LieIdeal R (F R X)) le_top⟩

/-- The denominator as a submodule of the numerator. -/
abbrev presentationHopfRelations (p : LieHom R (F R X) L) :
    Submodule R (presentationHopfNumerator R X p) :=
  (presentationHopfDenominator R X p).toSubmodule.comap
    (presentationHopfNumerator R X p).toSubmodule.subtype

/-- The presentation-level Hopf multiplier over an arbitrary commutative ring. -/
abbrev PresentationHopfMultiplier (p : LieHom R (F R X) L) :=
  presentationHopfNumerator R X p ⧸ presentationHopfRelations R X p

/-- The denominator, regarded as a submodule of the free derived ideal. -/
abbrev denominatorInFreeDerived (p : LieHom R (F R X) L) :
    Submodule R (freeDerived R X) :=
  (presentationHopfDenominator R X p).toSubmodule.comap
    (freeDerived R X).toSubmodule.subtype

private theorem relationWedges_map_freeReducedExteriorEquivDerived
    (p : LieHom R (F R X) L) :
    (relationWedges R p).map (freeReducedExteriorEquivDerived R X).toLinearMap =
      denominatorInFreeDerived R X p := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, relationWedges, Submodule.span_le]
    rintro _ ⟨r, hr, x, rfl⟩
    change freeReducedExteriorEquivDerived R X
        (reducedWedge R (F R X) r x) ∈ denominatorInFreeDerived R X p
    rw [show freeReducedExteriorEquivDerived R X
        (reducedWedge R (F R X) r x) =
          ⟨⁅r, x⁆, LieSubmodule.lie_mem_lie (by simp) (by simp)⟩ from
      reducedBracketToFreeDerived_wedge R X r x]
    change ⁅r, x⁆ ∈ presentationHopfDenominator R X p
    have hmem : ⁅r, x⁆ ∈
        ⁅presentationRelations R X p, (⊤ : LieIdeal R (F R X))⁆ :=
      LieSubmodule.lie_mem_lie hr (by simp)
    rw [LieSubmodule.lie_comm] at hmem
    exact hmem
  · intro z hz
    change (z : F R X) ∈ presentationHopfDenominator R X p at hz
    have hzspan : (z : F R X) ∈ Submodule.span R
        {q : F R X | ∃ a ∈ (⊤ : LieIdeal R (F R X)),
          ∃ r ∈ presentationRelations R X p, ⁅a, r⁆ = q} := by
      rw [← LieSubmodule.lieIdeal_oper_eq_linear_span'
        (presentationRelations R X p) (⊤ : LieIdeal R (F R X))]
      exact hz
    let W : Submodule R (freeDerived R X) :=
      (relationWedges R p).map (freeReducedExteriorEquivDerived R X).toLinearMap
    have hzmap : (z : F R X) ∈ W.map (freeDerived R X).toSubmodule.subtype := by
      refine Submodule.span_induction
        (p := fun q _ => q ∈ W.map (freeDerived R X).toSubmodule.subtype)
        ?_ ?_ ?_ ?_ hzspan
      · rintro q ⟨a, -, r, hr, rfl⟩
        let w : ReducedExteriorSquare R (F R X) :=
          -reducedWedge R (F R X) r a
        have hwrel : w ∈ relationWedges R p := by
          exact (relationWedges R p).neg_mem (relationWedge_mem R p hr a)
        have hweq : freeReducedExteriorEquivDerived R X w =
            ⟨⁅a, r⁆, LieSubmodule.lie_mem_lie (by simp) (by simp)⟩ := by
          apply Subtype.ext
          change reducedBracket R (F R X) (-reducedWedge R (F R X) r a) = ⁅a, r⁆
          rw [map_neg, reducedBracket_wedge, lie_skew]
        have hwW : freeReducedExteriorEquivDerived R X w ∈ W :=
          Submodule.mem_map_of_mem hwrel
        refine ⟨freeReducedExteriorEquivDerived R X w, hwW, ?_⟩
        exact congrArg Subtype.val hweq
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        exact (W.map (freeDerived R X).toSubmodule.subtype).add_mem ha hb
      · intro r a _ ha
        exact (W.map (freeDerived R X).toSubmodule.subtype).smul_mem r ha
    obtain ⟨y, hyW, hyz⟩ := hzmap
    have hy_eq : y = z := Subtype.ext hyz
    change z ∈ W
    rw [← hy_eq]
    exact hyW

/-- The manuscript's isomorphism
`Λ̃² L ≃ [F,F] / [F, ker p]`. -/
def reducedExteriorEquivDerivedQuotient (p : LieHom R (F R X) L)
    (hp : Function.Surjective p) :
    ReducedExteriorSquare R L ≃ₗ[R]
      (freeDerived R X ⧸ denominatorInFreeDerived R X p) :=
  (reducedExteriorPresentationEquiv R p hp).trans
    (Submodule.Quotient.equiv (relationWedges R p)
      (denominatorInFreeDerived R X p) (freeReducedExteriorEquivDerived R X)
      (relationWedges_map_freeReducedExteriorEquivDerived R X p))

/-- Evaluation on the derived ideal of the free source. -/
def freeDerivedEvaluation (p : LieHom R (F R X) L) :
    freeDerived R X →ₗ[R] L :=
  p.toLinearMap.comp (freeDerived R X).toSubmodule.subtype

private theorem denominatorInFreeDerived_le_ker_evaluation
    (p : LieHom R (F R X) L) :
    denominatorInFreeDerived R X p ≤ LinearMap.ker (freeDerivedEvaluation R X p) := by
  intro z hz
  change p (z : F R X) = 0
  change (z : F R X) ∈ presentationHopfDenominator R X p at hz
  have hzspan : (z : F R X) ∈ Submodule.span R
      {q : F R X | ∃ a ∈ (⊤ : LieIdeal R (F R X)),
        ∃ r ∈ presentationRelations R X p, ⁅a, r⁆ = q} := by
    rw [← LieSubmodule.lieIdeal_oper_eq_linear_span'
      (presentationRelations R X p) (⊤ : LieIdeal R (F R X))]
    exact hz
  refine Submodule.span_induction
    (p := fun q _ => p q = 0) ?_ (map_zero p) ?_ ?_ hzspan
  · rintro q ⟨a, -, r, hr, rfl⟩
    rw [p.map_lie]
    have hr0 : p r = 0 := hr
    rw [hr0, lie_zero]
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro r a _ ha
    rw [map_smul, ha, smul_zero]

/-- The map `[F,F]/[F,ker p] → L` induced by the presentation evaluation. -/
def derivedQuotientEvaluation (p : LieHom R (F R X) L) :
    (freeDerived R X ⧸ denominatorInFreeDerived R X p) →ₗ[R] L :=
  (denominatorInFreeDerived R X p).liftQ (freeDerivedEvaluation R X p)
    (denominatorInFreeDerived_le_ker_evaluation R X p)

@[simp]
theorem derivedQuotientEvaluation_mk (p : LieHom R (F R X) L)
    (z : freeDerived R X) :
    derivedQuotientEvaluation R X p (Submodule.Quotient.mk z) = p (z : F R X) :=
  rfl

@[simp]
theorem reducedExteriorEquivDerivedQuotient_wedge_map
    (p : LieHom R (F R X) L) (hp : Function.Surjective p) (x y : F R X) :
    reducedExteriorEquivDerivedQuotient R X p hp
        (reducedWedge R L (p x) (p y)) =
      Submodule.Quotient.mk
        (⟨⁅x, y⁆, LieSubmodule.lie_mem_lie (by simp) (by simp)⟩ : freeDerived R X) := by
  rw [reducedExteriorEquivDerivedQuotient, LinearEquiv.trans_apply,
    show reducedExteriorPresentationEquiv R p hp
        (reducedWedge R L (p x) (p y)) =
          reducedExteriorToPresentationQuotient R p hp
            (reducedWedge R L (p x) (p y)) by rfl,
    reducedExteriorToPresentationQuotient_wedge_map]
  rw [Submodule.Quotient.equiv_apply,
    show relationClass R p (reducedWedge R (F R X) x y) =
        Submodule.Quotient.mk (reducedWedge R (F R X) x y) by rfl,
    Submodule.mapQ_apply]
  apply congrArg (fun z : freeDerived R X =>
    (Submodule.Quotient.mk z : freeDerived R X ⧸ denominatorInFreeDerived R X p))
  change reducedBracketToFreeDerived R X (reducedWedge R (F R X) x y) = _
  exact reducedBracketToFreeDerived_wedge R X x y

/-- The presentation isomorphism intertwines the reduced bracket with evaluation. -/
theorem derivedQuotientEvaluation_comp_reducedExteriorEquiv
    (p : LieHom R (F R X) L) (hp : Function.Surjective p) :
    (derivedQuotientEvaluation R X p).comp
        (reducedExteriorEquivDerivedQuotient R X p hp).toLinearMap =
      reducedBracket R L := by
  apply reducedExteriorMap_ext R L
  intro a b
  obtain ⟨x, rfl⟩ := hp a
  obtain ⟨y, rfl⟩ := hp b
  change derivedQuotientEvaluation R X p
      (reducedExteriorEquivDerivedQuotient R X p hp
        (reducedWedge R L (p x) (p y))) =
    reducedBracket R L (reducedWedge R L (p x) (p y))
  rw [reducedExteriorEquivDerivedQuotient_wedge_map,
    derivedQuotientEvaluation_mk, reducedBracket_wedge, p.map_lie]

/-- The commuting presentation square identifies the two bracket kernels. -/
def reducedBracketKernelEquivDerivedEvaluationKernel
    (p : LieHom R (F R X) L) (hp : Function.Surjective p) :
    LinearMap.ker (reducedBracket R L) ≃ₗ[R]
      LinearMap.ker (derivedQuotientEvaluation R X p) where
  toFun z := ⟨reducedExteriorEquivDerivedQuotient R X p hp z, by
    exact (LinearMap.congr_fun
      (derivedQuotientEvaluation_comp_reducedExteriorEquiv R X p hp) z).trans
        z.property⟩
  invFun z := ⟨(reducedExteriorEquivDerivedQuotient R X p hp).symm z, by
    calc
      reducedBracket R L ((reducedExteriorEquivDerivedQuotient R X p hp).symm z) =
          derivedQuotientEvaluation R X p
            (reducedExteriorEquivDerivedQuotient R X p hp
              ((reducedExteriorEquivDerivedQuotient R X p hp).symm z)) :=
        (LinearMap.congr_fun
          (derivedQuotientEvaluation_comp_reducedExteriorEquiv R X p hp)
          ((reducedExteriorEquivDerivedQuotient R X p hp).symm z)).symm
      _ = derivedQuotientEvaluation R X p z := by
        rw [(reducedExteriorEquivDerivedQuotient R X p hp).apply_symm_apply]
      _ = 0 := z.property⟩
  left_inv z := by
    apply Subtype.ext
    exact (reducedExteriorEquivDerivedQuotient R X p hp).symm_apply_apply z
  right_inv z := by
    apply Subtype.ext
    exact (reducedExteriorEquivDerivedQuotient R X p hp).apply_symm_apply z
  map_add' x y := by
    apply Subtype.ext
    exact map_add (reducedExteriorEquivDerivedQuotient R X p hp) x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (reducedExteriorEquivDerivedQuotient R X p hp) r x.1

/-- The Hopf numerator maps to the kernel of evaluation on the derived quotient. -/
def hopfNumeratorToDerivedEvaluationKernel (p : LieHom R (F R X) L) :
    presentationHopfNumerator R X p →ₗ[R]
      LinearMap.ker (derivedQuotientEvaluation R X p) where
  toFun z := ⟨Submodule.Quotient.mk
      (⟨(z : F R X), z.property.2⟩ : freeDerived R X), by
    change p (z : F R X) = 0
    exact z.property.1⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

private theorem ker_hopfNumeratorToDerivedEvaluationKernel
    (p : LieHom R (F R X) L) :
    LinearMap.ker (hopfNumeratorToDerivedEvaluationKernel R X p) =
      presentationHopfRelations R X p := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    have hz' := congrArg Subtype.val hz
    change (Submodule.Quotient.mk
      (⟨(z : F R X), z.property.2⟩ : freeDerived R X) :
        freeDerived R X ⧸ denominatorInFreeDerived R X p) = 0 at hz'
    have hzden :
        (⟨(z : F R X), z.property.2⟩ : freeDerived R X) ∈
          denominatorInFreeDerived R X p :=
      (Submodule.Quotient.mk_eq_zero (denominatorInFreeDerived R X p)).1 hz'
    change (z : F R X) ∈ presentationHopfDenominator R X p
    exact hzden
  · intro hz
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change (Submodule.Quotient.mk
      (⟨(z : F R X), z.property.2⟩ : freeDerived R X) :
        freeDerived R X ⧸ denominatorInFreeDerived R X p) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact hz

private theorem hopfNumeratorToDerivedEvaluationKernel_surjective
    (p : LieHom R (F R X) L) :
    Function.Surjective (hopfNumeratorToDerivedEvaluationKernel R X p) := by
  intro z
  obtain ⟨d, hd⟩ :=
    (Submodule.Quotient.mk_surjective (denominatorInFreeDerived R X p)) z.1
  have hpd : p (d : F R X) = 0 := by
    have hz := z.property
    rw [← hd] at hz
    exact hz
  let x : presentationHopfNumerator R X p :=
    ⟨(d : F R X), ⟨hpd, d.property⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hd

/-- The kernel of `[F,F]/[F,ker p] → L` is the Hopf multiplier. -/
def presentationHopfEquivDerivedEvaluationKernel
    (p : LieHom R (F R X) L) :
    PresentationHopfMultiplier R X p ≃ₗ[R]
      LinearMap.ker (derivedQuotientEvaluation R X p) :=
  (Submodule.quotEquivOfEq
      (presentationHopfRelations R X p)
      (LinearMap.ker (hopfNumeratorToDerivedEvaluationKernel R X p))
      (ker_hopfNumeratorToDerivedEvaluationKernel R X p).symm).trans
    ((hopfNumeratorToDerivedEvaluationKernel R X p).quotKerEquivOfSurjective
      (hopfNumeratorToDerivedEvaluationKernel_surjective R X p))

@[simp]
theorem presentationHopfEquivDerivedEvaluationKernel_mk
    (p : LieHom R (F R X) L) (x : presentationHopfNumerator R X p) :
    presentationHopfEquivDerivedEvaluationKernel R X p
        (Submodule.Quotient.mk x) =
      hopfNumeratorToDerivedEvaluationKernel R X p x := by
  rw [presentationHopfEquivDerivedEvaluationKernel, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- **Hopf formula for Chevalley--Eilenberg homology.**  For every free presentation
`p : FreeLieAlgebra R X → L`, the standard second CE homology is canonically isomorphic to
`(ker p ∩ [F,F]) / [F,ker p]`. -/
def secondHomologyHopfEquiv (p : LieHom R (F R X) L)
    (hp : Function.Surjective p) :
    SecondHomology R L ≃ₗ[R] PresentationHopfMultiplier R X p :=
  (secondHomologyEquivReducedBracketKernel R L).trans
    ((reducedBracketKernelEquivDerivedEvaluationKernel R X p hp).trans
      (presentationHopfEquivDerivedEvaluationKernel R X p).symm)

/-- The Hopf formula stated for degree two of the all-degree CE homology object. -/
def homologyTwoHopfEquiv (p : LieHom R (F R X) L)
    (hp : Function.Surjective p) :
    Homology (R := R) (L := L) 2 ≃ₗ[R] PresentationHopfMultiplier R X p :=
  (secondHomologyConcreteIso R L).toLinearEquiv.trans
    (secondHomologyHopfEquiv R X p hp)

end

end LieRings.Homological.LieHomology

namespace LieRings.Homological.FreePresentation

noncomputable section

variable {L : Type u} [LieRing L]

set_option maxHeartbeats 2000000 in
-- Unifying the generic and project-specific nested quotient abbreviations is elaboration-heavy.
/-- The Hopf formula specialized to one of the project's integral free presentations. -/
def ceSecondHomologyEquivHopf (P : FreePresentation L) :
    LieHomology.SecondHomology ℤ L ≃ₗ[ℤ] P.hopfSecondHomology := by
  change LieHomology.SecondHomology ℤ L ≃ₗ[ℤ]
    LieHomology.PresentationHopfMultiplier ℤ P.Generators P.evaluation
  exact LieHomology.secondHomologyHopfEquiv ℤ P.Generators
    P.evaluation P.surjective

set_option maxHeartbeats 2000000 in
-- The canonical presentation expands several nested quotient abbreviations during elaboration.
/-- Standard integral Chevalley--Eilenberg `H₂` is canonically isomorphic to the project's
canonical Hopf-formula model. -/
def ceSecondHomologyEquivHopfModel :
    LieHomology.SecondHomology ℤ L ≃ₗ[ℤ] secondHomology L :=
  ceSecondHomologyEquivHopf (canonicalPresentation L)

set_option maxHeartbeats 2000000 in
-- This expands both the categorical homology quotient and the canonical presentation quotient.
/-- Degree two of the all-degree integral CE homology object, compared with the canonical Hopf
model used by the pre-existing five-term API. -/
def ceHomologyTwoEquivHopfModel :
    LieHomology.Homology (R := ℤ) (L := L) 2 ≃ₗ[ℤ] secondHomology L :=
  (LieHomology.secondHomologyConcreteIso ℤ L).toLinearEquiv.trans
    ceSecondHomologyEquivHopfModel

end

end LieRings.Homological.FreePresentation
