import LieRings.Homological.LieHomology.HopfFormula

/-!
# Naturality of the Hopf formula

This file proves naturality of the CE Hopf isomorphism with respect to a commuting morphism of
free presentations.  Everything is formulated over an arbitrary commutative ring, avoiding any
presentation-specific choice of scalar-module instance.
-/

universe u v w x y

namespace LieRings.Homological.LieHomology

noncomputable section

variable (R : Type u) [CommRing R]
variable {X : Type v} {Y : Type w}
variable {L : Type x} [LieRing L] [LieAlgebra R L]
variable {M : Type y} [LieRing M] [LieAlgebra R M]
variable {p : LieHom R (FreeLieAlgebra R X) L}
variable {q : LieHom R (FreeLieAlgebra R Y) M}

/-- A commuting morphism between two free presentations. -/
structure PresentationHom
    (p : LieHom R (FreeLieAlgebra R X) L)
    (q : LieHom R (FreeLieAlgebra R Y) M) where
  base : LieHom R L M
  free : LieHom R (FreeLieAlgebra R X) (FreeLieAlgebra R Y)
  commutes : q.comp free = base.comp p

namespace PresentationHom

variable (f : PresentationHom R p q)

theorem map_relations :
    LieIdeal.map f.free (presentationRelations R X p) ≤
      presentationRelations R Y q := by
  rw [LieIdeal.map_le_iff_le_comap]
  intro z hz
  change q (f.free z) = 0
  have hz0 : p z = 0 := hz
  have h := LieHom.congr_fun f.commutes z
  simpa [hz0] using h

theorem map_freeDerived :
    LieIdeal.map f.free (freeDerived R X) ≤ freeDerived R Y := by
  exact (LieIdeal.map_bracket_le f.free).trans
    (LieSubmodule.mono_lie le_top le_top)

theorem map_hopfDenominator :
    LieIdeal.map f.free (presentationHopfDenominator R X p) ≤
      presentationHopfDenominator R Y q := by
  exact (LieIdeal.map_bracket_le f.free).trans
    (LieSubmodule.mono_lie le_top (map_relations (R := R) f))

theorem map_hopfNumerator :
    LieIdeal.map f.free (presentationHopfNumerator R X p) ≤
      presentationHopfNumerator R Y q := by
  rw [LieIdeal.map_le_iff_le_comap]
  intro z hz
  exact ⟨(LieIdeal.map_le_iff_le_comap.mp (map_relations (R := R) f)) hz.1,
    (LieIdeal.map_le_iff_le_comap.mp (map_freeDerived (R := R) f)) hz.2⟩

/-- The map between Hopf numerators induced by a presentation morphism. -/
def numeratorMap :
    presentationHopfNumerator R X p →ₗ[R]
      presentationHopfNumerator R Y q :=
  f.free.toLinearMap.restrict (by
    intro z hz
    exact (LieIdeal.map_le_iff_le_comap.mp (map_hopfNumerator (R := R) f)) hz)

theorem hopfRelations_le_comap_numeratorMap :
    presentationHopfRelations R X p ≤
      (presentationHopfRelations R Y q).comap (numeratorMap (R := R) f) := by
  intro z hz
  change f.free (z : FreeLieAlgebra R X) ∈ presentationHopfDenominator R Y q
  change (z : FreeLieAlgebra R X) ∈ presentationHopfDenominator R X p at hz
  exact (LieIdeal.map_le_iff_le_comap.mp (map_hopfDenominator (R := R) f)) hz

/-- The map on presentation-level Hopf multipliers. -/
def hopfMap : PresentationHopfMultiplier R X p →ₗ[R]
    PresentationHopfMultiplier R Y q :=
  (presentationHopfRelations R X p).mapQ
    (presentationHopfRelations R Y q) (numeratorMap (R := R) f)
    (hopfRelations_le_comap_numeratorMap (R := R) f)

@[simp]
theorem hopfMap_mk (z : presentationHopfNumerator R X p) :
    hopfMap (R := R) f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (numeratorMap (R := R) f z) :=
  rfl

/-- The map between the derived ideals of the free sources. -/
def derivedMap : freeDerived R X →ₗ[R] freeDerived R Y :=
  f.free.toLinearMap.restrict (by
    intro z hz
    exact (LieIdeal.map_le_iff_le_comap.mp (map_freeDerived (R := R) f)) hz)

theorem denominatorInFreeDerived_le_comap_derivedMap :
    denominatorInFreeDerived R X p ≤
      (denominatorInFreeDerived R Y q).comap (derivedMap (R := R) f) := by
  intro z hz
  change f.free (z : FreeLieAlgebra R X) ∈ presentationHopfDenominator R Y q
  change (z : FreeLieAlgebra R X) ∈ presentationHopfDenominator R X p at hz
  exact (LieIdeal.map_le_iff_le_comap.mp (map_hopfDenominator (R := R) f)) hz

/-- The induced map `[F,F]/[F,ker p] → [F',F']/[F',ker q]`. -/
def derivedQuotientMap :
    (freeDerived R X ⧸ denominatorInFreeDerived R X p) →ₗ[R]
      (freeDerived R Y ⧸ denominatorInFreeDerived R Y q) :=
  (denominatorInFreeDerived R X p).mapQ
    (denominatorInFreeDerived R Y q) (derivedMap (R := R) f)
    (denominatorInFreeDerived_le_comap_derivedMap (R := R) f)

@[simp]
theorem derivedQuotientMap_mk (z : freeDerived R X) :
    derivedQuotientMap (R := R) f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (derivedMap (R := R) f z) :=
  rfl

/-- Naturality of `Λ̃²L ≃ [F,F]/[F,ker p]`. -/
theorem reducedExteriorEquivDerivedQuotient_natural
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    (derivedQuotientMap (R := R) f).comp
        (reducedExteriorEquivDerivedQuotient R X p hp).toLinearMap =
      (reducedExteriorEquivDerivedQuotient R Y q hq).toLinearMap.comp
        (reducedExteriorMap (R := R) (L := L) (K := M) f.base) := by
  apply reducedExteriorMap_ext R L
  intro a b
  obtain ⟨s, rfl⟩ := hp a
  obtain ⟨t, rfl⟩ := hp b
  have hs : q (f.free s) = f.base (p s) := LieHom.congr_fun f.commutes s
  have ht : q (f.free t) = f.base (p t) := LieHom.congr_fun f.commutes t
  change derivedQuotientMap (R := R) f
      (reducedExteriorEquivDerivedQuotient R X p hp
        (reducedWedge R L (p s) (p t))) =
    reducedExteriorEquivDerivedQuotient R Y q hq
      (reducedExteriorMap (R := R) (L := L) (K := M) f.base
        (reducedWedge R L (p s) (p t)))
  rw [reducedExteriorEquivDerivedQuotient_wedge_map,
    derivedQuotientMap_mk, reducedExteriorMap_wedge, ← hs, ← ht,
    reducedExteriorEquivDerivedQuotient_wedge_map]
  apply congrArg (fun z : freeDerived R Y =>
    (Submodule.Quotient.mk z :
      freeDerived R Y ⧸ denominatorInFreeDerived R Y q))
  apply Subtype.ext
  exact f.free.map_lie s t

/-- Evaluation of the derived quotients commutes with the base map. -/
theorem derivedQuotientEvaluation_natural :
    (derivedQuotientEvaluation R Y q).comp (derivedQuotientMap (R := R) f) =
      f.base.toLinearMap.comp (derivedQuotientEvaluation R X p) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      rw [LinearMap.comp_apply, derivedQuotientMap_mk,
        derivedQuotientEvaluation_mk, LinearMap.comp_apply,
        derivedQuotientEvaluation_mk]
      exact LieHom.congr_fun f.commutes z

/-- The induced map between the two evaluation kernels. -/
def derivedEvaluationKernelMap :
    LinearMap.ker (derivedQuotientEvaluation R X p) →ₗ[R]
      LinearMap.ker (derivedQuotientEvaluation R Y q) where
  toFun z := ⟨derivedQuotientMap (R := R) f z.1, by
    calc
      derivedQuotientEvaluation R Y q (derivedQuotientMap (R := R) f z.1) =
          f.base (derivedQuotientEvaluation R X p z.1) :=
        LinearMap.congr_fun (derivedQuotientEvaluation_natural (R := R) f) z.1
      _ = 0 := by rw [z.property, map_zero]⟩
  map_add' a b := by
    apply Subtype.ext
    exact map_add (derivedQuotientMap (R := R) f) a.1 b.1
  map_smul' r a := by
    apply Subtype.ext
    exact map_smul (derivedQuotientMap (R := R) f) r a.1

/-- Naturality of the kernel transport in the Hopf proof. -/
theorem reducedBracketKernelEquivDerivedEvaluationKernel_natural
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    (reducedBracketKernelEquivDerivedEvaluationKernel R Y q hq).toLinearMap.comp
        (reducedBracketKernelMap (R := R) (L := L) (K := M) f.base) =
      (derivedEvaluationKernelMap (R := R) f).comp
        (reducedBracketKernelEquivDerivedEvaluationKernel R X p hp).toLinearMap := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change reducedExteriorEquivDerivedQuotient R Y q hq
      (reducedExteriorMap (R := R) (L := L) (K := M) f.base z.1) =
    derivedQuotientMap (R := R) f
      (reducedExteriorEquivDerivedQuotient R X p hp z.1)
  exact (LinearMap.congr_fun
    (reducedExteriorEquivDerivedQuotient_natural (R := R) f hp hq) z.1).symm

/-- Naturality of the Hopf-multiplier/evaluation-kernel identification. -/
theorem presentationHopfEquivDerivedEvaluationKernel_natural :
    (presentationHopfEquivDerivedEvaluationKernel R Y q).toLinearMap.comp
        (hopfMap (R := R) f) =
      (derivedEvaluationKernelMap (R := R) f).comp
        (presentationHopfEquivDerivedEvaluationKernel R X p).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      change presentationHopfEquivDerivedEvaluationKernel R Y q
          (Submodule.Quotient.mk (numeratorMap (R := R) f z)) =
        derivedEvaluationKernelMap (R := R) f
          (presentationHopfEquivDerivedEvaluationKernel R X p
            (Submodule.Quotient.mk z))
      rw [
        presentationHopfEquivDerivedEvaluationKernel_mk,
        presentationHopfEquivDerivedEvaluationKernel_mk]
      apply Subtype.ext
      rfl

set_option maxHeartbeats 1000000 in
-- The final statement composes the four quotient-and-kernel equivalences proved above.
set_option synthInstance.maxHeartbeats 100000 in
-- Typeclass synthesis must unfold the concrete cycles-and-boundaries quotient in two universes.
/-- Naturality of the Chevalley--Eilenberg Hopf formula. -/
theorem secondHomologyHopfEquiv_natural
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    (secondHomologyHopfEquiv R Y q hq).toLinearMap.comp
        (secondHomologyMap f.base) =
      (hopfMap (R := R) f).comp
        (secondHomologyHopfEquiv R X p hp).toLinearMap := by
  apply LinearMap.ext
  intro z
  change secondHomologyHopfEquiv R Y q hq (secondHomologyMap f.base z) =
    hopfMap (R := R) f (secondHomologyHopfEquiv R X p hp z)
  apply (presentationHopfEquivDerivedEvaluationKernel R Y q).injective
  simp only [secondHomologyHopfEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [show secondHomologyEquivReducedBracketKernel R M
        (secondHomologyMap f.base z) =
      reducedBracketKernelMap (R := R) (L := L) (K := M) f.base
        (secondHomologyEquivReducedBracketKernel R L z) from
    LinearMap.congr_fun
      (secondHomologyEquivReducedBracketKernel_natural R f.base) z]
  rw [show reducedBracketKernelEquivDerivedEvaluationKernel R Y q hq
        (reducedBracketKernelMap (R := R) (L := L) (K := M) f.base
          (secondHomologyEquivReducedBracketKernel R L z)) =
      derivedEvaluationKernelMap (R := R) f
        (reducedBracketKernelEquivDerivedEvaluationKernel R X p hp
          (secondHomologyEquivReducedBracketKernel R L z)) from
    LinearMap.congr_fun
      (reducedBracketKernelEquivDerivedEvaluationKernel_natural (R := R) f hp hq)
      (secondHomologyEquivReducedBracketKernel R L z)]
  rw [show presentationHopfEquivDerivedEvaluationKernel R Y q
        (hopfMap (R := R) f
          ((presentationHopfEquivDerivedEvaluationKernel R X p).symm
            (reducedBracketKernelEquivDerivedEvaluationKernel R X p hp
              (secondHomologyEquivReducedBracketKernel R L z)))) =
      derivedEvaluationKernelMap (R := R) f
        (presentationHopfEquivDerivedEvaluationKernel R X p
          ((presentationHopfEquivDerivedEvaluationKernel R X p).symm
            (reducedBracketKernelEquivDerivedEvaluationKernel R X p hp
              (secondHomologyEquivReducedBracketKernel R L z)))) from
    LinearMap.congr_fun
      (presentationHopfEquivDerivedEvaluationKernel_natural (R := R) f)
      ((presentationHopfEquivDerivedEvaluationKernel R X p).symm
        (reducedBracketKernelEquivDerivedEvaluationKernel R X p hp
          (secondHomologyEquivReducedBracketKernel R L z)))]
  rw [(presentationHopfEquivDerivedEvaluationKernel R X p).apply_symm_apply]

end PresentationHom

end

end LieRings.Homological.LieHomology
