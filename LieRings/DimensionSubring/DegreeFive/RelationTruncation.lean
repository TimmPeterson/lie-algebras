import LieRings.DimensionSubring.DegreeFive.PresentationResolution

/-!
# Surjectivity of relation truncation

This is the basis-free formalization of the relation-truncation lemma in the invariant proof.
We use the canonical free Lie presentation on the underlying set of `L`.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- The canonical free Lie ring presenting `L`. -/
abbrev CanonicalFreeLie := FreeLieAlgebra ℤ L

/-- Evaluation of the canonical free Lie presentation. -/
def canonicalFreeLieEvaluation : CanonicalFreeLie L →ₗ⁅ℤ⁆ L :=
  FreeLieAlgebra.lift ℤ id

@[simp]
theorem canonicalFreeLieEvaluation_of (x : L) :
    canonicalFreeLieEvaluation L (FreeLieAlgebra.of ℤ x) = x := by
  exact FreeLieAlgebra.lift_of_apply _ _

/-- The canonical free Lie presentation is onto. -/
theorem canonicalFreeLieEvaluation_surjective :
    Function.Surjective (canonicalFreeLieEvaluation L) := by
  intro x
  exact ⟨FreeLieAlgebra.of ℤ x, canonicalFreeLieEvaluation_of L x⟩

/-- Evaluation of the free Abelian generator module. -/
def canonicalGeneratorEvaluation : GeneratorModule L →ₗ[ℤ] L :=
  Finsupp.linearCombination ℤ id

@[simp]
theorem canonicalGeneratorEvaluation_single (x : L) :
    canonicalGeneratorEvaluation L (Finsupp.single x 1) = x := by
  simp [canonicalGeneratorEvaluation]

/-- The canonical class-two presentation map. -/
def canonicalClassTwoEvaluation :
    FreeClassTwo (GeneratorModule L) →ₗ⁅ℤ⁆ ModGammaThree L :=
  freeClassTwoEvaluation (GeneratorModule L) L (canonicalGeneratorEvaluation L)

/-- Evaluation commutes with class-two truncation. -/
theorem canonical_evaluation_comp_truncation :
    (canonicalClassTwoEvaluation L).comp (freeClassTwoTruncation L) =
      (UEA.lieIdealQuotientMk ℤ L (lowerCentralSeries ℤ L 2)).comp
        (canonicalFreeLieEvaluation L) := by
  apply FreeLieAlgebra.hom_ext
  intro x
  change canonicalClassTwoEvaluation L
      (freeClassTwoTruncation L (FreeLieAlgebra.of ℤ x)) =
    LieSubmodule.Quotient.mk (canonicalFreeLieEvaluation L
      (FreeLieAlgebra.of ℤ x))
  rw [freeClassTwoTruncation_of, canonicalFreeLieEvaluation_of]
  rw [show canonicalClassTwoEvaluation L =
      freeClassTwoEvaluation (GeneratorModule L) L
        (canonicalGeneratorEvaluation L) from rfl]
  rw [freeClassTwoEvaluation_apply]
  rw [canonicalGeneratorEvaluation_single, map_zero, add_zero]

/-- Relations of the canonical free Lie presentation. -/
abbrev CanonicalLieRelations :=
  LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap

/-- The kernel in the explicit resolution of `L/γ₃(L)`. -/
abbrev ClassTwoResolutionRelations :=
  LinearMap.ker (canonicalClassTwoEvaluation L).toLinearMap

/-- A free-Lie relation, truncated to weights one and two. -/
def relationTruncation :
    CanonicalLieRelations L →ₗ[ℤ] ClassTwoResolutionRelations L where
  toFun r := ⟨freeClassTwoTruncation L (r : CanonicalFreeLie L), by
    rw [LinearMap.mem_ker]
    have hcomp := LieHom.congr_fun (canonical_evaluation_comp_truncation L)
      (r : CanonicalFreeLie L)
    change canonicalClassTwoEvaluation L (freeClassTwoTruncation L (r : CanonicalFreeLie L)) = 0
    change canonicalClassTwoEvaluation L (freeClassTwoTruncation L (r : CanonicalFreeLie L)) =
      LieSubmodule.Quotient.mk (canonicalFreeLieEvaluation L (r : CanonicalFreeLie L)) at hcomp
    rw [hcomp, show canonicalFreeLieEvaluation L (r : CanonicalFreeLie L) = 0 from r.property]
    rfl⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (freeClassTwoTruncation L)
      (x : CanonicalFreeLie L) (y : CanonicalFreeLie L)
  map_smul' n x := by
    apply Subtype.ext
    exact map_smul (freeClassTwoTruncation L) n (x : CanonicalFreeLie L)

@[simp]
theorem relationTruncation_coe (r : CanonicalLieRelations L) :
    ((relationTruncation L r : ClassTwoResolutionRelations L) :
      FreeClassTwo (GeneratorModule L)) =
      freeClassTwoTruncation L (r : CanonicalFreeLie L) :=
  rfl

/-- The class-two truncation kills `γ₃` of the free Lie ring. -/
theorem freeClassTwoTruncation_eq_zero_of_mem_lowerCentralSeries_two
    {x : CanonicalFreeLie L}
    (hx : x ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 2) :
    freeClassTwoTruncation L x = 0 := by
  have hmem : freeClassTwoTruncation L x ∈
      lowerCentralSeries ℤ (FreeClassTwo (GeneratorModule L)) 2 := by
    change freeClassTwoTruncation L x ∈
      LieModule.lowerCentralSeries ℤ (FreeClassTwo (GeneratorModule L))
        (FreeClassTwo (GeneratorModule L)) 2
    rw [← LieIdeal.lowerCentralSeries_map_eq 2
      (freeClassTwoTruncation_surjective L)]
    exact LieIdeal.mem_map hx
  change freeClassTwoTruncation L x ∈
    LieModule.lowerCentralSeries ℤ (FreeClassTwo (GeneratorModule L))
      (FreeClassTwo (GeneratorModule L)) 2 at hmem
  rw [FreeClassTwo.lowerCentralSeries_two_eq_bot] at hmem
  simpa using hmem

/-- **Relation truncation is surjective.** -/
theorem relationTruncation_surjective :
    Function.Surjective (relationTruncation L) := by
  intro z
  obtain ⟨f, hf⟩ := freeClassTwoTruncation_surjective L (z : FreeClassTwo (GeneratorModule L))
  have hevalGamma : canonicalFreeLieEvaluation L f ∈ lowerCentralSeries ℤ L 2 := by
    have hzker : canonicalClassTwoEvaluation L (z : FreeClassTwo (GeneratorModule L)) = 0 :=
      z.property
    have hcomp := LieHom.congr_fun (canonical_evaluation_comp_truncation L) f
    change canonicalClassTwoEvaluation L (freeClassTwoTruncation L f) =
      (LieSubmodule.Quotient.mk (canonicalFreeLieEvaluation L f) : ModGammaThree L) at hcomp
    rw [hf, hzker] at hcomp
    have hcomp' : (LieSubmodule.Quotient.mk (canonicalFreeLieEvaluation L f) :
        ModGammaThree L) = 0 := hcomp.symm
    exact (LieSubmodule.Quotient.mk_eq_zero'
      (N := lowerCentralSeries ℤ L 2)).mp hcomp'
  have hevalMap : canonicalFreeLieEvaluation L f ∈
      (lowerCentralSeries ℤ (CanonicalFreeLie L) 2).map
        (canonicalFreeLieEvaluation L) := by
    rw [LieIdeal.lowerCentralSeries_map_eq 2
      (canonicalFreeLieEvaluation_surjective L)]
    exact hevalGamma
  obtain ⟨c, hceq⟩ := LieIdeal.mem_map_of_surjective
    (I := lowerCentralSeries ℤ (CanonicalFreeLie L) 2)
    (canonicalFreeLieEvaluation_surjective L) hevalMap
  let r : CanonicalLieRelations L := ⟨f - (c : CanonicalFreeLie L), by
    rw [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr hceq.symm⟩
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change freeClassTwoTruncation L (f - (c : CanonicalFreeLie L)) =
    (z : FreeClassTwo (GeneratorModule L))
  rw [map_sub, freeClassTwoTruncation_eq_zero_of_mem_lowerCentralSeries_two L c.property,
    sub_zero, hf]

end

end DegreeFive

end LieRings
