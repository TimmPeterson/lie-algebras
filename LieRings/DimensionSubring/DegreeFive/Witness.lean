import LieRings.DimensionSubring.DegreeFive.PresentationKernel
import LieRings.DimensionSubring.DegreeFive.RelationIdeal
import LieRings.DimensionSubring.DegreeFive.RelationTruncation
import LieRings.DimensionSubring.DegreeThree
import LieRings.DimensionSubring.FreeLie

/-!
# Lifting a fifth-dimension witness to the canonical free presentation

An element of `δ₅(L)` is represented by a free Lie element `f` and an associative word of
augmentation degree at least five. Their difference is a finite sum of products with a defining
Lie relation placed on the left. This is the exact input of the remaining finite PBW collector.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

/-- Free-presentation data attached to an element of the fifth dimension subring. -/
structure FreeDimensionFiveWitness (a : L) where
  lieLift : CanonicalFreeLie L
  highWord : UEA ℤ (CanonicalFreeLie L)
  evaluates : canonicalFreeLieEvaluation L lieLift = a
  highWord_mem : highWord ∈ UEA.augmentationIdeal ℤ (CanonicalFreeLie L) ^ 5
  relationDifference :
    UniversalEnvelopingAlgebra.ι ℤ lieLift - highWord ∈
      rightRelationSpan ℤ (CanonicalFreeLie L) (CanonicalLieRelationsIdeal L)

/-- Every element of `δ₅(L)` has a collected free-presentation witness. -/
theorem exists_freeDimensionFiveWitness (a : L)
    (ha : a ∈ dimensionSubring ℤ L 5) :
    Nonempty (FreeDimensionFiveWitness L a) := by
  have ha' : UniversalEnvelopingAlgebra.ι ℤ a ∈
      UEA.augmentationIdeal ℤ L ^ 5 :=
    (mem_dimensionSubring ℤ L).mp ha
  obtain ⟨t, htHigh, htEval⟩ :=
    UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ
      (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
      (canonicalFreeLieEvaluation_surjective L) 4 ha'
  let f : CanonicalFreeLie L := FreeLieAlgebra.of ℤ a
  have hfEval : canonicalFreeLieEvaluation L f = a :=
    canonicalFreeLieEvaluation_of L a
  have hdiffZero :
      UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
          (UniversalEnvelopingAlgebra.ι ℤ f - t) = 0 := by
    rw [map_sub, UEA.map_ι, hfEval, htEval, sub_self]
  have hdiff :=
    (mem_kernel_canonical_uea_evaluation_iff_relation_sum L
      (UniversalEnvelopingAlgebra.ι ℤ f - t)).mp hdiffZero
  exact ⟨⟨f, t, hfEval, htHigh, hdiff⟩⟩

/-- A fifth-dimension witness may be chosen with its free-Lie lift already in `γ₃`.

This is the form used by the degree-five PBW extraction.  It follows from the previously
proved integral identity `δ₃ = γ₃` and surjectivity of the canonical free presentation;
no finiteness assumption is involved. -/
theorem exists_freeDimensionFiveWitness_gammaThree (a : L)
    (ha : a ∈ dimensionSubring ℤ L 5) :
    ∃ w : FreeDimensionFiveWitness L a,
      w.lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 2 := by
  have haThree : a ∈ dimensionSubring ℤ L 3 :=
    dimensionSubring_antitone ℤ L (by omega) ha
  have haGamma : a ∈ lowerCentralSeries ℤ L 2 := by
    rw [← dimensionSubring_three_eq_lowerCentralSeries_two L]
    exact haThree
  have haMap : a ∈
      (lowerCentralSeries ℤ (CanonicalFreeLie L) 2).map
        (canonicalFreeLieEvaluation L) := by
    rw [LieIdeal.lowerCentralSeries_map_eq 2
      (canonicalFreeLieEvaluation_surjective L)]
    exact haGamma
  obtain ⟨f, hfEval⟩ := LieIdeal.mem_map_of_surjective
    (I := lowerCentralSeries ℤ (CanonicalFreeLie L) 2)
    (canonicalFreeLieEvaluation_surjective L) haMap
  have ha' : UniversalEnvelopingAlgebra.ι ℤ a ∈
      UEA.augmentationIdeal ℤ L ^ 5 :=
    (mem_dimensionSubring ℤ L).mp ha
  obtain ⟨t, htHigh, htEval⟩ :=
    UEA.exists_mem_augmentationIdeal_pow_succ_of_surjective ℤ
      (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
      (canonicalFreeLieEvaluation_surjective L) 4 ha'
  have hdiffZero :
      UEA.map ℤ (CanonicalFreeLie L) L (canonicalFreeLieEvaluation L)
          (UniversalEnvelopingAlgebra.ι ℤ (f : CanonicalFreeLie L) - t) = 0 := by
    rw [map_sub, UEA.map_ι, hfEval, htEval, sub_self]
  have hdiff :=
    (mem_kernel_canonical_uea_evaluation_iff_relation_sum L
      (UniversalEnvelopingAlgebra.ι ℤ (f : CanonicalFreeLie L) - t)).mp hdiffZero
  exact ⟨⟨(f : CanonicalFreeLie L), t, hfEval, htHigh, hdiff⟩, f.property⟩

/-- The class-two truncation of the adapted `γ₃`-witness is zero. -/
theorem FreeDimensionFiveWitness.freeClassTwoTruncation_lieLift_eq_zero
    {a : L} (w : FreeDimensionFiveWitness L a)
    (hw : w.lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 2) :
    freeClassTwoTruncation L w.lieLift = 0 :=
  freeClassTwoTruncation_eq_zero_of_mem_lowerCentralSeries_two L hw

/-- The high word of a free witness has no associative word of length below five. -/
theorem FreeDimensionFiveWitness.highWord_mem_associativeHigh
    {a : L} (w : FreeDimensionFiveWitness L a) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L w.highWord ∈
      FreeLieDimension.associativeHigh L 5 := by
  exact FreeLieDimension.universalEnvelopingEquiv_mem_associativeHigh L 5
    w.highWord_mem

/-- A witness's relation difference comes with a genuinely finite family of tagged relations. -/
theorem FreeDimensionFiveWitness.exists_relation_finsupp
    {a : L} (w : FreeDimensionFiveWitness L a) :
    ∃ c : (CanonicalLieRelationsIdeal L × UEA ℤ (CanonicalFreeLie L)) →₀ ℤ,
      c.sum (fun p n ↦ n •
        (UniversalEnvelopingAlgebra.ι ℤ
          (p.1 : CanonicalFreeLie L) * p.2)) =
        UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord := by
  exact exists_relation_finsupp_of_mem_rightRelationSpan ℤ
    (CanonicalFreeLie L) (CanonicalLieRelationsIdeal L) w.relationDifference

end

end DegreeFive

end LieRings
