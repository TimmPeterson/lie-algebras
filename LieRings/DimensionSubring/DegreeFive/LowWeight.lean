import LieRings.DimensionSubring.DegreeFive.Witness

/-!
# Homogeneous associative components below weight five

The PBW extraction starts in `U(FreeLie(X)) = FreeAlgebra(X)`.  This file supplies the
coordinate-free bookkeeping for its ordinary word-length grading.  In particular, a word in
the fifth augmentation power has zero components in lengths `0, …, 4`.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u)

local notation "A" => FreeAlgebra ℤ X
local notation "MA" => MonoidAlgebra ℤ (FreeMonoid X)

/-- Projection of a monoid polynomial onto words of one fixed length. -/
def monoidLengthComponent (n : ℕ) : MA →ₗ[ℤ] MA where
  toFun p := Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n) p
  map_add' p q := by
    ext w
    by_cases h : w.length = n <;> simp [h]
  map_smul' a p := by
    exact Finsupp.filter_smul

/-- Projection of a free associative polynomial onto words of one fixed length. -/
def associativeLengthComponent (n : ℕ) : A →ₗ[ℤ] A :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toLinearMap.comp
    ((monoidLengthComponent X n).comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

@[simp]
theorem equiv_associativeLengthComponent (n : ℕ) (p : A) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (associativeLengthComponent X n p) =
      Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n)
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
        (Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n)
          (FreeAlgebra.equivMonoidAlgebraFreeMonoid p))) = _
  exact FreeAlgebra.equivMonoidAlgebraFreeMonoid.apply_symm_apply _

/-- A homogeneous projection is supported in precisely its indicated length. -/
theorem associativeLengthComponent_mem_exact (n : ℕ) (p : A) :
    associativeLengthComponent X n p ∈
      FreeLieDimension.associativeExact X n := by
  intro w hw
  have hnz := Finsupp.mem_support_iff.mp hw
  by_contra hlength
  apply hnz
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (associativeLengthComponent X n p)) w = 0
  rw [equiv_associativeLengthComponent]
  exact Finsupp.filter_apply_neg
    (fun w : FreeMonoid X ↦ w.length = n)
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) hlength

/-- Projection to length `n` vanishes on polynomials of minimum length `m > n`. -/
theorem associativeLengthComponent_eq_zero_of_mem_high
    {m n : ℕ} {p : A}
    (hp : p ∈ FreeLieDimension.associativeHigh X m) (hnm : n < m) :
    associativeLengthComponent X n p = 0 := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  ext w
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (associativeLengthComponent X n p)) w =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid 0) w
  rw [equiv_associativeLengthComponent]
  rw [map_zero]
  change (Finsupp.filter (fun w : FreeMonoid X ↦ w.length = n)
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid p)) w = 0
  by_cases hw : w.length = n
  · rw [Finsupp.filter_apply_pos
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hw]
    by_contra hcoeff
    have hsupport : w ∈
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).support :=
      Finsupp.mem_support_iff.mpr hcoeff
    exact (Nat.not_le_of_gt (hw ▸ hnm)) (hp hsupport)
  · rw [Finsupp.filter_apply_neg
      (p := fun w : FreeMonoid X ↦ w.length = n)
      (f := FreeAlgebra.equivMonoidAlgebraFreeMonoid p) (a := w) hw]

/-- All four positive low components of a fifth-augmentation word vanish. -/
theorem low_components_eq_zero_of_mem_high_five
    {p : A} (hp : p ∈ FreeLieDimension.associativeHigh X 5) :
    associativeLengthComponent X 1 p = 0 ∧
      associativeLengthComponent X 2 p = 0 ∧
      associativeLengthComponent X 3 p = 0 ∧
      associativeLengthComponent X 4 p = 0 := by
  constructor
  · exact associativeLengthComponent_eq_zero_of_mem_high X hp (by omega)
  constructor
  · exact associativeLengthComponent_eq_zero_of_mem_high X hp (by omega)
  constructor
  · exact associativeLengthComponent_eq_zero_of_mem_high X hp (by omega)
  · exact associativeLengthComponent_eq_zero_of_mem_high X hp (by omega)

/-- The high word in a dimension-five witness contributes nothing in associative lengths
one through four. -/
theorem FreeDimensionFiveWitness.low_highWord_components_eq_zero
    {L : Type u} [LieRing L] {a : L} (w : FreeDimensionFiveWitness L a) :
    let t := FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L w.highWord
    associativeLengthComponent L 1 t = 0 ∧
      associativeLengthComponent L 2 t = 0 ∧
      associativeLengthComponent L 3 t = 0 ∧
      associativeLengthComponent L 4 t = 0 := by
  exact low_components_eq_zero_of_mem_high_five L
    w.highWord_mem_associativeHigh

/-- The relation-side element of a free dimension-five witness, transported to the ordinary
free associative algebra. -/
def FreeDimensionFiveWitness.freeRelationDifference
    {L : Type u} [LieRing L] {a : L} (w : FreeDimensionFiveWitness L a) :
    FreeAlgebra ℤ L :=
  FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
    (UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord)

/-- After transport through `U(FreeLie(L)) ≃ FreeAlgebra(L)`, the relation-side witness remains
an actual finite sum with a Lie relation in the marked left position. -/
theorem FreeDimensionFiveWitness.exists_freeAlgebra_relation_finsupp
    {L : Type u} [LieRing L] {a : L} (w : FreeDimensionFiveWitness L a) :
    ∃ c : (CanonicalLieRelationsIdeal L ×
        UEA ℤ (CanonicalFreeLie L)) →₀ ℤ,
      c.sum (fun p n ↦ n •
        (PBW.freeLieToFreeAlgebra ℤ L
            (p.1 : CanonicalFreeLie L) *
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2)) =
        w.freeRelationDifference := by
  obtain ⟨c, hc⟩ := w.exists_relation_finsupp
  refine ⟨c, ?_⟩
  let e := FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
  calc
    _ = e (c.sum (fun p n ↦ n •
          (UniversalEnvelopingAlgebra.ι ℤ
            (p.1 : CanonicalFreeLie L) * p.2))) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro p hp
      calc
        c p • (PBW.freeLieToFreeAlgebra ℤ L
              (p.1 : CanonicalFreeLie L) * e p.2) =
            c p • (e (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie L)) * e p.2) :=
          congrArg (fun z ↦ c p • (z * e p.2))
            (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
              L (p.1 : CanonicalFreeLie L)).symm
        _ = c p • e (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie L) * p.2) :=
          congrArg (fun z ↦ c p • z) (map_mul e _ _).symm
        _ = e (c p • (UniversalEnvelopingAlgebra.ι ℤ
              (p.1 : CanonicalFreeLie L) * p.2)) :=
          (map_zsmul e (c p) _).symm
    _ = e (UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord) :=
      congrArg e hc
    _ = w.freeRelationDifference := rfl

/-- Below length five, the collected relation difference has exactly the same homogeneous
components as the free Lie lift; the augmentation-five comparison word is invisible. -/
theorem FreeDimensionFiveWitness.lengthComponent_freeRelationDifference
    {L : Type u} [LieRing L] {a : L} (w : FreeDimensionFiveWitness L a)
    {n : ℕ} (hn : n < 5) :
    associativeLengthComponent L n w.freeRelationDifference =
      associativeLengthComponent L n
        (PBW.freeLieToFreeAlgebra ℤ L w.lieLift) := by
  have ht : associativeLengthComponent L n
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L w.highWord) = 0 :=
    associativeLengthComponent_eq_zero_of_mem_high L
      w.highWord_mem_associativeHigh hn
  have he := map_sub
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
    (UniversalEnvelopingAlgebra.ι ℤ w.lieLift) w.highWord
  change associativeLengthComponent L n
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
        (UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord)) = _
  calc
    _ = associativeLengthComponent L n
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
            (UniversalEnvelopingAlgebra.ι ℤ w.lieLift) -
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L w.highWord) :=
      congrArg (associativeLengthComponent L n) he
    _ = _ := by
      rw [map_sub, ht, sub_zero]
      exact congrArg (associativeLengthComponent L n)
        (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
          L w.lieLift)

/-- The completely finite input to the placed PBW collector.  It records one tagged relation
sum and the four exact low-weight ledger equations; no congruence modulo a filtration occurs in
the statement. -/
structure LowWeightRelationLedger
    {L : Type u} [LieRing L] {a : L} (w : FreeDimensionFiveWitness L a) where
  coefficients : (CanonicalLieRelationsIdeal L ×
    UEA ℤ (CanonicalFreeLie L)) →₀ ℤ
  collected :
    coefficients.sum (fun p n ↦ n •
      (PBW.freeLieToFreeAlgebra ℤ L (p.1 : CanonicalFreeLie L) *
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2)) =
      w.freeRelationDifference
  component_one :
    associativeLengthComponent L 1
        (coefficients.sum (fun p n ↦ n •
          (PBW.freeLieToFreeAlgebra ℤ L (p.1 : CanonicalFreeLie L) *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2))) =
      associativeLengthComponent L 1
        (PBW.freeLieToFreeAlgebra ℤ L w.lieLift)
  component_two :
    associativeLengthComponent L 2
        (coefficients.sum (fun p n ↦ n •
          (PBW.freeLieToFreeAlgebra ℤ L (p.1 : CanonicalFreeLie L) *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2))) =
      associativeLengthComponent L 2
        (PBW.freeLieToFreeAlgebra ℤ L w.lieLift)
  component_three :
    associativeLengthComponent L 3
        (coefficients.sum (fun p n ↦ n •
          (PBW.freeLieToFreeAlgebra ℤ L (p.1 : CanonicalFreeLie L) *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2))) =
      associativeLengthComponent L 3
        (PBW.freeLieToFreeAlgebra ℤ L w.lieLift)
  component_four :
    associativeLengthComponent L 4
        (coefficients.sum (fun p n ↦ n •
          (PBW.freeLieToFreeAlgebra ℤ L (p.1 : CanonicalFreeLie L) *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2))) =
      associativeLengthComponent L 4
        (PBW.freeLieToFreeAlgebra ℤ L w.lieLift)

/-- Every fifth-dimension witness supplies the finite four-line ledger required by the remaining
placed PBW calculation. -/
theorem FreeDimensionFiveWitness.exists_lowWeightRelationLedger
    {L : Type u} [LieRing L] {a : L} (w : FreeDimensionFiveWitness L a) :
    Nonempty (LowWeightRelationLedger w) := by
  obtain ⟨c, hc⟩ := w.exists_freeAlgebra_relation_finsupp
  refine ⟨⟨c, hc, ?_, ?_, ?_, ?_⟩⟩
  · rw [hc]
    exact w.lengthComponent_freeRelationDifference (by omega)
  · rw [hc]
    exact w.lengthComponent_freeRelationDifference (by omega)
  · rw [hc]
    exact w.lengthComponent_freeRelationDifference (by omega)
  · rw [hc]
    exact w.lengthComponent_freeRelationDifference (by omega)

end

end DegreeFive

end LieRings
