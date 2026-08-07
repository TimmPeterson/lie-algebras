import LieRings.DimensionSubring.DegreeFive.WordExpansion

/-!
# A genuinely finite placed-word ledger

The low-weight ledger initially has arbitrary elements of the enveloping algebra on the
right of each marked relation.  This file makes the input to collection completely discrete:
each right factor is replaced by a finitely supported integral family of generator words.
The relation tag is retained throughout.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L]

local notation "F" => CanonicalFreeLie L
local notation "Rel" => CanonicalLieRelationsIdeal L

/-- The initial marked packet attached to a relation term and a generator word. -/
def initialAlgebraPacket
    (p : Rel × UEA ℤ F) (word : FreeMonoid L) :
    AlgebraPacket ℤ F Rel where
  left := []
  relation := p.1
  right := (FreeMonoid.toList word).map (FreeLieAlgebra.of ℤ)

/-- Under `U(FreeLie(L)) ≃ FreeAlgebra(L)`, an enveloping word in the free generators is the
corresponding free-associative word. -/
theorem universalEnvelopingEquiv_envelopingWord_of (xs : List L) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
        (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ))) =
      freeAlgebraWord L xs := by
  induction xs with
  | nil =>
      exact map_one
        (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L)
  | cons x xs ih =>
      simp only [List.map_cons, envelopingWord_cons, freeAlgebraWord_cons]
      calc
        _ = FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
              (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)) *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
              (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ))) :=
          map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L) _ _
        _ = PBW.freeLieToFreeAlgebra ℤ L (FreeLieAlgebra.of ℤ x) *
            freeAlgebraWord L xs := by
          exact congrArg₂ (· * ·)
            (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
              L (FreeLieAlgebra.of ℤ x)) ih
        _ = _ := by
          simp [PBW.freeLieToFreeAlgebra]

/-- Evaluation of an initial marked packet agrees exactly with the word term in the finite
placed ledger. -/
theorem universalEnvelopingEquiv_initialAlgebraPacket_value
    (p : Rel × UEA ℤ F) (word : FreeMonoid L) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
        (AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word)) =
      PBW.freeLieToFreeAlgebra ℤ L (p.1 : F) *
        freeAlgebraWord L (FreeMonoid.toList word) := by
  rw [show AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word) =
      UniversalEnvelopingAlgebra.ι ℤ (p.1 : F) *
        envelopingWord ℤ F
          ((FreeMonoid.toList word).map (FreeLieAlgebra.of ℤ)) by
    simp [AlgebraPacket.value, initialAlgebraPacket]]
  calc
    _ = FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
          (UniversalEnvelopingAlgebra.ι ℤ (p.1 : F)) *
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
          (envelopingWord ℤ F
            ((FreeMonoid.toList word).map (FreeLieAlgebra.of ℤ))) :=
      map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L) _ _
    _ = _ := by
      exact congrArg₂ (· * ·)
        (FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra
          L (p.1 : F))
        (universalEnvelopingEquiv_envelopingWord_of
          (L := L) (FreeMonoid.toList word))

/-- Replace a packet's relation by its chosen weight-one-plus-two row. -/
def AlgebraPacket.row (p : AlgebraPacket ℤ F Rel) : AlgebraPacket ℤ F Rel :=
  ⟨p.left, relationIdealRow L p.relation, p.right⟩

/-- The complementary packet has a relation lying in `γ₃` of the free Lie ring. -/
def AlgebraPacket.rowRemainder
    (p : AlgebraPacket ℤ F Rel) : AlgebraPacket ℤ F Rel :=
  ⟨p.left, relationRowRemainder L p.relation, p.right⟩

/-- Exact first row-normalization rewrite for an arbitrary marked packet. -/
theorem AlgebraPacket.value_eq_row_add_rowRemainder
    (p : AlgebraPacket ℤ F Rel) :
    AlgebraPacket.value ℤ F Rel p =
      AlgebraPacket.value ℤ F Rel p.row +
        AlgebraPacket.value ℤ F Rel p.rowRemainder := by
  unfold AlgebraPacket.value AlgebraPacket.row AlgebraPacket.rowRemainder
  rw [relation_eq_row_add_remainder L p.relation, map_add]
  noncomm_ring

/-- The correction relation created by row normalization starts in bracket weight three. -/
theorem AlgebraPacket.rowRemainder_relation_mem_gammaThree
    (p : AlgebraPacket ℤ F Rel) :
    (p.rowRemainder.relation : F) ∈ lowerCentralSeries ℤ F 2 :=
  relationRowRemainder_mem_lowerCentralSeries_two L p.relation

/-- The coefficient family of words chosen for one marked relation term. -/
def placedWordCoefficients
    (p : Rel × UEA ℤ F) : FreeMonoid L →₀ ℤ :=
  Classical.choose (exists_mul_freeAlgebra_word_finsupp L
    (PBW.freeLieToFreeAlgebra ℤ L (p.1 : F))
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2))

/-- The chosen word family evaluates to the original marked relation product. -/
theorem placedWordCoefficients_evaluate
    (p : Rel × UEA ℤ F) :
    (placedWordCoefficients p).sum (fun word n ↦ n •
      (PBW.freeLieToFreeAlgebra ℤ L (p.1 : F) *
        freeAlgebraWord L (FreeMonoid.toList word))) =
      PBW.freeLieToFreeAlgebra ℤ L (p.1 : F) *
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2 :=
  Classical.choose_spec (exists_mul_freeAlgebra_word_finsupp L
    (PBW.freeLieToFreeAlgebra ℤ L (p.1 : F))
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2))

/-- A low-weight ledger together with its finite, relation-tagged word expansion. -/
structure FinitePlacedRelationLedger
    {a : L} (w : FreeDimensionFiveWitness L a) where
  lowWeight : LowWeightRelationLedger w

namespace FinitePlacedRelationLedger

/-- The same nested finite packet sum, evaluated in `U(FreeLie(L))`. -/
def initialPacketValue {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) : UEA ℤ F :=
  ledger.lowWeight.coefficients.sum (fun p n ↦ n •
    (placedWordCoefficients p).sum (fun word m ↦ m •
      AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word)))

/-- The nested finite sum which is fed to the placed collector.  Both levels are `Finsupp`
sums, so this expression contains only finitely many tagged packets. -/
def placedValue {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) : FreeAlgebra ℤ L :=
  ledger.lowWeight.coefficients.sum (fun p n ↦ n •
    (placedWordCoefficients p).sum (fun word m ↦ m •
      (PBW.freeLieToFreeAlgebra ℤ L (p.1 : F) *
        freeAlgebraWord L (FreeMonoid.toList word))))

/-- The free-enveloping and free-associative evaluations of the initial packets agree. -/
theorem universalEnvelopingEquiv_initialPacketValue
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
        ledger.initialPacketValue = ledger.placedValue := by
  let e := FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L
  change e ledger.initialPacketValue = ledger.placedValue
  unfold initialPacketValue placedValue
  calc
    e (ledger.lowWeight.coefficients.sum (fun p n ↦ n •
        (placedWordCoefficients p).sum (fun word m ↦ m •
          AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word)))) =
      ledger.lowWeight.coefficients.sum (fun p n ↦ e (n •
        (placedWordCoefficients p).sum (fun word m ↦ m •
          AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word)))) :=
        map_finsuppSum e ledger.lowWeight.coefficients _
    _ = _ := by
      apply Finsupp.sum_congr
      intro p hp
      calc
        e (ledger.lowWeight.coefficients p •
            (placedWordCoefficients p).sum (fun word m ↦ m •
              AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word))) =
          ledger.lowWeight.coefficients p •
            e ((placedWordCoefficients p).sum (fun word m ↦ m •
              AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word))) :=
            map_zsmul e (ledger.lowWeight.coefficients p) _
        _ = ledger.lowWeight.coefficients p •
            (placedWordCoefficients p).sum (fun word m ↦
              e (m • AlgebraPacket.value ℤ F Rel
                (initialAlgebraPacket p word))) := by
          congr 1
          exact map_finsuppSum e (placedWordCoefficients p) _
        _ = _ := by
          apply congrArg (fun z ↦ ledger.lowWeight.coefficients p • z)
          apply Finsupp.sum_congr
          intro word hword
          exact (map_zsmul e ((placedWordCoefficients p) word)
            (AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word))).trans
              (congrArg (fun z ↦ (placedWordCoefficients p) word • z)
                (universalEnvelopingEquiv_initialAlgebraPacket_value p word))

/-- Expanding all right factors leaves the relation-side value unchanged. -/
theorem placedValue_eq_freeRelationDifference
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    ledger.placedValue = w.freeRelationDifference := by
  calc
    ledger.placedValue =
        ledger.lowWeight.coefficients.sum (fun p n ↦ n •
          (PBW.freeLieToFreeAlgebra ℤ L (p.1 : F) *
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L p.2)) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [placedWordCoefficients_evaluate]
    _ = w.freeRelationDifference := ledger.lowWeight.collected

/-- Exact initial-packet identity back in the enveloping algebra. -/
theorem initialPacketValue_eq_relationDifference
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    ledger.initialPacketValue =
      UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord := by
  apply FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ L |>.injective
  rw [ledger.universalEnvelopingEquiv_initialPacketValue,
    ledger.placedValue_eq_freeRelationDifference]
  rfl

/-- The four exact homogeneous-component equations survive the finite word expansion. -/
theorem component_eq_lieLift
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) {n : ℕ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) :
    associativeLengthComponent L n ledger.placedValue =
      associativeLengthComponent L n
        (PBW.freeLieToFreeAlgebra ℤ L w.lieLift) := by
  rw [ledger.placedValue_eq_freeRelationDifference]
  exact w.lengthComponent_freeRelationDifference (by omega)

end FinitePlacedRelationLedger

/-- Every dimension-five witness has completely finite placed-word collection data. -/
theorem FreeDimensionFiveWitness.exists_finitePlacedRelationLedger
    {a : L} (w : FreeDimensionFiveWitness L a) :
    Nonempty (FinitePlacedRelationLedger w) :=
  w.exists_lowWeightRelationLedger.map FinitePlacedRelationLedger.mk

end

end DegreeFive

end LieRings
