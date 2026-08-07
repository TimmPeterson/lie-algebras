import LieRings.DimensionSubring.DegreeFive.WeightedClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.LowSymbolExtraction

/-!
# Weighted extraction from a fifth-dimension ledger

This file connects the explicit weighted PBW representation to the finite free-associative word
expansion.  Its principal result says that an element of associative minimum length `m` has no
class-two PBW symbol below weight `m`.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [LinearOrder X]

local notation "F" => CanonicalFreeLie X
local notation "I" => ClassTwoBasisIndex X
local notation "Poly" => MvPolynomial I ℤ

/-- Expansion of a free enveloping element as its actual finite family of words in the original
free generators. -/
theorem freeEnveloping_eq_generatorWord_sum (u : UEA ℤ F) :
    let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u)
    c.sum (fun w n ↦ n •
      envelopingWord ℤ F
        ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ))) = u := by
  let e := FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
  let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid (e u)
  apply e.injective
  calc
    e (c.sum (fun w n ↦ n •
        envelopingWord ℤ F
          ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ)))) =
        c.sum (fun w n ↦ n • freeAlgebraWord X (FreeMonoid.toList w)) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro w hw
      calc
        e (c w • envelopingWord ℤ F
            ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ))) =
            c w • e (envelopingWord ℤ F
              ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ))) :=
          map_zsmul e (c w) _
        _ = _ := congrArg (c w • ·)
          (universalEnvelopingEquiv_generatorWord X (FreeMonoid.toList w))
    _ = e u := freeAlgebra_eq_word_sum X (e u)

/-- Associative minimum length is preserved as minimum weighted degree by the explicit
class-two PBW symbol. -/
theorem classTwoWeightedComponent_freeEnveloping_eq_zero_of_mem_associativeHigh
    {m n : ℕ} {u : UEA ℤ F}
    (hu : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u ∈
      FreeLieDimension.associativeHigh X m)
    (hnm : n < m) :
    classTwoWeightedComponent X n
      (freeEnvelopingToClassTwoPBWSymbol X u) = 0 := by
  let e := FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
  let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid (e u)
  rw [← freeEnveloping_eq_generatorWord_sum X u]
  rw [map_finsuppSum, map_finsuppSum]
  classical
  apply Finset.sum_eq_zero
  intro w hw
  change classTwoWeightedComponent X n
      (freeEnvelopingToClassTwoPBWSymbol X
        (c w • envelopingWord ℤ F
          ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ)))) = 0
  rw [map_zsmul, map_zsmul]
  have hweight :=
    freeEnvelopingToClassTwoPBWSymbol_generatorWord_isWeighted X
      (FreeMonoid.toList w)
  have hlen : (FreeMonoid.toList w).length ≠ n := by
    have hm : m ≤ w.length := hu hw
    simpa using ne_of_gt (hnm.trans_le hm)
  rw [classTwoWeightedComponent_eq_zero_of_isWeighted_of_ne X hweight hlen,
    zsmul_zero]

/-- The augmentation-five comparison term has no class-two PBW components of weights one
through four. -/
theorem FreeDimensionFiveWitness.classTwoPBW_highWord_component_eq_zero
    {L : Type u} [LieRing L] [LinearOrder L]
    {a : L} (w : FreeDimensionFiveWitness L a)
    {n : ℕ} (hn : n < 5) :
    classTwoWeightedComponent L n
      (freeEnvelopingToClassTwoPBWSymbol L w.highWord) = 0 := by
  exact classTwoWeightedComponent_freeEnveloping_eq_zero_of_mem_associativeHigh L
    w.highWord_mem_associativeHigh hn

/-- Every weight below five of the exact semantic ledger is the corresponding weighted PBW
component of the witness's free-Lie lift. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_weightedPBW_sum
    {L : Type u} [LieRing L] [LinearOrder L]
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w)
    {n : ℕ} (hn : n < 5) :
    ledger.semanticNormalForm.sum (fun p c ↦ c •
        classTwoWeightedComponent L n
          (freeEnvelopingToClassTwoPBWSymbol L p.value)) =
      classTwoWeightedComponent L n
        (freeClassTwoPolynomial L (freeClassTwoTruncation L w.lieLift)) := by
  let φ := (classTwoWeightedComponent L n).comp
    (freeEnvelopingToClassTwoPBWSymbol L)
  have hledger := congrArg φ
    ledger.evaluate_semanticNormalForm_eq_relationDifference
  change φ ((semanticPacketCollector L).evaluate ledger.semanticNormalForm) =
    φ (UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord) at hledger
  rw [map_sub] at hledger
  change classTwoWeightedComponent L n
      (freeEnvelopingToClassTwoPBWSymbol L
        ((semanticPacketCollector L).evaluate ledger.semanticNormalForm)) =
    classTwoWeightedComponent L n
        (freeEnvelopingToClassTwoPBWSymbol L
          (UniversalEnvelopingAlgebra.ι ℤ w.lieLift)) -
      classTwoWeightedComponent L n
        (freeEnvelopingToClassTwoPBWSymbol L w.highWord) at hledger
  rw [freeEnvelopingToClassTwoPBWSymbol_iota,
    w.classTwoPBW_highWord_component_eq_zero hn, sub_zero] at hledger
  rw [← hledger]
  change ledger.semanticNormalForm.sum (fun p c ↦ c •
      classTwoWeightedComponent L n
        (freeEnvelopingToClassTwoPBWSymbol L p.value)) =
    classTwoWeightedComponent L n
      (freeEnvelopingToClassTwoPBWSymbol L
        (ledger.semanticNormalForm.sum (fun p c ↦ c • p.value)))
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, map_zsmul]

/-- For the adapted witness whose lift lies in `γ₃`, every weighted PBW component below five
of the collected relation ledger is exactly zero. -/
theorem FinitePlacedRelationLedger.semanticNormalForm_weightedPBW_sum_eq_zero
    {L : Type u} [LieRing L] [LinearOrder L]
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w)
    (hw : w.lieLift ∈ lowerCentralSeries ℤ (CanonicalFreeLie L) 2)
    {n : ℕ} (hn : n < 5) :
    ledger.semanticNormalForm.sum (fun p c ↦ c •
        classTwoWeightedComponent L n
          (freeEnvelopingToClassTwoPBWSymbol L p.value)) = 0 := by
  rw [ledger.semanticNormalForm_weightedPBW_sum hn,
    FreeDimensionFiveWitness.freeClassTwoTruncation_lieLift_eq_zero L w hw,
    map_zero, map_zero]

end

end DegreeFive

end LieRings
