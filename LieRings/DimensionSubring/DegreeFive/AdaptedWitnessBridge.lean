import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedWitness
import LieRings.DimensionSubring.DegreeFive.PlacedLedger

/-!
# From the canonical dimension-five witness to the adapted collector

This file only flattens the already finite relation/word expansion.  It introduces no
presentation hypothesis and changes no packet value.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L] [Finite L]

local notation "F" => CanonicalFreeLie L
local notation "Rel" => CanonicalLieRelationsIdeal L
local notation "ev" => canonicalFreeLieEvaluation L

namespace FinitePlacedRelationLedger

private theorem flattenWordSum_evaluate
    (p : Rel × UEA ℤ F) (n : ℤ) (c : FreeMonoid L →₀ ℤ) :
    (c.sum fun word m ↦
        Finsupp.single (p.1, FreeMonoid.toList word) (n * m)).sum
      (fun p n ↦ n •
        (UniversalEnvelopingAlgebra.ι ℤ (p.1 : F) *
          envelopingWord ℤ F (p.2.map (FreeLieAlgebra.of ℤ)))) =
      n • c.sum (fun word m ↦ m •
        AlgebraPacket.value ℤ F Rel (initialAlgebraPacket p word)) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add word m c hword hm ih =>
      rw [Finsupp.sum_add_index
        (fun _ _ ↦ by simp)
        (fun _ _ b₁ b₂ ↦ by rw [mul_add, Finsupp.single_add])]
      rw [Finsupp.sum_add_index
        (fun _ _ ↦ by simp)
        (fun a _ b₁ b₂ ↦ add_zsmul _ b₁ b₂)]
      rw [ih, Finsupp.sum_add_index
        (fun _ _ ↦ by simp)
        (fun a _ b₁ b₂ ↦ add_zsmul _ b₁ b₂)]
      simp [initialAlgebraPacket, AlgebraPacket.value, smul_smul]
      noncomm_ring

set_option maxHeartbeats 1000000 in
/-- Flatten the two finite sums (relations, then associative words) into precisely the input
type expected by the adapted collector. -/
def adaptedRelationWords {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    (LinearMap.ker (canonicalFreeLieEvaluation L).toLinearMap × List L) →₀ ℤ :=
  ledger.lowWeight.coefficients.sum fun p n ↦
    (placedWordCoefficients p).sum fun word m ↦
      Finsupp.single (p.1, FreeMonoid.toList word) (n * m)

/-- Evaluation of the flattened family is the original marked relation sum. -/
theorem adaptedRelationWords_evaluate
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    ledger.adaptedRelationWords.sum (fun p n ↦ n •
      (UniversalEnvelopingAlgebra.ι ℤ (p.1 : F) *
        envelopingWord ℤ F (p.2.map (FreeLieAlgebra.of ℤ)))) =
      ledger.initialPacketValue := by
  classical
  unfold adaptedRelationWords initialPacketValue
  rw [Finsupp.sum_sum_index (fun _ ↦ by simp)
    (fun _ a b ↦ add_zsmul _ a b)]
  apply Finsupp.sum_congr
  intro p hp
  exact flattenWordSum_evaluate p (ledger.lowWeight.coefficients p)
    (placedWordCoefficients p)

/-- The adapted placed collector therefore applies directly to every canonical witness whose
free Lie lift has already been chosen in `γ₃`. -/
def toAdaptedPresentationDimensionFiveWitness
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w)
    (hlift : w.lieLift ∈ lowerCentralSeries ℤ F 2) :
    AdaptedPresentationDimensionFiveWitness L L ev a where
  lieLift := w.lieLift
  highWord := w.highWord
  evaluates := w.evaluates
  lieLift_mem_gammaThree := hlift
  highWord_mem := w.highWord_mem
  relationWords := ledger.adaptedRelationWords
  relationEquation := by
    rw [ledger.adaptedRelationWords_evaluate,
      ledger.initialPacketValue_eq_relationDifference]

end FinitePlacedRelationLedger

/-- Every element of `δ₅` has a genuine adapted-presentation witness, with no additional
coordinate or collection assumption. -/
theorem exists_adaptedPresentationDimensionFiveWitness
    (a : L) (ha : a ∈ dimensionSubring ℤ L 5) :
    Nonempty (AdaptedPresentationDimensionFiveWitness L L ev a) := by
  obtain ⟨w, hw⟩ := exists_freeDimensionFiveWitness_gammaThree L a ha
  obtain ⟨ledger⟩ := w.exists_finitePlacedRelationLedger
  exact ⟨ledger.toAdaptedPresentationDimensionFiveWitness hw⟩

end

end DegreeFive

end LieRings
