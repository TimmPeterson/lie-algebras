import LieRings.DimensionSubring.DegreeFive.ResolutionCycle
import LieRings.DimensionSubring.DegreeFive.WeightedLedgerExtraction

/-!
# The resolution tensor carried by the placed packet ledger

Only terminal packets with one external factor contribute to the quadratic resolution
boundary.  This file records that extraction directly as a finite `Finsupp` sum.  Packets with
no external factor are scalar relations, while packets with two or more external factors have
PBW polynomial degree at least three.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (L : Type u) [LieRing L]

local notation "F" => CanonicalFreeLie L
local notation "M" => FreeClassTwo (GeneratorModule L)
local notation "Rel₂" => ClassTwoResolutionRelations L

/-- The resolution tensor represented by one terminal packet.  The defining relation is
truncated to the kernel of `M → L/γ₃`, and the unique external factor is truncated to `M`.
All other packet shapes contribute zero. -/
def terminalPacketResolutionTensor (p : FilteredRelationPacket L) : Rel₂ ⊗[ℤ] M :=
  match p.factors with
  | [x] =>
      relationTruncation L (p.relation : CanonicalLieRelations L) ⊗ₜ[ℤ]
        freeClassTwoTruncation L x.value
  | _ => 0

/-- The finite resolution tensor extracted from a collected fifth-dimension ledger. -/
def FinitePlacedRelationLedger.resolutionTensor
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) : Rel₂ ⊗[ℤ] M :=
  ledger.semanticNormalForm.sum fun p n ↦
    n • terminalPacketResolutionTensor L p

/-- Applying the resolution boundary merely forgets the kernel proof on the relation factor. -/
theorem classTwoResolutionBoundary_terminalPacketResolutionTensor
    (p : FilteredRelationPacket L) :
    classTwoResolutionBoundary L (terminalPacketResolutionTensor L p) =
      match p.factors with
      | [x] =>
          (relationTruncation L (p.relation : CanonicalLieRelations L) : M) ⊗ₜ[ℤ]
            freeClassTwoTruncation L x.value
      | _ => 0 := by
  rcases p with ⟨r, s, hs, hr, factors⟩
  cases factors with
  | nil => simp [terminalPacketResolutionTensor]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [terminalPacketResolutionTensor,
            classTwoResolutionBoundary_tmul]
      | cons y ys => simp [terminalPacketResolutionTensor]

/-- Coefficient form of the boundary of the extracted resolution tensor. -/
theorem FinitePlacedRelationLedger.classTwoResolutionBoundary_resolutionTensor
    {a : L} {w : FreeDimensionFiveWitness L a}
    (ledger : FinitePlacedRelationLedger w) :
    classTwoResolutionBoundary L ledger.resolutionTensor =
      ledger.semanticNormalForm.sum (fun p n ↦ n •
        match p.factors with
        | [x] =>
            (relationTruncation L (p.relation : CanonicalLieRelations L) : M) ⊗ₜ[ℤ]
              freeClassTwoTruncation L x.value
        | _ => 0) := by
  unfold FinitePlacedRelationLedger.resolutionTensor
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul,
    classTwoResolutionBoundary_terminalPacketResolutionTensor]

/-- Empty and non-singleton terminal packets contribute no resolution tensor. -/
@[simp]
theorem terminalPacketResolutionTensor_nil
    (r : CanonicalLieRelationsIdeal L) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s) :
    terminalPacketResolutionTensor L
      (FilteredRelationPacket.withFactors L r s hs hr []) = 0 :=
  rfl

@[simp]
theorem terminalPacketResolutionTensor_singleton
    (r : CanonicalLieRelationsIdeal L) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s)
    (x : FilteredLieFactor L) :
    terminalPacketResolutionTensor L
      (FilteredRelationPacket.withFactors L r s hs hr [x]) =
        relationTruncation L (r : CanonicalLieRelations L) ⊗ₜ[ℤ]
          freeClassTwoTruncation L x.value :=
  rfl

@[simp]
theorem terminalPacketResolutionTensor_cons_cons
    (r : CanonicalLieRelationsIdeal L) (s : ℕ) (hs : 0 < s)
    (hr : (r : F) ∈ FreeLieDimension.lieHigh L s)
    (x y : FilteredLieFactor L) (xs : List (FilteredLieFactor L)) :
    terminalPacketResolutionTensor L
      (FilteredRelationPacket.withFactors L r s hs hr (x :: y :: xs)) = 0 :=
  rfl

end

end DegreeFive

end LieRings
