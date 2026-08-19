import LieRings.DimensionSubring.MetabelianVanishing.QuadraticCharacter
import LieRings.DimensionSubring.DegreeFive.AdaptedSmith

/-!
# Homogeneous Smith bases for triangular relation rows

This module is deliberately earlier than the PBW witness.  In particular,
the weight-one ambient basis chosen here is the basis used by the global PBW
collection.  The terminal quadratic presentation keeps its independent
ordered `pSmith` coordinates and is compared to this basis later.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)

local instance triangularBasisFintype : Fintype L := Fintype.ofFinite L

/-- The standard finite basis of the deliberately nonminimal generator
module. -/
def generatorBasis : Module.Basis (Fin (Nat.card L)) ℤ (Generator L) :=
  (Finsupp.basisSingleOne (R := ℤ) (ι := L)).reindex (Finite.equivFin L)

local instance pieceFree (s : ℕ) :
    Module.Free ℤ (FreeMetabelian.Piece (Generator L) s) :=
  Module.Free.of_basis (FreeMetabelian.Free.pieceBasis (generatorBasis L) s)

local instance pieceFinite (s : ℕ) :
    Module.Finite ℤ (FreeMetabelian.Piece (Generator L) s) :=
  Module.Finite.of_basis (FreeMetabelian.Free.pieceBasis (generatorBasis L) s)

/-- Relations whose first possible zero-based homogeneous coordinate is
`s`. -/
def FilteredRelations (s : ℕ) : Submodule ℤ (FreeModel n L) :=
  (Relations n L data).toSubmodule ⊓
    (FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s).toSubmodule

/-- The weight-`s+1` leading terms of relations beginning in that weight. -/
def RelationLeading (s : ℕ) (hs : s < n + 1) :
    Submodule ℤ (FreeMetabelian.Piece (Generator L) s) :=
  (FilteredRelations n L data s).map
    (FreeMetabelian.Free.weightProject s hs)

/-- Multiplication by the cardinality of the finite target lands in the
leading-relation submodule. -/
def cardMultipleToRelationLeading (s : ℕ) (hs : s < n + 1) :
    FreeMetabelian.Piece (Generator L) s →ₗ[ℤ]
      RelationLeading n L data s hs where
  toFun x := by
    let r : FreeModel n L :=
      Nat.card L • FreeMetabelian.Free.weightIncl s hs x
    have hrEval : evaluation n L data r = 0 := by
      dsimp only [r]
      rw [map_nsmul, Nat.card_eq_fintype_card, card_nsmul_eq_zero]
    have hrTail : r ∈
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s := by
      have hx : FreeMetabelian.Free.weightIncl s hs x ∈
          FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) s := by
        change ∀ i : Fin (n + 1), i.val < s →
          FreeMetabelian.Free.incl ⟨s, hs⟩ x i = 0
        intro i hi
        exact FreeMetabelian.Free.incl_apply_of_ne
          ⟨s, hs⟩ i (by
            intro h
            have hval : i.val = s := congrArg Fin.val h
            omega) x
      apply (FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) s).nsmul_mem
      exact hx
    let rf : FilteredRelations n L data s :=
      ⟨r, ⟨hrEval, hrTail⟩⟩
    refine ⟨Nat.card L • x, ⟨rf, rf.property, ?_⟩⟩
    change FreeMetabelian.Free.weightProject s hs r = Nat.card L • x
    dsimp only [r]
    rw [map_nsmul, FreeMetabelian.Free.weightProject_weightIncl]
  map_add' x y := by
    apply Subtype.ext
    change Nat.card L • (x + y) = Nat.card L • x + Nat.card L • y
    exact nsmul_add _ _ _
  map_smul' z x := by
    apply Subtype.ext
    change Nat.card L • (z • x) = z • (Nat.card L • x)
    simp only [← Nat.cast_smul_eq_nsmul ℤ]
    module

theorem cardMultipleToRelationLeading_injective
    (s : ℕ) (hs : s < n + 1) :
    Function.Injective (cardMultipleToRelationLeading n L data s hs) := by
  intro x y hxy
  have hval := congrArg
    (fun z : RelationLeading n L data s hs ↦
      (z : FreeMetabelian.Piece (Generator L) s)) hxy
  simp only [cardMultipleToRelationLeading] at hval
  change Nat.card L • x = Nat.card L • y at hval
  rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ] at hval
  exact smul_right_injective _ (by exact_mod_cast Nat.card_pos.ne') hval

theorem relationLeading_finrank_eq
    (s : ℕ) (hs : s < n + 1) :
    Module.finrank ℤ (RelationLeading n L data s hs) =
      Module.finrank ℤ (FreeMetabelian.Piece (Generator L) s) := by
  apply le_antisymm
  · exact Submodule.finrank_le _
  · exact (cardMultipleToRelationLeading n L data s hs).finrank_le_finrank_of_injective
      (cardMultipleToRelationLeading_injective n L data s hs)

theorem relationLeading_quotient_finite
    (s : ℕ) (hs : s < n + 1) :
    Finite (FreeMetabelian.Piece (Generator L) s ⧸
      RelationLeading n L data s hs) := by
  exact Submodule.finiteQuotientOfFreeOfRankEq
    (RelationLeading n L data s hs)
    (relationLeading_finrank_eq n L data s hs)

/-- Positive Smith data for the leading relations in one weight. -/
def triangularSmith (s : ℕ) (hs : s < n + 1) :
    LieRings.DegreeFive.PositiveSmithPresentation
      (ι := FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s)
      (RelationLeading n L data s hs) :=
  LieRings.DegreeFive.PositiveSmithPresentation.ofFiniteQuotient
    (FreeMetabelian.Free.pieceBasis (generatorBasis L) s)
    (RelationLeading n L data s hs)
    (relationLeading_quotient_finite n L data s hs)

/-- The homogeneous basis used in the triangular row calculation. -/
def triangularPieceBasis (s : ℕ) (hs : s < n + 1) :
    Module.Basis (FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) s) ℤ
      (FreeMetabelian.Piece (Generator L) s) :=
  (triangularSmith n L data s hs).ambientBasis

end

end LieRings.MetabelianVanishing
