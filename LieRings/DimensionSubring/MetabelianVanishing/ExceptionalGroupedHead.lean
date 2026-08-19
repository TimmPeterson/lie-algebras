import LieRings.DimensionSubring.MetabelianVanishing.OrderedPBWPrimitive

/-!
# The grouped weight-one head of an exceptional cell

This file makes the narrow connection between the contextual component row
and the grouped insertion calculation.  It does not assert that an
order-selected part of the triangular head is itself a relation: the entire
Smith head remains the argument of `weightOneRightInsertionPrimitive`.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance exceptionalGroupedHeadFintype : Fintype L :=
  Fintype.ofFinite L

/-- A mark-one hole cell whose root is a zero-based-weight-zero triangular
relation has exactly the grouped Smith-head primitive.  The nonempty word is
returned in cons form so downstream code can apply the insertion formula
without making a second choice. -/
theorem ProvenancedCell.primitive_eq_weightOneRightInsertionPrimitive
    (c : ProvenancedCell n L data hn)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0)
    (hroot : c.root = triangularRelationOfIndex n L data
      (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
        TriangularRelationIndex n L))
    (hmark : c.mark.val = 1)
    (hcontext : c.context = .hole)
    (hordered : c.left.Pairwise (· ≤ ·))
    (hne : c.left ≠ []) :
    ∃ (x : AdaptedIndex n L data hn)
        (xs : List (AdaptedIndex n L data hn)),
      c.left = x :: xs ∧
        c.primitive n L data hn =
          weightOneRightInsertionPrimitive n L data hn x xs
            (((triangularSmith n L data 0 (by omega)).diagonal
                i : ℤ) •
              triangularPieceBasis n L data 0 (by omega) i) := by
  classical
  cases hcword : c.left with
  | nil => exact (hne hcword).elim
  | cons x xs =>
      refine ⟨x, xs, rfl, ?_⟩
      have hmarkEq : c.mark = ⟨1, by omega⟩ := Fin.ext hmark
      have hcomponentWord : c.componentRow.value =
          MarkedRow.basisWord n L data hn (x :: xs) *
            UniversalEnvelopingAlgebra.ι ℤ
              (RelationContext.component n L data hn
                c.context c.root c.mark) := by
        rw [← hcword]
        simp [ProvenancedCell.componentRow, ProvenancedRow.value,
          MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word]
      rw [ProvenancedCell.primitive, hcomponentWord, hcontext, hroot,
        hmarkEq]
      have hhead := triangularRelationOfIndex_head n L data
        ((⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩) :
          TriangularRelationIndex n L)
      simp only at hhead
      rw [RelationContext.component, dif_neg (by simp),
        RelationContext.apply_hole]
      change pbwPrimitive n L data hn
          (MarkedRow.basisWord n L data hn (x :: xs) *
            UniversalEnvelopingAlgebra.ι ℤ
              (FreeMetabelian.Free.weightIncl 0 (by omega)
                (FreeMetabelian.Free.weightProject 0 (by omega)
                  (triangularRelationOfIndex n L data
                    ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
                      FreeModel n L)))) =
        weightOneRightInsertionPrimitive n L data hn x xs
          (((triangularSmith n L data 0 (by omega)).diagonal i : ℤ) •
            triangularPieceBasis n L data 0 (by omega) i)
      rw [hhead]
      apply pbwPrimitive_basisWord_mul_iota_weightOne
        n L data hn x xs
      simpa only [hcword] using hordered

end

end LieRings.MetabelianVanishing
