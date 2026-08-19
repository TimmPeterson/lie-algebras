import LieRings.DimensionSubring.MetabelianVanishing.RelationSubsetTailCorrection

/-!
# The unbracketed exceptional row sees only its grouped Smith head

After subset collection, the sole exceptional row has the form
`x₁ ... xᵣ ρ`, where the spectator word is ordered and `r ≥ 2`, while `ρ`
is a triangular relation beginning in weight one.  The higher triangular
tail begins in weight two.  Since all positive-weight adapted factors commute
in the metabelian free model, appending such a tail to an ordered word cannot
create a factor-two or factor-one PBW term.  Consequently both reads needed
by the terminal ledger depend only on the complete, grouped Smith head.

The Smith diagonal remains inside the homogeneous head throughout; no
coordinate of that head is promoted to a relation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance exceptionalUnbracketedHeadFintype : Fintype L :=
  Fintype.ofFinite L

/-- The grouped weight-one Smith head of a zero-leading triangular relation. -/
def triangularRelationZeroHead
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0) :
    FreeModel n L :=
  FreeMetabelian.Free.weightIncl 0 (by omega)
    (((triangularSmith n L data 0 (by omega)).diagonal i : ℤ) •
      triangularPieceBasis n L data 0 (by omega) i)

/-- The factor-two read of the exceptional unbracketed row is exactly the
read of its grouped weight-one Smith head. -/
theorem rightSymbol_basisWord_mul_iota_triangularRelation_zero_eq_head
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·))
    (hlen : 2 ≤ xs.length) :
    rightSymbol n L data hn 2 n (by omega)
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationOfIndex n L data
              (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
                TriangularRelationIndex n L) : FreeModel n L)) =
      rightSymbol n L data hn 2 n (by omega)
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationZeroHead n L data hn i)) := by
  let tag : TriangularRelationIndex n L :=
    ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
  have htail : triangularRelationTail n L data tag ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
    simpa [tag] using triangularRelationTail_mem_tail_succ n L data tag
  have htailSymbol : fullRightSymbol n L data hn 2
      (MarkedRow.basisWord n L data hn xs *
        UniversalEnvelopingAlgebra.ι ℤ
          (triangularRelationTail n L data tag)) = 0 := by
    apply fullRightSymbol_basisWord_mul_iota_of_mem_tail_one_eq_zero
      n L data hn 2 (triangularRelationTail n L data tag) xs
        hordered htail
    omega
  rw [show triangularRelationOfIndex n L data tag =
      triangularRelationZeroHead n L data hn i +
        triangularRelationTail n L data tag by
    simpa [tag, triangularRelationZeroHead] using
      triangularRelation_eq_head_add_tail n L data tag]
  rw [map_add, mul_add, map_add]
  change _ + SymmetricPower.map (R := ℤ) (prLE n L n (by omega))
      (fullRightSymbol n L data hn 2
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationTail n L data tag))) = _
  rw [htailSymbol, map_zero, add_zero]

/-- The complete factor-one primitive of the same row likewise depends only
on the grouped weight-one Smith head. -/
theorem pbwPrimitive_basisWord_mul_iota_triangularRelation_zero_eq_head
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·))
    (hlen : 2 ≤ xs.length) :
    pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationOfIndex n L data
              (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
                TriangularRelationIndex n L) : FreeModel n L)) =
      pbwPrimitive n L data hn
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationZeroHead n L data hn i)) := by
  let tag : TriangularRelationIndex n L :=
    ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
  have htail : triangularRelationTail n L data tag ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
    simpa [tag] using triangularRelationTail_mem_tail_succ n L data tag
  have htailPrimitive : pbwPrimitive n L data hn
      (MarkedRow.basisWord n L data hn xs *
        UniversalEnvelopingAlgebra.ι ℤ
          (triangularRelationTail n L data tag)) = 0 := by
    change (SymmetricPower.degreeOneLinearEquiv
        (adaptedBasis n L data hn))
      (fullRightSymbol n L data hn 1
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ
            (triangularRelationTail n L data tag))) = 0
    rw [fullRightSymbol_basisWord_mul_iota_of_mem_tail_one_eq_zero
      n L data hn 1 (triangularRelationTail n L data tag) xs
        hordered htail (by omega), map_zero]
  rw [show triangularRelationOfIndex n L data tag =
      triangularRelationZeroHead n L data hn i +
        triangularRelationTail n L data tag by
    simpa [tag, triangularRelationZeroHead] using
      triangularRelation_eq_head_add_tail n L data tag]
  rw [map_add, mul_add, map_add, htailPrimitive, add_zero]

end

end LieRings.MetabelianVanishing
