import LieRings.DimensionSubring.MetabelianVanishing.RelationSubsetTailCorrection

/-!
# The exceptional triangular Smith head in top context

For a triangular relation beginning in weight one, a bracket context of
manuscript weight `n` kills the whole higher-weight tail: that tail begins in
zero-based weight one, so the context sends it into the cutoff tail `n + 1`.
Consequently the contextual full relation is literally its Smith head.  This
is the all-weight-one replacement used in the terminal comb calculation.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance exceptionalTriangularCombFintype : Fintype L :=
  Fintype.ofFinite L

/-- A top-weight context sees only the Smith head of a triangular relation
whose leading coordinate is weight one. -/
theorem RelationContext.apply_triangularRelationOfIndex_eq_apply_head
    (tag : TriangularRelationIndex n L)
    (htag : tag.1.val = 0)
    (c : RelationContext n L data hn)
    (hc : RelationContext.weight n L data hn c = n) :
    RelationContext.apply n L data hn c
        (triangularRelationOfIndex n L data tag : FreeModel n L) =
      RelationContext.apply n L data hn c
        (FreeMetabelian.Free.weightIncl tag.1.val tag.1.isLt
          (((triangularSmith n L data tag.1.val tag.1.isLt).diagonal
              tag.2 : ℤ) •
            triangularPieceBasis n L data tag.1.val tag.1.isLt tag.2)) := by
  have htail : triangularRelationTail n L data tag ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
    simpa [htag] using triangularRelationTail_mem_tail_succ n L data tag
  have happly := RelationContext.apply_mem_tail n L data hn c
    (triangularRelationTail n L data tag) 1 htail
  have happlyTop : RelationContext.apply n L data hn c
      (triangularRelationTail n L data tag) ∈
        FreeMetabelian.Free.tail
          (X := Generator L) (c := n + 1) (n + 1) := by
    simpa [hc, Nat.add_comm] using happly
  have hzero : RelationContext.apply n L data hn c
      (triangularRelationTail n L data tag) = 0 := by
    rw [FreeMetabelian.Free.tail_cutoff_eq_bot] at happlyTop
    simpa using happlyTop
  rw [triangularRelation_eq_head_add_tail n L data tag, map_add,
    hzero, add_zero]

/-- The same exceptional top-context identity in the component notation of
the marked ledger.  At mark one, `component` is precisely the contextual
weight-one coordinate, and the full relation may replace it because all
higher coordinates overshoot the class cutoff. -/
theorem RelationContext.apply_triangularRelationOfIndex_eq_component_one
    (tag : TriangularRelationIndex n L)
    (_htag : tag.1.val = 0)
    (c : RelationContext n L data hn)
    (hc : RelationContext.weight n L data hn c = n) :
    RelationContext.apply n L data hn c
        (triangularRelationOfIndex n L data tag : FreeModel n L) =
      RelationContext.component n L data hn c
        (triangularRelationOfIndex n L data tag) ⟨1, by omega⟩ := by
  let k : Fin (n + 2) := ⟨1, by omega⟩
  have hfull := RelationContext.relation_eq_markedPrefix_of_active_top
    n L data hn c (triangularRelationOfIndex n L data tag) k (by
      dsimp only [k]
      omega)
  change RelationContext.apply n L data hn c
      (triangularRelationOfIndex n L data tag : FreeModel n L) =
    RelationContext.apply n L data hn c
      (rowTruncation n L 1 (by omega)
        (triangularRelationOfIndex n L data tag : FreeModel n L)) at hfull
  have hrow := rowTruncation_succ n L 0 (by omega)
    (triangularRelationOfIndex n L data tag : FreeModel n L)
  have hrowZero : rowTruncation n L 0 (by omega)
      (triangularRelationOfIndex n L data tag : FreeModel n L) = 0 :=
    rowTruncation_zero n L hn
      (triangularRelationOfIndex n L data tag : FreeModel n L)
  have hrowOne : rowTruncation n L 1 (by omega)
        (triangularRelationOfIndex n L data tag : FreeModel n L) =
      FreeMetabelian.Free.weightIncl 0 (by omega)
        (FreeMetabelian.Free.weightProject 0 (by omega)
          (triangularRelationOfIndex n L data tag : FreeModel n L)) := by
    calc
      rowTruncation n L 1 (by omega)
          (triangularRelationOfIndex n L data tag : FreeModel n L) =
        rowTruncation n L 0 (by omega)
            (triangularRelationOfIndex n L data tag : FreeModel n L) +
          FreeMetabelian.Free.weightIncl 0 (by omega)
            (FreeMetabelian.Free.weightProject 0 (by omega)
              (triangularRelationOfIndex n L data tag : FreeModel n L)) := by
                simpa only [Nat.zero_add] using hrow
      _ = _ := by rw [hrowZero, zero_add]
  calc
    RelationContext.apply n L data hn c
        (triangularRelationOfIndex n L data tag : FreeModel n L) =
      RelationContext.apply n L data hn c
        (rowTruncation n L 1 (by omega)
          (triangularRelationOfIndex n L data tag : FreeModel n L)) := hfull
    _ = RelationContext.apply n L data hn c
        (FreeMetabelian.Free.weightIncl 0 (by omega)
          (FreeMetabelian.Free.weightProject 0 (by omega)
            (triangularRelationOfIndex n L data tag : FreeModel n L))) := by
          rw [hrowOne]
    _ = RelationContext.component n L data hn c
        (triangularRelationOfIndex n L data tag) k := by
          dsimp only [k]
          rw [RelationContext.component, dif_neg (by simp)]
          rfl

/-- One step below the terminal context, the higher triangular tail need not
vanish in the full free model.  It does, however, begin at zero-based cutoff
`n`, so the terminal presentation prefix `prLE n` sees only the Smith head.
This is the factor-two analogue of
`apply_triangularRelationOfIndex_eq_apply_head`. -/
theorem RelationContext.prLE_apply_triangularRelationOfIndex_eq_apply_head
    (tag : TriangularRelationIndex n L)
    (htag : tag.1.val = 0)
    (c : RelationContext n L data hn)
    (hc : RelationContext.weight n L data hn c = n - 1) :
    prLE n L n (by omega)
        (RelationContext.apply n L data hn c
          (triangularRelationOfIndex n L data tag : FreeModel n L)) =
      prLE n L n (by omega)
        (RelationContext.apply n L data hn c
          (FreeMetabelian.Free.weightIncl tag.1.val tag.1.isLt
            (((triangularSmith n L data tag.1.val tag.1.isLt).diagonal
                tag.2 : ℤ) •
              triangularPieceBasis n L data tag.1.val tag.1.isLt tag.2))) := by
  have htail : triangularRelationTail n L data tag ∈
      FreeMetabelian.Free.tail
        (X := Generator L) (c := n + 1) 1 := by
    simpa [htag] using triangularRelationTail_mem_tail_succ n L data tag
  have happly := RelationContext.apply_mem_tail n L data hn c
    (triangularRelationTail n L data tag) 1 htail
  have happlyN : RelationContext.apply n L data hn c
      (triangularRelationTail n L data tag) ∈
        FreeMetabelian.Free.tail
          (X := Generator L) (c := n + 1) n := by
    have hnpos : 0 < n := by omega
    simpa [hc, Nat.add_sub_of_le hnpos] using happly
  have hproject : prLE n L n (by omega)
      (RelationContext.apply n L data hn c
        (triangularRelationTail n L data tag)) = 0 := by
    funext i
    change RelationContext.apply n L data hn c
      (triangularRelationTail n L data tag)
        ⟨i.val, i.isLt.trans_le (by omega)⟩ = 0
    exact happlyN ⟨i.val, i.isLt.trans_le (by omega)⟩ i.isLt
  rw [triangularRelation_eq_head_add_tail n L data tag, map_add,
    map_add, hproject, add_zero]

/-- Coordinate-free Smith-head form of the preceding prefix identity.

For a triangular relation whose leading weight is one, the head is a single
vector of the adapted weight-one Smith basis, multiplied by its Smith
diagonal.  Keeping that scalar inside the contextual full relation is the
grouped form needed by the terminal insertion comb: subsequent PBW coordinate
expansions must not duplicate the full relation once per coordinate. -/
theorem RelationContext.prLE_apply_triangularRelation_zero_eq_diagonal_smul
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0)
    (c : RelationContext n L data hn)
    (hc : RelationContext.weight n L data hn c = n - 1) :
    prLE n L n (by omega)
        (RelationContext.apply n L data hn c
          (triangularRelationOfIndex n L data
            (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
              TriangularRelationIndex n L) : FreeModel n L)) =
      ((triangularSmith n L data 0 (by omega)).diagonal i : ℤ) •
        prLE n L n (by omega)
          (RelationContext.apply n L data hn c
            (adaptedBasis n L data hn
              (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
                AdaptedIndex n L data hn))) := by
  rw [RelationContext.prLE_apply_triangularRelationOfIndex_eq_apply_head
    n L data hn
      (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
        TriangularRelationIndex n L) (by simp) c hc]
  rw [adaptedBasis_apply, map_zsmul, map_zsmul]
  congr 2

end

end LieRings.MetabelianVanishing
