import LieRings.DimensionSubring.MetabelianVanishing.RelationSubsetCorrection

/-!
# The proper-subset part of full-relation collection

The subset collector for `rho * x₁ * ⋯ * xᵣ` has one distinguished
unbracketed output, namely `x₁ * ⋯ * xᵣ * rho`.  Every other output
contains at least one bracket with `rho`, and its relation label consequently
lies in the positive-weight tail.  This file separates those proper-subset
outputs and realizes their complete factor-two and primitive reads by genuine
terminal Koszul chains.

No hypothesis on the weight-one component of `rho` is used.  Thus the sole
term left for the exceptional all-weight-one calculation is the distinguished
unbracketed row itself.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance relationSubsetTailCorrectionFintype : Fintype L :=
  Fintype.ofFinite L

/-- The proper-subset outputs of the literal subset collection.  Defining
this recursively, rather than filtering the completed list by equality,
retains the occurrence-level distinction even if two algebraic row values
happen to coincide. -/
def relationSubsetTailCollection
    (rho : Relations n L data) :
    List (AdaptedIndex n L data hn) →
      List (RelationRightRow n L data hn)
  | [] => []
  | x :: xs =>
      (relationSubsetTailCollection rho xs).map
          (fun r ↦ ⟨r.relation, x :: r.ordinary⟩) ++
        relationSubsetCollection n L data hn
          (relationRightBracket n L data hn rho x) xs

/-- The complete subset collection is its unique unbracketed row followed by
the proper-subset outputs. -/
theorem relationSubsetCollection_eq_unbracketed_cons_tail
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn)) :
    relationSubsetCollection n L data hn rho xs =
      ⟨rho, xs⟩ :: relationSubsetTailCollection n L data hn rho xs := by
  induction xs generalizing rho with
  | nil => rfl
  | cons x xs ih =>
      rw [relationSubsetCollection, ih]
      simp only [List.map_cons, List.cons_append,
        relationSubsetTailCollection]

/-- Every ordinary word occurring in the subset collection is a sublist of
the original ordered spectator word. -/
theorem relationSubsetCollection_ordinary_sublist
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (r : RelationRightRow n L data hn)
    (hr : r ∈ relationSubsetCollection n L data hn rho xs) :
    r.ordinary.Sublist xs := by
  induction xs generalizing rho r with
  | nil =>
      simp only [relationSubsetCollection, List.mem_singleton] at hr
      subst r
      exact List.Sublist.refl []
  | cons x xs ih =>
      rw [relationSubsetCollection, List.mem_append] at hr
      rcases hr with hr | hr
      · rw [List.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        exact (ih rho s hs).cons_cons x
      · exact List.sublist_cons_of_sublist x
          (ih (relationRightBracket n L data hn rho x) r hr)

/-- Bracketing an arbitrary full relation on the right by one positive-weight
homogeneous basis vector removes its weight-one coordinate. -/
theorem relationRightBracket_mem_tail_one_unconditionally
    (rho : Relations n L data)
    (x : AdaptedIndex n L data hn) :
    ((relationRightBracket n L data hn rho x : Relations n L data) :
        FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  have hzero : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 0 := by
    rw [FreeMetabelian.Free.mem_tail_iff]
    intro i hi
    omega
  have hbracket := RelationContext.bracket_weightIncl_right_mem_tail n L
    (rho : FreeModel n L) 0 x.1.val x.1.isLt hzero
    (pieceAdaptedBasis n L data hn x.1 x.2)
  rw [FreeMetabelian.Free.mem_tail_iff] at hbracket ⊢
  intro i hi
  change ⁅(rho : FreeModel n L), adaptedBasis n L data hn x⁆ i = 0
  rw [adaptedBasis_apply]
  exact hbracket i (by omega)

/-- Every proper-subset output carries a genuine full relation in the
positive-weight tail. -/
theorem relationSubsetTailCollection_relation_mem_tail_one
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (r : RelationRightRow n L data hn)
    (hr : r ∈ relationSubsetTailCollection n L data hn rho xs) :
    ((r.relation : Relations n L data) : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  induction xs generalizing rho r with
  | nil => simp [relationSubsetTailCollection] at hr
  | cons x xs ih =>
      rw [relationSubsetTailCollection, List.mem_append] at hr
      rcases hr with hr | hr
      · rw [List.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        exact ih rho s hs
      · exact (relationSubsetCollection_invariants n L data hn
          (relationRightBracket n L data hn rho x) xs
          (relationRightBracket_mem_tail_one_unconditionally
            n L data hn rho x) r hr).2

/-- Every proper-subset ordinary word inherits ordering from the original
spectator word. -/
theorem relationSubsetTailCollection_ordinary_pairwise
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·))
    (r : RelationRightRow n L data hn)
    (hr : r ∈ relationSubsetTailCollection n L data hn rho xs) :
    r.ordinary.Pairwise (· ≤ ·) := by
  have hsub : r.ordinary.Sublist xs := by
    apply relationSubsetCollection_ordinary_sublist n L data hn rho xs r
    rw [relationSubsetCollection_eq_unbracketed_cons_tail]
    exact List.mem_cons_of_mem _ hr
  exact hordered.sublist hsub

/-- Aggregate terminal chain for all proper-subset outputs. -/
def relationSubsetTailFactorTwoChain
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn)) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  ((relationSubsetTailCollection n L data hn rho xs).map
    (fun r ↦ r.factorTwoChain n L data hn)).sum

/-- Aggregate source-placement error of the same proper-subset outputs. -/
def relationSubsetTailPrimitiveError
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn)) : Relations n L data :=
  ((relationSubsetTailCollection n L data hn rho xs).map
    (fun r ↦ r.primitiveError n L data hn)).sum

/-- The proper-subset chain realizes the complete factor-two symbol of the
proper-subset row values. -/
theorem dOne_relationSubsetTailFactorTwoChain
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·)) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (relationSubsetTailFactorTwoChain n L data hn rho xs) =
      rightSymbol n L data hn 2 n (by omega)
        (((relationSubsetTailCollection n L data hn rho xs).map
          (RelationRightRow.value n L data hn)).sum) := by
  classical
  let rows := relationSubsetTailCollection n L data hn rho xs
  have hrow (r : RelationRightRow n L data hn) (hr : r ∈ rows) :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (r.factorTwoChain n L data hn) =
        rightSymbol n L data hn 2 n (by omega)
          (r.value n L data hn) := by
    apply relationRightRow_factorTwoChain_boundary n L data hn r
    · exact relationSubsetTailCollection_ordinary_pairwise
        n L data hn rho xs hordered r hr
    · exact relationSubsetTailCollection_relation_mem_tail_one
        n L data hn rho xs r hr
  calc
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (relationSubsetTailFactorTwoChain n L data hn rho xs) =
      (rows.map (fun r ↦ Koszul.dOne
        (terminalSourcePresentation n L data hn) 1
          (r.factorTwoChain n L data hn))).sum := by
            rw [relationSubsetTailFactorTwoChain, map_list_sum]
            dsimp only [rows]
            rw [List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro r hr
            rfl
    _ = (rows.map (fun r ↦ rightSymbol n L data hn 2 n (by omega)
          (r.value n L data hn))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro r hr
            exact hrow r hr
    _ = rightSymbol n L data hn 2 n (by omega)
        ((rows.map (RelationRightRow.value n L data hn)).sum) := by
          rw [map_list_sum, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r hr
          rfl

/-- The source primitive of the proper-subset chain is the PBW primitive of
the same complete row sum, up to one explicitly grouped full relation. -/
theorem terminalSourcePrimitive_relationSubsetTailFactorTwoChain
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·)) :
    terminalSourcePrimitive n L data hn
        (relationSubsetTailFactorTwoChain n L data hn rho xs) =
      pbwPrimitive n L data hn
          (((relationSubsetTailCollection n L data hn rho xs).map
            (RelationRightRow.value n L data hn)).sum) +
        (relationSubsetTailPrimitiveError n L data hn rho xs :
          FreeModel n L) := by
  classical
  let rows := relationSubsetTailCollection n L data hn rho xs
  have hrow (r : RelationRightRow n L data hn) (hr : r ∈ rows) :
      terminalSourcePrimitive n L data hn
          (r.factorTwoChain n L data hn) =
        pbwPrimitive n L data hn (r.value n L data hn) +
          (r.primitiveError n L data hn : FreeModel n L) := by
    apply relationRightRow_factorTwoChain_primitive n L data hn r
    · exact relationSubsetTailCollection_ordinary_pairwise
        n L data hn rho xs hordered r hr
    · exact relationSubsetTailCollection_relation_mem_tail_one
        n L data hn rho xs r hr
  calc
    terminalSourcePrimitive n L data hn
        (relationSubsetTailFactorTwoChain n L data hn rho xs) =
      (rows.map (fun r ↦ terminalSourcePrimitive n L data hn
        (r.factorTwoChain n L data hn))).sum := by
          rw [relationSubsetTailFactorTwoChain, map_list_sum]
          dsimp only [rows]
          rw [List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r hr
          rfl
    _ = (rows.map (fun r ↦
        pbwPrimitive n L data hn (r.value n L data hn) +
          (r.primitiveError n L data hn : FreeModel n L))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro r hr
            exact hrow r hr
    _ = (rows.map (fun r ↦
          pbwPrimitive n L data hn (r.value n L data hn))).sum +
        (rows.map (fun r ↦
          (r.primitiveError n L data hn : FreeModel n L))).sum := by
            induction rows with
            | nil => simp
            | cons r rows ih => simp [add_assoc, add_left_comm, add_comm]
    _ = pbwPrimitive n L data hn
          ((rows.map (RelationRightRow.value n L data hn)).sum) +
        ((rows.map (fun r ↦ r.primitiveError n L data hn)).sum :
          Relations n L data) := by
            congr 1
            · rw [map_list_sum, List.map_map]
              apply congrArg List.sum
              apply List.map_congr_left
              intro r hr
              rfl
            · change (rows.map (fun r ↦
                  ((r.primitiveError n L data hn : Relations n L data) :
                    FreeModel n L))).sum =
                (Relations n L data).subtype
                  ((rows.map (fun r ↦
                    r.primitiveError n L data hn)).sum)
              rw [map_list_sum, List.map_map]
              apply congrArg List.sum
              apply List.map_congr_left
              intro r hr
              rfl
    _ = _ := rfl

/-- Value-level isolation of the exceptional unbracketed row. -/
theorem relationSubsetCollection_value_eq_unbracketed_add_tail
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn)) :
    ((relationSubsetCollection n L data hn rho xs).map
        (RelationRightRow.value n L data hn)).sum =
      (RelationRightRow.value n L data hn ⟨rho, xs⟩) +
        ((relationSubsetTailCollection n L data hn rho xs).map
          (RelationRightRow.value n L data hn)).sum := by
  rw [relationSubsetCollection_eq_unbracketed_cons_tail]
  rfl

end

end LieRings.MetabelianVanishing
