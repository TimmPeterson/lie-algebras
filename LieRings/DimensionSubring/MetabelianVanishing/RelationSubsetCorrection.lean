import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 2000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

private theorem adaptedIndex_weight_mono
    {i j : AdaptedIndex n L data hn} (hij : i ≤ j) :
    i.1.val ≤ j.1.val := by
  change toLex (i.1.val, i.2.val) ≤ toLex (j.1.val, j.2.val) at hij
  simpa using Prod.Lex.monotone_fst _ _ hij

private theorem adaptedBasis_lie_eq_zero_of_pos
    (i j : AdaptedIndex n L data hn)
    (hi : 0 < i.1.val) (hj : 0 < j.1.val) :
    ⁅adaptedBasis n L data hn i, adaptedBasis n L data hn j⁆ = 0 := by
  rw [adaptedBasis_apply, adaptedBasis_apply]
  exact FreeMetabelian.Free.bracket_weightIncl_eq_zero_of_pos
    i.1.val j.1.val i.1.isLt j.1.isLt hi hj
      ((pieceAdaptedBasis n L data hn i.1) i.2)
      ((pieceAdaptedBasis n L data hn j.1) j.2)

private theorem iota_adaptedBasis_comm_of_pos
    (i j : AdaptedIndex n L data hn)
    (hi : 0 < i.1.val) (hj : 0 < j.1.val) :
    UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) *
        UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn j) =
      UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn j) *
        UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) := by
  have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
    (FreeModel n L) (adaptedBasis n L data hn i)
      (adaptedBasis n L data hn j)
  rw [adaptedBasis_lie_eq_zero_of_pos n L data hn i j hi hj,
    map_zero, add_zero] at hswap
  exact hswap

private theorem basisWord_mul_iota_comm_of_pos
    (i : AdaptedIndex n L data hn) (hi : 0 < i.1.val)
    (xs : List (AdaptedIndex n L data hn))
    (hxs : ∀ j ∈ xs, 0 < j.1.val) :
    MarkedRow.basisWord n L data hn xs *
        UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) =
      UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) *
        MarkedRow.basisWord n L data hn xs := by
  induction xs with
  | nil =>
      simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word]
  | cons x xs ih =>
      have hx : 0 < x.1.val := hxs x (by simp)
      have htail : ∀ j ∈ xs, 0 < j.1.val := by
        intro j hj
        exact hxs j (by simp [hj])
      have hcons : MarkedRow.basisWord n L data hn (x :: xs) =
          UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) *
            MarkedRow.basisWord n L data hn xs := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      rw [hcons]
      calc
        (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) *
              MarkedRow.basisWord n L data hn xs) *
            UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn i) =
          UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) *
            (MarkedRow.basisWord n L data hn xs *
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn i)) := by
                  rw [mul_assoc]
        _ = UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn x) *
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn i) *
              MarkedRow.basisWord n L data hn xs) := by rw [ih htail]
        _ = (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn i) *
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x)) *
            MarkedRow.basisWord n L data hn xs := by
              rw [← mul_assoc, iota_adaptedBasis_comm_of_pos
                n L data hn x i hx hi]
        _ = UniversalEnvelopingAlgebra.ι ℤ
              (adaptedBasis n L data hn i) *
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) *
              MarkedRow.basisWord n L data hn xs) := by rw [mul_assoc]

private theorem basisWord_mul_iota_eq_orderedInsert
    (i : AdaptedIndex n L data hn) (hi : 0 < i.1.val)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·)) :
    MarkedRow.basisWord n L data hn xs *
        UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) =
      MarkedRow.basisWord n L data hn
        (xs.orderedInsert (· ≤ ·) i) := by
  induction xs with
  | nil =>
      simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
        LieRings.PBW.word, adaptedWeightedBasis]
  | cons x xs ih =>
      have htail : xs.Pairwise (· ≤ ·) := hordered.tail
      have hcons (ys : List (AdaptedIndex n L data hn)) :
          MarkedRow.basisWord n L data hn (x :: ys) =
            UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) *
              MarkedRow.basisWord n L data hn ys := by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word, adaptedWeightedBasis]
      by_cases hix : i ≤ x
      · simp only [List.orderedInsert_cons, if_pos hix]
        rw [hcons]
        have hx : 0 < x.1.val :=
          lt_of_lt_of_le hi (adaptedIndex_weight_mono
            n L data hn hix)
        have hpositive : ∀ j ∈ x :: xs, 0 < j.1.val := by
          intro j hj
          simp only [List.mem_cons] at hj
          rcases hj with rfl | hj
          · exact hx
          · exact lt_of_lt_of_le hx (adaptedIndex_weight_mono
              n L data hn ((List.pairwise_cons.mp hordered).1 j hj))
        exact basisWord_mul_iota_comm_of_pos
          n L data hn i hi (x :: xs) hpositive
      · simp only [List.orderedInsert_cons, if_neg hix]
        rw [hcons, hcons, mul_assoc, ih htail]

theorem fullRightSymbol_basisWord_mul_iota_tail_one_eq_zero
    (q : ℕ)
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·))
    (htail : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1)
    (hlen : xs.length + 1 ≠ q) :
    fullRightSymbol n L data hn q
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L)) = 0 := by
  classical
  rw [← (adaptedBasis n L data hn).sum_repr (rho : FreeModel n L),
    map_sum, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, mul_smul_comm, map_zsmul]
  by_cases hcoeff : ((adaptedBasis n L data hn).repr
      (rho : FreeModel n L)) i = 0
  · rw [hcoeff, zero_smul]
  · have hi0 : i.1.val ≠ 0 := by
      intro hi0
      apply hcoeff
      change ((pieceAdaptedBasis n L data hn i.1).repr
        ((rho : FreeModel n L) i.1)) i.2 = 0
      have hz : (rho : FreeModel n L) i.1 = 0 := by
        exact htail i.1 (by omega)
      rw [hz, map_zero]
      rfl
    have hword : MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) =
        MarkedRow.basisWord n L data hn
          (xs.orderedInsert (· ≤ ·) i) :=
      basisWord_mul_iota_eq_orderedInsert
        n L data hn i (by omega) xs hordered
    rw [hword,
      fullRightSymbol_basisWord_sorted_of_length_ne
        n L data hn q (xs.orderedInsert (· ≤ ·) i)
          (hordered.orderedInsert i xs)
          (by rw [List.orderedInsert_length]; exact hlen)]
    exact smul_zero _

/-- The preceding vanishing statement does not use relation membership: it
only uses that the displayed free-model element has zero weight-one
coordinate.  This form is needed when a genuine full relation is compared
with its weight-one Smith head; their difference lies in the derived tail
but is not itself asserted to be a relation. -/
theorem fullRightSymbol_basisWord_mul_iota_of_mem_tail_one_eq_zero
    (q : ℕ)
    (x : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·))
    (htail : x ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1)
    (hlen : xs.length + 1 ≠ q) :
    fullRightSymbol n L data hn q
        (MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ x) = 0 := by
  classical
  rw [← (adaptedBasis n L data hn).sum_repr x,
    map_sum, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, mul_smul_comm, map_zsmul]
  by_cases hcoeff : ((adaptedBasis n L data hn).repr x) i = 0
  · rw [hcoeff, zero_smul]
  · have hi0 : i.1.val ≠ 0 := by
      intro hi0
      apply hcoeff
      change ((pieceAdaptedBasis n L data hn i.1).repr (x i.1)) i.2 = 0
      have hz : x i.1 = 0 := htail i.1 (by omega)
      rw [hz, map_zero]
      rfl
    have hword : MarkedRow.basisWord n L data hn xs *
          UniversalEnvelopingAlgebra.ι ℤ (adaptedBasis n L data hn i) =
        MarkedRow.basisWord n L data hn
          (xs.orderedInsert (· ≤ ·) i) :=
      basisWord_mul_iota_eq_orderedInsert
        n L data hn i (by omega) xs hordered
    rw [hword,
      fullRightSymbol_basisWord_sorted_of_length_ne
        n L data hn q (xs.orderedInsert (· ≤ ·) i)
          (hordered.orderedInsert i xs)
          (by rw [List.orderedInsert_length]; exact hlen)]
    exact smul_zero _

theorem relationRightBracket_mem_tail_one
    (rho : Relations n L data)
    (x : AdaptedIndex n L data hn)
    (htail : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    ((relationRightBracket n L data hn rho x : Relations n L data) :
        FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  change ⁅(rho : FreeModel n L), adaptedBasis n L data hn x⁆ ∈
    FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1
  rw [← lie_skew]
  exact (FreeMetabelian.Free.tail (X := Generator L)
    (c := n + 1) 1).neg_mem
      ((FreeMetabelian.Free.tail (X := Generator L)
        (c := n + 1) 1).lie_mem htail)

theorem relationSubsetCollection_invariants
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (htail : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1)
    (r : RelationRightRow n L data hn)
    (hr : r ∈ relationSubsetCollection n L data hn rho xs) :
    r.ordinary.Sublist xs ∧
      ((r.relation : Relations n L data) : FreeModel n L) ∈
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  induction xs generalizing rho r with
  | nil =>
      simp only [relationSubsetCollection, List.mem_singleton] at hr
      subst r
      exact ⟨List.Sublist.refl [], htail⟩
  | cons x xs ih =>
      rw [relationSubsetCollection, List.mem_append] at hr
      rcases hr with hr | hr
      · rw [List.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        obtain ⟨hsub, hsTail⟩ := ih rho htail s hs
        exact ⟨hsub.cons_cons x, hsTail⟩
      · obtain ⟨hsub, hsTail⟩ := ih
          (relationRightBracket n L data hn rho x)
          (relationRightBracket_mem_tail_one n L data hn rho x htail)
          r hr
        exact ⟨List.sublist_cons_of_sublist x hsub, hsTail⟩

def RelationRightRow.factorTwoChain
    (r : RelationRightRow n L data hn) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  match r.ordinary with
  | [x] => terminalFullRelationFactorChain n L data hn r.relation
      (adaptedBasis n L data hn x)
  | _ => 0

def RelationRightRow.factorTwoSourceWord
    (r : RelationRightRow n L data hn) : UEA ℤ (FreeModel n L) :=
  match r.ordinary with
  | [x] => terminalFullRelationFactorWord n L data r.relation
      (adaptedBasis n L data hn x)
  | _ => 0

def RelationRightRow.primitiveError
    (r : RelationRightRow n L data hn) : Relations n L data :=
  match r.ordinary with
  | [] => -r.relation
  | [x] => relationRightBracket n L data hn r.relation x
  | _ => 0

theorem relationRightRow_factorTwoChain_boundary
    (r : RelationRightRow n L data hn)
    (hordered : r.ordinary.Pairwise (· ≤ ·))
    (htail : (r.relation : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (r.factorTwoChain n L data hn) =
      rightSymbol n L data hn 2 n (by omega) (r.value n L data hn) := by
  cases hordinary : r.ordinary with
  | nil =>
      simp only [RelationRightRow.factorTwoChain, hordinary, map_zero,
        RelationRightRow.value]
      change 0 = SymmetricPower.map (R := ℤ) (prLE n L n (by omega))
        (fullRightSymbol n L data hn 2
          (MarkedRow.basisWord n L data hn [] *
            UniversalEnvelopingAlgebra.ι ℤ (r.relation : FreeModel n L)))
      rw [fullRightSymbol_basisWord_mul_iota_tail_one_eq_zero
        n L data hn 2 r.relation [] (by simp) htail (by simp),
        map_zero]
  | cons x xs =>
      cases xs with
      | nil =>
          simp only [RelationRightRow.factorTwoChain, hordinary,
            RelationRightRow.value]
          rw [terminalFullRelationFactorChain, Koszul.dOne_tmul]
          rw [show (terminalSourcePresentation n L data hn).d
              (fullRelationToD n L data n (by omega) r.relation) =
                prLE n L n (by omega) (r.relation : FreeModel n L) by rfl]
          rw [show MarkedRow.basisWord n L data hn [x] =
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, adaptedWeightedBasis]]
          change SymmetricPower.insert ℤ (A L n) 1
              (prLE n L n (by omega) (r.relation : FreeModel n L))
              (SymmetricPower.degreeOne
                (prLE n L n (by omega) (adaptedBasis n L data hn x))) =
            rightSymbol n L data hn 2 n (by omega)
              (UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn x) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (r.relation : FreeModel n L))
          exact (rightSymbol_iota_mul_iota_two_comm n L data hn
            (r.relation : FreeModel n L)
            (adaptedBasis n L data hn x)).symm
      | cons y ys =>
          simp only [RelationRightRow.factorTwoChain, hordinary, map_zero,
            RelationRightRow.value]
          change 0 = SymmetricPower.map (R := ℤ) (prLE n L n (by omega))
            (fullRightSymbol n L data hn 2
              (MarkedRow.basisWord n L data hn (x :: y :: ys) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (r.relation : FreeModel n L)))
          rw [fullRightSymbol_basisWord_mul_iota_tail_one_eq_zero
            n L data hn 2 r.relation (x :: y :: ys)
              (by simpa [hordinary] using hordered)
              htail (by simp),
            map_zero]

theorem relationRightRow_factorTwoChain_primitive
    (r : RelationRightRow n L data hn)
    (hordered : r.ordinary.Pairwise (· ≤ ·))
    (htail : (r.relation : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    terminalSourcePrimitive n L data hn
        (r.factorTwoChain n L data hn) =
      pbwPrimitive n L data hn (r.value n L data hn) +
        (r.primitiveError n L data hn : FreeModel n L) := by
  cases hordinary : r.ordinary with
  | nil =>
      simp only [RelationRightRow.factorTwoChain, hordinary, map_zero,
        RelationRightRow.value, RelationRightRow.primitiveError]
      rw [show MarkedRow.basisWord n L data hn [] = 1 by
        simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
          LieRings.PBW.word], one_mul, pbwPrimitive_iota]
      change 0 = (r.relation : FreeModel n L) +
        -(r.relation : FreeModel n L)
      abel
  | cons x xs =>
      cases xs with
      | nil =>
          simp only [RelationRightRow.factorTwoChain, hordinary,
            RelationRightRow.value, RelationRightRow.primitiveError]
          rw [terminalSourcePrimitive_fullRelationFactorChain]
          unfold terminalFullRelationFactorWord
          rw [show MarkedRow.basisWord n L data hn [x] =
              UniversalEnvelopingAlgebra.ι ℤ
                (adaptedBasis n L data hn x) by
            simp [MarkedRow.basisWord, LieRings.PBW.basisWord,
              LieRings.PBW.word, adaptedWeightedBasis]]
          change pbwPrimitive n L data hn
              (UniversalEnvelopingAlgebra.ι ℤ
                  (r.relation : FreeModel n L) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedBasis n L data hn x)) =
            pbwPrimitive n L data hn
                (UniversalEnvelopingAlgebra.ι ℤ
                    (adaptedBasis n L data hn x) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (r.relation : FreeModel n L)) +
              (relationRightBracket n L data hn r.relation x : FreeModel n L)
          have hswap := LieRings.DegreeFive.iota_mul_iota_swap ℤ
            (FreeModel n L) (r.relation : FreeModel n L)
              (adaptedBasis n L data hn x)
          rw [hswap, map_add, pbwPrimitive_iota]
          rfl
      | cons y ys =>
          simp only [RelationRightRow.factorTwoChain, hordinary, map_zero,
            RelationRightRow.value, RelationRightRow.primitiveError]
          have hzero : pbwPrimitive n L data hn
              (MarkedRow.basisWord n L data hn (x :: y :: ys) *
                UniversalEnvelopingAlgebra.ι ℤ
                  (r.relation : FreeModel n L)) = 0 := by
            change (SymmetricPower.degreeOneLinearEquiv
                (adaptedBasis n L data hn))
              (fullRightSymbol n L data hn 1
                (MarkedRow.basisWord n L data hn (x :: y :: ys) *
                  UniversalEnvelopingAlgebra.ι ℤ
                    (r.relation : FreeModel n L))) = 0
            rw [fullRightSymbol_basisWord_mul_iota_tail_one_eq_zero
              n L data hn 1 r.relation (x :: y :: ys)
                (by simpa [hordinary] using hordered)
                htail (by simp),
              map_zero]
          rw [hzero]
          simp

def relationSubsetFactorTwoChain
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn)) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  ((relationSubsetCollection n L data hn rho xs).map
    (fun r ↦ r.factorTwoChain n L data hn)).sum

def relationSubsetPrimitiveError
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn)) : Relations n L data :=
  ((relationSubsetCollection n L data hn rho xs).map
    (fun r ↦ r.primitiveError n L data hn)).sum

theorem dOne_relationSubsetFactorTwoChain
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·))
    (htail : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (relationSubsetFactorTwoChain n L data hn rho xs) =
      rightSymbol n L data hn 2 n (by omega)
        (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
          MarkedRow.basisWord n L data hn xs) := by
  classical
  let rows := relationSubsetCollection n L data hn rho xs
  have hrow (r : RelationRightRow n L data hn) (hr : r ∈ rows) :
      Koszul.dOne (terminalSourcePresentation n L data hn) 1
          (r.factorTwoChain n L data hn) =
        rightSymbol n L data hn 2 n (by omega) (r.value n L data hn) := by
    obtain ⟨hsub, htailr⟩ := relationSubsetCollection_invariants
      n L data hn rho xs htail r hr
    apply relationRightRow_factorTwoChain_boundary
      n L data hn r (hordered.sublist hsub) htailr
  calc
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (relationSubsetFactorTwoChain n L data hn rho xs) =
      (rows.map (fun r ↦ Koszul.dOne
        (terminalSourcePresentation n L data hn) 1
          (r.factorTwoChain n L data hn))).sum := by
            rw [relationSubsetFactorTwoChain, map_list_sum]
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
        ((rows.map (fun r ↦ r.value n L data hn)).sum) := by
          rw [map_list_sum]
          rw [List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro r hr
          rfl
    _ = _ := by
      apply congrArg (rightSymbol n L data hn 2 n (by omega))
      exact relationSubsetCollection_value n L data hn rho xs

theorem terminalSourcePrimitive_relationSubsetFactorTwoChain
    (rho : Relations n L data)
    (xs : List (AdaptedIndex n L data hn))
    (hordered : xs.Pairwise (· ≤ ·))
    (htail : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    terminalSourcePrimitive n L data hn
        (relationSubsetFactorTwoChain n L data hn rho xs) =
      pbwPrimitive n L data hn
          (UniversalEnvelopingAlgebra.ι ℤ (rho : FreeModel n L) *
            MarkedRow.basisWord n L data hn xs) +
        (relationSubsetPrimitiveError n L data hn rho xs : FreeModel n L) := by
  classical
  let rows := relationSubsetCollection n L data hn rho xs
  have hrow (r : RelationRightRow n L data hn) (hr : r ∈ rows) :
      terminalSourcePrimitive n L data hn
          (r.factorTwoChain n L data hn) =
        pbwPrimitive n L data hn (r.value n L data hn) +
          (r.primitiveError n L data hn : FreeModel n L) := by
    obtain ⟨hsub, htailr⟩ := relationSubsetCollection_invariants
      n L data hn rho xs htail r hr
    apply relationRightRow_factorTwoChain_primitive
      n L data hn r (hordered.sublist hsub) htailr
  calc
    terminalSourcePrimitive n L data hn
        (relationSubsetFactorTwoChain n L data hn rho xs) =
      (rows.map (fun r ↦ terminalSourcePrimitive n L data hn
        (r.factorTwoChain n L data hn))).sum := by
          rw [relationSubsetFactorTwoChain, map_list_sum]
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
          ((rows.map (fun r ↦ r.value n L data hn)).sum) +
        ((rows.map (fun r ↦ r.primitiveError n L data hn)).sum :
          Relations n L data) := by
            congr 1
            · rw [map_list_sum]
              rw [List.map_map]
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
              rw [map_list_sum]
              rw [List.map_map]
              apply congrArg List.sum
              apply List.map_congr_left
              intro r hr
              rfl
    _ = _ := by
      rw [relationSubsetCollection_value n L data hn rho xs]
      rfl

/-! ## Contextual full-relation specialization -/

/-- A nonempty bracket context sends every full relation into the derived
tail.  This is the precise metabelian support input needed when its full label
is collected through the ordinary factors. -/
theorem RelationContext.relation_mem_tail_one_of_ne_hole
    (c : RelationContext n L data hn) (rho : Relations n L data)
    (hc : c ≠ .hole) :
    (RelationContext.relation n L data hn c rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1 := by
  have hzero : (rho : FreeModel n L) ∈
      FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 0 := by
    rw [FreeMetabelian.Free.mem_tail_iff]
    intro i hi
    omega
  have hcontext := RelationContext.apply_mem_tail n L data hn c
    (rho : FreeModel n L) 0 hzero
  have hweight : 0 < RelationContext.weight n L data hn c := by
    by_contra hnot
    have hz : RelationContext.weight n L data hn c = 0 := by omega
    exact hc (RelationContext.eq_hole_of_weight_eq_zero
      n L data hn c hz)
  rw [FreeMetabelian.Free.mem_tail_iff] at hcontext ⊢
  intro i hi
  exact hcontext i (by omega)

/-- The mark-one cell label with the ordinary word on the left, expressed in
the exact row type consumed by the factor-two correction. -/
def ProvenancedCell.fullLabelRightRow
    (c : ProvenancedCell n L data hn) : RelationRightRow n L data hn :=
  ⟨RelationContext.relation n L data hn c.context c.root, c.left⟩

@[simp] theorem ProvenancedCell.fullLabelRightRow_value
    (c : ProvenancedCell n L data hn) :
    (c.fullLabelRightRow n L data hn).value n L data hn =
      contextualFullRelationWord n L data hn
        c.root c.context c.left [] := by
  simp [ProvenancedCell.fullLabelRightRow, RelationRightRow.value,
    contextualFullRelationWord, MarkedRow.basisWord,
    LieRings.PBW.basisWord, LieRings.PBW.word]

end

end LieRings.MetabelianVanishing
