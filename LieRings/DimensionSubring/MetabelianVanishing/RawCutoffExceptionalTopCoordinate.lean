import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalComb
import LieRings.DimensionSubring.MetabelianVanishing.ExceptionalGroupedHead
import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalTailAssembly

/-!
# Terminal coordinate of the exceptional Smith-head primitive

This is the local PBW classification at the last exceptional wall.  A
supported exceptional occurrence either has the wrong total homogeneous
weight, contains a positive-weight spectator and vanishes by metabelianity,
or consists entirely of weight-one factors.  In the last case its complete
Smith head is replaced by the corresponding full triangular relation before
the terminal coordinate is evaluated.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

private def rightCombContext
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext n L data hn :=
  xs.foldl (fun c x ↦ .lieRight c x) .hole

private theorem rightCombContext_weight_aux
    (c : RelationContext n L data hn)
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.weight n L data hn
        (xs.foldl (fun c x ↦ RelationContext.lieRight c x) c) =
      RelationContext.weight n L data hn c +
        (xs.map (adaptedWeightedBasis n L data hn).weight).sum := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [RelationContext.weight, Nat.add_assoc]

private theorem rightCombContext_weight
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.weight n L data hn
        (rightCombContext n L data hn xs) =
      (xs.map (adaptedWeightedBasis n L data hn).weight).sum := by
  simpa [rightCombContext, RelationContext.weight] using
    rightCombContext_weight_aux n L data hn
      (.hole : RelationContext n L data hn) xs

private theorem rightCombContext_apply_aux
    (c : RelationContext n L data hn)
    (d : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.apply n L data hn
        (xs.foldl (fun c x ↦ RelationContext.lieRight c x) c) d =
      adaptedRightComb n L data hn
        (RelationContext.apply n L data hn c d) xs := by
  induction xs generalizing c d with
  | nil => simp [adaptedRightComb]
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      rfl

private theorem rightCombContext_apply
    (d : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn)) :
    RelationContext.apply n L data hn
        (rightCombContext n L data hn xs) d =
      adaptedRightComb n L data hn d xs := by
  simpa [rightCombContext] using
    rightCombContext_apply_aux n L data hn
      (.hole : RelationContext n L data hn) d xs

@[simp] private theorem adaptedRightComb_zero
    (xs : List (AdaptedIndex n L data hn)) :
    adaptedRightComb n L data hn 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [adaptedRightComb, zero_lie, ih]

private theorem adaptedRightComb_zsmul
    (a : ℤ) (d : FreeModel n L)
    (xs : List (AdaptedIndex n L data hn)) :
    adaptedRightComb n L data hn (a • d) xs =
      a • adaptedRightComb n L data hn d xs := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih =>
      change adaptedRightComb n L data hn
          ⁅a • d, adaptedBasis n L data hn x⁆ xs =
        a • adaptedRightComb n L data hn
          ⁅d, adaptedBasis n L data hn x⁆ xs
      rw [smul_lie, ih]

private theorem adaptedBasis_mem_derived_of_pos
    (i : AdaptedIndex n L data hn) (hi : 0 < i.1.val) :
    adaptedBasis n L data hn i ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  have hweight := FreeMetabelian.Evaluation.weightIncl_mem_lowerCentralSeries
    (generatorBasis L) i.1.val i.1.isLt
      (pieceAdaptedBasis n L data hn i.1 i.2)
  have hone : adaptedBasis n L data hn i ∈
      lowerCentralSeries ℤ (FreeModel n L) 1 := by
    rw [adaptedBasis_apply]
    exact LieModule.antitone_lowerCentralSeries ℤ
      (FreeModel n L) (FreeModel n L) (by omega) hweight
  simpa [LieAlgebra.derivedSeries_def,
    LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero,
    lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    LieSubmodule.lie_comm] using hone

private theorem derived_lie_adaptedBasis
    (d : FreeModel n L)
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1)
    (i : AdaptedIndex n L data hn) :
    ⁅d, adaptedBasis n L data hn i⁆ ∈
      LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
  rw [← lie_skew]
  exact (LieAlgebra.derivedSeries ℤ (FreeModel n L) 1).neg_mem
    ((LieAlgebra.derivedSeries ℤ (FreeModel n L) 1).lie_mem hd)

private theorem adaptedRightComb_eq_zero_of_derived_of_exists_pos
    (d : FreeModel n L)
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (FreeModel n L) 1)
    (xs : List (AdaptedIndex n L data hn))
    (hpos : ∃ i ∈ xs, 0 < i.1.val) :
    adaptedRightComb n L data hn d xs = 0 := by
  induction xs generalizing d with
  | nil => simp at hpos
  | cons x xs ih =>
      by_cases hx : 0 < x.1.val
      · have hbracket : ⁅d, adaptedBasis n L data hn x⁆ = 0 :=
          IsMetabelian.bracket_eq_zero
            (FreeMetabelian.Free.isMetabelian
              (X := Generator L) (c := n + 1)) hd
            (adaptedBasis_mem_derived_of_pos n L data hn x hx)
        rw [adaptedRightComb, hbracket, adaptedRightComb_zero]
      · have htail : ∃ i ∈ xs, 0 < i.1.val := by
          obtain ⟨i, hi, hipos⟩ := hpos
          simp only [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact (hx hipos).elim
          · exact ⟨i, hi, hipos⟩
        rw [adaptedRightComb]
        exact ih ⁅d, adaptedBasis n L data hn x⁆
          (derived_lie_adaptedBasis n L data hn d hd x) htail

private theorem adaptedIndex_weight_mono
    {i j : AdaptedIndex n L data hn} (hij : i ≤ j) :
    i.1.val ≤ j.1.val := by
  change toLex (i.1.val, i.2.val) ≤ toLex (j.1.val, j.2.val) at hij
  simpa using Prod.Lex.monotone_fst _ _ hij

private theorem top_homogeneous_apply
    (c : RelationContext n L data hn)
    (hc : RelationContext.weight n L data hn c = n)
    (z : FreeMetabelian.Piece (Generator L) 0) :
    FreeMetabelian.Free.weightIncl n (by omega)
        (FreeMetabelian.Free.weightProject n (by omega)
          (RelationContext.apply n L data hn c
            (FreeMetabelian.Free.weightIncl 0 (by omega) z))) =
      RelationContext.apply n L data hn c
        (FreeMetabelian.Free.weightIncl 0 (by omega) z) := by
  let y := RelationContext.apply n L data hn c
    (FreeMetabelian.Free.weightIncl 0 (by omega) z)
  change FreeMetabelian.Free.incl (⟨n, by omega⟩ : Fin (n + 1))
      (FreeMetabelian.Free.project (⟨n, by omega⟩ : Fin (n + 1)) y) = y
  calc
    _ = ∑ j : Fin (n + 1),
        FreeMetabelian.Free.incl j (FreeMetabelian.Free.project j y) := by
      symm
      apply Finset.sum_eq_single (⟨n, by omega⟩ : Fin (n + 1))
      · intro j _ hj
        have hjval : j.val ≠ n := by
          intro hval
          exact hj (Fin.ext hval)
        have hz : FreeMetabelian.Free.project j y = 0 :=
          RelationContext.apply_weightIncl_apply_eq_zero_of_ne
            n L data hn c 0 (by omega) z j (by omega)
        rw [hz, map_zero]
      · simp
    _ = y := FreeMetabelian.Free.sum_incl_project y

private theorem topCoord_weightProject_eq_zero_of_relation
    (x : FreeModel n L) (rho : Relations n L data)
    (hhom : FreeMetabelian.Free.weightIncl n (by omega)
        (FreeMetabelian.Free.weightProject n (by omega) x) = x)
    (hrho : x = (rho : FreeModel n L)) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega) x) = 0 := by
  change terminalEval n L data
    (topInclPreimage n L data
      (FreeMetabelian.Free.weightProject n (by omega) x)) = 0
  have heq : topInclPreimage n L data
      (FreeMetabelian.Free.weightProject n (by omega) x) =
        relationTopPreimage n L data rho := by
    apply Subtype.ext
    exact hhom.trans hrho
  rw [heq, terminalEval_relationTopPreimage]

/-- A weight-one component of a genuine triangular relation has zero
terminal primitive coordinate, independently of how the occurrence was
produced.  This is the local form needed by a root-inclusive ledger: the
root is retained as a whole triangular relation, and the order-selected PBW
head is never declared to be a relation.

The proof first keeps the complete Smith head grouped.  If the displayed
word has the wrong total weight, homogeneity kills it.  At total weight
`n`, the sole possible primitive is the insertion comb.  That comb is the
negative of the full contextual triangular relation at context weight `n`;
the triangular tail is beyond the nilpotence cutoff. -/
theorem ProvenancedCell.topCoord_weightProject_primitive_eq_zero_of_triangularWeightOne
    (c : ProvenancedCell n L data hn)
    (i : FreeMetabelian.Free.PieceIndex (Fin (Nat.card L)) 0)
    (hroot : c.root = triangularRelationOfIndex n L data
      (⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ :
        TriangularRelationIndex n L))
    (hmark : c.mark.val = 1)
    (hcontext : c.context = .hole)
    (hordered : c.left.Pairwise (· ≤ ·)) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega)
          (c.primitive n L data hn)) = 0 := by
  classical
  have hactive : c.activeWeight n L data hn = 1 := by
    simp [ProvenancedCell.activeWeight, hmark, hcontext,
      RelationContext.weight]
  by_cases htopWeight :
      (c.left.map (adaptedWeightedBasis n L data hn).weight).sum = n
  · have hne : c.left ≠ [] := by
      intro hnil
      rw [hnil] at htopWeight
      simp at htopWeight
      omega
    obtain ⟨x, xs, hleft, hprimitive⟩ :=
      c.primitive_eq_weightOneRightInsertionPrimitive
        n L data hn i hroot hmark hcontext hordered hne
    let h : AdaptedIndex n L data hn :=
      ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
    let d : ℤ :=
      ((triangularSmith n L data 0 (by omega)).diagonal i : ℤ)
    have hhead : adaptedBasis n L data hn h =
        FreeMetabelian.Free.weightIncl 0 (by omega)
          (triangularPieceBasis n L data 0 (by omega) i) := by
      rw [adaptedBasis_apply]
      change FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (n + 1))
        (pieceAdaptedBasis n L data hn
          (⟨0, by omega⟩ : Fin (n + 1)) i) = _
      congr 1
    have hprimitiveSeed : c.primitive n L data hn =
        d • weightOneRightInsertionSeed n L data hn x xs i := by
      rw [hprimitive, map_zsmul]
      change d • weightOneRightInsertionPrimitive n L data hn x xs
          (triangularPieceBasis n L data 0 (by omega) i) = _
      congr 1
      change (Finsupp.linearCombination ℤ
          (weightOneRightInsertionSeed n L data hn x xs))
            ((pieceAdaptedBasis n L data hn
              (⟨0, by omega⟩ : Fin (n + 1))).repr
                (triangularPieceBasis n L data 0 (by omega) i)) = _
      change (Finsupp.linearCombination ℤ
          (weightOneRightInsertionSeed n L data hn x xs))
            ((triangularPieceBasis n L data 0 (by omega)).repr
              (triangularPieceBasis n L data 0 (by omega) i)) = _
      rw [Module.Basis.repr_self]
      have hsingle := Finsupp.linearCombination_single (R := ℤ) (v :=
        weightOneRightInsertionSeed n L data hn x xs) (1 : ℤ) i
      simpa only [one_smul] using hsingle
    have hcontextWeight : RelationContext.weight n L data hn
        (rightCombContext n L data hn c.left) = n := by
      rw [rightCombContext_weight, htopWeight]
    by_cases hbefore : ∀ y ∈ x :: xs, h ≤ y
    · have hprimComb : c.primitive n L data hn =
          -RelationContext.apply n L data hn
            (rightCombContext n L data hn c.left)
            (FreeMetabelian.Free.weightIncl 0 (by omega)
              (d • triangularPieceBasis n L data 0 (by omega) i)) := by
        rw [hprimitiveSeed, weightOneRightInsertionSeed, if_pos hbefore]
        calc
          d • adaptedRightComb n L data hn
              ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ xs =
              d • (-adaptedRightComb n L data hn
                (adaptedBasis n L data hn h) (x :: xs)) := by
                  rw [adaptedRightComb_bracket_skew]
          _ = -adaptedRightComb n L data hn
                (d • adaptedBasis n L data hn h) (x :: xs) := by
                  rw [smul_neg, adaptedRightComb_zsmul]
          _ = -RelationContext.apply n L data hn
                (rightCombContext n L data hn c.left)
                (d • adaptedBasis n L data hn h) := by
                  rw [rightCombContext_apply, hleft]
          _ = -RelationContext.apply n L data hn
                (rightCombContext n L data hn c.left)
                (FreeMetabelian.Free.weightIncl 0 (by omega)
                  (d • triangularPieceBasis n L data 0 (by omega) i)) := by
                  simp only [map_zsmul, hhead]
      let rho : Relations n L data :=
        -RelationContext.relation n L data hn
          (rightCombContext n L data hn c.left)
          (triangularRelationOfIndex n L data
            ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩)
      have hfull :=
        RelationContext.apply_triangularRelationOfIndex_eq_apply_head
          n L data hn
            ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ rfl
            (rightCombContext n L data hn c.left) hcontextWeight
      have hrho : c.primitive n L data hn =
          (rho : FreeModel n L) := by
        rw [hprimComb]
        change -_ = -RelationContext.apply n L data hn
          (rightCombContext n L data hn c.left)
            (triangularRelationOfIndex n L data
              ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ : FreeModel n L)
        exact congrArg Neg.neg hfull.symm
      have hheadHom := top_homogeneous_apply n L data hn
        (rightCombContext n L data hn c.left) hcontextWeight
        (d • triangularPieceBasis n L data 0 (by omega) i)
      have hhom : FreeMetabelian.Free.weightIncl n (by omega)
            (FreeMetabelian.Free.weightProject n (by omega)
              (c.primitive n L data hn)) =
          c.primitive n L data hn := by
        rw [hprimComb, map_neg, map_neg]
        exact congrArg Neg.neg hheadHom
      exact topCoord_weightProject_eq_zero_of_relation
        n L data (c.primitive n L data hn) rho hhom hrho
    · rw [hprimitiveSeed, weightOneRightInsertionSeed, if_neg hbefore,
        smul_zero, map_zero]
      exact map_zero _
  · have hweightNe :
        (c.left.map (adaptedWeightedBasis n L data hn).weight).sum +
            c.activeWeight n L data hn ≠ n + 1 := by
      rw [hactive]
      omega
    rw [c.weightProject_primitive_eq_zero_of_ne n L data hn hweightNe,
      map_zero]

set_option maxHeartbeats 2000000 in
/-- The terminal coordinate of each supported exceptional primitive is zero.
The statement retains the complete Smith head; no selected part of a
triangular relation is treated as a relation. -/
theorem GoverningWitness.topCoord_weightProject_primitive_eq_zero_of_rawCutoffHoleExceptional
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0)
    (hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega)
          (c.primitive n L data hn)) = 0 := by
  classical
  have hcases := w.rawCutoffHoleExceptional_left_cases
    n L data hn c hc hexceptional
  obtain ⟨tag, htag, hroot⟩ :=
    w.rawCutoffHoleExceptional_root n L data hn c hc hexceptional
  rcases tag with ⟨⟨s, hslt⟩, i⟩
  simp only at htag
  subst s
  have hproof : hslt = (by omega : 0 < n + 1) := Subsingleton.elim _ _
  cases hproof
  obtain ⟨x, xs, hleft, hprimitive⟩ :=
    c.primitive_eq_weightOneRightInsertionPrimitive
      n L data hn i hroot hexceptional.1 hexceptional.2.1 hcases.1
        (by intro h; rw [h] at hcases; simp at hcases)
  let h : AdaptedIndex n L data hn :=
    ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩
  let d : ℤ :=
    ((triangularSmith n L data 0 (by omega)).diagonal i : ℤ)
  have hhead : adaptedBasis n L data hn h =
      FreeMetabelian.Free.weightIncl 0 (by omega)
        (triangularPieceBasis n L data 0 (by omega) i) := by
    rw [adaptedBasis_apply]
    change FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (n + 1))
      (pieceAdaptedBasis n L data hn
        (⟨0, by omega⟩ : Fin (n + 1)) i) = _
    congr 1
  have hprimitiveSeed : c.primitive n L data hn =
      d • weightOneRightInsertionSeed n L data hn x xs i := by
    rw [hprimitive, map_zsmul]
    change d • weightOneRightInsertionPrimitive n L data hn x xs
        (triangularPieceBasis n L data 0 (by omega) i) = _
    congr 1
    change (Finsupp.linearCombination ℤ
        (weightOneRightInsertionSeed n L data hn x xs))
          ((pieceAdaptedBasis n L data hn
            (⟨0, by omega⟩ : Fin (n + 1))).repr
              (triangularPieceBasis n L data 0 (by omega) i)) = _
    change (Finsupp.linearCombination ℤ
        (weightOneRightInsertionSeed n L data hn x xs))
          ((triangularPieceBasis n L data 0 (by omega)).repr
            (triangularPieceBasis n L data 0 (by omega) i)) = _
    rw [Module.Basis.repr_self]
    have hsingle := Finsupp.linearCombination_single (R := ℤ) (v :=
      weightOneRightInsertionSeed n L data hn x xs) (1 : ℤ) i
    simpa only [one_smul] using hsingle
  have hactive : c.activeWeight n L data hn = 1 := by
    simp [ProvenancedCell.activeWeight, hexceptional.1,
      hexceptional.2.1, RelationContext.weight]
  by_cases htopWeight :
      (c.left.map (adaptedWeightedBasis n L data hn).weight).sum = n
  · rcases hcases.2.2 with hall | hpos
    · have hlen : c.left.length = n := by omega
      have hcontextWeight : RelationContext.weight n L data hn
          (rightCombContext n L data hn c.left) = n := by
        rw [rightCombContext_weight, htopWeight]
      by_cases hbefore : ∀ y ∈ x :: xs, h ≤ y
      · have hprimComb : c.primitive n L data hn =
            -RelationContext.apply n L data hn
              (rightCombContext n L data hn c.left)
              (FreeMetabelian.Free.weightIncl 0 (by omega)
                (d • triangularPieceBasis n L data 0 (by omega) i)) := by
          rw [hprimitiveSeed, weightOneRightInsertionSeed, if_pos hbefore]
          calc
            d • adaptedRightComb n L data hn
                ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ xs =
                d • (-adaptedRightComb n L data hn
                  (adaptedBasis n L data hn h) (x :: xs)) := by
                    rw [adaptedRightComb_bracket_skew]
            _ = -adaptedRightComb n L data hn
                  (d • adaptedBasis n L data hn h) (x :: xs) := by
                    rw [smul_neg, adaptedRightComb_zsmul]
            _ = -RelationContext.apply n L data hn
                  (rightCombContext n L data hn c.left)
                  (d • adaptedBasis n L data hn h) := by
                    rw [rightCombContext_apply, hleft]
            _ = -RelationContext.apply n L data hn
                  (rightCombContext n L data hn c.left)
                  (FreeMetabelian.Free.weightIncl 0 (by omega)
                    (d • triangularPieceBasis n L data 0 (by omega) i)) := by
                    simp only [map_zsmul, hhead]
        let rho : Relations n L data :=
          -RelationContext.relation n L data hn
            (rightCombContext n L data hn c.left)
            (triangularRelationOfIndex n L data
              ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩)
        have hfull :=
          RelationContext.apply_triangularRelationOfIndex_eq_apply_head
            n L data hn
              ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ rfl
              (rightCombContext n L data hn c.left) hcontextWeight
        have hrho : c.primitive n L data hn =
            (rho : FreeModel n L) := by
          rw [hprimComb]
          change -_ = -RelationContext.apply n L data hn
            (rightCombContext n L data hn c.left)
              (triangularRelationOfIndex n L data
                ⟨(⟨0, by omega⟩ : Fin (n + 1)), i⟩ : FreeModel n L)
          exact congrArg Neg.neg hfull.symm
        have hheadHom := top_homogeneous_apply n L data hn
          (rightCombContext n L data hn c.left) hcontextWeight
          (d • triangularPieceBasis n L data 0 (by omega) i)
        have hhom : FreeMetabelian.Free.weightIncl n (by omega)
              (FreeMetabelian.Free.weightProject n (by omega)
                (c.primitive n L data hn)) =
            c.primitive n L data hn := by
          rw [hprimComb, map_neg, map_neg]
          exact congrArg Neg.neg hheadHom
        exact topCoord_weightProject_eq_zero_of_relation
          n L data (c.primitive n L data hn) rho hhom hrho
      · rw [hprimitiveSeed, weightOneRightInsertionSeed, if_neg hbefore,
          smul_zero, map_zero]
        exact map_zero _
    · have hlen : 2 ≤ (x :: xs).length := by
          simpa [hleft] using hcases.2.1
      have hordered : (x :: xs).Pairwise (· ≤ ·) := by
        simpa [hleft] using hcases.1
      have hxsne : xs ≠ [] := by
        intro hnil
        simp [hnil] at hlen
      have htailPos : ∃ j ∈ xs, 0 < j.1.val := by
        obtain ⟨j, hj, hjpos⟩ := hpos.1
        rw [hleft] at hj
        simp only [List.mem_cons] at hj
        rcases hj with hjx | hj
        · have hxpos : 0 < x.1.val := by simpa [hjx] using hjpos
          obtain ⟨y, ys, hxs⟩ := List.exists_cons_of_ne_nil hxsne
          have hy : y ∈ xs := by rw [hxs]; simp
          have hxy : x ≤ y := (List.pairwise_cons.mp hordered).1 y hy
          exact ⟨y, hy,
            lt_of_lt_of_le hxpos
              (adaptedIndex_weight_mono n L data hn hxy)⟩
        · exact ⟨j, hj, hjpos⟩
      by_cases hbefore : ∀ y ∈ x :: xs, h ≤ y
      · have hderived :
            ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆ ∈
              LieAlgebra.derivedSeries ℤ (FreeModel n L) 1 := by
            rw [LieAlgebra.derivedSeries_def,
              LieAlgebra.derivedSeriesOfIdeal_succ,
              LieAlgebra.derivedSeriesOfIdeal_zero]
            exact LieSubmodule.lie_mem_lie (by simp) (by simp)
        have hcomb := adaptedRightComb_eq_zero_of_derived_of_exists_pos
          n L data hn
            ⁅adaptedBasis n L data hn x, adaptedBasis n L data hn h⁆
            hderived xs htailPos
        rw [hprimitiveSeed, weightOneRightInsertionSeed, if_pos hbefore,
          hcomb, smul_zero, map_zero]
        exact map_zero _
      · rw [hprimitiveSeed, weightOneRightInsertionSeed, if_neg hbefore,
          smul_zero, map_zero]
        exact map_zero _
  · have hweightNe :
        (c.left.map (adaptedWeightedBasis n L data hn).weight).sum +
            c.activeWeight n L data hn ≠ n + 1 := by
        rw [hactive]
        omega
    rw [c.weightProject_primitive_eq_zero_of_ne n L data hn hweightNe,
      map_zero]

/-- The conditional exceptional-component primitive has zero terminal
coordinate on every supported raw-cutoff occurrence. -/
theorem GoverningWitness.topCoord_weightProject_holeExceptionalComponentPrimitive_eq_zero
    {a : L} (w : GoverningWitness n L data a)
    (c : ProvenancedCell n L data hn)
    (hc : w.rawCutoffFullProvenancedCells n L data hn c ≠ 0) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega)
          (c.holeExceptionalComponentPrimitive n L data hn)) = 0 := by
  classical
  by_cases hexceptional : c.mark.val = 1 ∧ c.context = .hole ∧
      (c.root : FreeModel n L) ∉
        FreeMetabelian.Free.tail (X := Generator L) (c := n + 1) 1
  · rw [ProvenancedCell.holeExceptionalComponentPrimitive,
      if_pos hexceptional]
    exact w.topCoord_weightProject_primitive_eq_zero_of_rawCutoffHoleExceptional
      n L data hn c hc hexceptional
  · rw [ProvenancedCell.holeExceptionalComponentPrimitive,
      if_neg hexceptional, map_zero, map_zero]

/-- The signed aggregate of all exceptional component primitives has zero
terminal coordinate. -/
theorem GoverningWitness.topCoord_weightProject_rawCutoffExceptionalComponentPrimitive_eq_zero
    {a : L} (w : GoverningWitness n L data a) :
    topCoord n L data
        (FreeMetabelian.Free.weightProject n (by omega)
          ((w.rawCutoffFullProvenancedCells n L data hn).sum (fun c z ↦
            z • c.holeExceptionalComponentPrimitive n L data hn))) = 0 := by
  classical
  rw [map_finsuppSum, map_finsuppSum]
  apply Finset.sum_eq_zero
  intro c hc
  change topCoord n L data
    (FreeMetabelian.Free.weightProject n (by omega)
      (w.rawCutoffFullProvenancedCells n L data hn c •
        c.holeExceptionalComponentPrimitive n L data hn)) = 0
  rw [map_zsmul, map_zsmul,
    w.topCoord_weightProject_holeExceptionalComponentPrimitive_eq_zero
      n L data hn c
      (Finsupp.mem_support_iff.mp hc), smul_zero]

end

end LieRings.MetabelianVanishing
