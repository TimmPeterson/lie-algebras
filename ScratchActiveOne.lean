import LieRings.DimensionSubring.MetabelianVanishing.Assembly

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct

universe u

noncomputable section

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance : Fintype L := Fintype.ofFinite L

theorem test_context_eq_hole_of_weight_eq_zero
    (c : RelationContext n L data hn)
    (h : RelationContext.weight n L data hn c = 0) :
    c = .hole := by
  cases c with
  | hole => rfl
  | lieRight c x =>
      simp [RelationContext.weight, adaptedWeightedBasis] at h

theorem test_cell_active_one_context
    (c : ProvenancedCell n L data hn)
    (h : c.activeWeight n L data hn = 1) :
    c.context = .hole ∧ c.mark.val = 1 := by
  have hm : c.mark.val = 1 := by
    simp only [ProvenancedCell.activeWeight] at h
    have hp := c.mark_pos
    omega
  have hc : RelationContext.weight n L data hn c.context = 0 := by
    simp only [ProvenancedCell.activeWeight] at h
    omega
  exact ⟨test_context_eq_hole_of_weight_eq_zero n L data hn c.context hc, hm⟩

theorem test_relation_weightZero_pieceEval_mem_derived
    (rho : Relations n L data) :
    FreeMetabelian.Evaluation.pieceEval data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) 0
        (FreeMetabelian.Free.weightProject 0 (by omega) rho.1) ∈
      LieAlgebra.derivedSeries ℤ L 1 := by
  have hp : relationPrefix n L data 1 (by omega) rho =
      FreeMetabelian.Free.weightIncl 0 (by omega)
        (FreeMetabelian.Free.weightProject 0 (by omega) rho.1) := by
    change FreeMetabelian.Free.projectPrefix 1 (by omega) rho.1 = _
    funext i
    fin_cases i
    change rho.1 ⟨0, by omega⟩ =
      (FreeMetabelian.Free.incl ⟨0, by omega⟩
        (rho.1 ⟨0, by omega⟩)) ⟨0, by omega⟩
    rw [FreeMetabelian.Free.incl_apply_same]
  have hD : relationPrefix n L data 1 (by omega) rho ∈
      D n L data 1 (by omega) := ⟨rho, rfl⟩
  have hz := D_le_ker_augmentation n L data 1 (by omega) hD
  rw [LinearMap.mem_ker, hp] at hz
  change (lowerCentralSeries ℤ L 1 : Submodule ℤ L).mkQ
      (FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) 1
        (FreeMetabelian.Free.weightIncl 0 (by omega)
          (FreeMetabelian.Free.weightProject 0 (by omega) rho.1))) = 0 at hz
  change (lowerCentralSeries ℤ L 1 : Submodule ℤ L).mkQ
      (FreeMetabelian.Evaluation.linear data.metabelian
        (FreeMetabelian.Evaluation.canonicalGeneratorMap L) 1
        (FreeMetabelian.Free.incl ⟨0, by omega⟩
          (FreeMetabelian.Free.weightProject 0 (by omega) rho.1))) = 0 at hz
  rw [FreeMetabelian.Evaluation.linear_incl] at hz
  rw [derived_eq_lowerCentralSeries_one L]
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

theorem test_T_factorEdge_eq_zero_of_activeWeight_one
    (c : ProvenancedCell n L data hn)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (hlen : c.left.length = n - k + 1)
    (hactive : c.activeWeight n L data hn = 1) :
    T n L data k hk hkn
        (c.factorEdge n L data hn (n - k + 2) k (by omega)) = 0 := by
  classical
  obtain ⟨hcontext, hmarkval⟩ :=
    test_cell_active_one_context n L data hn c hactive
  have hmark : c.mark = ⟨1, by omega⟩ := Fin.ext hmarkval
  let x₀ : FreeMetabelian.Piece (Generator L) 0 :=
    FreeMetabelian.Free.weightProject 0 (by omega) c.root.1
  have hcomponent : RelationContext.component n L data hn
      c.context c.root c.mark =
      FreeMetabelian.Free.weightIncl 0 (by omega) x₀ := by
    rw [RelationContext.component, dif_neg (by omega), hcontext]
    change FreeMetabelian.Free.incl
          (⟨c.mark.val - 1, by omega⟩ : Fin (n + 1))
          (FreeMetabelian.Free.project
            (⟨c.mark.val - 1, by omega⟩ : Fin (n + 1)) c.root.1) =
        FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin (n + 1))
          (FreeMetabelian.Free.project
            (⟨0, by omega⟩ : Fin (n + 1)) c.root.1)
    have hpred : c.mark.val - 1 = 0 := by omega
    have hidx : (⟨c.mark.val - 1, by omega⟩ : Fin (n + 1)) =
        ⟨0, by omega⟩ := Fin.ext hpred
    rw [hidx]
  have hvalue : c.componentRow.value =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ
          (RelationContext.component n L data hn
            c.context c.root c.mark) := by
    simp [ProvenancedCell.componentRow, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word]
  have hedge : c.factorEdge n L data hn (n - k + 2) k (by omega) =
      SymmetricPower.insert ℤ (A L k) (n - k + 1)
        (prLE n L k (by omega)
          (RelationContext.component n L data hn
            c.context c.root c.mark))
        (SymmetricPower.tprod ℤ (fun j : Fin (n - k + 1) ↦
          prLE n L k (by omega)
            (adaptedBasis n L data hn
              (c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩)))) := by
    rw [ProvenancedCell.factorEdge, hvalue]
    exact rightSymbol_basisWord_mul_iota_of_length n L data hn
      (n - k + 1) k (by omega) c.left _ hlen
  by_cases hall : ∀ j : Fin (n - k + 1),
      (c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩).1.val < k
  · let index : Fin (n - k + 1) → AdaptedIndex n L data hn := fun j ↦
      c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩
    let degrees : Fin (n - k + 2) → Fin k :=
      Fin.cons ⟨0, by omega⟩ (fun j ↦ ⟨(index j).1.val, hall j⟩)
    let pieces : ∀ i, FreeMetabelian.Piece (Generator L) (degrees i).val :=
      Fin.cons x₀ (fun j ↦
        pieceAdaptedBasis n L data hn (index j).1 (index j).2)
    have hcomponentPrefix : prLE n L k (by omega)
        (RelationContext.component n L data hn
          c.context c.root c.mark) =
        FreeMetabelian.Free.weightIncl 0 (by omega) x₀ := by
      rw [hcomponent]
      exact FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
        k 0 (by omega) (by omega) (by omega) x₀
    have hinputs : Fin.cons
          (prLE n L k (by omega)
            (RelationContext.component n L data hn
              c.context c.root c.mark))
          (fun j : Fin (n - k + 1) ↦
            prLE n L k (by omega)
              (adaptedBasis n L data hn (index j))) =
        fun i ↦ FreeMetabelian.Free.weightIncl
          (degrees i).val (degrees i).isLt (pieces i) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact hcomponentPrefix
      · change prLE n L k (by omega)
            (adaptedBasis n L data hn (index j)) =
          FreeMetabelian.Free.weightIncl (index j).1.val (hall j)
            (pieceAdaptedBasis n L data hn (index j).1 (index j).2)
        rw [adaptedBasis_apply]
        exact FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
          k (index j).1.val (by omega) (index j).1.isLt (hall j) _
    rw [hedge, SymmetricPower.insert_tprod]
    change T n L data k hk hkn
        (SymmetricPower.tprod ℤ (Fin.cons
          (prLE n L k (by omega)
            (RelationContext.component n L data hn
              c.context c.root c.mark))
          (fun j : Fin (n - k + 1) ↦
            prLE n L k (by omega)
              (adaptedBasis n L data hn (index j))))) = 0
    rw [hinputs]
    apply T_homogeneous_eq_zero_of_derived_weightOne
      n L data k hk hkn degrees pieces 0
    · rfl
    · exact test_relation_weightZero_pieceEval_mem_derived
        n L data hn c.root
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hprefix : prLE n L k (by omega)
        (adaptedBasis n L data hn
          (c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩)) = 0 := by
      rw [adaptedBasis_apply]
      exact FreeMetabelian.Free.projectPrefix_weightIncl_eq_zero
        k _ (by omega) _ hj _
    have htprod : SymmetricPower.tprod ℤ
        (fun r : Fin (n - k + 1) ↦
          prLE n L k (by omega)
            (adaptedBasis n L data hn
              (c.left.get ⟨r.val, by simpa only [hlen] using r.isLt⟩))) = 0 :=
      (SymmetricPower.tprod ℤ).map_coord_zero j hprefix
    rw [hedge, htprod, map_zero, map_zero]

theorem test_T_activeWeightOneComponentFactorSum_eq_zero
    (cells : ProvenancedCell n L data hn →₀ ℤ)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    T n L data k hk hkn
        (cells.sum (fun c z ↦ z •
          if hlen : c.left.length = n - k + 1 then
            if hactive : c.activeWeight n L data hn = 1 then
              c.factorEdge n L data hn (n - k + 2) k (by omega)
            else 0
          else 0)) = 0 := by
  classical
  rw [map_finsuppSum]
  calc
    _ = cells.sum (fun _ _ ↦ (0 : ZMod (2 ^ data.exponent))) := by
      apply Finsupp.sum_congr
      intro c hc
      rw [map_zsmul]
      by_cases hlen : c.left.length = n - k + 1
      · rw [dif_pos hlen]
        by_cases hactive : c.activeWeight n L data hn = 1
        · rw [dif_pos hactive,
            test_T_factorEdge_eq_zero_of_activeWeight_one
              n L data hn c k hk hkn hlen hactive, smul_zero]
        · rw [dif_neg hactive, map_zero, smul_zero]
      · rw [dif_neg hlen, map_zero, smul_zero]
    _ = 0 := by simp

theorem test_T_factorEdge_eq_zero_of_activeWeight_gt_one_ne
    (c : ProvenancedCell n L data hn)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (hlen : c.left.length = n - k + 1)
    (hgt : 1 < c.activeWeight n L data hn)
    (hne : c.activeWeight n L data hn ≠ k) :
    T n L data k hk hkn
        (c.factorEdge n L data hn (n - k + 2) k (by omega)) = 0 := by
  classical
  let component := RelationContext.component n L data hn
    c.context c.root c.mark
  have hvalue : c.componentRow.value =
      MarkedRow.basisWord n L data hn c.left *
        UniversalEnvelopingAlgebra.ι ℤ component := by
    simp [ProvenancedCell.componentRow, ProvenancedRow.value,
      MarkedRow.basisWord, LieRings.PBW.basisWord, LieRings.PBW.word,
      component]
  have hedge : c.factorEdge n L data hn (n - k + 2) k (by omega) =
      SymmetricPower.insert ℤ (A L k) (n - k + 1)
        (prLE n L k (by omega) component)
        (SymmetricPower.tprod ℤ (fun j : Fin (n - k + 1) ↦
          prLE n L k (by omega)
            (adaptedBasis n L data hn
              (c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩)))) := by
    rw [ProvenancedCell.factorEdge, hvalue]
    exact rightSymbol_basisWord_mul_iota_of_length n L data hn
      (n - k + 1) k (by omega) c.left _ hlen
  by_cases hactiveLt : c.activeWeight n L data hn < k
  · let r := c.activeWeight n L data hn - 1
    let xᵣ : FreeMetabelian.Piece (Generator L) r :=
      FreeMetabelian.Free.weightProject r (by omega) component
    have hcomponentPrefix : prLE n L k (by omega) component =
        FreeMetabelian.Free.weightIncl r (by omega) xᵣ := by
      funext i
      let ir : Fin k := ⟨r, by omega⟩
      by_cases hi : i = ir
      · subst i
        change component ⟨r, by omega⟩ =
          (FreeMetabelian.Free.incl ir xᵣ) ir
        rw [FreeMetabelian.Free.incl_apply_same]
        rfl
      · have hir : i.val ≠ r := by
          intro hir
          apply hi
          exact Fin.ext hir
        have hleft : component ⟨i.val, by omega⟩ = 0 := by
          apply RelationContext.component_apply_eq_zero_of_ne
            n L data hn c.context c.root c.mark c.mark_pos
          change i.val + 1 ≠ c.activeWeight n L data hn
          omega
        change component ⟨i.val, by omega⟩ =
          (FreeMetabelian.Free.incl ir xᵣ) i
        rw [hleft, FreeMetabelian.Free.incl_apply_of_ne]
        exact hi
    by_cases hall : ∀ j : Fin (n - k + 1),
        (c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩).1.val < k
    · let index : Fin (n - k + 1) → AdaptedIndex n L data hn := fun j ↦
        c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩
      let degrees : Fin (n - k + 2) → Fin k :=
        Fin.cons ⟨r, by omega⟩ (fun j ↦ ⟨(index j).1.val, hall j⟩)
      let pieces : ∀ i, FreeMetabelian.Piece (Generator L) (degrees i).val :=
        Fin.cons xᵣ (fun j ↦
          pieceAdaptedBasis n L data hn (index j).1 (index j).2)
      have hinputs : Fin.cons (prLE n L k (by omega) component)
            (fun j : Fin (n - k + 1) ↦
              prLE n L k (by omega)
                (adaptedBasis n L data hn (index j))) =
          fun i ↦ FreeMetabelian.Free.weightIncl
            (degrees i).val (degrees i).isLt (pieces i) := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact hcomponentPrefix
        · change prLE n L k (by omega)
              (adaptedBasis n L data hn (index j)) =
            FreeMetabelian.Free.weightIncl (index j).1.val (hall j)
              (pieceAdaptedBasis n L data hn (index j).1 (index j).2)
          rw [adaptedBasis_apply]
          exact FreeMetabelian.Free.projectPrefix_weightIncl_of_lt
            k (index j).1.val (by omega) (index j).1.isLt (hall j) _
      rw [hedge, SymmetricPower.insert_tprod]
      change T n L data k hk hkn
          (SymmetricPower.tprod ℤ (Fin.cons
            (prLE n L k (by omega) component)
            (fun j : Fin (n - k + 1) ↦
              prLE n L k (by omega)
                (adaptedBasis n L data hn (index j))))) = 0
      rw [hinputs]
      by_contra hT
      obtain ⟨i, hi, _⟩ := T_homogeneous_ne_zero_shape
        n L data k hk hkn degrees pieces hT
      by_cases hi0 : i = 0
      · subst i
        have htop : r = k - 1 := hi.1
        dsimp only [r] at htop
        omega
      · have hzero : r = 0 := by
          simpa only [degrees, Fin.cons_zero] using hi.2 0 (Ne.symm hi0)
        dsimp only [r] at hzero
        omega
    · obtain ⟨j, hj⟩ := not_forall.mp hall
      have hj' : k ≤
          (c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩).1.val :=
        Nat.le_of_not_gt hj
      have hprefix : prLE n L k (by omega)
          (adaptedBasis n L data hn
            (c.left.get ⟨j.val, by simpa only [hlen] using j.isLt⟩)) = 0 := by
        rw [adaptedBasis_apply]
        exact FreeMetabelian.Free.projectPrefix_weightIncl_eq_zero
          k _ (by omega) _ hj' _
      have htprod : SymmetricPower.tprod ℤ
          (fun t : Fin (n - k + 1) ↦
            prLE n L k (by omega)
              (adaptedBasis n L data hn
                (c.left.get ⟨t.val, by simpa only [hlen] using t.isLt⟩))) = 0 :=
        (SymmetricPower.tprod ℤ).map_coord_zero j hprefix
      rw [hedge, htprod, map_zero, map_zero]
  · have hactiveGt : k < c.activeWeight n L data hn := by omega
    have hcomponentPrefix : prLE n L k (by omega) component = 0 := by
      funext i
      change component ⟨i.val, by omega⟩ = 0
      apply RelationContext.component_apply_eq_zero_of_ne
        n L data hn c.context c.root c.mark c.mark_pos
      change i.val + 1 ≠ c.activeWeight n L data hn
      omega
    rw [hedge, hcomponentPrefix, SymmetricPower.insert_zero,
      LinearMap.zero_apply, map_zero]

theorem test_T_componentFactorSum_eq_activeDiagonal
    (cells : ProvenancedCell n L data hn →₀ ℤ)
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) :
    T n L data k hk hkn
        (cells.sum (fun c z ↦ z •
          if hlen : c.left.length = n - k + 1 then
            c.factorEdge n L data hn (n - k + 2) k (by omega)
          else 0)) =
      T n L data k hk hkn
        (cells.sum (fun c z ↦ z •
          if hlen : c.left.length = n - k + 1 then
            if hactive : c.activeWeight n L data hn = k then
              c.factorEdge n L data hn (n - k + 2) k (by omega)
            else 0
          else 0)) := by
  classical
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  rw [map_zsmul, map_zsmul]
  congr 1
  by_cases hlen : c.left.length = n - k + 1
  · rw [dif_pos hlen, dif_pos hlen]
    by_cases hactive : c.activeWeight n L data hn = k
    · rw [dif_pos hactive]
    · rw [dif_neg hactive, map_zero]
      by_cases hone : c.activeWeight n L data hn = 1
      · exact test_T_factorEdge_eq_zero_of_activeWeight_one
          n L data hn c k hk hkn hlen hone
      · apply test_T_factorEdge_eq_zero_of_activeWeight_gt_one_ne
          n L data hn c k hk hkn hlen (by
            have hp := c.mark_pos
            simp only [ProvenancedCell.activeWeight]
            simp only [ProvenancedCell.activeWeight] at hone
            omega) hactive
  · rw [dif_neg hlen, dif_neg hlen]

end

end LieRings.MetabelianVanishing
