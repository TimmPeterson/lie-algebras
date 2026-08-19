import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmithStokes

/-!
# Feeding an arbitrary terminal relation word to the Smith collector

The terminal Smith collector is formulated row by row.  This file supplies
the missing finite input expansion: an arbitrary element of `D_n`, followed
by an arbitrary enveloping-algebra multiplier, is expanded in the relation
Smith basis and the ambient PBW basis.  Every resulting row still has one
genuine `D_n` basis mark.  Consequently the factor-two frontier gives an
actual chain in the terminal source presentation.

This construction is deliberately independent of the raw-cutoff ledger.  In
particular it does not define a chain as a difference of two already known
boundaries.
-/

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance terminalSmithContinuationFintype : Fintype L :=
  Fintype.ofFinite L

/-- The ordered terminal-Smith word represented by a PBW exponent vector. -/
def terminalSmithExponentWord
    (e : TerminalSmithIndex n L data hn →₀ ℕ) :
    List (TerminalSmithIndex n L data hn) :=
  (Finsupp.toMultiset e).sort (· ≤ ·)

theorem terminalSmithExponentWord_pairwise
    (e : TerminalSmithIndex n L data hn →₀ ℕ) :
    (terminalSmithExponentWord n L data hn e).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort _ _

/-- Finite family of genuinely marked Smith rows representing `ι(d) * u`.
The relation and ambient PBW coordinate expansions are performed only once,
at the input of the already verified terminal collector. -/
def terminalSmithRowsOfRelationRightFactor
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    TerminalSmithRow n L data hn →₀ ℤ :=
  ((terminalSmith n L data hn).relationBasis.repr d).sum fun i a ↦
    ((LieRings.PBW.orderedPBWEquiv
      (terminalSmith n L data hn).ambientBasis).symm u).sum fun e z ↦
        Finsupp.single
          (⟨i, [], terminalSmithExponentWord n L data hn e⟩ :
            TerminalSmithRow n L data hn) (a * z)

private theorem terminalSmithAmbientWord_exponentWord
    (e : TerminalSmithIndex n L data hn →₀ ℕ) :
    TerminalSmithRow.ambientWord n L data hn
        (terminalSmithExponentWord n L data hn e) =
      LieRings.PBW.orderedMonomial ℤ (A L n)
        (TerminalSmithIndex n L data hn)
        (terminalSmith n L data hn).ambientBasis e := by
  simp [TerminalSmithRow.ambientWord, terminalSmithExponentWord,
    LieRings.PBW.basisWord, LieRings.PBW.orderedMonomial,
    LieRings.PBW.word, List.map_map, Function.comp_def]

/-- Exact UEA evaluation of the terminal input family. -/
theorem evaluate_terminalSmithRowsOfRelationRightFactor
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    (terminalSmithCollector n L data hn).evaluate
        (terminalSmithRowsOfRelationRightFactor n L data hn d u) =
      UniversalEnvelopingAlgebra.ι ℤ (d : A L n) * u := by
  classical
  let RB := (terminalSmith n L data hn).relationBasis
  let AB := (terminalSmith n L data hn).ambientBasis
  let P := LieRings.PBW.orderedPBWEquiv AB
  have hu : (P.symm u).sum (fun e z ↦ z •
      LieRings.PBW.orderedMonomial ℤ (A L n)
        (TerminalSmithIndex n L data hn) AB e) = u := by
    have hsum : (P.symm u).sum (fun e z ↦ MvPolynomial.monomial e z) =
        P.symm u := by
      simpa only [MvPolynomial.monomial] using Finsupp.sum_single (P.symm u)
    calc
      _ = (P.symm u).sum (fun e z ↦
          P (MvPolynomial.monomial e z)) := by
        apply Finsupp.sum_congr
        intro e he
        rw [LieRings.PBW.orderedPBWEquiv_monomial]
      _ = P ((P.symm u).sum (fun e z ↦
          MvPolynomial.monomial e z)) := by rw [map_finsuppSum]
      _ = P (P.symm u) := by rw [hsum]
      _ = u := P.apply_symm_apply u
  have hd : (RB.repr d).sum (fun i a ↦ a • (RB i : A L n)) =
      (d : A L n) := by
    rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
    change ∑ i, (D n L data n (by omega)).subtype
        ((RB.repr d i) • RB i) = (D n L data n (by omega)).subtype d
    rw [← map_sum, RB.sum_repr]
  rw [terminalSmithRowsOfRelationRightFactor, map_finsuppSum]
  calc
    _ = (RB.repr d).sum (fun i a ↦
        (P.symm u).sum (fun e z ↦ (a * z) •
          (UniversalEnvelopingAlgebra.ι ℤ (RB i : A L n) *
            LieRings.PBW.orderedMonomial ℤ (A L n)
              (TerminalSmithIndex n L data hn) AB e))) := by
      apply Finsupp.sum_congr
      intro i hi
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro e he
      rw [LieRings.DegreeFive.FiniteTaggedCollector.evaluate_single]
      change ((RB.repr d i) * (P.symm u e)) •
          TerminalSmithRow.value n L data hn
            ⟨i, [], terminalSmithExponentWord n L data hn e⟩ =
        ((RB.repr d i) * (P.symm u e)) •
          (UniversalEnvelopingAlgebra.ι ℤ (RB i : A L n) *
            LieRings.PBW.orderedMonomial ℤ (A L n)
              (TerminalSmithIndex n L data hn) AB e)
      congr 1
      simp only [TerminalSmithRow.value, List.nil_append]
      rw [show TerminalSmithRow.ambientWord n L data hn [] = 1 by
        simp [TerminalSmithRow.ambientWord, LieRings.PBW.basisWord]]
      rw [one_mul, terminalSmithAmbientWord_exponentWord]
    _ = (RB.repr d).sum (fun i a ↦ a •
        (UniversalEnvelopingAlgebra.ι ℤ (RB i : A L n) * u)) := by
      apply Finsupp.sum_congr
      intro i hi
      calc
        (P.symm u).sum (fun e z ↦ ((RB.repr d i) * z) •
            (UniversalEnvelopingAlgebra.ι ℤ (RB i : A L n) *
              LieRings.PBW.orderedMonomial ℤ (A L n)
                (TerminalSmithIndex n L data hn) AB e)) =
          (RB.repr d i) • (UniversalEnvelopingAlgebra.ι ℤ (RB i : A L n) *
            (P.symm u).sum (fun e z ↦ z •
              LieRings.PBW.orderedMonomial ℤ (A L n)
                (TerminalSmithIndex n L data hn) AB e)) := by
          rw [Finsupp.mul_sum, Finsupp.smul_sum]
          apply Finsupp.sum_congr
          intro e he
          rw [mul_smul_comm, smul_smul]
        _ = _ := by rw [hu]
    _ = ((RB.repr d).sum (fun i a ↦ a •
          UniversalEnvelopingAlgebra.ι ℤ (RB i : A L n))) * u := by
      rw [Finsupp.sum_mul]
      apply Finsupp.sum_congr
      intro i hi
      rw [smul_mul_assoc]
    _ = UniversalEnvelopingAlgebra.ι ℤ
          ((RB.repr d).sum (fun i a ↦ a • (RB i : A L n))) * u := by
      rw [map_finsuppSum]
      apply congrArg (fun x ↦ x * u)
      apply Finsupp.sum_congr
      intro i hi
      rw [map_zsmul]
    _ = _ := by rw [hd]

/-- Every input row has ordered ordinary neighbours. -/
theorem terminalSmithRowsOfRelationRightFactor_neighbors_pairwise
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n))
    (r : TerminalSmithRow n L data hn)
    (hr : terminalSmithRowsOfRelationRightFactor n L data hn d u r ≠ 0) :
    (r.left ++ r.right).Pairwise (· ≤ ·) := by
  classical
  rw [terminalSmithRowsOfRelationRightFactor, Finsupp.sum_apply] at hr
  have hexists : ∃ i ∈
      ((terminalSmith n L data hn).relationBasis.repr d).support,
      (((LieRings.PBW.orderedPBWEquiv
        (terminalSmith n L data hn).ambientBasis).symm u).sum fun e z ↦
          Finsupp.single
            (⟨i, [], terminalSmithExponentWord n L data hn e⟩ :
              TerminalSmithRow n L data hn)
            (((terminalSmith n L data hn).relationBasis.repr d i) * z)) r ≠
        0 := by
    by_contra h
    push Not at h
    exact hr (Finset.sum_eq_zero fun i hi ↦ h i hi)
  obtain ⟨i, hi, hir⟩ := hexists
  rw [Finsupp.sum_apply] at hir
  have he : ∃ e ∈ ((LieRings.PBW.orderedPBWEquiv
      (terminalSmith n L data hn).ambientBasis).symm u).support,
      (Finsupp.single
          (⟨i, [], terminalSmithExponentWord n L data hn e⟩ :
            TerminalSmithRow n L data hn)
          (((terminalSmith n L data hn).relationBasis.repr d i) *
            ((LieRings.PBW.orderedPBWEquiv
              (terminalSmith n L data hn).ambientBasis).symm u e))) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hir (Finset.sum_eq_zero fun e he ↦ h e he)
  obtain ⟨e, he, her⟩ := he
  have hre : r = ⟨i, [], terminalSmithExponentWord n L data hn e⟩ := by
    by_contra hne
    simp [Finsupp.single_apply, hne] at her
  subst r
  simpa using terminalSmithExponentWord_pairwise n L data hn e

/-- Factor-two chain obtained by collecting every row of the finite terminal
input family. -/
def terminalSmithRelationRightFactorChain
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    Koszul.One (terminalSourcePresentation n L data hn) 1 :=
  (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum fun r z ↦
    z • terminalSmithFactorTwoChain n L data hn r

/-- The independently generated chain has boundary equal to the terminal
Smith factor-two symbol of the complete projected relation word. -/
theorem dOne_terminalSmithRelationRightFactorChain
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    Koszul.dOne (terminalSourcePresentation n L data hn) 1
        (terminalSmithRelationRightFactorChain n L data hn d u) =
      LieRings.PBW.factorSymbol
        (terminalSmith n L data hn).ambientBasis 2
        (UniversalEnvelopingAlgebra.ι ℤ (d : A L n) * u) := by
  classical
  rw [terminalSmithRelationRightFactorChain, map_finsuppSum]
  calc
    _ = (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
        (fun r z ↦ z • LieRings.PBW.factorSymbol
          (terminalSmith n L data hn).ambientBasis 2
          (r.value n L data hn)) := by
      apply Finsupp.sum_congr
      intro r hr
      rw [map_zsmul,
        dOne_terminalSmithFactorTwoChain_eq_factorSymbol n L data hn r
          (terminalSmithRowsOfRelationRightFactor_neighbors_pairwise
            n L data hn d u r (Finsupp.mem_support_iff.mp hr))]
      rfl
    _ = LieRings.PBW.factorSymbol
          (terminalSmith n L data hn).ambientBasis 2
          ((terminalSmithCollector n L data hn).evaluate
            (terminalSmithRowsOfRelationRightFactor n L data hn d u)) := by
      change (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
          (fun r z ↦ z • LieRings.PBW.factorSymbol
            (terminalSmith n L data hn).ambientBasis 2
            (r.value n L data hn)) =
        LieRings.PBW.factorSymbol
          (terminalSmith n L data hn).ambientBasis 2
          ((terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
            (fun r z ↦ z • r.value n L data hn))
      rw [map_finsuppSum]
      simp only [map_zsmul]
    _ = _ := by
      rw [evaluate_terminalSmithRowsOfRelationRightFactor]

/-! ## Exact primitive read of the collected terminal family -/

/-- Literal full-lift factor-two frontier word of the complete input family. -/
def terminalSmithRelationRightFactorFullLiftWord
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    UEA ℤ (FreeModel n L) :=
  (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum fun r z ↦
    z • terminalSmithFactorTwoFullLiftWordRows n L data hn
      (terminalSmithFactorTwoFrontier n L data hn r)

/-- Sum of the genuine placement relations in the same frontier. -/
def terminalSmithRelationRightFactorPlacementRelation
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    Relations n L data :=
  (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum fun r z ↦
    z • terminalSmithFactorTwoPlacementCorrectionRows n L data hn
      (terminalSmithFactorTwoFrontier n L data hn r)

/-- Exact source primitive of the independently generated terminal chain.
No comparison with an external full lift is hidden in this statement. -/
theorem terminalSourcePrimitive_terminalSmithRelationRightFactorChain
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    terminalSourcePrimitive n L data hn
        (terminalSmithRelationRightFactorChain n L data hn d u) =
      pbwPrimitive n L data hn
          (terminalSmithRelationRightFactorFullLiftWord n L data hn d u) +
        (terminalSmithRelationRightFactorPlacementRelation
          n L data hn d u : FreeModel n L) := by
  classical
  rw [terminalSmithRelationRightFactorChain,
    terminalSmithRelationRightFactorFullLiftWord,
    terminalSmithRelationRightFactorPlacementRelation,
    map_finsuppSum, map_finsuppSum]
  simp_rw [map_zsmul]
  have hcoe :
      ((terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
          (fun r z ↦ z •
            terminalSmithFactorTwoPlacementCorrectionRows n L data hn
              (terminalSmithFactorTwoFrontier n L data hn r)) :
            Relations n L data) =
        (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
          (fun r z ↦ z •
            (terminalSmithFactorTwoPlacementCorrectionRows n L data hn
              (terminalSmithFactorTwoFrontier n L data hn r) :
                FreeModel n L)) := by
    change (Relations n L data).subtype
        ((terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
          (fun r z ↦ z •
            terminalSmithFactorTwoPlacementCorrectionRows n L data hn
              (terminalSmithFactorTwoFrontier n L data hn r))) = _
    rw [map_finsuppSum]
    rfl
  rw [hcoe]
  change (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
      (fun r z ↦ z • terminalSourcePrimitive n L data hn
        (terminalSmithFactorTwoChain n L data hn r)) =
    (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
        (fun r z ↦ z • pbwPrimitive n L data hn
          (terminalSmithFactorTwoFullLiftWordRows n L data hn
            (terminalSmithFactorTwoFrontier n L data hn r))) +
      (terminalSmithRowsOfRelationRightFactor n L data hn d u).sum
        (fun r z ↦ z •
          (terminalSmithFactorTwoPlacementCorrectionRows n L data hn
            (terminalSmithFactorTwoFrontier n L data hn r) : FreeModel n L))
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro r hr
  rw [terminalSourcePrimitive_terminalSmithFactorTwoChain n L data hn r,
    smul_add]

end

end LieRings.MetabelianVanishing
