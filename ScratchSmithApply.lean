import LieRings.DimensionSubring.MetabelianVanishing.CompleteFactorTwoPrimitiveBridge
import LieRings.DimensionSubring.MetabelianVanishing.TerminalSmithCollector

namespace LieRings.MetabelianVanishing

open FreeMetabelian TensorProduct LieRings.PBW

universe u

noncomputable section

set_option maxHeartbeats 4000000

variable (n : ℕ) (L : Type u) [LieRing L] [Finite L]
variable (data : CyclicTopData n L)
variable (hn : 2 ≤ n)

local instance scratchSmithFintype : Fintype L := Fintype.ofFinite L

theorem scratch_projectPrefix_lie
    (x y : FreeModel n L) :
    prLE n L n (by omega) ⁅x, y⁆ =
      ⁅prLE n L n (by omega) x, prLE n L n (by omega) y⁆ := by
  funext i
  rcases i with ⟨(_ | _ | q), hi⟩ <;> rfl

def scratchPrLELieHom :
    FreeModel n L →ₗ⁅ℤ⁆ A L n where
  toLinearMap := prLE n L n (by omega)
  map_lie' := by
    intro x y
    exact scratch_projectPrefix_lie n L x y

def scratchPrLEUEA :
    UEA ℤ (FreeModel n L) →ₐ[ℤ] UEA ℤ (A L n) :=
  UEA.map ℤ (FreeModel n L) (A L n) (scratchPrLELieHom n L)

@[simp] theorem scratchPrLEUEA_iota (x : FreeModel n L) :
    scratchPrLEUEA n L (UniversalEnvelopingAlgebra.ι ℤ x) =
      UniversalEnvelopingAlgebra.ι ℤ (prLE n L n (by omega) x) := by
  exact UEA.map_ι ℤ (FreeModel n L) (A L n)
    (scratchPrLELieHom n L) x

/-- Unweighted integral PBW coordinates in the terminal ambient Smith basis. -/
def terminalAmbientPBWEquiv :
    MvPolynomial (TerminalSmithIndex n L data hn) ℤ ≃ₗ[ℤ]
      UEA ℤ (A L n) :=
  LinearEquiv.ofBijective
    (orderedPBWMap ℤ (A L n) (TerminalSmithIndex n L data hn)
      (terminalSmith n L data hn).ambientBasis)
    (freeModulePBW_int (A L n) (TerminalSmithIndex n L data hn)
      (terminalSmith n L data hn).ambientBasis)

@[simp] theorem terminalAmbientPBWEquiv_monomial
    (e : TerminalSmithIndex n L data hn →₀ ℕ) (z : ℤ) :
    terminalAmbientPBWEquiv n L data hn (MvPolynomial.monomial e z) =
      z • orderedMonomial ℤ (A L n) (TerminalSmithIndex n L data hn)
        (terminalSmith n L data hn).ambientBasis e := by
  exact orderedPBWMap_monomial ℤ (A L n)
    (TerminalSmithIndex n L data hn)
    (terminalSmith n L data hn).ambientBasis e z

def terminalSmithExponentWord
    (e : TerminalSmithIndex n L data hn →₀ ℕ) :
    List (TerminalSmithIndex n L data hn) :=
  (Finsupp.toMultiset e).sort (· ≤ ·)

theorem terminalSmithExponentWord_pairwise
    (e : TerminalSmithIndex n L data hn →₀ ℕ) :
    (terminalSmithExponentWord n L data hn e).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort _ _

/-- Expand one terminal relation vector followed by an arbitrary terminal
ambient UEA multiplier into source-Smith rows. -/
def terminalSmithRowsOfRelationMultiplier
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    TerminalSmithRow n L data hn →₀ ℤ :=
  ((terminalSmith n L data hn).relationBasis.repr d).sum (fun i zi ↦
    ((terminalAmbientPBWEquiv n L data hn).symm u).sum (fun e ze ↦
      Finsupp.single
        (⟨i, [], terminalSmithExponentWord n L data hn e⟩ :
          TerminalSmithRow n L data hn) (zi * ze)))

theorem evaluate_terminalSmithRowsOfRelationMultiplier
    (d : D n L data n (by omega)) (u : UEA ℤ (A L n)) :
    (terminalSmithCollector n L data hn).evaluate
        (terminalSmithRowsOfRelationMultiplier n L data hn d u) =
      UniversalEnvelopingAlgebra.ι ℤ (d : A L n) * u := by
  classical
  let S := terminalSmith n L data hn
  let B := terminalAmbientPBWEquiv n L data hn
  change Finsupp.linearCombination ℤ (TerminalSmithRow.value n L data hn)
      ((S.relationBasis.repr d).sum (fun i zi ↦
        (B.symm u).sum (fun e ze ↦
          Finsupp.single
            (⟨i, [], terminalSmithExponentWord n L data hn e⟩ :
              TerminalSmithRow n L data hn) (zi * ze)))) = _
  rw [map_finsuppSum]
  have hu : (B.symm u).sum (fun e ze ↦ ze •
      orderedMonomial ℤ (A L n) (TerminalSmithIndex n L data hn)
        S.ambientBasis e) = u := by
    have hsum : (B.symm u).sum
        (fun e ze ↦ MvPolynomial.monomial e ze) = B.symm u := by
      simpa only [MvPolynomial.monomial] using
        (Finsupp.sum_single (B.symm u))
    calc
      _ = (B.symm u).sum (fun e ze ↦
          B (MvPolynomial.monomial e ze)) := by
            apply Finsupp.sum_congr
            intro e he
            rw [terminalAmbientPBWEquiv_monomial]
      _ = B ((B.symm u).sum
          (fun e ze ↦ MvPolynomial.monomial e ze)) := by
            rw [map_finsuppSum]
      _ = B (B.symm u) := by rw [hsum]
      _ = u := B.apply_symm_apply u
  calc
    _ = (S.relationBasis.repr d).sum (fun i zi ↦ zi •
        (UniversalEnvelopingAlgebra.ι ℤ (S.relationBasis i : A L n) * u)) := by
      apply Finsupp.sum_congr
      intro i hi
      rw [map_finsuppSum]
      simp only [Finsupp.linearCombination_single]
      calc
        _ = (B.symm u).sum (fun e ze ↦
            ((S.relationBasis.repr d) i) • (ze •
            (UniversalEnvelopingAlgebra.ι ℤ (S.relationBasis i : A L n) *
              orderedMonomial ℤ (A L n)
                (TerminalSmithIndex n L data hn) S.ambientBasis e))) := by
          apply Finsupp.sum_congr
          intro e he
          rw [mul_smul]
          congr 2
          simp [TerminalSmithRow.value, TerminalSmithRow.ambientWord,
            terminalSmithExponentWord, LieRings.PBW.basisWord,
            LieRings.PBW.orderedMonomial, LieRings.PBW.word,
            Function.comp_def, S]
        _ = ((S.relationBasis.repr d) i) •
            (UniversalEnvelopingAlgebra.ι ℤ
              (S.relationBasis i : A L n) *
            (B.symm u).sum (fun e ze ↦ ze •
              orderedMonomial ℤ (A L n)
                (TerminalSmithIndex n L data hn) S.ambientBasis e)) := by
          rw [Finsupp.mul_sum, Finsupp.smul_sum]
          apply Finsupp.sum_congr
          intro e he
          rw [mul_smul_comm]
        _ = _ := by rw [hu]
    _ = UniversalEnvelopingAlgebra.ι ℤ
          ((S.relationBasis.repr d).sum (fun i zi ↦ zi •
            (S.relationBasis i : A L n))) * u := by
      rw [map_finsuppSum, Finsupp.sum_mul]
      apply Finsupp.sum_congr
      intro i hi
      rw [map_zsmul, smul_mul_assoc]
    _ = _ := by
      rw [show (S.relationBasis.repr d).sum (fun i zi ↦ zi •
          (S.relationBasis i : A L n)) = (d : A L n) by
        rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
        have h := congrArg (D n L data n (by omega)).subtype
          (S.relationBasis.sum_repr d)
        simpa only [map_sum, map_zsmul] using h]

def GoverningWitness.terminalSmithInitial {a : L}
    (w : GoverningWitness n L data a) :
    TerminalSmithRow n L data hn →₀ ℤ :=
  w.relationCoefficients.sum (fun p z ↦ z •
    terminalSmithRowsOfRelationMultiplier n L data hn
      ⟨relationPrefix n L data n (by omega) p.1, ⟨p.1, rfl⟩⟩
      (scratchPrLEUEA n L p.2))

theorem GoverningWitness.evaluate_terminalSmithInitial {a : L}
    (w : GoverningWitness n L data a) :
    (terminalSmithCollector n L data hn).evaluate
        (w.terminalSmithInitial n L data hn) =
      scratchPrLEUEA n L w.theta := by
  classical
  rw [GoverningWitness.terminalSmithInitial, map_finsuppSum,
    GoverningWitness.theta, map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, map_zsmul,
    evaluate_terminalSmithRowsOfRelationMultiplier]
  congr 1
  rw [map_mul, scratchPrLEUEA_iota]
  rfl

end

end LieRings.MetabelianVanishing
