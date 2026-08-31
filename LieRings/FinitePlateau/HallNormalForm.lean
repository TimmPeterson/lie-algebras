import LieRings.FinitePlateau.TopLayer
import LieRings.FinitePlateau.MagnusCoordinateReads
import LieRings.FinitePlateau.TopMinusOneMagnus
import LieRings.DimensionSubring.MetabelianTwoFactor

/-!
# The filtered Hall normal form in the critical degree

This file isolates the augmentation-sensitive part of the finite-plateau
calculation.  It is important that the statements below retain membership in
`dimensionSubring`; the corresponding assertion for arbitrary central
two-torsion elements is false, because the presentation has lower-weight
torsion Hall coordinates.
-/

namespace LieRings.FinitePlateau

noncomputable section

open scoped BigOperators

/-- The literal graded Hall index of the relatively free source.  This index
remembers the occurrences of the five manuscript generators in each Hall word. -/
abbrev CriticalHallIndex (N : ℕ) :=
  (s : Fin (N + 3)) × FreeMetabelian.Free.PieceIndex Generator s.val

/-- A fixed order on the finite literal Hall index.  It supplies the finite
enumeration used in the Hall-basis coordinate sums below. -/
noncomputable instance criticalHallIndexLinearOrder (N : ℕ) :
    LinearOrder (CriticalHallIndex N) :=
  LinearOrder.lift' (Finite.equivFin (CriticalHallIndex N))
    (Finite.equivFin (CriticalHallIndex N)).injective

@[simp] private theorem criticalHallGradedBasis_apply (N : ℕ)
    (p : CriticalHallIndex N) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis p =
      FreeMetabelian.Free.incl p.1
        (FreeMetabelian.Free.pieceBasis generatorBasis p.1.val p.2) := by
  classical
  rw [FreeMetabelian.Free.hallGradedBasis]
  let bPi := Pi.basis (fun i : Fin (N + 3) ↦
    FreeMetabelian.Free.pieceBasis generatorBasis i.val)
  have he : bPi.equivFun.toAddEquiv.toIntLinearEquiv = bPi.equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv bPi.equivFun
  rw [he, Module.Basis.ofEquivFun_equivFun, Pi.basis_apply]
  ext s
  by_cases hs : s = p.1
  · subst s
    simp [FreeMetabelian.Free.incl]
  · simp [FreeMetabelian.Free.incl, Pi.single_eq_of_ne hs]

private theorem criticalHallGradedBasis_repr_apply (N : ℕ)
    (z : Source N) (p : CriticalHallIndex N) :
    (FreeMetabelian.Free.hallGradedBasis generatorBasis).repr z p =
      (FreeMetabelian.Free.pieceBasis generatorBasis p.1.val).repr
        (z p.1) p.2 := by
  classical
  rw [FreeMetabelian.Free.hallGradedBasis]
  let bPi := Pi.basis (fun i : Fin (N + 3) ↦
    FreeMetabelian.Free.pieceBasis generatorBasis i.val)
  have he : bPi.equivFun.toAddEquiv.toIntLinearEquiv = bPi.equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv bPi.equivFun
  rw [he, Module.Basis.ofEquivFun_equivFun]
  rfl

@[simp] theorem gradedCoordinate_sourceGenerator
    (N : ℕ) (j k : Generator) :
    gradedCoordinate N
        (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N)
        (sourceGenerator N k) =
      if j = k then 1 else 0 := by
  have hk : sourceGenerator N k =
      FreeMetabelian.Free.hallGradedBasis generatorBasis
        (⟨⟨0, by omega⟩, k⟩ : CriticalHallIndex N) := by
    rw [criticalHallGradedBasis_apply]
    rfl
  rw [hk]
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl, gradedCoordinate_hallGradedBasis_self]
  · rw [if_neg hjk, gradedCoordinate_hallGradedBasis_of_ne]
    intro he
    apply hjk
    cases he
    rfl

/-! ## The exact shifted-row Hall ledger -/

/-- The leading coefficient of the shifted row indexed by `i`. -/
def hallRowScale : Fin 3 → ℤ
  | 0 => 4
  | 1 => 16
  | 2 => 64

/-- The high-weight tail of the shifted row indexed by `i`. -/
def hallRowTail (N : ℕ) : Fin 3 → Source N
  | 0 => (2 : ℤ) • c3Source N + c2Source N
  | 1 => (4 : ℤ) • c3Source N - c1Source N
  | 2 => -((4 : ℤ) • c2Source N) - (2 : ℤ) • c1Source N

/-- The full shifted row, without discarding its high-weight tail. -/
def hallShiftedRow (N : ℕ) (i : Fin 3) : Source N :=
  hallRowScale i • smallSourceGenerator N i + hallRowTail N i

@[simp] theorem hallShiftedRow_zero (N : ℕ) :
    hallShiftedRow N 0 = r1Source N := by
  simp only [hallShiftedRow, hallRowScale, hallRowTail,
    smallSourceGenerator_zero, r1Source]
  module

@[simp] theorem hallShiftedRow_one (N : ℕ) :
    hallShiftedRow N 1 = r2Source N := by
  simp only [hallShiftedRow, hallRowScale, hallRowTail,
    smallSourceGenerator_one, r2Source]
  module

@[simp] theorem hallShiftedRow_two (N : ℕ) :
    hallShiftedRow N 2 = r3Source N := by
  simp only [hallShiftedRow, hallRowScale, hallRowTail,
    smallSourceGenerator_two, r3Source]
  module

theorem hallShiftedRow_mem_relationIdeal (N : ℕ) (i : Fin 3) :
    hallShiftedRow N i ∈ relationIdeal N := by
  apply mem_relationIdeal_of_mem_definingRelators
  fin_cases i <;> simp [definingRelators]

/-- A literal integral combination of the three *full* shifted rows. -/
def hallShiftedRowCombination (N : ℕ) (A : Fin 3 → ℤ) : Source N :=
  ∑ i, A i • hallShiftedRow N i

theorem hallShiftedRowCombination_mem_relationIdeal
    (N : ℕ) (A : Fin 3 → ℤ) :
    hallShiftedRowCombination N A ∈ relationIdeal N := by
  apply Submodule.sum_mem
  intro i hi
  exact (relationIdeal N).smul_mem (A i)
    (hallShiftedRow_mem_relationIdeal N i)

/-- Subtract the whole row combination selected by the weight-one
coordinates.  Keeping the high tails here is the essential coupling that
the invalid factor-number splitting had lost. -/
def reduceByHallShiftedRows (N : ℕ) (A : Fin 3 → ℤ)
    (x : Source N) : Source N :=
  x - hallShiftedRowCombination N A

@[simp] theorem quotientMap_reduceByHallShiftedRows
    (N : ℕ) (A : Fin 3 → ℤ) (x : Source N) :
    quotientMap N (reduceByHallShiftedRows N A x) = quotientMap N x := by
  rw [reduceByHallShiftedRows, map_sub]
  have hzero : quotientMap N (hallShiftedRowCombination N A) = 0 :=
    (LieSubmodule.Quotient.mk_eq_zero' (N := relationIdeal N)).mpr
      (hallShiftedRowCombination_mem_relationIdeal N A)
  rw [hzero, sub_zero]

private theorem rightBracketPow_mem_source_lowerCentralSeries
    (N r : ℕ) :
    rightBracketPow (x4Source N) (x5Source N) r ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [rightBracketPow_succ]
      have hrev : ⁅x5Source N,
          rightBracketPow (x4Source N) (x5Source N) r⁆ ∈
          LieModule.lowerCentralSeries ℤ (Source N) (Source N) (r + 1) := by
        rw [LieModule.lowerCentralSeries_succ]
        exact LieSubmodule.lie_mem_lie (by simp) ih
      rw [← lie_skew]
      exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (r + 1)).neg_mem hrev

private theorem cSource_mem_source_lowerCentralSeries
    (N : ℕ) (i : Fin 3) :
    cSource N i ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1) := by
  rw [cSource]
  have hrev : ⁅smallSourceGenerator N i, tSource N⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp)
      (by simpa [tSource] using
        rightBracketPow_mem_source_lowerCentralSeries N N)
  rw [← lie_skew]
  exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).neg_mem hrev

private theorem hallRowTail_mem_source_lowerCentralSeries
    (N : ℕ) (i : Fin 3) :
    hallRowTail N i ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1) := by
  fin_cases i
  · exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).add_mem
      ((LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).smul_mem
        2 (cSource_mem_source_lowerCentralSeries N 2))
      (cSource_mem_source_lowerCentralSeries N 1)
  · exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).sub_mem
      ((LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).smul_mem
        4 (cSource_mem_source_lowerCentralSeries N 2))
      (cSource_mem_source_lowerCentralSeries N 0)
  · exact (LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).sub_mem
      ((LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).neg_mem
        ((LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).smul_mem
          4 (cSource_mem_source_lowerCentralSeries N 1)))
      ((LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 1)).smul_mem
        2 (cSource_mem_source_lowerCentralSeries N 0))

private theorem gradedCoordinate_hallRowTail_generator_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    gradedCoordinate N
        (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N)
        (hallRowTail N i) = 0 := by
  have htail := FreeMetabelian.Free.lowerCentralSeries_le_tail (N + 1)
    (hallRowTail_mem_source_lowerCentralSeries N i)
  rw [gradedCoordinate, Module.Basis.coord_apply,
    criticalHallGradedBasis_repr_apply]
  change (FreeMetabelian.Free.pieceBasis generatorBasis 0).repr
      (hallRowTail N i (⟨0, by omega⟩ : Fin (N + 3))) j = 0
  rw [htail (⟨0, by omega⟩ : Fin (N + 3)) (by simp), map_zero]
  rfl

@[simp] theorem gradedCoordinate_hallShiftedRow_generator
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    gradedCoordinate N
        (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N)
        (hallShiftedRow N i) =
      if j = smallGeneratorIndex i then hallRowScale i else 0 := by
  rw [hallShiftedRow, map_add, map_zsmul,
    gradedCoordinate_hallRowTail_generator_eq_zero N hN]
  change hallRowScale i *
      gradedCoordinate N
        (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N)
        (sourceGenerator N (smallGeneratorIndex i)) + 0 = _
  rw [gradedCoordinate_sourceGenerator]
  by_cases hj : j = smallGeneratorIndex i <;> simp [hj]

/-- Divisible small-generator coordinates can be removed by subtracting
the corresponding *full* shifted rows.  The two outer coordinates are
assumed zero.  The quotient class is unchanged, and every weight-one Hall
coordinate of the resulting lift is literally zero. -/
theorem exists_reduceByHallShiftedRows_generator_coordinates_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (x : Source N)
    (hsmall : ∀ i : Fin 3,
      hallRowScale i ∣
        gradedCoordinate N
          (⟨⟨0, by omega⟩, smallGeneratorIndex i⟩ : CriticalHallIndex N) x)
    (houterZero : ∀ j : Generator,
      (∀ i : Fin 3, j ≠ smallGeneratorIndex i) →
        gradedCoordinate N
          (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N) x = 0) :
    ∃ A : Fin 3 → ℤ,
      quotientMap N (reduceByHallShiftedRows N A x) = quotientMap N x ∧
      ∀ j : Generator,
        gradedCoordinate N
          (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N)
          (reduceByHallShiftedRows N A x) = 0 := by
  choose A hA using hsmall
  refine ⟨A, quotientMap_reduceByHallShiftedRows N A x, ?_⟩
  intro j
  rw [reduceByHallShiftedRows, map_sub, hallShiftedRowCombination, map_sum]
  simp only [map_zsmul,
    gradedCoordinate_hallShiftedRow_generator N hN]
  fin_cases j
  · have hout := houterZero 0 (by
      intro i
      fin_cases i <;> simp [smallGeneratorIndex])
    change gradedCoordinate N
        (⟨⟨0, by omega⟩, (0 : Generator)⟩ : CriticalHallIndex N) x - _ = 0
    rw [hout]
    norm_num [Fin.sum_univ_succ, smallGeneratorIndex, hallRowScale]
  · have h := hA 0
    change gradedCoordinate N
        (⟨⟨0, by omega⟩, (1 : Generator)⟩ : CriticalHallIndex N) x - _ = 0
    rw [show (1 : Generator) = smallGeneratorIndex 0 by rfl, h]
    norm_num [Fin.sum_univ_succ, smallGeneratorIndex, hallRowScale]
    ring
  · have h := hA 1
    change gradedCoordinate N
        (⟨⟨0, by omega⟩, (2 : Generator)⟩ : CriticalHallIndex N) x - _ = 0
    rw [show (2 : Generator) = smallGeneratorIndex 1 by rfl, h]
    norm_num [Fin.sum_univ_succ, smallGeneratorIndex, hallRowScale]
    ring
  · have h := hA 2
    change gradedCoordinate N
        (⟨⟨0, by omega⟩, (3 : Generator)⟩ : CriticalHallIndex N) x - _ = 0
    rw [show (3 : Generator) = smallGeneratorIndex 2 by rfl, h]
    norm_num [Fin.sum_univ_succ, smallGeneratorIndex, hallRowScale]
    ring
  · have hout := houterZero 4 (by
      intro i
      fin_cases i <;> simp [smallGeneratorIndex])
    change gradedCoordinate N
        (⟨⟨0, by omega⟩, (4 : Generator)⟩ : CriticalHallIndex N) x - _ = 0
    rw [hout]
    norm_num [Fin.sum_univ_succ, smallGeneratorIndex, hallRowScale]

/-- Every critical class has a source lift whose complete weight-one Hall
part is zero.  The divisibilities and outer zeroes come from the descended
masked Magnus probes; the lift is then changed only by full defining rows.
-/
theorem exists_critical_lift_generator_coordinates_eq_zero
    (N : ℕ) (hN : 1 ≤ N) {z : L N}
    (hz : z ∈ dimensionSubring ℤ (L N) (N + 4)) :
    ∃ x : Source N,
      quotientMap N x = z ∧
      quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4) ∧
      ∀ j : Generator,
        gradedCoordinate N
          (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N) x = 0 := by
  obtain ⟨x, hx⟩ := quotientMap_surjective N z
  have hxcritical :
      quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4) := by
    rwa [hx]
  have hsmall : ∀ i : Fin 3,
      hallRowScale i ∣
        gradedCoordinate N
          (⟨⟨0, by omega⟩, smallGeneratorIndex i⟩ : CriticalHallIndex N) x := by
    intro i
    have hactive : MagnusMasks.Active i (smallGeneratorIndex i) := by
      fin_cases i <;> simp [MagnusMasks.Active, smallGeneratorIndex]
    have hd :=
      MagnusCoordinateReads.modulus_dvd_generatorCoordinate_of_quotient_dimensionSubring
        N i (smallGeneratorIndex i) hactive x hxcritical
    fin_cases i <;>
      simpa [MagnusCoordinateReads.generatorIndex, MagnusMasks.modulus,
        hallRowScale] using hd
  have houter : ∀ j : Generator,
      (∀ i : Fin 3, j ≠ smallGeneratorIndex i) →
        gradedCoordinate N
          (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N) x = 0 := by
    intro j hj
    fin_cases j
    · have hzero :=
        MagnusCoordinateReads.generatorCoordinate_eq_zero_of_outerActive_of_quotient_dimensionSubring
          N 0 (by simp [MagnusMasks.OuterActive]) x hxcritical
      simpa [MagnusCoordinateReads.generatorIndex] using hzero
    · exact (hj 0 rfl).elim
    · exact (hj 1 rfl).elim
    · exact (hj 2 rfl).elim
    · have hzero :=
        MagnusCoordinateReads.generatorCoordinate_eq_zero_of_outerActive_of_quotient_dimensionSubring
          N 4 (by simp [MagnusMasks.OuterActive]) x hxcritical
      simpa [MagnusCoordinateReads.generatorIndex] using hzero
  obtain ⟨A, hq, hgen⟩ :=
    exists_reduceByHallShiftedRows_generator_coordinates_eq_zero
      N hN x hsmall houter
  refine ⟨reduceByHallShiftedRows N A x, ?_, ?_, hgen⟩
  · exact hq.trans hx
  · rwa [hq]

private theorem hallRowTail_doubleBracket_eq_zero
    (N : ℕ) (i : Fin 3) (x y : Source N) :
    ⁅⁅hallRowTail N i, x⁆, y⁆ = 0 := by
  have h1 : ⁅hallRowTail N i, x⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2) := by
    have hrev : ⁅x, hallRowTail N i⁆ ∈
        LieModule.lowerCentralSeries ℤ (Source N) (Source N) ((N + 1) + 1) := by
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (by simp)
        (hallRowTail_mem_source_lowerCentralSeries N i)
    rw [← lie_skew]
    simpa only [show (N + 1) + 1 = N + 2 by omega] using
      (LieModule.lowerCentralSeries ℤ (Source N) (Source N) ((N + 1) + 1)).neg_mem hrev
  have h2' : ⁅y, ⁅hallRowTail N i, x⁆⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) ((N + 2) + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) h1
  have h2 : ⁅⁅hallRowTail N i, x⁆, y⁆ ∈
      LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 3) := by
    rw [← lie_skew]
    simpa only [show (N + 2) + 1 = N + 3 by omega] using
      (LieModule.lowerCentralSeries ℤ (Source N) (Source N) ((N + 2) + 1)).neg_mem h2'
  have hcut := FreeMetabelian.Free.lowerCentralSeries_cutoff_eq_bot
    (X := GeneratorModule) (c := N + 3)
  rw [hcut] at h2
  exact h2

private theorem hallRowTail_lie_bracket_eq_zero
    (N : ℕ) (i : Fin 3) (x y : Source N) :
    ⁅⁅x, y⁆, hallRowTail N i⁆ = 0 := by
  have hxy : ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ (Source N) 1 := by
    change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℤ (Source N)),
      (⊤ : LieIdeal ℤ (Source N))⁆
    exact LieSubmodule.lie_mem_lie (by simp) (by simp)
  have htail : hallRowTail N i ∈
      LieAlgebra.derivedSeries ℤ (Source N) 1 := by
    have h := hallRowTail_mem_source_lowerCentralSeries N i
    have hle := LieModule.antitone_lowerCentralSeries ℤ
      (Source N) (Source N) (show 1 ≤ N + 1 by omega) h
    simpa only [LieAlgebra.derivedSeries, LieAlgebra.derivedSeriesOfIdeal,
      LieModule.lowerCentralSeries, LieSubmodule.lcs] using hle
  exact FreeMetabelian.Free.isMetabelian.bracket_eq_zero hxy htail

private theorem hallRowTail_lie_eq_zero_of_mem_derived
    (N : ℕ) (i : Fin 3) (d : Source N)
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    ⁅d, hallRowTail N i⁆ = 0 := by
  have htail : hallRowTail N i ∈
      LieAlgebra.derivedSeries ℤ (Source N) 1 := by
    have h := hallRowTail_mem_source_lowerCentralSeries N i
    have hle := LieModule.antitone_lowerCentralSeries ℤ
      (Source N) (Source N) (show 1 ≤ N + 1 by omega) h
    simpa only [LieAlgebra.derivedSeries, LieAlgebra.derivedSeriesOfIdeal,
      LieModule.lowerCentralSeries, LieSubmodule.lcs] using hle
  exact FreeMetabelian.Free.isMetabelian.bracket_eq_zero hd htail

private theorem rightOrbit_mem_relationIdeal
    (N : ℕ) {z : Source N} (hz : z ∈ relationIdeal N) :
    ∀ xs : List (Source N), rightOrbit z xs ∈ relationIdeal N
  | [] => hz
  | x :: xs => by
      rw [rightOrbit_cons]
      exact rightOrbit_mem_relationIdeal N
        (lie_mem_left ℤ (Source N) (relationIdeal N) z x hz) xs

/-- If the distinguished generator occurs in either initial bracket slot,
two subsequent brackets kill the high tail of the full shifted row. -/
theorem hallRowScale_deepBracket_mem_relationIdeal
    (N : ℕ) (i : Fin 3) (x y : Source N) (xs : List (Source N)) :
    hallRowScale i •
        rightOrbit ⁅⁅smallSourceGenerator N i, x⁆, y⁆ xs ∈
      relationIdeal N := by
  have hrow : rightOrbit ⁅⁅hallShiftedRow N i, x⁆, y⁆ xs ∈
      relationIdeal N :=
    rightOrbit_mem_relationIdeal N
      (lie_mem_left ℤ (Source N) (relationIdeal N) _ y
        (lie_mem_left ℤ (Source N) (relationIdeal N) _ x
          (hallShiftedRow_mem_relationIdeal N i))) xs
  have hbase : ⁅⁅hallShiftedRow N i, x⁆, y⁆ =
      hallRowScale i • ⁅⁅smallSourceGenerator N i, x⁆, y⁆ := by
    rw [hallShiftedRow, add_lie, zsmul_lie, add_lie, zsmul_lie,
      hallRowTail_doubleBracket_eq_zero, add_zero]
  rw [hbase, rightOrbit_zsmul] at hrow
  exact hrow

/-- If the distinguished generator occurs as a tooth, bracketing the full
row with the derived initial pair kills its tail by metabelianity. -/
theorem hallRowScale_toothBracket_mem_relationIdeal
    (N : ℕ) (i : Fin 3) (x y : Source N) (xs : List (Source N)) :
    hallRowScale i •
        rightOrbit ⁅⁅x, y⁆, smallSourceGenerator N i⁆ xs ∈
      relationIdeal N := by
  have hrow : rightOrbit ⁅⁅x, y⁆, hallShiftedRow N i⁆ xs ∈
      relationIdeal N :=
    rightOrbit_mem_relationIdeal N
      (lie_mem_right ℤ (Source N) (relationIdeal N) _ _
        (hallShiftedRow_mem_relationIdeal N i)) xs
  have hbase : ⁅⁅x, y⁆, hallShiftedRow N i⁆ =
      hallRowScale i • ⁅⁅x, y⁆, smallSourceGenerator N i⁆ := by
    rw [hallShiftedRow, lie_add, lie_zsmul,
      hallRowTail_lie_bracket_eq_zero, add_zero]
  rw [hbase, rightOrbit_zsmul] at hrow
  exact hrow

/-- The tooth calculation with an arbitrary derived initial word. -/
theorem hallRowScale_lie_smallGenerator_mem_relationIdeal_of_mem_derived
    (N : ℕ) (i : Fin 3) (d : Source N)
    (hd : d ∈ LieAlgebra.derivedSeries ℤ (Source N) 1) :
    hallRowScale i • ⁅d, smallSourceGenerator N i⁆ ∈
      relationIdeal N := by
  have hrow : ⁅d, hallShiftedRow N i⁆ ∈ relationIdeal N :=
    lie_mem_right ℤ (Source N) (relationIdeal N) _ _
      (hallShiftedRow_mem_relationIdeal N i)
  have hbase : ⁅d, hallShiftedRow N i⁆ =
      hallRowScale i • ⁅d, smallSourceGenerator N i⁆ := by
    rw [hallShiftedRow, lie_add, lie_zsmul,
      hallRowTail_lie_eq_zero_of_mem_derived N i d hd, add_zero]
  rwa [hbase] at hrow

/-- A literal Hall word contains the indicated small generator. -/
def HallContainsSmall {q : ℕ} (h : FreeMetabelian.HallIndex Generator q)
    (i : Fin 3) : Prop :=
  h.head = smallGeneratorIndex i ∨
    h.pivot = smallGeneratorIndex i ∨
      smallGeneratorIndex i ∈ (h.teeth : Multiset Generator)

/-- The occurrence formulation of `HallContainsSmall`.  This is the bridge
between the literal Hall-row ledger and the recursive Magnus masks. -/
theorem hallContainsSmall_iff_mem_hallOccurrences {q : ℕ}
    (h : FreeMetabelian.HallIndex Generator q) (i : Fin 3) :
    HallContainsSmall h i ↔
      smallGeneratorIndex i ∈ MagnusCoordinates.hallOccurrences q h := by
  rw [MagnusCoordinates.hallOccurrences_eq_head_cons_pivot_cons_teeth]
  simp only [HallContainsSmall, Multiset.mem_cons]
  tauto

private theorem hallSurvives_iff_forall_mem_active (i : Fin 3) :
    ∀ (q : ℕ) (h : FreeMetabelian.HallIndex Generator q),
      MagnusMasks.HallSurvives i q h ↔
        ∀ j ∈ MagnusCoordinates.hallOccurrences q h,
          MagnusMasks.Active i j := by
  intro q
  induction q with
  | zero =>
      intro h
      simp [MagnusCoordinates.hallOccurrences, MagnusMasks.HallSurvives]
  | succ q ih =>
      intro h
      simp [MagnusCoordinates.hallOccurrences, MagnusMasks.HallSurvives,
        ih h.predecessor]

private theorem outerHallSurvives_iff_forall_mem_outerActive :
    ∀ (q : ℕ) (h : FreeMetabelian.HallIndex Generator q),
      MagnusMasks.OuterHallSurvives q h ↔
        ∀ j ∈ MagnusCoordinates.hallOccurrences q h,
          MagnusMasks.OuterActive j := by
  intro q
  induction q with
  | zero =>
      intro h
      simp [MagnusCoordinates.hallOccurrences, MagnusMasks.OuterHallSurvives]
  | succ q ih =>
      intro h
      simp [MagnusCoordinates.hallOccurrences, MagnusMasks.OuterHallSurvives,
        ih h.predecessor]

private theorem hallSurvives_zero (q : ℕ)
    (h : FreeMetabelian.HallIndex Generator q) :
    MagnusMasks.HallSurvives 0 q h := by
  rw [hallSurvives_iff_forall_mem_active]
  intro j hj
  exact MagnusMasks.active_zero j

private theorem hallSurvives_one_of_not_contains_zero {q : ℕ}
    (h : FreeMetabelian.HallIndex Generator q)
    (hzero : ¬ HallContainsSmall h 0) :
    MagnusMasks.HallSurvives 1 q h := by
  rw [hallSurvives_iff_forall_mem_active]
  intro j hj
  rw [MagnusMasks.active_one]
  intro heq
  apply hzero
  apply (hallContainsSmall_iff_mem_hallOccurrences h 0).2
  simpa [heq] using hj

private theorem hallSurvives_two_of_not_contains_zero_one {q : ℕ}
    (h : FreeMetabelian.HallIndex Generator q)
    (hzero : ¬ HallContainsSmall h 0)
    (hone : ¬ HallContainsSmall h 1) :
    MagnusMasks.HallSurvives 2 q h := by
  rw [hallSurvives_iff_forall_mem_active]
  intro j hj
  rw [MagnusMasks.active_two]
  constructor
  · intro heq
    apply hzero
    apply (hallContainsSmall_iff_mem_hallOccurrences h 0).2
    simpa [heq] using hj
  · intro heq
    apply hone
    apply (hallContainsSmall_iff_mem_hallOccurrences h 1).2
    simpa [heq] using hj

private theorem outerHallSurvives_of_not_contains_small {q : ℕ}
    (h : FreeMetabelian.HallIndex Generator q)
    (hzero : ¬ HallContainsSmall h 0)
    (hone : ¬ HallContainsSmall h 1)
    (htwo : ¬ HallContainsSmall h 2) :
    MagnusMasks.OuterHallSurvives q h := by
  rw [outerHallSurvives_iff_forall_mem_outerActive]
  intro j hj
  fin_cases j
  · simp [MagnusMasks.OuterActive]
  · exfalso
    apply hzero
    apply (hallContainsSmall_iff_mem_hallOccurrences h 0).2
    simpa [smallGeneratorIndex] using hj
  · exfalso
    apply hone
    apply (hallContainsSmall_iff_mem_hallOccurrences h 1).2
    simpa [smallGeneratorIndex] using hj
  · exfalso
    apply htwo
    apply (hallContainsSmall_iff_mem_hallOccurrences h 2).2
    simpa [smallGeneratorIndex] using hj
  · simp [MagnusMasks.OuterActive]

/-- The complete coordinate information supplied by the Magnus probes in
all Hall layers below the terminal one.  At the top-minus-one layer the
three literal `c_i` are retained; every other coordinate is either zero or
divisible by the scale of the first small generator which occurs. -/
theorem hallCoordinate_cSource_or_rowScale_dvd_or_zero
    (N : ℕ) (hN : 1 ≤ N) (x : Source N)
    (hx : quotientMap N x ∈ dimensionSubring ℤ (L N) (N + 4))
    (q : ℕ) (h : FreeMetabelian.HallIndex Generator q)
    (hq : q < N + 1) :
    (∃ i : Fin 3,
      FreeMetabelian.Evaluation.hallBracket generatorBasis q h (by omega) =
        cSource N i) ∨
    (∃ i : Fin 3,
      HallContainsSmall h i ∧
        hallRowScale i ∣
          gradedCoordinate N
            (⟨⟨q + 1, by omega⟩, h⟩ : CriticalHallIndex N) x) ∨
    gradedCoordinate N
        (⟨⟨q + 1, by omega⟩, h⟩ : CriticalHallIndex N) x = 0 := by
  by_cases hc : ∃ i : Fin 3,
      FreeMetabelian.Evaluation.hallBracket generatorBasis q h (by omega) =
        cSource N i
  · exact Or.inl hc
  · right
    have hcne : ∀ i : Fin 3,
        FreeMetabelian.Evaluation.hallBracket generatorBasis q h (by omega) ≠
          cSource N i := by
      intro i hi
      exact hc ⟨i, hi⟩
    by_cases hzero : HallContainsSmall h 0
    · left
      refine ⟨0, hzero, ?_⟩
      by_cases htop : q = N
      · subst q
        have hd :=
          TopMinusOneMagnus.modulus_dvd_hallCoordinate_topMinusOne
            N hN 0 h (hallSurvives_zero N h) hcne hx
        simpa [MagnusCoordinateReads.hallIndex, MagnusMasks.modulus,
          hallRowScale] using hd
      · have hqN : q < N := by omega
        have hd :=
          MagnusCoordinateReads.modulus_dvd_hallCoordinate_of_quotient_dimensionSubring
            N 0 q hqN h (hallSurvives_zero q h) x hx
        simpa [MagnusCoordinateReads.hallIndex, MagnusMasks.modulus,
          hallRowScale] using hd
    · by_cases hone : HallContainsSmall h 1
      · left
        refine ⟨1, hone, ?_⟩
        have hsurvive := hallSurvives_one_of_not_contains_zero h hzero
        by_cases htop : q = N
        · subst q
          have hd :=
            TopMinusOneMagnus.modulus_dvd_hallCoordinate_topMinusOne
              N hN 1 h hsurvive hcne hx
          simpa [MagnusCoordinateReads.hallIndex, MagnusMasks.modulus,
            hallRowScale] using hd
        · have hqN : q < N := by omega
          have hd :=
            MagnusCoordinateReads.modulus_dvd_hallCoordinate_of_quotient_dimensionSubring
              N 1 q hqN h hsurvive x hx
          simpa [MagnusCoordinateReads.hallIndex, MagnusMasks.modulus,
            hallRowScale] using hd
      · by_cases htwo : HallContainsSmall h 2
        · left
          refine ⟨2, htwo, ?_⟩
          have hsurvive :=
            hallSurvives_two_of_not_contains_zero_one h hzero hone
          by_cases htop : q = N
          · subst q
            have hd :=
              TopMinusOneMagnus.modulus_dvd_hallCoordinate_topMinusOne
                N hN 2 h hsurvive hcne hx
            simpa [MagnusCoordinateReads.hallIndex, MagnusMasks.modulus,
              hallRowScale] using hd
          · have hqN : q < N := by omega
            have hd :=
              MagnusCoordinateReads.modulus_dvd_hallCoordinate_of_quotient_dimensionSubring
                N 2 q hqN h hsurvive x hx
            simpa [MagnusCoordinateReads.hallIndex, MagnusMasks.modulus,
              hallRowScale] using hd
        · right
          have hsurvive :=
            outerHallSurvives_of_not_contains_small h hzero hone htwo
          have hz :=
            MagnusCoordinateReads.hallCoordinate_eq_zero_of_outerSurvives_of_quotient_dimensionSubring
              N q (by omega) h hsurvive x hx
          simpa [MagnusCoordinateReads.hallIndex] using hz

private theorem hallContainsSmall_predecessor_or_nextTooth
    {q : ℕ} (h : FreeMetabelian.HallIndex Generator (q + 1)) (i : Fin 3)
    (hi : HallContainsSmall h i) :
    HallContainsSmall h.predecessor i ∨
      h.nextTooth = smallGeneratorIndex i := by
  rcases hi with hhead | hpivot | hteeth
  · left
    exact Or.inl hhead
  · left
    exact Or.inr (Or.inl hpivot)
  · by_cases hnext : h.nextTooth = smallGeneratorIndex i
    · exact Or.inr hnext
    · left
      right
      right
      change smallGeneratorIndex i ∈
        (h.teeth : Multiset Generator).erase h.nextTooth
      exact (Multiset.mem_erase_of_ne (Ne.symm hnext)).2 hteeth

private theorem hallBracket_mem_source_derived
    (N q : ℕ) (h : FreeMetabelian.HallIndex Generator q)
    (hq : q + 1 < N + 3) :
    FreeMetabelian.Evaluation.hallBracket generatorBasis q h hq ∈
      LieAlgebra.derivedSeries ℤ (Source N) 1 := by
  have hm := FreeMetabelian.Evaluation.hallBracket_mem_lowerCentralSeries
    generatorBasis q h hq
  have hm1 := LieModule.antitone_lowerCentralSeries ℤ
    (Source N) (Source N) (show 1 ≤ q + 1 by omega) hm
  simpa only [LieAlgebra.derivedSeries, LieAlgebra.derivedSeriesOfIdeal,
    LieModule.lowerCentralSeries, LieSubmodule.lcs] using hm1

/-- **Intermediate Hall-row elimination.**  Every Hall comb of manuscript
weight at least three that contains `xᵢ` is killed by the corresponding
row scale in the presented quotient.  The proof uses the full shifted row;
its high tail vanishes only after the two required bracket contexts. -/
theorem hallRowScale_hallBracket_mem_relationIdeal
    (N q : ℕ) (hq : q + 1 + 1 < N + 3)
    (h : FreeMetabelian.HallIndex Generator (q + 1)) (i : Fin 3)
    (hi : HallContainsSmall h i) :
    hallRowScale i •
        FreeMetabelian.Evaluation.hallBracket generatorBasis (q + 1) h hq ∈
      relationIdeal N := by
  induction q with
  | zero =>
      rcases hallContainsSmall_predecessor_or_nextTooth h i hi with
        hpred | hnext
      · rcases hpred with hhead | hpivot | hteeth
        · have hm := hallRowScale_deepBracket_mem_relationIdeal N i
              (sourceGenerator N h.predecessor.pivot)
              (sourceGenerator N h.nextTooth) []
          rw [rightOrbit_nil] at hm
          rw [FreeMetabelian.Evaluation.hallBracket,
            FreeMetabelian.Evaluation.hallBracket]
          simpa [hhead] using hm
        · have hm := hallRowScale_deepBracket_mem_relationIdeal N i
              (sourceGenerator N h.predecessor.head)
              (sourceGenerator N h.nextTooth) []
          rw [rightOrbit_nil] at hm
          have hmneg := (relationIdeal N).neg_mem hm
          rw [FreeMetabelian.Evaluation.hallBracket,
            FreeMetabelian.Evaluation.hallBracket]
          rw [hpivot]
          change hallRowScale i •
              Bracket.bracket
                (Bracket.bracket (sourceGenerator N h.predecessor.head)
                  (smallSourceGenerator N i))
                (sourceGenerator N h.nextTooth) ∈ relationIdeal N
          have hskew :
              Bracket.bracket (sourceGenerator N h.predecessor.head)
                  (smallSourceGenerator N i) =
                -Bracket.bracket (smallSourceGenerator N i)
                    (sourceGenerator N h.predecessor.head) :=
            (lie_skew _ _).symm
          rw [hskew, neg_lie, smul_neg]
          exact hmneg
        · have hcard :
              ((h.predecessor.teeth : Sym Generator 0) :
                Multiset Generator).card = 0 :=
            h.predecessor.teeth.property
          have hpos :
              0 < ((h.predecessor.teeth : Sym Generator 0) :
                Multiset Generator).card :=
            Multiset.card_pos_iff_exists_mem.mpr
              ⟨smallGeneratorIndex i, hteeth⟩
          omega
      · rw [FreeMetabelian.Evaluation.hallBracket, hnext]
        exact hallRowScale_lie_smallGenerator_mem_relationIdeal_of_mem_derived
          N i _ (hallBracket_mem_source_derived N 0 h.predecessor (by omega))
  | succ q ih =>
      rcases hallContainsSmall_predecessor_or_nextTooth h i hi with
        hpred | hnext
      · rw [FreeMetabelian.Evaluation.hallBracket, ← zsmul_lie]
        exact lie_mem_left ℤ (Source N) (relationIdeal N) _ _
          (ih (by omega) h.predecessor hpred)
      · rw [FreeMetabelian.Evaluation.hallBracket, hnext]
        exact hallRowScale_lie_smallGenerator_mem_relationIdeal_of_mem_derived
          N i _ (hallBracket_mem_source_derived N (q + 1) h.predecessor
            (by omega))

theorem quotientMap_hallRowScale_hallBracket_eq_zero
    (N q : ℕ) (hq : q + 1 + 1 < N + 3)
    (h : FreeMetabelian.HallIndex Generator (q + 1)) (i : Fin 3)
    (hi : HallContainsSmall h i) :
    quotientMap N
        (hallRowScale i •
          FreeMetabelian.Evaluation.hallBracket generatorBasis (q + 1) h hq) =
      0 := by
  apply (LieSubmodule.Quotient.mk_eq_zero' (N := relationIdeal N)).mpr
  exact hallRowScale_hallBracket_mem_relationIdeal N q hq h i hi

theorem quotientMap_zsmul_hallBracket_eq_zero_of_rowScale_dvd
    (N q : ℕ) (hq : q + 1 + 1 < N + 3)
    (h : FreeMetabelian.HallIndex Generator (q + 1)) (i : Fin 3)
    (hi : HallContainsSmall h i) (a : ℤ) (ha : hallRowScale i ∣ a) :
    quotientMap N
        (a • FreeMetabelian.Evaluation.hallBracket generatorBasis (q + 1) h hq) =
      0 := by
  obtain ⟨b, rfl⟩ := ha
  apply (LieSubmodule.Quotient.mk_eq_zero' (N := relationIdeal N)).mpr
  simpa only [mul_smul, mul_comm] using
    (relationIdeal N).smul_mem b
      (hallRowScale_hallBracket_mem_relationIdeal N q hq h i hi)

/-! ## Reduction of the terminal Hall layer -/

/-- Every terminal Hall basis vector is either a defining zero relation or
one of the three exceptional diagonals, hence is an integral multiple of
`u₃` in the presented ring. -/
theorem exists_quotientMap_topHallSource_eq_zsmul_u3
    (N : ℕ) (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    ∃ a : ℤ, quotientMap N (topHallSource N h) = a • u3 N := by
  by_cases hex : IsExceptionalTop N h
  · rcases hex with h1 | h2 | h3
    · refine ⟨16, ?_⟩
      rw [h1, map_uSource]
      exact u1_eq_sixteen_u3 N
    · refine ⟨4, ?_⟩
      rw [h2, map_uSource]
      exact u2_eq_four_u3 N
    · refine ⟨1, ?_⟩
      rw [h3, map_uSource, one_zsmul]
  · refine ⟨0, ?_⟩
    rw [zero_zsmul]
    apply quotientMap_eq_zero_of_mem_definingRelators
    exact Or.inl (Or.inr ⟨h, hex, rfl⟩)

/-! ## The finite additive target of Hall collection -/

/-- The four coordinates before the final centrality read: the three
distinguished `c_i` and the terminal generator. -/
def cTerminalFrame (N : ℕ) : Fin 4 → L N
  | 0 => c1 N
  | 1 => c2 N
  | 2 => c3 N
  | 3 => u3 N

def cTerminalSpan (N : ℕ) : Submodule ℤ (L N) :=
  Submodule.span ℤ (Set.range (cTerminalFrame N))

private theorem cTerminalFrame_mem (N : ℕ) (i : Fin 4) :
    cTerminalFrame N i ∈ cTerminalSpan N :=
  Submodule.subset_span ⟨i, rfl⟩

theorem c1_mem_cTerminalSpan (N : ℕ) : c1 N ∈ cTerminalSpan N := by
  simpa [cTerminalFrame] using cTerminalFrame_mem N 0

theorem c2_mem_cTerminalSpan (N : ℕ) : c2 N ∈ cTerminalSpan N := by
  simpa [cTerminalFrame] using cTerminalFrame_mem N 1

theorem c3_mem_cTerminalSpan (N : ℕ) : c3 N ∈ cTerminalSpan N := by
  simpa [cTerminalFrame] using cTerminalFrame_mem N 2

theorem u3_mem_cTerminalSpan (N : ℕ) : u3 N ∈ cTerminalSpan N := by
  simpa [cTerminalFrame] using cTerminalFrame_mem N 3

private theorem u_mem_cTerminalSpan (N : ℕ) (i : Fin 3) :
    u N i ∈ cTerminalSpan N := by
  fin_cases i
  · change u1 N ∈ cTerminalSpan N
    rw [u1_eq_sixteen_u3]
    exact (cTerminalSpan N).smul_mem 16 (u3_mem_cTerminalSpan N)
  · change u2 N ∈ cTerminalSpan N
    rw [u2_eq_four_u3]
    exact (cTerminalSpan N).smul_mem 4 (u3_mem_cTerminalSpan N)
  · change u3 N ∈ cTerminalSpan N
    exact u3_mem_cTerminalSpan N

private theorem quotientMap_eq_zero_of_mem_relationIdeal
    {N : ℕ} {x : Source N} (hx : x ∈ relationIdeal N) :
    quotientMap N x = 0 := by
  exact (LieSubmodule.Quotient.mk_eq_zero' (N := relationIdeal N)).mpr hx

private theorem quotientMap_cSource_lie_sourceGenerator_mem_cTerminalSpan
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    quotientMap N (Bracket.bracket (cSource N i) (sourceGenerator N j)) ∈
      cTerminalSpan N := by
  have hrel := cSource_lie_sourceGenerator_sub_diagonal_mem_relationIdeal
    N hN i j
  have hzero := quotientMap_eq_zero_of_mem_relationIdeal hrel
  have heq :
      quotientMap N (Bracket.bracket (cSource N i) (sourceGenerator N j)) =
        quotientMap N
          (if j = smallGeneratorIndex i then uSource N i else 0) := by
    simpa only [map_sub, sub_eq_zero, LieHom.map_lie] using hzero
  rw [heq]
  split
  · simpa only [map_uSource] using u_mem_cTerminalSpan N i
  · simp

private theorem quotientMap_hallRowTail_lie_sourceGenerator_mem_cTerminalSpan
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    quotientMap N
        (Bracket.bracket (hallRowTail N i) (sourceGenerator N j)) ∈
      cTerminalSpan N := by
  fin_cases i
  · simp only [hallRowTail, add_lie, zsmul_lie, LieHom.map_lie,
      map_add, map_zsmul]
    exact (cTerminalSpan N).add_mem
      ((cTerminalSpan N).smul_mem 2
        (quotientMap_cSource_lie_sourceGenerator_mem_cTerminalSpan
          N hN 2 j))
      (quotientMap_cSource_lie_sourceGenerator_mem_cTerminalSpan
        N hN 1 j)
  · simp only [hallRowTail, sub_lie, zsmul_lie, LieHom.map_lie,
      map_sub, map_zsmul]
    exact (cTerminalSpan N).sub_mem
      ((cTerminalSpan N).smul_mem 4
        (quotientMap_cSource_lie_sourceGenerator_mem_cTerminalSpan
          N hN 2 j))
      (quotientMap_cSource_lie_sourceGenerator_mem_cTerminalSpan
        N hN 0 j)
  · simp only [hallRowTail, sub_lie, neg_lie, zsmul_lie,
      LieHom.map_lie, map_sub, map_neg, map_zsmul]
    exact (cTerminalSpan N).sub_mem
      ((cTerminalSpan N).neg_mem
        ((cTerminalSpan N).smul_mem 4
          (quotientMap_cSource_lie_sourceGenerator_mem_cTerminalSpan
            N hN 1 j)))
      ((cTerminalSpan N).smul_mem 2
        (quotientMap_cSource_lie_sourceGenerator_mem_cTerminalSpan
          N hN 0 j))

theorem quotientMap_hallRowScale_small_lie_generator_mem_cTerminalSpan
    (N : ℕ) (hN : 1 ≤ N) (i : Fin 3) (j : Generator) :
    quotientMap N
        (hallRowScale i •
          Bracket.bracket (smallSourceGenerator N i)
            (sourceGenerator N j)) ∈
      cTerminalSpan N := by
  have hrow :
      Bracket.bracket (hallShiftedRow N i) (sourceGenerator N j) ∈
      relationIdeal N :=
    lie_mem_left ℤ (Source N) (relationIdeal N) _ _
      (hallShiftedRow_mem_relationIdeal N i)
  have hzero := quotientMap_eq_zero_of_mem_relationIdeal hrow
  have heq :
      quotientMap N
          (hallRowScale i •
            Bracket.bracket (smallSourceGenerator N i)
              (sourceGenerator N j)) =
        -quotientMap N
          (Bracket.bracket (hallRowTail N i) (sourceGenerator N j)) := by
    rw [hallShiftedRow, add_lie, zsmul_lie] at hzero
    exact eq_neg_of_add_eq_zero_left (by
      simpa only [map_add, map_zsmul] using hzero)
  rw [heq]
  exact (cTerminalSpan N).neg_mem
    (quotientMap_hallRowTail_lie_sourceGenerator_mem_cTerminalSpan
      N hN i j)

theorem quotientMap_hallRowScale_weightTwoHall_mem_cTerminalSpan
    (N : ℕ) (hN : 1 ≤ N)
    (h : FreeMetabelian.HallIndex Generator 0) (i : Fin 3)
    (hi : HallContainsSmall h i) :
    quotientMap N
        (hallRowScale i •
          FreeMetabelian.Evaluation.hallBracket generatorBasis 0 h (by omega)) ∈
      cTerminalSpan N := by
  rcases hi with hhead | hpivot | hteeth
  · rw [FreeMetabelian.Evaluation.hallBracket, hhead]
    exact quotientMap_hallRowScale_small_lie_generator_mem_cTerminalSpan
      N hN i h.pivot
  · rw [FreeMetabelian.Evaluation.hallBracket, hpivot]
    have hm := quotientMap_hallRowScale_small_lie_generator_mem_cTerminalSpan
      N hN i h.head
    have hskew :
        hallRowScale i •
            Bracket.bracket (sourceGenerator N h.head)
              (smallSourceGenerator N i) =
          -(hallRowScale i •
            Bracket.bracket (smallSourceGenerator N i)
              (sourceGenerator N h.head)) := by
      rw [show Bracket.bracket (sourceGenerator N h.head)
          (smallSourceGenerator N i) =
        -Bracket.bracket (smallSourceGenerator N i)
          (sourceGenerator N h.head) by
          exact (lie_skew _ _).symm,
        smul_neg]
    change quotientMap N
        (hallRowScale i •
          Bracket.bracket (sourceGenerator N h.head)
            (smallSourceGenerator N i)) ∈ cTerminalSpan N
    rw [hskew, map_neg]
    exact (cTerminalSpan N).neg_mem hm
  · have hcard : ((h.teeth : Sym Generator 0) : Multiset Generator).card = 0 :=
      h.teeth.property
    have hpos : 0 < ((h.teeth : Sym Generator 0) : Multiset Generator).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨smallGeneratorIndex i, hteeth⟩
    omega

theorem quotientMap_topHallSource_mem_cTerminalSpan
    (N : ℕ) (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    quotientMap N (topHallSource N h) ∈ cTerminalSpan N := by
  obtain ⟨a, ha⟩ := exists_quotientMap_topHallSource_eq_zsmul_u3 N h
  rw [ha]
  exact (cTerminalSpan N).smul_mem a (u3_mem_cTerminalSpan N)

private theorem c_mem_cTerminalSpan (N : ℕ) (i : Fin 3) :
    c N i ∈ cTerminalSpan N := by
  fin_cases i
  · exact c1_mem_cTerminalSpan N
  · exact c2_mem_cTerminalSpan N
  · exact c3_mem_cTerminalSpan N

/-- A graded Hall basis vector in a positive homogeneous piece is exactly
the corresponding literal Hall bracket. -/
theorem hallGradedBasis_succ_eq_hallBracket
    (N q : ℕ) (h : FreeMetabelian.HallIndex Generator q)
    (hq : q + 1 < N + 3) :
    FreeMetabelian.Free.hallGradedBasis generatorBasis
        (⟨⟨q + 1, hq⟩, h⟩ : CriticalHallIndex N) =
      FreeMetabelian.Evaluation.hallBracket generatorBasis q h hq := by
  rw [hallGradedBasis_apply,
    FreeMetabelian.Evaluation.hallBracket_eq_incl]
  change FreeMetabelian.Free.incl
      (⟨q + 1, hq⟩ : Fin (N + 3))
        (FreeMetabelian.Free.pieceBasis generatorBasis (q + 1) h) =
    FreeMetabelian.Free.incl (⟨q + 1, hq⟩ : Fin (N + 3))
      (FreeMetabelian.hallVector generatorBasis q h)
  rw [FreeMetabelian.Free.pieceBasis]
  have he :
      (FreeMetabelian.hallBasis generatorBasis q).equivFun.toAddEquiv.toIntLinearEquiv =
        (FreeMetabelian.hallBasis generatorBasis q).equivFun :=
    LinearEquiv.toAddEquiv_toIntLinearEquiv
      (FreeMetabelian.hallBasis generatorBasis q).equivFun
  have hbEq : Module.Basis.ofEquivFun
        (FreeMetabelian.hallBasis generatorBasis q).equivFun.toAddEquiv.toIntLinearEquiv =
      FreeMetabelian.hallBasis generatorBasis q := by
    rw [he, Module.Basis.ofEquivFun_equivFun]
  have hpEq := congrArg (fun b ↦ b h) hbEq
  calc
    _ = FreeMetabelian.Free.incl (⟨q + 1, hq⟩ : Fin (N + 3))
        (FreeMetabelian.hallBasis generatorBasis q h) :=
      congrArg (FreeMetabelian.Free.incl
        (⟨q + 1, hq⟩ : Fin (N + 3))) hpEq
    _ = _ := by rw [FreeMetabelian.hallBasis_apply]

/-- Hall collection with precisely the three top-minus-one exceptions left
unreduced.  This is the direct consumer of the masked Magnus probes: after
the full shifted rows have removed weight one, all lower Hall coordinates
are row multiples, while at weight `N+2` the three literal `c_i` may remain.
-/
theorem quotientMap_mem_cTerminalSpan_of_reduced_coordinate_conditions
    (N : ℕ) (hN : 1 ≤ N) (x : Source N)
    (hgen : ∀ j : Generator,
      gradedCoordinate N
        (⟨⟨0, by omega⟩, j⟩ : CriticalHallIndex N) x = 0)
    (hhall : ∀ (q : ℕ) (h : FreeMetabelian.HallIndex Generator q)
        (hq : q < N + 1),
      (∃ i : Fin 3,
        FreeMetabelian.Evaluation.hallBracket generatorBasis q h (by omega) =
          cSource N i) ∨
      (∃ i : Fin 3,
        HallContainsSmall h i ∧
          hallRowScale i ∣
            gradedCoordinate N
              (⟨⟨q + 1, by omega⟩, h⟩ : CriticalHallIndex N) x) ∨
      gradedCoordinate N
          (⟨⟨q + 1, by omega⟩, h⟩ : CriticalHallIndex N) x = 0) :
    quotientMap N x ∈ cTerminalSpan N := by
  let B : Module.Basis (CriticalHallIndex N) ℤ (Source N) :=
    FreeMetabelian.Free.hallGradedBasis generatorBasis
  have hterm : ∀ p : CriticalHallIndex N,
      quotientMap N (gradedCoordinate N p x • B p) ∈
        cTerminalSpan N := by
    rintro ⟨⟨s, hs⟩, p⟩
    cases s with
    | zero =>
        change Generator at p
        have hbasis :
            B (⟨⟨0, hs⟩, p⟩ : CriticalHallIndex N) =
              sourceGenerator N p := by
          rw [show B = FreeMetabelian.Free.hallGradedBasis generatorBasis by rfl,
            hallGradedBasis_apply]
          rfl
        rw [hbasis, hgen p, zero_smul, map_zero]
        exact (cTerminalSpan N).zero_mem
    | succ q =>
        change FreeMetabelian.HallIndex Generator q at p
        have hbasis :
            B (⟨⟨q + 1, hs⟩, p⟩ : CriticalHallIndex N) =
              FreeMetabelian.Evaluation.hallBracket generatorBasis q p hs := by
          exact hallGradedBasis_succ_eq_hallBracket N q p hs
        rw [hbasis]
        by_cases htop : q = N + 1
        · subst q
          have hsource :
              FreeMetabelian.Evaluation.hallBracket generatorBasis (N + 1) p hs =
                topHallSource N p := by
            calc
              _ = B (⟨⟨N + 1 + 1, hs⟩, p⟩ : CriticalHallIndex N) :=
                hbasis.symm
              _ = _ := by
                simpa only [B, topGradedIndex] using
                  hallGradedBasis_topGradedIndex N p
          rw [hsource, map_zsmul]
          exact (cTerminalSpan N).smul_mem _
            (quotientMap_topHallSource_mem_cTerminalSpan N p)
        · have hq : q < N + 1 := by omega
          rcases hhall q p hq with hc | hdiv | hzero
          · obtain ⟨i, hc⟩ := hc
            rw [hc, map_zsmul, map_cSource]
            exact (cTerminalSpan N).smul_mem _
              (c_mem_cTerminalSpan N i)
          · obtain ⟨i, hi, a, ha⟩ := hdiv
            rw [ha]
            cases q with
            | zero =>
                have hm := (cTerminalSpan N).smul_mem a
                  (quotientMap_hallRowScale_weightTwoHall_mem_cTerminalSpan
                    N hN p i hi)
                simpa only [mul_smul, mul_comm, map_zsmul] using hm
            | succ q =>
                have hz :=
                  quotientMap_zsmul_hallBracket_eq_zero_of_rowScale_dvd
                    N q (by omega) p i hi (hallRowScale i * a)
                    (dvd_mul_right (hallRowScale i) a)
                rw [hz]
                exact (cTerminalSpan N).zero_mem
          · rw [hzero, zero_smul, map_zero]
            exact (cTerminalSpan N).zero_mem
  rw [← B.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro p hp
  simpa only [map_zsmul, gradedCoordinate, Module.Basis.coord_apply] using
    hterm p

theorem mem_cTerminalSpan_iff (N : ℕ) (z : L N) :
    z ∈ cTerminalSpan N ↔
      ∃ μ₁ μ₂ μ₃ η : ℤ,
        z = μ₁ • c1 N + μ₂ • c2 N + μ₃ • c3 N + η • u3 N := by
  rw [cTerminalSpan, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f 0, f 1, f 2, f 3, ?_⟩
    have hf' := hf.symm
    simp [Fin.sum_univ_succ, cTerminalFrame] at hf'
    rw [hf']
    abel
  · rintro ⟨μ₁, μ₂, μ₃, η, rfl⟩
    refine ⟨![μ₁, μ₂, μ₃, η], ?_⟩
    simp [Fin.sum_univ_succ, cTerminalFrame]
    abel

/-! ## The last lower-central term -/

/-- The cyclic Lie ideal generated by the retained terminal class `u₃`. -/
def terminalCyclicIdeal (N : ℕ) : LieIdeal ℤ (L N) :=
  LieSubmodule.lieSpan ℤ (L N) {u3 N}

private theorem u3_mem_terminalCyclicIdeal (N : ℕ) :
    u3 N ∈ terminalCyclicIdeal N :=
  LieSubmodule.subset_lieSpan (Set.mem_singleton (u3 N))

/-- The terminal diagonal is central by its lower-central weight and the
presentation cutoff. -/
theorem u3_mem_center (N : ℕ) :
    u3 N ∈ LieAlgebra.center ℤ (L N) := by
  rw [LieModule.mem_maxTrivSubmodule]
  intro x
  have hx' : ⁅x, u3 N⁆ ∈
      LieModule.lowerCentralSeries ℤ (L N) (L N) ((N + 2) + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) (u_mem_lowerCentralSeries N 2)
  have hx : ⁅x, u3 N⁆ ∈
      LieModule.lowerCentralSeries ℤ (L N) (L N) (N + 3) := by
    simpa only [show (N + 2) + 1 = N + 3 by omega] using hx'
  have hcut :
      LieModule.lowerCentralSeries ℤ (L N) (L N) (N + 3) = ⊥ :=
    lowerCentralSeries_cutoff_eq_bot N
  rw [hcut] at hx
  simpa using hx

/-- Since `u₃` is central, its Lie-ideal span is exactly its additive cyclic
span.  This coefficient extraction is needed for the final order-`64`
calculation. -/
theorem mem_terminalCyclicIdeal_iff_exists_zsmul_u3
    (N : ℕ) (z : L N) :
    z ∈ terminalCyclicIdeal N ↔ ∃ η : ℤ, z = η • u3 N := by
  constructor
  · intro hz
    change z ∈ LieSubmodule.lieSpan ℤ (L N) {u3 N} at hz
    induction hz using LieSubmodule.lieSpan_induction with
    | mem y hy =>
        have hy' : y = u3 N := by simpa using hy
        subst y
        exact ⟨1, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨a, rfl⟩ := ihx
        obtain ⟨b, rfl⟩ := ihy
        exact ⟨a + b, by rw [add_zsmul]⟩
    | smul a x hx ih =>
        obtain ⟨b, rfl⟩ := ih
        exact ⟨a * b, by rw [mul_smul]⟩
    | lie x y hy ih =>
        obtain ⟨b, rfl⟩ := ih
        refine ⟨0, ?_⟩
        rw [lie_zsmul]
        have hcenter := u3_mem_center N
        rw [LieModule.mem_maxTrivSubmodule] at hcenter
        rw [hcenter x, smul_zero, zero_zsmul]
  · rintro ⟨η, rfl⟩
    exact (terminalCyclicIdeal N).smul_mem η (u3_mem_terminalCyclicIdeal N)

private theorem right_lie_eq_zero_of_mem_center
    {N : ℕ} {z : L N} (hz : z ∈ LieAlgebra.center ℤ (L N)) (x : L N) :
    ⁅z, x⁆ = 0 := by
  have hleft := (LieModule.mem_maxTrivSubmodule ℤ (L N) (L N) z).mp hz x
  rw [← lie_skew, hleft, neg_zero]

/-- Centrality removes exactly the three residual `c_i` coordinates.
Bracketing with `x_i` reads `μ_i u_i`; exact order `64` of `u₃`, together
with `u₁=16u₃` and `u₂=4u₃`, gives divisibility by `4,16,64`.  The three
full-row consequences `4c₁=16c₂=64c₃=0` then kill those coordinates. -/
theorem mem_terminalCyclicIdeal_of_mem_cTerminalSpan_of_mem_center
    (N : ℕ) (hN : 1 ≤ N) {z : L N}
    (hzspan : z ∈ cTerminalSpan N)
    (hzcenter : z ∈ LieAlgebra.center ℤ (L N)) :
    z ∈ terminalCyclicIdeal N := by
  obtain ⟨μ₁, μ₂, μ₃, η, hz⟩ := (mem_cTerminalSpan_iff N z).mp hzspan
  have hu3center := u3_mem_center N
  have hu3x (i : Fin 3) : ⁅u3 N, smallGenerator N i⁆ = 0 :=
    right_lie_eq_zero_of_mem_center hu3center _
  have hμ₁ : μ₁ • u1 N = 0 := by
    have hbr := right_lie_eq_zero_of_mem_center hzcenter (smallGenerator N 0)
    rw [hz] at hbr
    simp only [add_lie, zsmul_lie, c1, c2, c3]
      at hbr
    rw [c_lie_smallGenerator N 0,
      offDiagonalTop_eq_zero N hN (i := 1) (j := 0) (by decide),
      offDiagonalTop_eq_zero N hN (i := 2) (j := 0) (by decide),
      hu3x 0, smul_zero, add_zero] at hbr
    simpa only [smul_zero, add_zero] using hbr
  have hμ₂ : μ₂ • u2 N = 0 := by
    have hbr := right_lie_eq_zero_of_mem_center hzcenter (smallGenerator N 1)
    rw [hz] at hbr
    simp only [add_lie, zsmul_lie, c1, c2, c3]
      at hbr
    rw [offDiagonalTop_eq_zero N hN (i := 0) (j := 1) (by decide),
      c_lie_smallGenerator N 1,
      offDiagonalTop_eq_zero N hN (i := 2) (j := 1) (by decide),
      hu3x 1] at hbr
    simpa only [smul_zero, zero_add, add_zero] using hbr
  have hμ₃ : μ₃ • u3 N = 0 := by
    have hbr := right_lie_eq_zero_of_mem_center hzcenter (smallGenerator N 2)
    rw [hz] at hbr
    simp only [add_lie, zsmul_lie, c1, c2, c3]
      at hbr
    rw [offDiagonalTop_eq_zero N hN (i := 0) (j := 2) (by decide),
      offDiagonalTop_eq_zero N hN (i := 1) (j := 2) (by decide),
      c_lie_smallGenerator N 2, hu3x 2] at hbr
    simpa only [smul_zero, zero_add, add_zero] using hbr
  have horder : (addOrderOf (u3 N) : ℤ) = 64 := by
    exact_mod_cast addOrderOf_u3_eq_sixtyFour N hN
  have h4 : (4 : ℤ) ∣ μ₁ := by
    have hzero : (μ₁ * 16) • u3 N = 0 := by
      rw [← smul_smul, ← u1_eq_sixteen_u3]
      exact hμ₁
    have hd : (64 : ℤ) ∣ μ₁ * 16 := by
      rw [← horder, addOrderOf_dvd_iff_zsmul_eq_zero]
      exact hzero
    obtain ⟨d, hd⟩ := hd
    exact ⟨d, by omega⟩
  have h16 : (16 : ℤ) ∣ μ₂ := by
    have hzero : (μ₂ * 4) • u3 N = 0 := by
      rw [← smul_smul, ← u2_eq_four_u3]
      exact hμ₂
    have hd : (64 : ℤ) ∣ μ₂ * 4 := by
      rw [← horder, addOrderOf_dvd_iff_zsmul_eq_zero]
      exact hzero
    obtain ⟨d, hd⟩ := hd
    exact ⟨d, by omega⟩
  have h64 : (64 : ℤ) ∣ μ₃ := by
    rw [← horder, addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hμ₃
  obtain ⟨A, rfl⟩ := h4
  obtain ⟨B, rfl⟩ := h16
  obtain ⟨C, rfl⟩ := h64
  rw [hz]
  have hc1 := four_c1_eq_zero N hN
  have hc2 := sixteen_c2_eq_zero N hN
  have hc3 := sixtyFour_c3_eq_zero N hN
  have hc1A : (4 * A) • c1 N = 0 := by
    calc
      (4 * A) • c1 N = A • ((4 : ℤ) • c1 N) := by module
      _ = 0 := by rw [hc1, smul_zero]
  have hc2B : (16 * B) • c2 N = 0 := by
    calc
      (16 * B) • c2 N = B • ((16 : ℤ) • c2 N) := by module
      _ = 0 := by rw [hc2, smul_zero]
  have hc3C : (64 * C) • c3 N = 0 := by
    calc
      (64 * C) • c3 N = C • ((64 : ℤ) • c3 N) := by module
      _ = 0 := by rw [hc3, smul_zero]
  have hzEq :
      (4 * A) • c1 N + (16 * B) • c2 N + (64 * C) • c3 N + η • u3 N =
        η • u3 N := by
    rw [hc1A, hc2B, hc3C, zero_add, zero_add, zero_add]
  rw [hzEq]
  exact (terminalCyclicIdeal N).smul_mem η (u3_mem_terminalCyclicIdeal N)

private theorem quotientMap_topHallSource_mem_terminalCyclicIdeal
    (N : ℕ) (h : FreeMetabelian.HallIndex Generator (N + 1)) :
    quotientMap N (topHallSource N h) ∈ terminalCyclicIdeal N := by
  obtain ⟨a, ha⟩ := exists_quotientMap_topHallSource_eq_zsmul_u3 N h
  rw [ha]
  exact (terminalCyclicIdeal N).smul_mem a
    (u3_mem_terminalCyclicIdeal N)

private theorem quotientMap_mem_terminalCyclicIdeal_of_mem_topTail
    (N : ℕ) {x : Source N}
    (hx : x ∈ FreeMetabelian.Free.tail (X := GeneratorModule) (N + 2)) :
    quotientMap N x ∈ terminalCyclicIdeal N := by
  let B : Module.Basis (CriticalHallIndex N) ℤ (Source N) :=
    FreeMetabelian.Free.hallGradedBasis generatorBasis
  rw [← B.sum_repr x, map_sum]
  apply Submodule.sum_mem
  rintro ⟨⟨s, hs⟩, p⟩ hp
  by_cases htop : s = N + 2
  · subst s
    change FreeMetabelian.HallIndex Generator (N + 1) at p
    have hbasis :
        B (⟨⟨N + 2, hs⟩, p⟩ : CriticalHallIndex N) =
          topHallSource N p := by
      simpa only [B, topGradedIndex, show N + 1 + 1 = N + 2 by omega] using
        hallGradedBasis_topGradedIndex N p
    rw [hbasis, map_zsmul]
    exact (terminalCyclicIdeal N).smul_mem _
      (quotientMap_topHallSource_mem_terminalCyclicIdeal N p)
  · have hslt : s < N + 2 := by omega
    have hx0 : x ⟨s, hs⟩ = 0 := hx ⟨s, hs⟩ hslt
    have hcoord : B.repr x (⟨⟨s, hs⟩, p⟩ : CriticalHallIndex N) = 0 := by
      change (FreeMetabelian.Free.hallGradedBasis generatorBasis).repr x
          (⟨⟨s, hs⟩, p⟩ : CriticalHallIndex N) = 0
      rw [criticalHallGradedBasis_repr_apply, hx0]
      simp
    rw [hcoord, zero_smul, map_zero]
    exact (terminalCyclicIdeal N).zero_mem

/-- The last potentially nonzero lower-central term is exactly the cyclic
ideal generated by `u₃`.  This records the precise upper statement, not just
the height/nonvanishing result. -/
theorem lowerCentralSeries_top_eq_terminalCyclicIdeal
    (N : ℕ) :
    lowerCentralSeries ℤ (L N) (N + 2) = terminalCyclicIdeal N := by
  apply le_antisymm
  · intro z hz
    have hmap := LieIdeal.lowerCentralSeries_map_eq
      (R := ℤ) (N + 2) (quotientMap_surjective N)
    change z ∈ LieModule.lowerCentralSeries ℤ (L N) (L N) (N + 2) at hz
    rw [← hmap] at hz
    obtain ⟨⟨x, hx⟩, hqx⟩ := LieIdeal.mem_map_of_surjective
      (I := LieModule.lowerCentralSeries ℤ (Source N) (Source N) (N + 2))
      (f := quotientMap N) (quotientMap_surjective N) hz
    rw [← hqx]
    apply quotientMap_mem_terminalCyclicIdeal_of_mem_topTail N
    exact FreeMetabelian.Free.lowerCentralSeries_le_tail (N + 2) hx
  · change LieSubmodule.lieSpan ℤ (L N) {u3 N} ≤
      LieModule.lowerCentralSeries ℤ (L N) (L N) (N + 2)
    rw [LieSubmodule.lieSpan_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact u_mem_lowerCentralSeries N 2

private theorem critical_dimensionSubring_le_center_from_centrality (N : ℕ) :
    dimensionSubring ℤ (L N) (N + 4) ≤ LieAlgebra.center ℤ (L N) := by
  intro z hz
  rw [LieModule.mem_maxTrivSubmodule]
  intro x
  have hbracket : ⁅z, x⁆ ∈
      ⁅dimensionSubring ℤ (L N) (N + 4), (⊤ : LieIdeal ℤ (L N))⁆ :=
    LieSubmodule.lie_mem_lie hz (by simp)
  rw [dimensionSubring_bracket_eq_lowerCentralSeries_of_pos
      ℤ (L N) (by omega : 1 ≤ N + 4)] at hbracket
  have hzero : lowerCentralSeries ℤ (L N) (N + 4) = ⊥ := by
    apply le_antisymm
    · exact (LieModule.antitone_lowerCentralSeries ℤ (L N) (L N)
          (by omega : N + 3 ≤ N + 4)).trans
        (by rw [lowerCentralSeries_cutoff_eq_bot N])
    · exact bot_le
  rw [hzero] at hbracket
  have hzx : ⁅z, x⁆ = 0 := by simpa using hbracket
  rw [← lie_skew, hzx, neg_zero]

/-- The exact Hall/Magnus reduction: every element of the critical dimension
term lies in the cyclic terminal ideal.  No PBW factor-number splitting is
used; the three top-minus-one exceptions are removed by centrality. -/
theorem critical_dimensionSubring_le_terminalCyclicIdeal
    (N : ℕ) (hN : 1 ≤ N) :
    dimensionSubring ℤ (L N) (N + 4) ≤ terminalCyclicIdeal N := by
  intro z hz
  obtain ⟨x, hxz, hxcritical, hgen⟩ :=
    exists_critical_lift_generator_coordinates_eq_zero N hN hz
  have hspan : quotientMap N x ∈ cTerminalSpan N :=
    quotientMap_mem_cTerminalSpan_of_reduced_coordinate_conditions
      N hN x hgen (fun q h hq ↦
        hallCoordinate_cSource_or_rowScale_dvd_or_zero
          N hN x hxcritical q h hq)
  rw [hxz] at hspan
  exact mem_terminalCyclicIdeal_of_mem_cTerminalSpan_of_mem_center
    N hN hspan (critical_dimensionSubring_le_center_from_centrality N hz)

/-- **Unconditional critical upper bound.**  The terminal coefficient is
annihilated by two, while `u₃` has exact additive order `64`; hence that
coefficient is a multiple of `32`, and the element lies in the Lie ideal
generated by `a = 32u₃`. -/
theorem dimensionSubring_critical_le_exceptionalIdeal
    (N : ℕ) (hN : 1 ≤ N) :
    dimensionSubring ℤ (L N) (N + 4) ≤ exceptionalIdeal N := by
  intro z hz
  have hzterminal := critical_dimensionSubring_le_terminalCyclicIdeal N hN hz
  obtain ⟨η, hzη⟩ :=
    (mem_terminalCyclicIdeal_iff_exists_zsmul_u3 N z).mp hzterminal
  have htwo : (2 : ℤ) • z = 0 := by
    apply LieRings.MetabelianTwoFactor.Presentation.dimensionSubring_succ_two_smul_eq_zero
      (c := N + 3) (hc := by omega) (R := relationIdeal N)
    simpa only [show N + 3 + 1 = N + 4 by omega] using hz
  have htwoEta : (2 * η) • u3 N = 0 := by
    rw [mul_smul, ← hzη]
    exact htwo
  have horder : (addOrderOf (u3 N) : ℤ) = 64 := by
    exact_mod_cast addOrderOf_u3_eq_sixtyFour N hN
  have h64 : (64 : ℤ) ∣ 2 * η := by
    rw [← horder, addOrderOf_dvd_iff_zsmul_eq_zero]
    exact htwoEta
  obtain ⟨D, hD⟩ := h64
  have hη : η = 32 * D := by omega
  have ha : a N ∈ exceptionalIdeal N := by
    change a N ∈ LieSubmodule.lieSpan ℤ (L N) {a N}
    exact LieSubmodule.subset_lieSpan (Set.mem_singleton (a N))
  have heq : (32 * D) • u3 N = D • a N := by
    rw [a_eq_thirtyTwo_u3 N hN]
    module
  rw [hzη, hη, heq]
  exact (exceptionalIdeal N).smul_mem D ha

end

end LieRings.FinitePlateau

assert_no_sorry LieRings.FinitePlateau.dimensionSubring_critical_le_exceptionalIdeal
