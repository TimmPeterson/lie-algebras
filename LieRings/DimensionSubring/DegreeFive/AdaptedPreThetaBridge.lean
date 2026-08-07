import LieRings.DimensionSubring.DegreeFive.AdaptedTerminalProjection

/-!
# The terminal ledger as a pre-Theta equation

This file is the final coordinate-reading bridge.  Its data are the actual terminal packets
of the adapted collector; no coordinate equation is stored as an assumption.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L] [Finite L]

namespace StandingReductionData

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L
local notation "I" => CoordinateI L
local notation "K" => CoordinateK L

open Coordinate Coordinate.Data Coordinate.Data.CollectedExpression

variable (R : StandingReductionData L)

private theorem rawPBWProjection_yy_self_zero
    (P : @RawExpression I K) (k : K) :
    R.coordinateData.rawPBWProjection (.yy k k) P = 0 := by
  classical
  unfold Coordinate.Data.rawPBWProjection
  change P.sum (fun w n ↦ n *
    R.coordinateData.rawWordCoordinate w.toList (.yy k k)) = 0
  calc
    _ = P.sum (fun _ _ ↦ (0 : ℤ)) := by
      apply Finsupp.sum_congr
      intro w hw
      change P w * R.coordinateData.rawWordCoordinate w.toList (.yy k k) = 0
      unfold Coordinate.Data.rawWordCoordinate
      split <;> simp_all [ne_comm] <;> aesop
    _ = 0 := by simp

private theorem rawPBWProjection_yy_swap
    (P : @RawExpression I K) (k l : K) :
    R.coordinateData.rawPBWProjection (.yy k l) P =
      R.coordinateData.rawPBWProjection (.yy l k) P := by
  classical
  unfold Coordinate.Data.rawPBWProjection
  change P.sum (fun w n ↦ n *
      R.coordinateData.rawWordCoordinate w.toList (.yy k l)) =
    P.sum (fun w n ↦ n *
      R.coordinateData.rawWordCoordinate w.toList (.yy l k))
  apply Finsupp.sum_congr
  intro w hw
  congr 1
  unfold Coordinate.Data.rawWordCoordinate
  split <;> simp_all [ne_comm, and_comm, or_comm, or_left_comm, or_assoc]

/-- The literal pre-Theta ledger read from the terminating adapted collector. -/
def terminalPreTheta {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) :
    @PreTheta I K inferInstance :=
  AdaptedTerminalCoordinates.visiblePreTheta L L ev w.terminalPackets t .zero

@[simp] theorem terminalPreTheta_r {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (i : I) :
    (terminalPreTheta w t).r i =
      AdaptedTerminalCoordinates.r L L ev w.terminalPackets i := rfl

@[simp] theorem terminalPreTheta_s {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (k : K) :
    (terminalPreTheta w t).s k =
      AdaptedTerminalCoordinates.s L L ev w.terminalPackets k := rfl

@[simp] theorem terminalPreTheta_rxx {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (i : I) :
    (terminalPreTheta w t).rxx i =
      AdaptedTerminalCoordinates.rxx L L ev w.terminalPackets i := rfl

@[simp] theorem terminalPreTheta_rx {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (i j : I) :
    (terminalPreTheta w t).rx i j =
      AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j := rfl

@[simp] theorem terminalPreTheta_xr {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (i j : I) :
    (terminalPreTheta w t).xr i j =
      AdaptedTerminalCoordinates.xr L L ev w.terminalPackets i j := rfl


/-- The actual terminal equality supplies every weight-one pre-Theta coordinate. -/
theorem terminalPreTheta_xEquation {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (i : I) :
    preThetaProjection R.coordinateData (.x i)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  rw [show preThetaProjection R.coordinateData (.x i) =
      rawCoefficient [.x i] by rfl,
    rawCoefficient_preTheta_x]
  change (R.coordinateD i : ℤ) *
      AdaptedTerminalCoordinates.r L L ev w.terminalPackets i = 0
  rw [← R.terminalPackets_xProjection w i]
  exact w.terminalPackets_xCoefficient_eq_zero i

/-- The actual terminal equality supplies every weight-two `y` coordinate. -/
theorem terminalPreTheta_yEquation {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (k : K) :
    preThetaProjection R.coordinateData (.y k)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  rw [show preThetaProjection R.coordinateData (.y k) =
      rawCoefficient [.y k] by rfl,
    rawCoefficient_preTheta_y]
  change -( ∑ i : I, AdaptedTerminalCoordinates.r L L ev
        w.terminalPackets i * R.coordinateB i k) +
      (R.coordinateE k : ℤ) *
        AdaptedTerminalCoordinates.s L L ev w.terminalPackets k = 0
  rw [← R.terminalPackets_yProjection w k]
  exact w.terminalPackets_yCoefficient_eq_zero k

/-- The diagonal two-`x` coordinate of the actual terminal equality. -/
theorem terminalPreTheta_xxDiagEquation {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ) (i : I) :
    preThetaProjection R.coordinateData (.xx i i)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  rw [show preThetaProjection R.coordinateData (.xx i i) =
      rawCoefficient [.x i, .x i] by rfl,
    rawCoefficient_preTheta_xx_diag]
  change (R.coordinateD i : ℤ) *
      AdaptedTerminalCoordinates.rxx L L ev w.terminalPackets i = 0
  rw [← R.terminalPackets_xxDiagProjection w i]
  exact w.terminalPackets_xxCoefficient_eq_zero i i

/-- The ordered off-diagonal two-`x` coordinate of the actual terminal equality. -/
theorem terminalPreTheta_xxOffdiagEquation {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ)
    {i j : I} (hij : i < j) :
    preThetaProjection R.coordinateData (.xx i j)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  rw [show preThetaProjection R.coordinateData (.xx i j) =
      rawCoefficient [.x i, .x j] by rfl,
    rawCoefficient_preTheta_xx _ _ _ hij]
  change (R.coordinateD i : ℤ) *
        AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j +
      (R.coordinateD j : ℤ) *
        AdaptedTerminalCoordinates.xr L L ev w.terminalPackets i j = 0
  rw [← R.terminalPackets_xxOffdiagProjection w hij]
  exact w.terminalPackets_xxCoefficient_eq_zero i j

/-- A reversed two-`x` word is absent from the ordered terminal pre-Theta
polynomial. -/
theorem terminalPreTheta_xxReverseEquation {a : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a) (t : ℤ)
    {i j : I} (hji : j < i) :
    preThetaProjection R.coordinateData (.xx i j)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  rw [show preThetaProjection R.coordinateData (.xx i j) =
      rawCoefficient [.x i, .x j] by rfl]
  classical
  simp [terminalPreTheta, AdaptedTerminalCoordinates.visiblePreTheta,
    PreTheta.polynomial, rRelation, sRelation, tRelation, coreWordExpression,
    TableRemainder.expression, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord, rawCoefficient_tableRemainder_xx,
    hji.ne, hji, not_lt_of_ge hji.le]
  change _ + _ = (0 : ℤ) + 0
  apply congrArg₂ (.+.)
  · apply Finset.sum_eq_zero
    intro x hx
    by_cases hs : i = x ∧ j = x
    · exact (hji.ne (hs.2.trans hs.1.symm)).elim
    · simp [hs]
  · apply Finset.sum_eq_zero
    intro x hx
    have hlt := mem_upperPairs.mp hx
    have hs : ¬(i = x.1 ∧ j = x.2) := by
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge hji.le hlt)
    simp [hs]

theorem terminalPreTheta_xyPolynomial {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ)
    (a : I) (k : K) :
    R.coordinateData.rawPBWProjection (.xy a k)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) =
      w.terminalPackets.sum (fun p n ↦ n •
        adaptedPBWCoefficient L L ev (xyExponent (L := L) a k) (p.value L L ev)) := by
  classical
  have hxrZero {i : I} (hia : i < a) :
      AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i = 0 := by
    exact terminalPackets_leftXCoefficient_eq_zero_of_lt w hia
  have hrxZero {i : I} (hai : a < i) :
      AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a = 0 := by
    exact terminalPackets_rightXCoefficient_eq_zero_of_lt w hai
  have hxrErase :
      (∑ i ∈ Finset.univ.erase a,
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i *
            R.coordinateB i k) =
        ∑ i ∈ Finset.univ.filter (a < ·),
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i *
            R.coordinateB i k := by
    symm
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [ne_of_gt hi]
    · intro i hiErase hiNot
      have hne : i ≠ a := (Finset.mem_erase.mp hiErase).1
      have hnot : ¬ a < i := by simpa using hiNot
      have hia : i < a := lt_of_le_of_ne (le_of_not_gt hnot) hne
      rw [hxrZero hia, zero_mul]
  have hrxErase :
      (∑ i ∈ Finset.univ.erase a,
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a *
            R.coordinateB i k) =
        ∑ i ∈ Finset.univ.filter (· < a),
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a *
            R.coordinateB i k := by
    symm
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [ne_of_lt hi]
    · intro i hiErase hiNot
      have hne : i ≠ a := (Finset.mem_erase.mp hiErase).1
      have hnot : ¬ i < a := by simpa using hiNot
      have hai : a < i := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)
      rw [hrxZero hai, zero_mul]
  have hxrAll :
      (∑ i : I, AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i *
          R.coordinateB i k) =
        AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a a *
            R.coordinateB a k +
          ∑ i ∈ Finset.univ.filter (a < ·),
            AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i *
              R.coordinateB i k := by
    calc
      _ = (∑ i ∈ Finset.univ.erase a,
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i *
            R.coordinateB i k) +
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a a *
            R.coordinateB a k :=
        (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ a)).symm
      _ = _ := by rw [hxrErase]; ring
  have hrxAll :
      (∑ i : I, AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a *
          R.coordinateB i k) =
        AdaptedTerminalCoordinates.rx L L ev w.terminalPackets a a *
            R.coordinateB a k +
          ∑ i ∈ Finset.univ.filter (· < a),
            AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a *
              R.coordinateB i k := by
    calc
      _ = (∑ i ∈ Finset.univ.erase a,
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a *
            R.coordinateB i k) +
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets a a *
            R.coordinateB a k :=
        (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ a)).symm
      _ = _ := by rw [hrxErase]; ring
  have hupperXR :
      (∑ ij ∈ upperPairs I,
          if a = ij.1 then
            AdaptedTerminalCoordinates.xr L L ev w.terminalPackets ij.1 ij.2 *
              R.coordinateB ij.2 k else 0) =
        ∑ i ∈ Finset.univ.filter (a < ·),
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i *
            R.coordinateB i k := by
    rw [show (∑ ij ∈ upperPairs I,
        if a = ij.1 then
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets ij.1 ij.2 *
            R.coordinateB ij.2 k else 0) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        if a = i then
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets i j *
            R.coordinateB j k else 0 from
      sum_upperPairs (fun i j ↦ if a = i then
        AdaptedTerminalCoordinates.xr L L ev w.terminalPackets i j *
          R.coordinateB j k else 0)]
    rw [Finset.sum_eq_single a]
    · simp
    · intro i hi hia
      simp [Ne.symm hia]
    · simp
  have hupperRX :
      (∑ ij ∈ upperPairs I,
          if a = ij.2 then
            AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 *
              R.coordinateB ij.1 k else 0) =
        ∑ i ∈ Finset.univ.filter (· < a),
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a *
            R.coordinateB i k := by
    rw [show (∑ ij ∈ upperPairs I,
        if a = ij.2 then
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 *
            R.coordinateB ij.1 k else 0) =
      ∑ j, ∑ i ∈ Finset.univ.filter (· < j),
        if a = j then
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j *
            R.coordinateB i k else 0 from
      sum_upperPairs_right (fun i j ↦ if a = j then
        AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i j *
          R.coordinateB i k else 0)]
    rw [Finset.sum_eq_single a]
    · simp
    · intro j hj hja
      simp [Ne.symm hja]
    · simp
  have hB :
      -(AdaptedTerminalCoordinates.rxx L L ev w.terminalPackets a *
          R.coordinateB a k) +
        ∑ ij ∈ upperPairs I,
          ((-if a = ij.2 then
              AdaptedTerminalCoordinates.rx L L ev w.terminalPackets ij.1 ij.2 *
                R.coordinateB ij.1 k else 0) -
            if a = ij.1 then
              AdaptedTerminalCoordinates.xr L L ev w.terminalPackets ij.1 ij.2 *
                R.coordinateB ij.2 k else 0) =
      -∑ i : I,
        (AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i +
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a) *
            R.coordinateB i k := by
    rw [show AdaptedTerminalCoordinates.rxx L L ev w.terminalPackets a =
        AdaptedTerminalCoordinates.rx L L ev w.terminalPackets a a +
          AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a a by rfl]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      hupperRX, hupperXR]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    rw [hxrAll, hrxAll]
    ring
  rw [R.terminalPackets_xyProjection w a k]
  simp [terminalPreTheta, AdaptedTerminalCoordinates.visiblePreTheta,
    PreTheta.polynomial, rRelation, sRelation, tRelation,
    coreWordExpression, TableRemainder.expression,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord, rawWordCoordinate]
  simp only [StandingReductionData.coordinateData]
  change -(AdaptedTerminalCoordinates.rxx L L ev w.terminalPackets a *
          R.coordinateB a k) +
        (∑ x ∈ upperPairs I,
          ((-if a = x.2 then
              AdaptedTerminalCoordinates.rx L L ev w.terminalPackets x.1 x.2 *
                R.coordinateB x.1 k else 0) -
            if a = x.1 then
              AdaptedTerminalCoordinates.xr L L ev w.terminalPackets x.1 x.2 *
                R.coordinateB x.2 k else 0)) +
      AdaptedTerminalCoordinates.v L L ev w.terminalPackets a k *
          (R.coordinateD a : ℤ) +
        AdaptedTerminalCoordinates.v' L L ev w.terminalPackets a k *
          (R.coordinateE k : ℤ) =
    -(∑ i : I,
        (AdaptedTerminalCoordinates.xr L L ev w.terminalPackets a i +
          AdaptedTerminalCoordinates.rx L L ev w.terminalPackets i a) *
            R.coordinateB i k) +
      (R.coordinateD a : ℤ) *
          AdaptedTerminalCoordinates.v L L ev w.terminalPackets a k +
        AdaptedTerminalCoordinates.v' L L ev w.terminalPackets a k *
          (R.coordinateE k : ℤ)
  rw [hB]
  ring

/-- The `xy` PBW coordinate of the terminal pre-Theta polynomial vanishes. -/
theorem terminalPreTheta_xyEquation {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ)
    (a : I) (k : K) :
    preThetaProjection R.coordinateData (.pbw (.xy a k))
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  change R.coordinateData.rawPBWProjection (.xy a k)
      ((terminalPreTheta w t).polynomial R.coordinateData
        R.coordinateRelationTails) = 0
  rw [R.terminalPreTheta_xyPolynomial w t a k]
  exact w.terminalPackets_xyCoefficient_eq_zero a k

/-- The ordered off-diagonal `yy` PBW coordinate of the literal terminal
pre-Theta polynomial is the semantic terminal-ledger coordinate. -/
theorem terminalPreTheta_yyPolynomial {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ)
    {k l : K} (hkl : k < l) :
    R.coordinateData.rawPBWProjection (.yy k l)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) =
      w.terminalPackets.sum (fun p n ↦ n •
        adaptedPBWCoefficient L L ev (yyExponent (L := L) k l) (p.value L L ev)) := by
  classical
  rw [R.terminalPackets_yyOffdiagProjection w hkl]
  simp [terminalPreTheta, AdaptedTerminalCoordinates.visiblePreTheta,
    PreTheta.polynomial, rRelation, sRelation, tRelation,
    coreWordExpression, TableRemainder.expression,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord, rawWordCoordinate, hkl.ne,
    sum_unordered_indicator, sum_unordered_indicator_rev,
    upperPairs_rawTerm_yy_projection]
  simp only [StandingReductionData.coordinateData]
  rw [upperPairs_unordered_indicator
    (fun a b ↦ (R.coordinateE a : ℤ) *
      AdaptedTerminalCoordinates.sY L L ev w.terminalPackets a b +
      (R.coordinateE b : ℤ) *
        AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets a b) hkl]
  have hv (i : I) :
      (∑ j : K,
        AdaptedTerminalCoordinates.v L L ev w.terminalPackets i j *
          ((-if j = k then R.coordinateB i l else 0) +
            -if j = l then R.coordinateB i k else 0)) =
        -(AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k *
            R.coordinateB i l +
          AdaptedTerminalCoordinates.v L L ev w.terminalPackets i l *
            R.coordinateB i k) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp [eq_comm]
    ring
  rw [show (∑ i : I, ∑ j : K,
      AdaptedTerminalCoordinates.v L L ev w.terminalPackets i j *
        ((-if j = k then R.coordinateB i l else 0) +
          -if j = l then R.coordinateB i k else 0)) =
      ∑ i : I, -(AdaptedTerminalCoordinates.v L L ev w.terminalPackets i k *
          R.coordinateB i l +
        AdaptedTerminalCoordinates.v L L ev w.terminalPackets i l *
          R.coordinateB i k) by
    apply Finset.sum_congr rfl
    intro i hi
    exact hv i]
  rw [Finset.sum_neg_distrib]
  ring

/-- The diagonal `y²` PBW coordinate of the literal terminal pre-Theta
polynomial is the semantic terminal-ledger coordinate. -/
theorem terminalPreTheta_ySquarePolynomial {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ)
    (k : K) :
    R.coordinateData.rawPBWProjection (.ySquare k)
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) =
      w.terminalPackets.sum (fun p n ↦ n •
        adaptedPBWCoefficient L L ev (yyExponent (L := L) k k) (p.value L L ev)) := by
  classical
  rw [R.terminalPackets_ySquareProjection w k]
  simp [terminalPreTheta, AdaptedTerminalCoordinates.visiblePreTheta,
    PreTheta.polynomial, rRelation, sRelation, tRelation,
    coreWordExpression, TableRemainder.expression,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum,
    rawTerm_mul_rawTerm, rawTerm_mul_rawWord, rawWord_mul_rawTerm,
    rawWord_mul_rawWord, rawWordCoordinate,
    and_comm, eq_comm]
  simp only [StandingReductionData.coordinateData]
  have hupper :
      (∑ x ∈ upperPairs K,
        if k = x.1 ∧ k = x.2 then
          (R.coordinateE x.1 : ℤ) *
              AdaptedTerminalCoordinates.sY L L ev w.terminalPackets x.1 x.2 +
            (R.coordinateE x.2 : ℤ) *
              AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets x.1 x.2
        else 0) = 0 := by
    simpa only [eq_comm] using upperPairs_diagonal_indicator_zero
      (fun a b ↦ (R.coordinateE a : ℤ) *
        AdaptedTerminalCoordinates.sY L L ev w.terminalPackets a b +
        (R.coordinateE b : ℤ) *
          AdaptedTerminalCoordinates.Ys L L ev w.terminalPackets a b) k
  rw [hupper]
  ring

/-- Condition `(C1)` read from the actual terminal equality. -/
theorem terminalPreTheta_yyEquation {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ)
    {k l : K} (hkl : k < l) :
    preThetaProjection R.coordinateData (.pbw (.yy k l))
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  change R.coordinateData.rawPBWProjection (.yy k l)
      ((terminalPreTheta w t).polynomial R.coordinateData
        R.coordinateRelationTails) = 0
  rw [R.terminalPreTheta_yyPolynomial w t hkl]
  exact w.terminalPackets_yyCoefficient_eq_zero k l

/-- Condition `(C2)` read from the actual terminal equality. -/
theorem terminalPreTheta_ySquareEquation {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ)
    (k : K) :
    preThetaProjection R.coordinateData (.pbw (.ySquare k))
        ((terminalPreTheta w t).polynomial R.coordinateData
          R.coordinateRelationTails) = 0 := by
  change R.coordinateData.rawPBWProjection (.ySquare k)
      ((terminalPreTheta w t).polynomial R.coordinateData
        R.coordinateRelationTails) = 0
  rw [R.terminalPreTheta_ySquarePolynomial w t k]
  exact w.terminalPackets_yyCoefficient_eq_zero k k

/-- The integral `z` coefficient actually read from the terminal pre-Theta
polynomial. -/
def terminalLieZ {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ) : ℤ :=
  R.coordinateData.rawPBWProjection .z
    ((terminalPreTheta w t).polynomial R.coordinateData R.coordinateRelationTails)

/-- The corresponding cyclic weight-three coordinate. -/
def terminalZeta {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ) : ZMod R.q :=
  (R.terminalLieZ w t : ZMod R.q)

/-- **The terminal ledger produces a `PreThetaEquation` without any coordinate
assumption.**  Every non-`z` field is one of the preceding semantic PBW
projections, and the `z` field is the actual projection itself. -/
def terminalPreThetaEquation {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ) :
    PreThetaEquation R.coordinateData (terminalPreTheta w t)
      R.coordinateRelationTails (R.terminalZeta w t) where
  lieZ := R.terminalLieZ w t
  lieZ_mod := rfl
  collected_eq := by
    intro c
    cases c with
    | x i =>
        simpa [preThetaRightCoefficient] using R.terminalPreTheta_xEquation w t i
    | y k =>
        simpa [preThetaRightCoefficient] using R.terminalPreTheta_yEquation w t k
    | xx i j =>
        rcases lt_trichotomy i j with hij | hij | hji
        · simpa [preThetaRightCoefficient] using
            R.terminalPreTheta_xxOffdiagEquation w t hij
        · subst j
          simpa [preThetaRightCoefficient] using
            R.terminalPreTheta_xxDiagEquation w t i
        · simpa [preThetaRightCoefficient] using
            R.terminalPreTheta_xxReverseEquation w t hji
    | pbw c =>
        cases c with
        | xy i k =>
            simpa [preThetaRightCoefficient] using
              R.terminalPreTheta_xyEquation w t i k
        | z =>
            rfl
        | yy k l =>
            rcases lt_trichotomy k l with hkl | hkl | hlk
            · simpa [preThetaRightCoefficient] using
                R.terminalPreTheta_yyEquation w t hkl
            · subst l
              change R.coordinateData.rawPBWProjection (.yy k k)
                ((terminalPreTheta w t).polynomial R.coordinateData
                  R.coordinateRelationTails) = 0
              exact rawPBWProjection_yy_self_zero R _ k
            · change R.coordinateData.rawPBWProjection (.yy k l)
                  ((terminalPreTheta w t).polynomial R.coordinateData
                    R.coordinateRelationTails) = 0
              rw [rawPBWProjection_yy_swap R _ k l]
              exact R.terminalPreTheta_yyEquation w t hlk
        | ySquare k =>
            simpa [preThetaRightCoefficient] using
              R.terminalPreTheta_ySquareEquation w t k

/-- The complete coordinate system `(B)`, `(Z)`, `(C1)`, `(C2)` extracted
from the terminal ledger. -/
def terminalCoefficientSystem {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ) :
    R.coordinateData.CoefficientSystem (R.terminalZeta w t) :=
  PreThetaEquation.toCoefficientSystem R.coordinateData (terminalPreTheta w t)
    R.coordinateRelationTails R.coordinateIdentities
    R.coordinateD_pos R.coordinateE_pos (R.terminalPreThetaEquation w t)

/-- The symplectic certificate annihilates the cyclic coordinate extracted
from every actual terminal ledger.  The sole ambient hypothesis is
`StandingReductionData`. -/
theorem terminalZeta_eq_zero {a₀ : L}
    (w : AdaptedPresentationDimensionFiveWitness L L ev a₀) (t : ℤ) :
    R.terminalZeta w t = 0 := by
  exact R.coordinateData.coefficientSystem_vanishes R.q_pos R.coordinateD_pos
    R.coordinateIdentities (R.terminalCoefficientSystem w t)

end StandingReductionData

end

end DegreeFive

end LieRings
