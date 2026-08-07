import LieRings.DimensionSubring.DegreeFive.AdaptedWeightedClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.AdaptedTerminalCoordinates
import LieRings.DimensionSubring.DegreeFive.AdaptedRelationTails

/-!
# The semantic-to-coordinate PBW bridge

This file applies genuine PBW coefficient maps, in the collector's shared Smith basis, to the
terminal packet equality.  No coordinate equality is stored as presentation data.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable {L : Type u} [LieRing L] [Finite L]

namespace AdaptedPresentationDimensionFiveWitness

variable {X : Type*} [Finite X]
variable {A : Type*} [LieRing A] [Finite A]
variable {evaluation : LieHom ℤ (FreeLieAlgebra ℤ X) A} {a : A}

/-- Every adapted class-two PBW coefficient below weight five vanishes on the terminal ledger
of a witness whose lift lies in the third lower-central term. -/
theorem terminalPackets_adaptedPBWCoefficient_eq_zero
    (w : AdaptedPresentationDimensionFiveWitness X A evaluation a)
    (e : FiniteClassTwoBasisIndex X →₀ ℕ)
    (he : adaptedClassTwoExponentWeight X e < 5) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient X A evaluation e (p.value X A evaluation)) = 0 := by
  let φ := adaptedPBWCoefficient X A evaluation e
  have hvalue := w.terminalPackets_value
  change w.terminalPackets.sum (fun p n ↦ n • p.value X A evaluation) =
      UniversalEnvelopingAlgebra.ι ℤ w.lieLift - w.highWord at hvalue
  have h := congrArg φ hvalue
  rw [map_finsuppSum] at h
  simp_rw [map_zsmul] at h
  rw [map_sub] at h
  have hlift : freeClassTwoTruncation X w.lieLift = 0 :=
    (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two X _).mpr
      w.lieLift_mem_gammaThree
  have hhigh : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X w.highWord ∈
      FreeLieDimension.associativeHigh X 5 :=
    FreeLieDimension.universalEnvelopingEquiv_mem_associativeHigh X 5 w.highWord_mem
  have hiota : φ (UniversalEnvelopingAlgebra.ι ℤ w.lieLift) = 0 := by
    change MvPolynomial.coeff e
      (adaptedFreeEnvelopingToClassTwoPBWSymbol X A evaluation
        (UniversalEnvelopingAlgebra.ι ℤ w.lieLift)) = 0
    rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_iota, hlift, map_zero]
    rfl
  have hhighzero : φ w.highWord = 0 := by
    exact adaptedPBWCoefficient_eq_zero_of_mem_associativeHigh
      X A evaluation hhigh e he
  rw [hiota, hhighzero, sub_zero] at h
  exact h

theorem terminalPackets_xCoefficient_eq_zero
    (w : AdaptedPresentationDimensionFiveWitness X A evaluation a)
    (i : FreeLieExactBasisIndex X 1) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient X A evaluation
        (Finsupp.single (.weightOne i) 1) (p.value X A evaluation)) = 0 := by
  apply w.terminalPackets_adaptedPBWCoefficient_eq_zero
  simp [adaptedClassTwoExponentWeight, adaptedClassTwoVariableWeight]

theorem terminalPackets_yCoefficient_eq_zero
    (w : AdaptedPresentationDimensionFiveWitness X A evaluation a)
    (k : FreeLieExactBasisIndex X 2) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient X A evaluation
        (Finsupp.single (.weightTwo k) 1) (p.value X A evaluation)) = 0 := by
  apply w.terminalPackets_adaptedPBWCoefficient_eq_zero
  simp [adaptedClassTwoExponentWeight, adaptedClassTwoVariableWeight]

theorem terminalPackets_xxCoefficient_eq_zero
    (w : AdaptedPresentationDimensionFiveWitness X A evaluation a)
    (i j : FreeLieExactBasisIndex X 1) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient X A evaluation
        (Finsupp.single (.weightOne i) 1 + Finsupp.single (.weightOne j) 1)
        (p.value X A evaluation)) = 0 := by
  apply w.terminalPackets_adaptedPBWCoefficient_eq_zero
  rw [adaptedClassTwoExponentWeight_add]
  simp [adaptedClassTwoVariableWeight]

theorem terminalPackets_xyCoefficient_eq_zero
    (w : AdaptedPresentationDimensionFiveWitness X A evaluation a)
    (i : FreeLieExactBasisIndex X 1) (k : FreeLieExactBasisIndex X 2) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient X A evaluation
        (Finsupp.single (.weightOne i) 1 + Finsupp.single (.weightTwo k) 1)
        (p.value X A evaluation)) = 0 := by
  apply w.terminalPackets_adaptedPBWCoefficient_eq_zero
  rw [adaptedClassTwoExponentWeight_add]
  simp [adaptedClassTwoVariableWeight]

theorem terminalPackets_yyCoefficient_eq_zero
    (w : AdaptedPresentationDimensionFiveWitness X A evaluation a)
    (k l : FreeLieExactBasisIndex X 2) :
    w.terminalPackets.sum (fun p n ↦ n •
      adaptedPBWCoefficient X A evaluation
        (Finsupp.single (.weightTwo k) 1 + Finsupp.single (.weightTwo l) 1)
        (p.value X A evaluation)) = 0 := by
  apply w.terminalPackets_adaptedPBWCoefficient_eq_zero
  rw [adaptedClassTwoExponentWeight_add]
  simp [adaptedClassTwoVariableWeight]

end AdaptedPresentationDimensionFiveWitness

namespace StandingReductionData

local notation "F" => CanonicalFreeLie L
local notation "ev" => canonicalFreeLieEvaluation L
local notation "I" => CoordinateI L
local notation "K" => CoordinateK L
local notation "BI" => FiniteClassTwoBasisIndex L

/-! ## The five adapted PBW exponents used by the coordinate proof -/

def xExponent (i : I) : BI →₀ ℕ :=
  Finsupp.single (.weightOne i) 1

def yExponent (k : K) : BI →₀ ℕ :=
  Finsupp.single (.weightTwo k) 1

def xxExponent (i j : I) : BI →₀ ℕ :=
  xExponent (L := L) i + xExponent (L := L) j

def xyExponent (i : I) (k : K) : BI →₀ ℕ :=
  xExponent (L := L) i + yExponent (L := L) k

def yyExponent (k l : K) : BI →₀ ℕ :=
  yExponent (L := L) k + yExponent (L := L) l

@[simp] theorem xExponent_weight (i : I) :
    adaptedClassTwoExponentWeight L (xExponent (L := L) i) = 1 := by
  simp [xExponent, adaptedClassTwoVariableWeight]

@[simp] theorem yExponent_weight (k : K) :
    adaptedClassTwoExponentWeight L (yExponent (L := L) k) = 2 := by
  simp [yExponent, adaptedClassTwoVariableWeight]

@[simp] theorem xxExponent_weight (i j : I) :
    adaptedClassTwoExponentWeight L (xxExponent (L := L) i j) = 2 := by
  simp [xxExponent, adaptedClassTwoExponentWeight_add]

@[simp] theorem xyExponent_weight (i : I) (k : K) :
    adaptedClassTwoExponentWeight L (xyExponent (L := L) i k) = 3 := by
  simp [xyExponent, adaptedClassTwoExponentWeight_add]

@[simp] theorem yyExponent_weight (k l : K) :
    adaptedClassTwoExponentWeight L (yyExponent (L := L) k l) = 4 := by
  simp [yyExponent, adaptedClassTwoExponentWeight_add]

/-- Exact weight-one component of a first adapted row. -/
theorem firstRow_component_one (R : StandingReductionData L) (i : I) :
    (⟨freeLieLengthComponent L 1 (collectedRelationRow L L ev 1 i : F),
      freeLieLengthComponent_mem_exact L 1 _⟩ : freeLieExact L 1) =
      (R.coordinateD i : ℤ) • collectedHomogeneousBasis L L ev 1 i := by
  simpa [freeLieExactProjection, coordinateD] using
    collectedRelationRow_head L L ev 1 i

/-- Exact weight-two component of a first adapted row. -/
theorem firstRow_component_two (R : StandingReductionData L) (i : I) :
    (⟨freeLieLengthComponent L 2 (collectedRelationRow L L ev 1 i : F),
      freeLieLengthComponent_mem_exact L 2 _⟩ : freeLieExact L 2) =
      -∑ k, R.coordinateB i k • collectedHomogeneousBasis L L ev 2 k := by
  apply Subtype.ext
  simpa [coordinateY, map_sum] using R.firstRow_degreeTwo_eq_neg_B_sum i

/-- The class-two truncation of `r_i` is literally `d_i x_i-B_i` in the shared basis. -/
theorem freeClassTwoTruncation_firstRow (R : StandingReductionData L) (i : I) :
    freeClassTwoTruncation L (collectedRelationRow L L ev 1 i : F) =
      finiteLowExactToClassTwo L
        ((R.coordinateD i : ℤ) • collectedHomogeneousBasis L L ev 1 i,
          -∑ k, R.coordinateB i k • collectedHomogeneousBasis L L ev 2 k) := by
  rw [freeClassTwoTruncation_eq_lowComponents]
  congr 1
  exact Prod.ext (R.firstRow_component_one i) (R.firstRow_component_two i)

/-- A weight-two row has no weight-one component. -/
theorem secondRow_component_one (R : StandingReductionData L) (k : K) :
    (⟨freeLieLengthComponent L 1 (collectedRelationRow L L ev 2 k : F),
      freeLieLengthComponent_mem_exact L 1 _⟩ : freeLieExact L 1) = 0 := by
  apply Subtype.ext
  exact freeLieLengthComponent_eq_zero_of_mem_lieHigh L
    (collectedRelationRow_mem_lieHigh L L ev 2 k) (by omega)

/-- Exact weight-two component of a second adapted row. -/
theorem secondRow_component_two (R : StandingReductionData L) (k : K) :
    (⟨freeLieLengthComponent L 2 (collectedRelationRow L L ev 2 k : F),
      freeLieLengthComponent_mem_exact L 2 _⟩ : freeLieExact L 2) =
      (R.coordinateE k : ℤ) • collectedHomogeneousBasis L L ev 2 k := by
  simpa [freeLieExactProjection, coordinateE] using
    collectedRelationRow_head L L ev 2 k

/-- The class-two truncation of `s_k` is literally `e_k y_k`. -/
theorem freeClassTwoTruncation_secondRow (R : StandingReductionData L) (k : K) :
    freeClassTwoTruncation L (collectedRelationRow L L ev 2 k : F) =
      finiteLowExactToClassTwo L
        (0, (R.coordinateE k : ℤ) • collectedHomogeneousBasis L L ev 2 k) := by
  rw [freeClassTwoTruncation_eq_lowComponents]
  congr 1
  exact Prod.ext (R.secondRow_component_one k) (R.secondRow_component_two k)

/-! ## Literal class-two symbols of the two adapted relation rows -/

theorem finiteLowExactToClassTwo_firstRow_coordinates
    (R : StandingReductionData L) (i : I) :
    finiteLowExactToClassTwo L
        ((R.coordinateD i : ℤ) • collectedHomogeneousBasis L L ev 1 i,
          -∑ k, R.coordinateB i k • collectedHomogeneousBasis L L ev 2 k) =
      (R.coordinateD i : ℤ) •
          adaptedHomogeneousClassTwoBasis L L ev (.weightOne i) -
        ∑ k, R.coordinateB i k •
          adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k) := by
  rw [show adaptedHomogeneousClassTwoBasis L L ev (.weightOne i) =
      finiteLowExactToClassTwo L
        (collectedHomogeneousBasis L L ev 1 i, 0) by
    rw [adaptedHomogeneousClassTwoBasis_weightOne]
    simp [finiteLowExactToClassTwo]]
  simp_rw [show ∀ k : K,
      adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k) =
        finiteLowExactToClassTwo L
          (0, collectedHomogeneousBasis L L ev 2 k) by
    intro k
    rw [adaptedHomogeneousClassTwoBasis_weightTwo]
    simp [finiteLowExactToClassTwo]]
  have hfirst := map_zsmul (finiteLowExactToClassTwo L) (R.coordinateD i : ℤ)
    (collectedHomogeneousBasis L L ev 1 i, (0 : freeLieExact L 2))
  have hsecond :
      finiteLowExactToClassTwo L
          (∑ k, R.coordinateB i k •
            ((0 : freeLieExact L 1), collectedHomogeneousBasis L L ev 2 k)) =
        ∑ k, R.coordinateB i k •
          finiteLowExactToClassTwo L
            (0, collectedHomogeneousBasis L L ev 2 k) := by
    rw [map_sum]
    simp_rw [map_zsmul]
  rw [← hfirst, ← hsecond, ← map_sub]
  congr 1
  apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem finiteLowExactToClassTwo_secondRow_coordinates
    (R : StandingReductionData L) (k : K) :
    finiteLowExactToClassTwo L
        (0, (R.coordinateE k : ℤ) • collectedHomogeneousBasis L L ev 2 k) =
      (R.coordinateE k : ℤ) •
        adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k) := by
  rw [show adaptedHomogeneousClassTwoBasis L L ev (.weightTwo k) =
      finiteLowExactToClassTwo L
        (0, collectedHomogeneousBasis L L ev 2 k) by
    rw [adaptedHomogeneousClassTwoBasis_weightTwo]
    simp [finiteLowExactToClassTwo]]
  calc
    finiteLowExactToClassTwo L
        (0, (R.coordinateE k : ℤ) • collectedHomogeneousBasis L L ev 2 k) =
      finiteLowExactToClassTwo L
        ((R.coordinateE k : ℤ) •
          ((0 : freeLieExact L 1), collectedHomogeneousBasis L L ev 2 k)) := by
            congr 1
    _ = _ := map_zsmul (finiteLowExactToClassTwo L) (R.coordinateE k : ℤ)
      ((0 : freeLieExact L 1), collectedHomogeneousBasis L L ev 2 k)

/-- The first row is exactly `dᵢ Xᵢ-∑ₖ BᵢₖYₖ` under the unchanged class-two PBW map. -/
theorem firstRow_PBWSymbol (R : StandingReductionData L) (i : I) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 1 i : F)) =
      (R.coordinateD i : ℤ) • MvPolynomial.X (.weightOne i) -
        ∑ k, R.coordinateB i k • MvPolynomial.X (.weightTwo k) := by
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_iota,
    R.freeClassTwoTruncation_firstRow,
    R.finiteLowExactToClassTwo_firstRow_coordinates,
    map_sub, map_sum, map_zsmul,
    adaptedHomogeneousClassTwoPolynomial_basis]
  simp_rw [map_zsmul, adaptedHomogeneousClassTwoPolynomial_basis]

/-- The second row is exactly `eₖYₖ`. -/
theorem secondRow_PBWSymbol (R : StandingReductionData L) (k : K) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol L L ev
        (UniversalEnvelopingAlgebra.ι ℤ
          (collectedRelationRow L L ev 2 k : F)) =
      (R.coordinateE k : ℤ) • MvPolynomial.X (.weightTwo k) := by
  rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_iota,
    R.freeClassTwoTruncation_secondRow,
    R.finiteLowExactToClassTwo_secondRow_coordinates,
    map_zsmul, adaptedHomogeneousClassTwoPolynomial_basis]

end StandingReductionData

end

end DegreeFive

end LieRings
