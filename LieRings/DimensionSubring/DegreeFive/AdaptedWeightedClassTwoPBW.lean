import LieRings.DimensionSubring.DegreeFive.AdaptedHomogeneousClassTwoPBW
import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedPackets
import LieRings.DimensionSubring.DegreeFive.FinitePlacedInput
import LieRings.DimensionSubring.DegreeFive.WeightedLedgerExtraction

/-!
# Weighted PBW projections in the shared adapted basis

The two blocks of the adapted class-two basis have weights one and two.  This file records
only the grading facts needed to discard the augmentation-five comparison word.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]
variable (evaluation : LieHom ℤ (FreeLieAlgebra ℤ X) L)

local notation "F" => FreeLieAlgebra ℤ X
local notation "P" => GeneratorModule X
local notation "M" => FreeClassTwo P
local notation "I" => FiniteClassTwoBasisIndex X
local notation "b" => adaptedHomogeneousClassTwoBasis X L evaluation
local notation "Poly" => MvPolynomial I ℤ

/-- Class-two truncation is completely determined by the first two homogeneous components. -/
theorem freeClassTwoTruncation_eq_lowComponents (f : F) :
    freeClassTwoTruncation X f = finiteLowExactToClassTwo X
      (⟨freeLieLengthComponent X 1 f, freeLieLengthComponent_mem_exact X 1 f⟩,
       ⟨freeLieLengthComponent X 2 f, freeLieLengthComponent_mem_exact X 2 f⟩) := by
  let f₁ : freeLieExact X 1 :=
    ⟨freeLieLengthComponent X 1 f, freeLieLengthComponent_mem_exact X 1 f⟩
  let f₂ : freeLieExact X 2 :=
    ⟨freeLieLengthComponent X 2 f, freeLieLengthComponent_mem_exact X 2 f⟩
  have hhighOne : f - (f₁ : F) - (f₂ : F) ∈
      FreeLieDimension.lieHigh X 1 := by
    rw [FreeLieDimension.lieHigh_one]
    trivial
  have hone : freeLieLengthComponent X 1 (f - (f₁ : F) - (f₂ : F)) = 0 := by
    rw [map_sub, map_sub, freeLieLengthComponent_coe_exact X 1 f₁,
      freeLieLengthComponent_coe_exact_of_ne X f₂ (by omega : 2 ≠ 1)]
    change freeLieLengthComponent X 1 f - freeLieLengthComponent X 1 f - 0 = 0
    abel
  have hhighTwo : f - (f₁ : F) - (f₂ : F) ∈
      FreeLieDimension.lieHigh X 2 := by
    simpa using mem_lieHigh_succ_of_component_eq_zero X hhighOne hone
  have htwo : freeLieLengthComponent X 2 (f - (f₁ : F) - (f₂ : F)) = 0 := by
    rw [map_sub, map_sub,
      freeLieLengthComponent_coe_exact_of_ne X f₁ (by omega : 1 ≠ 2),
      freeLieLengthComponent_coe_exact X 2 f₂]
    change freeLieLengthComponent X 2 f - 0 - freeLieLengthComponent X 2 f = 0
    abel
  have hhighThree : f - (f₁ : F) - (f₂ : F) ∈
      FreeLieDimension.lieHigh X 3 := by
    simpa using mem_lieHigh_succ_of_component_eq_zero X hhighTwo htwo
  have hker : freeClassTwoTruncation X (f - (f₁ : F) - (f₂ : F)) = 0 :=
    (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two X _).mpr
      (by simpa [FreeLieDimension.lieHigh_eq_lowerCentralSeries X 2] using hhighThree)
  rw [map_sub, map_sub] at hker
  change freeClassTwoTruncation X f =
    freeClassTwoTruncation X ((f₁ : F) + (f₂ : F))
  rw [map_add]
  rw [sub_sub] at hker
  exact sub_eq_zero.mp hker

/-- The bracket weight of a variable in the shared class-two basis. -/
def adaptedClassTwoVariableWeight : I → ℕ
  | .weightOne _ => 1
  | .weightTwo _ => 2

/-- Weighted degree of a PBW exponent. -/
def adaptedClassTwoExponentWeight (e : I →₀ ℕ) : ℕ :=
  e.sum fun i n ↦ n * adaptedClassTwoVariableWeight X i

theorem adaptedClassTwoExponentWeight_add (e f : I →₀ ℕ) :
    adaptedClassTwoExponentWeight X (e + f) =
      adaptedClassTwoExponentWeight X e + adaptedClassTwoExponentWeight X f := by
  classical
  simp [adaptedClassTwoExponentWeight, Finsupp.sum_add_index, add_mul, add_comm,
    add_left_comm, add_assoc]

@[simp]
theorem adaptedClassTwoExponentWeight_single (i : I) (n : ℕ) :
    adaptedClassTwoExponentWeight X (Finsupp.single i n) =
      n * adaptedClassTwoVariableWeight X i := by
  simp [adaptedClassTwoExponentWeight]

/-- A polynomial supported in one exact bracket weight. -/
def AdaptedClassTwoIsWeighted (n : ℕ) (p : Poly) : Prop :=
  ∀ e ∈ p.support, adaptedClassTwoExponentWeight X e = n

theorem adaptedClassTwoIsWeighted_zero (n : ℕ) :
    AdaptedClassTwoIsWeighted X n (0 : Poly) := by simp [AdaptedClassTwoIsWeighted]

theorem adaptedClassTwoIsWeighted_add {n : ℕ} {p q : Poly}
    (hp : AdaptedClassTwoIsWeighted X n p)
    (hq : AdaptedClassTwoIsWeighted X n q) :
    AdaptedClassTwoIsWeighted X n (p + q) := by
  classical
  intro e he
  have he' := MvPolynomial.support_add he
  simp only [Finset.mem_union] at he'
  exact he'.elim (hp e) (hq e)

theorem adaptedClassTwoIsWeighted_zsmul {n : ℕ} {p : Poly} (a : ℤ)
    (hp : AdaptedClassTwoIsWeighted X n p) :
    AdaptedClassTwoIsWeighted X n (a • p) := by
  classical
  intro e he
  exact hp e (MvPolynomial.support_smul he)

theorem adaptedClassTwoIsWeighted_monomial (e : I →₀ ℕ) (a : ℤ) :
    AdaptedClassTwoIsWeighted X (adaptedClassTwoExponentWeight X e)
      (MvPolynomial.monomial e a) := by
  classical
  intro f hf
  have hf' := MvPolynomial.support_monomial_subset hf
  exact congrArg (adaptedClassTwoExponentWeight X) (by simpa using hf')

theorem adaptedClassTwoIsWeighted_X (i : I) :
    AdaptedClassTwoIsWeighted X (adaptedClassTwoVariableWeight X i)
      (MvPolynomial.X i) := by
  simpa [MvPolynomial.X] using
    adaptedClassTwoIsWeighted_monomial X (Finsupp.single i 1) (1 : ℤ)

theorem adaptedClassTwoIsWeighted_mul {m n : ℕ} {p q : Poly}
    (hp : AdaptedClassTwoIsWeighted X m p)
    (hq : AdaptedClassTwoIsWeighted X n q) :
    AdaptedClassTwoIsWeighted X (m + n) (p * q) := by
  classical
  intro e he
  have he' := MvPolynomial.support_mul p q he
  rw [Finset.mem_add] at he'
  obtain ⟨f, hf, g, hg, hfg⟩ := he'
  rw [← hfg, adaptedClassTwoExponentWeight_add, hp f hf, hq g hg]

def adaptedClassTwoWeightedSubmodule (n : ℕ) : Submodule ℤ Poly where
  carrier := AdaptedClassTwoIsWeighted X n
  zero_mem' := adaptedClassTwoIsWeighted_zero X n
  add_mem' := adaptedClassTwoIsWeighted_add X
  smul_mem' a _ hp := adaptedClassTwoIsWeighted_zsmul X a hp

/-- Coordinates of an exact weight-two element have exact weight two. -/
theorem adaptedHomogeneousClassTwoPolynomial_exactTwo_isWeighted
    (x : freeLieExact X 2) :
    AdaptedClassTwoIsWeighted X 2
      (adaptedHomogeneousClassTwoPolynomial X L evaluation
        (finiteLowExactToClassTwo X (0, x))) := by
  let f : freeLieExact X 2 →ₗ[ℤ] Poly :=
    (adaptedHomogeneousClassTwoPolynomial X L evaluation).comp
      ((finiteLowExactToClassTwo X).comp (LinearMap.inr ℤ _ _))
  let N := adaptedClassTwoWeightedSubmodule X 2
  have hb (i : FreeLieExactBasisIndex X 2) : f
      (collectedHomogeneousBasis X L evaluation 2 i) ∈ N := by
    change AdaptedClassTwoIsWeighted X 2
      (adaptedHomogeneousClassTwoPolynomial X L evaluation
        (finiteLowExactToClassTwo X
          (0, collectedHomogeneousBasis X L evaluation 2 i)))
    rw [show finiteLowExactToClassTwo X
        (0, collectedHomogeneousBasis X L evaluation 2 i) = b (.weightTwo i) by
      rw [adaptedHomogeneousClassTwoBasis_weightTwo]
      simp [finiteLowExactToClassTwo]]
    rw [adaptedHomogeneousClassTwoPolynomial_basis]
    exact adaptedClassTwoIsWeighted_X X (.weightTwo i)
  let g : freeLieExact X 2 →ₗ[ℤ] N :=
    (collectedHomogeneousBasis X L evaluation 2).constr ℤ
      fun i ↦ ⟨f (collectedHomogeneousBasis X L evaluation 2 i), hb i⟩
  have hgf : N.subtype.comp g = f := by
    apply (collectedHomogeneousBasis X L evaluation 2).ext
    intro i
    simp [g]
  change f x ∈ N
  rw [← LinearMap.congr_fun hgf x]
  exact (g x).property

set_option maxHeartbeats 1000000 in
theorem adaptedCorrectionValue_isWeighted
    (i : FreeLieExactBasisIndex X 1) (k : I) :
    AdaptedClassTwoIsWeighted X 2 (adaptedCorrectionValue X L evaluation i k) := by
  cases k with
  | weightOne j =>
      by_cases h : (FiniteClassTwoBasisIndex.weightOne j : I) < .weightOne i
      · rw [adaptedCorrectionValue, if_pos h,
          adaptedHomogeneousClassTwoBasis_bracket_weightOne X L evaluation]
        exact adaptedHomogeneousClassTwoPolynomial_exactTwo_isWeighted X L evaluation _
      · rw [adaptedCorrectionValue, if_neg h]
        exact adaptedClassTwoIsWeighted_zero X 2
  | weightTwo j => exact adaptedClassTwoIsWeighted_zero X 2

theorem adaptedClassTwoExponentWeight_sub_single_add
    (e : I →₀ ℕ) (i : I) (hi : 0 < e i) :
    adaptedClassTwoExponentWeight X (e - Finsupp.single i 1) +
        adaptedClassTwoVariableWeight X i =
      adaptedClassTwoExponentWeight X e := by
  have hle : Finsupp.single i 1 ≤ e := by
    rw [Finsupp.single_le_iff]
    exact hi
  have h := adaptedClassTwoExponentWeight_add X
    (e - Finsupp.single i 1) (Finsupp.single i 1)
  rw [tsub_add_cancel_of_le hle, adaptedClassTwoExponentWeight_single, one_mul] at h
  exact h.symm

theorem adaptedCorrectionDerivation_monomial_isWeighted
    (i : FreeLieExactBasisIndex X 1) (e : I →₀ ℕ) (a : ℤ) :
    AdaptedClassTwoIsWeighted X (adaptedClassTwoExponentWeight X e + 1)
      (adaptedCorrectionDerivation X L evaluation i
        (MvPolynomial.monomial e a)) := by
  classical
  rw [adaptedCorrectionDerivation, MvPolynomial.mkDerivation_monomial]
  apply adaptedClassTwoIsWeighted_zsmul X a
  let N := adaptedClassTwoWeightedSubmodule X
    (adaptedClassTwoExponentWeight X e + 1)
  change e.sum (fun k n ↦
      MvPolynomial.monomial (e - Finsupp.single k 1) (n : ℤ) •
        adaptedCorrectionValue X L evaluation i k) ∈ N
  rw [Finsupp.sum]
  apply N.sum_mem
  intro k hk
  rw [Algebra.smul_def]
  cases k with
  | weightTwo j =>
      change MvPolynomial.monomial _ _ * 0 ∈ N
      simp
  | weightOne j =>
      have hj : 0 < e (FiniteClassTwoBasisIndex.weightOne j) :=
        (Finsupp.mem_support_iff.mp hk).bot_lt
      have hsub := adaptedClassTwoExponentWeight_sub_single_add X e
        (FiniteClassTwoBasisIndex.weightOne j) hj
      simp only [adaptedClassTwoVariableWeight] at hsub
      have hm := adaptedClassTwoIsWeighted_monomial X
        (e - Finsupp.single (FiniteClassTwoBasisIndex.weightOne j) 1)
        ((e (FiniteClassTwoBasisIndex.weightOne j) : ℕ) : ℤ)
      have hc := adaptedCorrectionValue_isWeighted X L evaluation i
        (FiniteClassTwoBasisIndex.weightOne j)
      have hp := adaptedClassTwoIsWeighted_mul X hm hc
      change AdaptedClassTwoIsWeighted X (adaptedClassTwoExponentWeight X e + 1) _
      convert hp using 1 <;> omega

theorem adaptedCorrectionDerivation_isWeighted
    (i : FreeLieExactBasisIndex X 1) {n : ℕ} {p : Poly}
    (hp : AdaptedClassTwoIsWeighted X n p) :
    AdaptedClassTwoIsWeighted X (n + 1)
      (adaptedCorrectionDerivation X L evaluation i p) := by
  classical
  let N := adaptedClassTwoWeightedSubmodule X (n + 1)
  rw [MvPolynomial.as_sum p, map_sum]
  apply N.sum_mem
  intro e he
  have hew := hp e he
  change AdaptedClassTwoIsWeighted X (n + 1)
    (adaptedCorrectionDerivation X L evaluation i
      (MvPolynomial.monomial e (MvPolynomial.coeff e p)))
  rw [← hew]
  exact adaptedCorrectionDerivation_monomial_isWeighted X L evaluation i e _

theorem adaptedHomogeneousClassTwoAction_weightOne_isWeighted
    (i : FreeLieExactBasisIndex X 1) {n : ℕ} {p : Poly}
    (hp : AdaptedClassTwoIsWeighted X n p) :
    AdaptedClassTwoIsWeighted X (n + 1)
      (adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne i)) p) := by
  rw [adaptedHomogeneousClassTwoAction_weightOne_apply]
  apply adaptedClassTwoIsWeighted_add X
  · have hx := adaptedClassTwoIsWeighted_X X
      (FiniteClassTwoBasisIndex.weightOne i)
    simpa [add_comm] using adaptedClassTwoIsWeighted_mul X hx hp
  · exact adaptedCorrectionDerivation_isWeighted X L evaluation i hp

theorem adaptedHomogeneousClassTwoAction_exactOne_isWeighted
    (x : freeLieExact X 1) {n : ℕ} {p : Poly}
    (hp : AdaptedClassTwoIsWeighted X n p) :
    AdaptedClassTwoIsWeighted X (n + 1)
      (adaptedHomogeneousClassTwoAction X L evaluation
        (finiteLowExactToClassTwo X (x, 0)) p) := by
  let N := adaptedClassTwoWeightedSubmodule X (n + 1)
  let f : freeLieExact X 1 →ₗ[ℤ] Poly :=
    (LinearMap.applyₗ p).comp
      ((adaptedHomogeneousClassTwoAction X L evaluation).comp
        ((finiteLowExactToClassTwo X).comp (LinearMap.inl ℤ _ _)))
  have hb (i : FreeLieExactBasisIndex X 1) :
      f (collectedHomogeneousBasis X L evaluation 1 i) ∈ N := by
    change AdaptedClassTwoIsWeighted X (n + 1)
      (adaptedHomogeneousClassTwoAction X L evaluation
        (finiteLowExactToClassTwo X
          (collectedHomogeneousBasis X L evaluation 1 i, 0)) p)
    rw [show finiteLowExactToClassTwo X
        (collectedHomogeneousBasis X L evaluation 1 i, 0) = b (.weightOne i) by
      rw [adaptedHomogeneousClassTwoBasis_weightOne]
      simp [finiteLowExactToClassTwo]]
    exact adaptedHomogeneousClassTwoAction_weightOne_isWeighted X L evaluation i hp
  let g : freeLieExact X 1 →ₗ[ℤ] N :=
    (collectedHomogeneousBasis X L evaluation 1).constr ℤ
      fun i ↦ ⟨f (collectedHomogeneousBasis X L evaluation 1 i), hb i⟩
  have hgf : N.subtype.comp g = f := by
    apply (collectedHomogeneousBasis X L evaluation 1).ext
    intro i
    simp [g]
  change f x ∈ N
  rw [← LinearMap.congr_fun hgf x]
  exact (g x).property

/-- The enveloping map induced by the class-two truncation. -/
def adaptedFreeEnvelopingToClassTwoEnveloping :
    UEA ℤ F →ₐ[ℤ] UEA ℤ M :=
  UniversalEnvelopingAlgebra.lift ℤ
    ((UniversalEnvelopingAlgebra.ι ℤ : LieHom ℤ M (UEA ℤ M)).comp
      (freeClassTwoTruncation X))

/-- Ordered PBW polynomial after class-two truncation, in the shared adapted basis. -/
def adaptedFreeEnvelopingToClassTwoPBWSymbol : UEA ℤ F →ₗ[ℤ] Poly :=
  (adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).vacuumEvaluation.comp
    (adaptedFreeEnvelopingToClassTwoEnveloping X).toLinearMap

@[simp]
theorem adaptedFreeEnvelopingToClassTwoPBWSymbol_iota (x : F) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation
        (UniversalEnvelopingAlgebra.ι ℤ x) =
      adaptedHomogeneousClassTwoPolynomial X L evaluation
        (freeClassTwoTruncation X x) := by
  change (adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).vacuumEvaluation
      (adaptedFreeEnvelopingToClassTwoEnveloping X
        (UniversalEnvelopingAlgebra.ι ℤ x)) = _
  rw [show adaptedFreeEnvelopingToClassTwoEnveloping X
      (UniversalEnvelopingAlgebra.ι ℤ x) =
      UniversalEnvelopingAlgebra.ι ℤ (freeClassTwoTruncation X x) by
    exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ x]
  rw [LieRings.PBW.TriangularRepresentation.vacuumEvaluation_apply,
    LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
  exact (adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).toLieHom_apply_one
    (freeClassTwoTruncation X x)

theorem adaptedFreeEnvelopingToClassTwoPBWSymbol_mul (u v : UEA ℤ F) :
    adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation (u * v) =
      (adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).envelopingAction
          (adaptedFreeEnvelopingToClassTwoEnveloping X u)
        (adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation v) := by
  change (adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).envelopingAction
      (adaptedFreeEnvelopingToClassTwoEnveloping X (u * v)) 1 = _
  rw [map_mul, map_mul]
  rfl

theorem adaptedFreeGeneratorPolynomial_isWeighted (x : X) :
    AdaptedClassTwoIsWeighted X 1
      (adaptedHomogeneousClassTwoPolynomial X L evaluation
        (freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x))) := by
  let ex : freeLieExact X 1 := freeGeneratorExactOne X x
  have htrunc : freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x) =
      finiteLowExactToClassTwo X (ex, 0) := by
    simp [ex, freeGeneratorExactOne, finiteLowExactToClassTwo]
  rw [htrunc]
  let N := adaptedClassTwoWeightedSubmodule X 1
  let f : freeLieExact X 1 →ₗ[ℤ] Poly :=
    (adaptedHomogeneousClassTwoPolynomial X L evaluation).comp
      ((finiteLowExactToClassTwo X).comp (LinearMap.inl ℤ _ _))
  have hb (i : FreeLieExactBasisIndex X 1) :
      f (collectedHomogeneousBasis X L evaluation 1 i) ∈ N := by
    change AdaptedClassTwoIsWeighted X 1
      (adaptedHomogeneousClassTwoPolynomial X L evaluation
        (finiteLowExactToClassTwo X
          (collectedHomogeneousBasis X L evaluation 1 i, 0)))
    rw [show finiteLowExactToClassTwo X
        (collectedHomogeneousBasis X L evaluation 1 i, 0) = b (.weightOne i) by
      rw [adaptedHomogeneousClassTwoBasis_weightOne]
      simp [finiteLowExactToClassTwo]]
    rw [adaptedHomogeneousClassTwoPolynomial_basis]
    exact adaptedClassTwoIsWeighted_X X (.weightOne i)
  let g : freeLieExact X 1 →ₗ[ℤ] N :=
    (collectedHomogeneousBasis X L evaluation 1).constr ℤ
      fun i ↦ ⟨f (collectedHomogeneousBasis X L evaluation 1 i), hb i⟩
  have hgf : N.subtype.comp g = f := by
    apply (collectedHomogeneousBasis X L evaluation 1).ext
    intro i
    simp [g]
  change f ex ∈ N
  rw [← LinearMap.congr_fun hgf ex]
  exact (g ex).property

theorem adaptedClassTwoIsWeighted_one :
    AdaptedClassTwoIsWeighted X 0 (1 : Poly) := by
  intro e he
  have : e = 0 := by simpa using he
  subst e
  simp [adaptedClassTwoExponentWeight]

/-- A word in original free generators has exactly its word length as adapted PBW weight. -/
theorem adaptedPBWSymbol_generatorWord_isWeighted (xs : List X) :
    AdaptedClassTwoIsWeighted X xs.length
      (adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation
        (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))) := by
  induction xs with
  | nil =>
      simp only [List.map_nil, envelopingWord_nil]
      change AdaptedClassTwoIsWeighted X 0
        ((adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).vacuumEvaluation
          (adaptedFreeEnvelopingToClassTwoEnveloping X 1))
      rw [map_one, LieRings.PBW.TriangularRepresentation.vacuumEvaluation_apply,
        map_one (adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).envelopingAction]
      exact adaptedClassTwoIsWeighted_one X
  | cons x xs ih =>
      simp only [List.map_cons, envelopingWord_cons, List.length_cons]
      rw [adaptedFreeEnvelopingToClassTwoPBWSymbol_mul,
        show adaptedFreeEnvelopingToClassTwoEnveloping X
            (UniversalEnvelopingAlgebra.ι ℤ (FreeLieAlgebra.of ℤ x)) =
          UniversalEnvelopingAlgebra.ι ℤ
            (freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x)) by
          exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ _ _,
        LieRings.PBW.TriangularRepresentation.envelopingAction_ι]
      let ex : freeLieExact X 1 := freeGeneratorExactOne X x
      have htrunc : freeClassTwoTruncation X (FreeLieAlgebra.of ℤ x) =
          finiteLowExactToClassTwo X (ex, 0) := by
        simp [ex, freeGeneratorExactOne, finiteLowExactToClassTwo]
      rw [htrunc]
      simpa [Nat.succ_eq_add_one] using
        adaptedHomogeneousClassTwoAction_exactOne_isWeighted X L evaluation ex ih

/-- Coefficient projection to a single adapted PBW monomial. -/
def adaptedPBWCoefficient (e : I →₀ ℕ) : UEA ℤ F →ₗ[ℤ] ℤ :=
  (MvPolynomial.lcoeff ℤ e).comp
    (adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation)

/-- Every adapted PBW coefficient of weight below `m` vanishes on augmentation degree `m`. -/
theorem adaptedPBWCoefficient_eq_zero_of_mem_associativeHigh
    {m : ℕ} {u : UEA ℤ F}
    (hu : FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u ∈
      FreeLieDimension.associativeHigh X m)
    (e : I →₀ ℕ) (he : adaptedClassTwoExponentWeight X e < m) :
    adaptedPBWCoefficient X L evaluation e u = 0 := by
  letI : LinearOrder X := WellOrderingRel.isWellOrder.linearOrder
  let c := FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X u)
  rw [← freeEnveloping_eq_generatorWord_sum X u, map_finsuppSum]
  classical
  apply Finset.sum_eq_zero
  intro w hw
  change adaptedPBWCoefficient X L evaluation e
      (c w • envelopingWord ℤ F
        ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ))) = 0
  rw [map_zsmul]
  change c w • MvPolynomial.coeff e
      (adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation
        (envelopingWord ℤ F ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ)))) = 0
  have hweight := adaptedPBWSymbol_generatorWord_isWeighted X L evaluation
    (FreeMonoid.toList w)
  have hlen : (FreeMonoid.toList w).length ≠ adaptedClassTwoExponentWeight X e := by
    have hm : m ≤ w.length := hu hw
    simpa using ne_of_gt (he.trans_le hm)
  have hcoeff : MvPolynomial.coeff e
      (adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation
        (envelopingWord ℤ F ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ)))) = 0 := by
    by_contra hn
    have hsupp : e ∈ (adaptedFreeEnvelopingToClassTwoPBWSymbol X L evaluation
        (envelopingWord ℤ F ((FreeMonoid.toList w).map (FreeLieAlgebra.of ℤ)))).support := by
      simpa [MvPolynomial.mem_support_iff] using hn
    exact hlen (hweight e hsupp).symm
  rw [hcoeff, smul_zero]

/-! ## Certified filtration of adapted packets -/

/-- A free-Lie element of bracket filtration at least `m` has associative filtration at least
`m` after the canonical PBW map. -/
theorem freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh
    {m : ℕ} {x : F} (hx : x ∈ FreeLieDimension.lieHigh X m) :
    PBW.freeLieToFreeAlgebra ℤ X x ∈ FreeLieDimension.associativeHigh X m := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [FreeLieDimension.freeLieToFreeAlgebra_mk]
  exact FreeLieDimension.magmaToFreeAlgebra_mem_high X hp

/-- A word of adapted homogeneous factors lies in the sum of their certified weights. -/
theorem adaptedLowEnvelopingWord_mem_associativeHigh
    (xs : List (AdaptedLowBasisIndex X)) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
        (envelopingWord ℤ F (xs.map (adaptedLowBasisValue X L evaluation))) ∈
      FreeLieDimension.associativeHigh X
        ((xs.map (adaptedLowBasisWeight X)).sum) := by
  induction xs with
  | nil =>
      simp only [List.map_nil, envelopingWord_nil, map_one, List.sum_nil]
      intro w hw
      exact Nat.zero_le _
  | cons i xs ih =>
      simp only [List.map_cons, envelopingWord_cons, List.sum_cons]
      rw [show FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedLowBasisValue X L evaluation i) *
              envelopingWord ℤ F
                (xs.map (adaptedLowBasisValue X L evaluation))) =
            FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
                (UniversalEnvelopingAlgebra.ι ℤ
                  (adaptedLowBasisValue X L evaluation i)) *
              FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
                (envelopingWord ℤ F
                  (xs.map (adaptedLowBasisValue X L evaluation))) by
          exact map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X) _ _]
      have hiota :=
        FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra X
          (adaptedLowBasisValue X L evaluation i)
      have hfirst :
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
              (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedLowBasisValue X L evaluation i)) ∈
            FreeLieDimension.associativeHigh X
              (adaptedLowBasisWeight X i) := by
        have hfree := freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh X
          (freeLieExact_mem_lieHigh X
          ⟨adaptedLowBasisValue X L evaluation i,
            adaptedLowBasisValue_mem_exact X L evaluation i⟩)
        exact hiota.symm ▸ hfree
      exact FreeLieDimension.associativeHigh_mul X hfirst ih

/-- The exact value of an adapted placed packet has its declared total filtration weight. -/
theorem adaptedPlacedPacket_value_mem_associativeHigh
    (p : AdaptedSmithPlacedPacket X L evaluation) :
    FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
        (p.value X L evaluation) ∈
      FreeLieDimension.associativeHigh X (p.totalWeight X) := by
  change FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
      (envelopingWord ℤ F
          (p.left.map (adaptedLowBasisValue X L evaluation)) *
        UniversalEnvelopingAlgebra.ι ℤ
          (p.relation.value X L evaluation) *
        envelopingWord ℤ F
          (p.right.map (adaptedLowBasisValue X L evaluation))) ∈ _
  rw [show FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
          ((envelopingWord ℤ F
              (p.left.map (adaptedLowBasisValue X L evaluation)) *
            UniversalEnvelopingAlgebra.ι ℤ
              (p.relation.value X L evaluation)) *
            envelopingWord ℤ F
              (p.right.map (adaptedLowBasisValue X L evaluation))) =
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
            (envelopingWord ℤ F
                (p.left.map (adaptedLowBasisValue X L evaluation)) *
              UniversalEnvelopingAlgebra.ι ℤ
                (p.relation.value X L evaluation)) *
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
            (envelopingWord ℤ F
              (p.right.map (adaptedLowBasisValue X L evaluation))) by
        exact map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X) _ _,
    show FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
          (envelopingWord ℤ F
              (p.left.map (adaptedLowBasisValue X L evaluation)) *
            UniversalEnvelopingAlgebra.ι ℤ
              (p.relation.value X L evaluation)) =
        FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
            (envelopingWord ℤ F
              (p.left.map (adaptedLowBasisValue X L evaluation))) *
          FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
            (UniversalEnvelopingAlgebra.ι ℤ
              (p.relation.value X L evaluation)) by
        exact map_mul (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X) _ _]
  have hiota :=
    FreeLieDimension.universalEnvelopingEquiv_ι_eq_freeLieToFreeAlgebra X
      (p.relation.value X L evaluation)
  have hleft := adaptedLowEnvelopingWord_mem_associativeHigh X L evaluation p.left
  have hrel :
      FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℤ X
          (UniversalEnvelopingAlgebra.ι ℤ
            (p.relation.value X L evaluation)) ∈
        FreeLieDimension.associativeHigh X
          (p.relation.weight X L evaluation) := by
    have hfree := freeLieToFreeAlgebra_mem_associativeHigh_of_mem_lieHigh X
      (p.relation.value_mem_lieHigh X L evaluation)
    exact hiota.symm ▸ hfree
  have hright := adaptedLowEnvelopingWord_mem_associativeHigh X L evaluation p.right
  have hlr := FreeLieDimension.associativeHigh_mul X hleft hrel
  have hall := FreeLieDimension.associativeHigh_mul X hlr hright
  convert hall using 1 <;>
    simp [AdaptedSmithPlacedPacket.totalWeight,
      AdaptedSmithPlacedPacket.externalWeight, add_assoc, add_comm, add_left_comm]

/-- Therefore a packet has no adapted PBW monomial below its declared total weight. -/
theorem adaptedPBWCoefficient_packet_eq_zero_of_lt
    (p : AdaptedSmithPlacedPacket X L evaluation)
    (e : I →₀ ℕ)
    (he : adaptedClassTwoExponentWeight X e < p.totalWeight X) :
    adaptedPBWCoefficient X L evaluation e (p.value X L evaluation) = 0 :=
  adaptedPBWCoefficient_eq_zero_of_mem_associativeHigh X L evaluation
    (adaptedPlacedPacket_value_mem_associativeHigh X L evaluation p) e he

end

end DegreeFive

end LieRings
