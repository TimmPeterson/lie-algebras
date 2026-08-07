import LieRings.DimensionSubring.DegreeFive.AdaptedPlacedCollector

/-!
# Coherent adapted input for the placed Smith collector

This file expands the original free generators in the chosen homogeneous basis.  It is the
first half of the finite-support bridge: after this change of basis, every relation word is a
literal finite sum of `AdaptedSmithPlacedPacket`s.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L] [Finite L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "Factor" => AdaptedLowBasisIndex X

variable (evaluation : LieHom ℤ F L)

/-- A free generator, bundled in the homogeneous component of weight one. -/
def adaptedFreeGeneratorExactOne (x : X) : freeLieExact X 1 :=
  ⟨FreeLieAlgebra.of ℤ x, ⟨FreeNonUnitalNonAssocAlgebra.of ℤ x, by
    intro w hw
    have hnz := Finsupp.mem_support_iff.mp hw
    have hw' : w = FreeMagma.of x := by
      by_contra hne
      exact hnz (by simp [FreeNonUnitalNonAssocAlgebra.of, hne])
    subst w
    rfl
  , rfl⟩⟩

/-- Coordinates of a free generator in the common basis of homogeneous factors of weights
one through four. -/
def adaptedFreeGeneratorLowCoefficients
    (evaluation : LieHom ℤ F L) (x : X) : Factor →₀ ℤ :=
  ((collectedHomogeneousBasis X L evaluation 1).repr (adaptedFreeGeneratorExactOne X x)).mapDomain
    (adaptedLowBasisIndexOf X (by omega) (by omega))

/-- Evaluation of the weight-one coordinate family gives back the original free generator. -/
theorem adaptedFreeGeneratorLowCoefficients_sum
    (evaluation : LieHom ℤ F L) (x : X) :
    (adaptedFreeGeneratorLowCoefficients X L evaluation x).sum
        (fun i c ↦ c • adaptedLowBasisValue X L evaluation i) =
      FreeLieAlgebra.of ℤ x := by
  classical
  unfold adaptedFreeGeneratorLowCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · simp only [adaptedLowBasisValue_indexOf]
    have h := (collectedHomogeneousBasis X L evaluation 1).linearCombination_repr
      (adaptedFreeGeneratorExactOne X x)
    calc
      ((collectedHomogeneousBasis X L evaluation 1).repr (adaptedFreeGeneratorExactOne X x)).sum
          (fun i c ↦ c • ((collectedHomogeneousBasis X L evaluation 1 i : freeLieExact X 1) : F)) =
          (freeLieExact X 1).subtype
            (((collectedHomogeneousBasis X L evaluation 1).repr (adaptedFreeGeneratorExactOne X x)).sum
              (fun i c ↦ c • collectedHomogeneousBasis X L evaluation 1 i)) := by
            rw [map_finsuppSum]
            apply Finsupp.sum_congr
            intro i hi
            rw [map_zsmul]
            rfl
      _ = FreeLieAlgebra.of ℤ x := congrArg Subtype.val h
  · intro i
    simp
  · intro i a b
    simp [add_smul]

/-- Expand a generator list into finite lists of homogeneous basis factors. -/
def adaptedGeneratorListLowCoefficients
    (evaluation : LieHom ℤ F L) : List X → List Factor →₀ ℤ
  | [] => Finsupp.single [] 1
  | x :: xs =>
      (adaptedFreeGeneratorLowCoefficients X L evaluation x).sum fun i a ↦
        a • (adaptedGeneratorListLowCoefficients evaluation xs).mapDomain (i :: ·)

@[simp]
theorem adaptedGeneratorListLowCoefficients_nil
    (evaluation : LieHom ℤ F L) :
    adaptedGeneratorListLowCoefficients X L evaluation [] = Finsupp.single [] 1 := rfl

theorem adaptedGeneratorListLowCoefficients_cons
    (evaluation : LieHom ℤ F L) (x : X) (xs : List X) :
    adaptedGeneratorListLowCoefficients X L evaluation (x :: xs) =
      (adaptedFreeGeneratorLowCoefficients X L evaluation x).sum fun i a ↦
        a • (adaptedGeneratorListLowCoefficients X L evaluation xs).mapDomain (i :: ·) := rfl

/-- The finite change-of-basis expansion preserves the corresponding enveloping word. -/
theorem adaptedGeneratorListLowCoefficients_value
    (evaluation : LieHom ℤ F L) (xs : List X) :
    (adaptedGeneratorListLowCoefficients X L evaluation xs).sum
        (fun is c ↦ c • envelopingWord ℤ F
          (is.map (adaptedLowBasisValue X L evaluation))) =
      envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  induction xs with
  | nil => simp [adaptedGeneratorListLowCoefficients]
  | cons x xs ih =>
      rw [adaptedGeneratorListLowCoefficients_cons]
      rw [Finsupp.sum_sum_index (fun _ ↦ by simp)
        (fun is a b ↦ add_zsmul
          (envelopingWord ℤ F (is.map (adaptedLowBasisValue X L evaluation))) a b)]
      simp only [List.map_cons]
      rw [envelopingWord_cons,
        ← adaptedFreeGeneratorLowCoefficients_sum X L evaluation x]
      rw [map_finsuppSum]
      let rightMul : UEA ℤ F →+ UEA ℤ F :=
        AddMonoidHom.mulRight (envelopingWord ℤ F
          (xs.map (FreeLieAlgebra.of ℤ)))
      change _ = rightMul
        ((adaptedFreeGeneratorLowCoefficients X L evaluation x).sum
        (fun i c ↦ UniversalEnvelopingAlgebra.ι ℤ
          (c • adaptedLowBasisValue X L evaluation i)))
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro i hi
      rw [map_zsmul]
      rw [Finsupp.sum_smul_index (fun _ ↦ by simp)]
      rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
        (fun is a b ↦ by rw [mul_add, add_zsmul])]
      let c := adaptedFreeGeneratorLowCoefficients X L evaluation x i
      let A : UEA ℤ F := UniversalEnvelopingAlgebra.ι ℤ
        (adaptedLowBasisValue X L evaluation i)
      calc
        (adaptedGeneratorListLowCoefficients X L evaluation xs).sum (fun is m ↦
            (c * m) • envelopingWord ℤ F
              ((i :: is).map (adaptedLowBasisValue X L evaluation))) =
            c • (adaptedGeneratorListLowCoefficients X L evaluation xs).sum (fun is m ↦
              m • envelopingWord ℤ F
                ((i :: is).map (adaptedLowBasisValue X L evaluation))) := by
              rw [Finsupp.smul_sum]
              apply Finsupp.sum_congr
              intro is his
              rw [smul_smul]
        _ = c • (A * (adaptedGeneratorListLowCoefficients X L evaluation xs).sum
            (fun is m ↦
              m • envelopingWord ℤ F
                (is.map (adaptedLowBasisValue X L evaluation)))) := by
              congr 1
              let leftMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulLeft A
              change _ = leftMul
                ((adaptedGeneratorListLowCoefficients X L evaluation xs).sum
                (fun is m ↦ m • envelopingWord ℤ F
                  (is.map (adaptedLowBasisValue X L evaluation))))
              rw [map_finsuppSum]
              apply Finsupp.sum_congr
              intro is his
              simp only [List.map_cons, envelopingWord_cons]
              rw [map_zsmul]
              rfl
        _ = c • (A * envelopingWord ℤ F
              (xs.map (FreeLieAlgebra.of ℤ))) := by rw [ih]
        _ = rightMul (c • A) := by
              simp only [rightMul, AddMonoidHom.mulRight_apply]
              rw [smul_mul_assoc]

variable (evaluation : LieHom ℤ F L)

local notation "Packet" => AdaptedSmithPlacedPacket X L evaluation
local notation "Row" => AdaptedLowRelationRowIndex X

/-- A normalized Smith row followed by a list of homogeneous basis factors. -/
def adaptedInitialRowPacket
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X) (is : List Factor) :
    AdaptedSmithPlacedPacket X L evaluation :=
  ⟨[], .row i, is⟩

/-- A weight-five remainder followed by a list of homogeneous basis factors. -/
def adaptedInitialHighPacket
  (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap)
    (is : List Factor) : AdaptedSmithPlacedPacket X L evaluation :=
  ⟨[], .high
    ⟨(iteratedCollectedRelationRemainder X L evaluation 4 r : F),
      fourCollectedWeightFiveRemainder_mem_ker X L evaluation r⟩
    (fourCollectedWeightFiveRemainder_mem_lieHigh X L evaluation r), is⟩

/-- Change the external generator word to the homogeneous basis while retaining one row tag. -/
def adaptedInitialRowWordCoefficients
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X) (xs : List X) :
    AdaptedSmithPlacedPacket X L evaluation →₀ ℤ :=
  (adaptedGeneratorListLowCoefficients X L evaluation xs).mapDomain
    (adaptedInitialRowPacket X L evaluation i)

/-- The same change of basis for the exact weight-five remainder. -/
def adaptedInitialHighWordCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    AdaptedSmithPlacedPacket X L evaluation →₀ ℤ :=
  (adaptedGeneratorListLowCoefficients X L evaluation xs).mapDomain
    (adaptedInitialHighPacket X L evaluation r)

theorem adaptedInitialRowPacket_value
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X) (is : List Factor) :
    (adaptedInitialRowPacket X L evaluation i is).value X L evaluation =
      UniversalEnvelopingAlgebra.ι ℤ
          (adaptedLowRelationRow X L evaluation i) *
        envelopingWord ℤ F (is.map (adaptedLowBasisValue X L evaluation)) := by
  simp [adaptedInitialRowPacket, AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value]

theorem adaptedInitialHighPacket_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (is : List Factor) :
    (adaptedInitialHighPacket X L evaluation r is).value X L evaluation =
      UniversalEnvelopingAlgebra.ι ℤ
          (iteratedCollectedRelationRemainder X L evaluation 4 r : F) *
        envelopingWord ℤ F (is.map (adaptedLowBasisValue X L evaluation)) := by
  simp [adaptedInitialHighPacket, AdaptedSmithPlacedPacket.value,
    AdaptedSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    AdaptedCollectedRelation.value]

/-- Exact value of the row-word change of basis. -/
theorem adaptedInitialRowWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (i : AdaptedLowRelationRowIndex X) (xs : List X) :
    (adaptedInitialRowWordCoefficients X L evaluation i xs).sum
        (fun p c ↦ c • p.value X L evaluation) =
      UniversalEnvelopingAlgebra.ι ℤ
          (adaptedLowRelationRow X L evaluation i) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  unfold adaptedInitialRowWordCoefficients
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ add_zsmul _ _ _)]
  let leftMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulLeft
    (UniversalEnvelopingAlgebra.ι ℤ (adaptedLowRelationRow X L evaluation i))
  change _ = leftMul (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
  rw [← adaptedGeneratorListLowCoefficients_value X L evaluation xs, map_finsuppSum]
  apply Finsupp.sum_congr
  intro is his
  rw [map_zsmul, adaptedInitialRowPacket_value]
  rfl

/-- Exact value of the high-remainder word change of basis. -/
theorem adaptedInitialHighWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    (adaptedInitialHighWordCoefficients X L evaluation r xs).sum
        (fun p c ↦ c • p.value X L evaluation) =
      UniversalEnvelopingAlgebra.ι ℤ
          (iteratedCollectedRelationRemainder X L evaluation 4 r : F) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  unfold adaptedInitialHighWordCoefficients
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ add_zsmul _ _ _)]
  let leftMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulLeft
    (UniversalEnvelopingAlgebra.ι ℤ
      (iteratedCollectedRelationRemainder X L evaluation 4 r : F))
  change _ = leftMul (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
  rw [← adaptedGeneratorListLowCoefficients_value X L evaluation xs, map_finsuppSum]
  apply Finsupp.sum_congr
  intro is his
  rw [map_zsmul, adaptedInitialHighPacket_value]
  rfl

/-- Expand one defining relation followed by a generator word into the exact finite family of
Smith-row packets (through weight four) and its certified weight-five remainder. -/
def adaptedInitialRelationWordCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    AdaptedSmithPlacedPacket X L evaluation →₀ ℤ :=
  (fourCollectedLowRowCoefficients X L evaluation r).sum
      (fun i c ↦ c • adaptedInitialRowWordCoefficients X L evaluation i xs) +
    adaptedInitialHighWordCoefficients X L evaluation r xs

/-- The Smith-row input expansion is exact in the universal enveloping algebra. -/
theorem adaptedInitialRelationWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    (adaptedInitialRelationWordCoefficients X L evaluation r xs).sum
        (fun p c ↦ c • p.value X L evaluation) =
      UniversalEnvelopingAlgebra.ι ℤ (r : F) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  let value : (AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) →+
      UEA ℤ F := (adaptedPlacedPacketCollector X L evaluation).evaluate
  have hvalue (c : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) :
      value c = c.sum (fun p n ↦ n • p.value X L evaluation) := by
    rfl
  rw [adaptedInitialRelationWordCoefficients, ← hvalue, map_add]
  rw [map_finsuppSum]
  simp only [map_zsmul]
  simp only [hvalue]
  simp_rw [adaptedInitialRowWordCoefficients_value]
  rw [adaptedInitialHighWordCoefficients_value]
  have hrows :
      (fourCollectedLowRowCoefficients X L evaluation r).sum
          (fun i c ↦ c •
            (UniversalEnvelopingAlgebra.ι ℤ
                (adaptedLowRelationRow X L evaluation i) *
              envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))) =
        UniversalEnvelopingAlgebra.ι ℤ
            ((fourCollectedLowRowCoefficients X L evaluation r).sum
              (fun i c ↦ c • adaptedLowRelationRow X L evaluation i)) *
          envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
    let rightMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulRight
      (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
    change _ = rightMul
      (UniversalEnvelopingAlgebra.ι ℤ
        ((fourCollectedLowRowCoefficients X L evaluation r).sum
          (fun i c ↦ c • adaptedLowRelationRow X L evaluation i)))
    rw [map_finsuppSum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro i hi
    simp only [map_zsmul]
    rfl
  rw [hrows]
  have hrelation := congrArg
    (fun z : F ↦ UniversalEnvelopingAlgebra.ι ℤ z *
      envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
    (relation_eq_fourCollectedLowRows_add_weightFiveRemainder
      X L evaluation r)
  simpa only [map_add, add_mul] using hrelation.symm

/-- Extend the one-packet collector linearly to a finite packet family. -/
def adaptedPlacedCollect
    (evaluation : LieHom ℤ F L)
    (c : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) :
    AdaptedSmithPlacedPacket X L evaluation →₀ ℤ :=
  c.sum (fun p n ↦ n •
    (adaptedPlacedPacketCollector X L evaluation).normalForm p)

/-- Linear collection preserves the exact enveloping-algebra value of the whole family. -/
theorem adaptedPlacedCollect_value
    (evaluation : LieHom ℤ F L)
    (c : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ) :
    (adaptedPlacedPacketCollector X L evaluation).evaluate
        (adaptedPlacedCollect X L evaluation c) =
      (adaptedPlacedPacketCollector X L evaluation).evaluate c := by
  unfold adaptedPlacedCollect
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, adaptedPlacedPacketCollector_evaluate_normalForm]
  rfl

/-- Every packet in a linearly collected family is terminal. -/
theorem adaptedPlacedPacketExpansion_eq_none_of_mem_adaptedPlacedCollect_support
    (evaluation : LieHom ℤ F L)
    (c : AdaptedSmithPlacedPacket X L evaluation →₀ ℤ)
    (q : AdaptedSmithPlacedPacket X L evaluation)
    (hq : q ∈ (adaptedPlacedCollect X L evaluation c).support) :
    adaptedPlacedPacketExpansion X L evaluation q = none := by
  classical
  by_contra hnonterminal
  rw [Finsupp.mem_support_iff] at hq
  unfold adaptedPlacedCollect at hq
  apply hq
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  dsimp only
  rw [Finsupp.smul_apply, smul_eq_mul]
  have hnotmem : q ∉
      ((adaptedPlacedPacketCollector X L evaluation).normalForm p).support := by
    intro hmem
    exact hnonterminal
      (FiniteTaggedCollector.expansion_eq_none_of_mem_normalForm_support
        (adaptedPlacedPacketCollector X L evaluation) hmem)
  have hz : (adaptedPlacedPacketCollector X L evaluation).normalForm p q = 0 := by
    simpa [Finsupp.mem_support_iff] using hnotmem
  rw [hz, mul_zero]

/-- The completely collected finite input attached to one relation word. -/
def adaptedCollectedRelationWordCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    AdaptedSmithPlacedPacket X L evaluation →₀ ℤ :=
  adaptedPlacedCollect X L evaluation
    (adaptedInitialRelationWordCoefficients X L evaluation r xs)

/-- Exact evaluation of the completely collected relation word. -/
theorem adaptedCollectedRelationWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    (adaptedPlacedPacketCollector X L evaluation).evaluate
        (adaptedCollectedRelationWordCoefficients X L evaluation r xs) =
      UniversalEnvelopingAlgebra.ι ℤ (r : F) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  rw [adaptedCollectedRelationWordCoefficients, adaptedPlacedCollect_value]
  exact adaptedInitialRelationWordCoefficients_value X L evaluation r xs

/-- Every packet occurring in the collected relation word is terminal. -/
theorem adaptedCollectedRelationWordCoefficients_terminal
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X)
    (q : AdaptedSmithPlacedPacket X L evaluation)
    (hq : q ∈ (adaptedCollectedRelationWordCoefficients
      X L evaluation r xs).support) :
    adaptedPlacedPacketExpansion X L evaluation q = none :=
  adaptedPlacedPacketExpansion_eq_none_of_mem_adaptedPlacedCollect_support
    X L evaluation _ q hq

end

end DegreeFive

end LieRings
