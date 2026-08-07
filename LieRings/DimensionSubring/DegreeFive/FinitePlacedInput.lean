import LieRings.DimensionSubring.DegreeFive.FinitePlacedCollector

/-!
# Finite input for the placed Smith collector

This file expands the original free generators in the chosen homogeneous basis.  It is the
first half of the finite-support bridge: after this change of basis, every relation word is a
literal finite sum of `FiniteSmithPlacedPacket`s.
-/

namespace LieRings

universe u v

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]
variable (L : Type v) [LieRing L]

local notation "F" => FreeLieAlgebra ℤ X
local notation "Factor" => LowHomogeneousBasisIndex X

/-- A free generator, bundled in the homogeneous component of weight one. -/
def freeGeneratorExactOne (x : X) : freeLieExact X 1 :=
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
def freeGeneratorLowCoefficients (x : X) : Factor →₀ ℤ :=
  ((freeLieExactBasis X 1).repr (freeGeneratorExactOne X x)).mapDomain
    (lowHomogeneousBasisIndexOf X (by omega) (by omega))

/-- Evaluation of the weight-one coordinate family gives back the original free generator. -/
theorem freeGeneratorLowCoefficients_sum (x : X) :
    (freeGeneratorLowCoefficients X x).sum
        (fun i c ↦ c • lowHomogeneousBasisValue X i) =
      FreeLieAlgebra.of ℤ x := by
  classical
  unfold freeGeneratorLowCoefficients
  rw [Finsupp.sum_mapDomain_index]
  · simp only [lowHomogeneousBasisValue_indexOf]
    have h := (freeLieExactBasis X 1).linearCombination_repr
      (freeGeneratorExactOne X x)
    calc
      ((freeLieExactBasis X 1).repr (freeGeneratorExactOne X x)).sum
          (fun i c ↦ c • ((freeLieExactBasis X 1 i : freeLieExact X 1) : F)) =
          (freeLieExact X 1).subtype
            (((freeLieExactBasis X 1).repr (freeGeneratorExactOne X x)).sum
              (fun i c ↦ c • freeLieExactBasis X 1 i)) := by
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
def generatorListLowCoefficients : List X → List Factor →₀ ℤ
  | [] => Finsupp.single [] 1
  | x :: xs =>
      (freeGeneratorLowCoefficients X x).sum fun i a ↦
        a • (generatorListLowCoefficients xs).mapDomain (i :: ·)

@[simp]
theorem generatorListLowCoefficients_nil :
    generatorListLowCoefficients X [] = Finsupp.single [] 1 := rfl

theorem generatorListLowCoefficients_cons (x : X) (xs : List X) :
    generatorListLowCoefficients X (x :: xs) =
      (freeGeneratorLowCoefficients X x).sum fun i a ↦
        a • (generatorListLowCoefficients X xs).mapDomain (i :: ·) := rfl

/-- The finite change-of-basis expansion preserves the corresponding enveloping word. -/
theorem generatorListLowCoefficients_value (xs : List X) :
    (generatorListLowCoefficients X xs).sum
        (fun is c ↦ c • envelopingWord ℤ F
          (is.map (lowHomogeneousBasisValue X))) =
      envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  induction xs with
  | nil => simp [generatorListLowCoefficients]
  | cons x xs ih =>
      rw [generatorListLowCoefficients_cons]
      rw [Finsupp.sum_sum_index (fun _ ↦ by simp)
        (fun is a b ↦ add_zsmul
          (envelopingWord ℤ F (is.map (lowHomogeneousBasisValue X))) a b)]
      simp only [List.map_cons]
      rw [envelopingWord_cons, ← freeGeneratorLowCoefficients_sum X x]
      rw [map_finsuppSum]
      let rightMul : UEA ℤ F →+ UEA ℤ F :=
        AddMonoidHom.mulRight (envelopingWord ℤ F
          (xs.map (FreeLieAlgebra.of ℤ)))
      change _ = rightMul ((freeGeneratorLowCoefficients X x).sum
        (fun i c ↦ UniversalEnvelopingAlgebra.ι ℤ
          (c • lowHomogeneousBasisValue X i)))
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro i hi
      rw [map_zsmul]
      rw [Finsupp.sum_smul_index (fun _ ↦ by simp)]
      rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
        (fun is a b ↦ by rw [mul_add, add_zsmul])]
      let c := freeGeneratorLowCoefficients X x i
      let A : UEA ℤ F := UniversalEnvelopingAlgebra.ι ℤ
        (lowHomogeneousBasisValue X i)
      calc
        (generatorListLowCoefficients X xs).sum (fun is m ↦
            (c * m) • envelopingWord ℤ F
              ((i :: is).map (lowHomogeneousBasisValue X))) =
            c • (generatorListLowCoefficients X xs).sum (fun is m ↦
              m • envelopingWord ℤ F
                ((i :: is).map (lowHomogeneousBasisValue X))) := by
              rw [Finsupp.smul_sum]
              apply Finsupp.sum_congr
              intro is his
              rw [smul_smul]
        _ = c • (A * (generatorListLowCoefficients X xs).sum (fun is m ↦
              m • envelopingWord ℤ F
                (is.map (lowHomogeneousBasisValue X)))) := by
              congr 1
              let leftMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulLeft A
              change _ = leftMul ((generatorListLowCoefficients X xs).sum
                (fun is m ↦ m • envelopingWord ℤ F
                  (is.map (lowHomogeneousBasisValue X))))
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

local notation "Packet" => FiniteSmithPlacedPacket X L evaluation
local notation "Row" => LowRelationSmithRowIndex X L evaluation

/-- A normalized Smith row followed by a list of homogeneous basis factors. -/
def finiteInitialRowPacket
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) (is : List Factor) :
    FiniteSmithPlacedPacket X L evaluation :=
  ⟨[], .row i, is⟩

/-- A weight-five remainder followed by a list of homogeneous basis factors. -/
def finiteInitialHighPacket
  (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap)
    (is : List Factor) : FiniteSmithPlacedPacket X L evaluation :=
  ⟨[], .high
    ⟨(iteratedRelationSmithRemainder X L evaluation 4 r : F),
      fourRowWeightFiveRemainder_mem_ker X L evaluation r⟩
    (fourRowWeightFiveRemainder_mem_lieHigh X L evaluation r), is⟩

/-- Change the external generator word to the homogeneous basis while retaining one row tag. -/
def finiteInitialRowWordCoefficients
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) (xs : List X) :
    FiniteSmithPlacedPacket X L evaluation →₀ ℤ :=
  (generatorListLowCoefficients X xs).mapDomain
    (finiteInitialRowPacket X L evaluation i)

/-- The same change of basis for the exact weight-five remainder. -/
def finiteInitialHighWordCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    FiniteSmithPlacedPacket X L evaluation →₀ ℤ :=
  (generatorListLowCoefficients X xs).mapDomain
    (finiteInitialHighPacket X L evaluation r)

theorem finiteInitialRowPacket_value
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) (is : List Factor) :
    (finiteInitialRowPacket X L evaluation i is).value X L evaluation =
      UniversalEnvelopingAlgebra.ι ℤ
          (lowRelationSmithRow X L evaluation i) *
        envelopingWord ℤ F (is.map (lowHomogeneousBasisValue X)) := by
  simp [finiteInitialRowPacket, FiniteSmithPlacedPacket.value,
    FiniteSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    FiniteCollectedRelation.value]

theorem finiteInitialHighPacket_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (is : List Factor) :
    (finiteInitialHighPacket X L evaluation r is).value X L evaluation =
      UniversalEnvelopingAlgebra.ι ℤ
          (iteratedRelationSmithRemainder X L evaluation 4 r : F) *
        envelopingWord ℤ F (is.map (lowHomogeneousBasisValue X)) := by
  simp [finiteInitialHighPacket, FiniteSmithPlacedPacket.value,
    FiniteSmithPlacedPacket.toAlgebraPacket, AlgebraPacket.value,
    FiniteCollectedRelation.value]

/-- Exact value of the row-word change of basis. -/
theorem finiteInitialRowWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (i : LowRelationSmithRowIndex X L evaluation) (xs : List X) :
    (finiteInitialRowWordCoefficients X L evaluation i xs).sum
        (fun p c ↦ c • p.value X L evaluation) =
      UniversalEnvelopingAlgebra.ι ℤ
          (lowRelationSmithRow X L evaluation i) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  unfold finiteInitialRowWordCoefficients
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ add_zsmul _ _ _)]
  let leftMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulLeft
    (UniversalEnvelopingAlgebra.ι ℤ (lowRelationSmithRow X L evaluation i))
  change _ = leftMul (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
  rw [← generatorListLowCoefficients_value X xs, map_finsuppSum]
  apply Finsupp.sum_congr
  intro is his
  rw [map_zsmul, finiteInitialRowPacket_value]
  rfl

/-- Exact value of the high-remainder word change of basis. -/
theorem finiteInitialHighWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    (finiteInitialHighWordCoefficients X L evaluation r xs).sum
        (fun p c ↦ c • p.value X L evaluation) =
      UniversalEnvelopingAlgebra.ι ℤ
          (iteratedRelationSmithRemainder X L evaluation 4 r : F) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  unfold finiteInitialHighWordCoefficients
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp)
    (fun _ _ _ ↦ add_zsmul _ _ _)]
  let leftMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulLeft
    (UniversalEnvelopingAlgebra.ι ℤ
      (iteratedRelationSmithRemainder X L evaluation 4 r : F))
  change _ = leftMul (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
  rw [← generatorListLowCoefficients_value X xs, map_finsuppSum]
  apply Finsupp.sum_congr
  intro is his
  rw [map_zsmul, finiteInitialHighPacket_value]
  rfl

/-- Expand one defining relation followed by a generator word into the exact finite family of
Smith-row packets (through weight four) and its certified weight-five remainder. -/
def finiteInitialRelationWordCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    FiniteSmithPlacedPacket X L evaluation →₀ ℤ :=
  (fourLowRelationSmithRowCoefficients X L evaluation r).sum
      (fun i c ↦ c • finiteInitialRowWordCoefficients X L evaluation i xs) +
    finiteInitialHighWordCoefficients X L evaluation r xs

/-- The Smith-row input expansion is exact in the universal enveloping algebra. -/
theorem finiteInitialRelationWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    (finiteInitialRelationWordCoefficients X L evaluation r xs).sum
        (fun p c ↦ c • p.value X L evaluation) =
      UniversalEnvelopingAlgebra.ι ℤ (r : F) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  classical
  let value : (FiniteSmithPlacedPacket X L evaluation →₀ ℤ) →+
      UEA ℤ F := (finitePlacedPacketCollector X L evaluation).evaluate
  have hvalue (c : FiniteSmithPlacedPacket X L evaluation →₀ ℤ) :
      value c = c.sum (fun p n ↦ n • p.value X L evaluation) := by
    rfl
  rw [finiteInitialRelationWordCoefficients, ← hvalue, map_add]
  rw [map_finsuppSum]
  simp only [map_zsmul]
  simp only [hvalue]
  simp_rw [finiteInitialRowWordCoefficients_value]
  rw [finiteInitialHighWordCoefficients_value]
  have hrows :
      (fourLowRelationSmithRowCoefficients X L evaluation r).sum
          (fun i c ↦ c •
            (UniversalEnvelopingAlgebra.ι ℤ
                (lowRelationSmithRow X L evaluation i) *
              envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))) =
        UniversalEnvelopingAlgebra.ι ℤ
            ((fourLowRelationSmithRowCoefficients X L evaluation r).sum
              (fun i c ↦ c • lowRelationSmithRow X L evaluation i)) *
          envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
    let rightMul : UEA ℤ F →+ UEA ℤ F := AddMonoidHom.mulRight
      (envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
    change _ = rightMul
      (UniversalEnvelopingAlgebra.ι ℤ
        ((fourLowRelationSmithRowCoefficients X L evaluation r).sum
          (fun i c ↦ c • lowRelationSmithRow X L evaluation i)))
    rw [map_finsuppSum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro i hi
    simp only [map_zsmul]
    rfl
  rw [hrows]
  have hrelation := congrArg
    (fun z : F ↦ UniversalEnvelopingAlgebra.ι ℤ z *
      envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)))
    (relation_eq_fourLowRelationSmithRows_add_weightFiveRemainder
      X L evaluation r)
  simpa only [map_add, add_mul] using hrelation.symm

/-- Extend the one-packet collector linearly to a finite packet family. -/
def finitePlacedCollect
    (evaluation : LieHom ℤ F L)
    (c : FiniteSmithPlacedPacket X L evaluation →₀ ℤ) :
    FiniteSmithPlacedPacket X L evaluation →₀ ℤ :=
  c.sum (fun p n ↦ n •
    (finitePlacedPacketCollector X L evaluation).normalForm p)

/-- Linear collection preserves the exact enveloping-algebra value of the whole family. -/
theorem finitePlacedCollect_value
    (evaluation : LieHom ℤ F L)
    (c : FiniteSmithPlacedPacket X L evaluation →₀ ℤ) :
    (finitePlacedPacketCollector X L evaluation).evaluate
        (finitePlacedCollect X L evaluation c) =
      (finitePlacedPacketCollector X L evaluation).evaluate c := by
  unfold finitePlacedCollect
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro p hp
  rw [map_zsmul, finitePlacedPacketCollector_evaluate_normalForm]
  rfl

/-- Every packet in a linearly collected family is terminal. -/
theorem finitePlacedPacketExpansion_eq_none_of_mem_finitePlacedCollect_support
    (evaluation : LieHom ℤ F L)
    (c : FiniteSmithPlacedPacket X L evaluation →₀ ℤ)
    (q : FiniteSmithPlacedPacket X L evaluation)
    (hq : q ∈ (finitePlacedCollect X L evaluation c).support) :
    finitePlacedPacketExpansion X L evaluation q = none := by
  classical
  by_contra hnonterminal
  rw [Finsupp.mem_support_iff] at hq
  unfold finitePlacedCollect at hq
  apply hq
  rw [Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  dsimp only
  rw [Finsupp.smul_apply, smul_eq_mul]
  have hnotmem : q ∉
      ((finitePlacedPacketCollector X L evaluation).normalForm p).support := by
    intro hmem
    exact hnonterminal
      (FiniteTaggedCollector.expansion_eq_none_of_mem_normalForm_support
        (finitePlacedPacketCollector X L evaluation) hmem)
  have hz : (finitePlacedPacketCollector X L evaluation).normalForm p q = 0 := by
    simpa [Finsupp.mem_support_iff] using hnotmem
  rw [hz, mul_zero]

/-- The completely collected finite input attached to one relation word. -/
def finiteCollectedRelationWordCoefficients
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    FiniteSmithPlacedPacket X L evaluation →₀ ℤ :=
  finitePlacedCollect X L evaluation
    (finiteInitialRelationWordCoefficients X L evaluation r xs)

/-- Exact evaluation of the completely collected relation word. -/
theorem finiteCollectedRelationWordCoefficients_value
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X) :
    (finitePlacedPacketCollector X L evaluation).evaluate
        (finiteCollectedRelationWordCoefficients X L evaluation r xs) =
      UniversalEnvelopingAlgebra.ι ℤ (r : F) *
        envelopingWord ℤ F (xs.map (FreeLieAlgebra.of ℤ)) := by
  rw [finiteCollectedRelationWordCoefficients, finitePlacedCollect_value]
  exact finiteInitialRelationWordCoefficients_value X L evaluation r xs

/-- Every packet occurring in the collected relation word is terminal. -/
theorem finiteCollectedRelationWordCoefficients_terminal
    (evaluation : LieHom ℤ F L)
    (r : LinearMap.ker evaluation.toLinearMap) (xs : List X)
    (q : FiniteSmithPlacedPacket X L evaluation)
    (hq : q ∈ (finiteCollectedRelationWordCoefficients
      X L evaluation r xs).support) :
    finitePlacedPacketExpansion X L evaluation q = none :=
  finitePlacedPacketExpansion_eq_none_of_mem_finitePlacedCollect_support
    X L evaluation _ q hq

end

end DegreeFive

end LieRings
