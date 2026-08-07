import LieRings.DimensionSubring.DegreeFive.AdaptedClassTwoBasis
import LieRings.PBW.TriangularRepresentation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie

/-!
# PBW in the homogeneous basis used by the adapted collector

This is the elementary triangular representation for the two-step quotient, but with the
independently chosen exact weight-one and weight-two bases used by the placed collector.  The
weight-two entries are central, and the correction attached to a weight-one entry only changes
earlier weight-one variables into the coordinate polynomial of their bracket.
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

/-- Polynomial coordinates in the collector's homogeneous class-two basis. -/
def adaptedHomogeneousClassTwoPolynomial : M →ₗ[ℤ] Poly :=
  LieRings.PBW.basisPolynomial ℤ M I b

@[simp]
theorem adaptedHomogeneousClassTwoPolynomial_basis (i : I) :
    adaptedHomogeneousClassTwoPolynomial X L evaluation (b i) = MvPolynomial.X i :=
  LieRings.PBW.basisPolynomial_basis ℤ M I b i

/-- Multiplication by a polynomial. -/
def adaptedPolynomialMul (p : Poly) : Module.End ℤ Poly :=
  LinearMap.mulLeft ℤ p

@[simp]
theorem adaptedPolynomialMul_apply (p q : Poly) :
    adaptedPolynomialMul X p q = p * q := rfl

/-- The triangular correction on variables for a weight-one basis element. -/
def adaptedCorrectionValue (i : FreeLieExactBasisIndex X 1) : I → Poly
  | .weightOne j =>
      if (FiniteClassTwoBasisIndex.weightOne j : I) < .weightOne i then
        adaptedHomogeneousClassTwoPolynomial X L evaluation
          ⁅b (.weightOne i), b (.weightOne j)⁆
      else 0
  | .weightTwo _ => 0

/-- The polynomial derivation determined by `adaptedCorrectionValue`. -/
def adaptedCorrectionDerivation
    (i : FreeLieExactBasisIndex X 1) : Derivation ℤ Poly Poly := by
  have hmodule : (inferInstance : Module ℤ Poly) =
      AddCommGroup.toIntModule Poly := Subsingleton.elim _ _
  cases hmodule
  let hTower : IsScalarTower ℤ Poly Poly :=
    ⟨fun n p q ↦ (AddMonoidHom.mulRight q).map_zsmul p n⟩
  exact @MvPolynomial.mkDerivation I ℤ Poly inferInstance inferInstance
    inferInstance inferInstance hTower (adaptedCorrectionValue X L evaluation i)

@[simp]
theorem adaptedCorrectionDerivation_X_weightOne
    (i j : FreeLieExactBasisIndex X 1) :
    adaptedCorrectionDerivation X L evaluation i
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j : I)) =
      if (FiniteClassTwoBasisIndex.weightOne j : I) < .weightOne i then
        adaptedHomogeneousClassTwoPolynomial X L evaluation
          ⁅b (.weightOne i), b (.weightOne j)⁆
      else 0 := by
  simp [adaptedCorrectionDerivation, adaptedCorrectionValue]

@[simp]
theorem adaptedCorrectionDerivation_X_weightTwo
    (i : FreeLieExactBasisIndex X 1)
    (j : FreeLieExactBasisIndex X 2) :
    adaptedCorrectionDerivation X L evaluation i
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo j : I)) = 0 := by
  simp [adaptedCorrectionDerivation, adaptedCorrectionValue]

def adaptedCorrectionEnd
    (i : FreeLieExactBasisIndex X 1) : Module.End ℤ Poly where
  toFun := adaptedCorrectionDerivation X L evaluation i
  map_add' p q := map_add (adaptedCorrectionDerivation X L evaluation i) p q
  map_smul' n p := map_zsmul (adaptedCorrectionDerivation X L evaluation i) n p

@[simp]
theorem adaptedCorrectionEnd_apply
    (i : FreeLieExactBasisIndex X 1) (p : Poly) :
    adaptedCorrectionEnd X L evaluation i p = adaptedCorrectionDerivation X L evaluation i p := rfl

/-- An exact weight-two element gives a central class-two element. -/
theorem finiteLowExact_weightTwo_lie (x : freeLieExact X 2) (y : M) :
    ⁅finiteLowExactToClassTwo X (0, x), y⁆ = 0 := by
  obtain ⟨f, rfl⟩ := freeClassTwoTruncation_surjective X y
  rw [show finiteLowExactToClassTwo X (0, x) =
      freeClassTwoTruncation X (x : F) by
    simp [finiteLowExactToClassTwo]]
  change ⁅freeClassTwoTruncation X (x : F),
    freeClassTwoTruncation X f⁆ = 0
  rw [← LieHom.map_lie]
  change freeClassTwoTruncation X ⁅(x : F), f⁆ = 0
  apply (freeClassTwoTruncation_eq_zero_iff_mem_lowerCentralSeries_two X _).mpr
  have hxHigh : (x : F) ∈ FreeLieDimension.lieHigh X 2 := by
    obtain ⟨p, hp, hpx⟩ := x.property
    refine ⟨p, ?_, hpx⟩
    intro w hw
    exact (hp hw).ge
  have hx : (x : F) ∈ lowerCentralSeries ℤ F 1 := by
    rw [FreeLieDimension.lieHigh_eq_lowerCentralSeries X 1] at hxHigh
    exact hxHigh
  rw [lowerCentralSeries, LieModule.lowerCentralSeries_succ,
    ← LieSubmodule.lie_comm]
  exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top f)

/-- The bracket of two weight-one basis entries is represented entirely in exact weight two. -/
def adaptedHomogeneousBasisBracketExactTwo
    (i j : FreeLieExactBasisIndex X 1) : freeLieExact X 2 :=
  ⟨⁅((collectedHomogeneousBasis X L evaluation 1 i : freeLieExact X 1) : F),
      ((collectedHomogeneousBasis X L evaluation 1 j : freeLieExact X 1) : F)⁆,
    freeLieExact_bracket_mem X (collectedHomogeneousBasis X L evaluation 1 i)
      (collectedHomogeneousBasis X L evaluation 1 j)⟩

theorem adaptedHomogeneousClassTwoBasis_bracket_weightOne
    (i j : FreeLieExactBasisIndex X 1) :
    ⁅b (.weightOne i), b (.weightOne j)⁆ =
      finiteLowExactToClassTwo X
        (0, adaptedHomogeneousBasisBracketExactTwo X L evaluation i j) := by
  rw [adaptedHomogeneousClassTwoBasis_weightOne,
    adaptedHomogeneousClassTwoBasis_weightOne, ← LieHom.map_lie]
  simp [finiteLowExactToClassTwo,
    adaptedHomogeneousBasisBracketExactTwo]

/-- Every correction derivation kills the coordinate polynomial of an exact weight-two
element. -/
theorem adaptedCorrectionDerivation_exactTwo
    (i : FreeLieExactBasisIndex X 1) (x : freeLieExact X 2) :
    adaptedCorrectionDerivation X L evaluation i
      (adaptedHomogeneousClassTwoPolynomial X L evaluation
        (finiteLowExactToClassTwo X (0, x))) = 0 := by
  let f : freeLieExact X 2 →ₗ[ℤ] Poly :=
    (adaptedCorrectionEnd X L evaluation i).comp
      ((adaptedHomogeneousClassTwoPolynomial X L evaluation).comp
        ((finiteLowExactToClassTwo X).comp (LinearMap.inr ℤ _ _)))
  have hf : f = 0 := by
    apply (collectedHomogeneousBasis X L evaluation 2).ext
    intro j
    change adaptedCorrectionDerivation X L evaluation i
      (adaptedHomogeneousClassTwoPolynomial X L evaluation
        (finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 j))) = 0
    rw [show finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 j) =
        b (.weightTwo j) by
      rw [adaptedHomogeneousClassTwoBasis_weightTwo]
      simp [finiteLowExactToClassTwo]]
    rw [adaptedHomogeneousClassTwoPolynomial_basis,
      adaptedCorrectionDerivation_X_weightTwo]
  exact LinearMap.congr_fun hf x

@[simp]
theorem adaptedCorrectionDerivation_bracket
    (i : FreeLieExactBasisIndex X 1) (x y : M) :
    adaptedCorrectionDerivation X L evaluation i
      (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x, y⁆) = 0 := by
  let q : M →ₗ[ℤ] M →ₗ[ℤ] Poly :=
    LinearMap.mk₂ ℤ (fun x y ↦ adaptedCorrectionDerivation X L evaluation i
        (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x, y⁆))
      (by
        intro x₁ x₂ z
        change adaptedCorrectionDerivation X L evaluation i
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x₁ + x₂, z⁆) = _
        rw [add_lie, map_add, map_add])
      (by
        intro n x₁ z
        change adaptedCorrectionDerivation X L evaluation i
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅n • x₁, z⁆) = _
        rw [smul_lie, map_smul, map_zsmul])
      (by
        intro x₁ y₁ y₂
        change adaptedCorrectionDerivation X L evaluation i
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x₁, y₁ + y₂⁆) = _
        rw [lie_add, map_add, map_add])
      (by
        intro n x₁ y₁
        change adaptedCorrectionDerivation X L evaluation i
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x₁, n • y₁⁆) = _
        rw [lie_smul, map_smul, map_zsmul])
  have hq : q = 0 := by
    apply LinearMap.ext_basis b b
    intro j k
    change adaptedCorrectionDerivation X L evaluation i
      (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅b j, b k⁆) = 0
    cases j with
    | weightOne j =>
        cases k with
        | weightOne k =>
            rw [adaptedHomogeneousClassTwoBasis_bracket_weightOne]
            exact adaptedCorrectionDerivation_exactTwo X L evaluation i
              (adaptedHomogeneousBasisBracketExactTwo X L evaluation j k)
        | weightTwo k =>
            rw [adaptedHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X
                (collectedHomogeneousBasis X L evaluation 2 k : F) =
                finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 k) by
              simp [finiteLowExactToClassTwo]]
            rw [show ⁅b (.weightOne j),
                finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 k)⁆ =
                -⁅finiteLowExactToClassTwo X
                  (0, collectedHomogeneousBasis X L evaluation 2 k), b (.weightOne j)⁆ by
              exact (lie_skew
                (b (.weightOne j))
                (finiteLowExactToClassTwo X
                  (0, collectedHomogeneousBasis X L evaluation 2 k) : M)).symm,
              finiteLowExact_weightTwo_lie X (collectedHomogeneousBasis X L evaluation 2 k),
              neg_zero, map_zero, Derivation.map_zero]
    | weightTwo j =>
        rw [adaptedHomogeneousClassTwoBasis_weightTwo]
        rw [show freeClassTwoTruncation X
            (collectedHomogeneousBasis X L evaluation 2 j : F) =
            finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 j) by
          simp [finiteLowExactToClassTwo]]
        rw [finiteLowExact_weightTwo_lie X (collectedHomogeneousBasis X L evaluation 2 j),
          map_zero, Derivation.map_zero]
  exact DFunLike.congr_fun (DFunLike.congr_fun hq x) y

/-- The correction derivations commute. -/
theorem adaptedCorrectionDerivation_commute
    (i j : FreeLieExactBasisIndex X 1) (p : Poly) :
    adaptedCorrectionDerivation X L evaluation i (adaptedCorrectionDerivation X L evaluation j p) =
      adaptedCorrectionDerivation X L evaluation j (adaptedCorrectionDerivation X L evaluation i p) := by
  have hX (k : I) :
      adaptedCorrectionDerivation X L evaluation i
          (adaptedCorrectionDerivation X L evaluation j (MvPolynomial.X k)) =
        adaptedCorrectionDerivation X L evaluation j
          (adaptedCorrectionDerivation X L evaluation i (MvPolynomial.X k)) := by
    cases k with
    | weightOne k =>
        simp only [adaptedCorrectionDerivation_X_weightOne]
        split_ifs <;> simp only [adaptedCorrectionDerivation_bracket,
          Derivation.map_zero]
    | weightTwo k =>
        simp only [adaptedCorrectionDerivation_X_weightTwo, Derivation.map_zero]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
      rw [Derivation.leibniz, Derivation.leibniz]
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
      rw [map_add, map_add, Derivation.leibniz, Derivation.leibniz,
        Derivation.leibniz, Derivation.leibniz, hp, hX k]
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
      ring

/-- The antisymmetric correction difference is the bracket coordinate polynomial. -/
theorem adaptedCorrectionDerivation_X_sub
    (i j : FreeLieExactBasisIndex X 1) :
    adaptedCorrectionDerivation X L evaluation i
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j : I)) -
      adaptedCorrectionDerivation X L evaluation j
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i : I)) =
      adaptedHomogeneousClassTwoPolynomial X L evaluation
        ⁅b (.weightOne i), b (.weightOne j)⁆ := by
  rcases lt_trichotomy (FiniteClassTwoBasisIndex.weightOne i : I)
      (.weightOne j) with hij | hij | hij
  · have hji : ¬ (FiniteClassTwoBasisIndex.weightOne j : I) < .weightOne i :=
      not_lt_of_ge hij.le
    rw [adaptedCorrectionDerivation_X_weightOne,
      adaptedCorrectionDerivation_X_weightOne]
    simp only [hij, hji, if_true, if_false, zero_sub]
    rw [← map_neg, lie_skew]
  · have heq : i = j := FiniteClassTwoBasisIndex.weightOne.inj hij
    subst j
    simp
  · have hij' : ¬ (FiniteClassTwoBasisIndex.weightOne i : I) < .weightOne j :=
      not_lt_of_ge hij.le
    rw [adaptedCorrectionDerivation_X_weightOne,
      adaptedCorrectionDerivation_X_weightOne]
    simp [hij, hij']

/-- Basis operators for the collector's homogeneous class-two basis. -/
def adaptedHomogeneousClassTwoActionBasis : I → Module.End ℤ Poly
  | .weightOne i =>
      adaptedPolynomialMul X (MvPolynomial.X (.weightOne i)) +
        adaptedCorrectionEnd X L evaluation i
  | .weightTwo i =>
      adaptedPolynomialMul X (MvPolynomial.X (.weightTwo i))

/-- Extend the basis operators linearly. -/
def adaptedHomogeneousClassTwoAction : M →ₗ[ℤ] Module.End ℤ Poly :=
  (Finsupp.linearCombination ℤ (adaptedHomogeneousClassTwoActionBasis X L evaluation)).comp
    (adaptedHomogeneousClassTwoBasis X L evaluation).repr.toLinearMap

@[simp]
theorem adaptedHomogeneousClassTwoAction_basis (i : I) :
    adaptedHomogeneousClassTwoAction X L evaluation (b i) =
      adaptedHomogeneousClassTwoActionBasis X L evaluation i := by
  simp [adaptedHomogeneousClassTwoAction]

@[simp]
theorem adaptedHomogeneousClassTwoAction_weightOne_apply
    (i : FreeLieExactBasisIndex X 1) (p : Poly) :
    adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne i)) p =
      MvPolynomial.X (.weightOne i) * p +
        adaptedCorrectionDerivation X L evaluation i p := by
  rw [adaptedHomogeneousClassTwoAction_basis]
  rfl

@[simp]
theorem adaptedHomogeneousClassTwoAction_weightTwo_apply
    (i : FreeLieExactBasisIndex X 2) (p : Poly) :
    adaptedHomogeneousClassTwoAction X L evaluation (b (.weightTwo i)) p =
      MvPolynomial.X (.weightTwo i) * p := by
  rw [adaptedHomogeneousClassTwoAction_basis]
  rfl

/-- Multiplication depends linearly on the polynomial. -/
def adaptedPolynomialMulLinear : Poly →ₗ[ℤ] Module.End ℤ Poly where
  toFun := adaptedPolynomialMul X
  map_add' p q := by
    apply LinearMap.ext
    intro r
    exact add_mul p q r
  map_smul' n p := by
    apply LinearMap.ext
    intro q
    change (n • p) * q = n • (p * q)
    exact smul_mul_assoc n p q

/-- Every exact weight-two element acts by multiplication by its coordinate polynomial. -/
theorem adaptedHomogeneousClassTwoAction_exactTwo (x : freeLieExact X 2) :
    adaptedHomogeneousClassTwoAction X L evaluation
        (finiteLowExactToClassTwo X (0, x)) =
      adaptedPolynomialMul X
        (adaptedHomogeneousClassTwoPolynomial X L evaluation
          (finiteLowExactToClassTwo X (0, x))) := by
  let lhs : freeLieExact X 2 →ₗ[ℤ] Module.End ℤ Poly :=
    (adaptedHomogeneousClassTwoAction X L evaluation).comp
      ((finiteLowExactToClassTwo X).comp (LinearMap.inr ℤ _ _))
  let rhs : freeLieExact X 2 →ₗ[ℤ] Module.End ℤ Poly :=
    (adaptedPolynomialMulLinear X).comp
      ((adaptedHomogeneousClassTwoPolynomial X L evaluation).comp
        ((finiteLowExactToClassTwo X).comp (LinearMap.inr ℤ _ _)))
  have h : lhs = rhs := by
    apply (collectedHomogeneousBasis X L evaluation 2).ext
    intro i
    change adaptedHomogeneousClassTwoAction X L evaluation
        (finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 i)) =
      adaptedPolynomialMul X (adaptedHomogeneousClassTwoPolynomial X L evaluation
        (finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 i)))
    rw [show finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 i) =
        b (.weightTwo i) by
      rw [adaptedHomogeneousClassTwoBasis_weightTwo]
      simp [finiteLowExactToClassTwo]]
    rw [adaptedHomogeneousClassTwoAction_basis,
      adaptedHomogeneousClassTwoPolynomial_basis]
    rfl
  exact LinearMap.congr_fun h x

@[simp]
theorem adaptedHomogeneousClassTwoAction_bracket (x y : M) :
    adaptedHomogeneousClassTwoAction X L evaluation ⁅x, y⁆ =
      adaptedPolynomialMul X
        (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x, y⁆) := by
  let lhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun x y ↦ adaptedHomogeneousClassTwoAction X L evaluation ⁅x, y⁆)
      (by
        intro x₁ x₂ z
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅x₁ + x₂, z⁆ = _
        rw [add_lie, map_add])
      (by
        intro n x z
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅n • x, z⁆ = _
        rw [smul_lie, map_smul])
      (by
        intro x y₁ y₂
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅x, y₁ + y₂⁆ = _
        rw [lie_add, map_add])
      (by
        intro n x y
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅x, n • y⁆ = _
        rw [lie_smul, map_smul])
  let rhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun x y ↦ adaptedPolynomialMul X
        (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x, y⁆))
      (by
        intro x₁ x₂ z
        change adaptedPolynomialMul X
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x₁ + x₂, z⁆) = _
        rw [add_lie, map_add]
        exact (adaptedPolynomialMulLinear X).map_add _ _)
      (by
        intro n x z
        change adaptedPolynomialMul X
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅n • x, z⁆) = _
        rw [smul_lie, map_smul]
        exact (adaptedPolynomialMulLinear X).map_smul n _)
      (by
        intro x y₁ y₂
        change adaptedPolynomialMul X
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x, y₁ + y₂⁆) = _
        rw [lie_add, map_add]
        exact (adaptedPolynomialMulLinear X).map_add _ _)
      (by
        intro n x y
        change adaptedPolynomialMul X
          (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅x, n • y⁆) = _
        rw [lie_smul, map_smul]
        exact (adaptedPolynomialMulLinear X).map_smul n _)
  have h : lhs = rhs := by
    apply LinearMap.ext_basis b b
    intro i j
    change adaptedHomogeneousClassTwoAction X L evaluation ⁅b i, b j⁆ =
      adaptedPolynomialMul X
        (adaptedHomogeneousClassTwoPolynomial X L evaluation ⁅b i, b j⁆)
    cases i with
    | weightOne i =>
        cases j with
        | weightOne j =>
            rw [adaptedHomogeneousClassTwoBasis_bracket_weightOne,
              adaptedHomogeneousClassTwoAction_exactTwo]
        | weightTwo j =>
            rw [adaptedHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (collectedHomogeneousBasis X L evaluation 2 j : F) =
                finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 j) by
              simp [finiteLowExactToClassTwo]]
            rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                (0, collectedHomogeneousBasis X L evaluation 2 j)⁆ = 0 by
              rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j)⁆ =
                  -⁅finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j), b (.weightOne i)⁆ by
                exact (lie_skew (b (.weightOne i))
                  (finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j) : M)).symm]
              rw [finiteLowExact_weightTwo_lie, neg_zero], map_zero, map_zero]
            apply LinearMap.ext
            intro p
            simp [adaptedPolynomialMul]
    | weightTwo i =>
        rw [adaptedHomogeneousClassTwoBasis_weightTwo]
        rw [show freeClassTwoTruncation X (collectedHomogeneousBasis X L evaluation 2 i : F) =
            finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 i) by
          simp [finiteLowExactToClassTwo]]
        rw [finiteLowExact_weightTwo_lie, map_zero, map_zero]
        apply LinearMap.ext
        intro p
        simp [adaptedPolynomialMul]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- The commutator of two weight-one basis operators is multiplication by the bracket. -/
theorem adaptedHomogeneousClassTwoAction_weightOne_commutator
    (i j : FreeLieExactBasisIndex X 1) :
    ⁅adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne i)),
      adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne j))⁆ =
      adaptedPolynomialMul X
        (adaptedHomogeneousClassTwoPolynomial X L evaluation
          ⁅b (.weightOne i), b (.weightOne j)⁆) := by
  apply LinearMap.ext
  intro p
  change adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne i))
      (adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne j)) p) -
    adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne j))
      (adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne i)) p) = _
  rw [adaptedHomogeneousClassTwoAction_weightOne_apply,
    adaptedHomogeneousClassTwoAction_weightOne_apply,
    adaptedHomogeneousClassTwoAction_weightOne_apply,
    adaptedHomogeneousClassTwoAction_weightOne_apply]
  rw [map_add, map_add, Derivation.leibniz, Derivation.leibniz,
    adaptedCorrectionDerivation_commute X L evaluation i j p]
  rw [← adaptedCorrectionDerivation_X_sub X L evaluation i j]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  simp [adaptedPolynomialMul]
  split_ifs <;> ring

/-- The explicit homogeneous action respects the Lie bracket. -/
theorem adaptedHomogeneousClassTwoAction_map_lie (x y : M) :
    adaptedHomogeneousClassTwoAction X L evaluation ⁅x, y⁆ =
      ⁅adaptedHomogeneousClassTwoAction X L evaluation x,
        adaptedHomogeneousClassTwoAction X L evaluation y⁆ := by
  let lhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun a c ↦ adaptedHomogeneousClassTwoAction X L evaluation ⁅a, c⁆)
      (by
        intro x₁ x₂ z
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅x₁ + x₂, z⁆ = _
        rw [add_lie, map_add])
      (by
        intro n x z
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅n • x, z⁆ = _
        rw [smul_lie, map_smul])
      (by
        intro x y₁ y₂
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅x, y₁ + y₂⁆ = _
        rw [lie_add, map_add])
      (by
        intro n x y
        change adaptedHomogeneousClassTwoAction X L evaluation ⁅x, n • y⁆ = _
        rw [lie_smul, map_smul])
  let rhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun a c ↦
        ⁅adaptedHomogeneousClassTwoAction X L evaluation a,
          adaptedHomogeneousClassTwoAction X L evaluation c⁆)
      (by
        intro x₁ x₂ z
        change ⁅adaptedHomogeneousClassTwoAction X L evaluation (x₁ + x₂),
          adaptedHomogeneousClassTwoAction X L evaluation z⁆ = _
        rw [map_add, add_lie])
      (by
        intro n x z
        change ⁅adaptedHomogeneousClassTwoAction X L evaluation (n • x),
          adaptedHomogeneousClassTwoAction X L evaluation z⁆ = _
        rw [map_smul, smul_lie])
      (by
        intro x y₁ y₂
        change ⁅adaptedHomogeneousClassTwoAction X L evaluation x,
          adaptedHomogeneousClassTwoAction X L evaluation (y₁ + y₂)⁆ = _
        rw [map_add, lie_add])
      (by
        intro n x y
        change ⁅adaptedHomogeneousClassTwoAction X L evaluation x,
          adaptedHomogeneousClassTwoAction X L evaluation (n • y)⁆ = _
        rw [map_smul, lie_smul])
  have h : lhs = rhs := by
    apply LinearMap.ext_basis b b
    intro i j
    change adaptedHomogeneousClassTwoAction X L evaluation ⁅b i, b j⁆ =
      ⁅adaptedHomogeneousClassTwoAction X L evaluation (b i),
        adaptedHomogeneousClassTwoAction X L evaluation (b j)⁆
    cases i with
    | weightOne i =>
        cases j with
        | weightOne j =>
            rw [adaptedHomogeneousClassTwoAction_bracket,
              adaptedHomogeneousClassTwoAction_weightOne_commutator]
        | weightTwo j =>
            rw [adaptedHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (collectedHomogeneousBasis X L evaluation 2 j : F) =
                finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 j) by
              simp [finiteLowExactToClassTwo]]
            rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                (0, collectedHomogeneousBasis X L evaluation 2 j)⁆ = 0 by
              rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j)⁆ =
                  -⁅finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j), b (.weightOne i)⁆ by
                exact (lie_skew (b (.weightOne i))
                  (finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j) : M)).symm]
              rw [finiteLowExact_weightTwo_lie, neg_zero], map_zero]
            apply LinearMap.ext
            intro p
            rw [LinearMap.zero_apply]
            change 0 =
              adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne i))
                  (adaptedHomogeneousClassTwoAction X L evaluation
                    (finiteLowExactToClassTwo X
                      (0, collectedHomogeneousBasis X L evaluation 2 j)) p) -
                adaptedHomogeneousClassTwoAction X L evaluation
                    (finiteLowExactToClassTwo X
                      (0, collectedHomogeneousBasis X L evaluation 2 j))
                  (adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne i)) p)
            rw [adaptedHomogeneousClassTwoAction_exactTwo,
              adaptedHomogeneousClassTwoAction_weightOne_apply,
              adaptedHomogeneousClassTwoAction_weightOne_apply]
            change 0 = MvPolynomial.X (.weightOne i) *
                (adaptedHomogeneousClassTwoPolynomial X L evaluation
                  (finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j)) * p) +
                adaptedCorrectionDerivation X L evaluation i
                  (adaptedHomogeneousClassTwoPolynomial X L evaluation
                    (finiteLowExactToClassTwo X
                      (0, collectedHomogeneousBasis X L evaluation 2 j)) * p) -
              adaptedHomogeneousClassTwoPolynomial X L evaluation
                  (finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 j)) *
                (MvPolynomial.X (.weightOne i) * p +
                  adaptedCorrectionDerivation X L evaluation i p)
            rw [Derivation.leibniz,
              adaptedCorrectionDerivation_exactTwo]
            simp only [Algebra.smul_def, Algebra.algebraMap_self_apply,
              zero_mul]
            ring
    | weightTwo i =>
        cases j with
        | weightOne j =>
            rw [adaptedHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (collectedHomogeneousBasis X L evaluation 2 i : F) =
                finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 i) by
              simp [finiteLowExactToClassTwo]]
            rw [finiteLowExact_weightTwo_lie, map_zero]
            apply LinearMap.ext
            intro p
            rw [LinearMap.zero_apply]
            change 0 =
              adaptedHomogeneousClassTwoAction X L evaluation
                  (finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 i))
                  (adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne j)) p) -
                adaptedHomogeneousClassTwoAction X L evaluation (b (.weightOne j))
                  (adaptedHomogeneousClassTwoAction X L evaluation
                    (finiteLowExactToClassTwo X
                      (0, collectedHomogeneousBasis X L evaluation 2 i)) p)
            rw [adaptedHomogeneousClassTwoAction_exactTwo,
              adaptedHomogeneousClassTwoAction_weightOne_apply,
              adaptedHomogeneousClassTwoAction_weightOne_apply]
            change 0 =
              adaptedHomogeneousClassTwoPolynomial X L evaluation
                  (finiteLowExactToClassTwo X
                    (0, collectedHomogeneousBasis X L evaluation 2 i)) *
                (MvPolynomial.X (.weightOne j) * p +
                  adaptedCorrectionDerivation X L evaluation j p) -
              (MvPolynomial.X (.weightOne j) *
                  (adaptedHomogeneousClassTwoPolynomial X L evaluation
                    (finiteLowExactToClassTwo X
                      (0, collectedHomogeneousBasis X L evaluation 2 i)) * p) +
                adaptedCorrectionDerivation X L evaluation j
                  (adaptedHomogeneousClassTwoPolynomial X L evaluation
                    (finiteLowExactToClassTwo X
                      (0, collectedHomogeneousBasis X L evaluation 2 i)) * p))
            rw [Derivation.leibniz,
              adaptedCorrectionDerivation_exactTwo]
            simp only [Algebra.smul_def, Algebra.algebraMap_self_apply,
              zero_mul]
            ring
        | weightTwo j =>
            rw [adaptedHomogeneousClassTwoBasis_weightTwo,
              adaptedHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (collectedHomogeneousBasis X L evaluation 2 i : F) =
                finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 i) by
              simp [finiteLowExactToClassTwo],
              show freeClassTwoTruncation X (collectedHomogeneousBasis X L evaluation 2 j : F) =
                finiteLowExactToClassTwo X (0, collectedHomogeneousBasis X L evaluation 2 j) by
              simp [finiteLowExactToClassTwo]]
            rw [finiteLowExact_weightTwo_lie, map_zero]
            apply LinearMap.ext
            intro p
            rw [LinearMap.zero_apply]
            rw [adaptedHomogeneousClassTwoAction_exactTwo,
              adaptedHomogeneousClassTwoAction_exactTwo]
            change 0 = _ * (_ * p) - _ * (_ * p)
            ring
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- The collector's homogeneous class-two Lie representation. -/
def adaptedHomogeneousClassTwoLieHom :
    LieHom ℤ M (Module.End ℤ Poly) where
  __ := adaptedHomogeneousClassTwoAction X L evaluation
  map_lie' {x y} := adaptedHomogeneousClassTwoAction_map_lie X L evaluation x y

@[simp]
theorem adaptedHomogeneousClassTwoLieHom_apply (x : M) :
    adaptedHomogeneousClassTwoLieHom X L evaluation x =
      adaptedHomogeneousClassTwoAction X L evaluation x := rfl

/-- The commutative variable word of a basis-index list. -/
def adaptedClassTwoVariableWord (is : List I) : Poly :=
  (is.map MvPolynomial.X).prod

@[simp]
theorem adaptedClassTwoVariableWord_nil :
    adaptedClassTwoVariableWord X [] = 1 := rfl

@[simp]
theorem adaptedClassTwoVariableWord_cons (i : I) (is : List I) :
    adaptedClassTwoVariableWord X (i :: is) =
      MvPolynomial.X i * adaptedClassTwoVariableWord X is := by
  simp [adaptedClassTwoVariableWord]

theorem adaptedClassTwo_toFinsupp_cons (i : I) (is : List I) :
    Multiset.toFinsupp ((i :: is : List I) : Multiset I) =
      Finsupp.single i 1 + Multiset.toFinsupp (is : Multiset I) := by
  rw [show ((i :: is : List I) : Multiset I) =
      {i} + (is : Multiset I) by rfl,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

theorem adaptedClassTwoVariableWord_eq_monomial (is : List I) :
    adaptedClassTwoVariableWord X is =
      MvPolynomial.monomial (Multiset.toFinsupp (is : Multiset I)) 1 := by
  induction is with
  | nil => simp [adaptedClassTwoVariableWord]
  | cons i is ih =>
      rw [adaptedClassTwoVariableWord_cons, ih,
        adaptedClassTwo_toFinsupp_cons]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul]

/-- A correction vanishes on every variable not preceding its source index. -/
theorem adaptedCorrectionDerivation_X_eq_zero_of_le
    (i : FreeLieExactBasisIndex X 1) (k : I)
    (hik : (FiniteClassTwoBasisIndex.weightOne i : I) ≤ k) :
    adaptedCorrectionDerivation X L evaluation i (MvPolynomial.X k) = 0 := by
  cases k with
  | weightOne j =>
      rw [adaptedCorrectionDerivation_X_weightOne]
      simp [not_lt_of_ge hik]
  | weightTwo j =>
      exact adaptedCorrectionDerivation_X_weightTwo X L evaluation i j

/-- A correction kills an ordered suffix starting no earlier than its source. -/
theorem adaptedCorrectionDerivation_variableWord_eq_zero
    (i : FreeLieExactBasisIndex X 1) (is : List I)
    (hi : ∀ k ∈ is, (FiniteClassTwoBasisIndex.weightOne i : I) ≤ k) :
    adaptedCorrectionDerivation X L evaluation i (adaptedClassTwoVariableWord X is) = 0 := by
  induction is with
  | nil => simp [adaptedClassTwoVariableWord]
  | cons k is ih =>
      rw [adaptedClassTwoVariableWord_cons, Derivation.leibniz,
        adaptedCorrectionDerivation_X_eq_zero_of_le X L evaluation i k (hi k (by simp)),
        ih (fun j hj ↦ hi j (by simp [hj]))]
      simp

/-- A basis operator prepends its variable to an ordered suffix. -/
theorem adaptedHomogeneousClassTwoAction_basis_variableWord
    (i : I) (is : List I) (hi : ∀ j ∈ is, i ≤ j) :
    adaptedHomogeneousClassTwoAction X L evaluation (b i)
        (adaptedClassTwoVariableWord X is) =
      adaptedClassTwoVariableWord X (i :: is) := by
  cases i with
  | weightOne i =>
      rw [adaptedHomogeneousClassTwoAction_weightOne_apply,
        adaptedCorrectionDerivation_variableWord_eq_zero X L evaluation i is hi,
        add_zero, adaptedClassTwoVariableWord_cons]
  | weightTwo i =>
      rw [adaptedHomogeneousClassTwoAction_weightTwo_apply,
        adaptedClassTwoVariableWord_cons]

/-- Product of the homogeneous basis operators. -/
def adaptedHomogeneousBasisWordAction (is : List I) :
    Module.End ℤ Poly :=
  (is.map fun i ↦ adaptedHomogeneousClassTwoLieHom X L evaluation (b i)).prod

@[simp]
theorem adaptedHomogeneousBasisWordAction_nil :
    adaptedHomogeneousBasisWordAction X L evaluation [] = 1 := rfl

@[simp]
theorem adaptedHomogeneousBasisWordAction_cons (i : I) (is : List I) :
    adaptedHomogeneousBasisWordAction X L evaluation (i :: is) =
      adaptedHomogeneousClassTwoLieHom X L evaluation (b i) *
        adaptedHomogeneousBasisWordAction X L evaluation is := by
  simp [adaptedHomogeneousBasisWordAction]

/-- An ordered basis word sends the vacuum to its commutative variable word. -/
theorem adaptedHomogeneousBasisWordAction_apply_one
    (is : List I) (his : is.Pairwise (· ≤ ·)) :
    adaptedHomogeneousBasisWordAction X L evaluation is 1 =
      adaptedClassTwoVariableWord X is := by
  induction is with
  | nil => simp [adaptedHomogeneousBasisWordAction,
      adaptedClassTwoVariableWord]
  | cons i is ih =>
      have hcons := List.pairwise_cons.mp his
      rw [adaptedHomogeneousBasisWordAction_cons, Module.End.mul_apply,
        ih hcons.2]
      change adaptedHomogeneousClassTwoAction X L evaluation (b i)
          (adaptedClassTwoVariableWord X is) = _
      exact adaptedHomogeneousClassTwoAction_basis_variableWord X L evaluation i is hcons.1

def adaptedHomogeneousClassTwoSortedWord (e : I →₀ ℕ) : List I := by
  classical
  exact (Finsupp.toMultiset e).sort (· ≤ ·)

theorem adaptedHomogeneousBasisWordAction_sortedExponent_apply_one
    (e : I →₀ ℕ) :
    adaptedHomogeneousBasisWordAction X L evaluation
        (adaptedHomogeneousClassTwoSortedWord X e) 1 =
      MvPolynomial.monomial e 1 := by
  classical
  unfold adaptedHomogeneousClassTwoSortedWord
  rw [adaptedHomogeneousBasisWordAction_apply_one X L evaluation _
      (Multiset.pairwise_sort _ _),
    adaptedClassTwoVariableWord_eq_monomial]
  congr 2
  rw [Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

/-- The triangular representation matching the placed collector's homogeneous basis. -/
def adaptedHomogeneousClassTwoTriangularRepresentation :
    LieRings.PBW.TriangularRepresentation ℤ M I b where
  toLieHom := adaptedHomogeneousClassTwoLieHom X L evaluation
  orderedMonomial_apply_one e := by
    classical
    unfold LieRings.PBW.orderedMonomial
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    have h := adaptedHomogeneousBasisWordAction_sortedExponent_apply_one X L evaluation e
    unfold adaptedHomogeneousClassTwoSortedWord
      adaptedHomogeneousBasisWordAction at h
    exact h

/-- PBW for the homogeneous basis as an explicit linear equivalence. -/
def adaptedHomogeneousClassTwoPBWLinearEquiv :
    Poly ≃ₗ[ℤ] UEA ℤ M :=
  (adaptedHomogeneousClassTwoTriangularRepresentation X L evaluation).orderedPBWLinearEquiv

end

end DegreeFive

end LieRings
