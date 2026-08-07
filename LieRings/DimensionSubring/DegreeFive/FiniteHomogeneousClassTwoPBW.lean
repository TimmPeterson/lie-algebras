import LieRings.DimensionSubring.DegreeFive.FiniteClassTwoBasis
import LieRings.PBW.TriangularRepresentation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie

/-!
# PBW in the homogeneous basis used by the finite collector

This is the elementary triangular representation for the two-step quotient, but with the
independently chosen exact weight-one and weight-two bases used by the placed collector.  The
weight-two entries are central, and the correction attached to a weight-one entry only changes
earlier weight-one variables into the coordinate polynomial of their bracket.
-/

namespace LieRings

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [Finite X]

local notation "F" => FreeLieAlgebra ℤ X
local notation "P" => GeneratorModule X
local notation "M" => FreeClassTwo P
local notation "I" => FiniteClassTwoBasisIndex X
local notation "b" => finiteHomogeneousClassTwoBasis X
local notation "Poly" => MvPolynomial I ℤ

/-- Polynomial coordinates in the collector's homogeneous class-two basis. -/
def finiteHomogeneousClassTwoPolynomial : M →ₗ[ℤ] Poly :=
  LieRings.PBW.basisPolynomial ℤ M I b

@[simp]
theorem finiteHomogeneousClassTwoPolynomial_basis (i : I) :
    finiteHomogeneousClassTwoPolynomial X (b i) = MvPolynomial.X i :=
  LieRings.PBW.basisPolynomial_basis ℤ M I b i

/-- Multiplication by a polynomial. -/
def finitePolynomialMul (p : Poly) : Module.End ℤ Poly :=
  LinearMap.mulLeft ℤ p

@[simp]
theorem finitePolynomialMul_apply (p q : Poly) :
    finitePolynomialMul X p q = p * q := rfl

/-- The triangular correction on variables for a weight-one basis element. -/
def finiteCorrectionValue (i : FreeLieExactBasisIndex X 1) : I → Poly
  | .weightOne j =>
      if (FiniteClassTwoBasisIndex.weightOne j : I) < .weightOne i then
        finiteHomogeneousClassTwoPolynomial X
          ⁅b (.weightOne i), b (.weightOne j)⁆
      else 0
  | .weightTwo _ => 0

/-- The polynomial derivation determined by `finiteCorrectionValue`. -/
def finiteCorrectionDerivation
    (i : FreeLieExactBasisIndex X 1) : Derivation ℤ Poly Poly := by
  have hmodule : (inferInstance : Module ℤ Poly) =
      AddCommGroup.toIntModule Poly := Subsingleton.elim _ _
  cases hmodule
  let hTower : IsScalarTower ℤ Poly Poly :=
    ⟨fun n p q ↦ (AddMonoidHom.mulRight q).map_zsmul p n⟩
  exact @MvPolynomial.mkDerivation I ℤ Poly inferInstance inferInstance
    inferInstance inferInstance hTower (finiteCorrectionValue X i)

@[simp]
theorem finiteCorrectionDerivation_X_weightOne
    (i j : FreeLieExactBasisIndex X 1) :
    finiteCorrectionDerivation X i
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j : I)) =
      if (FiniteClassTwoBasisIndex.weightOne j : I) < .weightOne i then
        finiteHomogeneousClassTwoPolynomial X
          ⁅b (.weightOne i), b (.weightOne j)⁆
      else 0 := by
  simp [finiteCorrectionDerivation, finiteCorrectionValue]

@[simp]
theorem finiteCorrectionDerivation_X_weightTwo
    (i : FreeLieExactBasisIndex X 1)
    (j : FreeLieExactBasisIndex X 2) :
    finiteCorrectionDerivation X i
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightTwo j : I)) = 0 := by
  simp [finiteCorrectionDerivation, finiteCorrectionValue]

def finiteCorrectionEnd
    (i : FreeLieExactBasisIndex X 1) : Module.End ℤ Poly where
  toFun := finiteCorrectionDerivation X i
  map_add' p q := map_add (finiteCorrectionDerivation X i) p q
  map_smul' n p := map_zsmul (finiteCorrectionDerivation X i) n p

@[simp]
theorem finiteCorrectionEnd_apply
    (i : FreeLieExactBasisIndex X 1) (p : Poly) :
    finiteCorrectionEnd X i p = finiteCorrectionDerivation X i p := rfl

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
def finiteHomogeneousBasisBracketExactTwo
    (i j : FreeLieExactBasisIndex X 1) : freeLieExact X 2 :=
  ⟨⁅((freeLieExactBasis X 1 i : freeLieExact X 1) : F),
      ((freeLieExactBasis X 1 j : freeLieExact X 1) : F)⁆,
    freeLieExact_bracket_mem X (freeLieExactBasis X 1 i)
      (freeLieExactBasis X 1 j)⟩

theorem finiteHomogeneousClassTwoBasis_bracket_weightOne
    (i j : FreeLieExactBasisIndex X 1) :
    ⁅b (.weightOne i), b (.weightOne j)⁆ =
      finiteLowExactToClassTwo X
        (0, finiteHomogeneousBasisBracketExactTwo X i j) := by
  rw [finiteHomogeneousClassTwoBasis_weightOne,
    finiteHomogeneousClassTwoBasis_weightOne, ← LieHom.map_lie]
  simp [finiteLowExactToClassTwo,
    finiteHomogeneousBasisBracketExactTwo]

/-- Every correction derivation kills the coordinate polynomial of an exact weight-two
element. -/
theorem finiteCorrectionDerivation_exactTwo
    (i : FreeLieExactBasisIndex X 1) (x : freeLieExact X 2) :
    finiteCorrectionDerivation X i
      (finiteHomogeneousClassTwoPolynomial X
        (finiteLowExactToClassTwo X (0, x))) = 0 := by
  let f : freeLieExact X 2 →ₗ[ℤ] Poly :=
    (finiteCorrectionEnd X i).comp
      ((finiteHomogeneousClassTwoPolynomial X).comp
        ((finiteLowExactToClassTwo X).comp (LinearMap.inr ℤ _ _)))
  have hf : f = 0 := by
    apply (freeLieExactBasis X 2).ext
    intro j
    change finiteCorrectionDerivation X i
      (finiteHomogeneousClassTwoPolynomial X
        (finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 j))) = 0
    rw [show finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 j) =
        b (.weightTwo j) by
      rw [finiteHomogeneousClassTwoBasis_weightTwo]
      simp [finiteLowExactToClassTwo]]
    rw [finiteHomogeneousClassTwoPolynomial_basis,
      finiteCorrectionDerivation_X_weightTwo]
  exact LinearMap.congr_fun hf x

@[simp]
theorem finiteCorrectionDerivation_bracket
    (i : FreeLieExactBasisIndex X 1) (x y : M) :
    finiteCorrectionDerivation X i
      (finiteHomogeneousClassTwoPolynomial X ⁅x, y⁆) = 0 := by
  let q : M →ₗ[ℤ] M →ₗ[ℤ] Poly :=
    LinearMap.mk₂ ℤ (fun x y ↦ finiteCorrectionDerivation X i
        (finiteHomogeneousClassTwoPolynomial X ⁅x, y⁆))
      (by
        intro x₁ x₂ z
        change finiteCorrectionDerivation X i
          (finiteHomogeneousClassTwoPolynomial X ⁅x₁ + x₂, z⁆) = _
        rw [add_lie, map_add, map_add])
      (by
        intro n x₁ z
        change finiteCorrectionDerivation X i
          (finiteHomogeneousClassTwoPolynomial X ⁅n • x₁, z⁆) = _
        rw [smul_lie, map_smul, map_zsmul])
      (by
        intro x₁ y₁ y₂
        change finiteCorrectionDerivation X i
          (finiteHomogeneousClassTwoPolynomial X ⁅x₁, y₁ + y₂⁆) = _
        rw [lie_add, map_add, map_add])
      (by
        intro n x₁ y₁
        change finiteCorrectionDerivation X i
          (finiteHomogeneousClassTwoPolynomial X ⁅x₁, n • y₁⁆) = _
        rw [lie_smul, map_smul, map_zsmul])
  have hq : q = 0 := by
    apply LinearMap.ext_basis b b
    intro j k
    change finiteCorrectionDerivation X i
      (finiteHomogeneousClassTwoPolynomial X ⁅b j, b k⁆) = 0
    cases j with
    | weightOne j =>
        cases k with
        | weightOne k =>
            rw [finiteHomogeneousClassTwoBasis_bracket_weightOne]
            exact finiteCorrectionDerivation_exactTwo X i
              (finiteHomogeneousBasisBracketExactTwo X j k)
        | weightTwo k =>
            rw [finiteHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X
                (freeLieExactBasis X 2 k : F) =
                finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 k) by
              simp [finiteLowExactToClassTwo]]
            rw [show ⁅b (.weightOne j),
                finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 k)⁆ =
                -⁅finiteLowExactToClassTwo X
                  (0, freeLieExactBasis X 2 k), b (.weightOne j)⁆ by
              exact (lie_skew
                (b (.weightOne j))
                (finiteLowExactToClassTwo X
                  (0, freeLieExactBasis X 2 k) : M)).symm,
              finiteLowExact_weightTwo_lie X (freeLieExactBasis X 2 k),
              neg_zero, map_zero, Derivation.map_zero]
    | weightTwo j =>
        rw [finiteHomogeneousClassTwoBasis_weightTwo]
        rw [show freeClassTwoTruncation X
            (freeLieExactBasis X 2 j : F) =
            finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 j) by
          simp [finiteLowExactToClassTwo]]
        rw [finiteLowExact_weightTwo_lie X (freeLieExactBasis X 2 j),
          map_zero, Derivation.map_zero]
  exact DFunLike.congr_fun (DFunLike.congr_fun hq x) y

/-- The correction derivations commute. -/
theorem finiteCorrectionDerivation_commute
    (i j : FreeLieExactBasisIndex X 1) (p : Poly) :
    finiteCorrectionDerivation X i (finiteCorrectionDerivation X j p) =
      finiteCorrectionDerivation X j (finiteCorrectionDerivation X i p) := by
  have hX (k : I) :
      finiteCorrectionDerivation X i
          (finiteCorrectionDerivation X j (MvPolynomial.X k)) =
        finiteCorrectionDerivation X j
          (finiteCorrectionDerivation X i (MvPolynomial.X k)) := by
    cases k with
    | weightOne k =>
        simp only [finiteCorrectionDerivation_X_weightOne]
        split_ifs <;> simp only [finiteCorrectionDerivation_bracket,
          Derivation.map_zero]
    | weightTwo k =>
        simp only [finiteCorrectionDerivation_X_weightTwo, Derivation.map_zero]
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
theorem finiteCorrectionDerivation_X_sub
    (i j : FreeLieExactBasisIndex X 1) :
    finiteCorrectionDerivation X i
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne j : I)) -
      finiteCorrectionDerivation X j
        (MvPolynomial.X (FiniteClassTwoBasisIndex.weightOne i : I)) =
      finiteHomogeneousClassTwoPolynomial X
        ⁅b (.weightOne i), b (.weightOne j)⁆ := by
  rcases lt_trichotomy (FiniteClassTwoBasisIndex.weightOne i : I)
      (.weightOne j) with hij | hij | hij
  · have hji : ¬ (FiniteClassTwoBasisIndex.weightOne j : I) < .weightOne i :=
      not_lt_of_ge hij.le
    rw [finiteCorrectionDerivation_X_weightOne,
      finiteCorrectionDerivation_X_weightOne]
    simp only [hij, hji, if_true, if_false, zero_sub]
    rw [← map_neg, lie_skew]
  · have heq : i = j := FiniteClassTwoBasisIndex.weightOne.inj hij
    subst j
    simp
  · have hij' : ¬ (FiniteClassTwoBasisIndex.weightOne i : I) < .weightOne j :=
      not_lt_of_ge hij.le
    rw [finiteCorrectionDerivation_X_weightOne,
      finiteCorrectionDerivation_X_weightOne]
    simp [hij, hij']

/-- Basis operators for the collector's homogeneous class-two basis. -/
def finiteHomogeneousClassTwoActionBasis : I → Module.End ℤ Poly
  | .weightOne i =>
      finitePolynomialMul X (MvPolynomial.X (.weightOne i)) +
        finiteCorrectionEnd X i
  | .weightTwo i =>
      finitePolynomialMul X (MvPolynomial.X (.weightTwo i))

/-- Extend the basis operators linearly. -/
def finiteHomogeneousClassTwoAction : M →ₗ[ℤ] Module.End ℤ Poly :=
  (Finsupp.linearCombination ℤ (finiteHomogeneousClassTwoActionBasis X)).comp
    (finiteHomogeneousClassTwoBasis X).repr.toLinearMap

@[simp]
theorem finiteHomogeneousClassTwoAction_basis (i : I) :
    finiteHomogeneousClassTwoAction X (b i) =
      finiteHomogeneousClassTwoActionBasis X i := by
  simp [finiteHomogeneousClassTwoAction]

@[simp]
theorem finiteHomogeneousClassTwoAction_weightOne_apply
    (i : FreeLieExactBasisIndex X 1) (p : Poly) :
    finiteHomogeneousClassTwoAction X (b (.weightOne i)) p =
      MvPolynomial.X (.weightOne i) * p +
        finiteCorrectionDerivation X i p := by
  rw [finiteHomogeneousClassTwoAction_basis]
  rfl

@[simp]
theorem finiteHomogeneousClassTwoAction_weightTwo_apply
    (i : FreeLieExactBasisIndex X 2) (p : Poly) :
    finiteHomogeneousClassTwoAction X (b (.weightTwo i)) p =
      MvPolynomial.X (.weightTwo i) * p := by
  rw [finiteHomogeneousClassTwoAction_basis]
  rfl

/-- Multiplication depends linearly on the polynomial. -/
def finitePolynomialMulLinear : Poly →ₗ[ℤ] Module.End ℤ Poly where
  toFun := finitePolynomialMul X
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
theorem finiteHomogeneousClassTwoAction_exactTwo (x : freeLieExact X 2) :
    finiteHomogeneousClassTwoAction X
        (finiteLowExactToClassTwo X (0, x)) =
      finitePolynomialMul X
        (finiteHomogeneousClassTwoPolynomial X
          (finiteLowExactToClassTwo X (0, x))) := by
  let lhs : freeLieExact X 2 →ₗ[ℤ] Module.End ℤ Poly :=
    (finiteHomogeneousClassTwoAction X).comp
      ((finiteLowExactToClassTwo X).comp (LinearMap.inr ℤ _ _))
  let rhs : freeLieExact X 2 →ₗ[ℤ] Module.End ℤ Poly :=
    (finitePolynomialMulLinear X).comp
      ((finiteHomogeneousClassTwoPolynomial X).comp
        ((finiteLowExactToClassTwo X).comp (LinearMap.inr ℤ _ _)))
  have h : lhs = rhs := by
    apply (freeLieExactBasis X 2).ext
    intro i
    change finiteHomogeneousClassTwoAction X
        (finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 i)) =
      finitePolynomialMul X (finiteHomogeneousClassTwoPolynomial X
        (finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 i)))
    rw [show finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 i) =
        b (.weightTwo i) by
      rw [finiteHomogeneousClassTwoBasis_weightTwo]
      simp [finiteLowExactToClassTwo]]
    rw [finiteHomogeneousClassTwoAction_basis,
      finiteHomogeneousClassTwoPolynomial_basis]
    rfl
  exact LinearMap.congr_fun h x

@[simp]
theorem finiteHomogeneousClassTwoAction_bracket (x y : M) :
    finiteHomogeneousClassTwoAction X ⁅x, y⁆ =
      finitePolynomialMul X
        (finiteHomogeneousClassTwoPolynomial X ⁅x, y⁆) := by
  let lhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun x y ↦ finiteHomogeneousClassTwoAction X ⁅x, y⁆)
      (by
        intro x₁ x₂ z
        change finiteHomogeneousClassTwoAction X ⁅x₁ + x₂, z⁆ = _
        rw [add_lie, map_add])
      (by
        intro n x z
        change finiteHomogeneousClassTwoAction X ⁅n • x, z⁆ = _
        rw [smul_lie, map_smul])
      (by
        intro x y₁ y₂
        change finiteHomogeneousClassTwoAction X ⁅x, y₁ + y₂⁆ = _
        rw [lie_add, map_add])
      (by
        intro n x y
        change finiteHomogeneousClassTwoAction X ⁅x, n • y⁆ = _
        rw [lie_smul, map_smul])
  let rhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun x y ↦ finitePolynomialMul X
        (finiteHomogeneousClassTwoPolynomial X ⁅x, y⁆))
      (by
        intro x₁ x₂ z
        change finitePolynomialMul X
          (finiteHomogeneousClassTwoPolynomial X ⁅x₁ + x₂, z⁆) = _
        rw [add_lie, map_add]
        exact (finitePolynomialMulLinear X).map_add _ _)
      (by
        intro n x z
        change finitePolynomialMul X
          (finiteHomogeneousClassTwoPolynomial X ⁅n • x, z⁆) = _
        rw [smul_lie, map_smul]
        exact (finitePolynomialMulLinear X).map_smul n _)
      (by
        intro x y₁ y₂
        change finitePolynomialMul X
          (finiteHomogeneousClassTwoPolynomial X ⁅x, y₁ + y₂⁆) = _
        rw [lie_add, map_add]
        exact (finitePolynomialMulLinear X).map_add _ _)
      (by
        intro n x y
        change finitePolynomialMul X
          (finiteHomogeneousClassTwoPolynomial X ⁅x, n • y⁆) = _
        rw [lie_smul, map_smul]
        exact (finitePolynomialMulLinear X).map_smul n _)
  have h : lhs = rhs := by
    apply LinearMap.ext_basis b b
    intro i j
    change finiteHomogeneousClassTwoAction X ⁅b i, b j⁆ =
      finitePolynomialMul X
        (finiteHomogeneousClassTwoPolynomial X ⁅b i, b j⁆)
    cases i with
    | weightOne i =>
        cases j with
        | weightOne j =>
            rw [finiteHomogeneousClassTwoBasis_bracket_weightOne,
              finiteHomogeneousClassTwoAction_exactTwo]
        | weightTwo j =>
            rw [finiteHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (freeLieExactBasis X 2 j : F) =
                finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 j) by
              simp [finiteLowExactToClassTwo]]
            rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                (0, freeLieExactBasis X 2 j)⁆ = 0 by
              rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j)⁆ =
                  -⁅finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j), b (.weightOne i)⁆ by
                exact (lie_skew (b (.weightOne i))
                  (finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j) : M)).symm]
              rw [finiteLowExact_weightTwo_lie, neg_zero], map_zero, map_zero]
            apply LinearMap.ext
            intro p
            simp [finitePolynomialMul]
    | weightTwo i =>
        rw [finiteHomogeneousClassTwoBasis_weightTwo]
        rw [show freeClassTwoTruncation X (freeLieExactBasis X 2 i : F) =
            finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 i) by
          simp [finiteLowExactToClassTwo]]
        rw [finiteLowExact_weightTwo_lie, map_zero, map_zero]
        apply LinearMap.ext
        intro p
        simp [finitePolynomialMul]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- The commutator of two weight-one basis operators is multiplication by the bracket. -/
theorem finiteHomogeneousClassTwoAction_weightOne_commutator
    (i j : FreeLieExactBasisIndex X 1) :
    ⁅finiteHomogeneousClassTwoAction X (b (.weightOne i)),
      finiteHomogeneousClassTwoAction X (b (.weightOne j))⁆ =
      finitePolynomialMul X
        (finiteHomogeneousClassTwoPolynomial X
          ⁅b (.weightOne i), b (.weightOne j)⁆) := by
  apply LinearMap.ext
  intro p
  change finiteHomogeneousClassTwoAction X (b (.weightOne i))
      (finiteHomogeneousClassTwoAction X (b (.weightOne j)) p) -
    finiteHomogeneousClassTwoAction X (b (.weightOne j))
      (finiteHomogeneousClassTwoAction X (b (.weightOne i)) p) = _
  rw [finiteHomogeneousClassTwoAction_weightOne_apply,
    finiteHomogeneousClassTwoAction_weightOne_apply,
    finiteHomogeneousClassTwoAction_weightOne_apply,
    finiteHomogeneousClassTwoAction_weightOne_apply]
  rw [map_add, map_add, Derivation.leibniz, Derivation.leibniz,
    finiteCorrectionDerivation_commute X i j p]
  rw [← finiteCorrectionDerivation_X_sub X i j]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  simp [finitePolynomialMul]
  split_ifs <;> ring

/-- The explicit homogeneous action respects the Lie bracket. -/
theorem finiteHomogeneousClassTwoAction_map_lie (x y : M) :
    finiteHomogeneousClassTwoAction X ⁅x, y⁆ =
      ⁅finiteHomogeneousClassTwoAction X x,
        finiteHomogeneousClassTwoAction X y⁆ := by
  let lhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun a c ↦ finiteHomogeneousClassTwoAction X ⁅a, c⁆)
      (by
        intro x₁ x₂ z
        change finiteHomogeneousClassTwoAction X ⁅x₁ + x₂, z⁆ = _
        rw [add_lie, map_add])
      (by
        intro n x z
        change finiteHomogeneousClassTwoAction X ⁅n • x, z⁆ = _
        rw [smul_lie, map_smul])
      (by
        intro x y₁ y₂
        change finiteHomogeneousClassTwoAction X ⁅x, y₁ + y₂⁆ = _
        rw [lie_add, map_add])
      (by
        intro n x y
        change finiteHomogeneousClassTwoAction X ⁅x, n • y⁆ = _
        rw [lie_smul, map_smul])
  let rhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun a c ↦
        ⁅finiteHomogeneousClassTwoAction X a,
          finiteHomogeneousClassTwoAction X c⁆)
      (by
        intro x₁ x₂ z
        change ⁅finiteHomogeneousClassTwoAction X (x₁ + x₂),
          finiteHomogeneousClassTwoAction X z⁆ = _
        rw [map_add, add_lie])
      (by
        intro n x z
        change ⁅finiteHomogeneousClassTwoAction X (n • x),
          finiteHomogeneousClassTwoAction X z⁆ = _
        rw [map_smul, smul_lie])
      (by
        intro x y₁ y₂
        change ⁅finiteHomogeneousClassTwoAction X x,
          finiteHomogeneousClassTwoAction X (y₁ + y₂)⁆ = _
        rw [map_add, lie_add])
      (by
        intro n x y
        change ⁅finiteHomogeneousClassTwoAction X x,
          finiteHomogeneousClassTwoAction X (n • y)⁆ = _
        rw [map_smul, lie_smul])
  have h : lhs = rhs := by
    apply LinearMap.ext_basis b b
    intro i j
    change finiteHomogeneousClassTwoAction X ⁅b i, b j⁆ =
      ⁅finiteHomogeneousClassTwoAction X (b i),
        finiteHomogeneousClassTwoAction X (b j)⁆
    cases i with
    | weightOne i =>
        cases j with
        | weightOne j =>
            rw [finiteHomogeneousClassTwoAction_bracket,
              finiteHomogeneousClassTwoAction_weightOne_commutator]
        | weightTwo j =>
            rw [finiteHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (freeLieExactBasis X 2 j : F) =
                finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 j) by
              simp [finiteLowExactToClassTwo]]
            rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                (0, freeLieExactBasis X 2 j)⁆ = 0 by
              rw [show ⁅b (.weightOne i), finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j)⁆ =
                  -⁅finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j), b (.weightOne i)⁆ by
                exact (lie_skew (b (.weightOne i))
                  (finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j) : M)).symm]
              rw [finiteLowExact_weightTwo_lie, neg_zero], map_zero]
            apply LinearMap.ext
            intro p
            rw [LinearMap.zero_apply]
            change 0 =
              finiteHomogeneousClassTwoAction X (b (.weightOne i))
                  (finiteHomogeneousClassTwoAction X
                    (finiteLowExactToClassTwo X
                      (0, freeLieExactBasis X 2 j)) p) -
                finiteHomogeneousClassTwoAction X
                    (finiteLowExactToClassTwo X
                      (0, freeLieExactBasis X 2 j))
                  (finiteHomogeneousClassTwoAction X (b (.weightOne i)) p)
            rw [finiteHomogeneousClassTwoAction_exactTwo,
              finiteHomogeneousClassTwoAction_weightOne_apply,
              finiteHomogeneousClassTwoAction_weightOne_apply]
            change 0 = MvPolynomial.X (.weightOne i) *
                (finiteHomogeneousClassTwoPolynomial X
                  (finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j)) * p) +
                finiteCorrectionDerivation X i
                  (finiteHomogeneousClassTwoPolynomial X
                    (finiteLowExactToClassTwo X
                      (0, freeLieExactBasis X 2 j)) * p) -
              finiteHomogeneousClassTwoPolynomial X
                  (finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 j)) *
                (MvPolynomial.X (.weightOne i) * p +
                  finiteCorrectionDerivation X i p)
            rw [Derivation.leibniz,
              finiteCorrectionDerivation_exactTwo]
            simp only [Algebra.smul_def, Algebra.algebraMap_self_apply,
              zero_mul]
            ring
    | weightTwo i =>
        cases j with
        | weightOne j =>
            rw [finiteHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (freeLieExactBasis X 2 i : F) =
                finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 i) by
              simp [finiteLowExactToClassTwo]]
            rw [finiteLowExact_weightTwo_lie, map_zero]
            apply LinearMap.ext
            intro p
            rw [LinearMap.zero_apply]
            change 0 =
              finiteHomogeneousClassTwoAction X
                  (finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 i))
                  (finiteHomogeneousClassTwoAction X (b (.weightOne j)) p) -
                finiteHomogeneousClassTwoAction X (b (.weightOne j))
                  (finiteHomogeneousClassTwoAction X
                    (finiteLowExactToClassTwo X
                      (0, freeLieExactBasis X 2 i)) p)
            rw [finiteHomogeneousClassTwoAction_exactTwo,
              finiteHomogeneousClassTwoAction_weightOne_apply,
              finiteHomogeneousClassTwoAction_weightOne_apply]
            change 0 =
              finiteHomogeneousClassTwoPolynomial X
                  (finiteLowExactToClassTwo X
                    (0, freeLieExactBasis X 2 i)) *
                (MvPolynomial.X (.weightOne j) * p +
                  finiteCorrectionDerivation X j p) -
              (MvPolynomial.X (.weightOne j) *
                  (finiteHomogeneousClassTwoPolynomial X
                    (finiteLowExactToClassTwo X
                      (0, freeLieExactBasis X 2 i)) * p) +
                finiteCorrectionDerivation X j
                  (finiteHomogeneousClassTwoPolynomial X
                    (finiteLowExactToClassTwo X
                      (0, freeLieExactBasis X 2 i)) * p))
            rw [Derivation.leibniz,
              finiteCorrectionDerivation_exactTwo]
            simp only [Algebra.smul_def, Algebra.algebraMap_self_apply,
              zero_mul]
            ring
        | weightTwo j =>
            rw [finiteHomogeneousClassTwoBasis_weightTwo,
              finiteHomogeneousClassTwoBasis_weightTwo]
            rw [show freeClassTwoTruncation X (freeLieExactBasis X 2 i : F) =
                finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 i) by
              simp [finiteLowExactToClassTwo],
              show freeClassTwoTruncation X (freeLieExactBasis X 2 j : F) =
                finiteLowExactToClassTwo X (0, freeLieExactBasis X 2 j) by
              simp [finiteLowExactToClassTwo]]
            rw [finiteLowExact_weightTwo_lie, map_zero]
            apply LinearMap.ext
            intro p
            rw [LinearMap.zero_apply]
            rw [finiteHomogeneousClassTwoAction_exactTwo,
              finiteHomogeneousClassTwoAction_exactTwo]
            change 0 = _ * (_ * p) - _ * (_ * p)
            ring
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- The collector's homogeneous class-two Lie representation. -/
def finiteHomogeneousClassTwoLieHom :
    LieHom ℤ M (Module.End ℤ Poly) where
  __ := finiteHomogeneousClassTwoAction X
  map_lie' {x y} := finiteHomogeneousClassTwoAction_map_lie X x y

@[simp]
theorem finiteHomogeneousClassTwoLieHom_apply (x : M) :
    finiteHomogeneousClassTwoLieHom X x =
      finiteHomogeneousClassTwoAction X x := rfl

/-- The commutative variable word of a basis-index list. -/
def finiteClassTwoVariableWord (is : List I) : Poly :=
  (is.map MvPolynomial.X).prod

@[simp]
theorem finiteClassTwoVariableWord_nil :
    finiteClassTwoVariableWord X [] = 1 := rfl

@[simp]
theorem finiteClassTwoVariableWord_cons (i : I) (is : List I) :
    finiteClassTwoVariableWord X (i :: is) =
      MvPolynomial.X i * finiteClassTwoVariableWord X is := by
  simp [finiteClassTwoVariableWord]

theorem finiteClassTwo_toFinsupp_cons (i : I) (is : List I) :
    Multiset.toFinsupp ((i :: is : List I) : Multiset I) =
      Finsupp.single i 1 + Multiset.toFinsupp (is : Multiset I) := by
  rw [show ((i :: is : List I) : Multiset I) =
      {i} + (is : Multiset I) by rfl,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

theorem finiteClassTwoVariableWord_eq_monomial (is : List I) :
    finiteClassTwoVariableWord X is =
      MvPolynomial.monomial (Multiset.toFinsupp (is : Multiset I)) 1 := by
  induction is with
  | nil => simp [finiteClassTwoVariableWord]
  | cons i is ih =>
      rw [finiteClassTwoVariableWord_cons, ih,
        finiteClassTwo_toFinsupp_cons]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul]

/-- A correction vanishes on every variable not preceding its source index. -/
theorem finiteCorrectionDerivation_X_eq_zero_of_le
    (i : FreeLieExactBasisIndex X 1) (k : I)
    (hik : (FiniteClassTwoBasisIndex.weightOne i : I) ≤ k) :
    finiteCorrectionDerivation X i (MvPolynomial.X k) = 0 := by
  cases k with
  | weightOne j =>
      rw [finiteCorrectionDerivation_X_weightOne]
      simp [not_lt_of_ge hik]
  | weightTwo j =>
      exact finiteCorrectionDerivation_X_weightTwo X i j

/-- A correction kills an ordered suffix starting no earlier than its source. -/
theorem finiteCorrectionDerivation_variableWord_eq_zero
    (i : FreeLieExactBasisIndex X 1) (is : List I)
    (hi : ∀ k ∈ is, (FiniteClassTwoBasisIndex.weightOne i : I) ≤ k) :
    finiteCorrectionDerivation X i (finiteClassTwoVariableWord X is) = 0 := by
  induction is with
  | nil => simp [finiteClassTwoVariableWord]
  | cons k is ih =>
      rw [finiteClassTwoVariableWord_cons, Derivation.leibniz,
        finiteCorrectionDerivation_X_eq_zero_of_le X i k (hi k (by simp)),
        ih (fun j hj ↦ hi j (by simp [hj]))]
      simp

/-- A basis operator prepends its variable to an ordered suffix. -/
theorem finiteHomogeneousClassTwoAction_basis_variableWord
    (i : I) (is : List I) (hi : ∀ j ∈ is, i ≤ j) :
    finiteHomogeneousClassTwoAction X (b i)
        (finiteClassTwoVariableWord X is) =
      finiteClassTwoVariableWord X (i :: is) := by
  cases i with
  | weightOne i =>
      rw [finiteHomogeneousClassTwoAction_weightOne_apply,
        finiteCorrectionDerivation_variableWord_eq_zero X i is hi,
        add_zero, finiteClassTwoVariableWord_cons]
  | weightTwo i =>
      rw [finiteHomogeneousClassTwoAction_weightTwo_apply,
        finiteClassTwoVariableWord_cons]

/-- Product of the homogeneous basis operators. -/
def finiteHomogeneousBasisWordAction (is : List I) :
    Module.End ℤ Poly :=
  (is.map fun i ↦ finiteHomogeneousClassTwoLieHom X (b i)).prod

@[simp]
theorem finiteHomogeneousBasisWordAction_nil :
    finiteHomogeneousBasisWordAction X [] = 1 := rfl

@[simp]
theorem finiteHomogeneousBasisWordAction_cons (i : I) (is : List I) :
    finiteHomogeneousBasisWordAction X (i :: is) =
      finiteHomogeneousClassTwoLieHom X (b i) *
        finiteHomogeneousBasisWordAction X is := by
  simp [finiteHomogeneousBasisWordAction]

/-- An ordered basis word sends the vacuum to its commutative variable word. -/
theorem finiteHomogeneousBasisWordAction_apply_one
    (is : List I) (his : is.Pairwise (· ≤ ·)) :
    finiteHomogeneousBasisWordAction X is 1 =
      finiteClassTwoVariableWord X is := by
  induction is with
  | nil => simp [finiteHomogeneousBasisWordAction,
      finiteClassTwoVariableWord]
  | cons i is ih =>
      have hcons := List.pairwise_cons.mp his
      rw [finiteHomogeneousBasisWordAction_cons, Module.End.mul_apply,
        ih hcons.2]
      change finiteHomogeneousClassTwoAction X (b i)
          (finiteClassTwoVariableWord X is) = _
      exact finiteHomogeneousClassTwoAction_basis_variableWord X i is hcons.1

def finiteHomogeneousClassTwoSortedWord (e : I →₀ ℕ) : List I := by
  classical
  exact (Finsupp.toMultiset e).sort (· ≤ ·)

theorem finiteHomogeneousBasisWordAction_sortedExponent_apply_one
    (e : I →₀ ℕ) :
    finiteHomogeneousBasisWordAction X
        (finiteHomogeneousClassTwoSortedWord X e) 1 =
      MvPolynomial.monomial e 1 := by
  classical
  unfold finiteHomogeneousClassTwoSortedWord
  rw [finiteHomogeneousBasisWordAction_apply_one X _
      (Multiset.pairwise_sort _ _),
    finiteClassTwoVariableWord_eq_monomial]
  congr 2
  rw [Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

/-- The triangular representation matching the placed collector's homogeneous basis. -/
def finiteHomogeneousClassTwoTriangularRepresentation :
    LieRings.PBW.TriangularRepresentation ℤ M I b where
  toLieHom := finiteHomogeneousClassTwoLieHom X
  orderedMonomial_apply_one e := by
    classical
    unfold LieRings.PBW.orderedMonomial
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    have h := finiteHomogeneousBasisWordAction_sortedExponent_apply_one X e
    unfold finiteHomogeneousClassTwoSortedWord
      finiteHomogeneousBasisWordAction at h
    exact h

/-- PBW for the homogeneous basis as an explicit linear equivalence. -/
def finiteHomogeneousClassTwoPBWLinearEquiv :
    Poly ≃ₗ[ℤ] UEA ℤ M :=
  (finiteHomogeneousClassTwoTriangularRepresentation X).orderedPBWLinearEquiv

end

end DegreeFive

end LieRings
