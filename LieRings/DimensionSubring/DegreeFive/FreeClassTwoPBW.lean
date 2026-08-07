import LieRings.DimensionSubring.DegreeFive.FreeClassTwo
import LieRings.PBW.TriangularRepresentation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Derivation.Lie

/-!
# An explicit PBW representation for the free class-two Lie ring

For the canonical basis of `P ⊕ ⋀²P`, put all generators before the central wedge
generators.  The operator belonging to a noncentral generator `i` is multiplication by `X i`
plus the derivation which sends an earlier generator `j` to the central variable representing
`[i,j]`; central generators act by multiplication.  The correction derivations commute, so
their commutator is exactly multiplication by the class-two bracket.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (X : Type u) [LinearOrder X]

local notation "P" => X →₀ ℤ
local notation "M" => FreeClassTwo P

/-- Indices for the canonical exterior-square basis. -/
abbrev ClassTwoWedgeIndex := Set.powersetCard X 2

/-- A fixed order on the central basis indices.  Its particular choice is immaterial; the sum
order below only needs every degree-one generator to precede every central generator. -/
noncomputable instance classTwoWedgeIndexLinearOrder : LinearOrder (ClassTwoWedgeIndex X) :=
  WellOrderingRel.isWellOrder.linearOrder

/-- Generator indices followed by central wedge indices.  A dedicated type avoids the competing
disjoint and lexicographic order instances carried by the ordinary sum type. -/
inductive ClassTwoBasisIndex (X : Type u)
  | generator (i : X)
  | central (a : ClassTwoWedgeIndex X)

/-- Identification with the sum index used by `Basis.prod`. -/
def classTwoBasisIndexEquiv :
    (X ⊕ ClassTwoWedgeIndex X) ≃ ClassTwoBasisIndex X where
  toFun
    | Sum.inl i => .generator i
    | Sum.inr a => .central a
  invFun
    | .generator i => Sum.inl i
    | .central a => Sum.inr a
  left_inv z := by cases z <;> rfl
  right_inv z := by cases z <;> rfl

/-- Generators retain their given order and precede all central basis vectors. -/
noncomputable instance classTwoBasisIndexLinearOrder : LinearOrder (ClassTwoBasisIndex X) :=
  LinearOrder.lift'
    (fun z ↦ (toLex ((classTwoBasisIndexEquiv X).symm z) :
      X ⊕ₗ ClassTwoWedgeIndex X))
    ((toLex : (X ⊕ ClassTwoWedgeIndex X) ≃
      Lex (X ⊕ ClassTwoWedgeIndex X)).injective.comp
        (classTwoBasisIndexEquiv X).symm.injective)

local notation "I" => ClassTwoBasisIndex X
local notation "Poly" => MvPolynomial I ℤ

/-- The canonical basis of the free generator module. -/
def freeGeneratorBasis : Module.Basis X ℤ P :=
  Finsupp.basisSingleOne

/-- The canonical basis of `P ⊕ ⋀²P`. -/
def freeClassTwoBasis : Module.Basis I ℤ M :=
  ((freeGeneratorBasis X).prod ((freeGeneratorBasis X).exteriorPower 2)).reindex
    (classTwoBasisIndexEquiv X)

@[simp]
theorem freeClassTwoBasis_inl_fst (i : X) :
    (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)).1 = Finsupp.single i 1 := by
  let b := (freeGeneratorBasis X).prod ((freeGeneratorBasis X).exteriorPower 2)
  calc
    (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)).1 =
        (b ((classTwoBasisIndexEquiv X).symm
          (ClassTwoBasisIndex.generator i))).1 :=
      congrArg Prod.fst (b.reindex_apply (classTwoBasisIndexEquiv X) _)
    _ = Finsupp.single i 1 := by
      simp [b, classTwoBasisIndexEquiv, freeGeneratorBasis]

@[simp]
theorem freeClassTwoBasis_inl_snd (i : X) :
    (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)).2 = 0 := by
  let b := (freeGeneratorBasis X).prod ((freeGeneratorBasis X).exteriorPower 2)
  calc
    (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)).2 =
        (b ((classTwoBasisIndexEquiv X).symm
          (ClassTwoBasisIndex.generator i))).2 :=
      congrArg Prod.snd (b.reindex_apply (classTwoBasisIndexEquiv X) _)
    _ = 0 := by simp [b, classTwoBasisIndexEquiv]

@[simp]
theorem freeClassTwoBasis_inr_fst (a : ClassTwoWedgeIndex X) :
    (freeClassTwoBasis X (ClassTwoBasisIndex.central a)).1 = 0 := by
  let b := (freeGeneratorBasis X).prod ((freeGeneratorBasis X).exteriorPower 2)
  calc
    (freeClassTwoBasis X (ClassTwoBasisIndex.central a)).1 =
        (b ((classTwoBasisIndexEquiv X).symm
          (ClassTwoBasisIndex.central a))).1 :=
      congrArg Prod.fst (b.reindex_apply (classTwoBasisIndexEquiv X) _)
    _ = 0 := by simp [b, classTwoBasisIndexEquiv]

@[simp]
theorem freeClassTwoBasis_inr (a : ClassTwoWedgeIndex X) :
    freeClassTwoBasis X (ClassTwoBasisIndex.central a) =
      (0, (freeGeneratorBasis X).exteriorPower 2 a) := by
  let b := (freeGeneratorBasis X).prod ((freeGeneratorBasis X).exteriorPower 2)
  calc
    freeClassTwoBasis X (ClassTwoBasisIndex.central a) =
        b ((classTwoBasisIndexEquiv X).symm (ClassTwoBasisIndex.central a)) :=
      b.reindex_apply (classTwoBasisIndexEquiv X) _
    _ = (0, (freeGeneratorBasis X).exteriorPower 2 a) := by
      simp [b, classTwoBasisIndexEquiv]

/-- Inclusion of the central exterior-square summand. -/
def freeClassTwoCentralInclusion :
    (⋀[ℤ]^2 P) →ₗ[ℤ] M :=
  LinearMap.inr ℤ P (⋀[ℤ]^2 P)

@[simp]
theorem freeClassTwoCentralInclusion_apply (w : ⋀[ℤ]^2 P) :
    freeClassTwoCentralInclusion X w = (0, w) := by
  exact LinearMap.inr_apply w

/-- Polynomial carrying the coordinates of a class-two element. -/
def freeClassTwoPolynomial : M →ₗ[ℤ] Poly :=
  LieRings.PBW.basisPolynomial ℤ M I (freeClassTwoBasis X)

@[simp]
theorem freeClassTwoPolynomial_basis (i : I) :
    freeClassTwoPolynomial X (freeClassTwoBasis X i) = MvPolynomial.X i := by
  exact LieRings.PBW.basisPolynomial_basis ℤ M I (freeClassTwoBasis X) i

/-- Left multiplication by a polynomial, as a linear endomorphism. -/
def polynomialMul (p : Poly) : Module.End ℤ Poly :=
  LinearMap.mulLeft ℤ p

@[simp]
theorem polynomialMul_apply (p q : Poly) : polynomialMul X p q = p * q := rfl

/-- The order-dependent value assigned to a polynomial variable by the correction derivation
for the generator `i`. -/
def correctionValue (i : X) : I → Poly
  | ClassTwoBasisIndex.generator j =>
      if (ClassTwoBasisIndex.generator j : I) <
          ClassTwoBasisIndex.generator i then
        freeClassTwoPolynomial X
          ⁅freeClassTwoBasis X (ClassTwoBasisIndex.generator i),
            freeClassTwoBasis X (ClassTwoBasisIndex.generator j)⁆
      else 0
  | ClassTwoBasisIndex.central _ => 0

/-- The correction derivation for a noncentral generator. -/
def correctionDerivation (i : X) : Derivation ℤ Poly Poly :=
  by
    have hmodule : (inferInstance : Module ℤ Poly) =
        AddCommGroup.toIntModule Poly := Subsingleton.elim _ _
    cases hmodule
    let hTower : IsScalarTower ℤ Poly Poly :=
      ⟨fun n p q ↦ (AddMonoidHom.mulRight q).map_zsmul p n⟩
    exact @MvPolynomial.mkDerivation I ℤ Poly inferInstance inferInstance
      inferInstance inferInstance hTower (correctionValue X i)

@[simp]
theorem correctionDerivation_X_inl (i j : X) :
    correctionDerivation X i (MvPolynomial.X (ClassTwoBasisIndex.generator j : I)) =
      if (ClassTwoBasisIndex.generator j : I) <
          ClassTwoBasisIndex.generator i then
        freeClassTwoPolynomial X
          ⁅freeClassTwoBasis X (ClassTwoBasisIndex.generator i),
            freeClassTwoBasis X (ClassTwoBasisIndex.generator j)⁆
      else 0 := by
  simp [correctionDerivation, correctionValue]

@[simp]
theorem correctionDerivation_X_inr (i : X) (a : ClassTwoWedgeIndex X) :
    correctionDerivation X i (MvPolynomial.X (ClassTwoBasisIndex.central a : I)) = 0 := by
  simp [correctionDerivation, correctionValue]

/-- The correction derivation viewed using the canonical integral module structure on the
underlying additive group. -/
def correctionEnd (i : X) : Module.End ℤ Poly where
  toFun := correctionDerivation X i
  map_add' p q := map_add (correctionDerivation X i) p q
  map_smul' n p := map_zsmul (correctionDerivation X i) n p

@[simp]
theorem correctionEnd_apply (i : X) (p : Poly) :
    correctionEnd X i p = correctionDerivation X i p := rfl

/-- Correction derivations kill the polynomial coordinates of every central class-two
element. -/
theorem correctionDerivation_central (i : X) (w : ⋀[ℤ]^2 P) :
    correctionDerivation X i (freeClassTwoPolynomial X (0, w)) = 0 := by
  let bW := (freeGeneratorBasis X).exteriorPower 2
  let f : (⋀[ℤ]^2 P) →ₗ[ℤ] Poly :=
    (correctionEnd X i).comp
      ((freeClassTwoPolynomial X).comp (freeClassTwoCentralInclusion X))
  rw [← freeClassTwoCentralInclusion_apply X w]
  change f w = 0
  have hf : f = 0 := by
    apply bW.ext
    intro a
    change correctionDerivation X i
      (freeClassTwoPolynomial X (0, bW a)) = 0
    rw [show (0, bW a) = freeClassTwoBasis X (ClassTwoBasisIndex.central a) by
      exact (freeClassTwoBasis_inr X a).symm]
    rw [freeClassTwoPolynomial_basis, correctionDerivation_X_inr]
  rw [hf]
  rfl

@[simp]
theorem correctionDerivation_bracket (i : X) (x y : M) :
    correctionDerivation X i (freeClassTwoPolynomial X ⁅x, y⁆) = 0 := by
  rw [FreeClassTwo.bracket_apply]
  exact correctionDerivation_central X i (wedgeTwo P x.1 y.1)

/-- The correction derivations commute.  Their values on generator variables are central
coordinate polynomials, and every correction derivation kills such polynomials. -/
theorem correctionDerivation_commute (i j : X) (p : Poly) :
    correctionDerivation X i (correctionDerivation X j p) =
      correctionDerivation X j (correctionDerivation X i p) := by
  have hX (k : I) :
      correctionDerivation X i
          (correctionDerivation X j (MvPolynomial.X k)) =
        correctionDerivation X j
          (correctionDerivation X i (MvPolynomial.X k)) := by
    cases k with
    | generator k =>
        simp only [correctionDerivation_X_inl]
        split_ifs <;> simp only [correctionDerivation_bracket,
          Derivation.map_zero]
    | central a =>
        simp only [correctionDerivation_X_inr, Derivation.map_zero]
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

/-- The antisymmetric difference of the two triangular corrections is the class-two bracket
coordinate. -/
theorem correctionDerivation_X_sub (i j : X) :
    correctionDerivation X i (MvPolynomial.X (ClassTwoBasisIndex.generator j : I)) -
        correctionDerivation X j (MvPolynomial.X (ClassTwoBasisIndex.generator i : I)) =
      freeClassTwoPolynomial X
        ⁅freeClassTwoBasis X (ClassTwoBasisIndex.generator i), freeClassTwoBasis X (ClassTwoBasisIndex.generator j)⁆ := by
  rcases lt_trichotomy (ClassTwoBasisIndex.generator i : I)
      (ClassTwoBasisIndex.generator j) with hij | hij | hij
  · have hji : ¬ (ClassTwoBasisIndex.generator j : I) <
        ClassTwoBasisIndex.generator i := not_lt_of_ge (le_of_lt hij)
    rw [correctionDerivation_X_inl, correctionDerivation_X_inl]
    simp only [hij, hji, if_true, if_false, zero_sub]
    rw [← map_neg, lie_skew]
  · have hEq : i = j := ClassTwoBasisIndex.generator.inj hij
    subst j
    simp
  · have hij' : ¬ (ClassTwoBasisIndex.generator i : I) <
        ClassTwoBasisIndex.generator j := not_lt_of_ge (le_of_lt hij)
    rw [correctionDerivation_X_inl, correctionDerivation_X_inl]
    simp [hij, hij']

/-- The operator attached to a canonical class-two basis vector. -/
def freeClassTwoActionBasis : I → Module.End ℤ Poly
  | ClassTwoBasisIndex.generator i => polynomialMul X (MvPolynomial.X (ClassTwoBasisIndex.generator i : I)) +
      correctionEnd X i
  | ClassTwoBasisIndex.central a => polynomialMul X (MvPolynomial.X (ClassTwoBasisIndex.central a : I))

/-- Extend the basis operators linearly to the free class-two Lie ring. -/
def freeClassTwoAction : M →ₗ[ℤ] Module.End ℤ Poly :=
  (Finsupp.linearCombination ℤ (freeClassTwoActionBasis X)).comp
    (freeClassTwoBasis X).repr.toLinearMap

@[simp]
theorem freeClassTwoAction_basis (i : I) :
    freeClassTwoAction X (freeClassTwoBasis X i) = freeClassTwoActionBasis X i := by
  simp [freeClassTwoAction]

@[simp]
theorem freeClassTwoAction_basis_inl_apply (i : X) (p : Poly) :
    freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)) p =
      MvPolynomial.X (ClassTwoBasisIndex.generator i : I) * p + correctionDerivation X i p := by
  simp [freeClassTwoActionBasis, polynomialMul]

@[simp]
theorem freeClassTwoAction_basis_inr_apply
    (a : ClassTwoWedgeIndex X) (p : Poly) :
    freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) p =
      MvPolynomial.X (ClassTwoBasisIndex.central a : I) * p := by
  rw [freeClassTwoAction_basis]
  rfl

/-- Multiplication by a polynomial depends linearly on the polynomial. -/
def polynomialMulLinear : Poly →ₗ[ℤ] Module.End ℤ Poly where
  toFun := polynomialMul X
  map_add' p q := by
    apply LinearMap.ext
    intro r
    exact add_mul p q r
  map_smul' n p := by
    apply LinearMap.ext
    intro q
    change (n • p) * q = n • (p * q)
    exact smul_mul_assoc n p q

@[simp]
theorem polynomialMulLinear_apply (p q : Poly) :
    polynomialMulLinear X p q = p * q := rfl

/-- Every element in the exterior-square summand acts by multiplication by its coordinate
polynomial. -/
theorem freeClassTwoAction_central (w : ⋀[ℤ]^2 P) :
    freeClassTwoAction X (0, w) =
      polynomialMul X (freeClassTwoPolynomial X (0, w)) := by
  let bW := (freeGeneratorBasis X).exteriorPower 2
  let lhs : (⋀[ℤ]^2 P) →ₗ[ℤ] Module.End ℤ Poly :=
    (freeClassTwoAction X).comp (freeClassTwoCentralInclusion X)
  let rhs : (⋀[ℤ]^2 P) →ₗ[ℤ] Module.End ℤ Poly :=
    (polynomialMulLinear X).comp
      ((freeClassTwoPolynomial X).comp (freeClassTwoCentralInclusion X))
  have h : lhs = rhs := by
    apply bW.ext
    intro a
    change freeClassTwoAction X (0, bW a) =
      polynomialMul X (freeClassTwoPolynomial X (0, bW a))
    rw [show (0, bW a) = freeClassTwoBasis X (ClassTwoBasisIndex.central a) by
      exact (freeClassTwoBasis_inr X a).symm]
    rw [freeClassTwoAction_basis, freeClassTwoPolynomial_basis]
    rfl
  rw [← freeClassTwoCentralInclusion_apply X w]
  exact LinearMap.congr_fun h w

@[simp]
theorem freeClassTwoAction_bracket (x y : M) :
    freeClassTwoAction X ⁅x, y⁆ =
      polynomialMul X (freeClassTwoPolynomial X ⁅x, y⁆) := by
  rw [FreeClassTwo.bracket_apply]
  exact freeClassTwoAction_central X (wedgeTwo P x.1 y.1)

/-- The commutator of two generator operators is multiplication by their class-two bracket. -/
theorem freeClassTwoAction_inl_commutator (i j : X) :
    ⁅freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)),
      freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator j))⁆ =
    polynomialMul X
      (freeClassTwoPolynomial X
        ⁅freeClassTwoBasis X (ClassTwoBasisIndex.generator i), freeClassTwoBasis X (ClassTwoBasisIndex.generator j)⁆) := by
  apply LinearMap.ext
  intro p
  change
    freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i))
        (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator j)) p) -
      freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator j))
        (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)) p) =
      freeClassTwoPolynomial X
        ⁅freeClassTwoBasis X (ClassTwoBasisIndex.generator i), freeClassTwoBasis X (ClassTwoBasisIndex.generator j)⁆ * p
  rw [freeClassTwoAction_basis_inl_apply, freeClassTwoAction_basis_inl_apply,
    freeClassTwoAction_basis_inl_apply, freeClassTwoAction_basis_inl_apply]
  rw [map_add, map_add, Derivation.leibniz, Derivation.leibniz,
    correctionDerivation_commute X i j p]
  rw [← correctionDerivation_X_sub X i j]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  ring

/-- The explicit polynomial action respects the Lie bracket. -/
theorem freeClassTwoAction_map_lie (x y : M) :
    freeClassTwoAction X ⁅x, y⁆ =
      ⁅freeClassTwoAction X x, freeClassTwoAction X y⁆ := by
  let lhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun a b ↦ freeClassTwoAction X ⁅a, b⁆)
      (by
        intro a b c
        change freeClassTwoAction X ⁅a + b, c⁆ =
          freeClassTwoAction X ⁅a, c⁆ + freeClassTwoAction X ⁅b, c⁆
        rw [add_lie, map_add])
      (by
        intro n a b
        change freeClassTwoAction X ⁅n • a, b⁆ =
          n • freeClassTwoAction X ⁅a, b⁆
        rw [smul_lie, map_smul])
      (by
        intro a b c
        change freeClassTwoAction X ⁅a, b + c⁆ =
          freeClassTwoAction X ⁅a, b⁆ + freeClassTwoAction X ⁅a, c⁆
        rw [lie_add, map_add])
      (by
        intro n a b
        change freeClassTwoAction X ⁅a, n • b⁆ =
          n • freeClassTwoAction X ⁅a, b⁆
        rw [lie_smul, map_smul])
  let rhs : M →ₗ[ℤ] M →ₗ[ℤ] Module.End ℤ Poly :=
    LinearMap.mk₂ ℤ (fun a b ↦ ⁅freeClassTwoAction X a, freeClassTwoAction X b⁆)
      (by
        intro a b c
        change ⁅freeClassTwoAction X (a + b), freeClassTwoAction X c⁆ = _
        rw [map_add, add_lie])
      (by
        intro n a b
        change ⁅freeClassTwoAction X (n • a), freeClassTwoAction X b⁆ = _
        rw [map_smul, smul_lie])
      (by
        intro a b c
        change ⁅freeClassTwoAction X a, freeClassTwoAction X (b + c)⁆ = _
        rw [map_add, lie_add])
      (by
        intro n a b
        change ⁅freeClassTwoAction X a, freeClassTwoAction X (n • b)⁆ = _
        rw [map_smul, lie_smul])
  have hb : lhs = rhs := by
    apply LinearMap.ext_basis (freeClassTwoBasis X) (freeClassTwoBasis X)
    intro i j
    change freeClassTwoAction X
        ⁅freeClassTwoBasis X i, freeClassTwoBasis X j⁆ =
      ⁅freeClassTwoAction X (freeClassTwoBasis X i),
        freeClassTwoAction X (freeClassTwoBasis X j)⁆
    cases i with
    | generator i =>
        cases j with
        | generator j =>
            rw [freeClassTwoAction_bracket, freeClassTwoAction_inl_commutator]
        | central a =>
            rw [FreeClassTwo.bracket_apply, freeClassTwoBasis_inr_fst,
              wedgeTwo_zero_right]
            apply LinearMap.ext
            intro p
            rw [show ((0, 0) : M) = 0 by rfl, map_zero, LinearMap.zero_apply]
            change 0 =
              (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)) *
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) -
              freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) *
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i))) p
            rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
            change 0 =
              freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i))
                  (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) p) -
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a))
                  (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator i)) p)
            rw [freeClassTwoAction_basis_inr_apply,
              freeClassTwoAction_basis_inl_apply,
              freeClassTwoAction_basis_inl_apply,
              freeClassTwoAction_basis_inr_apply]
            rw [Derivation.leibniz, correctionDerivation_X_inr]
            simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
            ring
    | central a =>
        cases j with
        | generator j =>
            rw [FreeClassTwo.bracket_apply, freeClassTwoBasis_inr_fst,
              wedgeTwo_zero_left]
            apply LinearMap.ext
            intro p
            rw [show ((0, 0) : M) = 0 by rfl, map_zero, LinearMap.zero_apply]
            change 0 =
              (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) *
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator j)) -
              freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator j)) *
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a))) p
            rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
            change 0 =
              freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a))
                  (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator j)) p) -
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.generator j))
                  (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) p)
            rw [freeClassTwoAction_basis_inl_apply,
              freeClassTwoAction_basis_inr_apply,
              freeClassTwoAction_basis_inr_apply,
              freeClassTwoAction_basis_inl_apply]
            rw [Derivation.leibniz, correctionDerivation_X_inr]
            simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
            ring
        | central b =>
            rw [FreeClassTwo.bracket_apply, freeClassTwoBasis_inr_fst,
              wedgeTwo_zero_left]
            apply LinearMap.ext
            intro p
            rw [show ((0, 0) : M) = 0 by rfl, map_zero, LinearMap.zero_apply]
            change 0 =
              (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) *
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central b)) -
              freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central b)) *
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a))) p
            rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
            change 0 =
              freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a))
                  (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central b)) p) -
                freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central b))
                  (freeClassTwoAction X (freeClassTwoBasis X (ClassTwoBasisIndex.central a)) p)
            rw [freeClassTwoAction_basis_inr_apply,
              freeClassTwoAction_basis_inr_apply,
              freeClassTwoAction_basis_inr_apply,
              freeClassTwoAction_basis_inr_apply]
            ring
  exact DFunLike.congr_fun (DFunLike.congr_fun hb x) y

/-- The free class-two Lie ring acts on its coordinate polynomial ring by the triangular
operators above. -/
def freeClassTwoLieHom : LieHom ℤ M (Module.End ℤ Poly) where
  __ := freeClassTwoAction X
  map_lie' {x y} := freeClassTwoAction_map_lie X x y

@[simp]
theorem freeClassTwoLieHom_apply (x : M) :
    freeClassTwoLieHom X x = freeClassTwoAction X x := rfl

/-- The commutative variable word attached to a list of basis indices. -/
def classTwoVariableWord (is : List I) : Poly :=
  (is.map MvPolynomial.X).prod

@[simp]
theorem classTwoVariableWord_nil : classTwoVariableWord X [] = 1 := rfl

@[simp]
theorem classTwoVariableWord_cons (i : I) (is : List I) :
    classTwoVariableWord X (i :: is) =
      MvPolynomial.X i * classTwoVariableWord X is := by
  simp [classTwoVariableWord]

theorem classTwo_toFinsupp_cons (i : I) (is : List I) :
    Multiset.toFinsupp ((i :: is : List I) : Multiset I) =
      Finsupp.single i 1 + Multiset.toFinsupp (is : Multiset I) := by
  rw [show ((i :: is : List I) : Multiset I) = {i} + (is : Multiset I) by rfl,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

/-- A variable word is the monomial whose exponent vector counts its letters. -/
theorem classTwoVariableWord_eq_monomial (is : List I) :
    classTwoVariableWord X is =
      MvPolynomial.monomial (Multiset.toFinsupp (is : Multiset I)) 1 := by
  induction is with
  | nil => simp [classTwoVariableWord]
  | cons i is ih =>
      rw [classTwoVariableWord_cons, ih, classTwo_toFinsupp_cons]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul]

/-- A correction derivation vanishes on every variable not preceding its generator. -/
theorem correctionDerivation_X_eq_zero_of_le (i : X) (k : I)
    (hik : (ClassTwoBasisIndex.generator i : I) ≤ k) :
    correctionDerivation X i (MvPolynomial.X k) = 0 := by
  cases k with
  | generator j =>
      rw [correctionDerivation_X_inl]
      simp [not_lt_of_ge hik]
  | central a =>
      exact correctionDerivation_X_inr X i a

/-- Hence the correction attached to `i` kills an ordered suffix beginning no earlier than
`i`. -/
theorem correctionDerivation_classTwoVariableWord_eq_zero
    (i : X) (is : List I)
    (hi : ∀ k ∈ is, (ClassTwoBasisIndex.generator i : I) ≤ k) :
    correctionDerivation X i (classTwoVariableWord X is) = 0 := by
  induction is with
  | nil => simp [classTwoVariableWord]
  | cons k is ih =>
      rw [classTwoVariableWord_cons, Derivation.leibniz,
        correctionDerivation_X_eq_zero_of_le X i k (hi k (by simp)),
        ih (fun j hj ↦ hi j (by simp [hj]))]
      simp

/-- A basis operator prepends its variable to an ordered suffix. -/
theorem freeClassTwoAction_basis_classTwoVariableWord
    (i : I) (is : List I) (hi : ∀ j ∈ is, i ≤ j) :
    freeClassTwoAction X (freeClassTwoBasis X i)
        (classTwoVariableWord X is) =
      classTwoVariableWord X (i :: is) := by
  cases i with
  | generator i =>
      rw [freeClassTwoAction_basis_inl_apply,
        correctionDerivation_classTwoVariableWord_eq_zero X i is hi,
        add_zero, classTwoVariableWord_cons]
  | central a =>
      rw [freeClassTwoAction_basis_inr_apply, classTwoVariableWord_cons]

/-- The product of the operators belonging to a basis word. -/
def freeClassTwoBasisWordAction (is : List I) : Module.End ℤ Poly :=
  (is.map fun i ↦ freeClassTwoLieHom X (freeClassTwoBasis X i)).prod

@[simp]
theorem freeClassTwoBasisWordAction_nil :
    freeClassTwoBasisWordAction X [] = 1 := rfl

@[simp]
theorem freeClassTwoBasisWordAction_cons (i : I) (is : List I) :
    freeClassTwoBasisWordAction X (i :: is) =
      freeClassTwoLieHom X (freeClassTwoBasis X i) *
        freeClassTwoBasisWordAction X is := by
  simp [freeClassTwoBasisWordAction]

/-- An ordered basis word sends the vacuum to its variable word. -/
theorem freeClassTwoBasisWordAction_apply_one
    (is : List I) (his : is.Pairwise (· ≤ ·)) :
    freeClassTwoBasisWordAction X is 1 = classTwoVariableWord X is := by
  induction is with
  | nil => simp [freeClassTwoBasisWordAction, classTwoVariableWord]
  | cons i is ih =>
      have hcons := List.pairwise_cons.mp his
      rw [freeClassTwoBasisWordAction_cons, Module.End.mul_apply, ih hcons.2]
      change freeClassTwoAction X (freeClassTwoBasis X i)
          (classTwoVariableWord X is) = _
      exact freeClassTwoAction_basis_classTwoVariableWord X i is hcons.1

/-- Exponent-vector form of the ordered-word vacuum identity. -/
def classTwoSortedWord (e : I →₀ ℕ) : List I := by
  classical
  exact (Finsupp.toMultiset e).sort (· ≤ ·)

theorem freeClassTwoBasisWordAction_sortedExponent_apply_one (e : I →₀ ℕ) :
    freeClassTwoBasisWordAction X (classTwoSortedWord X e) 1 =
      MvPolynomial.monomial e 1 := by
  classical
  unfold classTwoSortedWord
  rw [freeClassTwoBasisWordAction_apply_one X _ (Multiset.pairwise_sort _ _),
    classTwoVariableWord_eq_monomial]
  congr 2
  rw [Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

/-- The explicit triangular representation of the free class-two Lie ring. -/
def freeClassTwoTriangularRepresentation :
    LieRings.PBW.TriangularRepresentation ℤ M I (freeClassTwoBasis X) where
  toLieHom := freeClassTwoLieHom X
  orderedMonomial_apply_one e := by
    classical
    unfold LieRings.PBW.orderedMonomial
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    have h := freeClassTwoBasisWordAction_sortedExponent_apply_one X e
    unfold classTwoSortedWord freeClassTwoBasisWordAction at h
    exact h

/-- PBW for the explicit free class-two Lie ring, as a linear equivalence with its coordinate
polynomial ring. -/
def freeClassTwoPBWLinearEquiv :
    Poly ≃ₗ[ℤ] UEA ℤ M :=
  (freeClassTwoTriangularRepresentation X).orderedPBWLinearEquiv

end

end DegreeFive

end LieRings
