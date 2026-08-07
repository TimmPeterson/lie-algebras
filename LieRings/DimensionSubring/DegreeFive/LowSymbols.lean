import LieRings.DimensionSubring.DegreeFive.FreeClassTwoKernel
import LieRings.PBW.Reduction
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Integral symbols through associative degree two

The placed calculation must compare coefficients without dividing by two.  We therefore use the
truncated tensor algebra

`ℤ ⊕ P ⊕ (P ⊗ P)`

with all products of three positive-degree factors set to zero.  Its first two positive
components remember ordered tensor words.  The commutator of two degree-one elements has
quadratic component `x ⊗ y - y ⊗ x`, exactly the integral alternation of `x ∧ y`.
-/

namespace LieRings

open scoped TensorProduct

universe u

namespace DegreeFive

noncomputable section

variable (P : Type u) [AddCommGroup P]

/-- The tensor algebra on `P`, truncated after degree two. -/
@[ext]
structure QuadraticTensorTruncation where
  scalar : ℤ
  linear : P
  quadratic : P ⊗[ℤ] P

namespace QuadraticTensorTruncation

/-- Coordinate equivalence used to transport the additive and module structures. -/
def equivProd : QuadraticTensorTruncation P ≃ ℤ × P × (P ⊗[ℤ] P) where
  toFun x := (x.scalar, x.linear, x.quadratic)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

instance : AddCommGroup (QuadraticTensorTruncation P) :=
  (equivProd P).addCommGroup

@[simp]
theorem zero_scalar : (0 : QuadraticTensorTruncation P).scalar = 0 := rfl

@[simp]
theorem zero_linear : (0 : QuadraticTensorTruncation P).linear = 0 := rfl

@[simp]
theorem zero_quadratic : (0 : QuadraticTensorTruncation P).quadratic = 0 := rfl

@[simp]
theorem add_scalar (a b : QuadraticTensorTruncation P) :
    (a + b).scalar = a.scalar + b.scalar := rfl

@[simp]
theorem add_linear (a b : QuadraticTensorTruncation P) :
    (a + b).linear = a.linear + b.linear := rfl

@[simp]
theorem add_quadratic (a b : QuadraticTensorTruncation P) :
    (a + b).quadratic = a.quadratic + b.quadratic := rfl

@[simp]
theorem neg_scalar (a : QuadraticTensorTruncation P) :
    (-a).scalar = -a.scalar := rfl

@[simp]
theorem neg_linear (a : QuadraticTensorTruncation P) :
    (-a).linear = -a.linear := rfl

@[simp]
theorem neg_quadratic (a : QuadraticTensorTruncation P) :
    (-a).quadratic = -a.quadratic := rfl

@[simp]
theorem sub_scalar (a b : QuadraticTensorTruncation P) :
    (a - b).scalar = a.scalar - b.scalar := rfl

@[simp]
theorem sub_linear (a b : QuadraticTensorTruncation P) :
    (a - b).linear = a.linear - b.linear := rfl

@[simp]
theorem sub_quadratic (a b : QuadraticTensorTruncation P) :
    (a - b).quadratic = a.quadratic - b.quadratic := rfl

@[simp]
theorem smul_scalar (n : ℤ) (a : QuadraticTensorTruncation P) :
    (n • a).scalar = n • a.scalar := rfl

@[simp]
theorem smul_linear (n : ℤ) (a : QuadraticTensorTruncation P) :
    (n • a).linear = n • a.linear := rfl

@[simp]
theorem smul_quadratic (n : ℤ) (a : QuadraticTensorTruncation P) :
    (n • a).quadratic = n • a.quadratic := rfl

@[simp]
theorem mk_add_mk (a b : ℤ) (x y : P) (t u : P ⊗[ℤ] P) :
    (⟨a, x, t⟩ + ⟨b, y, u⟩ : QuadraticTensorTruncation P) =
      ⟨a + b, x + y, t + u⟩ := rfl

@[simp]
theorem smul_mk (n a : ℤ) (x : P) (t : P ⊗[ℤ] P) :
    n • (⟨a, x, t⟩ : QuadraticTensorTruncation P) =
      ⟨n • a, n • x, n • t⟩ := rfl

/-- Projection to the degree-one component. -/
def linearProjection : QuadraticTensorTruncation P →ₗ[ℤ] P where
  toFun x := x.linear
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem linearProjection_apply (x : QuadraticTensorTruncation P) :
    linearProjection P x = x.linear := rfl

/-- Projection to the degree-two ordered tensor component. -/
def quadraticProjection :
    QuadraticTensorTruncation P →ₗ[ℤ] (P ⊗[ℤ] P) where
  toFun x := x.quadratic
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem quadraticProjection_apply (x : QuadraticTensorTruncation P) :
    quadraticProjection P x = x.quadratic := rfl

/-- Move an integral scalar from the first tensor factor to the tensor product.  This lemma also
bridges the two definitionally distinct, but propositionally equal, integral scalar actions that
arise for a tensor product over `ℤ`. -/
theorem zsmul_tmul_left (n : ℤ) (x y : P) :
    (n • x) ⊗ₜ[ℤ] y = n • (x ⊗ₜ[ℤ] y) :=
  (TensorProduct.smul_tmul' n x y).symm

/-- Move an integral scalar from the second tensor factor to the tensor product. -/
theorem tmul_zsmul_right (n : ℤ) (x y : P) :
    x ⊗ₜ[ℤ] (n • y) = n • (x ⊗ₜ[ℤ] y) := by
  rw [TensorProduct.tmul_smul]
  exact (TensorProduct.smul_tmul' n x y).symm

/-- Associativity of the specific integral scalar action carried by the tensor product. -/
theorem zsmul_zsmul_tensor (n m : ℤ) (t : P ⊗[ℤ] P) :
    n • (m • t) = (n * m) • t :=
  (mul_zsmul t n m).symm

instance : One (QuadraticTensorTruncation P) :=
  ⟨⟨1, 0, 0⟩⟩

instance : Mul (QuadraticTensorTruncation P) where
  mul a b :=
    ⟨a.scalar * b.scalar,
      a.scalar • b.linear + b.scalar • a.linear,
      a.scalar • b.quadratic + b.scalar • a.quadratic +
        a.linear ⊗ₜ[ℤ] b.linear⟩

@[simp]
theorem one_scalar : (1 : QuadraticTensorTruncation P).scalar = 1 := rfl

@[simp]
theorem one_linear : (1 : QuadraticTensorTruncation P).linear = 0 := rfl

@[simp]
theorem one_quadratic : (1 : QuadraticTensorTruncation P).quadratic = 0 := rfl

@[simp]
theorem mul_scalar (a b : QuadraticTensorTruncation P) :
    (a * b).scalar = a.scalar * b.scalar := rfl

@[simp]
theorem mul_linear (a b : QuadraticTensorTruncation P) :
    (a * b).linear = a.scalar • b.linear + b.scalar • a.linear := rfl

@[simp]
theorem mul_quadratic (a b : QuadraticTensorTruncation P) :
    (a * b).quadratic =
      a.scalar • b.quadratic + b.scalar • a.quadratic +
        a.linear ⊗ₜ[ℤ] b.linear := rfl

instance : NonUnitalNonAssocRing (QuadraticTensorTruncation P) where
  zero_mul a := by
    ext
    · simp
    · simp
    · simp only [mul_quadratic, zero_scalar, zero_linear, zero_quadratic,
        zero_smul, zero_add, TensorProduct.zero_tmul]
      rw [zsmul_zero, zero_add]
  mul_zero a := by
    ext
    · simp
    · simp
    · simp only [mul_quadratic, zero_scalar, zero_linear, zero_quadratic,
        zero_smul, add_zero, TensorProduct.tmul_zero]
      exact zsmul_zero _
  left_distrib a b c := by
    ext
    · exact Int.mul_add _ _ _
    · simp only [mul_linear, add_linear, add_scalar, smul_add, add_smul]
      abel
    · simp only [mul_quadratic, add_quadratic, add_scalar, add_linear,
        add_smul, TensorProduct.tmul_add]
      rw [zsmul_add]
      abel
  right_distrib a b c := by
    ext
    · exact Int.add_mul _ _ _
    · simp only [mul_linear, add_linear, add_scalar, smul_add, add_smul]
      abel
    · simp only [mul_quadratic, add_quadratic, add_scalar, add_linear,
        add_smul, TensorProduct.add_tmul]
      rw [zsmul_add]
      abel

instance : Monoid (QuadraticTensorTruncation P) where
  one_mul a := by
    ext
    · simp
    · simp only [mul_linear, one_scalar, one_linear, one_smul]
      rw [zsmul_zero, add_zero]
    · simp only [mul_quadratic, one_scalar, one_linear, one_quadratic,
        one_smul, add_zero, TensorProduct.zero_tmul]
      rw [zsmul_zero, add_zero]
  mul_one a := by
    ext
    · simp
    · simp only [mul_linear, one_scalar, one_linear, one_smul]
      rw [zsmul_zero, zero_add]
    · simp only [mul_quadratic, one_scalar, one_linear, one_quadratic,
        one_smul, add_zero, TensorProduct.tmul_zero]
      rw [zsmul_zero, zero_add]
  mul_assoc a b c := by
    ext
    · simp [mul_assoc]
    · simp only [mul_linear, mul_scalar, smul_add, smul_smul, mul_comm]
      abel
    · simp only [mul_quadratic, mul_scalar, mul_linear,
        TensorProduct.add_tmul, TensorProduct.tmul_add,
        zsmul_tmul_left, tmul_zsmul_right]
      simp only [zsmul_add, zsmul_zsmul_tensor, mul_comm]
      abel

instance : Ring (QuadraticTensorTruncation P) where

/-- A pure degree-one element. -/
def ofLinear (x : P) : QuadraticTensorTruncation P :=
  ⟨0, x, 0⟩

@[simp]
theorem ofLinear_scalar (x : P) : (ofLinear P x).scalar = 0 := rfl

@[simp]
theorem ofLinear_linear (x : P) : (ofLinear P x).linear = x := rfl

@[simp]
theorem ofLinear_quadratic (x : P) : (ofLinear P x).quadratic = 0 := rfl

@[simp]
theorem ofLinear_mul_ofLinear (x y : P) :
    ofLinear P x * ofLinear P y = ⟨0, 0, x ⊗ₜ[ℤ] y⟩ := by
  ext <;> simp [ofLinear]

/-- Three positive-degree generators multiply to zero. -/
@[simp]
theorem ofLinear_mul_ofLinear_mul_ofLinear (x y z : P) :
    ofLinear P x * ofLinear P y * ofLinear P z = 0 := by
  ext <;> simp [ofLinear]

/-- The same degree argument for arbitrary elements with zero scalar component.  This is the
form needed for products of free-Lie symbols: such a symbol can have both a linear and a
quadratic component, but it still has positive augmentation degree. -/
theorem mul_mul_eq_zero_of_scalar_eq_zero
    (a b c : QuadraticTensorTruncation P)
    (ha : a.scalar = 0) (hb : b.scalar = 0) (hc : c.scalar = 0) :
    a * b * c = 0 := by
  ext
  · simp [ha, hb, hc]
  · simp [ha, hb, hc]
  · simp only [mul_quadratic, mul_scalar, mul_linear, ha, hb, hc,
      zero_mul, zero_smul, add_zero, zero_add]
    change (0 : P) ⊗ₜ[ℤ] c.linear = (0 : P ⊗[ℤ] P)
    exact TensorProduct.zero_tmul P c.linear

/-- A product of two positive symbols only remembers the ordered tensor of their linear
components. -/
theorem mul_eq_quadratic_of_scalar_eq_zero
    (a b : QuadraticTensorTruncation P)
    (ha : a.scalar = 0) (hb : b.scalar = 0) :
    a * b = ⟨0, 0, a.linear ⊗ₜ[ℤ] b.linear⟩ := by
  ext <;> simp [ha, hb]

end QuadraticTensorTruncation

/-! ## Integral alternation -/

/-- The alternating tensor `x ⊗ y - y ⊗ x`. -/
def tensorAlternating :
    P [⋀^Fin 2]→ₗ[ℤ] (P ⊗[ℤ] P) where
  toFun v := v 0 ⊗ₜ[ℤ] v 1 - v 1 ⊗ₜ[ℤ] v 0
  map_update_add' v i x y := by
    fin_cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add] <;> abel
  map_update_smul' v i n x := by
    fin_cases i
    · simp
      exact (zsmul_sub (x ⊗ₜ[ℤ] v 1) (v 1 ⊗ₜ[ℤ] x) n).symm
    · simp
      exact (zsmul_sub (v 0 ⊗ₜ[ℤ] x) (x ⊗ₜ[ℤ] v 0) n).symm
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change v 0 ⊗ₜ[ℤ] v 1 - v 1 ⊗ₜ[ℤ] v 0 = 0
      change v 0 = v 1 at hv
      rw [hv, sub_self]
    · change v 0 ⊗ₜ[ℤ] v 1 - v 1 ⊗ₜ[ℤ] v 0 = 0
      change v 1 = v 0 at hv
      rw [hv, sub_self]
    · exact (hij rfl).elim

/-- Integral alternation from the exterior square into the ordered tensor square. -/
def exteriorToTensor : ⋀[ℤ]^2 P →ₗ[ℤ] (P ⊗[ℤ] P) :=
  exteriorPower.alternatingMapLinearEquiv (tensorAlternating P)

@[simp]
theorem exteriorToTensor_wedge (x y : P) :
    exteriorToTensor P (wedgeTwo P x y) =
      x ⊗ₜ[ℤ] y - y ⊗ₜ[ℤ] x := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (tensorAlternating P) ![x, y]

/-- Embed the free class-two Lie ring into the commutator Lie ring of the quadratic tensor
truncation, retaining the integral alternating tensor in degree two. -/
def freeClassTwoToQuadraticTensor :
    FreeClassTwo P →ₗ⁅ℤ⁆ CommutatorRing (QuadraticTensorTruncation P) where
  toLinearMap :=
    ({ toFun := fun x ↦ ⟨0, x.1, exteriorToTensor P x.2⟩
       map_zero' := by
         change (⟨0, 0, exteriorToTensor P 0⟩ :
             QuadraticTensorTruncation P) = 0
         apply QuadraticTensorTruncation.ext <;> simp
       map_add' := by
         intro x y
         change (⟨0, x.1 + y.1, exteriorToTensor P (x.2 + y.2)⟩ :
             QuadraticTensorTruncation P) =
           ⟨0, x.1, exteriorToTensor P x.2⟩ +
             ⟨0, y.1, exteriorToTensor P y.2⟩
         simp } : FreeClassTwo P →+ CommutatorRing
           (QuadraticTensorTruncation P)).toIntLinearMap
  map_lie' := by
    intro x y
    change (⟨0, 0, exteriorToTensor P (wedgeTwo P x.1 y.1)⟩ :
        QuadraticTensorTruncation P) =
      ⟨0, x.1, exteriorToTensor P x.2⟩ *
          ⟨0, y.1, exteriorToTensor P y.2⟩ -
        ⟨0, y.1, exteriorToTensor P y.2⟩ *
          ⟨0, x.1, exteriorToTensor P x.2⟩
    apply QuadraticTensorTruncation.ext
    · simp
    · simp
    · simp [exteriorToTensor_wedge]

@[simp]
theorem freeClassTwoToQuadraticTensor_apply (x : FreeClassTwo P) :
    freeClassTwoToQuadraticTensor P x =
      ⟨0, x.1, exteriorToTensor P x.2⟩ := rfl

/-! ## Comparison with free associative words -/

variable (X : Type u)

local notation "PX" => GeneratorModule X

/-- Evaluate free associative words in the quadratic tensor truncation. -/
def freeAlgebraToQuadraticTensor :
    FreeAlgebra ℤ X →ₐ[ℤ] QuadraticTensorTruncation PX :=
  FreeAlgebra.lift ℤ (fun x ↦
    QuadraticTensorTruncation.ofLinear PX (Finsupp.single x 1))

@[simp]
theorem freeAlgebraToQuadraticTensor_ι (x : X) :
    freeAlgebraToQuadraticTensor X (FreeAlgebra.ι ℤ x) =
      QuadraticTensorTruncation.ofLinear PX (Finsupp.single x 1) := by
  exact FreeAlgebra.lift_ι_apply _ _

/-- The free-Lie quadratic symbol, defined by the same degree-one generators. -/
def freeLieToQuadraticTensor :
    FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆
      CommutatorRing (QuadraticTensorTruncation PX) :=
  FreeLieAlgebra.lift ℤ (fun x ↦
    QuadraticTensorTruncation.ofLinear PX (Finsupp.single x 1))

/-- **Low-symbol comparison.** The ordered degree-one and degree-two tensor symbols of a
free-Lie element are precisely its basis-free class-two truncation, with the exterior component
sent through integral alternation. -/
theorem freeLieToQuadraticTensor_eq_classTwo :
    freeLieToQuadraticTensor X =
      (freeClassTwoToQuadraticTensor PX).comp (freeClassTwoTruncation X) := by
  apply FreeLieAlgebra.hom_ext
  intro x
  simp only [freeLieToQuadraticTensor, FreeLieAlgebra.lift_of_apply]
  change QuadraticTensorTruncation.ofLinear PX (Finsupp.single x 1) =
    freeClassTwoToQuadraticTensor PX (freeClassTwoTruncation X
      (FreeLieAlgebra.of ℤ x))
  rw [freeClassTwoTruncation_of, freeClassTwoToQuadraticTensor_apply]
  simp [QuadraticTensorTruncation.ofLinear]

@[simp]
theorem freeLieToQuadraticTensor_apply (x : FreeLieAlgebra ℤ X) :
    freeLieToQuadraticTensor X x =
      ⟨0,
        (freeClassTwoTruncation X x).1,
        exteriorToTensor PX (freeClassTwoTruncation X x).2⟩ := by
  rw [freeLieToQuadraticTensor_eq_classTwo]
  rfl

/-- The quadratic symbol obtained by first evaluating a free-Lie element as an associative word.
This is the comparison map that connects coefficient extraction in the free associative algebra
to the basis-free class-two Lie truncation. -/
def freeLieToQuadraticTensorViaFreeAlgebra :
    FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆
      CommutatorRing (QuadraticTensorTruncation PX) :=
  (freeAlgebraToQuadraticTensor X).toLieHom.comp
    (PBW.freeLieToFreeAlgebra ℤ X)

/-- Evaluating in the free associative algebra and then taking symbols agrees with the direct
free-Lie symbol map. -/
theorem freeLieToQuadraticTensorViaFreeAlgebra_eq :
    freeLieToQuadraticTensorViaFreeAlgebra X =
      freeLieToQuadraticTensor X := by
  apply FreeLieAlgebra.hom_ext
  intro x
  unfold freeLieToQuadraticTensorViaFreeAlgebra
  change freeAlgebraToQuadraticTensor X
      (PBW.freeLieToFreeAlgebra ℤ X (FreeLieAlgebra.of ℤ x)) =
    freeLieToQuadraticTensor X (FreeLieAlgebra.of ℤ x)
  unfold PBW.freeLieToFreeAlgebra freeLieToQuadraticTensor
  calc
    freeAlgebraToQuadraticTensor X
        ((FreeLieAlgebra.lift ℤ (FreeAlgebra.ι ℤ))
          (FreeLieAlgebra.of ℤ x)) =
        QuadraticTensorTruncation.ofLinear PX (Finsupp.single x 1) := by
      rw [FreeLieAlgebra.lift_of_apply]
      exact freeAlgebraToQuadraticTensor_ι X x
    _ = (FreeLieAlgebra.lift ℤ (fun y ↦
          QuadraticTensorTruncation.ofLinear PX (Finsupp.single y 1)))
          (FreeLieAlgebra.of ℤ x) := by
      rw [FreeLieAlgebra.lift_of_apply]

/-- **Associative/Lie low-symbol comparison.** For every free-Lie element, the scalar symbol of
its associative evaluation is zero, its linear symbol is the degree-one class-two component, and
its quadratic symbol is the integral alternation of the degree-two component. -/
theorem freeAlgebraToQuadraticTensor_freeLieToFreeAlgebra (x : FreeLieAlgebra ℤ X) :
    freeAlgebraToQuadraticTensor X (PBW.freeLieToFreeAlgebra ℤ X x) =
      ⟨0,
        (freeClassTwoTruncation X x).1,
        exteriorToTensor PX (freeClassTwoTruncation X x).2⟩ := by
  change freeLieToQuadraticTensorViaFreeAlgebra X x = _
  rw [freeLieToQuadraticTensorViaFreeAlgebra_eq]
  exact freeLieToQuadraticTensor_apply X x

end

end DegreeFive

end LieRings
