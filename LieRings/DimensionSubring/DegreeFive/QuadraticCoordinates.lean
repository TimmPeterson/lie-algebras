import LieRings.DimensionSubring.DegreeFive.SemanticResolutionTensor

/-!
# Integral quadratic coordinates

For a free Abelian group with an ordered basis, commutative degree-two monomials distinguish
the ordered normal forms of tensors.  This is the precise integral injectivity statement used
to turn the quadratic PBW equation into an alternating boundary.
-/

namespace LieRings.DegreeFive
open scoped TensorProduct
noncomputable section
universe u v
variable {M : Type u} [AddCommGroup M]
variable {I : Type v} [LinearOrder I]
variable (b : Module.Basis I ℤ M)

def coordinatePolynomial : M →ₗ[ℤ] MvPolynomial I ℤ :=
  (Finsupp.linearCombination ℤ (MvPolynomial.X : I → MvPolynomial I ℤ)).comp
    b.repr.toLinearMap

@[simp] theorem coordinatePolynomial_basis (i : I) :
    coordinatePolynomial b (b i) = MvPolynomial.X i := by
  simp [coordinatePolynomial]

def tensorCommutativePolynomial : (M ⊗[ℤ] M) →ₗ[ℤ] MvPolynomial I ℤ :=
  TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun x y ↦ coordinatePolynomial b x * coordinatePolynomial b y)
    (by intros; simp [add_mul])
    (by intros; simp [Algebra.smul_def, mul_assoc])
    (by intros; simp [mul_add])
    (by
      intro c x y
      change coordinatePolynomial b x * coordinatePolynomial b (c • y) =
        c • (coordinatePolynomial b x * coordinatePolynomial b y)
      rw [map_smul]
      exact mul_smul_comm c (coordinatePolynomial b x)
        (coordinatePolynomial b y)))

@[simp] theorem tensorCommutativePolynomial_tmul (x y : M) :
    tensorCommutativePolynomial b (x ⊗ₜ[ℤ] y) =
      coordinatePolynomial b x * coordinatePolynomial b y :=
  TensorProduct.lift.tmul x y

@[simp] theorem tensorCommutativePolynomial_basis (i j : I) :
    tensorCommutativePolynomial b (b i ⊗ₜ[ℤ] b j) =
      MvPolynomial.X i * MvPolynomial.X j := by
  rw [tensorCommutativePolynomial_tmul, coordinatePolynomial_basis,
    coordinatePolynomial_basis]

def pairExponent (i j : I) : I →₀ ℕ :=
  Finsupp.single i 1 + Finsupp.single j 1

theorem pairExponent_eq_iff {a c i j : I} (hac : a ≤ c) (hij : i ≤ j) :
    pairExponent a c = pairExponent i j ↔ a = i ∧ c = j := by
  constructor
  · intro h
    have hm : ({a, c} : Multiset I) = {i, j} := by
      rw [Multiset.ext]
      intro x
      have hx := congrArg (fun e : I →₀ ℕ ↦ e x) h
      change Multiset.count x (a ::ₘ ({c} : Multiset I)) =
        Multiset.count x (i ::ₘ ({j} : Multiset I))
      rw [Multiset.count_cons, Multiset.count_cons,
        Multiset.count_singleton, Multiset.count_singleton]
      simpa [pairExponent, Finsupp.single_apply, eq_comm, add_comm] using hx
    have hs := congrArg
      (fun m : Multiset I ↦ m.sort (fun x y : I ↦ x ≤ y)) hm
    have hac' : ([a, c] : List I).Pairwise (· ≤ ·) := by simp [hac]
    have hij' : ([i, j] : List I).Pairwise (· ≤ ·) := by simp [hij]
    have hsortac : ({a, c} : Multiset I).sort (· ≤ ·) = [a, c] := by
      rw [show ({a, c} : Multiset I) = ([a, c] : List I) by rfl,
        Multiset.coe_sort, List.mergeSort_eq_self _ hac']
    have hsortij : ({i, j} : Multiset I).sort (· ≤ ·) = [i, j] := by
      rw [show ({i, j} : Multiset I) = ([i, j] : List I) by rfl,
        Multiset.coe_sort, List.mergeSort_eq_self _ hij']
    dsimp only at hs
    rw [hsortac, hsortij] at hs
    simpa using hs
  · rintro ⟨rfl, rfl⟩
    rfl

def mvCoefficient (e : I →₀ ℕ) : MvPolynomial I ℤ →ₗ[ℤ] ℤ where
  toFun p := MvPolynomial.coeff e p
  map_add' p q := MvPolynomial.coeff_add e p q
  map_smul' n p := by
    exact MvPolynomial.coeff_smul e n p

def tensorBasisCoordinate (i j : I) : (M ⊗[ℤ] M) →ₗ[ℤ] ℤ :=
  (Finsupp.lapply (i, j)).comp (b.tensorProduct b).repr.toLinearMap

@[simp] theorem tensorBasisCoordinate_basis (i j a c : I) :
    tensorBasisCoordinate b i j (b a ⊗ₜ[ℤ] b c) =
      if (a, c) = (i, j) then 1 else 0 := by
  change ((b.tensorProduct b).repr (b a ⊗ₜ[ℤ] b c)) (i, j) = _
  rw [← Module.Basis.tensorProduct_apply b b a c,
    Module.Basis.repr_self]
  simp [Finsupp.single_apply, Prod.ext_iff]

theorem tensorBasisCoordinate_orderedTensorNormal_of_le
    (i j : I) (hij : i ≤ j) :
    (tensorBasisCoordinate b i j).comp (orderedTensorNormal b) =
      (mvCoefficient (pairExponent i j)).comp
        (tensorCommutativePolynomial b) := by
  apply (b.tensorProduct b).ext
  rintro ⟨a, c⟩
  rw [Module.Basis.tensorProduct_apply]
  change tensorBasisCoordinate b i j
      (orderedTensorNormal b (b a ⊗ₜ[ℤ] b c)) =
    mvCoefficient (pairExponent i j)
      (tensorCommutativePolynomial b (b a ⊗ₜ[ℤ] b c))
  rw [orderedTensorNormal_tmul, orderedTensorBilinear_basis,
    tensorCommutativePolynomial_basis]
  by_cases hac : a ≤ c
  · rw [if_pos hac]
    rw [tensorBasisCoordinate_basis]
    change (if (a, c) = (i, j) then 1 else 0) =
      MvPolynomial.coeff (pairExponent i j)
        (MvPolynomial.X a * MvPolynomial.X c)
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
    change (if (a, c) = (i, j) then 1 else 0) =
      MvPolynomial.coeff (pairExponent i j)
        (MvPolynomial.monomial (pairExponent a c) 1)
    rw [MvPolynomial.coeff_monomial]
    rw [if_congr (by
      change (a, c) = (i, j) ↔
        pairExponent i j = pairExponent a c
      rw [pairExponent_eq_iff hij hac]
      constructor <;> aesop) rfl rfl]
    simp [eq_comm]
  · rw [if_neg hac]
    have hca : c ≤ a := le_of_not_ge hac
    rw [tensorBasisCoordinate_basis]
    change (if (c, a) = (i, j) then 1 else 0) =
      MvPolynomial.coeff (pairExponent i j)
        (MvPolynomial.X a * MvPolynomial.X c)
    rw [mul_comm]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
    change (if (c, a) = (i, j) then 1 else 0) =
      MvPolynomial.coeff (pairExponent i j)
        (MvPolynomial.monomial (pairExponent c a) 1)
    rw [MvPolynomial.coeff_monomial]
    rw [if_congr (by
      change (c, a) = (i, j) ↔
        pairExponent i j = pairExponent c a
      rw [pairExponent_eq_iff hij hca]
      constructor <;> aesop) rfl rfl]
    simp [eq_comm]

theorem tensorBasisCoordinate_orderedTensorNormal_of_not_le
    (i j : I) (hij : ¬i ≤ j) :
    (tensorBasisCoordinate b i j).comp (orderedTensorNormal b) = 0 := by
  apply (b.tensorProduct b).ext
  rintro ⟨a, c⟩
  rw [Module.Basis.tensorProduct_apply]
  change tensorBasisCoordinate b i j
      (orderedTensorNormal b (b a ⊗ₜ[ℤ] b c)) = 0
  rw [orderedTensorNormal_tmul, orderedTensorBilinear_basis]
  by_cases hac : a ≤ c
  · rw [if_pos hac, tensorBasisCoordinate_basis]
    rw [if_neg]
    rintro hpair
    have hai : a = i := congrArg Prod.fst hpair
    have hcj : c = j := congrArg Prod.snd hpair
    exact hij (hai ▸ hcj ▸ hac)
  · rw [if_neg hac, tensorBasisCoordinate_basis]
    have hca : c ≤ a := le_of_not_ge hac
    rw [if_neg]
    rintro hpair
    have hci : c = i := congrArg Prod.fst hpair
    have haj : a = j := congrArg Prod.snd hpair
    exact hij (hci ▸ haj ▸ hca)

/-- Commutative quadratic coordinates detect exactly the ordered tensor normal form. -/
theorem orderedTensorNormal_eq_zero_of_tensorCommutativePolynomial_eq_zero
    (t : M ⊗[ℤ] M) (ht : tensorCommutativePolynomial b t = 0) :
    orderedTensorNormal b t = 0 := by
  apply (b.tensorProduct b).repr.injective
  ext ij
  rcases ij with ⟨i, j⟩
  change tensorBasisCoordinate b i j (orderedTensorNormal b t) = 0
  by_cases hij : i ≤ j
  · have hmaps := LinearMap.congr_fun
      (tensorBasisCoordinate_orderedTensorNormal_of_le b i j hij) t
    change tensorBasisCoordinate b i j (orderedTensorNormal b t) =
      MvPolynomial.coeff (pairExponent i j)
        (tensorCommutativePolynomial b t) at hmaps
    rw [hmaps, ht]
    rfl
  · have hmaps := LinearMap.congr_fun
      (tensorBasisCoordinate_orderedTensorNormal_of_not_le b i j hij) t
    simpa using hmaps
end
end LieRings.DegreeFive
