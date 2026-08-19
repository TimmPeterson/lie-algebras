import LieRings.DimensionSubring.MetabelianOdd.WeightedPresentation
import LieRings.DimensionSubring.DegreeFive.CoordinatePBW
import Mathlib.RingTheory.MvPolynomial.Homogeneous

#check MvPolynomial.eval₂Hom
#check MvPolynomial.homogeneousComponent
#check RingHom.toLinearMap
#check AddMonoidHom.toIntLinearMap
#check RingHom.toAddMonoidHom
#check AlgHom.toLinearMap
#check MvPolynomial.coeff
#check MvPolynomial.coeffAddMonoidHom
#check MvPolynomial.coeffHom
#check LinearMap.comp
#check LinearMap.mul
#check Module.Basis.prod_repr
#check Module.Basis.repr_self
#check Module.Basis.sum_repr
#check MvPolynomial.coeff_mul
#check Finsupp.single_add_hom
#check List.sum_mul
#check List.mul_sum
#check List.sum_map_add
#check List.sum_map_neg
#check List.sum_map_smul
#check map_list_sum
#check List.sum_hom
#check List.map_sum
#check DistribMulAction.toAddMonoidHom
#check AddMonoidHom.mulLeft
#check Int.mulLeft

private def linPoly {I M : Type*} [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) (x : M) : MvPolynomial I ℤ :=
  (b.repr x).sum fun i c ↦ c • MvPolynomial.X i

example {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module ℤ M]
    (b : Module.Basis I ℤ M) (x y : M) (i j : I) :
    MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (linPoly b x * linPoly b y) =
      if i = j then b.repr x i * b.repr y i
      else b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
  classical
  unfold linPoly
  rw [Finsupp.sum_mul, map_finsuppSum]
  simp only [smul_eq_mul, mul_assoc]
  rw [Finsupp.mul_sum, map_finsuppSum]
  simp only [mul_smul_comm, smul_eq_mul, map_smul]
  by_cases hij : i = j
  · subst j
    simp [MvPolynomial.coeff_X_mul_X, Finsupp.single_add]
  · simp [MvPolynomial.coeff_X_mul_X, hij, Finsupp.single_apply]

example {I : Type*} [LinearOrder I] (i j : I) :
    MvPolynomial.X i * (MvPolynomial.X j : MvPolynomial I ℤ) =
      MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
  simp [MvPolynomial.X, MvPolynomial.monomial_mul]

example {I : Type*} [LinearOrder I] (i j : I) :
    Multiset.toFinsupp (([i, j] : List I) : Multiset I) =
      Finsupp.single i 1 + Finsupp.single j 1 := by
  ext k
  simp [Finsupp.single_apply, eq_comm, add_comm]
