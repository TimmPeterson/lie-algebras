import LieRings.Homological.SymmetricPower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

open TensorProduct

namespace SymmetricPower

universe v
noncomputable section

variable {R : Type} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private def emptyFun : Fin 0 → M := fun i => nomatch i

def degreeOne : M →ₗ[R] Sym[R] (Fin 1) M where
  toFun x := tprod R (Fin.cons x emptyFun)
  map_add' x y := by
    exact (tprod R).cons_add emptyFun x y
  map_smul' r x := by
    exact (tprod R).cons_smul emptyFun r x

@[simp] theorem degreeOne_apply (x : M) :
    degreeOne (R := R) x = tprod R (Fin.cons x emptyFun) := rfl

private def tensorToSymTwoBilinear : M →ₗ[R] M →ₗ[R] Sym[R] (Fin 2) M where
  toFun x := (insert R M 1 x).comp degreeOne
  map_add' x y := by
    ext z
    simp only [LinearMap.add_apply, LinearMap.comp_apply, degreeOne_apply,
      insert_tprod]
    exact (tprod R).cons_add (Fin.cons z emptyFun) x y
  map_smul' r x := by
    ext z
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, degreeOne_apply,
      insert_tprod, RingHom.id_apply]
    exact (tprod R).cons_smul (Fin.cons z emptyFun) r x

def tensorToSymTwo : M ⊗[R] M →ₗ[R] Sym[R] (Fin 2) M :=
  TensorProduct.lift tensorToSymTwoBilinear

@[simp] theorem tensorToSymTwo_tmul (x y : M) :
    tensorToSymTwo (R := R) (x ⊗ₜ[R] y) =
      tprod R (Fin.cons x (Fin.cons y emptyFun)) := by
  rw [tensorToSymTwo, TensorProduct.lift.tmul]
  change insert R M 1 x (degreeOne (R := R) y) = _
  rw [degreeOne_apply, insert_tprod]

private def antisymTail : M →ₗ[R] M [⋀^Fin 1]→ₗ[R] M ⊗[R] M where
  toFun x := AlternatingMap.ofSubsingleton R M (M ⊗[R] M) 0
    (TensorProduct.mk R M M x)
  map_add' x y := by ext v; simp [add_tmul]
  map_smul' r x := by ext v; simp [smul_tmul']

private def antisymAlternating : M [⋀^Fin 2]→ₗ[R] M ⊗[R] M :=
  AlternatingMap.alternatizeUncurryFin antisymTail

def exteriorTwoToTensor : (⋀[R]^2 M) →ₗ[R] M ⊗[R] M :=
  exteriorPower.alternatingMapLinearEquiv
    (antisymAlternating (R := R) (M := M))

@[simp] theorem exteriorTwoToTensor_ιMulti (x : Fin 2 → M) :
    exteriorTwoToTensor (R := R) (exteriorPower.ιMulti R 2 x) =
      x 0 ⊗ₜ[R] x 1 - x 1 ⊗ₜ[R] x 0 := by
  change (exteriorPower.alternatingMapLinearEquiv
    (antisymAlternating (R := R) (M := M)))
      (exteriorPower.ιMulti R 2 x) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simp [antisymAlternating, AlternatingMap.alternatizeUncurryFin_apply,
    antisymTail]
  change x 0 ⊗ₜ[R] x 1 + -(x 1 ⊗ₜ[R] x 0) = _
  abel

theorem tensorToSymTwo_comp_exteriorTwoToTensor :
    (tensorToSymTwo (R := R) (M := M)).comp
      (exteriorTwoToTensor (R := R) (M := M)) = 0 := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R 2 M)
  rintro _ ⟨x, rfl⟩
  simp only [LinearMap.comp_apply, exteriorTwoToTensor_ιMulti, map_sub,
    tensorToSymTwo_tmul]
  rw [show tprod R (Fin.cons (x 0) (Fin.cons (x 1) emptyFun)) =
      tprod R (Fin.cons (x 1) (Fin.cons (x 0) emptyFun)) by
    let p : Equiv.Perm (Fin 2) := Equiv.swap 0 1
    have hp : Fin.cons (x 0) (Fin.cons (x 1) emptyFun) =
        Fin.cons (x 1) (Fin.cons (x 0) emptyFun) ∘ p := by
      funext i
      fin_cases i <;> rfl
    rw [hp]
    exact tprod_equiv (R := R) (M := M) p _]
  exact sub_self _

section Exact

variable {κ : Type} [Finite κ] [LinearOrder κ]

private def pairFun (i j : κ) : Fin 2 → κ :=
  Fin.cons i (Fin.cons j emptyFun)

private theorem symIndex_pair_eq_iff (i j k l : κ) :
    symIndexOfFun 2 (pairFun i j) = symIndexOfFun 2 (pairFun k l) ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := exists_perm_of_symIndexOfFun_eq 2 (pairFun i j) (pairFun k l) h
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    by_cases he0 : e 0 = 0
    · left
      constructor
      · simpa [pairFun, he0] using h0
      · have he1 : e 1 = 1 := by
          apply Fin.eq_one_of_ne_zero (e 1)
          intro hz
          have hz' : (0 : Fin 2) = 1 := e.injective (he0.trans hz.symm)
          omega
        simpa [pairFun, he1] using h1
    · have he0' : e 0 = 1 := Fin.eq_one_of_ne_zero (e 0) he0
      right
      constructor
      · simpa [pairFun, he0'] using h0
      · have he1 : e 1 = 0 := by
          by_contra hz
          have he1' : e 1 = 1 := Fin.eq_one_of_ne_zero (e 1) hz
          have hz' : (0 : Fin 2) = 1 := e.injective (he0'.trans he1'.symm)
          omega
        simpa [pairFun, he1] using h1
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simpa [pairFun, Function.comp_def] using
        (symIndexOfFun_perm 2 (Equiv.swap 0 1) (pairFun j i))

private def orderedWedge (b : Module.Basis κ R M) (ij : κ × κ) :
    ⋀[R]^2 M :=
  if hij : ij.1 < ij.2 then
    exteriorPower.ιMulti R 2 (Fin.cons (b ij.1) (Fin.cons (b ij.2) emptyFun))
  else 0

def exteriorTwoLeftInverse (b : Module.Basis κ R M) :
    M ⊗[R] M →ₗ[R] ⋀[R]^2 M :=
  ((b.tensorProduct b).constr R) (orderedWedge b)

@[simp] private theorem exteriorTwoLeftInverse_basis_tmul
    (b : Module.Basis κ R M) (i j : κ) :
    exteriorTwoLeftInverse b (b i ⊗ₜ[R] b j) =
      if hij : i < j then
        exteriorPower.ιMulti R 2
          (Fin.cons (b i) (Fin.cons (b j) emptyFun))
      else 0 := by
  rw [← Module.Basis.tensorProduct_apply' b b (i, j)]
  rw [exteriorTwoLeftInverse, Module.Basis.constr_basis]
  rfl

theorem exteriorTwoLeftInverse_comp (b : Module.Basis κ R M) :
    (exteriorTwoLeftInverse b).comp
      (exteriorTwoToTensor (R := R) (M := M)) = LinearMap.id := by
  apply (b.exteriorPower 2).ext
  intro s
  rw [exteriorPower.basis_apply]
  let p : Fin 2 → κ := s.val.orderEmbOfFin s.property
  change exteriorTwoLeftInverse b
    (exteriorTwoToTensor (R := R) (M := M)
      (exteriorPower.ιMulti R 2 (b ∘ p))) = _
  rw [exteriorTwoToTensor_ιMulti, map_sub,
    show (b ∘ p) 0 = b (p 0) by rfl,
    show (b ∘ p) 1 = b (p 1) by rfl,
    exteriorTwoLeftInverse_basis_tmul, exteriorTwoLeftInverse_basis_tmul]
  have hp : p 0 < p 1 := by
    exact s.val.orderEmbOfFin s.property |>.strictMono (by decide)
  simp only [hp, ↓reduceDIte, LinearMap.id_apply]
  have hnp : ¬p 1 < p 0 := not_lt_of_ge hp.le
  simp only [hnp, ↓reduceDIte, sub_zero]
  rfl

theorem exteriorTwoToTensor_injective (b : Module.Basis κ R M) :
    Function.Injective (exteriorTwoToTensor (R := R) (M := M)) := by
  intro x y hxy
  have := congrArg (exteriorTwoLeftInverse b) hxy
  simpa [← LinearMap.comp_apply, exteriorTwoLeftInverse_comp b] using this

private def tensorCoord (b : Module.Basis κ R M) (i j : κ) :
    M ⊗[R] M →ₗ[R] R :=
  (b.tensorProduct b).coord (i, j)

private def symCoord (b : Module.Basis κ R M) (i j : κ) :
    Sym[R] (Fin 2) M →ₗ[R] R :=
  (monomialBasis b 2).coord (symIndexOfFun 2 (pairFun i j))

private theorem symCoord_tensor_basis (b : Module.Basis κ R M)
    (i j k l : κ) :
    symCoord b i j (tensorToSymTwo (R := R) (b k ⊗ₜ[R] b l)) =
      if symIndexOfFun 2 (pairFun k l) = symIndexOfFun 2 (pairFun i j)
      then 1 else 0 := by
  rw [tensorToSymTwo_tmul]
  rw [symCoord, Module.Basis.coord_apply, monomialBasis,
    Module.Basis.map_repr]
  simp only [LinearEquiv.symm_symm, Finsupp.basisSingleOne_repr,
    LinearEquiv.trans_apply, LinearEquiv.refl_apply]
  change (monomialRepr b 2
    (tprod R (Fin.cons (b k) (Fin.cons (b l) emptyFun))))
      (symIndexOfFun 2 (pairFun i j)) = _
  rw [show Fin.cons (b k) (Fin.cons (b l) emptyFun) = b ∘ pairFun k l by
    funext x
    fin_cases x <;> rfl]
  rw [monomialRepr_tprod_basis]
  by_cases h : symIndexOfFun 2 (pairFun k l) =
      symIndexOfFun 2 (pairFun i j)
  · rw [if_pos h]
    rw [← h]
    exact Finsupp.single_eq_same (M := R)
  · rw [if_neg h]
    exact Finsupp.single_eq_of_ne (M := R) (fun h' => h h'.symm)

private theorem offDiagonal_coord_identity (b : Module.Basis κ R M)
    (i j : κ) (hij : i < j) :
    (symCoord b i j).comp (tensorToSymTwo (R := R) (M := M)) =
      tensorCoord b i j + tensorCoord b j i := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, symCoord_tensor_basis,
    LinearMap.add_apply, tensorCoord, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp only [symIndex_pair_eq_iff]
  rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
    exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hki : k = i <;> by_cases hlj : l = j <;>
    by_cases hkj : k = j <;> by_cases hli : l = i <;>
    simp [hki, hlj, hkj, hli, hij.ne, hij.ne']

private theorem diagonal_coord_identity (b : Module.Basis κ R M) (i : κ) :
    (symCoord b i i).comp (tensorToSymTwo (R := R) (M := M)) =
      tensorCoord b i i := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, symCoord_tensor_basis, tensorCoord,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [symIndex_pair_eq_iff]
  rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
    exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hki : k = i <;> by_cases hli : l = i <;> simp [hki, hli]

private def tensorNormalization (b : Module.Basis κ R M) :
    M ⊗[R] M →ₗ[R] M ⊗[R] M :=
  (exteriorTwoToTensor (R := R) (M := M)).comp (exteriorTwoLeftInverse b)

@[simp] private theorem tensorNormalization_basis_tmul
    (b : Module.Basis κ R M) (i j : κ) :
    tensorNormalization b (b i ⊗ₜ[R] b j) =
      if hij : i < j then b i ⊗ₜ[R] b j - b j ⊗ₜ[R] b i else 0 := by
  rw [tensorNormalization, LinearMap.comp_apply, exteriorTwoLeftInverse_basis_tmul]
  split_ifs with hij
  · rw [exteriorTwoToTensor_ιMulti]
    rfl
  · rw [map_zero]

private theorem tensorNormalization_coord_lt (b : Module.Basis κ R M)
    (i j : κ) (hij : i < j) :
    (tensorCoord b i j).comp (tensorNormalization b) = tensorCoord b i j := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, tensorNormalization_basis_tmul]
  split_ifs with hkl
  · simp only [tensorCoord, Module.Basis.coord_apply, map_sub]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm,
      show b l ⊗ₜ[R] b k = (b.tensorProduct b) (l, k) by
      exact (Module.Basis.tensorProduct_apply' b b (l, k)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hlj : l = j <;>
      by_cases hli : l = i <;> by_cases hkj : k = j <;>
      simp [hki, hlj, hli, hkj] <;> order
  · simp only [tensorCoord, Module.Basis.coord_apply, map_zero]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hlj : l = j <;>
      simp [hki, hlj] <;> order

private theorem tensorNormalization_coord_gt (b : Module.Basis κ R M)
    (i j : κ) (hji : j < i) :
    (tensorCoord b i j).comp (tensorNormalization b) =
      -(tensorCoord b j i) := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, tensorNormalization_basis_tmul]
  split_ifs with hkl
  · simp only [tensorCoord, Module.Basis.coord_apply, map_sub,
      LinearMap.neg_apply]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm,
      show b l ⊗ₜ[R] b k = (b.tensorProduct b) (l, k) by
      exact (Module.Basis.tensorProduct_apply' b b (l, k)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hlj : l = j <;>
      by_cases hli : l = i <;> by_cases hkj : k = j <;>
      simp [hki, hlj, hli, hkj] <;> order
  · simp only [tensorCoord, Module.Basis.coord_apply, map_zero,
      LinearMap.neg_apply]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hkj : k = j <;> by_cases hli : l = i <;>
      simp [hkj, hli] <;> order

private theorem tensorNormalization_coord_diag (b : Module.Basis κ R M) (i : κ) :
    (tensorCoord b i i).comp (tensorNormalization b) = 0 := by
  apply (b.tensorProduct b).ext
  rintro ⟨k, l⟩
  rw [Module.Basis.tensorProduct_apply']
  simp only [LinearMap.comp_apply, tensorNormalization_basis_tmul]
  split_ifs with hkl
  · simp only [tensorCoord, Module.Basis.coord_apply, map_sub]
    rw [show b k ⊗ₜ[R] b l = (b.tensorProduct b) (k, l) by
      exact (Module.Basis.tensorProduct_apply' b b (k, l)).symm,
      show b l ⊗ₜ[R] b k = (b.tensorProduct b) (l, k) by
      exact (Module.Basis.tensorProduct_apply' b b (l, k)).symm]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hki : k = i <;> by_cases hli : l = i <;>
      simp [hki, hli] <;> order
  · simp

private theorem tensorNormalization_eq_of_mem_ker (b : Module.Basis κ R M)
    (x : M ⊗[R] M) (hx : x ∈ LinearMap.ker (tensorToSymTwo (R := R) (M := M))) :
    tensorNormalization b x = x := by
  have hx0 : tensorToSymTwo (R := R) (M := M) x = 0 := hx
  have hoff (i j : κ) (hij : i < j) :
      tensorCoord b i j x + tensorCoord b j i x = 0 := by
    have h := LinearMap.congr_fun (offDiagonal_coord_identity b i j hij) x
    rw [LinearMap.comp_apply, hx0, map_zero] at h
    exact h.symm
  have hdiag (i : κ) : tensorCoord b i i x = 0 := by
    have h := LinearMap.congr_fun (diagonal_coord_identity b i) x
    rw [LinearMap.comp_apply, hx0, map_zero] at h
    exact h.symm
  apply (b.tensorProduct b).repr.injective
  ext ij
  rcases ij with ⟨i, j⟩
  change tensorCoord b i j (tensorNormalization b x) = tensorCoord b i j x
  rcases lt_trichotomy i j with hij | hij | hij
  · have h := LinearMap.congr_fun (tensorNormalization_coord_lt b i j hij) x
    exact h
  · subst j
    have h := LinearMap.congr_fun (tensorNormalization_coord_diag b i) x
    rw [LinearMap.comp_apply] at h
    have h' : tensorCoord b i i (tensorNormalization b x) = 0 := by
      simpa using h
    rw [h', hdiag]
  · have h := LinearMap.congr_fun (tensorNormalization_coord_gt b i j hij) x
    rw [LinearMap.comp_apply, LinearMap.neg_apply] at h
    rw [h]
    have hs := hoff j i hij
    exact neg_eq_of_add_eq_zero_right hs

theorem exteriorTwoToTensor_range_eq_ker (b : Module.Basis κ R M) :
    LinearMap.range (exteriorTwoToTensor (R := R) (M := M)) =
      LinearMap.ker (tensorToSymTwo (R := R) (M := M)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change tensorToSymTwo (R := R) (M := M)
      (exteriorTwoToTensor (R := R) (M := M) y) = 0
    exact LinearMap.congr_fun tensorToSymTwo_comp_exteriorTwoToTensor y
  · intro hx
    refine ⟨exteriorTwoLeftInverse b x, ?_⟩
    exact tensorNormalization_eq_of_mem_ker b x hx

end Exact

end
end SymmetricPower
