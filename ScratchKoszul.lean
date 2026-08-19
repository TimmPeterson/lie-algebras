import LieRings.Homological.Koszul
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex

open TensorProduct

#check AlternatingMap.alternatizeUncurryFin
#check AlternatingMap.alternatizeUncurryFin_apply
#check AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
#check exteriorPower.alternatingMapLinearEquiv
#check exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
#check LinearMap.compAlternatingMap
#check AlternatingMap.compLinearMap
#check TensorProduct.map
#check ModuleCat.ofHom
#check ChainComplex.of
#check LinearEquiv.ofBijective
#check Submodule.mapQ
#check Submodule.liftQ
#check TensorProduct.tmul_smul
#check TensorProduct.smul_tmul'
#check TensorProduct.smul_tmul
#check tmul_smul
#check TensorProduct.CompatibleSMul.int

namespace Scratch

universe u v
noncomputable section

variable {Rel : Type u} {Gen : Type v} [AddCommGroup Rel] [AddCommGroup Gen]

private def wedgeTensorInsert (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) (a : Rel) :
    (⋀[ℤ]^n Rel) →ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) where
  toFun w := (TensorProduct.mk ℤ _ _ w).comp (SymmetricPower.insert ℤ Gen q (d a))
  map_add' x y := by
    ext s
    change (x + y) ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s =
      x ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s +
        y ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s
    exact add_tmul x y _
  map_smul' r x := by
    ext s
    change (r • x) ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s =
      r • (x ⊗ₜ[ℤ] SymmetricPower.insert ℤ Gen q (d a) s)
    exact smul_tmul' r x _

private def tail (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    Rel →ₗ[ℤ] Rel [⋀^Fin n]→ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) where
  toFun a := (wedgeTensorInsert d n q a).compAlternatingMap (exteriorPower.ιMulti ℤ n)
  map_add' a b := by
    ext v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen q (d (a + b)) s =
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d a) s +
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d b) s
    rw [map_add, SymmetricPower.insert_add_apply, tmul_add]
  map_smul' r a := by
    letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^n Rel)
        (Sym[ℤ] (Fin (q + 1)) Gen) := TensorProduct.CompatibleSMul.int
    ext v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen q (d (r • a)) s =
      r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen q (d a) s)
    rw [map_smul, SymmetricPower.insert_smul_apply]
    calc
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          (r • SymmetricPower.insert ℤ Gen q (d a) s) =
          (r • exteriorPower.ιMulti ℤ n v) ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ Gen q (d a) s :=
        (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) r _ _).symm
      _ = r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d a) s) :=
        (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) r _ _).symm

private def differentialAlternating (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    Rel [⋀^Fin (n + 1)]→ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) :=
  ((-1 : ℤ) ^ n) • AlternatingMap.alternatizeUncurryFin (tail d n q)

private def differentialCore (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    (⋀[ℤ]^(n + 1) Rel) →ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) :=
  exteriorPower.alternatingMapLinearEquiv (differentialAlternating d n q)

def differential (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    ((⋀[ℤ]^(n + 1) Rel) ⊗[ℤ] Sym[ℤ] (Fin q) Gen) →ₗ[ℤ]
      ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) :=
  (TensorProduct.lift (differentialCore d n q)).toAddMonoidHom.toIntLinearMap

private theorem neg_one_pow_mul_neg_one_pow (n : ℕ) (j : Fin (n + 1)) :
    ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ j.val) = (-1 : ℤ) ^ (n - j.val) := by
  have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  rw [← pow_add]
  rw [show n + j.val = (n - j.val) + 2 * j.val by omega, pow_add]
  have heven : (-1 : ℤ) ^ (2 * j.val) = 1 :=
    Even.neg_one_pow ⟨j.val, by omega⟩
  rw [heven, mul_one]

@[simp]
theorem differential_wedge_tmul (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 1) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    differential d n q (exteriorPower.ιMulti ℤ (n + 1) a ⊗ₜ[ℤ] s) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (n - j.val)) •
        (exteriorPower.ιMulti ℤ n (j.removeNth a) ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen q (d (a j)) s) := by
  change differentialCore d n q (exteriorPower.ιMulti ℤ (n + 1) a) s = _
  have h := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (differentialAlternating d n q) a
  calc
    differentialCore d n q (exteriorPower.ιMulti ℤ (n + 1) a) s =
        differentialAlternating d n q a s := by
      exact DFunLike.congr_fun h s
    _ = _ := by
      simp only [differentialAlternating, AlternatingMap.smul_apply,
        AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum, smul_smul,
        tail, wedgeTensorInsert, neg_one_pow_mul_neg_one_pow]
      let ev :
          (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
            ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen)) →ₗ[ℤ]
              ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) Gen) := {
        toFun f := f s
        map_add' f g := rfl
        map_smul' r f := rfl }
      change ev (∑ x : Fin (n + 1),
          ((-1 : ℤ) ^ (n - x.val)) • (tail d n q (a x)) (x.removeNth a)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rfl

private def wedgeTensorDouble (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) (a b : Rel) :
    (⋀[ℤ]^n Rel) →ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) where
  toFun w := (TensorProduct.mk ℤ _ _ w).comp
    ((SymmetricPower.insert ℤ Gen (q + 1) (d b)).comp
      (SymmetricPower.insert ℤ Gen q (d a)))
  map_add' x y := by
    ext s
    change (x + y) ⊗ₜ[ℤ] _ = x ⊗ₜ[ℤ] _ + y ⊗ₜ[ℤ] _
    exact add_tmul x y _
  map_smul' r x := by
    ext s
    change (r • x) ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d b)
          (SymmetricPower.insert ℤ Gen q (d a) s) =
      r • (x ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d b)
          (SymmetricPower.insert ℤ Gen q (d a) s))
    exact smul_tmul' r x _

set_option maxHeartbeats 800000 in
private def doubleTail (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    Rel →ₗ[ℤ] Rel →ₗ[ℤ] Rel [⋀^Fin n]→ₗ[ℤ]
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) where
  toFun a := {
    toFun := fun b ↦ (wedgeTensorDouble d n q a b).compAlternatingMap
      (exteriorPower.ιMulti ℤ n)
    map_add' := by
      intro b c
      ext v s
      change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d (b + c))
            (SymmetricPower.insert ℤ Gen q (d a) s) =
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ Gen (q + 1) (d b)
              (SymmetricPower.insert ℤ Gen q (d a) s) +
          exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
            SymmetricPower.insert ℤ Gen (q + 1) (d c)
              (SymmetricPower.insert ℤ Gen q (d a) s)
      rw [map_add, SymmetricPower.insert_add_apply, tmul_add]
    map_smul' := by
      intro r b
      letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^n Rel)
          (Sym[ℤ] (Fin (q + 2)) Gen) := TensorProduct.CompatibleSMul.int
      ext v s
      change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d (r • b))
            (SymmetricPower.insert ℤ Gen q (d a) s) = _
      rw [map_smul, SymmetricPower.insert_smul_apply]
      calc
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
            (r • SymmetricPower.insert ℤ Gen (q + 1) (d b)
              (SymmetricPower.insert ℤ Gen q (d a) s)) =
            (r • exteriorPower.ιMulti ℤ n v) ⊗ₜ[ℤ] _ :=
          (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) r _ _).symm
        _ = r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ] _) :=
          (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) r _ _).symm }
  map_add' := by
    intro a b
    ext c v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d c)
          (SymmetricPower.insert ℤ Gen q (d (a + b)) s) =
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d c)
            (SymmetricPower.insert ℤ Gen q (d a) s) +
        exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ Gen (q + 1) (d c)
            (SymmetricPower.insert ℤ Gen q (d b) s)
    rw [map_add, SymmetricPower.insert_add_apply, map_add, tmul_add]
  map_smul' := by
    intro r a
    letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^n Rel)
        (Sym[ℤ] (Fin (q + 2)) Gen) := TensorProduct.CompatibleSMul.int
    ext b v s
    change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d b)
          (SymmetricPower.insert ℤ Gen q (d (r • a)) s) = _
    rw [map_smul, SymmetricPower.insert_smul_apply, map_smul]
    calc
      exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
          (r • SymmetricPower.insert ℤ Gen (q + 1) (d b)
            (SymmetricPower.insert ℤ Gen q (d a) s)) =
          (r • exteriorPower.ιMulti ℤ n v) ⊗ₜ[ℤ] _ :=
        (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) r _ _).symm
      _ = r • (exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ] _) :=
        (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) r _ _).symm

private theorem doubleTail_symmetric (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) (a b : Rel) :
    doubleTail d n q a b = doubleTail d n q b a := by
  ext v s
  change exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
      SymmetricPower.insert ℤ Gen (q + 1) (d b)
        (SymmetricPower.insert ℤ Gen q (d a) s) =
    exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ]
      SymmetricPower.insert ℤ Gen (q + 1) (d a)
        (SymmetricPower.insert ℤ Gen q (d b) s)
  apply congrArg (fun z ↦ exteriorPower.ιMulti ℤ n v ⊗ₜ[ℤ] z)
  exact LinearMap.congr_fun (SymmetricPower.insert_comm ℤ Gen q (d b) (d a)) s

private theorem doubleAlternating_zero (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    AlternatingMap.alternatizeUncurryFin
      (AlternatingMap.alternatizeUncurryFinLM ∘ₗ doubleTail d n q) = 0 :=
  AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    (doubleTail_symmetric d n q)

private def doubleSum (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) •
      (exteriorPower.ιMulti ℤ n (j.removeNth (i.removeNth a)) ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d ((i.removeNth a) j))
          (SymmetricPower.insert ℤ Gen q (d (a i)) s))

private theorem doubleSum_zero (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    doubleSum d n q a s = 0 := by
  have h := DFunLike.congr_fun (doubleAlternating_zero d n q) a
  have hs := DFunLike.congr_fun h s
  simp only [AlternatingMap.alternatizeUncurryFin_apply,
    LinearMap.coe_comp, Function.comp_apply,
    AlternatingMap.alternatizeUncurryFinLM_apply] at hs
  let ev :
      (Sym[ℤ] (Fin q) Gen →ₗ[ℤ]
        ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen)) →ₗ[ℤ]
          ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) := {
    toFun f := f s
    map_add' f g := rfl
    map_smul' r f := rfl }
  change ev (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) •
        (doubleTail d n q (a i) ((i.removeNth a) j))
          (j.removeNth (i.removeNth a))) = ev 0 at hs
  simp only [map_sum, map_smul, map_zero, doubleTail, wedgeTensorDouble] at hs
  exact hs

private def reverseDoubleSum (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    (⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (n + 1 - i.val)) •
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (n - j.val)) •
      (exteriorPower.ιMulti ℤ n (j.removeNth (i.removeNth a)) ⊗ₜ[ℤ]
        SymmetricPower.insert ℤ Gen (q + 1) (d ((i.removeNth a) j))
          (SymmetricPower.insert ℤ Gen q (d (a i)) s))

private def intScalarEnd {T : Type*} [AddCommGroup T] (c : ℤ) : T →ₗ[ℤ] T :=
  c • LinearMap.id

@[simp]
private theorem intScalarEnd_apply {T : Type*} [AddCommGroup T] (c : ℤ) (x : T) :
    intScalarEnd c x = c • x := rfl

private theorem int_smul_fintype_sum {T I : Type*} [AddCommGroup T] [Fintype I]
    (c : ℤ) (f : I → T) :
    c • (∑ i, f i) = ∑ i, c • f i := by
  change intScalarEnd c (∑ i, f i) = _
  rw [map_sum]
  rfl

private theorem reverseSignedSum_eq {T : Type*} [AddCommGroup T] (n : ℕ)
    (f : Fin (n + 1) → T) :
    (∑ i, ((-1 : ℤ) ^ (n - i.val)) • f i) =
      ((-1 : ℤ) ^ n) • ∑ i, ((-1 : ℤ) ^ i.val) • f i := by
  rw [int_smul_fintype_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, neg_one_pow_mul_neg_one_pow]

private theorem reverseDoubleSum_eq (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    reverseDoubleSum d n q a s =
      (((-1 : ℤ) ^ (n + 1)) * ((-1 : ℤ) ^ n)) • doubleSum d n q a s := by
  unfold reverseDoubleSum doubleSum
  rw [reverseSignedSum_eq (n + 1)]
  simp_rw [reverseSignedSum_eq n]
  let g : Fin (n + 2) → Fin (n + 1) →
      ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) := fun i j ↦
    exteriorPower.ιMulti ℤ n (j.removeNth (i.removeNth a)) ⊗ₜ[ℤ]
      SymmetricPower.insert ℤ Gen (q + 1) (d ((i.removeNth a) j))
        (SymmetricPower.insert ℤ Gen q (d (a i)) s)
  change ((-1 : ℤ) ^ (n + 1)) •
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (((-1 : ℤ) ^ n) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j) =
    (((-1 : ℤ) ^ (n + 1)) * ((-1 : ℤ) ^ n)) •
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j
  have hinside :
      (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (((-1 : ℤ) ^ n) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j)) =
      ((-1 : ℤ) ^ n) •
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j := by
    calc
      _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ n) •
          (((-1 : ℤ) ^ i.val) •
            ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [smul_smul]
        congr 1
        ring
      _ = _ := (int_smul_fintype_sum ((-1 : ℤ) ^ n)
        (fun i : Fin (n + 2) ↦ ((-1 : ℤ) ^ i.val) •
          ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • g i j)).symm
  rw [hinside, smul_smul]

private theorem reverseDoubleSum_zero (d : Rel →ₗ[ℤ] Gen) (n q : ℕ)
    (a : Fin (n + 2) → Rel) (s : Sym[ℤ] (Fin q) Gen) :
    reverseDoubleSum d n q a s = 0 := by
  rw [reverseDoubleSum_eq, doubleSum_zero]
  exact smul_zero _

theorem differential_comp_differential (d : Rel →ₗ[ℤ] Gen) (n q : ℕ) :
    (differential d n (q + 1)).comp (differential d (n + 1) q) = 0 := by
  apply TensorProduct.ext'
  intro w s
  let F : (⋀[ℤ]^(n + 2) Rel) →ₗ[ℤ]
      ((⋀[ℤ]^n Rel) ⊗[ℤ] Sym[ℤ] (Fin (q + 2)) Gen) :=
    ((differential d n (q + 1)).comp (differential d (n + 1) q)).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^(n + 2) Rel) _).flip s)
  have hF : F = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change differential d n (q + 1)
      (differential d (n + 1) q
        (exteriorPower.ιMulti ℤ (n + 2) a ⊗ₜ[ℤ] s)) = 0
    rw [differential_wedge_tmul, map_sum]
    simp only [map_smul, differential_wedge_tmul, Finset.smul_sum, smul_smul]
    exact reverseDoubleSum_zero d n q a s
  have hw := LinearMap.congr_fun hF w
  simpa [F, LinearMap.comp_apply] using hw

end
end Scratch
