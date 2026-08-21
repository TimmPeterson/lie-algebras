import LieRings.Metabelian.FreeNilpotent
import Mathlib.LinearAlgebra.Multilinear.Curry

open TensorProduct

namespace FreeMetabelian.Evaluation

universe u w
noncomputable section

variable {X : Type u} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable {L : Type w} [LieRing L]
variable {c : ℕ}

abbrev Derived (L : Type w) [LieRing L] := LieAlgebra.derivedSeries ℤ L 1

def rightAction (f : X →ₗ[ℤ] L) (x : X) : Module.End ℤ (Derived L) where
  toFun d := ⟨⁅d.1, f x⁆, by
    rw [← lie_skew]
    exact (LieAlgebra.derivedSeries ℤ L 1).neg_mem
      ((LieAlgebra.derivedSeries ℤ L 1).lie_mem d.property)⟩
  map_add' a b := by
    apply Subtype.ext
    exact add_lie a.1 b.1 (f x)
  map_smul' z a := by
    apply Subtype.ext
    exact zsmul_lie a.1 (f x) z

def rightActionLinear (f : X →ₗ[ℤ] L) : X →ₗ[ℤ] Module.End ℤ (Derived L) where
  toFun := rightAction f
  map_add' x y := by
    ext d
    change ⁅d.1, f (x + y)⁆ = ⁅d.1, f x⁆ + ⁅d.1, f y⁆
    rw [map_add]
    exact lie_add d.1 (f x) (f y)
  map_smul' z x := by
    ext d
    change ⁅d.1, f (z • x)⁆ = z • ⁅d.1, f x⁆
    rw [map_zsmul]
    exact lie_zsmul d.1 (f x) z

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem rightAction_commute (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (x y : X) :
    Commute (rightAction f x) (rightAction f y) := by
  rw [Commute]
  ext d
  change ⁅⁅d.1, f y⁆, f x⁆ = ⁅⁅d.1, f x⁆, f y⁆
  have hxy : ⁅f x, f y⁆ ∈ LieAlgebra.derivedSeries ℤ L 1 := by
    change ⁅f x, f y⁆ ∈ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆
    exact LieSubmodule.lie_mem_lie (by simp) (by simp)
  have hz : ⁅d.1, ⁅f x, f y⁆⁆ = 0 := hmeta.bracket_eq_zero d.property hxy
  have hj := leibniz_lie d.1 (f x) (f y)
  have hs : ⁅f x, ⁅d.1, f y⁆⁆ = -⁅⁅d.1, f y⁆, f x⁆ := by
    exact (lie_skew (f x) ⁅d.1, f y⁆).symm
  rw [hz, hs] at hj
  apply Eq.symm
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg]
  exact hj.symm

def actionMultilinear (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) :
    MultilinearMap ℤ (fun _ : Fin q ↦ X) (Module.End ℤ (Derived L)) :=
  (MultilinearMap.mkPiAlgebraFin ℤ q (Module.End ℤ (Derived L))).compLinearMap
    (fun _ ↦ rightActionLinear f)

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem actionMultilinear_symmetric (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) :
    SymmetricPower.IsSymmetric (actionMultilinear hmeta f q) := by
  intro e x
  simp only [actionMultilinear, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebraFin_apply]
  let g : Fin q → Module.End ℤ (Derived L) := fun i ↦ rightAction f (x i)
  have hp : (List.ofFn g).Pairwise Commute := by
    rw [List.pairwise_iff_get]
    intro i j _
    simp only [List.get_ofFn]
    exact rightAction_commute hmeta f _ _
  exact ((Equiv.Perm.ofFn_comp_perm e g).symm.prod_eq' hp).symm

def symmetricAction (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) :
    Sym[ℤ] (Fin q) X →ₗ[ℤ] Module.End ℤ (Derived L) :=
  SymmetricPower.lift (actionMultilinear hmeta f q)
    (actionMultilinear_symmetric hmeta f q)

@[simp]
theorem symmetricAction_tprod (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) (x : Fin q → X) :
    symmetricAction hmeta f q (SymmetricPower.tprod ℤ x) =
      (List.ofFn (fun i ↦ rightAction f (x i))).prod := by
  rw [symmetricAction, SymmetricPower.lift_tprod]
  rfl

theorem symmetricAction_insert (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) (x : X) :
    (symmetricAction hmeta f (q + 1)).comp
        (SymmetricPower.insert ℤ X q x) =
      (LinearMap.mulLeft ℤ (rightAction f x)).comp
        (symmetricAction hmeta f q) := by
  apply SymmetricPower.linearMap_ext
  intro a
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    SymmetricPower.insert_tprod, symmetricAction_tprod,
    symmetricAction_tprod]
  change (List.ofFn (fun i : Fin (q + 1) ↦
      rightAction f ((Fin.cons x a : Fin (q + 1) → X) i))).prod =
    rightAction f x * (List.ofFn (fun i : Fin q ↦ rightAction f (a i))).prod
  rw [List.ofFn_succ]
  rfl

private theorem bracket_mem_derived (x y : L) :
    ⁅x, y⁆ ∈ LieAlgebra.derivedSeries ℤ L 1 := by
  change ⁅x, y⁆ ∈ ⁅(⊤ : LieIdeal ℤ L), (⊤ : LieIdeal ℤ L)⁆
  exact LieSubmodule.lie_mem_lie (by simp) (by simp)

private def bracketMultilinear (f : X →ₗ[ℤ] L) :
    MultilinearMap ℤ (fun _ : Fin 2 ↦ X) (Derived L) :=
  MultilinearMap.mk'
    (fun a ↦ ⟨⁅f (a 0), f (a 1)⁆, bracket_mem_derived _ _⟩)
    (by
      intro a i x y
      fin_cases i
      · apply Subtype.ext
        change ⁅f (x + y), f (a 1)⁆ = ⁅f x, f (a 1)⁆ + ⁅f y, f (a 1)⁆
        rw [map_add, add_lie]
      · apply Subtype.ext
        change ⁅f (a 0), f (x + y)⁆ = ⁅f (a 0), f x⁆ + ⁅f (a 0), f y⁆
        rw [map_add, lie_add])
    (by
      intro a i z x
      fin_cases i
      · apply Subtype.ext
        change ⁅f (z • x), f (a 1)⁆ = z • ⁅f x, f (a 1)⁆
        rw [map_zsmul, zsmul_lie]
      · apply Subtype.ext
        change ⁅f (a 0), f (z • x)⁆ = z • ⁅f (a 0), f x⁆
        rw [map_zsmul, lie_zsmul])

private def bracketAlternating (f : X →ₗ[ℤ] L) :
    X [⋀^Fin 2]→ₗ[ℤ] Derived L :=
  AlternatingMap.mk (bracketMultilinear f) (by
    intro a i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · apply Subtype.ext
      change ⁅f (a 0), f (a 1)⁆ = 0
      have hij' : a 0 = a 1 := by simpa using hij
      rw [hij', lie_self]
    · apply Subtype.ext
      change ⁅f (a 0), f (a 1)⁆ = 0
      have hij' : a 1 = a 0 := by simpa using hij
      rw [hij', lie_self]
    · exact (hne rfl).elim)

def wedgeEval (f : X →ₗ[ℤ] L) : (⋀[ℤ]^2 X) →ₗ[ℤ] Derived L :=
  exteriorPower.alternatingMapLinearEquiv (bracketAlternating f)

@[simp]
theorem wedgeEval_ιMulti (f : X →ₗ[ℤ] L) (a : Fin 2 → X) :
    wedgeEval f (exteriorPower.ιMulti ℤ 2 a) =
      ⟨⁅f (a 0), f (a 1)⁆, bracket_mem_derived _ _⟩ := by
  calc
    wedgeEval f (exteriorPower.ιMulti ℤ 2 a) = bracketAlternating f a :=
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
    _ = _ := rfl

private def preEvalBilinear (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) :
    (⋀[ℤ]^2 X) →ₗ[ℤ] Sym[ℤ] (Fin q) X →ₗ[ℤ] L :=
  LinearMap.mk₂ ℤ
    (fun w s ↦ ((symmetricAction hmeta f q s) (wedgeEval f w)).1)
    (by
      intro a b s
      change ((symmetricAction hmeta f q s) (wedgeEval f (a + b))).1 = _
      rw [map_add, map_add]
      rfl)
    (by
      intro z a s
      change ((symmetricAction hmeta f q s) (wedgeEval f (z • a))).1 = _
      rw [map_zsmul, map_zsmul]
      rfl)
    (by
      intro w a b
      change ((symmetricAction hmeta f q (a + b)) (wedgeEval f w)).1 = _
      rw [map_add, LinearMap.add_apply]
      rfl)
    (by
      intro z w s
      change ((symmetricAction hmeta f q (z • s)) (wedgeEval f w)).1 = _
      rw [map_zsmul, LinearMap.smul_apply]
      rfl)

def preEval (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) : PreComponent X q →ₗ[ℤ] L :=
  TensorProduct.lift (preEvalBilinear hmeta f q)

@[simp]
theorem preEval_tmul (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) (w : ⋀[ℤ]^2 X)
    (s : Sym[ℤ] (Fin q)X) :
    preEval hmeta f q (w ⊗ₜ[ℤ] s) =
      ((symmetricAction hmeta f q s) (wedgeEval f w)).1 := by
  change preEvalBilinear hmeta f q w s = _
  rfl

private theorem rightAction_commute_symmetricAction
    (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    (q : ℕ) (x : X) (s : Sym[ℤ] (Fin q)X) :
    Commute (rightAction f x) (symmetricAction hmeta f q s) := by
  let left : Sym[ℤ] (Fin q) X →ₗ[ℤ] Module.End ℤ (Derived L) :=
    (LinearMap.mulLeft ℤ (rightAction f x)).comp (symmetricAction hmeta f q)
  let right : Sym[ℤ] (Fin q) X →ₗ[ℤ] Module.End ℤ (Derived L) :=
    (LinearMap.mulRight ℤ (rightAction f x)).comp (symmetricAction hmeta f q)
  have hlr : left = right := by
    apply SymmetricPower.linearMap_ext
    intro a
    simp only [left, right, LinearMap.comp_apply, symmetricAction_tprod,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    change rightAction f x *
        (List.ofFn (fun i ↦ rightAction f (a i))).prod =
      (List.ofFn (fun i ↦ rightAction f (a i))).prod * rightAction f x
    exact (Commute.list_prod_right _ _ (fun y hy ↦ by
      rw [List.mem_ofFn] at hy
      obtain ⟨i, rfl⟩ := hy
      exact rightAction_commute hmeta f x (a i))).eq
  exact LinearMap.congr_fun hlr s

theorem preEval_insert (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) (x : X) (w : ⋀[ℤ]^2 X)
    (s : Sym[ℤ] (Fin q)X) :
    preEval hmeta f (q + 1)
        (w ⊗ₜ[ℤ] SymmetricPower.insert ℤ X q x s) =
      ⁅preEval hmeta f q (w ⊗ₜ[ℤ] s), f x⁆ := by
  rw [preEval_tmul, preEval_tmul]
  have hi := LinearMap.congr_fun (symmetricAction_insert hmeta f q x) s
  change symmetricAction hmeta f (q + 1)
      (SymmetricPower.insert ℤ X q x s) =
    rightAction f x * symmetricAction hmeta f q s at hi
  rw [hi]
  rfl

theorem preEval_jacobi (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) :
    (preEval hmeta f (q + 1)).comp (jacobi X (q + 1)) = 0 := by
  apply TensorProduct.ext'
  intro w s
  let F : (⋀[ℤ]^3 X) →ₗ[ℤ] L :=
    ((preEval hmeta f (q + 1)).comp (jacobi X (q + 1))).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^3 X) _).flip s)
  have hF : F = 0 := by
    apply exteriorPower.linearMap_ext
    ext a
    change preEval hmeta f (q + 1)
        (jacobi X (q + 1) (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] s)) = 0
    rw [jacobi_wedge_tmul, map_add, map_sub,
      preEval_insert, preEval_insert, preEval_insert,
      preEval_tmul, preEval_tmul, preEval_tmul]
    have h0 : (0 : Fin 3).removeNth a =
        Fin.cons (a 1) (Fin.cons (a 2) Fin.elim0) := by
      funext i
      fin_cases i <;> rfl
    have h1 : (1 : Fin 3).removeNth a =
        Fin.cons (a 0) (Fin.cons (a 2) Fin.elim0) := by
      funext i
      fin_cases i <;> rfl
    have h2 : (2 : Fin 3).removeNth a =
        Fin.cons (a 0) (Fin.cons (a 1) Fin.elim0) := by
      funext i
      fin_cases i <;> rfl
    rw [h0, h1, h2]
    let S := symmetricAction hmeta f q s
    let d0 := wedgeEval f (exteriorPower.ιMulti ℤ 2
      (Fin.cons (a 1) (Fin.cons (a 2) Fin.elim0)))
    let d1 := wedgeEval f (exteriorPower.ιMulti ℤ 2
      (Fin.cons (a 0) (Fin.cons (a 2) Fin.elim0)))
    let d2 := wedgeEval f (exteriorPower.ιMulti ℤ 2
      (Fin.cons (a 0) (Fin.cons (a 1) Fin.elim0)))
    have hc0 := congrArg (fun T : Module.End ℤ (Derived L) ↦ T d0)
      (rightAction_commute_symmetricAction hmeta f q (a 0) s).eq
    have hc1 := congrArg (fun T : Module.End ℤ (Derived L) ↦ T d1)
      (rightAction_commute_symmetricAction hmeta f q (a 1) s).eq
    have hc2 := congrArg (fun T : Module.End ℤ (Derived L) ↦ T d2)
      (rightAction_commute_symmetricAction hmeta f q (a 2) s).eq
    change (rightAction f (a 0) (S d0)).1 -
        (rightAction f (a 1) (S d1)).1 +
          (rightAction f (a 2) (S d2)).1 = 0
    change rightAction f (a 0) (S d0) = S (rightAction f (a 0) d0) at hc0
    change rightAction f (a 1) (S d1) = S (rightAction f (a 1) d1) at hc1
    change rightAction f (a 2) (S d2) = S (rightAction f (a 2) d2) at hc2
    rw [hc0, hc1, hc2]
    have hraw : rightAction f (a 0) d0 - rightAction f (a 1) d1 +
        rightAction f (a 2) d2 = 0 := by
      apply Subtype.ext
      simp only [d0, d1, d2, wedgeEval_ιMulti]
      change ⁅⁅f (a 1), f (a 2)⁆, f (a 0)⁆ -
            ⁅⁅f (a 0), f (a 2)⁆, f (a 1)⁆ +
          ⁅⁅f (a 0), f (a 1)⁆, f (a 2)⁆ = 0
      have hj := lie_jacobi (f (a 0)) (f (a 1)) (f (a 2))
      rw [← lie_skew (f (a 0)) ⁅f (a 1), f (a 2)⁆,
        ← lie_skew (f (a 1)) ⁅f (a 2), f (a 0)⁆,
        ← lie_skew (f (a 2)) ⁅f (a 0), f (a 1)⁆] at hj
      rw [show ⁅f (a 2), f (a 0)⁆ = -⁅f (a 0), f (a 2)⁆ by
        exact (lie_skew _ _).symm] at hj
      simp only [neg_lie] at hj
      have hn : -(⁅⁅f (a 1), f (a 2)⁆, f (a 0)⁆ -
            ⁅⁅f (a 0), f (a 2)⁆, f (a 1)⁆ +
          ⁅⁅f (a 0), f (a 1)⁆, f (a 2)⁆) = 0 := by
        calc
          _ = -⁅⁅f (a 1), f (a 2)⁆, f (a 0)⁆ +
                - -⁅⁅f (a 0), f (a 2)⁆, f (a 1)⁆ +
              -⁅⁅f (a 0), f (a 1)⁆, f (a 2)⁆ := by abel
          _ = 0 := hj
      exact neg_eq_zero.mp hn
    have hsraw : S (rightAction f (a 0) d0) -
        S (rightAction f (a 1) d1) + S (rightAction f (a 2) d2) = 0 := by
      calc
        S (rightAction f (a 0) d0) - S (rightAction f (a 1) d1) +
            S (rightAction f (a 2) d2) =
            S (rightAction f (a 0) d0 - rightAction f (a 1) d1) +
              S (rightAction f (a 2) d2) := by
          exact congrArg₂ (fun x y ↦ x + y)
            (S.map_sub (rightAction f (a 0) d0)
              (rightAction f (a 1) d1)).symm rfl
        _ = S (rightAction f (a 0) d0 - rightAction f (a 1) d1 +
              rightAction f (a 2) d2) :=
          (S.map_add _ _).symm
        _ = 0 := by rw [hraw, map_zero]
    have hsval := congrArg Subtype.val hsraw
    change (S (rightAction f (a 0) d0)).1 -
        (S (rightAction f (a 1) d1)).1 +
          (S (rightAction f (a 2) d2)).1 = 0 at hsval
    exact hsval
  exact LinearMap.congr_fun hF w

/-- Evaluation of the homogeneous metabelian component of weight `q+2`. -/
def componentEval (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) : (q : ℕ) → Component X q →ₗ[ℤ] L
  | 0 => (LieAlgebra.derivedSeries ℤ L 1).toSubmodule.subtype.comp (wedgeEval f)
  | q + 1 =>
      (LinearMap.range (jacobi X (q + 1))).liftQ
        (preEval hmeta f (q + 1)) (by
          rintro y ⟨z, rfl⟩
          change preEval hmeta f (q + 1) (jacobi X (q + 1) z) = 0
          exact LinearMap.congr_fun (preEval_jacobi hmeta f q) z)

@[simp]
theorem componentEval_zero_ιMulti (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (a : Fin 2 → X) :
    componentEval hmeta f 0 (exteriorPower.ιMulti ℤ 2 a) =
      ⁅f (a 0), f (a 1)⁆ := by
  change (wedgeEval f (exteriorPower.ιMulti ℤ 2 a)).1 = _
  rw [wedgeEval_ιMulti]

@[simp]
theorem componentEval_succ_mkQ (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) (z : PreComponent X (q + 1)) :
    componentEval hmeta f (q + 1)
        ((LinearMap.range (jacobi X (q + 1))).mkQ z) =
      preEval hmeta f (q + 1) z := rfl

theorem componentEval_generatorBracket (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (x y : X) :
    componentEval hmeta f 0 (generatorBracket X x y) = ⁅f x, f y⁆ := by
  rw [generatorBracket_apply, componentEval_zero_ιMulti]
  rfl

theorem componentEval_action (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) (x : X) (m : Component X q) :
    componentEval hmeta f (q + 1) (Action.apply X q x m) =
      ⁅componentEval hmeta f q m, f x⁆ := by
  cases q with
  | zero =>
      change componentEval hmeta f 1
          ((commutatorClass X 0)
            (m ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x)) = _
      change componentEval hmeta f 1
          ((LinearMap.range (jacobi X 1)).mkQ
            (m ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x)) = _
      rw [componentEval_succ_mkQ, preEval_tmul]
      let e0 : Sym[ℤ] (Fin 0) X :=
        SymmetricPower.tprod ℤ (fun i : Fin 0 => Fin.elim0 i)
      have hdegree : SymmetricPower.degreeOne (R := ℤ) x =
          SymmetricPower.insert ℤ X 0 x e0 := by
        rw [SymmetricPower.degreeOne_apply,
          SymmetricPower.insert_tprod]
        apply congrArg (SymmetricPower.tprod ℤ)
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      rw [hdegree]
      have hi := LinearMap.congr_fun (symmetricAction_insert hmeta f 0 x) e0
      change symmetricAction hmeta f 1
          (SymmetricPower.insert ℤ X 0 x e0) =
        rightAction f x * symmetricAction hmeta f 0 e0 at hi
      rw [hi]
      have he0 : symmetricAction hmeta f 0 e0 = 1 := by
        change symmetricAction hmeta f 0
            (SymmetricPower.tprod ℤ (fun i : Fin 0 => Fin.elim0 i)) = 1
        rw [symmetricAction_tprod]
        rfl
      rw [he0, mul_one]
      change ⁅(wedgeEval f m).1, f x⁆ = _
      rfl
  | succ q =>
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (jacobi X (q + 1))) m
      change componentEval hmeta f (q + 2)
          ((LinearMap.range (jacobi X (q + 2))).mkQ
            (Action.pre X (q + 1) x z)) = _
      rw [componentEval_succ_mkQ, componentEval_succ_mkQ]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul w s => rw [Action.pre_tmul, preEval_insert]
      | add a b ha hb => simp only [map_add, ha, hb, add_lie]

private theorem bracket_mem_lowerCentralSeries_succ (q : ℕ)
    {y : L} (hy : y ∈ LieModule.lowerCentralSeries ℤ L L (q + 1))
    (x : L) : ⁅y, x⁆ ∈ LieModule.lowerCentralSeries ℤ L L (q + 2) := by
  rw [show q + 2 = (q + 1) + 1 by omega,
    LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
  exact LieSubmodule.lie_mem_lie hy (by simp)

theorem preEval_mem_lowerCentralSeries (hmeta : LieRings.IsMetabelian L)
    (f : X →ₗ[ℤ] L) (q : ℕ) (z : PreComponent X q) :
    preEval hmeta f q z ∈ LieModule.lowerCentralSeries ℤ L L (q + 1) := by
  induction q with
  | zero =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul w s =>
          let G : Sym[ℤ] (Fin 0) X →ₗ[ℤ] L :=
            (preEval hmeta f 0).comp
              ((TensorProduct.mk ℤ (⋀[ℤ]^2 X) _ w))
          suffices hs : ∀ s : Sym[ℤ] (Fin 0) X,
              G s ∈ LieModule.lowerCentralSeries ℤ L L 1 by
            exact hs s
          intro t
          have ht : t ∈ Submodule.span ℤ
              (Set.range (SymmetricPower.tprod ℤ :
                (Fin 0 → X) → Sym[ℤ] (Fin 0) X)) := by
            rw [SymmetricPower.span_tprod_eq_top]
            simp
          induction ht using Submodule.span_induction with
          | mem t ht =>
              obtain ⟨a, rfl⟩ := ht
              change preEval hmeta f 0
                  (w ⊗ₜ[ℤ] SymmetricPower.tprod ℤ a) ∈ _
              rw [preEval_tmul, symmetricAction_tprod]
              change (wedgeEval f w).1 ∈ _
              exact (wedgeEval f w).property
          | zero => simp
          | add a b _ _ ha hb => simpa only [map_add] using
              (LieModule.lowerCentralSeries ℤ L L 1).add_mem ha hb
          | smul z a _ ha =>
              have heq : G (z • a) = z • G a := G.map_smul z a
              exact heq.symm ▸
                (LieModule.lowerCentralSeries ℤ L L 1).smul_mem z ha
      | add a b ha hb => simpa only [map_add] using
          (LieModule.lowerCentralSeries ℤ L L 1).add_mem ha hb
  | succ q ih =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul w s =>
          let G : Sym[ℤ] (Fin (q + 1)) X →ₗ[ℤ] L :=
            (preEval hmeta f (q + 1)).comp
              ((TensorProduct.mk ℤ (⋀[ℤ]^2 X) _ w))
          suffices hs : ∀ s : Sym[ℤ] (Fin (q + 1)) X,
              G s ∈ LieModule.lowerCentralSeries ℤ L L (q + 2) by
            exact hs s
          intro t
          have ht : t ∈ Submodule.span ℤ
              (Set.range (SymmetricPower.tprod ℤ :
                (Fin (q + 1) → X) → Sym[ℤ] (Fin (q + 1)) X)) := by
            rw [SymmetricPower.span_tprod_eq_top]
            simp
          induction ht using Submodule.span_induction with
          | mem t ht =>
              obtain ⟨a, rfl⟩ := ht
              let tail : Fin q → X := fun i ↦ a i.succ
              have htprod : SymmetricPower.tprod ℤ a =
                  SymmetricPower.insert ℤ X q (a 0)
                    (SymmetricPower.tprod ℤ tail) := by
                rw [SymmetricPower.insert_tprod]
                apply congrArg (SymmetricPower.tprod ℤ)
                funext i
                exact Fin.cases rfl (fun j ↦ rfl) i
              change preEval hmeta f (q + 1)
                  (w ⊗ₜ[ℤ] SymmetricPower.tprod ℤ a) ∈ _
              rw [htprod, preEval_insert]
              exact bracket_mem_lowerCentralSeries_succ q
                (ih (w ⊗ₜ[ℤ] SymmetricPower.tprod ℤ tail)) (f (a 0))
          | zero => simp
          | add a b _ _ ha hb => simpa only [map_add] using
              (LieModule.lowerCentralSeries ℤ L L (q + 2)).add_mem ha hb
          | smul z a _ ha =>
              have heq : G (z • a) = z • G a := G.map_smul z a
              exact heq.symm ▸
                (LieModule.lowerCentralSeries ℤ L L (q + 2)).smul_mem z ha
      | add a b ha hb => simpa only [map_add] using
          (LieModule.lowerCentralSeries ℤ L L (q + 2)).add_mem ha hb

theorem componentEval_mem_lowerCentralSeries
    (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    (q : ℕ) (m : Component X q) :
    componentEval hmeta f q m ∈
      LieModule.lowerCentralSeries ℤ L L (q + 1) := by
  cases q with
  | zero =>
      change (wedgeEval f m).1 ∈ LieModule.lowerCentralSeries ℤ L L 1
      exact (wedgeEval f m).property
  | succ q =>
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (jacobi X (q + 1))) m
      rw [componentEval_succ_mkQ]
      exact preEval_mem_lowerCentralSeries hmeta f (q + 1) z

def pieceEval (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L) :
    (n : ℕ) → FreeMetabelian.Piece X n →ₗ[ℤ] L
  | 0 => f
  | q + 1 => (componentEval hmeta f q).toAddMonoidHom.toIntLinearMap

/-- Sum of the homogeneous evaluations. -/
def linear (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    (c : ℕ) : FreeMetabelian.Free X c →ₗ[ℤ] L where
  toFun x := ∑ i : Fin c, pieceEval hmeta f i.val (x i)
  map_add' x y := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' z x := by
    change (∑ i : Fin c, pieceEval hmeta f i.val (z • x i)) =
      z • ∑ i : Fin c, pieceEval hmeta f i.val (x i)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (pieceEval hmeta f i.val).toAddMonoidHom.map_zsmul (x i) z

@[simp]
theorem linear_apply (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    (c : ℕ) (x : FreeMetabelian.Free X c) :
    linear hmeta f c x = ∑ i : Fin c, pieceEval hmeta f i.val (x i) := rfl

@[simp]
theorem linear_incl (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    {c : ℕ} (i : Fin c) (x : FreeMetabelian.Piece X i.val) :
    linear hmeta f c (FreeMetabelian.Free.incl i x) =
      pieceEval hmeta f i.val x := by
  rw [linear_apply]
  classical
  rw [Finset.sum_eq_single i]
  · exact congrArg (pieceEval hmeta f i.val)
      (FreeMetabelian.Free.incl_apply_same i x)
  · intro j _ hj
    rw [FreeMetabelian.Free.incl_apply_of_ne i j hj]
    exact map_zero _
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Extending a homogeneous prefix by zero does not change its evaluation. -/
theorem linear_prefixIncl (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    {c : ℕ} (k : ℕ) (hk : k ≤ c) (x : FreeMetabelian.Free X k) :
    linear hmeta f c (FreeMetabelian.Free.prefixIncl k hk x) =
      linear hmeta f k x := by
  rw [linear_apply, linear_apply]
  classical
  calc
    ∑ i : Fin c, pieceEval hmeta f i.val
        (FreeMetabelian.Free.prefixIncl k hk x i) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin c ↦ i.val < k),
          pieceEval hmeta f i.val
            (FreeMetabelian.Free.prefixIncl k hk x i) := by
      apply Eq.symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hik : k ≤ i.val := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hi
      rw [FreeMetabelian.Free.prefixIncl_apply_of_le k hk x i hik, map_zero]
    _ = ∑ i : Fin k, pieceEval hmeta f i.val (x i) := by
      apply Finset.sum_bij
          (fun i hi ↦ ⟨i.val,
            (Finset.mem_filter.mp hi).2⟩)
      · intro i hi
        exact Finset.mem_univ _
      · intro i₁ hi₁ i₂ hi₂ h
        exact Fin.ext (by simpa using congrArg Fin.val h)
      · intro j _
        let i : Fin c := ⟨j.val, j.isLt.trans_le hk⟩
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, ?_⟩
        exact Fin.ext rfl
      · intro i hi
        rw [FreeMetabelian.Free.prefixIncl_apply_of_lt k hk x i
          (Finset.mem_filter.mp hi).2]

/-- Evaluation sends a free homogeneous tail into the matching lower-central
term.  This is the direct sum-of-homogeneous-pieces argument used by the
canonical tower. -/
theorem linear_mem_lowerCentralSeries_of_mem_tail
    (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    {c k : ℕ} (x : FreeMetabelian.Free X c)
    (hx : x ∈ FreeMetabelian.Free.tail k) :
    linear hmeta f c x ∈ LieModule.lowerCentralSeries ℤ L L k := by
  rw [← FreeMetabelian.Free.sum_incl_project x, map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases hik : i.val < k
  · rw [linear_incl, FreeMetabelian.Free.project_apply, hx i hik, map_zero]
    exact Submodule.zero_mem _
  · rw [linear_incl]
    have hpiece : pieceEval hmeta f i.val
        (FreeMetabelian.Free.project i x) ∈
        LieModule.lowerCentralSeries ℤ L L i.val := by
      rcases i with ⟨(_ | q), hi⟩
      · rw [LieModule.lowerCentralSeries_zero]
        exact LieSubmodule.mem_top _
      · change componentEval hmeta f q (FreeMetabelian.Free.project
            (⟨q + 1, hi⟩ : Fin c) x) ∈
          LieModule.lowerCentralSeries ℤ L L (q + 1)
        exact componentEval_mem_lowerCentralSeries hmeta f q _
    change pieceEval hmeta f i.val (FreeMetabelian.Free.project i x) ∈
      LieModule.lowerCentralSeries ℤ L L k
    exact LieModule.antitone_lowerCentralSeries ℤ L L
      (Nat.le_of_not_gt hik) hpiece

private theorem bracket_incl_zero_zero {c : ℕ} (h : 1 < c) (x y : X) :
    ⁅FreeMetabelian.Free.incl (X := X) (⟨0, by omega⟩ : Fin c) x,
      FreeMetabelian.Free.incl (X := X) (⟨0, by omega⟩ : Fin c) y⁆ =
      FreeMetabelian.Free.incl (X := X) (⟨1, h⟩ : Fin c)
        (generatorBracket X x y) := by
  funext i
  change FreeMetabelian.Free.bracket _ _ i = _
  rcases i with ⟨(_ | _ | q), hi⟩
  · rw [FreeMetabelian.Free.bracket_apply_zero]
    apply Eq.symm
    apply FreeMetabelian.Free.incl_apply_of_ne
    intro heq
    have hv := congrArg Fin.val heq
    norm_num at hv
  · rw [FreeMetabelian.Free.bracket_apply_one]
    simp [FreeMetabelian.Free.degreeOne, FreeMetabelian.Free.incl]
  · rw [FreeMetabelian.Free.bracket_apply_succ_succ]
    have hne : (⟨q + 2, hi⟩ : Fin c) ≠ ⟨1, h⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      norm_num at hv
      omega
    rw [FreeMetabelian.Free.incl_apply_of_ne _ _ hne]
    simp [FreeMetabelian.Free.degreeOne, FreeMetabelian.Free.derived,
      FreeMetabelian.Free.incl]
    have hy0 : Action.apply X q y (0 : Component X q) = 0 :=
      (Action.apply X q y).map_zero
    have hx0 : Action.apply X q x (0 : Component X q) = 0 :=
      (Action.apply X q x).map_zero
    exact sub_eq_zero.mpr (hy0.trans hx0.symm)

private theorem bracket_incl_derived_zero {c q : ℕ} (hq : q + 2 < c)
    (m : Component X q) (x : X) :
    ⁅FreeMetabelian.Free.incl (X := X) (⟨q + 1, by omega⟩ : Fin c) m,
      FreeMetabelian.Free.incl (X := X) (⟨0, by omega⟩ : Fin c) x⁆ =
      FreeMetabelian.Free.incl (X := X) (⟨q + 2, hq⟩ : Fin c)
        (Action.apply X q x m) := by
  funext i
  change FreeMetabelian.Free.bracket _ _ i = _
  rcases i with ⟨(_ | _ | r), hi⟩
  · rw [FreeMetabelian.Free.bracket_apply_zero]
    apply Eq.symm
    apply FreeMetabelian.Free.incl_apply_of_ne
    intro heq
    have hv := congrArg Fin.val heq
    norm_num at hv
  · rw [FreeMetabelian.Free.bracket_apply_one]
    have hne : (⟨1, hi⟩ : Fin c) ≠ ⟨q + 2, hq⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      norm_num at hv
    rw [FreeMetabelian.Free.incl_apply_of_ne _ _ hne]
    change generatorBracket X 0 x = 0
    exact LinearMap.congr_fun (map_zero (generatorBracket X)) x
  · by_cases hr : r = q
    · subst r
      rw [FreeMetabelian.Free.bracket_apply_succ_succ]
      simp [FreeMetabelian.Free.degreeOne, FreeMetabelian.Free.derived,
        FreeMetabelian.Free.incl]
      have hz : Action.apply X q 0 (0 : Component X q) = 0 :=
        Action.apply_zero_apply X q 0
      calc
        Action.apply X q x m - Action.apply X q 0 0 =
            Action.apply X q x m - 0 := congrArg (fun z ↦ Action.apply X q x m - z) hz
        _ = Action.apply X q x m := sub_zero _
    · have hne : (⟨r + 2, hi⟩ : Fin c) ≠ ⟨q + 2, hq⟩ := by
        intro heq
        apply hr
        have hv := congrArg Fin.val heq
        norm_num at hv
        omega
      have hcoord : (⟨r + 1, by omega⟩ : Fin c) ≠ ⟨q + 1, by omega⟩ := by
        intro heq
        apply hr
        have hv := congrArg Fin.val heq
        norm_num at hv
        omega
      rw [FreeMetabelian.Free.bracket_apply_succ_succ]
      simp [FreeMetabelian.Free.degreeOne, FreeMetabelian.Free.derived,
        FreeMetabelian.Free.incl, hne, hcoord]
      have hx0 : Action.apply X r x (0 : Component X r) = 0 :=
        (Action.apply X r x).map_zero
      have hz0 : Action.apply X r 0 (0 : Component X r) = 0 :=
        Action.apply_zero_apply X r 0
      exact sub_eq_zero.mpr (hx0.trans hz0.symm)

private theorem bracket_incl_derived_zero_overflow {c q : ℕ}
    (hqc : q + 1 < c) (hover : c ≤ q + 2)
    (m : Component X q) (x : X) :
    ⁅FreeMetabelian.Free.incl (X := X) (⟨q + 1, hqc⟩ : Fin c) m,
      FreeMetabelian.Free.incl (X := X) (⟨0, by omega⟩ : Fin c) x⁆ = 0 := by
  funext i
  change FreeMetabelian.Free.bracket _ _ i = 0
  rcases i with ⟨(_ | _ | r), hi⟩
  · rw [FreeMetabelian.Free.bracket_apply_zero]
  · rw [FreeMetabelian.Free.bracket_apply_one]
    change generatorBracket X 0 x = 0
    exact LinearMap.congr_fun (map_zero (generatorBracket X)) x
  · have hr : r ≠ q := by omega
    have hcoord : (⟨r + 1, by omega⟩ : Fin c) ≠ ⟨q + 1, hqc⟩ := by
      intro heq
      apply hr
      have hv := congrArg Fin.val heq
      norm_num at hv
      omega
    rw [FreeMetabelian.Free.bracket_apply_succ_succ]
    simp [FreeMetabelian.Free.degreeOne, FreeMetabelian.Free.derived,
      FreeMetabelian.Free.incl, hcoord]
    have hx0 : Action.apply X r x (0 : Component X r) = 0 :=
      (Action.apply X r x).map_zero
    have hz0 : Action.apply X r 0 (0 : Component X r) = 0 :=
      Action.apply_zero_apply X r 0
    exact sub_eq_zero.mpr (hx0.trans hz0.symm)

private theorem bracket_incl_derived_derived {c q r : ℕ}
    (hq : q + 1 < c) (hr : r + 1 < c)
    (m : Component X q) (n : Component X r) :
    ⁅FreeMetabelian.Free.incl (X := X) (⟨q + 1, hq⟩ : Fin c) m,
      FreeMetabelian.Free.incl (X := X) (⟨r + 1, hr⟩ : Fin c) n⁆ = 0 := by
  funext i
  change FreeMetabelian.Free.bracket _ _ i = 0
  rcases i with ⟨(_ | _ | t), hi⟩
  · rw [FreeMetabelian.Free.bracket_apply_zero]
  · rw [FreeMetabelian.Free.bracket_apply_one]
    change generatorBracket X 0 0 = 0
    exact (generatorBracket X 0).map_zero
  · rw [FreeMetabelian.Free.bracket_apply_succ_succ]
    simp [FreeMetabelian.Free.degreeOne, FreeMetabelian.Free.incl]
    have hleft : Action.apply X t 0
        (FreeMetabelian.Free.derived
          (FreeMetabelian.Free.incl (X := X) (⟨q + 1, hq⟩ : Fin c) m)
          t (by omega)) = 0 := Action.apply_zero_apply X t _
    have hright : Action.apply X t 0
        (FreeMetabelian.Free.derived
          (FreeMetabelian.Free.incl (X := X) (⟨r + 1, hr⟩ : Fin c) n)
          t (by omega)) = 0 := Action.apply_zero_apply X t _
    exact sub_eq_zero.mpr (hleft.trans hright.symm)

private theorem bracket_eq_zero_of_class_bound {c : ℕ}
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    {k : ℕ} (hck : c ≤ k) {x : L}
    (hx : x ∈ LieModule.lowerCentralSeries ℤ L L k) : x = 0 := by
  have hx' : x ∈ LieModule.lowerCentralSeries ℤ L L c :=
    LieModule.antitone_lowerCentralSeries ℤ L L hck hx
  rw [hclass] at hx'
  exact hx'

private theorem linear_bracket_incl (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (f : X →ₗ[ℤ] L) (i j : Fin c)
    (a : FreeMetabelian.Piece X i.val)
    (b : FreeMetabelian.Piece X j.val) :
    linear hmeta f c
        ⁅FreeMetabelian.Free.incl i a, FreeMetabelian.Free.incl j b⁆ =
      ⁅pieceEval hmeta f i.val a, pieceEval hmeta f j.val b⁆ := by
  rcases i with ⟨(_ | q), hi⟩
  · rcases j with ⟨(_ | r), hj⟩
    · by_cases hc : 1 < c
      · rw [bracket_incl_zero_zero hc, linear_incl,
          show pieceEval hmeta f (⟨1, hc⟩ : Fin c).val =
              componentEval hmeta f 0 by rfl]
        change componentEval hmeta f 0 (generatorBracket X a b) = ⁅f a, f b⁆
        exact componentEval_generatorBracket hmeta f a b
      · have hc1 : c = 1 := by omega
        subst c
        have hsource :
            ⁅FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin 1) a,
              FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin 1) b⁆ = 0 := by
          funext k
          fin_cases k
          exact FreeMetabelian.Free.bracket_apply_zero _ _ (by omega)
        rw [hsource, map_zero]
        exact (bracket_eq_zero_of_class_bound hclass (show 1 ≤ 1 by omega)
          (show ⁅f a, f b⁆ ∈ LieModule.lowerCentralSeries ℤ L L 1 by
            rw [LieModule.lowerCentralSeries_succ]
            exact LieSubmodule.lie_mem_lie (by simp) (by simp))).symm
    · have hj' : r + 1 < c := hj
      by_cases hnext : r + 2 < c
      · rw [← lie_skew,
          bracket_incl_derived_zero (X := X) hnext b a,
          map_neg, linear_incl]
        change -componentEval hmeta f (r + 1) (Action.apply X r a b) =
          ⁅f a, componentEval hmeta f r b⁆
        rw [componentEval_action]
        exact lie_skew _ _
      · have hover : c ≤ r + 2 := by omega
        rw [← lie_skew,
          bracket_incl_derived_zero_overflow (X := X) hj hover b a,
          map_neg, map_zero, neg_zero]
        apply Eq.symm
        apply bracket_eq_zero_of_class_bound hclass hover
        rw [← lie_skew]
        exact (LieModule.lowerCentralSeries ℤ L L (r + 2)).neg_mem
          (bracket_mem_lowerCentralSeries_succ r
            (componentEval_mem_lowerCentralSeries hmeta f r b) (f a))
  · rcases j with ⟨(_ | r), hj⟩
    · by_cases hnext : q + 2 < c
      · rw [bracket_incl_derived_zero hnext, linear_incl,
          show pieceEval hmeta f (⟨q + 2, hnext⟩ : Fin c).val =
              componentEval hmeta f (q + 1) by rfl]
        change componentEval hmeta f (q + 1) (Action.apply X q b a) =
          ⁅componentEval hmeta f q a, f b⁆
        exact componentEval_action hmeta f q b a
      · have hover : c ≤ q + 2 := by omega
        rw [bracket_incl_derived_zero_overflow hi hover, map_zero]
        exact (bracket_eq_zero_of_class_bound hclass hover
          (bracket_mem_lowerCentralSeries_succ q
            (componentEval_mem_lowerCentralSeries hmeta f q a) (f b))).symm
    · rw [bracket_incl_derived_derived hi hj, map_zero]
      apply Eq.symm
      apply hmeta.bracket_eq_zero
      · change componentEval hmeta f q a ∈
          LieAlgebra.derivedSeries ℤ L 1
        exact LieModule.antitone_lowerCentralSeries ℤ L L
          (show 1 ≤ q + 1 by omega)
          (componentEval_mem_lowerCentralSeries hmeta f q a)
      · change componentEval hmeta f r b ∈
          LieAlgebra.derivedSeries ℤ L 1
        exact LieModule.antitone_lowerCentralSeries ℤ L L
          (show 1 ≤ r + 1 by omega)
          (componentEval_mem_lowerCentralSeries hmeta f r b)

theorem linear_lie (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (f : X →ₗ[ℤ] L) (x y : FreeMetabelian.Free X c) :
    linear hmeta f c ⁅x, y⁆ = ⁅linear hmeta f c x, linear hmeta f c y⁆ := by
  rw [← FreeMetabelian.Free.sum_incl_project x,
    ← FreeMetabelian.Free.sum_incl_project y]
  simp only [map_sum, sum_lie, lie_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [linear_incl, linear_incl]
  exact linear_bracket_incl hmeta hclass f j i
    (FreeMetabelian.Free.project j x) (FreeMetabelian.Free.project i y)

/-- The universal evaluation map on the truncated free metabelian Lie ring. -/
def lieHom (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (f : X →ₗ[ℤ] L) : FreeMetabelian.Free X c →ₗ⁅ℤ⁆ L where
  toLinearMap := linear hmeta f c
  map_lie' := fun {x y} ↦ linear_lie hmeta hclass f x y

@[simp]
theorem lieHom_apply (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (f : X →ₗ[ℤ] L) (x : FreeMetabelian.Free X c) :
    lieHom hmeta hclass f x = linear hmeta f c x := by
  change linear hmeta f c x = linear hmeta f c x
  rfl

@[simp]
theorem lieHom_incl (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (f : X →ₗ[ℤ] L) (i : Fin c)
    (x : FreeMetabelian.Piece X i.val) :
    lieHom hmeta hclass f (FreeMetabelian.Free.incl i x) =
      pieceEval hmeta f i.val x :=
  by
    rw [lieHom_apply]
    exact linear_incl hmeta f i x

private theorem pieceEval_next_bracket
    (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    (n : ℕ) (y : FreeMetabelian.Piece X n) (x : X) :
    ∃ z : FreeMetabelian.Piece X (n + 1),
      pieceEval hmeta f (n + 1) z = ⁅f x, pieceEval hmeta f n y⁆ := by
  cases n with
  | zero =>
      exact ⟨generatorBracket X x y,
        componentEval_generatorBracket hmeta f x y⟩
  | succ q =>
      refine ⟨-Action.apply X q x y, ?_⟩
      change componentEval hmeta f (q + 1) (-(Action.apply X q x y)) =
        ⁅f x, componentEval hmeta f q y⁆
      rw [map_neg, componentEval_action]
      exact lie_skew _ _

/-- Surjective generator evaluation identifies each manuscript weight with
the corresponding lower-central term.  Coordinate `n` has weight `n+1`, so
Mathlib's zero-based lower-central index is exactly `n`. -/
theorem pieceEval_range_eq_lowerCentralSeries
    (hmeta : LieRings.IsMetabelian L) (f : X →ₗ[ℤ] L)
    (hf : Function.Surjective f) (n : ℕ) :
    LinearMap.range (pieceEval hmeta f n) =
      (LieModule.lowerCentralSeries ℤ L L n).toSubmodule := by
  induction n with
  | zero =>
      rw [LieModule.lowerCentralSeries_zero]
      exact LinearMap.range_eq_top.mpr hf
  | succ n ih =>
      apply le_antisymm
      · rintro z ⟨y, rfl⟩
        cases n with
        | zero => exact componentEval_mem_lowerCentralSeries hmeta f 0 y
        | succ q => exact componentEval_mem_lowerCentralSeries hmeta f (q + 1) y
      · rw [LieModule.lowerCentralSeries_succ,
          LieSubmodule.lieIdeal_oper_eq_linear_span']
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
            obtain ⟨a, ha, b, hb, rfl⟩ := hz
            obtain ⟨x, rfl⟩ := hf a
            have hbRange : b ∈ LinearMap.range (pieceEval hmeta f n) := by
              rw [ih]
              exact hb
            obtain ⟨y, rfl⟩ := hbRange
            obtain ⟨w, hw⟩ := pieceEval_next_bracket hmeta f n y x
            exact ⟨w, hw⟩
        | zero => exact Submodule.zero_mem _
        | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
        | smul z a _ ha => exact Submodule.smul_mem _ z ha

/-- The canonical generator map: the basis vector indexed by `l` evaluates
to `l`.  This is the deliberately non-minimal manuscript presentation. -/
def canonicalGeneratorMap (L : Type w) [LieRing L] :
    (L →₀ ℤ) →ₗ[ℤ] L := Finsupp.linearCombination ℤ id

@[simp]
theorem canonicalGeneratorMap_single (l : L) (z : ℤ) :
    canonicalGeneratorMap L (Finsupp.single l z) = z • l := by
  simp [canonicalGeneratorMap]

theorem canonicalGeneratorMap_surjective :
    Function.Surjective (canonicalGeneratorMap L) := by
  intro l
  exact ⟨Finsupp.single l 1, by simp⟩

section Canonical

variable [Finite L]

/-- Canonical evaluation of the free metabelian cutoff onto `L`. -/
def canonicalEvaluation (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥) :
    FreeMetabelian.Free (L →₀ ℤ) c →ₗ⁅ℤ⁆ L :=
  lieHom hmeta hclass (canonicalGeneratorMap L)

theorem canonicalEvaluation_surjective
    (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (hc : 0 < c) : Function.Surjective (canonicalEvaluation hmeta hclass) := by
  intro l
  refine ⟨FreeMetabelian.Free.incl (⟨0, hc⟩ : Fin c)
    (Finsupp.single l 1), ?_⟩
  rw [canonicalEvaluation, lieHom_incl]
  change canonicalGeneratorMap L (Finsupp.single l 1) = l
  rw [canonicalGeneratorMap_single, one_zsmul]

/-- The canonical homogeneous coordinate has image exactly `gamma_(n+1)`. -/
theorem canonicalPiece_range_eq_lowerCentralSeries
    (hmeta : LieRings.IsMetabelian L) (n : ℕ) :
    LinearMap.range (pieceEval hmeta (canonicalGeneratorMap L) n) =
      (LieModule.lowerCentralSeries ℤ L L n).toSubmodule :=
  pieceEval_range_eq_lowerCentralSeries hmeta (canonicalGeneratorMap L)
    canonicalGeneratorMap_surjective n

/-- First-isomorphism form of the canonical metabelian presentation. -/
def canonicalQuotientEquiv
    (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (hc : 0 < c) :
    (FreeMetabelian.Free (L →₀ ℤ) c ⧸
      LieHom.ker (canonicalEvaluation hmeta hclass)) ≃ₗ⁅ℤ⁆ L where
  toLieHom :=
    { (canonicalEvaluation hmeta hclass).toLinearMap.quotKerEquivOfSurjective
        (canonicalEvaluation_surjective hmeta hclass hc) with
      map_lie' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y => exact LieHom.map_lie (canonicalEvaluation hmeta hclass) x y }
  invFun := ((canonicalEvaluation hmeta hclass).toLinearMap.quotKerEquivOfSurjective
    (canonicalEvaluation_surjective hmeta hclass hc)).symm
  left_inv := ((canonicalEvaluation hmeta hclass).toLinearMap.quotKerEquivOfSurjective
    (canonicalEvaluation_surjective hmeta hclass hc)).left_inv
  right_inv := ((canonicalEvaluation hmeta hclass).toLinearMap.quotKerEquivOfSurjective
    (canonicalEvaluation_surjective hmeta hclass hc)).right_inv

end Canonical

section UniversalUniqueness

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable (bX : Module.Basis ι ℤ X)

/-- The literal left-normed bracket represented by a Hall index, embedded in
the truncation.  The recursive step removes the least symmetric tooth. -/
def hallBracket : (q : ℕ) → (h : HallIndex ι q) →
    (hq : q + 1 < c) → FreeMetabelian.Free X c
  | 0, h, hq =>
      ⁅FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin c) (bX h.head),
        FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin c) (bX h.pivot)⁆
  | q + 1, h, hq =>
      ⁅hallBracket q h.predecessor (show q + 1 < c by omega),
        FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin c)
          (bX h.nextTooth)⁆

/-- Every Hall basis vector is exactly the corresponding iterated bracket in
weight-one generators. -/
theorem hallBracket_eq_incl : ∀ (q : ℕ) (h : HallIndex ι q)
    (hq : q + 1 < c),
    hallBracket bX q h hq =
      FreeMetabelian.Free.incl (⟨q + 1, hq⟩ : Fin c)
        (hallVector bX q h) := by
  intro q
  induction q with
  | zero =>
      intro h hq
      rw [hallBracket, bracket_incl_zero_zero (X := X) hq]
      rfl
  | succ q ih =>
      intro h hq
      change ⁅hallBracket bX q h.predecessor (show q + 1 < c by omega),
          FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin c)
            (bX h.nextTooth)⁆ = _
      rw [ih h.predecessor (show q + 1 < c by omega),
        bracket_incl_derived_zero (X := X) hq]
      exact congrArg (FreeMetabelian.Free.incl (⟨q + 2, hq⟩ : Fin c))
        (FreeMetabelian.hallVector_succ_eq_action bX q h).symm

/-- A Hall comb with `q` symmetric teeth has lower-central index `q+1`. -/
theorem hallBracket_mem_lowerCentralSeries : ∀ (q : ℕ) (h : HallIndex ι q)
    (hq : q + 1 < c),
    hallBracket bX q h hq ∈
      LieModule.lowerCentralSeries ℤ (FreeMetabelian.Free X c)
        (FreeMetabelian.Free X c) (q + 1) := by
  intro q
  induction q with
  | zero =>
      intro h hq
      rw [hallBracket, show 1 = 0 + 1 by omega,
        LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (by simp) (by simp)
  | succ q ih =>
      intro h hq
      change ⁅hallBracket bX q h.predecessor (show q + 1 < c by omega),
          FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin c)
            (bX h.nextTooth)⁆ ∈ _
      rw [show q + 1 + 1 = (q + 1) + 1 by omega,
        LieModule.lowerCentralSeries_succ, LieSubmodule.lie_comm]
      exact LieSubmodule.lie_mem_lie
        (ih h.predecessor (show q + 1 < c by omega)) (by simp)

/-- Every vector in homogeneous coordinate `s` lies in the `s`th
zero-based lower-central term.  This survives arbitrary basis changes within
that coordinate, in particular the Smith changes used by the PBW basis. -/
theorem weightIncl_mem_lowerCentralSeries
    (bX : Module.Basis ι ℤ X) (s : ℕ) (hs : s < c)
    (x : FreeMetabelian.Piece X s) :
    FreeMetabelian.Free.weightIncl s hs x ∈
      LieModule.lowerCentralSeries ℤ (FreeMetabelian.Free X c)
        (FreeMetabelian.Free X c) s := by
  cases s with
  | zero => simp
  | succ q =>
      letI : Fintype (FreeMetabelian.Free.PieceIndex ι (q + 1)) :=
        Fintype.ofFinite _
      let hb := FreeMetabelian.Free.pieceBasis bX (q + 1)
      rw [← hb.sum_repr x, map_sum]
      apply (LieModule.lowerCentralSeries ℤ (FreeMetabelian.Free X c)
        (FreeMetabelian.Free X c) (q + 1)).sum_mem
      intro h hh
      rw [map_zsmul]
      apply (LieModule.lowerCentralSeries ℤ (FreeMetabelian.Free X c)
        (FreeMetabelian.Free X c) (q + 1)).smul_mem
      have hv : hb h = FreeMetabelian.hallVector bX q h := by
        change (Module.Basis.ofEquivFun (FreeMetabelian.hallBasis bX q).equivFun) h = _
        rw [Module.Basis.ofEquivFun_equivFun,
          FreeMetabelian.hallBasis_apply]
      rw [hv]
      change FreeMetabelian.Free.incl (⟨q + 1, hs⟩ : Fin c)
        (FreeMetabelian.hallVector bX q h) ∈ _
      rw [← hallBracket_eq_incl bX q h hs]
      exact hallBracket_mem_lowerCentralSeries bX q h hs

private theorem lieHom_hallVector
    (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (f : X →ₗ[ℤ] L) (g : FreeMetabelian.Free X c →ₗ⁅ℤ⁆ L)
    (hc : 0 < c) (hg : ∀ x : X,
      g (FreeMetabelian.Free.incl (⟨0, hc⟩ : Fin c) x) = f x) :
    ∀ (q : ℕ) (h : HallIndex ι q) (hq : q + 1 < c),
      g (FreeMetabelian.Free.incl (⟨q + 1, hq⟩ : Fin c)
          (hallVector bX q h)) =
        componentEval hmeta f q (hallVector bX q h) := by
  intro q
  induction q with
  | zero =>
      intro h hq
      rw [← hallBracket_eq_incl bX 0 h hq]
      rw [hallBracket]
      rw [LieHom.map_lie, hg, hg]
      change ⁅f (bX h.head), f (bX h.pivot)⁆ =
        componentEval hmeta f 0
          (generatorBracket X (bX h.head) (bX h.pivot))
      exact (componentEval_generatorBracket hmeta f _ _).symm
  | succ q ih =>
      intro h hq
      rw [← hallBracket_eq_incl bX (q + 1) h hq]
      rw [hallBracket]
      change g ⁅hallBracket bX q h.predecessor (show q + 1 < c by omega),
          FreeMetabelian.Free.incl (⟨0, by omega⟩ : Fin c)
            (bX h.nextTooth)⁆ = _
      rw [LieHom.map_lie, hallBracket_eq_incl bX q h.predecessor
          (show q + 1 < c by omega),
        ih h.predecessor (show q + 1 < c by omega), hg]
      rw [FreeMetabelian.hallVector_succ_eq_action]
      exact (componentEval_action hmeta f q _ _).symm

private theorem lieHom_agrees_on_incl
    (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (bX : Module.Basis ι ℤ X)
    (f : X →ₗ[ℤ] L) (g : FreeMetabelian.Free X c →ₗ⁅ℤ⁆ L)
    (hc : 0 < c) (hg : ∀ x : X,
      g (FreeMetabelian.Free.incl (⟨0, hc⟩ : Fin c) x) = f x)
    (i : Fin c) (x : FreeMetabelian.Piece X i.val) :
    g (FreeMetabelian.Free.incl i x) = pieceEval hmeta f i.val x := by
  rcases i with ⟨n, hi⟩
  cases n with
  | zero => exact hg x
  | succ q =>
    change Component X q at x
    let inclQ : Component X q →ₗ[ℤ] FreeMetabelian.Free X c :=
      FreeMetabelian.Free.inclComponent q hi
    let lhs : Component X q →ₗ[ℤ] L :=
      g.toLinearMap.comp inclQ
    have heq : lhs = componentEval hmeta f q := by
      apply (hallBasis bX q).ext
      intro h
      rw [hallBasis_apply]
      change g (FreeMetabelian.Free.inclComponent q hi
          (hallVector bX q h)) =
        componentEval hmeta f q (hallVector bX q h)
      exact lieHom_hallVector bX hmeta hclass f g hc hg q h hi
    change g (FreeMetabelian.Free.inclComponent q hi x) =
      componentEval hmeta f q x
    change lhs x = componentEval hmeta f q x
    exact LinearMap.congr_fun heq x

/-- Uniqueness in the universal property: a Lie homomorphism out of the
truncation is determined by its values on weight-one generators. -/
theorem lieHom_unique
    (hmeta : LieRings.IsMetabelian L)
    (hclass : LieModule.lowerCentralSeries ℤ L L c = ⊥)
    (bX : Module.Basis ι ℤ X)
    (hc : 0 < c) (f : X →ₗ[ℤ] L)
    (g : FreeMetabelian.Free X c →ₗ⁅ℤ⁆ L)
    (hg : ∀ x : X,
      g (FreeMetabelian.Free.incl (⟨0, hc⟩ : Fin c) x) = f x) :
    g = lieHom hmeta hclass f := by
  apply LieHom.ext
  intro x
  rw [← FreeMetabelian.Free.sum_incl_project x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [lieHom_incl]
  exact lieHom_agrees_on_incl hmeta hclass bX f g hc hg i
    (FreeMetabelian.Free.project i x)

end UniversalUniqueness

end
end FreeMetabelian.Evaluation
