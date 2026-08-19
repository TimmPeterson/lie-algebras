import LieRings.Homological.Koszul
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Homogeneous components of a free metabelian Lie ring

The component indexed by `q` below is manuscript weight `q+2`.  Using the
remaining symmetric degree as the Lean index makes weight two a literal base
case and avoids every use of truncated subtraction.
-/

open TensorProduct

namespace FreeMetabelian

universe u

noncomputable section

variable (X : Type u) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

/-- Before imposing Jacobi, manuscript weight `q+2` is
`Λ²X ⊗ Sym^q X`. -/
abbrev PreComponent (q : ℕ) :=
  (⋀[ℤ]^2 X) ⊗[ℤ] Sym[ℤ] (Fin q) X

/-- Source of Jacobi in weight `q+2`.  It is the zero module at `q=0`. -/
def JacobiSource : ℕ → Type u
  | 0 => Fin 0 → X
  | Nat.succ q => (⋀[ℤ]^3 X) ⊗[ℤ] Sym[ℤ] (Fin q) X

instance (q : ℕ) : AddCommGroup (JacobiSource X q) := by
  cases q with
  | zero =>
      change AddCommGroup (Fin 0 → X)
      infer_instance
  | succ q =>
      change AddCommGroup ((⋀[ℤ]^3 X) ⊗[ℤ] Sym[ℤ] (Fin q) X)
      infer_instance

instance (q : ℕ) : Module ℤ (JacobiSource X q) := by
  cases q with
  | zero =>
      change Module ℤ (Fin 0 → X)
      infer_instance
  | succ q =>
      change Module ℤ ((⋀[ℤ]^3 X) ⊗[ℤ] Sym[ℤ] (Fin q) X)
      infer_instance

/-- Jacobi is precisely the third Koszul differential for the identity map. -/
def jacobi : (q : ℕ) → JacobiSource X q →ₗ[ℤ] PreComponent X q
  | 0 => 0
  | Nat.succ q => by
      change ((⋀[ℤ]^3 X) ⊗[ℤ] Sym[ℤ] (Fin q) X) →ₗ[ℤ]
        ((⋀[ℤ]^2 X) ⊗[ℤ] Sym[ℤ] (Fin (q + 1)) X)
      exact Koszul.AllDegrees.differential (LinearMap.id : X →ₗ[ℤ] X) 2 q

@[simp]
theorem jacobi_wedge_tmul (q : ℕ) (a : Fin 3 → X)
    (u : Sym[ℤ] (Fin q) X) :
    jacobi X (Nat.succ q) (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] u) =
      exteriorPower.ιMulti ℤ 2 ((0 : Fin 3).removeNth a) ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ X q (a 0) u -
        exteriorPower.ιMulti ℤ 2 ((1 : Fin 3).removeNth a) ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ X q (a 1) u +
        exteriorPower.ιMulti ℤ 2 ((2 : Fin 3).removeNth a) ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ X q (a 2) u := by
  rw [jacobi]
  change Koszul.AllDegrees.differential LinearMap.id 2 q
      (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] u) = _
  rw [Koszul.AllDegrees.differential_wedge_tmul, Fin.sum_univ_three]
  simp only [Fin.val_zero, Nat.reduceSubDiff, one_smul, LinearMap.id_apply,
    Fin.val_one, pow_one, neg_smul, Fin.isValue]
  norm_num
  abel

/-- Manuscript component `M_(q+2)`.  At weight two this is definitionally
the exterior square; only higher weights are presented as quotients. -/
def Component : ℕ → Type u
  | 0 => ⋀[ℤ]^2 X
  | Nat.succ q =>
      PreComponent X (Nat.succ q) ⧸ LinearMap.range (jacobi X (Nat.succ q))

instance (q : ℕ) : AddCommGroup (Component X q) := by
  cases q with
  | zero =>
      change AddCommGroup (⋀[ℤ]^2 X)
      infer_instance
  | succ q =>
      change AddCommGroup
        (PreComponent X (Nat.succ q) ⧸ LinearMap.range (jacobi X (Nat.succ q)))
      infer_instance

instance (q : ℕ) : Module ℤ (Component X q) := by
  cases q with
  | zero =>
      change Module ℤ (⋀[ℤ]^2 X)
      infer_instance
  | succ q =>
      change Module ℤ
        (PreComponent X (Nat.succ q) ⧸ LinearMap.range (jacobi X (Nat.succ q)))
      infer_instance

/-- Weight two has no Jacobi relations and is exactly `Λ²X`. -/
def componentTwoEquiv : Component X 0 ≃ₗ[ℤ] (⋀[ℤ]^2 X) :=
  by
    change (⋀[ℤ]^2 X) ≃ₗ[ℤ] (⋀[ℤ]^2 X)
    exact LinearEquiv.refl ℤ _

/-- The quotient map representing an oriented commutator followed by `q`
symmetric teeth. -/
abbrev commutatorClass (q : ℕ) :
    PreComponent X (Nat.succ q) →ₗ[ℤ] Component X (Nat.succ q) :=
  (LinearMap.range (jacobi X (Nat.succ q))).mkQ

/-- The universal degree-two commutator. -/
def generatorBracket : X →ₗ[ℤ] X →ₗ[ℤ] Component X 0 :=
  LinearMap.mk₂ ℤ
    (fun x y ↦ exteriorPower.ιMulti ℤ 2
      (Fin.cons x (Fin.cons y Fin.elim0)))
    (by
      intro x y z
      let v : Fin 2 → X := Fin.cons x (Fin.cons z Fin.elim0)
      have hvx : Function.update v 0 x = v := by
        funext i
        fin_cases i <;> rfl
      have hvy : Function.update v 0 y =
          Fin.cons y (Fin.cons z Fin.elim0) := by
        funext i
        fin_cases i <;> rfl
      have hvxy : Function.update v 0 (x + y) =
          Fin.cons (x + y) (Fin.cons z Fin.elim0) := by
        funext i
        fin_cases i <;> rfl
      simpa [hvx, hvy, hvxy] using
        (exteriorPower.ιMulti ℤ 2).map_update_add 0 x y (v := v))
    (by
      intro r x y
      let v : Fin 2 → X := Fin.cons x (Fin.cons y Fin.elim0)
      have hvx : Function.update v 0 x = v := by
        funext i
        fin_cases i <;> rfl
      have hvrx : Function.update v 0 (r • x) =
          Fin.cons (r • x) (Fin.cons y Fin.elim0) := by
        funext i
        fin_cases i <;> rfl
      simpa [hvx, hvrx] using
        (exteriorPower.ιMulti ℤ 2).map_update_smul 0 r x (v := v))
    (by
      intro x y z
      let v : Fin 2 → X := Fin.cons x (Fin.cons y Fin.elim0)
      have hvy : Function.update v 1 y = v := by
        funext i
        fin_cases i <;> rfl
      have hvz : Function.update v 1 z =
          Fin.cons x (Fin.cons z Fin.elim0) := by
        funext i
        fin_cases i <;> rfl
      have hvyz : Function.update v 1 (y + z) =
          Fin.cons x (Fin.cons (y + z) Fin.elim0) := by
        funext i
        fin_cases i <;> rfl
      simpa [hvy, hvz, hvyz] using
        (exteriorPower.ιMulti ℤ 2).map_update_add 1 y z (v := v))
    (by
      intro r x y
      let v : Fin 2 → X := Fin.cons x (Fin.cons y Fin.elim0)
      have hvy : Function.update v 1 y = v := by
        funext i
        fin_cases i <;> rfl
      have hvry : Function.update v 1 (r • y) =
          Fin.cons x (Fin.cons (r • y) Fin.elim0) := by
        funext i
        fin_cases i <;> rfl
      simpa [hvy, hvry] using
        (exteriorPower.ιMulti ℤ 2).map_update_smul 1 r y (v := v))

@[simp]
theorem generatorBracket_apply (x y : X) :
    generatorBracket X x y =
      exteriorPower.ιMulti ℤ 2 (Fin.cons x (Fin.cons y Fin.elim0)) := rfl

@[simp]
theorem generatorBracket_self (x : X) : generatorBracket X x x = 0 := by
  exact (exteriorPower.ιMulti ℤ 2).map_eq_zero_of_eq
    (Fin.cons x (Fin.cons x Fin.elim0)) (i := 0) (j := 1) rfl (by decide)

theorem generatorBracket_skew (x y : X) :
    generatorBracket X x y = -generatorBracket X y x := by
  have h := (exteriorPower.ιMulti ℤ 2).map_swap
    (v := Fin.cons y (Fin.cons x Fin.elim0))
    (i := 0) (j := 1) (by decide)
  exact h

namespace Action

/-- Multiply the symmetric part of a precomponent by one generator. -/
def pre (q : ℕ) (x : X) : PreComponent X q →ₗ[ℤ] PreComponent X (q + 1) :=
  TensorProduct.map LinearMap.id (SymmetricPower.insert ℤ X q x)

/-- The same operation on Jacobi sources. -/
def source (q : ℕ) (x : X) :
    JacobiSource X (q + 1) →ₗ[ℤ] JacobiSource X (q + 2) :=
  TensorProduct.map LinearMap.id (SymmetricPower.insert ℤ X q x)

@[simp]
theorem pre_tmul (q : ℕ) (x : X) (w : ⋀[ℤ]^2 X)
    (s : Sym[ℤ] (Fin q) X) :
    pre X q x (w ⊗ₜ[ℤ] s) =
      w ⊗ₜ[ℤ] SymmetricPower.insert ℤ X q x s := by
  change (TensorProduct.map LinearMap.id (SymmetricPower.insert ℤ X q x))
      (w ⊗ₜ[ℤ] s) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]

theorem pre_jacobi (q : ℕ) (x : X) :
    (pre X (q + 1) x).comp (jacobi X (q + 1)) =
      (jacobi X (q + 2)).comp (source X q x) := by
  apply TensorProduct.ext'
  intro w s
  let F : (⋀[ℤ]^3 X) →ₗ[ℤ] PreComponent X (q + 2) :=
    ((pre X (q + 1) x).comp (jacobi X (q + 1))).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^3 X) _).flip s)
  have hF : F = ((jacobi X (q + 2)).comp (source X q x)).comp
      ((TensorProduct.mk ℤ (⋀[ℤ]^3 X) _).flip s) := by
    apply exteriorPower.linearMap_ext
    ext a
    have hcomm (j : Fin 3) :
        SymmetricPower.insert ℤ X (q + 1) x
            (SymmetricPower.insert ℤ X q (a j) s) =
          SymmetricPower.insert ℤ X (q + 1) (a j)
            (SymmetricPower.insert ℤ X q x s) := by
      exact LinearMap.congr_fun
        (SymmetricPower.insert_comm ℤ X q x (a j)) s
    have hmid : pre X (q + 1) x
          (jacobi X (q + 1) (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] s)) =
        jacobi X (q + 2)
          (source X q x (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] s)) := by
      rw [jacobi_wedge_tmul, map_add, map_sub]
      simp only [pre_tmul, source]
      change _ = jacobi X (q + 2)
        (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ]
          SymmetricPower.insert ℤ X q x s)
      rw [jacobi_wedge_tmul]
      rw [hcomm 0, hcomm 1, hcomm 2]
    exact hmid
  exact LinearMap.congr_fun hF w

/-- The action of `X` on the weight-two component. -/
def zero (x : X) : Component X 0 →ₗ[ℤ] Component X 1 :=
  (commutatorClass X 0).comp
    ((TensorProduct.mk ℤ (⋀[ℤ]^2 X) (Sym[ℤ] (Fin 1) X)).flip
      (SymmetricPower.degreeOne (R := ℤ) x))

/-- The action in every higher component descends because multiplication
preserves the Jacobi image. -/
def succ (q : ℕ) (x : X) : Component X (q + 1) →ₗ[ℤ] Component X (q + 2) :=
  (LinearMap.range (jacobi X (q + 1))).mapQ
    (LinearMap.range (jacobi X (q + 2)))
    (pre X (q + 1) x) (by
      rintro y ⟨z, rfl⟩
      refine ⟨source X q x z, ?_⟩
      exact (LinearMap.congr_fun (pre_jacobi X q x) z).symm)

/-- Right action of a generator on every derived homogeneous component. -/
def apply : (q : ℕ) → X → Component X q →ₗ[ℤ] Component X (q + 1)
  | 0 => zero X
  | q + 1 => succ X q

theorem apply_add (q : ℕ) (x y : X) :
    apply X q (x + y) = apply X q x + apply X q y := by
  cases q with
  | zero =>
      apply LinearMap.ext
      intro w
      change (commutatorClass X 0)
          (w ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (x + y)) = _
      rw [map_add, tmul_add, map_add]
      rfl
  | succ q =>
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (jacobi X (q + 1))) z
      change (LinearMap.range (jacobi X (q + 2))).mkQ
          (pre X (q + 1) (x + y) w) = _
      rw [show pre X (q + 1) (x + y) =
          pre X (q + 1) x + pre X (q + 1) y by
        apply TensorProduct.ext'
        intro a s
        change a ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 1) (x + y) s =
          a ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 1) x s +
            a ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 1) y s
        rw [SymmetricPower.insert_add_apply, tmul_add]]
      rw [LinearMap.add_apply]
      rfl

theorem apply_smul (q : ℕ) (z : ℤ) (x : X) :
    apply X q (z • x) = z • apply X q x := by
  cases q with
  | zero =>
      apply LinearMap.ext
      intro w
      change (⋀[ℤ]^2 X) at w
      have hrhs : (z • apply X 0 x) w = z • apply X 0 x w :=
        AddMonoidHom.zsmul_apply (apply X 0 x).toAddMonoidHom z w
      change (commutatorClass X 0)
          (w ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) (z • x)) = _
      rw [map_zsmul]
      change (commutatorClass X 0)
        (w ⊗ₜ[ℤ] (z • SymmetricPower.degreeOne (R := ℤ) x)) = _
      rw [hrhs]
      change (commutatorClass X 0)
        (w ⊗ₜ[ℤ] (z • SymmetricPower.degreeOne (R := ℤ) x)) =
        z • (commutatorClass X 0)
          (w ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x)
      letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^2 X)
          (Sym[ℤ] (Fin 1) X) := TensorProduct.CompatibleSMul.int
      have ht :
          w ⊗ₜ[ℤ] (z • SymmetricPower.degreeOne (R := ℤ) x) =
            z • (w ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) := by
        calc
          w ⊗ₜ[ℤ] (z • SymmetricPower.degreeOne (R := ℤ) x) =
              (z • w) ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x :=
            (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) z _ _).symm
          _ = z • (w ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) :=
            (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) z _ _).symm
      calc
        (commutatorClass X 0)
            (w ⊗ₜ[ℤ] (z • SymmetricPower.degreeOne (R := ℤ) x)) =
            (commutatorClass X 0)
              (z • (w ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x)) :=
          congrArg (commutatorClass X 0) ht
        _ = z • (commutatorClass X 0)
              (w ⊗ₜ[ℤ] SymmetricPower.degreeOne (R := ℤ) x) := map_zsmul _ _ _
  | succ q =>
      apply LinearMap.ext
      intro y
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (jacobi X (q + 1))) y
      have hrhs :
          (z • apply X (q + 1) x)
              ((LinearMap.range (jacobi X (q + 1))).mkQ w) =
            z • apply X (q + 1) x
              ((LinearMap.range (jacobi X (q + 1))).mkQ w) :=
        AddMonoidHom.zsmul_apply (apply X (q + 1) x).toAddMonoidHom z _
      change (LinearMap.range (jacobi X (q + 2))).mkQ
          (pre X (q + 1) (z • x) w) = _
      have hpre : pre X (q + 1) (z • x) = z • pre X (q + 1) x := by
        apply TensorProduct.ext'
        intro a s
        change a ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 1) (z • x) s =
          z • (a ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 1) x s)
        rw [SymmetricPower.insert_smul_apply]
        letI : TensorProduct.CompatibleSMul ℤ ℤ (⋀[ℤ]^2 X)
            (Sym[ℤ] (Fin (q + 2)) X) := TensorProduct.CompatibleSMul.int
        calc
          a ⊗ₜ[ℤ] (z • SymmetricPower.insert ℤ X (q + 1) x s) =
              (z • a) ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 1) x s :=
            (TensorProduct.smul_tmul (R := ℤ) (R' := ℤ) z _ _).symm
          _ = z • (a ⊗ₜ[ℤ]
              SymmetricPower.insert ℤ X (q + 1) x s) :=
            (TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) z _ _).symm
      rw [hrhs]
      change (LinearMap.range (jacobi X (q + 2))).mkQ
          (pre X (q + 1) (z • x) w) =
        z • (LinearMap.range (jacobi X (q + 2))).mkQ
          (pre X (q + 1) x w)
      have hp : pre X (q + 1) (z • x) w =
          z • pre X (q + 1) x w := by
        calc
          pre X (q + 1) (z • x) w = (z • pre X (q + 1) x) w :=
            LinearMap.congr_fun hpre w
          _ = z • pre X (q + 1) x w :=
            AddMonoidHom.zsmul_apply (pre X (q + 1) x).toAddMonoidHom z w
      calc
        (LinearMap.range (jacobi X (q + 2))).mkQ
            (pre X (q + 1) (z • x) w) =
            (LinearMap.range (jacobi X (q + 2))).mkQ
              (z • pre X (q + 1) x w) := congrArg _ hp
        _ = z • (LinearMap.range (jacobi X (q + 2))).mkQ
              (pre X (q + 1) x w) := map_zsmul _ _ _

/-- Successive right actions commute.  This is the Jacobi identity with one
derived input and two degree-one inputs. -/
theorem apply_comm (q : ℕ) (x y : X) :
    (apply X (q + 1) y).comp (apply X q x) =
      (apply X (q + 1) x).comp (apply X q y) := by
  cases q with
  | zero =>
      apply LinearMap.ext
      intro w
      change (⋀[ℤ]^2 X) at w
      change (LinearMap.range (jacobi X 2)).mkQ
          (w ⊗ₜ[ℤ] SymmetricPower.insert ℤ X 1 y
            (SymmetricPower.degreeOne (R := ℤ) x)) =
        (LinearMap.range (jacobi X 2)).mkQ
          (w ⊗ₜ[ℤ] SymmetricPower.insert ℤ X 1 x
            (SymmetricPower.degreeOne (R := ℤ) y))
      apply congrArg (LinearMap.range (jacobi X 2)).mkQ
      apply congrArg (fun s => w ⊗ₜ[ℤ] s)
      let e0 : Sym[ℤ] (Fin 0) X :=
        SymmetricPower.tprod ℤ (fun i : Fin 0 => Fin.elim0 i)
      have hdegree (a : X) :
          SymmetricPower.insert ℤ X 0 a e0 =
            SymmetricPower.degreeOne (R := ℤ) a := by
        rw [SymmetricPower.degreeOne_apply,
          SymmetricPower.insert_tprod]
        apply congrArg (SymmetricPower.tprod ℤ)
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      have h := LinearMap.congr_fun
        (SymmetricPower.insert_comm ℤ X 0 y x) e0
      change SymmetricPower.insert ℤ X 1 y
          (SymmetricPower.insert ℤ X 0 x e0) =
        SymmetricPower.insert ℤ X 1 x
          (SymmetricPower.insert ℤ X 0 y e0) at h
      rw [hdegree x, hdegree y] at h
      exact h
  | succ q =>
      apply LinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (jacobi X (q + 1))) z
      change (LinearMap.range (jacobi X (q + 3))).mkQ
          (pre X (q + 2) y (pre X (q + 1) x w)) =
        (LinearMap.range (jacobi X (q + 3))).mkQ
          (pre X (q + 2) x (pre X (q + 1) y w))
      apply congrArg (LinearMap.range (jacobi X (q + 3))).mkQ
      have hpre :
          (pre X (q + 2) y).comp (pre X (q + 1) x) =
            (pre X (q + 2) x).comp (pre X (q + 1) y) := by
        apply TensorProduct.ext'
        intro a s
        change a ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 2) y
              (SymmetricPower.insert ℤ X (q + 1) x s) =
          a ⊗ₜ[ℤ] SymmetricPower.insert ℤ X (q + 2) x
              (SymmetricPower.insert ℤ X (q + 1) y s)
        exact congrArg (fun t => a ⊗ₜ[ℤ] t)
          (LinearMap.congr_fun
            (SymmetricPower.insert_comm ℤ X (q + 1) y x) s)
      exact LinearMap.congr_fun hpre w

/-- The weight-three Jacobi identity for the universal generator bracket. -/
theorem apply_generator_jacobi (x y z : X) :
    apply X 0 x (generatorBracket X y z) -
        apply X 0 y (generatorBracket X x z) +
      apply X 0 z (generatorBracket X x y) = 0 := by
  let a : Fin 3 → X :=
    Fin.cons x (Fin.cons y (Fin.cons z Fin.elim0))
  let e0 : Sym[ℤ] (Fin 0) X :=
    SymmetricPower.tprod ℤ (fun i : Fin 0 => Fin.elim0 i)
  have hdegree (t : X) :
      SymmetricPower.insert ℤ X 0 t e0 =
        SymmetricPower.degreeOne (R := ℤ) t := by
    rw [SymmetricPower.degreeOne_apply, SymmetricPower.insert_tprod]
    apply congrArg (SymmetricPower.tprod ℤ)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hj : (commutatorClass X 0)
      (jacobi X 1 (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] e0)) = 0 := by
    change (LinearMap.range (jacobi X 1)).mkQ
      (jacobi X 1 (exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] e0)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨exteriorPower.ιMulti ℤ 3 a ⊗ₜ[ℤ] e0, rfl⟩
  rw [jacobi_wedge_tmul, map_add, map_sub] at hj
  have hzero : (0 : Fin 3).removeNth a =
      Fin.cons y (Fin.cons z Fin.elim0) := by
    funext i
    fin_cases i <;> rfl
  have hone : (1 : Fin 3).removeNth a =
      Fin.cons x (Fin.cons z Fin.elim0) := by
    funext i
    fin_cases i <;> rfl
  have htwo : (2 : Fin 3).removeNth a =
      Fin.cons x (Fin.cons y Fin.elim0) := by
    funext i
    fin_cases i <;> rfl
  rw [hzero, hone, htwo,
    show a 0 = x by rfl, show a 1 = y by rfl, show a 2 = z by rfl,
    hdegree x, hdegree y, hdegree z] at hj
  exact hj

/-- The component action as a bilinear map. -/
def linear (q : ℕ) : X →ₗ[ℤ] Component X q →ₗ[ℤ] Component X (q + 1) where
  toFun := apply X q
  map_add' := apply_add X q
  map_smul' := apply_smul X q

@[simp]
theorem apply_zero (q : ℕ) : apply X q 0 = 0 := by
  exact map_zero (linear X q)

@[simp]
theorem apply_zero_apply (q : ℕ) (m : Component X q) :
    apply X q 0 m = 0 := by
  rw [apply_zero]
  rfl

end Action

end

end FreeMetabelian
