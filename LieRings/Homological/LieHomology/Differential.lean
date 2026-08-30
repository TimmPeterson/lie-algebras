import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Tactic

/-!
# The Chevalley--Eilenberg boundary

This file constructs the boundary on the exterior algebra of a Lie algebra.  The construction is
valid over an arbitrary commutative ring; in particular, it never divides by a factorial or by
two.

For `x : L` let `adExterior R L x` be the degree-preserving derivation of `ExteriorAlgebra R L`
induced by `y ↦ ⁅x, y⁆`.  The Chevalley--Eilenberg boundary is characterized by

`boundary (ι x * u) = adExterior R L x u - ι x * boundary u`.

Mathlib implements the exterior algebra as the Clifford algebra for the zero quadratic form.
`CliffordAlgebra.foldr'` is therefore exactly the quotient recursion needed to construct both
operators.  The square-zero theorem is proved from the Jacobi identity, not imposed as data.
-/

namespace LieRings.Homological.LieHomology

universe u v w

noncomputable section

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

private abbrev EA := ExteriorAlgebra R L

/-! ## The adjoint derivation on the exterior algebra -/

/-- One recursion step for the derivation of the exterior algebra induced by `ad x`.

The state is `(u, A u)`.  On prepending `y`, it becomes
`(ι y * u, ι ⁅x,y⁆ * u + ι y * A u)`; `foldr'` stores the first component itself. -/
private def adjointStep (x : L) :
    L →ₗ[R] (EA R L × EA R L) →ₗ[R] EA R L :=
  LinearMap.mk₂ R
    (fun y p ↦ ExteriorAlgebra.ι R ⁅x, y⁆ * p.1 + ExteriorAlgebra.ι R y * p.2)
    (by
      intro y z p
      simp only [lie_add, map_add, add_mul]
      abel)
    (by
      intro c y p
      simp only [lie_smul, map_smul, smul_mul_assoc]
      rw [smul_add])
    (by
      intro y p q
      simp only [Prod.fst_add, Prod.snd_add, mul_add]
      abel)
    (by
      intro c y p
      simp only [Prod.smul_fst, Prod.smul_snd, mul_smul_comm, smul_add])

@[simp]
private theorem adjointStep_apply (x y : L) (p : EA R L × EA R L) :
    adjointStep R L x y p =
      ExteriorAlgebra.ι R ⁅x, y⁆ * p.1 + ExteriorAlgebra.ι R y * p.2 :=
  rfl

private theorem adjointStep_square (x y : L) (u au : EA R L) :
    adjointStep R L x y
        (ExteriorAlgebra.ι R y * u, adjointStep R L x y (u, au)) = 0 := by
  simp only [adjointStep_apply, Prod.fst, Prod.snd]
  have hanti := ExteriorAlgebra.ι_add_mul_swap (R := R) ⁅x, y⁆ y
  have hsq := ExteriorAlgebra.ι_sq_zero (R := R) y
  calc
    _ = (ExteriorAlgebra.ι R ⁅x, y⁆ * ExteriorAlgebra.ι R y +
          ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R ⁅x, y⁆) * u +
        (ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R y) * au := by
      noncomm_ring
    _ = 0 := by rw [hanti, hsq, zero_mul, zero_add, zero_mul]

/-- The degree-preserving endomorphism of the exterior algebra induced by `ad x`.

It is bundled below as a linear map in `x`; this raw version makes the quotient recursion
transparent. -/
private def adExteriorRaw (x : L) : EA R L →ₗ[R] EA R L :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (adjointStep R L x)
    (by
      intro y u au
      simpa using adjointStep_square R L x y u au)
    0

@[simp]
private theorem adExteriorRaw_algebraMap (x : L) (r : R) :
    adExteriorRaw R L x (algebraMap R (EA R L) r) = 0 := by
  unfold adExteriorRaw
  rw [CliffordAlgebra.foldr'_algebraMap]
  exact smul_zero r

@[simp]
private theorem adExteriorRaw_ι_mul (x y : L) (u : EA R L) :
    adExteriorRaw R L x (ExteriorAlgebra.ι R y * u) =
      ExteriorAlgebra.ι R ⁅x, y⁆ * u +
        ExteriorAlgebra.ι R y * adExteriorRaw R L x u := by
  unfold adExteriorRaw
  rw [CliffordAlgebra.foldr'_ι_mul]
  rfl

private theorem adExteriorRaw_add (x y : L) :
    adExteriorRaw R L (x + y) = adExteriorRaw R L x + adExteriorRaw R L y := by
  apply LinearMap.ext
  intro u
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | ι_mul u z hu =>
      simp only [adExteriorRaw_ι_mul, add_lie, map_add, add_mul, LinearMap.add_apply, hu,
        mul_add]
      abel

private theorem adExteriorRaw_smul (c : R) (x : L) :
    adExteriorRaw R L (c • x) = c • adExteriorRaw R L x := by
  apply LinearMap.ext
  intro u
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, LinearMap.smul_apply, hu, hv, smul_add]
  | ι_mul u y hu =>
      simp only [adExteriorRaw_ι_mul, smul_lie, map_smul, smul_mul_assoc,
        LinearMap.smul_apply, hu, smul_add, mul_smul_comm]

/-- The adjoint action of a Lie algebra on its exterior algebra.

For each `x`, this is the derivation extending `y ↦ ⁅x,y⁆`. -/
def adExterior : L →ₗ[R] Module.End R (EA R L) where
  toFun := adExteriorRaw R L
  map_add' := adExteriorRaw_add R L
  map_smul' := adExteriorRaw_smul R L

@[simp]
theorem adExterior_algebraMap (x : L) (r : R) :
    adExterior R L x (algebraMap R (EA R L) r) = 0 :=
  adExteriorRaw_algebraMap R L x r

@[simp]
theorem adExterior_ι_mul (x y : L) (u : EA R L) :
    adExterior R L x (ExteriorAlgebra.ι R y * u) =
      ExteriorAlgebra.ι R ⁅x, y⁆ * u +
        ExteriorAlgebra.ι R y * adExterior R L x u :=
  adExteriorRaw_ι_mul R L x y u

@[simp]
theorem adExterior_ι (x y : L) :
    adExterior R L x (ExteriorAlgebra.ι R y) = ExteriorAlgebra.ι R ⁅x, y⁆ := by
  rw [show ExteriorAlgebra.ι R y = ExteriorAlgebra.ι R y * 1 by simp,
    adExterior_ι_mul]
  have hone : adExterior R L x (1 : EA R L) = 0 := by
    simpa using adExterior_algebraMap R L x 1
  rw [hone]
  simp

/-- `adExterior x` satisfies the Leibniz rule. -/
theorem adExterior_mul (x : L) (u v : EA R L) :
    adExterior R L x (u * v) =
      adExterior R L x u * v + u * adExterior R L x v := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [← Algebra.smul_def, map_smul, adExterior_algebraMap, zero_mul,
        Algebra.smul_def, zero_add]
  | add u w hu hw =>
      simp only [add_mul, map_add, hu, hw, mul_add]
      abel
  | ι_mul u y hu =>
      simp only [mul_assoc, adExterior_ι_mul, hu, mul_add]
      noncomm_ring

/-- The induced exterior derivations form the adjoint representation. -/
theorem adExterior_lie (x y : L) :
    adExterior R L ⁅x, y⁆ =
      (adExterior R L x).comp (adExterior R L y) -
        (adExterior R L y).comp (adExterior R L x) := by
  apply LinearMap.ext
  intro u
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, LinearMap.sub_apply, hu, hv]
  | ι_mul u z hu =>
      simp only [adExterior_ι_mul, LinearMap.sub_apply, LinearMap.comp_apply, map_add,
        hu, mul_add]
      have hj := leibniz_lie x y z
      have hj' :
          ExteriorAlgebra.ι R ⁅⁅x, y⁆, z⁆ =
            ExteriorAlgebra.ι R ⁅x, ⁅y, z⁆⁆ - ExteriorAlgebra.ι R ⁅y, ⁅x, z⁆⁆ := by
        have h := congrArg (ExteriorAlgebra.ι R) hj
        simp only [map_add] at h
        rw [h]
        abel
      rw [hj']
      noncomm_ring

/-! ## The boundary on the exterior algebra -/

/-- One recursion step for the Chevalley--Eilenberg boundary.  The state is `(u, ∂u)`. -/
private def boundaryStep :
    L →ₗ[R] (EA R L × EA R L) →ₗ[R] EA R L :=
  LinearMap.mk₂ R
    (fun x p ↦ adExterior R L x p.1 - ExteriorAlgebra.ι R x * p.2)
    (by
      intro x y p
      simp only [map_add, LinearMap.add_apply, Prod.fst, Prod.snd, mul_add, add_mul]
      abel)
    (by
      intro c x p
      simp only [map_smul, LinearMap.smul_apply, Prod.fst, Prod.snd, map_smul,
        smul_mul_assoc, smul_sub])
    (by
      intro x p q
      simp only [Prod.fst_add, Prod.snd_add, map_add, mul_add, sub_add_sub_comm])
    (by
      intro c x p
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, mul_smul_comm, smul_sub])

@[simp]
private theorem boundaryStep_apply (x : L) (p : EA R L × EA R L) :
    boundaryStep R L x p =
      adExterior R L x p.1 - ExteriorAlgebra.ι R x * p.2 :=
  rfl

private theorem boundaryStep_square (x : L) (u du : EA R L) :
    boundaryStep R L x
        (ExteriorAlgebra.ι R x * u, boundaryStep R L x (u, du)) = 0 := by
  simp only [boundaryStep_apply, Prod.fst, Prod.snd, adExterior_mul, adExterior_ι,
    lie_self, map_zero, zero_mul, zero_add, mul_sub]
  have hsq := ExteriorAlgebra.ι_sq_zero (R := R) x
  rw [← mul_assoc, hsq, zero_mul]
  simp

/-- The Chevalley--Eilenberg boundary on the whole exterior algebra.

Its restriction from `⋀^(n+1) L` to `⋀^n L` is defined below. -/
def boundary : EA R L →ₗ[R] EA R L :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (boundaryStep R L)
    (by
      intro x u du
      simpa using boundaryStep_square R L x u du)
    0

@[simp]
theorem boundary_algebraMap (r : R) :
    boundary R L (algebraMap R (EA R L) r) = 0 := by
  unfold boundary
  rw [CliffordAlgebra.foldr'_algebraMap]
  exact smul_zero r

@[simp]
theorem boundary_ι_mul (x : L) (u : EA R L) :
    boundary R L (ExteriorAlgebra.ι R x * u) =
      adExterior R L x u - ExteriorAlgebra.ι R x * boundary R L u := by
  unfold boundary
  rw [CliffordAlgebra.foldr'_ι_mul]
  rfl

@[simp]
theorem boundary_ι (x : L) : boundary R L (ExteriorAlgebra.ι R x) = 0 := by
  rw [show ExteriorAlgebra.ι R x = ExteriorAlgebra.ι R x * 1 by simp,
    boundary_ι_mul]
  have ha : adExterior R L x (1 : EA R L) = 0 := by
    simpa using adExterior_algebraMap R L x 1
  have hb : boundary R L (1 : EA R L) = 0 := by
    simpa using boundary_algebraMap R L 1
  rw [ha, hb]
  simp

/-- The CE boundary commutes with every induced adjoint derivation. -/
theorem boundary_adExterior (x : L) (u : EA R L) :
    boundary R L (adExterior R L x u) = adExterior R L x (boundary R L u) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu =>
      simp only [adExterior_ι_mul, map_add, boundary_ι_mul, adExterior_mul,
        adExterior_ι, hu, map_sub, mul_sub]
      have hrep := LinearMap.congr_fun (adExterior_lie R L x y) u
      simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hrep
      rw [hrep]
      abel

/-- The Chevalley--Eilenberg boundary squares to zero on the exterior algebra. -/
theorem boundary_boundary (u : EA R L) :
    boundary R L (boundary R L u) = 0 := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]
  | ι_mul u x hu =>
      simp only [boundary_ι_mul, map_sub, boundary_adExterior, hu, mul_zero, sub_zero,
        sub_self]

/-! ## Homogeneous restrictions -/

/-- The exterior adjoint action preserves every homogeneous exterior power. -/
theorem adExterior_mem_exteriorPower (x : L) {n : ℕ} {u : EA R L}
    (hu : u ∈ (⋀[R]^n L)) : adExterior R L x u ∈ (⋀[R]^n L) := by
  induction hu using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add u v i hu hv hAu hAv =>
      simpa only [map_add] using Submodule.add_mem (⋀[R]^i L) hAu hAv
  | mem_mul m hm i u hu hAu =>
      obtain ⟨y, rfl⟩ := hm
      rw [adExterior_ι_mul]
      apply Submodule.add_mem
      · simpa only [Nat.one_add] using
          (SetLike.mul_mem_graded
            (show ExteriorAlgebra.ι R ⁅x, y⁆ ∈ (⋀[R]^1 L) by
              simpa only [pow_one] using
                LinearMap.mem_range_self (ExteriorAlgebra.ι R) ⁅x, y⁆)
            hu)
      · simpa only [Nat.one_add] using
          (SetLike.mul_mem_graded
            (show ExteriorAlgebra.ι R y ∈ (⋀[R]^1 L) by
              simpa only [pow_one] using
                LinearMap.mem_range_self (ExteriorAlgebra.ι R) y)
            hAu)

/-- The adjoint exterior derivation vanishes in exterior degree zero. -/
theorem adExterior_eq_zero_of_mem_exteriorPower_zero (x : L) {u : EA R L}
    (hu : u ∈ (⋀[R]^0 L)) : adExterior R L x u = 0 := by
  change u ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ 0 at hu
  rw [pow_zero] at hu
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hu
  exact adExterior_algebraMap R L x r

/-- The boundary vanishes in exterior degree zero. -/
theorem boundary_eq_zero_of_mem_exteriorPower_zero {u : EA R L}
    (hu : u ∈ (⋀[R]^0 L)) : boundary R L u = 0 := by
  change u ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ 0 at hu
  rw [pow_zero] at hu
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hu
  exact boundary_algebraMap R L r

/-- The boundary lowers exterior degree by one.  Degree zero is sent to zero. -/
theorem boundary_mem_exteriorPower {n : ℕ} {u : EA R L}
    (hu : u ∈ (⋀[R]^n L)) : boundary R L u ∈ (⋀[R]^(n - 1) L) := by
  induction hu using Submodule.pow_induction_on_left' with
  | algebraMap r => simpa using (Submodule.zero_mem (⋀[R]^0 L))
  | add u v i hu hv hdu hdv =>
      simpa only [map_add] using Submodule.add_mem (⋀[R]^(i - 1) L) hdu hdv
  | mem_mul m hm i u hu hdu =>
      obtain ⟨x, rfl⟩ := hm
      rw [boundary_ι_mul]
      cases i with
      | zero =>
          rw [adExterior_eq_zero_of_mem_exteriorPower_zero R L x hu,
            boundary_eq_zero_of_mem_exteriorPower_zero R L hu, mul_zero, sub_zero]
          exact Submodule.zero_mem _
      | succ i =>
          apply Submodule.sub_mem
          · exact adExterior_mem_exteriorPower R L x hu
          · simpa only [Nat.succ_sub_one, Nat.one_add] using
              (SetLike.mul_mem_graded
                (show ExteriorAlgebra.ι R x ∈ (⋀[R]^1 L) by
                  simpa only [pow_one] using
                    LinearMap.mem_range_self (ExteriorAlgebra.ι R) x)
                hdu)

/-- The degree `n + 1` Chevalley--Eilenberg differential with the sign convention of the
supplied manuscript.  Thus `d₂(x ∧ y) = -⁅x,y⁆`; changing every differential by a global minus
sign gives the other common convention and does not change homology. -/
def differential (n : ℕ) : (⋀[R]^(n + 1) L) →ₗ[R] (⋀[R]^n L) where
  toFun u := ⟨-boundary R L (u : EA R L), by
    simpa using (boundary_mem_exteriorPower R L u.property)⟩
  map_add' u v := by
    apply Subtype.ext
    simp
    abel
  map_smul' r u := by
    apply Subtype.ext
    simp

@[simp]
theorem differential_coe (n : ℕ) (u : ⋀[R]^(n + 1) L) :
    ((differential R L n u : ⋀[R]^n L) : EA R L) = -boundary R L (u : EA R L) :=
  rfl

/-- Consecutive homogeneous CE differentials compose to zero. -/
theorem differential_comp_differential (n : ℕ) :
    (differential R L n).comp (differential R L (n + 1)) = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  simp only [LinearMap.comp_apply, differential_coe, map_neg, neg_neg, LinearMap.zero_apply,
    Submodule.coe_zero]
  exact boundary_boundary R L (u : EA R L)

/-- The degree-one differential is zero. -/
theorem differential_zero : differential R L 0 = 0 := by
  apply exteriorPower.linearMap_ext
  ext a
  change ((differential R L 0 (exteriorPower.ιMulti R 1 a) : ⋀[R]^0 L) : EA R L) = 0
  rw [differential_coe]
  change -boundary R L (ExteriorAlgebra.ιMulti R 1 a) = 0
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp

/-! ## Naturality -/

variable {K : Type w} [LieRing K] [LieAlgebra R K]

/-- Exterior-algebra maps commute with the induced adjoint derivations. -/
theorem map_adExterior (f : LieHom R L K) (x : L) (u : EA R L) :
    ExteriorAlgebra.map f.toLinearMap (adExterior R L x u) =
      adExterior R K (f x) (ExteriorAlgebra.map f.toLinearMap u) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu =>
      simp only [adExterior_ι_mul, map_add, map_mul, ExteriorAlgebra.map_apply_ι,
        hu]
      have hxy : f.toLinearMap ⁅x, y⁆ = ⁅f x, f y⁆ := by
        simpa only [LieHom.coe_toLinearMap] using f.map_lie x y
      have hy : f.toLinearMap y = f y := congrFun (LieHom.coe_toLinearMap f) y
      rw [hxy]
      rw [hy]

/-- Exterior-algebra maps commute with the CE boundary. -/
theorem map_boundary (f : LieHom R L K) (u : EA R L) :
    ExteriorAlgebra.map f.toLinearMap (boundary R L u) =
      boundary R K (ExteriorAlgebra.map f.toLinearMap u) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u x hu =>
      simp only [boundary_ι_mul, map_sub, map_mul, ExteriorAlgebra.map_apply_ι,
        map_adExterior, hu]
      rfl

/-- The map on exterior powers is literally the restriction of the map on exterior algebras. -/
theorem exteriorPower_map_coe (f : L →ₗ[R] K) (n : ℕ) (u : ⋀[R]^n L) :
    ((exteriorPower.map n f u : ⋀[R]^n K) : EA R K) =
      ExteriorAlgebra.map f (u : EA R L) := by
  let left : (⋀[R]^n L) →ₗ[R] EA R K :=
    (⋀[R]^n K).subtype.comp (exteriorPower.map n f)
  let right : (⋀[R]^n L) →ₗ[R] EA R K :=
    (ExteriorAlgebra.map f).toLinearMap.comp (⋀[R]^n L).subtype
  have h : left = right := by
    apply exteriorPower.linearMap_ext
    ext a
    simp [left, right]
  exact LinearMap.congr_fun h u

/-- Naturality of the homogeneous CE differential. -/
theorem differential_natural (f : LieHom R L K) (n : ℕ) :
    (exteriorPower.map n f.toLinearMap).comp (differential R L n) =
      (differential R K n).comp (exteriorPower.map (n + 1) f.toLinearMap) := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    exteriorPower_map_coe, differential_coe, differential_coe,
    exteriorPower_map_coe]
  rw [map_neg, map_boundary]

/-- Pointwise form of `differential_natural`, avoiding any need for clients to unfold
composition of linear maps. -/
theorem differential_natural_apply (f : LieHom R L K) (n : ℕ)
    (x : ⋀[R]^(n + 1) L) :
    exteriorPower.map n f.toLinearMap (differential R L n x) =
      differential R K n (exteriorPower.map (n + 1) f.toLinearMap x) := by
  simpa only [LinearMap.comp_apply] using LinearMap.congr_fun (differential_natural R L f n) x

end

end LieRings.Homological.LieHomology
