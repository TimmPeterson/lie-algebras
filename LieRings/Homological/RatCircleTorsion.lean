import Mathlib.Algebra.Module.CharacterModule
import Mathlib.RingTheory.Finiteness.Prod

/-!
# The finite torsion in the rational circle

This neutral file contains the exact coefficient change used by the odd
dimension-subring proof.  It deliberately does not import a degree-five
argument.
-/

namespace LieRings

noncomputable section

/-- The additive rational circle `ℚ/ℤ`. -/
abbrev RatCircle := AddCircle (1 : ℚ)

/-- The standard embedding `ℤ/q → ℚ/ℤ`, sending `m` to `m/q`. -/
def zmodToRatCircle (q : ℕ) : ZMod q →+ RatCircle :=
  ZMod.lift q ⟨CharacterModule.int.divByNat q,
    CharacterModule.int.divByNat_self q⟩

@[simp]
theorem zmodToRatCircle_intCast (q : ℕ) (m : ℤ) :
    zmodToRatCircle q (m : ZMod q) =
      ((m : ℚ) / (q : ℚ) : RatCircle) := by
  rw [zmodToRatCircle, ZMod.lift_coe]
  rfl

/-- A `q`-torsion point of `ℚ/ℤ` has a canonical class modulo `q`. -/
def ratCircleTorsionToZMod {q : ℕ} (hq : 0 < q) (u : RatCircle)
    (hu : q • u = 0) : ZMod q :=
  ((AddCircle.nsmul_eq_zero_iff hq).mp hu).choose

theorem zmodToRatCircle_torsionToZMod {q : ℕ} (hq : 0 < q)
    (u : RatCircle) (hu : q • u = 0) :
    zmodToRatCircle q (ratCircleTorsionToZMod hq u hu) = u := by
  let hex := (AddCircle.nsmul_eq_zero_iff hq).mp hu
  let m : ℕ := hex.choose
  have hm : (((m : ℚ) / (q : ℚ) : ℚ) : RatCircle) = u := by
    dsimp only [m]
    simpa only [mul_one] using hex.choose_spec.2
  change zmodToRatCircle q (m : ZMod q) = u
  calc
    zmodToRatCircle q (m : ZMod q) =
        zmodToRatCircle q ((m : ℤ) : ZMod q) := by norm_num
    _ = (((m : ℤ) : ℚ) / (q : ℚ) : RatCircle) :=
      zmodToRatCircle_intCast q (m : ℤ)
    _ = u := by simpa using hm

theorem zmodToRatCircle_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (zmodToRatCircle q) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  ext a
  constructor
  · intro ha
    rw [AddSubgroup.mem_bot]
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
    change zmodToRatCircle q (m : ZMod q) = 0 at ha
    rw [zmodToRatCircle_intCast] at ha
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℚ))).mp ha
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hmQ : (m : ℚ) = (q : ℚ) * (z : ℚ) := by
      simp only [zsmul_eq_mul, mul_one] at hz
      field_simp at hz ⊢
      linarith
    have hmZ : m = (q : ℤ) * z := by exact_mod_cast hmQ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨z, hmZ⟩
  · intro ha
    change zmodToRatCircle q a = 0
    rw [ha, map_zero]

/-- Convert one character on a group annihilated by `q` from `ℚ/ℤ` to
`ℤ/q`. -/
def ratCircleTorsionCharacterToZMod {X : Type*} [AddCommGroup X]
    {q : ℕ} (hq : 0 < q) (hX : ∀ x : X, q • x = 0)
    (f : X →ₗ[ℤ] RatCircle) : X →ₗ[ℤ] ZMod q :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x ↦ ratCircleTorsionToZMod hq (f x) (by
          rw [← map_nsmul, hX, map_zero])
      map_zero' := by
        apply zmodToRatCircle_injective hq
        rw [zmodToRatCircle_torsionToZMod, map_zero, map_zero]
      map_add' := by
        intro x y
        apply zmodToRatCircle_injective hq
        rw [zmodToRatCircle_torsionToZMod,
          map_add, map_add,
          zmodToRatCircle_torsionToZMod,
          zmodToRatCircle_torsionToZMod] }

@[simp] theorem zmodToRatCircle_torsionCharacterToZMod
    {X : Type*} [AddCommGroup X] {q : ℕ} (hq : 0 < q)
    (hX : ∀ x : X, q • x = 0) (f : X →ₗ[ℤ] RatCircle) (x : X) :
    zmodToRatCircle q (ratCircleTorsionCharacterToZMod hq hX f x) = f x :=
  zmodToRatCircle_torsionToZMod hq _ (by rw [← map_nsmul, hX, map_zero])

/-- Linear form of the torsion-coordinate equivalence used in the quadratic
certificate. -/
def ratCircleTorsionLinearMapToZMod {X : Type*} [AddCommGroup X]
    {q : ℕ} (hq : 0 < q) (hX : ∀ x : X, q • x = 0) :
    (X →ₗ[ℤ] RatCircle) →ₗ[ℤ] (X →ₗ[ℤ] ZMod q) where
  toFun := ratCircleTorsionCharacterToZMod hq hX
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro x
    apply zmodToRatCircle_injective hq
    simp
  map_smul' := by
    intro z f
    apply LinearMap.ext
    intro x
    apply zmodToRatCircle_injective hq
    change zmodToRatCircle q
        (ratCircleTorsionCharacterToZMod hq hX (z • f) x) =
      zmodToRatCircle q
        (z • ratCircleTorsionCharacterToZMod hq hX f x)
    rw [zmodToRatCircle_torsionCharacterToZMod,
      map_zsmul, zmodToRatCircle_torsionCharacterToZMod]
    rfl

@[simp] theorem zmodToRatCircle_torsionLinearMapToZMod
    {X : Type*} [AddCommGroup X] {q : ℕ} (hq : 0 < q)
    (hX : ∀ x : X, q • x = 0) (f : X →ₗ[ℤ] RatCircle) (x : X) :
    zmodToRatCircle q (ratCircleTorsionLinearMapToZMod hq hX f x) = f x :=
  zmodToRatCircle_torsionCharacterToZMod hq hX f x

end

end LieRings
