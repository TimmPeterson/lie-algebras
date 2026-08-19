import LieRings.Homological.FirstDerivedSymmetricPower
import LieRings.Homological.QuadraticUCT

/-!
# The integral quadratic Bockstein

This is the deliberately small Bockstein API used by the metabelian
vanishing proof.  An integral lift of a `ZMod q` quadratic cocycle is recorded
only through the assertion that its value on every degree-two boundary is
zero modulo `q`.  Its character on degree-one homology is the literal value
of the lift divided by `q`, modulo the integers.
-/

namespace Koszul.QuadraticBockstein

noncomputable section

universe u v w z v₂ w₂

variable {A : Type u} [AddCommGroup A]
variable (P : Presentation.{u, v, w} A)

/-- An integral lift of a `ZMod q`-valued quadratic degree-one cocycle. -/
structure IntegralLift (q : ℕ) where
  cochain : One P 1 →ₗ[ℤ] ℤ
  boundary_zero : ∀ y : Two P 0,
    (cochain (dTwo P 0 y) : ZMod q) = 0

/-- Division by `q` over the rationals. -/
private def divideRat (q : ℕ) (hq : 0 < q) : ℤ →ₗ[ℤ] ℚ where
  toFun z := (z : ℚ) / (q : ℚ)
  map_add' := by intro x y; push_cast; ring
  map_smul' := by
    intro z x
    simp only [smul_eq_mul, Int.cast_mul, RingHom.id_apply]
    ring

/-- The Bockstein character represented by an integral cocycle lift. -/
def character (q : ℕ) (hq : 0 < q) (l : IntegralLift P q) :
    homologyOne P 1 →ₗ[ℤ] LieRings.RatCircle :=
  (boundariesOne P 1).liftQ
    ((QuadraticUCT.ratToCircle.comp
      ((divideRat q hq).comp l.cochain)).domRestrict (cyclesOne P 1)) (by
        rintro c ⟨y, rfl⟩
        change QuadraticUCT.ratToCircle
          ((l.cochain (dTwo P 0 y) : ℚ) / (q : ℚ)) = 0
        have hdvd : (q : ℤ) ∣ l.cochain (dTwo P 0 y) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact l.boundary_zero y
        obtain ⟨z, hz⟩ := hdvd
        rw [hz]
        have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
        rw [show (((q : ℤ) * z : ℤ) : ℚ) / (q : ℚ) = (z : ℚ) by
          push_cast
          field_simp]
        exact QuadraticUCT.ratToCircle_intCast z)

@[simp] theorem character_mk (q : ℕ) (hq : 0 < q)
    (l : IntegralLift P q) (c : cyclesOne P 1) :
    character P q hq l ((boundariesOne P 1).mkQ c) =
      (((l.cochain c.1 : ℚ) / (q : ℚ)) : LieRings.RatCircle) := by
  rfl

/-- The character does not depend on the integral lift of the same modular
cochain. -/
theorem character_eq_of_cast_eq (q : ℕ) (hq : 0 < q)
    (l l' : IntegralLift P q)
    (hcast : ∀ x, (l.cochain x : ZMod q) = (l'.cochain x : ZMod q)) :
    character P q hq l = character P q hq l' := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (boundariesOne P 1) x
  rw [character_mk, character_mk]
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  have hdvd : (q : ℤ) ∣ l.cochain c.1 - l'.cochain c.1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hcast, sub_self]
  obtain ⟨z, hz⟩ := hdvd
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  change QuadraticUCT.ratToCircle
    (((l.cochain c.1 : ℚ) / (q : ℚ)) -
      ((l'.cochain c.1 : ℚ) / (q : ℚ))) = 0
  rw [← sub_div, ← Int.cast_sub, hz, Int.cast_mul]
  rw [show (((q : ℤ) : ℚ) * (z : ℚ) / (q : ℚ)) = (z : ℚ) by
    field_simp
    norm_num
    exact mul_comm _ _]
  exact QuadraticUCT.ratToCircle_intCast z

variable {B : Type z} [AddCommGroup B]
variable (Q : Presentation.{z, v₂, w₂} B)
variable {f : A →ₗ[ℤ] B} (F : Presentation.Hom P Q f)

/-- Pull back an integral cocycle lift along a strict presentation map. -/
def pullback (q : ℕ) (l : IntegralLift Q q) : IntegralLift P q where
  cochain := l.cochain.comp (PresentationHomology.oneMap P Q F 1)
  boundary_zero y := by
    have hnat := LinearMap.congr_fun
      (PresentationHomology.dTwo_natural P Q F 0) y
    change (l.cochain (PresentationHomology.oneMap P Q F 1
      (dTwo P 0 y)) : ZMod q) = 0
    change (l.cochain (PresentationHomology.oneMap P Q F (0 + 1)
      (dTwo P 0 y)) : ZMod q) = 0
    have heq : PresentationHomology.oneMap P Q F (0 + 1)
        (dTwo P 0 y) =
      dTwo Q 0 (PresentationHomology.twoMap P Q F 0 y) := by
      simpa only [LinearMap.comp_apply] using hnat.symm
    rw [heq]
    exact l.boundary_zero (PresentationHomology.twoMap P Q F 0 y)

/-- Naturality of the explicit Bockstein character. -/
theorem character_pullback (q : ℕ) (hq : 0 < q)
    (l : IntegralLift Q q) :
    character P q hq (pullback P Q F q l) =
      (character Q q hq l).comp (PresentationHomology.map P Q F 1) := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (boundariesOne P 1) x
  rw [character_mk]
  change _ = character Q q hq l
    (PresentationHomology.map P Q F 1
      ((boundariesOne P 1).mkQ c))
  rw [PresentationHomology.map_mk, character_mk]
  rfl

/-- A modular coboundary has zero Bockstein character.  It is enough to
state the condition on cycles, which is exactly what a degree-zero cochain
gives after composing with `dOne`. -/
theorem character_eq_zero_of_cycles_cast_zero (q : ℕ) (hq : 0 < q)
    (l : IntegralLift P q)
    (hzero : ∀ c : cyclesOne P 1, (l.cochain c.1 : ZMod q) = 0) :
    character P q hq l = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (boundariesOne P 1) x
  rw [character_mk, LinearMap.zero_apply]
  have hdvd : (q : ℤ) ∣ l.cochain c.1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hzero c
  obtain ⟨z, hz⟩ := hdvd
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  change QuadraticUCT.ratToCircle
    ((l.cochain c.1 : ℚ) / (q : ℚ)) = 0
  rw [hz, Int.cast_mul]
  rw [show (((q : ℤ) : ℚ) * (z : ℚ) / (q : ℚ)) = (z : ℚ) by
    field_simp
    norm_num
    exact mul_comm _ _]
  exact QuadraticUCT.ratToCircle_intCast z


end

end Koszul.QuadraticBockstein
