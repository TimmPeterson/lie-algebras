import LieRings.Plotkin.CentralPrime
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Util.AssertNoSorry

/-!
# Nilpotent associative targets and dimension subrings

This file formalizes the unitization argument in the proof of the zero-intersection lemma.  Its
main algebraic statement is slightly more general than the manuscript: a Lie map whose image lies
in a nilpotent two-sided ideal kills the corresponding dimension subring.  Taking the ideal to be
the nonunital summand in a unitization gives the manuscript verbatim.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

variable {K : Type u} [LieRing K]

-- Whenever the target is an associative ring, use its commutator Lie-algebra structure.  Raising
-- the existing instance's local priority avoids the competing generic integral `LieAlgebra`
-- instance while keeping the exact instance required by `UniversalEnvelopingAlgebra.lift`.
attribute [local instance 2000] LieAlgebra.ofAssociativeAlgebra

section NilpotentIdeal

variable {S : Type v} [Ring S] [Algebra ℤ S]

/-- The enveloping-algebra map induced by a Lie map to an associative algebra. -/
def associativeUEAMap (rho : K →ₗ⁅ℤ⁆ S) : UEA ℤ K →ₐ[ℤ] S :=
  UniversalEnvelopingAlgebra.lift ℤ rho

@[simp]
theorem associativeUEAMap_iota (rho : K →ₗ⁅ℤ⁆ S) (x : K) :
    associativeUEAMap rho (UniversalEnvelopingAlgebra.ι ℤ x) = rho x := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℤ rho x

/-- Modulo an ideal containing `rho(K)`, the induced enveloping map is just augmentation followed
by the scalar map. -/
theorem associativeUEAMap_sub_augmentation_mem
    (rho : K →ₗ⁅ℤ⁆ S) (J : Ideal S) [J.IsTwoSided]
    (hrho : ∀ x : K, rho x ∈ J) (u : UEA ℤ K) :
    associativeUEAMap rho u - algebraMap ℤ S (UEA.augmentation ℤ K u) ∈ J := by
  induction u using UEA.induction ℤ K with
  | algebraMap z => simp [associativeUEAMap]
  | ι x =>
      rw [associativeUEAMap_iota, UEA.augmentation_ι, map_zero, sub_zero]
      exact hrho x
  | add a b ha hb =>
      simpa only [map_add, add_sub_add_comm] using J.add_mem ha hb
  | mul a b ha hb =>
      have hleft : associativeUEAMap rho a *
          (associativeUEAMap rho b - algebraMap ℤ S (UEA.augmentation ℤ K b)) ∈ J :=
        J.mul_mem_left _ hb
      have hright :
          (associativeUEAMap rho a - algebraMap ℤ S (UEA.augmentation ℤ K a)) *
            algebraMap ℤ S (UEA.augmentation ℤ K b) ∈ J :=
        J.mul_mem_right _ ha
      convert J.add_mem hleft hright using 1 <;>
        simp only [map_mul] <;> noncomm_ring

theorem associativeUEAMap_mem_ideal
    (rho : K →ₗ⁅ℤ⁆ S) (J : Ideal S) [J.IsTwoSided]
    (hrho : ∀ x : K, rho x ∈ J) {u : UEA ℤ K}
    (hu : u ∈ UEA.augmentationIdeal ℤ K) :
    associativeUEAMap rho u ∈ J := by
  have h := associativeUEAMap_sub_augmentation_mem rho J hrho u
  rw [UEA.mem_augmentationIdeal] at hu
  simpa [hu] using h

/-- The induced enveloping map sends the `n`th augmentation power into the `n`th power of every
two-sided ideal containing the Lie image. -/
theorem associativeUEAMap_mem_ideal_pow
    (rho : K →ₗ⁅ℤ⁆ S) (J : Ideal S) [J.IsTwoSided]
    (hrho : ∀ x : K, rho x ∈ J) (n : ℕ) {u : UEA ℤ K}
    (hu : u ∈ UEA.augmentationIdeal ℤ K ^ n) :
    associativeUEAMap rho u ∈ J ^ n := by
  induction n generalizing u with
  | zero =>
      have hpow : J ^ 0 = (⊤ : Ideal S) := by simp
      rw [hpow]
      trivial
  | succ n ih =>
      rw [Ideal.IsTwoSided.pow_succ] at hu ⊢
      refine Submodule.mul_induction_on hu ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Ideal.mul_mem_mul (associativeUEAMap_mem_ideal rho J hrho ha) (ih hb)
      · intro a b ha hb
        rw [map_add]
        exact (J * J ^ n).add_mem ha hb

/-- A Lie map into a nilpotent ideal kills the dimension subring at the nilpotence exponent. -/
theorem lieHom_eq_zero_of_mem_dimensionSubring_of_ideal_pow_eq_bot
    (rho : K →ₗ⁅ℤ⁆ S) (J : Ideal S) [J.IsTwoSided]
    (hrho : ∀ x : K, rho x ∈ J) (N : ℕ) (hJ : J ^ N = ⊥)
    {x : K} (hx : x ∈ dimensionSubring ℤ K N) :
    rho x = 0 := by
  have hmap : associativeUEAMap rho (UniversalEnvelopingAlgebra.ι ℤ x) ∈ J ^ N :=
    associativeUEAMap_mem_ideal_pow rho J hrho N (mem_dimensionSubring ℤ K |>.mp hx)
  rw [hJ] at hmap
  rw [associativeUEAMap_iota] at hmap
  simpa using hmap

end NilpotentIdeal

/-! ## The literal nonunital-ring unitization -/

/-- Type synonym for the commutator Lie ring of a nonunital associative ring. -/
def NonUnitalCommutator (R : Type v) := R

namespace NonUnitalCommutator

variable (R : Type v) [NonUnitalRing R]

instance : NonUnitalRing (NonUnitalCommutator R) := inferInstanceAs (NonUnitalRing R)

instance : LieRing (NonUnitalCommutator R) where
  bracket x y := x * y - y * x
  add_lie := by intros; simp only [add_mul, mul_add]; abel
  lie_add := by intros; simp only [add_mul, mul_add]; abel
  lie_self := by intro; exact sub_self _
  leibniz_lie := by intros; simp only [mul_sub, sub_mul, mul_assoc]; abel

/-- The tautological integral linear equivalence with the underlying additive group. -/
def equiv : NonUnitalCommutator R ≃ₗ[ℤ] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end NonUnitalCommutator

section Unitization

variable {R : Type v} [NonUnitalRing R]

/-- Inclusion of a nonunital associative ring, with commutator bracket, into its unitization. -/
def nonUnitalCommutatorToUnitization :
    NonUnitalCommutator R →ₗ⁅ℤ⁆ Unitization ℤ R where
  toLinearMap := (Unitization.inrHom ℤ R).comp (NonUnitalCommutator.equiv R).toLinearMap
  map_lie' := by
    intro x y
    change (↑((show R from x) * (show R from y) - (show R from y) * (show R from x)) :
      Unitization ℤ R) =
      (↑(show R from x) * ↑(show R from y) - ↑(show R from y) * ↑(show R from x))
    simp

@[simp]
theorem nonUnitalCommutatorToUnitization_apply (x : NonUnitalCommutator R) :
    nonUnitalCommutatorToUnitization x =
      (↑(show R from x) : Unitization ℤ R) := rfl

/-- The nonunital summand in the unitization, expressed as a two-sided ideal. -/
def unitizationIdeal : Ideal (Unitization ℤ R) :=
  RingHom.ker (Unitization.fstHom ℤ R).toRingHom

instance unitizationIdeal_isTwoSided : (unitizationIdeal (R := R)).IsTwoSided :=
  inferInstanceAs (RingHom.ker (Unitization.fstHom ℤ R).toRingHom).IsTwoSided

@[simp]
theorem mem_unitizationIdeal_iff (x : Unitization ℤ R) :
    x ∈ unitizationIdeal (R := R) ↔ x.fst = 0 := by
  exact RingHom.mem_ker

theorem nonUnitalCommutatorToUnitization_mem (x : NonUnitalCommutator R) :
    nonUnitalCommutatorToUnitization x ∈ unitizationIdeal (R := R) := by
  rw [mem_unitizationIdeal_iff]
  rfl

/-- Ring-nilpotence for a nonunital ring, phrased intrinsically in its unitization: some power of
the nonunital summand is zero.  This is equivalent to the usual assertion that all sufficiently
long products in `R` vanish. -/
def IsNilpotentNonUnitalRing (R : Type v) [NonUnitalRing R] : Prop :=
  ∃ N : ℕ, unitizationIdeal (R := R) ^ N = ⊥

/-- The manuscript's unitization argument: a Lie map to the commutator Lie ring of a nilpotent
nonunital associative ring kills a finite dimension-subring term. -/
theorem exists_dimensionSubring_killed_by_nilpotent_nonUnitalRing
    (rho : K →ₗ⁅ℤ⁆ NonUnitalCommutator R)
    (hR : IsNilpotentNonUnitalRing R) :
    ∃ N : ℕ, ∀ x ∈ dimensionSubring ℤ K N, rho x = 0 := by
  obtain ⟨N, hN⟩ := hR
  let rho' : K →ₗ⁅ℤ⁆ Unitization ℤ R :=
    nonUnitalCommutatorToUnitization.comp rho
  refine ⟨N, fun x hx ↦ ?_⟩
  have hzero : rho' x = 0 :=
    lieHom_eq_zero_of_mem_dimensionSubring_of_ideal_pow_eq_bot rho'
      unitizationIdeal (fun y ↦ nonUnitalCommutatorToUnitization_mem (rho y)) N hN hx
  have hzeroR : (show R from rho x) = 0 := by
    apply (Unitization.inr_injective (R := ℤ) (A := R))
    simpa [rho'] using hzero
  exact hzeroR

end Unitization

/-! ## A compact interface for the separation theorem -/

/-- A representation of a Lie ring in a nilpotent two-sided ideal of an associative ring.
This is exactly the unitalized form of a representation in a nilpotent nonunital ring. -/
structure NilpotentIdealRepresentation (K : Type u) [LieRing K] where
  Target : Type u
  [targetRing : Ring Target]
  [targetAlgebra : Algebra ℤ Target]
  ideal : Ideal Target
  [idealTwoSided : ideal.IsTwoSided]
  exponent : ℕ
  ideal_pow_eq_bot : ideal ^ exponent = ⊥
  map : K →ₗ⁅ℤ⁆ Target
  map_mem : ∀ x : K, map x ∈ ideal

namespace NilpotentIdealRepresentation

instance (P : NilpotentIdealRepresentation K) : Ring P.Target := P.targetRing
instance (P : NilpotentIdealRepresentation K) : Algebra ℤ P.Target := P.targetAlgebra
instance (P : NilpotentIdealRepresentation K) : P.ideal.IsTwoSided := P.idealTwoSided

/-- Package a map into a nilpotent nonunital ring by adjoining an identity. -/
def ofNonUnital {R : Type u} [NonUnitalRing R]
    (rho : K →ₗ⁅ℤ⁆ NonUnitalCommutator R) (N : ℕ)
    (hN : unitizationIdeal (R := R) ^ N = ⊥) :
    NilpotentIdealRepresentation K where
  Target := Unitization ℤ R
  ideal := unitizationIdeal
  exponent := N
  ideal_pow_eq_bot := hN
  map := nonUnitalCommutatorToUnitization.comp rho
  map_mem x := nonUnitalCommutatorToUnitization_mem (rho x)

/-- Unitization preserves injectivity on every chosen subgroup. -/
theorem ofNonUnital_injective_on {R : Type u} [NonUnitalRing R]
    (rho : K →ₗ⁅ℤ⁆ NonUnitalCommutator R) (N : ℕ)
    (hN : unitizationIdeal (R := R) ^ N = ⊥) (A : LieIdeal ℤ K)
    (hinj : Function.Injective (fun a : A ↦ rho (a : K))) :
    Function.Injective
      (fun a : A ↦ (ofNonUnital rho N hN).map (a : K)) := by
  intro a b hab
  apply hinj
  apply (Unitization.inr_injective (R := ℤ) (A := R))
  exact hab

/-- Every represented element of the relevant dimension term is zero. -/
theorem map_eq_zero (P : NilpotentIdealRepresentation K) {x : K}
    (hx : x ∈ dimensionSubring ℤ K P.exponent) :
    P.map x = 0 :=
  lieHom_eq_zero_of_mem_dimensionSubring_of_ideal_pow_eq_bot
    P.map P.ideal P.map_mem P.exponent P.ideal_pow_eq_bot hx

end NilpotentIdealRepresentation

/-- The exact conditional form of central separation used by the zero-intersection argument. -/
abbrev HasCentralPrimeSeparation (K : Type u) [LieRing K] : Prop :=
  ∀ (p : ℕ) (A : LieIdeal ℤ K), p.Prime → Nat.card A = p →
    A ≤ LieAlgebra.center ℤ K →
    ∃ P : NilpotentIdealRepresentation K,
      Function.Injective (fun a : A ↦ P.map (a : K))

/-- **Zero intersection, conditional only on central separation.**  This is the direct consumer
for the separately constructed central-separation theorem; no separation hypothesis is hidden in
any preceding definition. -/
theorem dimensionSubringOmega_eq_bot_of_centralPrimeSeparation
    (hK : IsFinitelyGenerated K) (c : ℕ)
    (hclass : lowerCentralSeries ℤ K c = ⊥)
    (hsep : HasCentralPrimeSeparation K) :
    dimensionSubringOmega ℤ K = ⊥ := by
  by_contra homega
  obtain ⟨p, A, hp, hcard, hcentral, hAomega⟩ :=
    exists_central_prime_ideal_le_dimensionSubringOmega hK c hclass homega
  obtain ⟨P, hinj⟩ := hsep p A hp hcard hcentral
  have hzero (a : A) : P.map (a : K) = 0 := by
    apply P.map_eq_zero
    exact (mem_dimensionSubringOmega ℤ K).mp (hAomega a.2) P.exponent
  letI : Subsingleton A :=
    ⟨fun a b ↦ hinj (by
      change P.map (a : K) = P.map (b : K)
      rw [hzero a, hzero b])⟩
  have hcard_one : Nat.card A = 1 := Nat.card_unique
  rw [hcard] at hcard_one
  exact hp.ne_one hcard_one

end

end LieRings.Plotkin

assert_no_sorry LieRings.Plotkin.exists_dimensionSubring_killed_by_nilpotent_nonUnitalRing
assert_no_sorry LieRings.Plotkin.dimensionSubringOmega_eq_bot_of_centralPrimeSeparation
