import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.Ideal.Maps

/-!
# Universal enveloping algebras: basic infrastructure

This file keeps the definitions from mathlib and adds only the small pieces of infrastructure
needed by the Lie-ring library: an induction principle, the augmentation, and the augmentation
ideal.
-/

namespace LieRings

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A two-sided associative ideal, viewed as an ideal of the commutator Lie algebra. -/
def twoSidedIdealLieIdeal (A : Type*) [Ring A] [Algebra R A]
    (I : Ideal A) [I.IsTwoSided] : LieIdeal R A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' r x hx := by
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hx
  lie_mem {x m} hm := by
    rw [LieRing.of_associative_ring_bracket]
    exact I.sub_mem (I.mul_mem_left x hm) (I.mul_mem_right x hm)

@[simp]
theorem mem_twoSidedIdealLieIdeal (A : Type*) [Ring A] [Algebra R A]
    (I : Ideal A) [I.IsTwoSided] {x : A} :
    x ∈ twoSidedIdealLieIdeal R A I ↔ x ∈ I :=
  Iff.rfl

/-- A short local name for mathlib's universal enveloping algebra. -/
abbrev UEA := UniversalEnvelopingAlgebra R L

namespace UEA

/--
To prove a property of every element of `U(L)`, it is enough to prove it for scalars and for
the canonical images of elements of `L`, and to prove that it is closed under addition and
multiplication.
-/
@[elab_as_elim]
theorem induction {C : UEA R L → Prop}
    (algebraMap : ∀ r : R, C (algebraMap R (UEA R L) r))
    (ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (mul : ∀ a b, C a → C b → C (a * b))
    (add : ∀ a b, C a → C b → C (a + b))
    (a : UEA R L) : C a := by
  obtain ⟨t, rfl⟩ :=
    RingQuot.mkAlgHom_surjective R (UniversalEnvelopingAlgebra.Rel R L) a
  induction t using TensorAlgebra.induction with
  | algebraMap r => simpa using algebraMap r
  | ι x => simpa [UniversalEnvelopingAlgebra.ι] using ι x
  | mul x y hx hy => simpa using mul _ _ hx hy
  | add x y hx hy => simpa using add _ _ hx hy

/-- The augmentation `ε : U(L) →ₐ[R] R`, characterized by `ε(ι(x)) = 0`. -/
def augmentation : UEA R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

@[simp]
theorem augmentation_ι (x : L) :
    augmentation R L (UniversalEnvelopingAlgebra.ι R x) = 0 := by
  simp [augmentation]

@[simp]
theorem augmentation_algebraMap (r : R) :
    augmentation R L (algebraMap R (UEA R L) r) = r := by
  simp [augmentation]

/-- The augmentation ideal `ker ε` of `U(L)`. -/
def augmentationIdeal : Ideal (UEA R L) :=
  RingHom.ker (augmentation R L).toRingHom

instance augmentationIdeal_isTwoSided : (augmentationIdeal R L).IsTwoSided :=
  show (RingHom.ker (augmentation R L).toRingHom).IsTwoSided from inferInstance

@[simp]
theorem mem_augmentationIdeal {u : UEA R L} :
    u ∈ augmentationIdeal R L ↔ augmentation R L u = 0 :=
  RingHom.mem_ker

theorem ι_mem_augmentationIdeal (x : L) :
    UniversalEnvelopingAlgebra.ι R x ∈ augmentationIdeal R L := by
  rw [mem_augmentationIdeal]
  exact augmentation_ι R L x

end UEA

end LieRings
