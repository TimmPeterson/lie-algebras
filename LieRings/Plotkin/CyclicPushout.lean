import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Extension
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Module.Projective
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic
import Mathlib.Util.AssertNoSorry

/-!
# Finite cyclic pushouts of central prime-order ideals

This file formalizes the finite cyclic pushout used in the Plotkin separation
argument. The elementary pushout is developed first for an additive map
from K to D which is injective on the central ideal. If the central ideal has
prime order and the quotient is additively finitely generated, residual
finiteness of finitely generated Abelian groups supplies such a map with
finite cyclic codomain. The ambient Lie ring itself need not be finite.
-/

namespace LieRings.Plotkin

noncomputable section

universe u v

/-! ## An additive group with the zero Lie bracket -/

/-- A type synonym carrying the zero Lie bracket on an additive group. -/
def TrivialLieRing (D : Type u) := D

namespace TrivialLieRing

variable (D : Type u) [AddCommGroup D]

instance : AddCommGroup (TrivialLieRing D) := inferInstanceAs (AddCommGroup D)

instance [Finite D] : Finite (TrivialLieRing D) := inferInstanceAs (Finite D)

instance [IsAddCyclic D] : IsAddCyclic (TrivialLieRing D) :=
  inferInstanceAs (IsAddCyclic D)

instance : LieRing (TrivialLieRing D) where
  bracket _ _ := 0
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

/-- The tautological integral linear equivalence with the underlying group. -/
def equiv : TrivialLieRing D ≃ₗ[ℤ] D where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem equiv_apply (d : TrivialLieRing D) : equiv D d = d := rfl

@[simp]
theorem equiv_symm_apply (d : D) : (equiv D).symm d = d := rfl

end TrivialLieRing

/-! ## A finite cyclic target detected by a character -/

/-- The additive group underlying the image of a finite-group character. -/
abbrev CharacterRange {G : Type u} [AddCommGroup G]
    (φ : Multiplicative G →* ℂˣ) :=
  Additive (MonoidHom.range φ)

namespace CharacterRange

variable {G : Type u} [AddCommGroup G]
variable (φ : Multiplicative G →* ℂˣ)

/-- The character with its codomain restricted to its image, written
additively and hence as an integral linear map. -/
def linearMap : G →ₗ[ℤ] CharacterRange φ :=
  φ.rangeRestrict.toAdditive.toIntLinearMap

@[simp]
theorem linearMap_apply (g : G) :
    ((linearMap φ g).toMul : ℂˣ) = φ (.ofAdd g) :=
  rfl

instance [Finite G] : Finite (CharacterRange φ) :=
  Finite.of_surjective (linearMap φ)
    (by
      intro z
      obtain ⟨g, hg⟩ := MonoidHom.rangeRestrict_surjective φ z.toMul
      exact ⟨g.toAdd, Additive.toMul.injective hg⟩)

instance [Finite G] : IsAddCyclic (CharacterRange φ) := by
  rw [isAddCyclic_additive_iff]
  letI : Finite (MonoidHom.range φ) :=
    Finite.of_surjective φ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective φ)
  refine isCyclic_of_injective_ringHom
    ({ toFun := fun z : MonoidHom.range φ ↦ (z.1 : ℂˣ)
       map_one' := rfl
       map_mul' := by intro x y; rfl } : MonoidHom.range φ →* ℂ) ?_
  intro x y h
  exact Subtype.ext (Units.ext h)

end CharacterRange

/-- A homomorphism out of an additive group of prime cardinality is
injective as soon as it is nonzero on one nonzero element. -/
private theorem linearMap_injective_of_prime_card
    {G : Type u} [AddCommGroup G] [Finite G]
    {D : Type v} [AddCommGroup D]
    (f : G →ₗ[ℤ] D) (hprime : (Nat.card G).Prime)
    {a : G} (hfa : f a ≠ 0) :
    Function.Injective f := by
  letI : Fact (Nat.card G).Prime := ⟨hprime⟩
  rcases f.toAddMonoidHom.ker.eq_bot_or_eq_top_of_prime_card with hker | hker
  · exact (AddMonoidHom.ker_eq_bot_iff f.toAddMonoidHom).mp hker
  · exfalso
    apply hfa
    have haKer : a ∈ f.toAddMonoidHom.ker := by
      rw [hker]
      exact AddSubgroup.mem_top a
    exact haKer

/-- Finite Abelian duality gives a character whose finite cyclic image
detects a prescribed central ideal of prime cardinality. -/
theorem exists_character_injective_on_prime_ideal
    {K : Type u} [LieRing K] [Finite K]
    (A : LieIdeal ℤ K) (hprime : (Nat.card A).Prime) :
    ∃ φ : Multiplicative K →* ℂˣ,
      Function.Injective ((CharacterRange.linearMap φ).comp A.subtype) := by
  letI : Nontrivial A :=
    Finite.one_lt_card_iff_nontrivial.mp hprime.one_lt
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have haK : (a : K) ≠ 0 := by
    intro h
    exact ha (Subtype.ext h)
  obtain ⟨ψ, hψ⟩ :=
    (AddChar.exists_apply_ne_zero (α := K) (a := (a : K))).2 haK
  let φ : Multiplicative K →* ℂˣ := ψ.toMonoidHom.toHomUnits
  have hφ : φ (Multiplicative.ofAdd (a : K)) ≠ 1 := by
    intro h
    apply hψ
    have h' := congrArg Units.val h
    simpa [φ] using h'
  refine ⟨φ, linearMap_injective_of_prime_card
    ((CharacterRange.linearMap φ).comp A.subtype) hprime (a := a) ?_⟩
  intro hzero
  apply hφ
  have hvalues := congrArg Additive.toMul hzero
  have hRange :
      φ.rangeRestrict (Multiplicative.ofAdd (a : K)) = 1 := by
    simpa [CharacterRange.linearMap] using hvalues
  exact congrArg Subtype.val hRange

/-! ## The elementary pushout -/

section Pushout

variable {K : Type u} [LieRing K]
variable {D : Type v} [AddCommGroup D]

/-- The additive map whose kernel is the relation subgroup in the pushout.
It sends (d,k) to (d + χ(k), k + A). -/
def cyclicPushoutLinear (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D) :
    TrivialLieRing D × K →ₗ[ℤ] D × (K ⧸ A) where
  toFun z := ((TrivialLieRing.equiv D z.1) + χ z.2,
    LieSubmodule.Quotient.mk z.2)
  map_add' x y := by
    ext
    · dsimp
      rw [map_add]
      abel
    · rfl
  map_smul' z x := by
    ext
    · simp [smul_add]
    · rfl

@[simp]
theorem cyclicPushoutLinear_apply (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (d : TrivialLieRing D) (k : K) :
    cyclicPushoutLinear A χ (d, k) =
      ((TrivialLieRing.equiv D d) + χ k, LieSubmodule.Quotient.mk k) :=
  rfl

/-- The relation subgroup is central, hence is a Lie ideal. Describing it as
the kernel of cyclicPushoutLinear makes the additive splitting definitional. -/
def cyclicPushoutRelation (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    LieIdeal ℤ (TrivialLieRing D × K) :=
  { LinearMap.ker (cyclicPushoutLinear A χ) with
    lie_mem := by
      intro x y hy
      have hyq : (LieSubmodule.Quotient.mk y.2 : K ⧸ A) = 0 := by
        have h := congrArg Prod.snd hy
        simpa [cyclicPushoutLinear] using h
      have hyA : y.2 ∈ A :=
        (LieSubmodule.Quotient.mk_eq_zero' (N := A)).mp hyq
      have hbracket : ⁅x.2, y.2⁆ = 0 := by
        exact hcentral hyA x.2
      have hfirst : ⁅x.1, y.1⁆ = 0 := rfl
      have hxy : ⁅x, y⁆ = 0 := by
        apply Prod.ext
        · exact hfirst
        · exact hbracket
      change cyclicPushoutLinear A χ ⁅x, y⁆ = 0
      rw [hxy, map_zero] }

/-- The Lie-ring pushout (D ⊕ K)/{(χ(a),-a)}. -/
abbrev CyclicPushout (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :=
  (TrivialLieRing D × K) ⧸ cyclicPushoutRelation A χ hcentral

/-- The quotient by a Lie ideal, bundled as a Lie homomorphism. -/
def cyclicPushoutQuotientMk (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    TrivialLieRing D × K →ₗ⁅ℤ⁆ CyclicPushout A χ hcentral where
  __ := (cyclicPushoutRelation A χ hcentral).toSubmodule.mkQ
  map_lie' := by
    intro x y
    rfl

theorem cyclicPushoutLinear_surjective (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D) :
    Function.Surjective (cyclicPushoutLinear A χ) := by
  rintro ⟨d, h⟩
  obtain ⟨k, rfl⟩ := LieSubmodule.Quotient.surjective_mk' A h
  refine ⟨((TrivialLieRing.equiv D).symm (d - χ k), k), ?_⟩
  ext <;> simp [cyclicPushoutLinear]

/-- The canonical additive splitting of the pushout. -/
def cyclicPushoutAddEquiv (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    CyclicPushout A χ hcentral ≃ₗ[ℤ] D × (K ⧸ A) :=
  (cyclicPushoutLinear A χ).quotKerEquivOfSurjective
    (cyclicPushoutLinear_surjective A χ)

/-- The canonical central inclusion of D into the pushout. -/
def cyclicPushoutInclD (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    TrivialLieRing D →ₗ⁅ℤ⁆ CyclicPushout A χ hcentral :=
  (cyclicPushoutQuotientMk A χ hcentral).comp
    (LieHom.inl ℤ (TrivialLieRing D) K)

/-- The canonical map from K into the pushout. -/
def cyclicPushoutInclK (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    K →ₗ⁅ℤ⁆ CyclicPushout A χ hcentral :=
  (cyclicPushoutQuotientMk A χ hcentral).comp
    (LieHom.inr ℤ (TrivialLieRing D) K)

@[simp]
theorem cyclicPushoutAddEquiv_inclD
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) (d : TrivialLieRing D) :
    cyclicPushoutAddEquiv A χ hcentral (cyclicPushoutInclD A χ hcentral d) =
      (TrivialLieRing.equiv D d, 0) := by
  change
    (cyclicPushoutLinear A χ).quotKerEquivOfSurjective
        (cyclicPushoutLinear_surjective A χ)
        (Submodule.Quotient.mk (d, 0)) =
      (TrivialLieRing.equiv D d, 0)
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  apply Prod.ext
  · change (TrivialLieRing.equiv D d) + χ 0 =
      TrivialLieRing.equiv D d
    rw [map_zero, add_zero]
  · rfl

@[simp]
theorem cyclicPushoutAddEquiv_inclK
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) (k : K) :
    cyclicPushoutAddEquiv A χ hcentral (cyclicPushoutInclK A χ hcentral k) =
      (χ k, LieSubmodule.Quotient.mk k) := by
  change
    (cyclicPushoutLinear A χ).quotKerEquivOfSurjective
        (cyclicPushoutLinear_surjective A χ)
        (Submodule.Quotient.mk (0, k)) =
      (χ k, LieSubmodule.Quotient.mk k)
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  apply Prod.ext
  · change (0 : D) + χ k = χ k
    exact zero_add _
  · rfl

theorem cyclicPushoutInclD_injective
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    Function.Injective (cyclicPushoutInclD A χ hcentral) := by
  intro d e hde
  have h := congrArg (fun z ↦ (cyclicPushoutAddEquiv A χ hcentral z).1) hde
  simpa using h

theorem cyclicPushoutInclD_mem_center
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) (d : TrivialLieRing D) :
    cyclicPushoutInclD A χ hcentral d ∈
      LieAlgebra.center ℤ (CyclicPushout A χ hcentral) := by
  intro z
  obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
    (cyclicPushoutRelation A χ hcentral) z
  change LieSubmodule.Quotient.mk
    ⁅x, ((d, (0 : K)) : TrivialLieRing D × K)⁆ = 0
  have hzero : ⁅x, ((d, (0 : K)) : TrivialLieRing D × K)⁆ = 0 := by
    apply Prod.ext
    · rfl
    · simp
  simp [hzero]

/-- The natural map from K is injective provided the additive map to D
is injective on A. -/
theorem cyclicPushoutInclK_injective
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K)
    (hχ : Function.Injective (χ.comp A.subtype)) :
    Function.Injective (cyclicPushoutInclK A χ hcentral) := by
  intro x y hxy
  have hpairs := congrArg (cyclicPushoutAddEquiv A χ hcentral) hxy
  have hχxy : χ x = χ y := by
    simpa using congrArg Prod.fst hpairs
  have hqxy :
      (LieSubmodule.Quotient.mk x : K ⧸ A) =
        LieSubmodule.Quotient.mk y := by
    simpa using congrArg Prod.snd hpairs
  have hmem : x - y ∈ A :=
    (Submodule.Quotient.eq A.toSubmodule).mp hqxy
  let a : A := ⟨x - y, hmem⟩
  have haχ : (χ.comp A.subtype) a = 0 := by
    change χ (x - y) = 0
    rw [map_sub, hχxy, sub_self]
  have ha0 : a = 0 :=
    hχ (haχ.trans (map_zero (χ.comp A.subtype)).symm)
  have hsub : x - y = 0 := congrArg Subtype.val ha0
  exact sub_eq_zero.mp hsub

/-- The two canonical maps identify an element of A with its image under
the chosen map to D; this is the defining pushout square. -/
theorem cyclicPushout_glues
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) (a : A) :
    cyclicPushoutInclD A χ hcentral
        ((TrivialLieRing.equiv D).symm (χ (a : K))) =
      cyclicPushoutInclK A χ hcentral (a : K) := by
  apply (cyclicPushoutAddEquiv A χ hcentral).injective
  apply Prod.ext
  · simp
  · have ha0 : (LieSubmodule.Quotient.mk (a : K) : K ⧸ A) = 0 :=
      (LieSubmodule.Quotient.mk_eq_zero' (N := A)).mpr a.property
    simp [ha0]

/-- The projection of the pushout onto K/A. -/
def cyclicPushoutProj
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    CyclicPushout A χ hcentral →ₗ⁅ℤ⁆ K ⧸ A where
  toLinearMap :=
    (LinearMap.snd ℤ D (K ⧸ A)).comp
      (cyclicPushoutAddEquiv A χ hcentral).toLinearMap
  map_lie' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change
          (cyclicPushoutLinear A χ ⁅x, y⁆).2 =
            ⁅(cyclicPushoutLinear A χ x).2,
              (cyclicPushoutLinear A χ y).2⁆
        rfl

@[simp]
theorem cyclicPushoutProj_inclD
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) (d : TrivialLieRing D) :
    cyclicPushoutProj A χ hcentral (cyclicPushoutInclD A χ hcentral d) = 0 := by
  rfl

@[simp]
theorem cyclicPushoutProj_inclK
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) (k : K) :
    cyclicPushoutProj A χ hcentral (cyclicPushoutInclK A χ hcentral k) =
      LieSubmodule.Quotient.mk k := by
  rfl

theorem cyclicPushoutProj_surjective
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    Function.Surjective (cyclicPushoutProj A χ hcentral) := by
  intro h
  obtain ⟨k, rfl⟩ := LieSubmodule.Quotient.surjective_mk' A h
  exact ⟨cyclicPushoutInclK A χ hcentral k, rfl⟩

theorem cyclicPushoutInclD_range_eq_proj_ker
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    LieHom.range (cyclicPushoutInclD A χ hcentral) =
      LieHom.ker (cyclicPushoutProj A χ hcentral) := by
  ext z
  constructor
  · rintro ⟨d, rfl⟩
    simp
  · intro hz
    have hzsecond :
        (cyclicPushoutAddEquiv A χ hcentral z).2 = 0 := by
      exact hz
    let d : TrivialLieRing D :=
      (TrivialLieRing.equiv D).symm
        (cyclicPushoutAddEquiv A χ hcentral z).1
    refine ⟨d, ?_⟩
    apply (cyclicPushoutAddEquiv A χ hcentral).injective
    apply Prod.ext
    · simp [d]
    · simp [hzsecond]

/-- The canonical maps form a short exact central extension. -/
instance cyclicPushoutIsExtension
    (A : LieIdeal ℤ K) (χ : K →ₗ[ℤ] D)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    LieAlgebra.IsExtension
      (cyclicPushoutInclD A χ hcentral)
      (cyclicPushoutProj A χ hcentral) where
  ker_eq_bot :=
    (LieHom.ker_eq_bot _).mpr (cyclicPushoutInclD_injective A χ hcentral)
  range_eq_top :=
    (LieHom.range_eq_top _).mpr (cyclicPushoutProj_surjective A χ hcentral)
  exact := cyclicPushoutInclD_range_eq_proj_ker A χ hcentral

end Pushout

/-! ## Finite cyclic detection for finitely generated Abelian groups -/

/-- Finite generation is closed under extensions.  This concrete form is
used below with a finite kernel and a finitely generated quotient. -/
theorem moduleFinite_of_finite_submodule_and_quotient
    {M : Type u} [AddCommGroup M]
    (N : Submodule ℤ M) [Module.Finite ℤ N]
    [Module.Finite ℤ (M ⧸ N)] : Module.Finite ℤ M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ (M ⧸ N)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property N.mkQ f
    (Submodule.mkQ_surjective N)
  let F : N × (Fin n → ℤ) →ₗ[ℤ] M := LinearMap.coprod N.subtype g
  apply Module.Finite.of_surjective F
  intro m
  obtain ⟨v, hv⟩ := hf (N.mkQ m)
  have hqg : N.mkQ (g v) = N.mkQ m := by
    rw [← hv]
    exact LinearMap.congr_fun hg v
  have hmem : m - g v ∈ N :=
    (Submodule.Quotient.eq N).mp hqg.symm
  refine ⟨(⟨m - g v, hmem⟩, v), ?_⟩
  simp [F, LinearMap.coprod_apply]

/-- The Lie ideal `nM` of scalar multiples. -/
def scalarMultipleIdeal (M : Type u) [LieRing M] (n : ℤ) : LieIdeal ℤ M where
  toSubmodule := LinearMap.range (n • (LinearMap.id : M →ₗ[ℤ] M))
  lie_mem := by
    rintro x y ⟨z, rfl⟩
    refine ⟨⁅x, z⁆, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [lie_smul]

theorem mem_scalarMultipleIdeal_iff
    (M : Type u) [LieRing M] (n : ℤ) (x : M) :
    x ∈ scalarMultipleIdeal M n ↔ ∃ y : M, n • y = x := by
  rfl

/-- The Lie-ring quotient `M/nM`. -/
abbrev ScalarMultipleQuotient (M : Type u) [LieRing M] (n : ℕ) :=
  M ⧸ scalarMultipleIdeal M (n : ℤ)

theorem scalarMultipleQuotient_nsmul_eq_zero
    (M : Type u) [LieRing M] (n : ℕ)
    (x : ScalarMultipleQuotient M n) : n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change
        (LieSubmodule.Quotient.mk (n • x) : ScalarMultipleQuotient M n) = 0
      apply (LieSubmodule.Quotient.mk_eq_zero'
        (N := scalarMultipleIdeal M (n : ℤ))).mpr
      exact ⟨x, by simp⟩

theorem scalarMultipleQuotient_finite
    (M : Type u) [LieRing M] (n : ℕ) (hn : n ≠ 0)
    [Module.Finite ℤ M] : Finite (ScalarMultipleQuotient M n) := by
  letI : Module.Finite ℤ (ScalarMultipleQuotient M n) :=
    Module.Finite.quotient ℤ (scalarMultipleIdeal M (n : ℤ)).toSubmodule
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), ?_⟩, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (Int.ofNat_ne_zero.mpr hn)
  · simpa using scalarMultipleQuotient_nsmul_eq_zero M n x

/-- A nonzero element of a finitely generated Abelian group survives in
some quotient by nonzero scalar multiples.  This is the only use of the
structure theorem for finitely generated Abelian groups in the pushout
construction. -/
theorem exists_scalarMultipleQuotient_detecting
    {G : Type u} [AddCommGroup G] [Module.Finite ℤ G]
    {c : G} (hc : c ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ¬ ∃ x : G, (n : ℤ) • x = c := by
  classical
  letI : AddGroup.FG G := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨m, ι, fintypeι, p, hp, e, ⟨E⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  letI : Fintype ι := fintypeι
  have hEc : E c ≠ 0 :=
    fun h ↦ hc (E.injective (h.trans (map_zero E).symm))
  by_cases hfree : (E c).1 = 0
  · have htor : (E c).2 ≠ 0 := by
      intro h
      exact hEc (Prod.ext hfree h)
    obtain ⟨i, hi⟩ : ∃ i : ι, (E c).2 i ≠ 0 := by
      by_contra h
      push Not at h
      exact htor (DFinsupp.ext fun i ↦ by simpa using h i)
    let n := p i ^ e i
    have hn : n ≠ 0 := pow_ne_zero _ (hp i).ne_zero
    refine ⟨n, hn, ?_⟩
    rintro ⟨x, hx⟩
    have hmap := congrArg (fun z ↦ (E z).2 i) hx
    have hzero : (E ((n : ℤ) • x)).2 i = 0 := by
      rw [map_zsmul]
      change (n : ℤ) • (E x).2 i = 0
      rw [zsmul_eq_mul]
      have hcast : ((n : ℤ) : ZMod n) = 0 :=
        (CharP.intCast_eq_zero_iff (ZMod n) n (n : ℤ)).2 dvd_rfl
      rw [hcast, zero_mul]
    exact hi (hmap.symm.trans hzero)
  · obtain ⟨j, hj⟩ : ∃ j : Fin m, (E c).1 j ≠ 0 := by
      by_contra h
      push Not at h
      exact hfree (Finsupp.ext fun j ↦ by simpa using h j)
    let n : ℕ := ((E c).1 j).natAbs + 1
    have hn : n ≠ 0 := by simp [n]
    refine ⟨n, hn, ?_⟩
    rintro ⟨x, hx⟩
    have hmap := congrArg (fun z ↦ (E z).1 j) hx
    have hdvd : (n : ℤ) ∣ (E c).1 j := by
      refine ⟨(E x).1 j, ?_⟩
      simpa [map_zsmul, smul_eq_mul] using hmap.symm
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hj
    rw [Int.natAbs_natCast] at hle
    dsimp [n] at hle
    omega

/-- Every nonzero element of a finitely generated Abelian Lie ring is
detected by an integral linear map to a finite cyclic group. -/
theorem exists_finite_cyclic_target_separating
    {M : Type u} [LieRing M] [Module.Finite ℤ M]
    {c : M} (hc : c ≠ 0) :
    ∃ (D : Type) (_ : AddCommGroup D) (_ : Finite D)
      (_ : IsAddCyclic D) (χ : M →ₗ[ℤ] D), χ c ≠ 0 := by
  obtain ⟨n, hn, hndiv⟩ := exists_scalarMultipleQuotient_detecting hc
  let C := ScalarMultipleQuotient M n
  let q : M →ₗ[ℤ] C := (scalarMultipleIdeal M (n : ℤ)).toSubmodule.mkQ
  letI : Finite C := scalarMultipleQuotient_finite M n hn
  have hqc : q c ≠ 0 := by
    intro h
    have hcJ : c ∈ scalarMultipleIdeal M (n : ℤ) :=
      (LieSubmodule.Quotient.mk_eq_zero'
        (N := scalarMultipleIdeal M (n : ℤ))).mp h
    exact hndiv ((mem_scalarMultipleIdeal_iff M (n : ℤ) c).mp hcJ)
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := q c)).2 hqc
  let φ : Multiplicative C →* ℂˣ := ψ.toMonoidHom.toHomUnits
  have hφ : CharacterRange.linearMap φ (q c) ≠ 0 := by
    intro h
    apply hψ
    have hvalues := congrArg Additive.toMul h
    have hrange :
        φ.rangeRestrict (Multiplicative.ofAdd (q c)) = 1 := by
      simpa [CharacterRange.linearMap] using hvalues
    have hu := congrArg Subtype.val hrange
    exact congrArg Units.val hu
  let D := CharacterRange φ
  let χ : M →ₗ[ℤ] D := (CharacterRange.linearMap φ).comp q
  refine ⟨D, inferInstance, inferInstance, inferInstance, χ, ?_⟩
  simpa [χ] using hφ

/-! ## Prime-order pushouts with finitely generated quotient -/

/-- **Finite cyclic pushout, without finiteness of the ambient ring.**
Let `A` be a central ideal of prime cardinality in `K`.  If `K/A` is
finitely generated as an Abelian group, there is a finite cyclic group `D`
and a central extension `CyclicPushout A χ hcentral` of `K/A` by `D`.
Both `D` and `K` embed in the middle Lie ring, and its underlying Abelian
group is linearly equivalent to `D × (K/A)`. -/
theorem exists_finiteCyclic_central_pushout_of_finite_quotient
    {K : Type u} [LieRing K]
    (A : LieIdeal ℤ K) (hprime : (Nat.card A).Prime)
    (hcentral : A ≤ LieAlgebra.center ℤ K)
    (hquot : Module.Finite ℤ (K ⧸ A)) :
    ∃ (D : Type) (_ : AddCommGroup D) (_ : Finite D)
      (_ : IsAddCyclic D) (χ : K →ₗ[ℤ] D),
      Function.Injective (χ.comp A.subtype) ∧
      Function.Injective (cyclicPushoutInclD A χ hcentral) ∧
      (∀ d : TrivialLieRing D,
        cyclicPushoutInclD A χ hcentral d ∈
          LieAlgebra.center ℤ (CyclicPushout A χ hcentral)) ∧
      Function.Injective (cyclicPushoutInclK A χ hcentral) ∧
      LieAlgebra.IsExtension
        (cyclicPushoutInclD A χ hcentral)
        (cyclicPushoutProj A χ hcentral) ∧
      Nonempty (CyclicPushout A χ hcentral ≃ₗ[ℤ] D × (K ⧸ A)) := by
  letI : Finite A := Nat.finite_of_card_ne_zero hprime.ne_zero
  letI : Module.Finite ℤ A := Module.Finite.of_finite
  letI : Module.Finite ℤ (K ⧸ A) := hquot
  letI : Module.Finite ℤ K :=
    moduleFinite_of_finite_submodule_and_quotient A.toSubmodule
  letI : Nontrivial A :=
    Finite.one_lt_card_iff_nontrivial.mp hprime.one_lt
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have haK : (a : K) ≠ 0 := by
    intro h
    exact ha (Subtype.ext h)
  obtain ⟨D, instDadd, instDfin, instDcyc, χ, hχa⟩ :=
    exists_finite_cyclic_target_separating haK
  letI : AddCommGroup D := instDadd
  letI : Finite D := instDfin
  letI : IsAddCyclic D := instDcyc
  have hχA : Function.Injective (χ.comp A.subtype) :=
    linearMap_injective_of_prime_card (χ.comp A.subtype) hprime hχa
  refine ⟨D, instDadd, instDfin, instDcyc, χ, hχA,
    cyclicPushoutInclD_injective A χ hcentral, ?_,
    cyclicPushoutInclK_injective A χ hcentral hχA,
    inferInstance, ⟨cyclicPushoutAddEquiv A χ hcentral⟩⟩
  exact fun d ↦ cyclicPushoutInclD_mem_center A χ hcentral d

/-! ## The finite ambient-ring special case -/

section FinitePrime

variable {K : Type u} [LieRing K] [Finite K]

instance finite_lieIdeal_quotient (A : LieIdeal ℤ K) : Finite (K ⧸ A) :=
  Finite.of_surjective
    (fun k : K ↦ (LieSubmodule.Quotient.mk k : K ⧸ A))
    (LieSubmodule.Quotient.surjective_mk' A)

/-- The pushout obtained from a finite character. -/
abbrev FiniteCyclicPushout
    (A : LieIdeal ℤ K) (φ : Multiplicative K →* ℂˣ)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :=
  CyclicPushout A (CharacterRange.linearMap φ) hcentral

instance finiteCyclicPushout_finite
    (A : LieIdeal ℤ K) (φ : Multiplicative K →* ℂˣ)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    Finite (FiniteCyclicPushout A φ hcentral) :=
  Finite.of_injective (cyclicPushoutAddEquiv A
    (CharacterRange.linearMap φ) hcentral)
    (cyclicPushoutAddEquiv A (CharacterRange.linearMap φ) hcentral).injective

/-- **Finite cyclic pushout.** If A is a central ideal of prime
cardinality in a finite Lie ring K, a finite character produces a finite
cyclic central kernel D, a finite central extension of K/A by D,
and an embedding of K into its middle Lie ring. The displayed linear
equivalence is the required additive splitting. -/
theorem exists_finiteCyclic_central_pushout
    (A : LieIdeal ℤ K) (hprime : (Nat.card A).Prime)
    (hcentral : A ≤ LieAlgebra.center ℤ K) :
    ∃ φ : Multiplicative K →* ℂˣ,
      Finite (CharacterRange φ) ∧
      IsAddCyclic (CharacterRange φ) ∧
      Finite (FiniteCyclicPushout A φ hcentral) ∧
      Function.Injective
        (cyclicPushoutInclD A (CharacterRange.linearMap φ) hcentral) ∧
      (∀ d : TrivialLieRing (CharacterRange φ),
        cyclicPushoutInclD A (CharacterRange.linearMap φ) hcentral d ∈
          LieAlgebra.center ℤ (FiniteCyclicPushout A φ hcentral)) ∧
      Function.Injective
        (cyclicPushoutInclK A (CharacterRange.linearMap φ) hcentral) ∧
      LieAlgebra.IsExtension
        (cyclicPushoutInclD A (CharacterRange.linearMap φ) hcentral)
        (cyclicPushoutProj A (CharacterRange.linearMap φ) hcentral) ∧
      Nonempty
        (FiniteCyclicPushout A φ hcentral ≃ₗ[ℤ]
          CharacterRange φ × (K ⧸ A)) := by
  obtain ⟨φ, hφ⟩ :=
    exists_character_injective_on_prime_ideal A hprime
  refine ⟨φ, inferInstance, inferInstance, inferInstance,
    cyclicPushoutInclD_injective A (CharacterRange.linearMap φ) hcentral,
    ?_, cyclicPushoutInclK_injective A (CharacterRange.linearMap φ)
      hcentral hφ, inferInstance, ?_⟩
  · exact fun d ↦
      cyclicPushoutInclD_mem_center A (CharacterRange.linearMap φ) hcentral d
  · exact ⟨cyclicPushoutAddEquiv A (CharacterRange.linearMap φ) hcentral⟩

end FinitePrime

end

end LieRings.Plotkin

assert_no_sorry
  LieRings.Plotkin.exists_finiteCyclic_central_pushout_of_finite_quotient
assert_no_sorry LieRings.Plotkin.exists_finiteCyclic_central_pushout
